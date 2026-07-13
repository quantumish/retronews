#!/usr/bin/env python3
#
# Copyright (c) luke8086
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 2 as published by
# the Free Software Foundation.
#

import sys

# if sys.version_info < (3, 9):
#     sys.stderr.write("Python 3.9 or newer is required.\n")
#     sys.exit(1)

import argparse
import curses
import curses.textpad
import html.parser
import json
import logging
import os
import re
import sqlite3
import traceback
import unicodedata
import urllib.request
import webbrowser
import time
from collections import defaultdict
from datetime import datetime
from functools import partial, reduce
from textwrap import wrap

USER_AGENT = "retronews"

KEY_BINDINGS = {
    ord("q"): lambda app: cmd_quit(app),
    ord("?"): lambda app: cmd_help(app),
    ord("\n"): lambda app: cmd_open(app),
    ord(" "): lambda app: cmd_open(app),
    ord("o"): lambda app: cmd_show_links(app),
    ord("x"): lambda app: cmd_close(app),
    ord("s"): lambda app: cmd_star(app),
    ord("S"): lambda app: cmd_star_thread(app),
    ord("u"): lambda app: cmd_set_unread(app),
    ord("D"): lambda app: cmd_dump(app),
    ord("r"): lambda app: cmd_toggle_raw_mode(app),
    ord("k"): lambda app: cmd_up(app),
    ord("j"): lambda app: cmd_down(app),
    ord("p"): lambda app: cmd_prev(app),
    ord("n"): lambda app: cmd_next(app),
    ord("N"): lambda app: cmd_next_unread(app),
    ord("P"): lambda app: cmd_parent(app),
    ord(";"): lambda app: cmd_mark_set(app),
    ord(","): lambda app: cmd_mark_jump(app),
    ord("R"): lambda app: cmd_reload_page(app),
    ord("<"): lambda app: cmd_load_prev_page(app),
    ord(">"): lambda app: cmd_load_next_page(app),
    ord("g"): lambda app: cmd_load_page(app),
    curses.KEY_UP: lambda app: cmd_prev(app),
    curses.KEY_DOWN: lambda app: cmd_next(app),
    curses.KEY_PPAGE: lambda app: cmd_page_up(app),
    curses.KEY_NPAGE: lambda app: cmd_page_down(app),
    curses.KEY_RESIZE: lambda app: cmd_resize(app),
}
KEY_BINDINGS.update({ord(str(i)): lambda app, i=i: cmd_load_tab(app, i) for i in range(1, 10)})

HELP_MENU = "q:Quit  ?:Help  p:Prev  n:Next  N:Next-Unread  j:Down  k:Up  x:Close  s:Star"

HELP_SCREEN = """\
  q                       Quit retronews
  UP, DOWN                Go up / down by one message / pager line
  PG UP, PG DOWN          Gp up / down by one page of messages / pager lines
  p, n                    Go to previous / next message
  N                       Go to next unread message
  P                       Go to parent message
  ; ,                     Set mark, jump to mark & swap (valid within thread)
  RETURN, SPACE           Open selected message
  x                       Close current message / thread
  o                       Select link and open in browser
  1 - 9                   Change group
  R                       Refresh current page
  < >                     Go to previous / next page
  g                       Go to specific page
  k j                     Scroll pager up / down by one line
  s                       Star / unstar current message
  S                       Star / unstar current thread
  u                       Mark current message as unread
  r                       Toggle raw HTML mode

See https://github.com/luke8086/retronews for more information."""

COLORS = {
    "author": (curses.COLOR_YELLOW, -1),
    "code": (curses.COLOR_GREEN, -1),
    "cursor": (curses.COLOR_BLACK, curses.COLOR_CYAN),
    "date": (curses.COLOR_CYAN, -1),
    "default": (curses.COLOR_WHITE, -1),
    "empty_pager_line": (curses.COLOR_GREEN, -1),
    "deleted_message_pager_line": (curses.COLOR_RED, -1),
    "menu": (curses.COLOR_GREEN, curses.COLOR_BLUE),
    "menu_active": (curses.COLOR_YELLOW, curses.COLOR_BLUE),
    "nested_quote": (curses.COLOR_CYAN, -1),
    "quote": (curses.COLOR_YELLOW, -1),
    "starred_subject": (curses.COLOR_CYAN, -1),
    "header_subject": (curses.COLOR_GREEN, -1),
    "tree": (curses.COLOR_RED, -1),
    "unread_comments": (curses.COLOR_GREEN, -1),
    "url": (curses.COLOR_MAGENTA, -1),
}

PREFERRED_PAGE_SIZE = 30
UNREAD_SIZE = 3
UNREAD_MANY_CHAR = '!'
AUTHOR_SIZE = 10
COLUMN_SPACING = 2
DATECOL_SIZE = 16
DATECOL_FUNC = lambda date: date.strftime("%Y-%m-%d %H:%M")

REQUEST_TIMEOUT = 10

# Recognize ">text", "> text", ">>text", ">> text", etc.
QUOTE_REX = re.compile(r"^(> ?)+")

# Recognize "[n] link", "[n]: link", "[n] - link", etc.
REFERENCE_REX = re.compile(r"^\[\d+\][ :-]*https?://[^ ]*$")

# Recognize http/https URLs
URL_REX = re.compile(r"(https?://[^\s\)\"<,]+[^\s\)\"<,\.])")

# Recognize HN message URLs
HN_URL_REX = re.compile(r"^https://news\.ycombinator\.com/item\?id=(\d+)$")
LB_URL_REX = re.compile(r"^https://lobste\.rs/s/([a-z0-9]{6}).*$")

TRUNCATE = lambda s,l: s[:l]

class ExitException(Exception):
    def __init__(self, code = 0, message = ""):
        self.code = code
        self.message = message

        super().__init__(message)


class Provider:
    def __init__(self, fetch_thread, fetch_threads_by_id):
        self.fetch_thread = fetch_thread
        self.fetch_threads_by_id = fetch_threads_by_id

PROVIDERS = {
    "hn": Provider(
        fetch_thread=lambda msg_id: hn_fetch_thread(msg_id),
        fetch_threads_by_id=lambda msg_ids: hn_fetch_threads_by_id(msg_ids),
    ),
    "lb": Provider(
        fetch_thread=lambda msg_id: lb_fetch_thread(msg_id),
        fetch_threads_by_id=lambda msg_ids: [lb_fetch_thread(x) for x in msg_ids],
    ),
}


class Group:
    def __init__(self, label, fetch, page=0):
        self.label = label
        self.fetch = fetch
        self.page = page


GROUP_TABS = [
    Group(label="Front HN", fetch=lambda db, page: hn_fetch_threads("news", page)),
    Group(label="New HN", fetch=lambda db, page: hn_fetch_new_threads(page)),
    Group(label="Ask HN", fetch=lambda db, page: hn_fetch_threads("ask", page)),
    Group(label="Show HN", fetch=lambda db, page: hn_fetch_threads("show", page)),
    Group(label="Front LB", fetch=lambda db, page: lb_fetch_threads("", page)),
    Group(label="New LB", fetch=lambda db, page: lb_fetch_threads("newest", page)),
    Group(label="Starred", fetch=lambda db, page: group_fetch_starred_threads(db, page)),
]


class MessageFlags:
    def __init__(self, read = False, starred=False): 
        self.read = False
        self.starred = False


class Message:
    def __init__(self, msg_id, thread_id, content_location, date, author, title,
                 body=None, children=None, total_comments=0, parent=None):
        self.msg_id = msg_id
        self.thread_id = thread_id
        self.content_location = content_location
        self.date = date
        self.author = author
        self.title = title
        self.body = body
        self.children = children
        self.total_comments = total_comments
        self.parent = parent
        self.lines = []
        self.flags = MessageFlags()
        self.read_comments = 0
        self.index_position = 0
        self.index_tree = ""

    @property
    def is_read(self):
        return self.flags.read

    @property
    def is_shown_as_read(self):
        # If the message is an unloaded thread, check if all comments are read
        return self.read_comments >= self.total_comments if self.is_thread and self.children is None else self.is_read

    @property
    def is_thread(self):
        return self.msg_id == self.thread_id

    @property
    def is_deleted(self):
        return self.author is None


class Layout:
    def __init__(self):
        self.lines = 0
        self.cols = 0
        self.top_menu_row = 0
        self.index_start = 1
        self.index_height = 0
        self.middle_menu_row = None
        self.pager_start = None
        self.pager_height = None
        self.bottom_menu_row = 0
        self.flash_menu_row = 0


class AppState:
    def __init__(self, screen, db, group, ascii=False, monochrome=False):
        self.screen = screen
        self.db = db
        self.group = group
        self.ascii = ascii
        self.monochrome = monochrome
        self.colors = {}
        self.messages = []
        self.messages_by_id = {}
        self.selected_message = None
        self.marked_message_id = ""
        self.layout = Layout()
        self.pager_visible = False
        self.pager_offset = 0
        self.raw_mode = False
        self.flash = None

HTML_BLOCK_TAGS = set(("root", "p", "pre", "blockquote", "ul", "ol", "li", "hr"))
HTML_INLINE_TAGS = set(("code", "a", "em", "strong", "b", "br"))
HTML_KNOWN_TAGS = HTML_BLOCK_TAGS.union(HTML_INLINE_TAGS)
HTML_AUTOCLOSE_TAGS = set(("hr", "br"))

class HTMLNode:
    def __init__(self, tag, attrs=None, text="", pre=False):
        self.tag = tag
        self.text = text
        self.pre = pre
        self.attrs = {} if attrs is None else attrs
        self.parent = None
        self.prev_sibling = None
        self.next_sibling = None
        self.first_child = None
        self.last_child = None

class HTMLParser(html.parser.HTMLParser):
    def __init__(self):
        super().__init__()
        self.pre_level = 0
        self.root_node = self.current_node = HTMLNode(tag="root")

    def handle_data(self, data):
        if self.current_node.tag in HTML_AUTOCLOSE_TAGS:
            self.handle_endtag(self.current_node.tag)

        node = HTMLNode(tag="text", text=data, pre=self.pre_level > 0)
        html_node_append(self.current_node, node)

    def handle_starttag(self, tag, attrs):
        if self.current_node.tag in HTML_AUTOCLOSE_TAGS:
            self.handle_endtag(self.current_node.tag)

        if tag not in HTML_KNOWN_TAGS:
            return

        if tag == "pre":
            self.pre_level += 1

        node = HTMLNode(tag=tag, attrs=dict(attrs), pre=self.pre_level > 0)
        html_node_append(self.current_node, node)
        self.current_node = node

    def handle_endtag(self, tag):
        if tag not in HTML_KNOWN_TAGS:
            return

        if tag == "pre":
            self.pre_level = max(0, self.pre_level - 1)

        while True:
            node = self.current_node

            if node.parent is None:
                break

            self.current_node = node.parent

            if node.tag == tag:
                break


def text_wrap(text, width=70):
    if len(text) == 0:
        # Preserve empty lines
        return ""

    if text.startswith("  "):
        # Preserve code indentation
        return text

    if REFERENCE_REX.match(text):
        # Keep reference numbers with long links in the same line
        return text

    indent = ""

    match = QUOTE_REX.match(text)
    if match is not None:
        # Preserve quotation symbols in subsequent lines
        indent = match[0]

    lines = wrap(text, width, subsequent_indent=indent, break_on_hyphens=False, break_long_words=False)
    lines = [line.rstrip() for line in lines]

    return "\n".join(lines)


def text_clean(text, ascii = False):
    """Cleanup text for rendering, currently only removes non-ascii characters in ascii mode"""

    if ascii:
        text = text.encode("ascii", "replace").decode("ascii")

    return text


def text_unindent(text):
    lines = text.split("\n")

    while all(line.startswith(" ") or line == "" for line in lines):
        lines = [line[1:] for line in lines]

    return "\n".join(lines)


def text_sanitize(text):
    # For safety, remove any control characters except for \n and \t
    # At least on HN some messages contain \x00 characters

    text = text or ""
    allowed_cc = set(("\n", "\t"))
    chars = (c for c in text if c in allowed_cc or unicodedata.category(c) != "Cc")
    text = "".join(chars)

    return text


def text_split_urls(text):
    return [p for p in URL_REX.split(text) if p != ""]


def html_node_children(parent):
    ret = []
    node = parent.first_child

    while node is not None:
        ret.append(node)
        node = node.next_sibling

    return ret


def html_node_append(parent, child):
    if parent.first_child is None:
        parent.first_child = child

    if parent.last_child is not None:
        parent.last_child.next_sibling = child
        child.prev_sibling = parent.last_child

    parent.last_child = child
    child.parent = parent


def html_node_unlink(node):
    if node.prev_sibling:
        node.prev_sibling.next_sibling = node.next_sibling

    if node.next_sibling:
        node.next_sibling.prev_sibling = node.prev_sibling

    if node.parent and node.parent.first_child is node:
        node.parent.first_child = node.next_sibling

    if node.parent and node.parent.last_child is node:
        node.parent.last_child = node.prev_sibling

    node.parent = node.prev_sibling = node.next_sibling = None


def html_node_dump(node):
    lines = []
    lines.append("{} {}".format(node.tag, repr(node.attrs)))

    for child in html_node_children(node):
        if child.tag == "text":
            lines.append("  text " + repr(child.text))
        else:
            lines += ["  " + line for line in html_node_dump(child).split("\n")]

    return "\n".join(lines)


def html_node_trim_whitespace(node):
    if node.pre:
        node.text = node.text.rstrip("\r\n\t ")
        return

    text = node.text.strip("\r\n\t ")
    text = re.sub(r"[\r\n\t ]+", " ", text)
    text = text.replace("\x00", "\n")
    text = re.sub(r" *\n *", "\n", text)

    node.text = text


def html_node_process_inline(node, inline=False):
    """Traverse tree flattening all inline nodes into text nodes"""

    if node.tag not in HTML_BLOCK_TAGS:
        # Never disable inline if already enabled
        inline = True

    text = "".join(html_node_process_inline(c, inline) for c in html_node_children(node))

    if not inline:
        return ""

    if node.tag == "text":
        text = node.text
    elif node.tag == "br":
        text = "\x00"
    elif node.tag == "em" or node.tag == "i":
        text = "/{}/".format(text)
    elif node.tag == "strong" or node.tag == "b":
        text = "*{}*".format(text)
    elif node.tag == "code" and not node.pre:
        text = "`{}`".format(text)
    elif node.tag == "a":
        href = node.attrs.get("href", "") or ""
        if text.endswith("...") and href.startswith(text[:-3]):
            # Workaround for link formatting on HN
            text = href
        elif text != href:
            text = "{} {}".format(text, href)

    node.tag = "text"
    node.text = text
    node.first_child = node.last_child = None

    return text


def html_node_process_text(node):
    """Traverse tree merging, trimming and pruning text nodes"""

    for child in html_node_children(node):
        html_node_process_text(child)

    # Merge adjacent text nodes
    for child in html_node_children(node):
        prev = child.prev_sibling
        if child.tag == "text" and prev is not None and prev.tag == "text" and child.pre == prev.pre:
            child.text = prev.text + child.text
            html_node_unlink(prev)

    # Trim whitespace from text nodes
    for child in html_node_children(node):
        if child.tag == "text":
            html_node_trim_whitespace(child)

    # Remove empty text nodes
    for child in html_node_children(node):
        if child.tag == "text" and child.text == "":
            html_node_unlink(child)


def html_node_render_block(node, width=70):
    if node.tag == "blockquote" or node.tag == "li" or node.tag == "pre":
        width -= 2

    parts = []

    if node.tag == "hr":
        parts.append("-" * width)

    for child in html_node_children(node):
        if child.tag == "text" and child.pre:
            parts.append(child.text)

        elif child.tag == "text" and not child.pre:
            subparts = [text_wrap(p, width) for p in child.text.split("\n")]
            parts.append("\n".join(subparts))

        else:
            parts.append(html_node_render_block(child, width))

        if child.next_sibling is not None and child.tag != "li":
            parts.append("")

    text = "\n".join(parts)

    if node.tag == "blockquote":
        text = "\n".join((">" if line.startswith("> ") else "> ") + line for line in text.split("\n"))
    elif node.tag == "pre":
        text = text_unindent(text)
        text = "\n".join("| " + line for line in text.split("\n"))
    elif node.tag == "li":
        lines = text.split("\n")
        lines = [("- " + lines[0]).rstrip()] + [("  " + line).rstrip() for line in lines[1:]]
        text = "\n".join(lines)

    return text


def html_render(html):
    # This renderer works well for HN messages because their markup is simple, and it can do
    # some custom optimizations, like expanding ellipsis-shortened links, preserving quote
    # symbols in wrapped lines, and preventing references with long urls from being broken
    # into separate lines. For other backends it may make more sense to use an external app
    # (links, w3m, etc)

    html = text_sanitize(html)

    parser = HTMLParser()
    parser.feed(html)
    parser.close()

    node = parser.root_node

    log_sep = "\n" + "-" * 80 + "\n"
    logging.debug("Initial HTML tree{}{}{}".format(log_sep, html_node_dump(node), log_sep))

    html_node_process_inline(node)
    html_node_process_text(node)

    logging.debug("Processed HTML tree{}{}{}".format(log_sep, html_node_dump(node), log_sep))

    return html_node_render_block(node)


def fetch(url):
    logging.debug("Fetching '{}'...".format(url))

    headers = {}
    if USER_AGENT is not None:
        headers["User-Agent"] = USER_AGENT

    req = urllib.request.Request(url, headers=headers)
    resp = urllib.request.urlopen(req, timeout=REQUEST_TIMEOUT).read().decode()

    return resp


def list_get(lst, index, default=None):
    return lst[index] if 0 <= index < len(lst) else default


def list_chunk(lst, size):
    # Flake8 conflicts with Black here - https://github.com/PyCQA/pycodestyle/issues/373
    return [lst[i : i + size] for i in range(0, len(lst), size)]  # noqa: E203


def cmd_quit(_):
    raise ExitException()


def cmd_help(app):
    app_show_help_screen(app)


def cmd_show_links(app):
    app_show_links_screen(app)


def cmd_up(app):
    cmd_pager_up(app) if app.pager_visible else cmd_prev(app)


def cmd_down(app):
    cmd_pager_down(app) if app.pager_visible else cmd_next(app)


def cmd_prev(app):
    pos = app.selected_message.index_position - 1 if app.selected_message else 0
    app_select_message(app, list_get(app.messages, pos, app.selected_message))


def cmd_next(app):
    pos = app.selected_message.index_position + 1 if app.selected_message else 0
    app_select_message(app, list_get(app.messages, pos, app.selected_message))


def cmd_next_unread(app):
    pos = app.selected_message.index_position + 1 if app.selected_message else 0
    message = next((msg for msg in app.messages[pos:] if not msg.is_shown_as_read), None)
    if message is not None:
        app_select_message(app, message)


def cmd_next_sibling(app):
    msg = app.selected_message
    if msg is None:
        return
    parent_msg = msg.parent
    if parent_msg and parent_msg.children:
        # find the next sibling
        try:
            idx = parent_msg.children.index(msg)
            if idx < len(parent_msg.children):
                app_select_message(app, parent_msg.children[idx + 1])
        except IndexError:
            pass


def cmd_prev_sibling(app):
    msg = app.selected_message
    if msg is None:
        return
    parent_msg = msg.parent
    if parent_msg and parent_msg.children:
        # find the previous sibling
        try:
            idx = parent_msg.children.index(msg)
            if idx > 0:
                app_select_message(app, parent_msg.children[idx - 1])
        except IndexError:
            pass


def cmd_mark_thread_as_read(app):
    # recursively mark us and all children as read
    # then jump to the next sibling
    def iterate(message):
        if message.children:
            for child in message.children:
                child.flags.read = True
                db_save_message(app.db, child)
                iterate(child)

    msg = app.selected_message
    if msg is not None:
        iterate(msg)
        # jump to the next sibling
        cmd_next_sibling(app)


def cmd_parent(app):
    if app.selected_message is not None and app.selected_message.parent is not None:
        app_select_message(app, app.selected_message.parent)


def cmd_mark_set(app):
    if app.selected_message is not None:
        app.marked_message_id = app.selected_message.msg_id
    app_show_flash(app, "Mark set")


def cmd_mark_jump(app):
    marked_msg = app.messages_by_id.get(app.marked_message_id) if app.marked_message_id else None
    cmd_mark_set(app)
    if marked_msg is not None:
        app_select_message(app, marked_msg)
    app_show_flash(app, "Mark swapped")


def cmd_pager_up(app):
    app.pager_offset = max(0, app.pager_offset - 1)


def cmd_pager_down(app):
    if app.selected_message is not None and app.layout.pager_height is not None:
        app.pager_offset = min(app.pager_offset + 1, max(0, len(app.selected_message.lines) - app.layout.pager_height))


def cmd_page_up(app):
    cmd_pager_page_up(app) if app.pager_visible else cmd_index_page_up(app)


def cmd_page_down(app):
    cmd_pager_page_down(app) if app.pager_visible else cmd_index_page_down(app)


def cmd_index_page_up(app):
    pos = app.selected_message.index_position - app.layout.index_height if app.selected_message else 0
    pos = max(pos, 0)
    app_select_message(app, list_get(app.messages, pos, app.selected_message))


def cmd_index_page_down(app):
    pos = app.selected_message.index_position + app.layout.index_height if app.selected_message else 0
    pos = min(pos, len(app.messages) - 1)
    app_select_message(app, list_get(app.messages, pos, app.selected_message))


def cmd_pager_page_up(app):
    if app.layout.pager_height is not None:
        app.pager_offset = max(0, app.pager_offset - app.layout.pager_height)


def cmd_pager_page_down(app):
    message = app.selected_message
    pager_height = app.layout.pager_height
    if message is not None and pager_height is not None:
        app.pager_offset = min(app.pager_offset + pager_height, max(0, len(message.lines) - pager_height))


def cmd_load_tab(app, tab):
    group = list_get(GROUP_TABS, tab - 1)
    if group:
        app_load_group(app, group)


def cmd_reload_page(app):
    app_load_group(app, app.group)


def cmd_load_prev_page(app):
    app_load_group(app, group_advance_page(app.group, -1))


def cmd_load_next_page(app):
    app_load_group(app, group_advance_page(app.group, 1))


def cmd_load_page(app):
    user_input = app_prompt(app, "Go to page (empty to cancel): ")

    if not user_input.isnumeric() or int(user_input) < 1:
        app_show_flash(app, "Invalid page number")
    else:
        app_load_group(app, group_set_page(app.group, int(user_input)))

def make_group(name, f):
    return Group(label=name, fetch=lambda db, page: f(page))

def cmd_lb_see_tags(app):
    user_input = app_prompt(app, "Stories for tag(s) (comma to combine): ")
    app_load_group(app, make_group(TRUNCATE(user_input, 25),
                                   lambda page: lb_fetch_threads("t/"+user_input, page)))

def cmd_lb_see_user(app):
    user_input = app_prompt(app, "Stories posted by user: ")
    app_load_group(app, make_group(TRUNCATE(user_input, 25),
                                   lambda page: lb_fetch_threads("~{}/stories".format(user_input), page)))

def cmd_hn_see_user(app):
    user_input = app_prompt(app, "Stories posted by user: ")
    app_load_group(app, make_group(TRUNCATE(user_input, 25),
                                   lambda page: hn_fetch_user_threads(user_input, page)))

def cmd_open(app):
    if app.selected_message is None:
        return

    if app.selected_message.is_thread:
        app_open_thread(app, app.selected_message)
    else:
        app_select_message(app, app.selected_message, show_pager=True)


def cmd_close(app):
    if app.pager_visible:
        app.pager_visible = False
    else:
        app_close_thread(app)


def cmd_star(app):
    msg = app.selected_message
    if msg is not None:
        msg.flags.starred = not msg.flags.starred
        db_save_message(app.db, msg)
        cmd_next(app)


def cmd_star_thread(app):
    msg = app.selected_message
    if msg is None:
        return

    thread_msg = app.messages_by_id.get(msg.thread_id)
    if thread_msg is None:
        return

    thread_msg.flags.starred = not thread_msg.flags.starred
    db_save_message(app.db, thread_msg)
    cmd_next(app)


def cmd_set_unread(app):
    if app.selected_message is not None:
        app.selected_message.flags.read = False
        db_save_message(app.db, app.selected_message)
        cmd_next(app)


def cmd_dump(app):
    if app.selected_message is None:
        return

    filename = "{}.html".format(app.selected_message.msg_id)

    with open(filename, "w") as fp:
        fp.write(app.selected_message.body or "")

    app_show_flash(app, "Message body dumped to {}".format(filename))


def cmd_toggle_raw_mode(app):
    app.raw_mode = not app.raw_mode
    app_select_message(app, app.selected_message)


def cmd_resize(app):
    app_refresh_message(app)


def cmd_unknown(app):
    app.flash = "Unknown key"


def db_init(path):
    path = os.path.expanduser(path)
    create_table_sql = """
        CREATE TABLE IF NOT EXISTS messages (
            msg_id TEXT NOT NULL PRIMARY KEY,
            thread_id TEXT NOT NULL,
            date INTEGER NOT NULL,
            starred BOOLEAN NOT NULL,
            read BOOLEAN NOT NULL
        );

        CREATE INDEX IF NOT EXISTS messages_starred_date ON messages (starred, date);
    """

    db = sqlite3.connect(path)
    db.row_factory = sqlite3.Row
    db.executescript(create_table_sql)
    db.commit()

    return db


def db_save_message(db, message):
    sql = """INSERT OR REPLACE INTO messages (msg_id, thread_id, date, starred, read) VALUES (?, ?, ?, ?, ?)"""
    date = int(time.mktime(message.date.timetuple()))
    db.execute(sql, (message.msg_id, message.thread_id, date, message.flags.starred, message.flags.read))
    db.commit()


def db_load_message_flags(db, messages_by_id):
    message_ids = list(messages_by_id.keys())
    sql = "SELECT * FROM messages WHERE msg_id IN ({})".format(','.join('?' for _ in message_ids))

    for row in db.execute(sql, message_ids):
        flags = MessageFlags()
        flags.starred = row["starred"]
        flags.read = row["read"]
        messages_by_id[row["msg_id"]].flags = flags


def db_load_read_comments(db, messages_by_id):
    threads_by_id = {msg.msg_id: msg for msg in messages_by_id.values() if msg.is_thread}
    thread_ids = list(threads_by_id.keys())

    sql = """
        SELECT thread_id, COUNT(*) AS count
        FROM messages
        WHERE thread_id IN ({}) AND read
        GROUP BY thread_id
    """.format(','.join('?' for _ in thread_ids))

    for row in db.execute(sql, thread_ids):
        threads_by_id[row["thread_id"]].read_comments = row["count"]


def db_load_starred_thread_ids(db, page = 1):
    page_size = 30
    offset = (page - 1) * page_size
    sql = """
        SELECT thread_id
        FROM messages
        WHERE starred
        GROUP BY thread_id
        ORDER BY date DESC
        LIMIT ?
        OFFSET ?
    """

    return [row["thread_id"] for row in db.execute(sql, (page_size, offset))]


def msg_populate_total_count(msg):
    children = msg.children or []
    msg.total_count = 0
    
    if len(children) == 0:
        return

    for child in children:
        msg_populate_total_count(child)
        msg.total_count += 1 + child.total_count

def msg_flatten_thread(
    msg, prefix = "", is_last_child = False, ascii = False
):
    blcorner = "'-" if ascii else "└─"
    ltee = "|-" if ascii else "├─"
    vline = "| " if ascii else "│ "

    msg.index_tree = "" if msg.is_thread else "{}{}> ".format(prefix, blcorner if is_last_child else ltee)
    yield msg

    children = msg.children or []

    child_count = len(children)
    child_prefix = "" if msg.is_thread else "{}{}".format(prefix, '  ' if is_last_child else vline)

    for i, child_node in enumerate(children):
        child_is_last = i == child_count - 1
        for child in msg_flatten_thread(child_node, prefix=child_prefix, is_last_child=child_is_last, ascii=ascii):
            yield child


def msg_build_raw_lines(msg):
    text = text_sanitize(msg.body)

    # Unescape selected entities for better readability
    repl = {"&#x2F;": "/", "&#x27;": "'", "&quot;": '"'}
    for k, v in repl.items():
        text = text.replace(k, v)

    return reduce(lambda acc, line: acc + wrap(line, width=120, replace_whitespace=False), text.split("\n"), [])


def msg_build_lines(msg):
    lines = [
        "Content-Location: {}".format(msg.content_location),
        "Date: {}".format(msg.date.strftime('%Y-%m-%d %H:%M')),
        "From: {}".format(msg.author or '<unknown>'),
        "Subject: {}".format(msg.title),
        "",
    ]

    lines += html_render(msg.body or "").split("\n") if not msg.is_deleted else ["<deleted>"]

    return lines


def msg_unload(msg):
    msg.children = None
    msg.body = None
    return msg


def hn_parse_search_hit(hit):
    return Message(
        msg_id="{}@hn".format(hit['objectID']),
        thread_id="{}@hn".format(hit['objectID']),
        content_location="https://news.ycombinator.com/item?id={}".format(hit['objectID']),
        date=datetime.fromtimestamp(hit["created_at_i"]),
        author=hit["author"],
        title=html.unescape(hit["title"]),
        total_comments=(hit["num_comments"] or 0) + 1
    )


def hn_parse_entry(entry, thread_id = "", parent = None):
    thread_id = thread_id or str(entry["id"])

    my_title = html.unescape(entry["title"]) if entry["title"] else None

    parent_title = parent.title if parent else ""
    parent_title = parent_title if parent_title.startswith("Re: ") else "Re: {}".format(parent_title)

    body = "<p>{}</p>".format(entry['url']) if entry["url"] else ""
    body = "{}{}".format(body, entry['text']) if entry["text"] else body

    msg = Message(
        msg_id="{}@hn".format(entry['id']),
        thread_id="{}@hn".format(thread_id),
        content_location="https://news.ycombinator.com/item?id={}".format(entry['id']),
        date=datetime.fromtimestamp(entry["created_at_i"]),
        author=entry["author"],
        title=my_title or parent_title,
        body=body,
        parent=parent,
    )

    msg.children = [hn_parse_entry(child, thread_id, msg) for child in entry["children"]]

    return msg


def hn_fetch_threads_by_id(thread_ids):
    story_tags = ",".join("story_{}".format(x) for x in thread_ids)
    url = "https://hn.algolia.com/api/v1/search_by_date?hitsPerPage={}&tags=story,({})".format(len(thread_ids), story_tags)
    hits = json.loads(fetch(url))["hits"]
    hits_by_id = {hit["objectID"]: hit for hit in hits}
    threads = [hn_parse_search_hit(hits_by_id[tid]) for tid in thread_ids if tid in hits_by_id]

    return threads

def hn_fetch_user_threads(username, page = 1):
    url = "https://hn.algolia.com/api/v1/search?hitsPerPage={}&page={}&tags=story,author_{}".format(PREFERRED_PAGE_SIZE, page-1, username)
    print(url)
    hits = json.loads(fetch(url))["hits"]
    return [hn_parse_search_hit(hit) for hit in hits]
    
def hn_fetch_threads(group = "news", page = 1):
    rex = re.compile(r'href="item\?id=(\d+)"')

    url = "https://news.ycombinator.com/{}".format(group)
    # HN seems to be trigger-happy about sending 429s to some paginated requests with weird user agents
    if page != 1:
        url += "?p={}".format(page)
    
    html = fetch(url)
    thread_ids = list(dict.fromkeys(match.group(1) for match in rex.finditer(html)))

    return hn_fetch_threads_by_id(thread_ids)


def hn_fetch_new_threads(page = 1):
    url = "https://hn.algolia.com/api/v1/search_by_date?tags=story&hitsPerPage=30&page={}".format(page-1)
    hits = json.loads(fetch(url))["hits"]

    return [hn_parse_search_hit(hit) for hit in hits]


def hn_fetch_thread(entry_id):
    resp = fetch("http://hn.algolia.com/api/v1/items/{}".format(entry_id))
    entry = json.loads(resp)
    return hn_parse_entry(entry)


def datetime_from_iso(iso):
    # strptime()'s supported UTC offset format string requires it be
    # HHMM not HH:MM before python 3.12...
    iso = iso.replace(":", "")
    return datetime.strptime(iso, "%Y-%m-%dT%H%M%S.%f%z")


def lb_parse_thread(thread):
    comments = {}

    thread_body = thread['description']
    thread_body = "<p>{}</p>{}".format(thread['url'], thread_body) if thread["url"] else thread_body

    ret = Message(
        msg_id="{}@lb".format(thread['short_id']),
        thread_id="{}@lb".format(thread['short_id']),
        content_location=thread["short_id_url"],
        date=datetime_from_iso(thread["created_at"]),
        author=thread["submitter_user"],
        title=thread["title"],
        body=thread_body,
        children=None if thread.get("comments") is None else [],
        total_comments=thread["comment_count"] + 1
    )

    for comment in thread.get("comments", []) or []:
        comments[comment["short_id"]] = Message(
            msg_id="{}@lb".format(comment['short_id']),
            thread_id="{}@lb".format(thread['short_id']),
            content_location=comment["url"],
            date=datetime_from_iso(comment["created_at"]),
            author=comment["commenting_user"],
            title="Re: {}".format(thread['title']),
            body=comment["comment"],
            children=[]
        )

    for comment in thread.get("comments", []) or []:
        msg = comments[comment["short_id"]]
        parent_msg = comments[comment["parent_comment"]] if comment["parent_comment"] else ret
        msg.parent = parent_msg
        if parent_msg.children is not None:
            parent_msg.children.append(msg)

    return ret


def lb_fetch_threads(group = "", page = 1):
    group_path = group + "/" if group else ""
    resp = fetch("https://lobste.rs/{}page/{}.json".format(group_path, page))
    threads = json.loads(resp)

    return [lb_parse_thread(thread) for thread in threads]


def lb_fetch_thread(entry_id):
    resp = fetch("https://lobste.rs/s/{}.json".format(entry_id))
    thread = json.loads(resp)

    return lb_parse_thread(thread)


def group_set_page(group, page):
    return Group(group.label, group.fetch, page=page)


def group_advance_page(group, offset = 1):
    return group_set_page(group, page=max(1, group.page + offset))


def group_fetch_starred_threads(db, page = 1):
    thread_ids = db_load_starred_thread_ids(db, page)
    threads_by_provider_id = {}
    threads = []

    for source_id, provider_id in (t.split("@") for t in thread_ids):
        threads_by_provider_id.setdefault(provider_id, list()).append(source_id)

    for provider_id, thread_ids in threads_by_provider_id.items():
        provider = PROVIDERS[provider_id]
        threads += provider.fetch_threads_by_id(thread_ids)

    threads.sort(key=lambda x: x.date, reverse=True)

    return threads


def group_fetch_thread(thread_id):
    (msg_id, provider_id) = thread_id.split("@")
    provider = PROVIDERS[provider_id]

    return provider.fetch_thread(msg_id)


def group_for_msg_url(url):
    match = HN_URL_REX.match(url)
    if match is not None:
        msg_id = match[1]
        return Group(label=msg_id, fetch=lambda *x: [hn_fetch_thread(msg_id)])

    match = LB_URL_REX.match(url)
    if match is not None:
        msg_id = match[1]
        return Group(label=msg_id, fetch=lambda *x: [lb_fetch_thread(msg_id)])

    msg = "Unknown URL, available patterns: \n" + "\n".join("- {}".format(r.pattern) for r in [HN_URL_REX, LB_URL_REX])
    raise ExitException(1, msg)
7

def app_safe_run(app, fn, flash):
    if flash is not None:
        app_show_flash(app, flash)

    ret = None

    try:
        ret = fn()
    except Exception as e:
        logging.debug("\n".join(traceback.format_exception(type(e), e, e.__traceback__)))
        app_show_flash(app, "Error: " + str(e))
    else:
        if flash is not None:
            app_show_flash(app, None)

    return ret


def app_refresh_message(app):
    app.pager_offset = 0

    # Converting html to lines lazily on render for easier debugging
    msg = app.selected_message
    if msg is not None:
        msg.lines = msg_build_raw_lines(msg) if app.raw_mode else msg_build_lines(msg)


def app_select_message(app, message, show_pager = False):
    app.selected_message = message

    app_refresh_message(app)

    if message is None or message.body is None:
        app.pager_visible = False
        return

    if show_pager:
        app.pager_visible = True

    if app.pager_visible:
        message.flags.read = True
        db_save_message(app.db, message)
        db_load_read_comments(app.db, {message.thread_id: app.messages_by_id[message.thread_id]})


def app_load_messages(
    app, messages, selected_message_id = None, show_pager = False
):
    if selected_message_id is None and app.selected_message is not None:
        selected_message_id = app.selected_message.msg_id

    selected_message = None

    for i, message in enumerate(messages):
        message.index_position = i

        if message.msg_id == selected_message_id:
            selected_message = message

    if selected_message is None and len(messages) > 0:
        selected_message = messages[0]

    app.messages = messages
    app.messages_by_id = {msg.msg_id: msg for msg in messages}

    db_load_message_flags(app.db, app.messages_by_id)
    db_load_read_comments(app.db, app.messages_by_id)

    app_select_message(app, selected_message, show_pager)


def app_load_group(app, group):
    fn = partial(group.fetch, app.db, group.page)
    flash = "Fetching stories from '{}' (page {})...".format(group.label, group.page)

    messages = app_safe_run(app, fn, flash=flash)
    if messages is None:
        return

    app_load_messages(app, messages)
    app.group = group


def app_close_thread(app):
    selected_thread_id = app.selected_message.thread_id if app.selected_message else None
    filtered_messages = [msg_unload(msg) for msg in app.messages if msg.is_thread]

    app_load_messages(app, filtered_messages, selected_message_id=selected_thread_id)


def app_open_thread(app, thread_message):
    fn = partial(group_fetch_thread, thread_message.thread_id)
    flash = "Fetching thread '{}'...".format(thread_message.thread_id)

    new_thread_message = app_safe_run(app, fn, flash=flash)
    if new_thread_message is None:
        return

    app_close_thread(app)

    index_pos = thread_message.index_position
    thread_messages = list(msg_flatten_thread(new_thread_message, ascii=app.ascii))
    new_thread_message.total_comments = len(thread_messages)
    messages = app.messages[:index_pos] + thread_messages + app.messages[index_pos + 1 :]  # noqa: E203

    app_load_messages(app, messages, selected_message_id=thread_message.msg_id, show_pager=True)


def app_update_layout(app):
    lt = app.layout

    (lt.lines, lt.cols) = app.screen.getmaxyx()

    if lt.lines < 12 or lt.cols < 80:
        raise ExitException(1, "At least 80x12 terminal is required")

    max_index_height = lt.lines - 3
    lt.index_height = (max_index_height // 3) if app.pager_visible else max_index_height

    lt.middle_menu_row = lt.index_start + lt.index_height if app.pager_visible else None
    lt.pager_start = lt.index_start + lt.index_height + 1 if app.pager_visible else None
    lt.pager_height = lt.lines - lt.pager_start - 2 if lt.pager_start is not None else None

    lt.bottom_menu_row = lt.lines - 2
    lt.flash_menu_row = lt.lines - 1


def app_show_help_screen(app):
    max_lines = app.layout.lines - 4

    help_lines = HELP_SCREEN.split("\n")
    help_pages = ["\n".join(lines) for lines in list_chunk(help_lines, max_lines)]

    for page in help_pages:
        app.screen.erase()
        app.screen.addstr(0, 0, "Available commands:\n\n")
        app.screen.addstr(page)
        app.screen.addstr("\n\nPress any key to continue...")
        app.screen.refresh()
        app.screen.getch()


def app_show_links_screen(app):
    lines = app.selected_message.lines if app.selected_message is not None else []

    # Max amount of keys is 21 to fit on 25-line terminals
    keys = "1234567890abcdefghijk"
    urls = URL_REX.findall(" ".join(lines))
    items = dict(zip((ord(k) for k in keys), urls))

    if len(items) == 0:
        return app_show_flash(app, "No links available for opening")

    app.screen.erase()
    app.screen.addstr(0, 0, "Select link to open:")

    for i, (key, url) in enumerate(items.items()):
        app.screen.addstr(i + 2, 0, "{} - {}".format(chr(key), url))

    app.screen.addstr(i + 4, 0, "To change browser run: BROWSER='firefox %s' ./retronews.py")
    app.screen.refresh()

    key = app.screen.getch()

    if key not in items.keys():
        return app_show_flash(app, "Unknown key")

    url = items[key]

    app_show_flash(app, "Opening " + url)
    webbrowser.open(url)

    # Refresh window in case a terminal browser was used
    app.screen.clearok(True)


def app_show_flash(app, flash):
    app.flash = flash
    app_render(app)


def app_prompt(app, prompt):
    lt = app.layout

    app.screen.insstr(lt.flash_menu_row, 0, prompt.ljust(lt.cols))
    app.screen.refresh()

    curses.curs_set(1)
    win = curses.newwin(1, lt.cols - len(prompt), lt.flash_menu_row, len(prompt))

    textbox = curses.textpad.Textbox(win)
    textbox.stripspaces = True
    ret = textbox.edit().strip()

    del win
    curses.curs_set(0)

    return ret

def app_chgat(app, row, start, size, color):
    app.screen.chgat(row, start, size, color)
    return start + size

def app_render_index_row(app, row, message):
    cols = app.layout.cols
    date = TRUNCATE(DATECOL_FUNC(message.date), DATECOL_SIZE).rjust(DATECOL_SIZE)
    author = TRUNCATE(message.author or "<unknown>", AUTHOR_SIZE).ljust(AUTHOR_SIZE)

    is_response = message.title.startswith("Re:") and not message.is_thread
    is_selected = message == app.selected_message
    hide_title = is_response and row > app.layout.index_start and not message.flags.starred and not is_selected
    title = "" if hide_title else text_clean(message.title, ascii=app.ascii)

    unread_count = max(message.total_comments - message.read_comments, 0)
    unread_repr = str(unread_count) if unread_count < (10**UNREAD_SIZE - 1) else (UNREAD_MANY_CHAR * UNREAD_SIZE)
    unread = unread_repr.rjust(UNREAD_SIZE) if message.is_thread else (' ' * UNREAD_SIZE)

    spacing = ' ' * COLUMN_SPACING
    app.screen.insstr(row, 0, "[{}]{}[{}]{}[{}]{}{}{}".format(date, spacing, author, spacing, unread, spacing, message.index_tree, title))

    if is_selected:
        cursor_attr = curses.A_REVERSE if app.monochrome else 0
        app.screen.chgat(row, 0, cols, app.colors["cursor"] | cursor_attr)
    else:
        read_attr = 0 if message.is_shown_as_read else curses.A_BOLD
        subject_attr = app.colors["starred_subject"] if message.flags.starred else app.colors["default"]
        subject_attr = subject_attr | read_attr

        start = 1
        start = app_chgat(app, row, start, len(date), app.colors["date"] | read_attr)
        start = app_chgat(app, row, start + 2 + COLUMN_SPACING, AUTHOR_SIZE, app.colors["author"] | read_attr)
        start = app_chgat(app, row, start + 2 + COLUMN_SPACING, UNREAD_SIZE, app.colors["unread_comments"] | read_attr)
        start = app_chgat(app, row, start + 1 + COLUMN_SPACING, len(message.index_tree), app.colors["tree"])
        app_chgat(app, row, start, cols - start, subject_attr)


def app_render_index(app):
    height = app.layout.index_height

    offset = app.selected_message.index_position - height // 2 if app.selected_message else 0
    offset = min(offset, len(app.messages) - height)
    offset = max(offset, 0)

    rows_to_render = min(height, len(app.messages) - offset)

    for i in range(rows_to_render):
        app_render_index_row(app, app.layout.index_start + i, app.messages[i + offset])


def app_get_pager_line_attr(app, line):
    if line.startswith("Content-Location: "):
        return app.colors["tree"]
    elif line.startswith("Date: "):
        return app.colors["date"]
    elif line.startswith("From: "):
        return app.colors["author"]
    elif line.startswith("Subject: "):
        return app.colors["header_subject"]
    elif line.startswith(">>") or line.startswith("> >"):
        return app.colors["nested_quote"]
    elif line.startswith(">"):
        return app.colors["quote"]
    elif line.startswith("| "):
        return app.colors["code"]
    elif line == "~":
        return app.colors["empty_pager_line"]
    elif line == "<deleted>" or line == "[dead]":
        return app.colors["deleted_message_pager_line"]
    else:
        return 0


def app_render_pager_line(app, row, line):
    hl_lines = not app.raw_mode
    line_attr = app_get_pager_line_attr(app, line) if hl_lines else 0
    hl_urls = line_attr == 0 and hl_lines

    line = text_clean(line, ascii=app.ascii)

    app.screen.move(row, 0)
    app.screen.clrtoeol()
    app.screen.move(row, 0)

    for part in text_split_urls(line):
        is_url = URL_REX.fullmatch(part)
        part_attr = app.colors["url"] if is_url and hl_urls else line_attr
        app.screen.addstr(part, part_attr)


def app_render_pager(app):
    message = app.selected_message
    start = app.layout.pager_start
    height = app.layout.pager_height

    if message is None or start is None or height is None:
        return

    for i in range(height):
        line = list_get(message.lines, i + app.pager_offset, "~")
        app_render_pager_line(app, i + start, line)


def app_render_top_menu(app):
    lt = app.layout
    cols = lt.cols
    base_attr = curses.A_REVERSE if app.monochrome else curses.A_BOLD
    app.screen.insstr(lt.top_menu_row, 0, HELP_MENU[:cols].ljust(cols), app.colors["menu"] | base_attr)


def app_render_middle_menu(app):
    row = app.layout.middle_menu_row
    message = app.selected_message
    if row is None or message is None:
        return

    thread_message = app.messages_by_id.get(message.thread_id)
    if thread_message is None:
        return

    cols = app.layout.cols
    total = thread_message.total_comments
    unread = total - thread_message.read_comments

    text = "--({}/{} unread)".format(unread, total)
    if thread_message.flags.starred:
        text += "--(starred thread)"
    if app.raw_mode:
        text += "--(raw mode on)"
    text = text[:cols].ljust(cols, "-")

    base_attr = curses.A_REVERSE if app.monochrome else curses.A_BOLD
    app.screen.insstr(row, 0, text, app.colors["menu"] | base_attr)


def app_render_bottom_menu(app):
    lt = app.layout
    base_attr = curses.A_REVERSE if app.monochrome else curses.A_BOLD

    app.screen.chgat(lt.bottom_menu_row, 0, lt.cols, app.colors["menu"] | base_attr)
    app.screen.move(lt.bottom_menu_row, 0)

    for i, group in enumerate(GROUP_TABS):
        is_active = group.label == app.group.label
        item_attr = app.colors["menu_active"] | curses.A_BOLD if is_active else app.colors["menu"]
        item_attr = item_attr | base_attr
        app.screen.addstr("{}:{}".format(i+1, group.label), item_attr)
        app.screen.addstr("  ", app.colors["menu"] | base_attr)

    page_text = "page: {}".format(app.group.page)
    app.screen.insstr(lt.bottom_menu_row, lt.cols - len(page_text), page_text, app.colors["menu"] | base_attr)


def app_render(app):
    app_update_layout(app)
    app.screen.erase()
    app_render_index(app)
    app_render_pager(app)
    app_render_top_menu(app)
    app_render_middle_menu(app)
    app_render_bottom_menu(app)
    app.screen.insstr(app.layout.flash_menu_row, 0, app.flash or "")
    app.screen.refresh()


def app_init_colors(app):
    if app.monochrome:
        app.colors = defaultdict(lambda: 0)
        return

    try:
        curses.use_default_colors()
        for i, (name, (fg, bg)) in enumerate(COLORS.items()):
            curses.init_pair(i + 1, fg, bg)
            app.colors[name] = curses.color_pair(i + 1)
    except curses.error:
        app.colors = defaultdict(lambda: 0)
        app.monochrome = True


def app_main(screen, db, group, ascii, monochrome):
    curses.curs_set(0)

    app = AppState(screen=screen, db=db, group=group, ascii=ascii, monochrome=monochrome)

    app_init_colors(app)
    app_load_group(app, app.group)

    while True:
        app_render(app)
        app.flash = ""
        c = app.screen.getch()
        KEY_BINDINGS.get(c, cmd_unknown)(app)


def setup_logging(path):
    if path is None:
        return logging.disable(logging.CRITICAL)

    format = "%(asctime)s %(levelname)s: %(message)s"
    stream = sys.stderr if path == "-" else open(path, "a")
    logging.basicConfig(format=format, level="DEBUG", stream=stream)
    logging.debug("Session started")


def run_rcfile(path):
    path = os.path.expanduser(path)

    if not os.path.isfile(path):
        return

    code = compile(open(path).read(), path, "exec")
    exec(code, {"retronews": sys.modules[__name__]})


if __name__ == "__main__":
    tab_choices = range(1, len(GROUP_TABS) + 1)

    ap = argparse.ArgumentParser(
        formatter_class=lambda prog: argparse.ArgumentDefaultsHelpFormatter(prog, max_help_position=32)
    )
    ap.add_argument("--ascii", action="store_true", help="show only ascii characters")
    ap.add_argument("--monochrome", action="store_true", help="disable colors")
    ap.add_argument("-c", "--rcfile", metavar="PATH", default="~/.retronewsrc.py", help="optional startup code path")
    ap.add_argument("-d", "--db", metavar="PATH", default="~/.retronews.db", help="database path")
    ap.add_argument("-l", "--logfile", metavar="PATH", default=None, help="debug logfile path")
    ap.add_argument("-t", "--tab", metavar="TAB", type=int, default=1, choices=tab_choices, help="initial tab")
    ap.add_argument("-r", "--render", metavar="PATH", default=None, help="render raw html message and quit")
    ap.add_argument("-m", "--msg", metavar="URL", default=None, help="render message from URL")
    args = ap.parse_args()

    setup_logging(args.logfile)
    run_rcfile(args.rcfile)

    if args.render is not None:
        with open(args.render) as fp:
            print(html_render(fp.read()))
        sys.exit(0)

    try:
        db = db_init(args.db)

        if args.msg:
            group = group_for_msg_url(args.msg)
        else:
            group = GROUP_TABS[args.tab - 1]

        ascii = args.ascii
        monochrome = args.monochrome or "NO_COLOR" in os.environ

        ret = curses.wrapper(app_main, db=db, group=group, ascii=ascii, monochrome=monochrome)
    except ExitException as e:
        if e.message:
            sys.stderr.write(e.message + "\n")
        ret = e.code
    except BaseException as e:
        sys.stderr.write("\n".join(traceback.format_exception(type(e), e, e.__traceback__)))
        ret = 1
    finally:
        db.close()
        sys.exit(ret)
