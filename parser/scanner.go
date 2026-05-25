package parser

import (
	"bufio"
	"bytes"
	"io"
)

const (
	EOF = iota
	// kILLEGAL
)

// 	LABEL // letters/digits/_

// scanner is a lexical scanner.
type scanner struct {
	r         *bufio.Reader
	pos       TokenPos
	lastToken tok
}

// newScanner returns a new instance of Scanner.
func newScanner(r io.Reader) *scanner {
	return &scanner{r: bufio.NewReader(r), pos: TokenPos{Char: 0, Lines: []int{}}}
}

// read reads the next rune from the buffered reader.
// Returns the rune(0) if reached the end or error occurs.
func (s *scanner) read() rune {
	ch, _, err := s.r.ReadRune()
	if err != nil {
		return eof
	}
	if ch == '\n' {
		s.pos.Lines = append(s.pos.Lines, s.pos.Char)
		s.pos.Char = 0
	} else {
		s.pos.Char++
	}
	return ch
}

// unread places the previously read rune back on the reader.
func (s *scanner) unread() {
	_ = s.r.UnreadRune()
	if s.pos.Char == 0 {
		s.pos.Char = s.pos.Lines[len(s.pos.Lines)-1]
		s.pos.Lines = s.pos.Lines[:len(s.pos.Lines)-1]
	} else {
		s.pos.Char--
	}
}

// Scan returns the next token and parsed value.
func (s *scanner) Scan() (token tok, value string, startPos, endPos TokenPos) {
	ch := s.read()

	if isWhitespace(ch) {
		s.skipWhitespace()
		ch = s.read()
	}

	// Track token positions.
	startPos = s.pos
	defer func() { endPos = s.pos }()

	switch ch {
	case eof:
		s.lastToken = 0
		return 0, "", startPos, endPos
	case '>':
		s.lastToken = RANGLE
		return RANGLE, string(ch), startPos, endPos
	case '(':
		s.lastToken = LPAREN
		return LPAREN, string(ch), startPos, endPos
	case ')':
		s.lastToken = RPAREN
		return RPAREN, string(ch), startPos, endPos
	case '[':
		s.lastToken = LSBRACK
		return LSBRACK, string(ch), startPos, endPos
	case ']':
		s.lastToken = RSBRACK
		return RSBRACK, string(ch), startPos, endPos
	case '{':
		s.lastToken = LCBRACK
		return LCBRACK, string(ch), startPos, endPos
	case '}':
		s.lastToken = RCBRACK
		return RCBRACK, string(ch), startPos, endPos
	case '.':
		s.lastToken = DOT
		return DOT, string(ch), startPos, endPos
	case ';':
		s.lastToken = SEQUENCE
		return SEQUENCE, string(ch), startPos, endPos
	case ':':
		s.lastToken = COLON
		return COLON, string(ch), startPos, endPos
	case '|':
		s.lastToken = PIPE
		return PIPE, string(ch), startPos, endPos
	case ',':
		s.lastToken = COMMA
		return COMMA, string(ch), startPos, endPos
	case '+':
		s.lastToken = PLUS
		return PLUS, string(ch), startPos, endPos
	case '*':
		s.lastToken = TIMES
		return TIMES, string(ch), startPos, endPos
	case '&':
		s.lastToken = AMPERSAND
		return AMPERSAND, string(ch), startPos, endPos
	case '%':
		s.lastToken = PERCENTAGE
		return PERCENTAGE, string(ch), startPos, endPos
	case '@':
		s.lastToken = AT
		return AT, string(ch), startPos, endPos
	}

	if s.consumeIfComment(ch) {
		return s.Scan()
	}

	if isSpecialSymbol(ch) {
		// s.unread()
		return s.scanSpecialSymbol(ch)
	}

	// this is placed before the condition which scans a label to ensure that integer values are not treated as labels
	if isDigit(ch) {
		return s.scanInteger(ch)
	}

	if isAlphaNum(ch) || isUnderscore(ch) || isApostrophe(ch) {
		// s.unread()
		return s.scanLabel(ch)
	}

	return kILLEGAL, string(ch), startPos, endPos
}

func (s *scanner) scanInteger(ch rune) (token tok, value string, startPos, endPos TokenPos) {
	var buf bytes.Buffer
	startPos = s.pos
	defer func() { endPos = s.pos }()
	buf.WriteRune(ch)

	for {
		ch := s.read()
		if isDigit(ch) {
			_, _ = buf.WriteRune(ch)
		} else {
			s.unread()
			break
		}
	}

	s.lastToken = NAT
	return NAT, buf.String(), startPos, endPos
}

// Scan label or keyword
func (s *scanner) scanLabel(ch rune) (token tok, value string, startPos, endPos TokenPos) {
	var buf bytes.Buffer
	startPos = s.pos
	defer func() { endPos = s.pos }()
	buf.WriteRune(ch)

	for {
		if ch := s.read(); ch == eof {
			break
		} else if !isAlphaNum(ch) && !isUnderscore(ch) && !isApostrophe(ch) {
			s.unread()
			break
		} else {
			_, _ = buf.WriteRune(ch)
		}
	}

	switch buf.String() {
	case "send":
		s.lastToken = SEND
		return SEND, buf.String(), startPos, endPos
	case "recv":
		s.lastToken = RECEIVE
		return RECEIVE, buf.String(), startPos, endPos
	case "receive":
		s.lastToken = RECEIVE
		return RECEIVE, buf.String(), startPos, endPos
	case "case":
		s.lastToken = CASE
		return CASE, buf.String(), startPos, endPos
	case "close":
		s.lastToken = CLOSE
		return CLOSE, buf.String(), startPos, endPos
	case "wait":
		s.lastToken = WAIT
		return WAIT, buf.String(), startPos, endPos
	case "cast":
		s.lastToken = CAST
		return CAST, buf.String(), startPos, endPos
	case "shift":
		s.lastToken = SHIFT
		return SHIFT, buf.String(), startPos, endPos
	case "accept":
		s.lastToken = ACCEPT
		return ACCEPT, buf.String(), startPos, endPos
	case "acc":
		s.lastToken = ACCEPT
		return ACCEPT, buf.String(), startPos, endPos
	case "acquire":
		s.lastToken = ACQUIRE
		return ACQUIRE, buf.String(), startPos, endPos
	case "acq":
		s.lastToken = ACQUIRE
		return ACQUIRE, buf.String(), startPos, endPos
	case "detach":
		s.lastToken = DETACH
		return DETACH, buf.String(), startPos, endPos
	case "det":
		s.lastToken = DETACH
		return DETACH, buf.String(), startPos, endPos
	case "release":
		s.lastToken = RELEASE
		return RELEASE, buf.String(), startPos, endPos
	case "rel":
		s.lastToken = RELEASE
		return RELEASE, buf.String(), startPos, endPos
	case "drop":
		s.lastToken = DROP
		return DROP, buf.String(), startPos, endPos
	case "split":
		s.lastToken = SPLIT
		return SPLIT, buf.String(), startPos, endPos
	case "push":
		s.lastToken = PUSH
		return PUSH, buf.String(), startPos, endPos
	case "new":
		s.lastToken = NEW
		return NEW, buf.String(), startPos, endPos
	case "spawn":
		s.lastToken = SPAWN
		return SPAWN, buf.String(), startPos, endPos
	case "snew":
		s.lastToken = SNEW
		return SNEW, buf.String(), startPos, endPos
	case "forward":
		s.lastToken = FORWARD
		return FORWARD, buf.String(), startPos, endPos
	case "fwd":
		s.lastToken = FORWARD
		return FORWARD, buf.String(), startPos, endPos
	case "type":
		s.lastToken = TYPE
		return TYPE, buf.String(), startPos, endPos
	case "def":
		s.lastToken = DEF
		return DEF, buf.String(), startPos, endPos
	case "let":
		s.lastToken = LET
		return LET, buf.String(), startPos, endPos
	case "nat":
		s.lastToken = NAT_TYPE
		return NAT_TYPE, buf.String(), startPos, endPos
	case "in":
		s.lastToken = IN
		return IN, buf.String(), startPos, endPos
	case "end":
		s.lastToken = END
		return END, buf.String(), startPos, endPos
	case "sprc":
		s.lastToken = SPRC
		return SPRC, buf.String(), startPos, endPos
	case "prc":
		s.lastToken = PRC
		return PRC, buf.String(), startPos, endPos
	case "self":
		s.lastToken = SELF
		return SELF, buf.String(), startPos, endPos
	case "assuming":
		s.lastToken = ASSUMING
		return ASSUMING, buf.String(), startPos, endPos
	case "exec":
		s.lastToken = EXEC
		return EXEC, buf.String(), startPos, endPos
	case "print":
		// Debug keyword
		s.lastToken = PRINT
		return PRINT, buf.String(), startPos, endPos
	case "sync":
		s.lastToken = SYNC
		return SYNC, buf.String(), startPos, endPos
	case "boom":
		s.lastToken = BOOM
		return BOOM, buf.String(), startPos, endPos
	case "boom_in":
		s.lastToken = BOOM_IN
		return BOOM_IN, buf.String(), startPos, endPos
	}
	s.lastToken = LABEL
	return LABEL, buf.String(), startPos, endPos
}

func (s *scanner) skipWhitespace() {
	for {
		if ch := s.read(); ch == eof {
			break
		} else if !isWhitespace(ch) {
			s.unread()
			break
		}
	}
}

// Consumes line comments (//...) or multiline comments (/*...*/)
func (s *scanner) consumeIfComment(ch rune) bool {
	if ch == '/' {
		if ch = s.read(); ch == '/' {
			s.skipToEOL()
			return true
		} else if ch == '*' {
			s.skipToEndOfComment()
			return true
		} else {
			s.unread()
		}
		// s.unread()
	}
	// Not a comment, so do nothing
	return false
}

func (s *scanner) skipToEndOfComment() {
	for {
		if ch := s.read(); ch == '*' {
			for {
				if ch := s.read(); ch == '/' {
					return
				}
			}
		}
	}
}

func (s *scanner) skipToEOL() {
	for {
		if ch := s.read(); ch == '\n' || ch == eof {
			break
		}
	}
}

// Some commands are multi-character. So, they have to be check explicitly
func isSpecialSymbol(ch rune) bool {
	return ch == '=' || ch == '<' || ch == '-' || ch == '1' || ch == '/' || ch == '\\'
}

func (s *scanner) scanSpecialSymbol(ch rune) (token tok, value string, startPos, endPos TokenPos) {
	startPos = s.pos
	defer func() { endPos = s.pos }()
	// ch := s.read()
	ch2 := s.read()

	switch ch {
	case '=':
		// Can be = or =>
		if ch2 == '>' {
			// is =>
			s.lastToken = RIGHT_ARROW
			return RIGHT_ARROW, "=>", startPos, endPos
		} else {
			// is just =
			s.unread()
			s.lastToken = EQUALS
			return EQUALS, "=", startPos, endPos
		}
	case '<':
		// Can be < or <-
		if ch2 == '-' {
			// is <-
			s.lastToken = LEFT_ARROW
			return LEFT_ARROW, "<-", startPos, endPos
		} else {
			// is just <
			s.unread()
			s.lastToken = LANGLE
			return LANGLE, "<", startPos, endPos
		}
	case '-':
		// Can be - or -* (or -o)
		if ch2 == '*' {
			// is -o
			s.lastToken = LOLLI
			return LOLLI, "-*", startPos, endPos
		} else if ch2 == 'o' {
			// is -o
			s.lastToken = LOLLI
			return LOLLI, "-o", startPos, endPos
		} else if isAlphaNum(ch2) {
			s.unread()
			return s.scanLabel(ch)
		} else {
			// is just -
			s.unread()
			s.lastToken = MINUS
			return MINUS, "-", startPos, endPos
		}
	case '1':
		if s.lastToken == EQUALS || s.lastToken == AT {
			s.unread()
			return s.scanInteger(ch)
		} else if isAlphaNum(ch2) || isUnderscore(ch2) || isApostrophe(ch2) {
			// is a label
			s.unread()
			return s.scanLabel(ch)
		} else {
			// is just 1
			s.unread()
			s.lastToken = UNIT
			return UNIT, "1", startPos, endPos
		}
	case '\\':
		// Should be \/
		if ch2 == '/' {
			s.lastToken = DOWN_ARROW
			return DOWN_ARROW, "\\/", startPos, endPos
		}
	case '/':
		// Should be /\
		if ch2 == '\\' {
			s.lastToken = UP_ARROW
			return UP_ARROW, "/\\", startPos, endPos
		}
	}
	// Not one of the special commands
	s.lastToken = kILLEGAL
	return kILLEGAL, string(ch), startPos, endPos
}
