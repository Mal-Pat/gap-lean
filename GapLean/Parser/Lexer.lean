/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Authors: Malhar A. Patel
-/

import GapLean.Ast

namespace GapLean.Parser

inductive Tok where
  | ident (s : String)          -- a name the user chooses
  | kw    (s : String)          -- reserved word
  | int   (n : Nat)
  | float (raw : String)
  | str   (s : String)
  | chr   (c : Char)
  | sym   (s : String)          -- operator/punctuation
  | eof                         -- end of input
  deriving Repr, BEq, Inhabited

/-- A token with its character offset (for error messages). -/
structure Token where
  tok : Tok
  pos : Nat
  deriving Repr, Inhabited

/-- Render a token kind (for error messages). -/
def Tok.describe : Tok → String
  | .ident s => s!"identifier '{s}'"
  | .kw s    => s!"keyword '{s}'"
  | .int n   => s!"integer {n}"
  | .float s => s!"float {s}"
  | .str _   => "string literal"
  | .chr _   => "char literal"
  | .sym s   => s!"'{s}'"
  | .eof     => "end of input"

/-- Render a character offset as `line:col` for error messages. -/
def lineCol (src : String) (pos : Nat) : String := Id.run do
  let mut line := 1
  let mut col := 1
  let mut i := 0
  for c in src.toList do
    if i == pos then break
    if c == '\n' then line := line + 1; col := 1 else col := col + 1
    i := i + 1
  return s!"{line}:{col}"

/-- The character at offset `i`, or NUL (`'\x00'`) if `i` is past the end. -/
private def peek (cs : Array Char) (i : Nat) : Char :=
  cs.getD i '\x00'

private def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n'

/-- The characters that can appear inside an identifier.
(The first character is more restricted - it cannot be a digit) -/
private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '@'

/-- Resolve an escape char `\c` for some char `c` -/
private def escChar (c : Char) : Char :=
  match c with
  | 'n' => '\n' | 't' => '\t' | 'r' => '\r' | 'b' => '\x08' | 'c' => '\x03'
  | _   => c    -- anything else is the char itself (like `\\`, `\"`, and `\'`)

/-- Skip a `#`-comment up till the end of line `\n` -/
private def skipComment (cs : Array Char) (start : Nat) : Nat := Id.run do
  let mut i := start
  while i < cs.size && peek cs i != '\n' do
    i := i + 1
  return i

/-- Obtain an identifier or keyword starting at `start` (a letter, `_`, `@`, or
`\`).

In GAP, a backslash quotes the next character into the identifier.
This lets a name coincide with a reserved word. -/
private def lexIdent (cs : Array Char) (start : Nat) : Except String (Token × Nat) := do
  let n := cs.size
  let mut i := start
  if peek cs i == '\\' then i := i + 1        -- quoted first char
  let mut s := ""
  while i < n && (isIdentChar (peek cs i) || peek cs i == '\\') do
    if peek cs i == '\\' then
      i := i + 1                              -- skip the quoting backslash…
      if i < n then
        s := s.push (peek cs i)               -- …and take the next char verbatim
        i := i + 1
    else
      s := s.push (peek cs i)
      i := i + 1
  if s.isEmpty then
    throw s!"lex error at offset {start}: dangling '\\'"
  let isQuoted := peek cs start == '\\'
  if !isQuoted && Ast.keywords.contains s then
    return (⟨.kw s, start⟩, i)
  else
    return (⟨.ident s, start⟩, i)

/-- Obtain a number starting at `start`.

When the digits are followed by `.` we must look further
to decide which of these cases it is:

* `1.5` or `1.5e-3` — a float; return the float
* `[1..5]` — a range; return `1`
* `1.next` — field access; return `1`

Scanning a number cannot fail, hence no `Except` in the type. -/
private def lexNumber (cs : Array Char) (start : Nat) : Token × Nat := Id.run do
  let n := cs.size
  let mut i := start
  let mut value : Nat := 0
  let mut raw := ""
  while i < n && (peek cs i).isDigit do
    value := value * 10 + ((peek cs i).toNat - '0'.toNat)
    raw := raw.push (peek cs i)
    i := i + 1
  if peek cs i == '.' && (peek cs (i+1)).isDigit then
    raw := raw.push '.'
    i := i + 1
    let mut prevExp := false   -- was the previous char `e` or `E`
    while i < n && ((peek cs i).isDigit || peek cs i == 'e' || peek cs i == 'E'
                    || (prevExp && (peek cs i == '+' || peek cs i == '-'))) do
      prevExp := peek cs i == 'e' || peek cs i == 'E'
      raw := raw.push (peek cs i)
      i := i + 1
    return (⟨.float raw, start⟩, i)
  return (⟨.int value, start⟩, i)

/-- Obtain a string starting at `start` (a `"`).

There are two forms:

* triple-quoted `"""…"""` raw strings
* ordinary `"…"` strings

The token's payload is the string contents with quotes stripped. -/
private def lexString (cs : Array Char) (start : Nat) : Except String (Token × Nat) := do
  let n := cs.size
  if peek cs (start+1) == '"' && peek cs (start+2) == '"' then
    -- triple-quoted raw string
    let mut i := start + 3
    let mut s := ""
    while i < n do
      if peek cs i == '"' && peek cs (i+1) == '"' && peek cs (i+2) == '"' then
        return (⟨.str s, start⟩, i + 3)
      s := s.push (peek cs i)
      i := i + 1
    throw s!"lex error at offset {start}: unterminated triple-quoted string"
  else
    -- ordinary string
    let mut i := start + 1
    let mut s := ""
    while i < n do
      let d := peek cs i
      if d == '"' then
        return (⟨.str s, start⟩, i + 1)
      else if d == '\\' && i + 1 < n then
        if peek cs (i+1) != '\n' then
          s := s.push (escChar (peek cs (i+1)))
        i := i + 2
      else if d == '\n' then
        throw s!"lex error at offset {start}: newline in string literal"
      else
        s := s.push d
        i := i + 1
    throw s!"lex error at offset {start}: unterminated string"

/-- Obtain a char literal starting at `start` (a `'`) -/
private def lexChar (cs : Array Char) (start : Nat) : Except String (Token × Nat) := do
  let mut i := start + 1
  let mut ch := peek cs i
  if ch == '\\' && i + 1 < cs.size then
    ch := escChar (peek cs (i+1))
    i := i + 2
  else
    i := i + 1
  if peek cs i == '\'' then
    return (⟨.chr ch, start⟩, i + 1)
  throw s!"lex error at offset {start}: unterminated char literal"

/-- The multi-character operators, with the longest first. -/
private def multiCharSyms : List String :=
  ["...", ":=", "<=", ">=", "<>", "..", "->", "!.", "![", "!{"]

/-- Check if the characters starting at offset `i` spell out `s` -/
private def matchesAt (cs : Array Char) (i : Nat) (s : String) : Bool := Id.run do
  let mut k := 0
  for c in s.toList do
    if peek cs (i + k) != c then return false
    k := k + 1
  return true

/-- The single-character operators and punctuation. -/
private def singleCharSyms : String := "+-*/^=<>()[]{},;:.!~"

/-- Obtain an operator/punctuation symbol starting at `start`. -/
private def lexSymbol (cs : Array Char) (start : Nat) : Except String (Token × Nat) :=
  match multiCharSyms.find? (matchesAt cs start) with
  | some s => .ok (⟨.sym s, start⟩, start + s.length)
  | none   =>
    let c := peek cs start
    if singleCharSyms.contains c then
      .ok (⟨.sym c.toString, start⟩, start + 1)
    else
      .error s!"lex error at offset {start}: unexpected character '{c}'"

/-- Tokenize GAP source.  Returns the token array or an error message.

* space/tab/newline → skipped;
* `#`               → `skipComment` (to end of line);
* letter, `_`, `@`, `\` → `lexIdent` (identifier or keyword);
* digit             → `lexNumber` (integer or float);
* `"`               → `lexString`;
* `'`               → `lexChar`;
* anything else     → `lexSymbol`, or a lex error if unrecognized.

A final `eof` token is appended at the end. -/
def lex (src : String) : Except String (Array Token) := do
  let cs : Array Char := src.toList.toArray
  let n := cs.size
  let mut out : Array Token := #[]
  let mut i := 0
  while i < n do
    let c := peek cs i
    if isWhitespace c then
      i := i + 1
    else if c == '#' then
      i := skipComment cs i
    else
      let (tok, next) ←
        if c.isAlpha || c == '_' || c == '@' || c == '\\' then
          lexIdent cs i
        else if c.isDigit then
          pure (lexNumber cs i)
        else if c == '"' then
          lexString cs i
        else if c == '\'' then
          lexChar cs i
        else
          lexSymbol cs i
      out := out.push tok
      i := next
  out := out.push ⟨.eof, n⟩
  return out

end GapLean.Parser
