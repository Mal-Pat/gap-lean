/-
Copyright (c) 2026 Malhar A. Patel. All rights reserved.
Authors: Malhar A. Patel
-/

namespace GapLean.Ast

/-- Binary operators -/
inductive BinOp where
  | or | and
  | eq | ne | lt | le | gt | ge
  | mem
  | add | sub | mul | div | mod | pow
  deriving Repr, BEq, Hashable, Inhabited

/-- Unary operators -/
inductive UnOp where
  | not | neg | plus
  deriving Repr, BEq, Hashable, Inhabited

mutual

#check Float

/-- GAP expressions -/
inductive Expr where
  | int     (n : Nat)
  | float   (raw : String)
  | str     (s : String)
  | chr     (c : Char)
  | bool    (b : Bool)
  | var     (name : String)
  | tilde
  | binop   (op : BinOp) (a b : Expr)
  | unop    (op : UnOp) (a : Expr)
  | call    (fn : Expr) (args : Array Expr) (opts : Array (String × Option Expr))
  | index   (l : Expr) (idx : Array Expr)              -- l[i], m[i,j]
  | sublist (l : Expr) (idx : Expr)                    -- l{idx}
  | field   (r : Expr) (name : FieldSel)               -- r.x, r.(e)
  | list    (elems : Array (Option Expr))              -- holes ([1,,3]) are `none`
  | range   (first : Expr) (second? : Option Expr) (last : Expr)  -- [a..b], [a,s..b]
  | record  (fields : Array (FieldSel × Expr))         -- rec(a := 1, (e) := 2)
  | perm    (cycles : Array (Array Expr))              -- (1,2,3)(4,5); #[] = ()
  | lambda  (params : Array String) (body : Expr)      -- x -> e, {x,y} -> e
  | func    (params : Array String) (variadic : Bool)
            (locals : Array String) (body : Array Stmt)
  | isBound (lv : LValue)                              -- IsBound(lv)
  | raw     (gapSource : String)

/-- Record field selectors: `r.name` or computed `r.(expr)` -/
inductive FieldSel where
  | named    (s : String)
  | computed (e : Expr)

/-- Assignment targets -/
inductive LValue where
  | var     (name : String)
  | index   (base : LValue) (idx : Array Expr)
  | sublist (base : LValue) (idx : Expr)
  | field   (base : LValue) (name : FieldSel)

/-- GAP statements -/
inductive Stmt where
  | assign   (lhs : LValue) (rhs : Expr)
  | exprStmt (e : Expr)
  | «if»     (branches : Array (Expr × Array Stmt)) (els : Option (Array Stmt))
  | «while»  (cond : Expr) (body : Array Stmt)
  | «repeat» (body : Array Stmt) (until_ : Expr)
  | «for»    (var : String) (iter : Expr) (body : Array Stmt)
  | ret      (e : Option Expr)                         -- return; / return e;
  | «break»
  | «continue»
  | unbind   (lv : LValue)                             -- Unbind(lv)
  | empty                                              -- bare `;`

end

/-- A parsed GAP program as a sequence of statements -/
abbrev Prog := Array Stmt

/-- View an expression as an assignment target -/
partial def Expr.toLValue? : Expr → Option LValue
  | .var n        => some (.var n)
  | .index l i    => do return .index (← l.toLValue?) i
  | .sublist l i  => do return .sublist (← l.toLValue?) i
  | .field r n    => do return .field (← r.toLValue?) n
  | _             => none

/-- Reserved words of GAP -/
def keywords : List String :=
  ["and", "atomic", "break", "continue", "do", "elif", "else", "end", "false",
   "fi", "for", "function", "if", "in", "local", "mod", "not", "od", "or",
   "quit", "QUIT", "readonly", "readwrite", "rec", "repeat", "return", "then",
   "true", "until", "while"]

end GapLean.Ast
