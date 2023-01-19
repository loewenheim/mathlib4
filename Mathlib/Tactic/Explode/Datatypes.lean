import lean
import Lean.Meta.Basic

open Lean Elab
open Std
set_option linter.unusedVariables false

namespace Mathlib.Explode

inductive Status where
  | reg    : Status
  | intro  : Status
  | lam    : Status
  | sintro : Status
deriving Inhabited

inductive Thm where
  | expr   : Expr   → Thm
  | name   : Name   → Thm
  | string : String → Thm

def Thm.toString : Thm → String
  | (Thm.expr e) => Expr.dbgToString e
  | (Thm.name n) => n.toString
  | (Thm.string s) => s

structure Entry where
  expr   : Expr
  type   : Expr
  line   : Nat
  depth  : Nat
  status : Status
  thm    : Thm
  deps   : List Nat
  context: MessageDataContext

instance : ToString Entry where
  toString en := s!"expr: {en.expr}, line: {en.line}, thm: {en.thm.toString}"

--- Instead of simply keeping a list of entries (List Entry), we create a datatype Entries.
structure Entries : Type :=
  -- allows us to compare Exprs fast
  (s : ExprMap Entry)
  -- is a simple list of Exprs
  (l : List Entry)
deriving Inhabited

def Entries.find (es : Entries) (e : Expr) : Option Entry :=
  es.s.find? e
def Entries.size (es : Entries) : Nat :=
  es.s.size
-- TODO: why do we need to compare exprs though (for `match (f, args) with` case, but explore why exactly)
def Entries.add : Entries → Entry → Entries
  | entries@⟨s, l⟩, entry =>
    if s.contains entry.expr
      then entries
      else ⟨s.insert entry.expr entry, entry :: l⟩
    -- ⟨s.insert entry.expr entry, entry :: l⟩
def Entries.head (es : Entries) : Option Entry :=
  es.l.head?

-- Examples

-- 3. Expression λ x, 1 + x
def lam1plusx :=
  Expr.lam `x (Expr.const `Nat [])
  (Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 1, Expr.bvar 0])
  BinderInfo.default

-- def myEntry : Entry := {
--   -- λ (hP : p) => hP
--   expr   := lam1plusx, -- mkAppN (Expr.const `Nat.add []) #[mkNatLit 1, mkNatLit 2],
--   line   := 15,
--   depth  := 0,
--   status := Status.reg,
--   thm    := Thm.string "my_theorem",
--   deps   := [1, 2, 3],
--   context := { env := (← getEnv), mctx := {}, lctx := (← read).lctx, opts := {} }
-- }

-- def myEntry2 : Entry := {
--   expr   := mkAppN (Expr.const `Nat.add []) #[mkNatLit 666, mkNatLit 666],
--   line   := 15,
--   depth  := 0,
--   status := Status.reg,
--   thm    := Thm.string "my_theorem",
--   deps   := [1, 2, 3]
-- }

def entriesDefault : Entries := default
