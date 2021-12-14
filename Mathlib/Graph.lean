import Mathlib

open Lean Elab Tactic Meta Std
open Elab.Tactic Core

namespace SMap

variable {α β γ : Type _} [BEq α] [Hashable α]
-- If I go via `List (α × β)` Lean crashes with an error (stack overflow?)
def mapToRBMap (m : SMap α β) {cmp : α → α → Ordering} (f : β → γ) : RBMap α γ cmp :=
  m.fold (init := ∅) fun es a b => es.insert a (f b)

end SMap

-- namespace Lean.ConstMap
-- def toNameSet (m : ConstMap) : NameSet :=
--   SMap.mapToRBMap m λ _ => ()
-- end Lean.ConstMap

namespace Lean.Environment

def find! (e : Environment) (nm : Name) : ConstantInfo := (e.find? nm).get!

end Lean.Environment

namespace Std.RBMap

variable {α β : Type _} { cmp : α → α → Ordering}
def filter (t : RBMap α β cmp) (f : α → β → Bool) : RBMap α β cmp :=
  t.fold (init := ∅) fun es a b => match f a b with
  | true  => es.insert a b
  | false => es

-- where might be a more efficient way to do this using `RBNode.append`
def union (t₁ t₂ : RBMap α β cmp) : RBMap α β cmp :=
  t₂.fold (init := t₁) fun t a b => t.insert a b

def mapValue (t : RBMap α β cmp) (f : β → γ) : RBMap α γ cmp :=
t.fold (λ t' x y => t'.insert x (f y)) ∅

end Std.RBMap

namespace Std
/-- a variant of RBMaps that stores a list of elements for each key.
   `find` returns the list of elements in the opposite order that they were inserted. -/
def RBLMap (α β : Type _) (cmp : α → α → Ordering) : Type _ := RBMap α (List β) cmp

@[inline] def mkRBLMap (α : Type) (β : Type) (cmp : α → α → Ordering) : RBLMap α β cmp :=
mkRBMap α (List β) cmp

namespace RBLMap

variable {α β : Type _} {cmp : α → α → Ordering}

def insert (t : RBLMap α β cmp) (x : α) (y : β) : RBLMap α β cmp :=
match t.find? x with
| none   => RBMap.insert t x [y]
| some l => RBMap.insert (t.erase x) x (y :: l)

def erase (t : RBLMap α β cmp) (k : α) : RBLMap α β cmp :=
RBMap.erase t k

def contains (t : RBLMap α β cmp) (k : α) : Bool :=
RBMap.contains t k

def find (t : RBLMap α β cmp) (k : α) : List β :=
(RBMap.find? t k).getD []

end RBLMap

def NameLMap (β : Type _) := RBLMap Name β Name.quickCmp

instance (β : Type _) : EmptyCollection (NameLMap β) := ⟨mkNameMap _⟩

end Std

namespace Lean.Expr

/-- The names occurring in an expression. -/
def listNames (e : Expr) : NameSet :=
e.foldConsts ∅ λ nm nms => nms.insert nm

end Lean.Expr

namespace Array

def positions {α : Type _} (a : Array α) (cmp : α → α → Ordering) : RBMap α ℕ cmp :=
(a.zip $ range a.size).foldl (λ t (x, n) => t.insert x n) ∅

def sum (a : Array Float) : Float :=
a.foldr (·+·) 0

def take {α : Type _} [Inhabited α] (a : Array α) (n : ℕ) : Array α :=
if a.size ≤ n then a else (range n).map (a.get! ·)

end Array

namespace Lean.ConstantInfo

/-- The names referred to in the type.-/
def typeRefs (info : ConstantInfo) : NameSet :=
info.type.listNames

/-- The names referred to in the value of the expression.-/
def valueRefs (info : ConstantInfo) : NameSet :=
(info.value?.map λ e => e.listNames).getD ∅

/-- The names referred to in the expression. -/
def anyRefs (info : ConstantInfo) : NameSet :=
info.typeRefs.union info.valueRefs

end Lean.ConstantInfo

def isInteresting (nm : Name) (info : ConstantInfo) : Bool :=
!(nm.isInternal || info.isUnsafe)

/- by Gabriel -/
def getDeclsInCurrModule : CoreM (Array Name) := do
  (← getEnv).constants.map₂.toList.toArray.map (·.1)

/- by Gabriel -/
def getAllDecls : CoreM (Array Name) := do
  (← getDeclsInCurrModule) ++
    (← getEnv).constants.map₁.toArray.map (·.1)

/- by Gabriel -/
def getDeclsInMathlib : CoreM (Array Name) := do
  let mut decls ← getDeclsInCurrModule
  let mathlibModules := (← getEnv).header.moduleNames.map ((`Mathlib).isPrefixOf ·)
  for (declName, moduleIdx) in (← getEnv).const2ModIdx.toArray do
    if mathlibModules[moduleIdx] then
      decls := decls.push declName
  decls

def interestingDecls : CoreM (Array Name) := do
  let env ← getEnv
  (← getAllDecls).filter λ nm => isInteresting nm $ env.find! nm

def interestingDeclTree : CoreM (NameLMap Name) := do
let e ← getEnv
let interestingDeclsList := (SMap.mapToRBMap e.constants id).filter isInteresting
interestingDeclsList.mapValue λ info => info.anyRefs.toList

def transpose (t : NameLMap Name) : NameLMap Name :=
t.fold (λ tnew nm_src l => l.foldl (λ tnew nm_tgt => tnew.insert nm_tgt nm_src) tnew) ∅

/-- Edges point from a declaration `d` to all declarations occurring in `d`. -/
structure NameNode where
  name : Name
  outEdges : Array ℕ
  inEdges : Array ℕ
  weight : Float
deriving Inhabited

instance : ToString NameNode :=
⟨λ nn => "⟨" ++ toString nn.name ++ ", using " ++ toString nn.outEdges.size ++ ", used by " ++ toString nn.inEdges.size ++
  ", " ++ toString nn.weight ++ "⟩"⟩

protected def List.toStringSepAux {α : Type u} [ToString α] (sep : String := ", ") :
  Bool → List α → String
  | b,     []    => ""
  | true,  x::xs => toString x ++ List.toStringSepAux sep false xs
  | false, x::xs => sep ++ toString x ++ List.toStringSepAux sep false xs

protected def List.toStringSep {α : Type u} [ToString α] (sep : String := ", ") : List α → String
  | []    => "[]"
  | x::xs => "[" ++ List.toStringSepAux sep true (x::xs) ++ "]"

instance [ToString α] : ToString (Array α) where
  toString a := "!#" ++ a.toList.toStringSep ",\n"

/- TODO: currently we ignore all non-interesting declarations occurring in interesting declarations.
For _proof_i and _eqn_i declarations, it would be better to point at the corresponding interesting decl -/

def NameGraph := Array NameNode
deriving Inhabited


-- #print Array.get?
def mkNameGraph : CoreM NameGraph := do
  let l ← interestingDecls
  let env ← getEnv
  let pos : NameMap ℕ := l.positions _
  let inEdges ← transpose <$> interestingDeclTree
  return l.map λ nm => ⟨nm, (env.find! nm).anyRefs.toArray.filterMap pos.find?,
    (inEdges.find nm).toArray.filterMap pos.find?, (1 : Float) / Float.ofNat l.size⟩

def inEdgeNames (g : NameGraph) (nn : NameNode) : Array Name :=
nn.inEdges.map λ n => g[n].name

def outEdgeNames (g : NameGraph) (nn : NameNode) : Array Name :=
nn.outEdges.map λ n => g[n].name

-- def nodesWithNoOutEdges (g : NameGraph) : List ℕ :=

def weightWithNoOutEdges (g : NameGraph) : Float :=
g.foldr (λ nn s => if nn.outEdges.isEmpty then s + nn.weight else s) 0

def totalWeight (g : NameGraph) : Float :=
g.foldr (λ nn s => s + nn.weight) 0

/--
Every step, `w(A)`, the weight of node `A` is changed to
`(1 - d) / N + d ∑_B w(B) / L(B)`
where:
* `d` is the damping factor
* `N` is the size of the graph
* we sum over all nodes `B` that has a edge to `A`
* `L(B)` is the number of outgoing edges out of `B`.
-/
def step (g : NameGraph) (dampingFactor : Float := 0.85) : NameGraph :=
let w := weightWithNoOutEdges g
g.map λ nn => { nn with weight :=
  (1 - dampingFactor + w * dampingFactor) / Float.ofNat g.size +
  dampingFactor * (nn.inEdges.foldr (λ n s => s + g[n].weight / Float.ofNat g[n].outEdges.size) 0) }

def sortByName (g : NameGraph) : NameGraph :=
g.qsort λ nn1 nn2 => nn1.name.quickCmp nn2.name == Ordering.lt

def sortRevByWeight (g : NameGraph) : NameGraph :=
g.qsort λ nn1 nn2 => nn1.weight > nn2.weight

/-
graph currently has 27035 nodes

after 1 step, top weights:
#[Nat, Eq, Lean.Name, Bool, Array, Lean.Expr, OfNat.ofNat, String, Option, instOfNatNat]
Nat's weight is 0.029

-/

def test (printNum : ℕ := 10) (iter : ℕ := 5) (sort? : Bool := true) : CoreM Unit := do
  let env ← getEnv
  let g ← mkNameGraph
  if iter > 0 then
    let g := iter.iterate step g
    if sort? then
      let g := sortRevByWeight g
      -- IO.println $ (g.take printNum).map (·.name)
      IO.println $ "After iterating " ++ toString iter ++ " times, the " ++ toString printNum ++
        " entries with the highest weight:"
      IO.println $ g.take printNum
    else
      IO.println $ "After iterating " ++ toString iter ++ " times, the same entries:"
      IO.println $ g.take printNum
  else
    IO.println $ toString printNum ++ " entries from the graph:"
    IO.println $ g.take printNum

  -- let g := step g
  -- let nr := 22313
  -- IO.println $ g[nr]
  -- -- IO.println $ (g[nr].weight * (Float.ofNat g.size))
  -- -- IO.println $ (g[nr].name)
  -- -- IO.println $ (env.find! g[nr].name).anyRefs.toList
  -- -- IO.println $ (outEdgeNames g g[nr])
  -- -- IO.println $ (inEdgeNames g g[nr])
  -- let nr := 20827
  -- IO.println $ (g[nr])
  -- let nr := 12341
  -- IO.println $ (g[nr])
  -- IO.println $ (g[nr].weight * (Float.ofNat g.size))
  return ()
-- set_option profiler true
-- #print importModules
-- #exit
-- #eval test 1000 10
-- #eval 1
-- #print UInt64.ofNatCore

-- #print IO.Error
def main (strs : List String) : IO UInt32 := do
  initSearchPath (← Lean.findSysroot?) ["build/lib"]
  let env ← importModules [{module := `Mathlib}] {}
  let args := (strs.map String.toNat!).toArray
  -- IO.println args
  let u ← CoreM.toIO (test (args.getD 0 10) (args.getD 1 5) (args.getD 2 0 == 0)) {} {env := env}
  -- let u ← CoreM.toIO test {} {env := env}
  return 0
