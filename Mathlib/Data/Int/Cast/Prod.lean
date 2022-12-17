/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Prod

/-!
# The product of two `AddGroupWithOne`s.
-/


namespace Prod

variable {α β : Type _} [AddGroupWithOne α] [AddGroupWithOne β]

instance : AddGroupWithOne (α × β) :=
  { Prod.instAddMonoidWithOneProd, Prod.instAddGroupSum with
    intCast := fun n => (n, n)
    intCast_ofNat := fun _ => by simp; rfl
    intCast_negSucc := fun _ => by simp; rfl }

@[simp]
theorem fst_intCast (n : ℤ) : (n : α × β).fst = n :=
  rfl
#align prod.fst_int_cast Prod.fst_intCast

@[simp]
theorem snd_intCast (n : ℤ) : (n : α × β).snd = n :=
  rfl
#align prod.snd_int_cast Prod.snd_intCast

end Prod