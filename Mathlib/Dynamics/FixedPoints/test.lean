import Mathlib.Data.Int.Basic

def Foo (a b : ℕ) : Prop := (2:ℤ) ^ (a * b) = (2:ℤ) ^ (b * a)

example (n a : ℕ) : Foo a 22 :=
  calc (2:ℤ) ^ (a * 22) = (37 : ℤ) := sorry
  _ = 2 ^ n := sorry
  _ = (2:ℤ) ^ (22 * a) := sorry

example (n : ℕ) : Foo a 22 :=
  show (2:ℤ) ^ (a * 22) = (2:ℤ) ^ (22 * a) from
  calc (2:ℤ) ^ (a * 22) = (37 : ℤ) := sorry
  _ = 2 ^ n := sorry
  _ = (2:ℤ) ^ (22 * a) := sorry
