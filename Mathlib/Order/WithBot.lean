/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Order.BoundedOrder

/-!
# `WithBot`, `WithTop`

Adding a `bot` or a `top` to an order.

## Main declarations

* `With<Top/Bot> α`: Equips `Option α` with the order on `α` plus `none` as the top/bottom element.

 -/

variable {α β γ δ : Type _}

/-- Attach `⊥` to a type. -/
def WithBot (α : Type _) :=
  Option α
#align with_bot WithBot

namespace WithBot

variable {a b : α}

instance : CoeTC α (WithBot α) :=
  ⟨some⟩

instance bot : Bot (WithBot α) :=
  ⟨none⟩

instance : Inhabited (WithBot α) :=
  ⟨⊥⟩

open Function

theorem coe_injective : Injective (fun (x : α) => (x : WithBot α)) :=
  Option.some_injective _
#align with_bot.coe_injective WithBot.coe_injective

-- Porting note: this used to have `norm_cast`,
-- but there isn't anything here we can label with @[coe]
-- @[norm_cast]
theorem coe_inj : (a : WithBot α) = b ↔ a = b :=
  Option.some_inj
#align with_bot.coe_inj WithBot.coe_inj

protected theorem «forall» {p : WithBot α → Prop} : (∀ x, p x) ↔ p ⊥ ∧ ∀ x : α, p x :=
  Option.forall
#align with_bot.forall WithBot.forall

protected theorem «exists» {p : WithBot α → Prop} : (∃ x, p x) ↔ p ⊥ ∨ ∃ x : α, p x :=
  Option.exists
#align with_bot.exists WithBot.exists

theorem none_eq_bot : (none : WithBot α) = (⊥ : WithBot α) :=
  rfl
#align with_bot.none_eq_bot WithBot.none_eq_bot

theorem some_eq_coe (a : α) : (some a : WithBot α) = (↑a : WithBot α) :=
  rfl
#align with_bot.some_eq_coe WithBot.some_eq_coe

@[simp]
theorem bot_ne_coe : (⊥ : WithBot α) ≠ (a : WithBot α) :=
  fun.
#align with_bot.bot_ne_coe WithBot.bot_ne_coe

@[simp]
theorem coe_ne_bot : (a : WithBot α) ≠ (⊥ : WithBot α) :=
  fun.
#align with_bot.coe_ne_bot WithBot.coe_ne_bot

-- Porting note: used to be by `Option.rec h₁ h₂`,
-- but Lean complains `code generator does not support recursor 'Option.rec' yet`,
-- so we've replaced it with a match.
/-- Recursor for `with_bot` using the preferred forms `⊥` and `↑a`. -/
@[elab_as_elim]
def recBotCoe {C : WithBot α → Sort _} (h₁ : C ⊥) (h₂ : ∀ a : α, C a) : ∀ n : WithBot α, C n
| none => h₁
| some a => h₂ a
#align with_bot.rec_bot_coe WithBot.recBotCoe

@[simp]
theorem rec_bot_coe_bot {C : WithBot α → Sort _} (d : C ⊥) (f : ∀ a : α, C a) : @recBotCoe _ C d f ⊥ = d :=
  rfl
#align with_bot.rec_bot_coe_bot WithBot.rec_bot_coe_bot

@[simp]
theorem rec_bot_coe_coe {C : WithBot α → Sort _} (d : C ⊥) (f : ∀ a : α, C a) (x : α) : @recBotCoe _ C d f ↑x = f x :=
  rfl
#align with_bot.rec_bot_coe_coe WithBot.rec_bot_coe_coe

/-- Specialization of `option.get_or_else` to values in `with_bot α` that respects API boundaries.
-/
def unbot' (d : α) (x : WithBot α) : α :=
  recBotCoe d id x
#align with_bot.unbot' WithBot.unbot'

@[simp]
theorem unbot'_bot {α} (d : α) : unbot' d ⊥ = d :=
  rfl
#align with_bot.unbot'_bot WithBot.unbot'_bot

@[simp]
theorem unbot'_coe {α} (d x : α) : unbot' d x = x :=
  rfl
#align with_bot.unbot'_coe WithBot.unbot'_coe

-- Porting note: this used to have `norm_cast`,
-- but there isn't anything here we can label with @[coe]
-- @[norm_cast]
theorem coe_eq_coe : (a : WithBot α) = b ↔ a = b :=
  Option.some_inj
#align with_bot.coe_eq_coe WithBot.coe_eq_coe

/-- Lift a map `f : α → β` to `with_bot α → with_bot β`. Implemented using `option.map`. -/
def map (f : α → β) : WithBot α → WithBot β :=
  Option.map f
#align with_bot.map WithBot.map

@[simp]
theorem map_bot (f : α → β) : map f ⊥ = ⊥ :=
  rfl
#align with_bot.map_bot WithBot.map_bot

@[simp]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl
#align with_bot.map_coe WithBot.map_coe

theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
    map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _
#align with_bot.map_comm WithBot.map_comm

theorem ne_bot_iff_exists {x : WithBot α} : x ≠ ⊥ ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists
#align with_bot.ne_bot_iff_exists WithBot.ne_bot_iff_exists

/-- Deconstruct a `x : WithBot α` to the underlying value in `α`, given a proof that `x ≠ ⊥`. -/
def unbot : ∀ x : WithBot α, x ≠ ⊥ → α
  | ⊥, h => absurd rfl h
  | some x, _ => x
#align with_bot.unbot WithBot.unbot

@[simp]
theorem coe_unbot (x : WithBot α) (h : x ≠ ⊥) : (x.unbot h : WithBot α) = x := by
  cases x
  simpa using h
  rfl
#align with_bot.coe_unbot WithBot.coe_unbot

@[simp]
theorem unbot_coe (x : α) (h : (x : WithBot α) ≠ (⊥ : WithBot α) := coe_ne_bot) : (x : WithBot α).unbot h = x :=
  rfl
#align with_bot.unbot_coe WithBot.unbot_coe

instance canLift : CanLift (WithBot α) α coe fun r => r ≠ ⊥ where prf x h := ⟨x.unbot h, coe_unbot _ _⟩
#align with_bot.can_lift WithBot.canLift

section LE

variable [LE α]

instance (priority := 10) : LE (WithBot α) :=
  ⟨fun o₁ o₂ : Option α => ∀ a ∈ o₁, ∃ b ∈ o₂, a ≤ b⟩

@[simp]
theorem some_le_some : @LE.le (WithBot α) _ (some a) (some b) ↔ a ≤ b := by simp [(· ≤ ·)]
#align with_bot.some_le_some WithBot.some_le_some

@[simp, norm_cast]
theorem coe_le_coe : (a : WithBot α) ≤ b ↔ a ≤ b :=
  some_le_some
#align with_bot.coe_le_coe WithBot.coe_le_coe

@[simp]
theorem none_le {a : WithBot α} : @LE.le (WithBot α) _ none a := fun b h => Option.noConfusion h
#align with_bot.none_le WithBot.none_le

instance orderBot : OrderBot (WithBot α) :=
  { WithBot.bot with bot_le := fun _ => none_le }

instance orderTop [OrderTop α] : OrderTop (WithBot α) where
  top := some ⊤
  le_top o a ha := by cases ha; exact ⟨_, rfl, le_top⟩

instance [OrderTop α] : BoundedOrder (WithBot α) :=
  { WithBot.orderTop, WithBot.orderBot with }

theorem not_coe_le_bot (a : α) : ¬(a : WithBot α) ≤ ⊥ := fun h =>
  let ⟨b, hb, _⟩ := h _ rfl
  Option.not_mem_none _ hb
#align with_bot.not_coe_le_bot WithBot.not_coe_le_bot

theorem coe_le : ∀ {o : Option α}, b ∈ o → ((a : WithBot α) ≤ o ↔ a ≤ b)
  | _, rfl => coe_le_coe
#align with_bot.coe_le WithBot.coe_le

theorem coe_le_iff : ∀ {x : WithBot α}, ↑a ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b
  | some a => by simp [some_eq_coe, coe_eq_coe]
  | none => iff_of_false (not_coe_le_bot _) <| by simp [none_eq_bot]
#align with_bot.coe_le_iff WithBot.coe_le_iff

theorem le_coe_iff : ∀ {x : WithBot α}, x ≤ b ↔ ∀ a, x = ↑a → a ≤ b
  | some b => by simp [some_eq_coe, coe_eq_coe]
  | none => by simp [none_eq_bot]
#align with_bot.le_coe_iff WithBot.le_coe_iff

protected theorem _root_.is_max.with_bot (h : IsMax a) : IsMax (a : WithBot α)
  | none, _ => bot_le
  | some b, hb => some_le_some.2 <| h <| some_le_some.1 hb
#align with_bot._root_.is_max.with_bot with_bot._root_.is_max.with_bot

end LE

section LT

variable [LT α]

instance (priority := 10) : LT (WithBot α) :=
  ⟨fun o₁ o₂ : Option α => ∃ b ∈ o₂, ∀ a ∈ o₁, a < b⟩

@[simp]
theorem some_lt_some : @LT.lt (WithBot α) _ (some a) (some b) ↔ a < b := by simp [(· < ·)]
#align with_bot.some_lt_some WithBot.some_lt_some

@[simp, norm_cast]
theorem coe_lt_coe : (a : WithBot α) < b ↔ a < b :=
  some_lt_some
#align with_bot.coe_lt_coe WithBot.coe_lt_coe

@[simp]
theorem none_lt_some (a : α) : @LT.lt (WithBot α) _ none (some a) :=
  ⟨a, rfl, fun b hb => (Option.not_mem_none _ hb).elim⟩
#align with_bot.none_lt_some WithBot.none_lt_some

theorem bot_lt_coe (a : α) : (⊥ : WithBot α) < a :=
  none_lt_some a
#align with_bot.bot_lt_coe WithBot.bot_lt_coe

@[simp]
theorem not_lt_none (a : WithBot α) : ¬@LT.lt (WithBot α) _ a none := fun ⟨_, h, _⟩ => Option.not_mem_none _ h
#align with_bot.not_lt_none WithBot.not_lt_none

theorem lt_iff_exists_coe : ∀ {a b : WithBot α}, a < b ↔ ∃ p : α, b = p ∧ a < p
  | a, some b => by simp [some_eq_coe, coe_eq_coe]
  | a, none => iff_of_false (not_lt_none _) <| by simp [none_eq_bot]
#align with_bot.lt_iff_exists_coe WithBot.lt_iff_exists_coe

theorem lt_coe_iff : ∀ {x : WithBot α}, x < b ↔ ∀ a, x = ↑a → a < b
  | some b => by simp [some_eq_coe, coe_eq_coe, coe_lt_coe]
  | none => by simp [none_eq_bot, bot_lt_coe]
#align with_bot.lt_coe_iff WithBot.lt_coe_iff

end LT

instance [Preorder α] : Preorder (WithBot α) where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := by
    intros
    cases a <;> cases b <;> simp [lt_iff_le_not_le] <;> simp [(· < ·), (· ≤ ·)]
  le_refl o a ha := ⟨a, ha, le_rfl⟩
  le_trans o₁ o₂ o₃ h₁ h₂ a ha :=
    let ⟨b, hb, ab⟩ := h₁ a ha
    let ⟨c, hc, bc⟩ := h₂ b hb
    ⟨c, hc, le_trans ab bc⟩

instance [PartialOrder α] : PartialOrder (WithBot α) :=
  { WithBot.preorder with
    le_antisymm := fun o₁ o₂ h₁ h₂ => by
      cases' o₁ with a
      · cases' o₂ with b
        · rfl

        rcases h₂ b rfl with ⟨_, ⟨⟩, _⟩

      · rcases h₁ a rfl with ⟨b, ⟨⟩, h₁'⟩
        rcases h₂ b rfl with ⟨_, ⟨⟩, h₂'⟩
        rw [le_antisymm h₁' h₂']
         }

theorem coe_strict_mono [Preorder α] : StrictMono (coe : α → WithBot α) := fun a b => some_lt_some.2
#align with_bot.coe_strict_mono WithBot.coe_strict_mono

theorem coe_mono [Preorder α] : Monotone (coe : α → WithBot α) := fun a b => coe_le_coe.2
#align with_bot.coe_mono WithBot.coe_mono

theorem monotone_iff [Preorder α] [Preorder β] {f : WithBot α → β} :
    Monotone f ↔ Monotone (f ∘ coe : α → β) ∧ ∀ x : α, f ⊥ ≤ f x :=
  ⟨fun h => ⟨h.comp WithBot.coe_mono, fun x => h bot_le⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨fun _ => le_rfl, fun x _ => h.2 x⟩, fun x =>
        WithBot.forall.2 ⟨fun h => (not_coe_le_bot _ h).elim, fun y hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩
#align with_bot.monotone_iff WithBot.monotone_iff

@[simp]
theorem monotone_map_iff [Preorder α] [Preorder β] {f : α → β} : Monotone (WithBot.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp [Monotone]
#align with_bot.monotone_map_iff WithBot.monotone_map_iff

alias monotone_map_iff ↔ _ _root_.monotone.with_bot_map

theorem strict_mono_iff [Preorder α] [Preorder β] {f : WithBot α → β} :
    StrictMono f ↔ StrictMono (f ∘ coe : α → β) ∧ ∀ x : α, f ⊥ < f x :=
  ⟨fun h => ⟨h.comp WithBot.coe_strict_mono, fun x => h (bot_lt_coe _)⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨flip absurd (lt_irrefl _), fun x _ => h.2 x⟩, fun x =>
        WithBot.forall.2 ⟨fun h => (not_lt_bot h).elim, fun y hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩
#align with_bot.strict_mono_iff WithBot.strict_mono_iff

@[simp]
theorem strict_mono_map_iff [Preorder α] [Preorder β] {f : α → β} : StrictMono (WithBot.map f) ↔ StrictMono f :=
  strict_mono_iff.trans <| by simp [StrictMono, bot_lt_coe]
#align with_bot.strict_mono_map_iff WithBot.strict_mono_map_iff

alias strict_mono_map_iff ↔ _ _root_.strict_mono.with_bot_map

theorem map_le_iff [Preorder α] [Preorder β] (f : α → β) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    ∀ a b : WithBot α, a.map f ≤ b.map f ↔ a ≤ b
  | ⊥, _ => by simp only [map_bot, bot_le]
  | (a : α), ⊥ => by simp only [map_coe, map_bot, coe_ne_bot, not_coe_le_bot _]
  | (a : α), (b : α) => by simpa only [map_coe, coe_le_coe] using mono_iff
#align with_bot.map_le_iff WithBot.map_le_iff

theorem le_coe_unbot' [Preorder α] : ∀ (a : WithBot α) (b : α), a ≤ a.unbot' b
  | (a : α), b => le_rfl
  | ⊥, b => bot_le
#align with_bot.le_coe_unbot' WithBot.le_coe_unbot'

theorem unbot'_bot_le_iff [LE α] [OrderBot α] {a : WithBot α} {b : α} : a.unbot' ⊥ ≤ b ↔ a ≤ b := by
  cases a <;> simp [none_eq_bot, some_eq_coe]
#align with_bot.unbot'_bot_le_iff WithBot.unbot'_bot_le_iff

theorem unbot'_lt_iff [LT α] {a : WithBot α} {b c : α} (ha : a ≠ ⊥) : a.unbot' b < c ↔ a < c := by
  lift a to α using ha
  rw [unbot'_coe, coe_lt_coe]
#align with_bot.unbot'_lt_iff WithBot.unbot'_lt_iff

instance [SemilatticeSup α] : SemilatticeSup (WithBot α) :=
  { WithBot.orderBot, WithBot.partialOrder with sup := Option.liftOrGet (· ⊔ ·),
    le_sup_left := fun o₁ o₂ a ha => by cases ha <;> cases o₂ <;> simp [Option.liftOrGet],
    le_sup_right := fun o₁ o₂ a ha => by cases ha <;> cases o₁ <;> simp [Option.liftOrGet],
    sup_le := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases' o₁ with b <;> cases' o₂ with c <;> cases ha
      · exact h₂ a rfl

      · exact h₁ a rfl

      · rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩
        simp at h₂
        exact ⟨d, rfl, sup_le h₁' h₂⟩
         }

theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithBot α) = a ⊔ b :=
  rfl
#align with_bot.coe_sup WithBot.coe_sup

instance [SemilatticeInf α] : SemilatticeInf (WithBot α) :=
  { WithBot.orderBot, WithBot.partialOrder with inf := fun o₁ o₂ => o₁.bind fun a => o₂.map fun b => a ⊓ b,
    inf_le_left := fun o₁ o₂ a ha => by
      simp [map] at ha
      rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, inf_le_left⟩,
    inf_le_right := fun o₁ o₂ a ha => by
      simp [map] at ha
      rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, inf_le_right⟩,
    le_inf := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases ha
      rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩
      rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩
      exact ⟨_, rfl, le_inf ab ac⟩ }

theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithBot α) = a ⊓ b :=
  rfl
#align with_bot.coe_inf WithBot.coe_inf

instance [Lattice α] : Lattice (WithBot α) :=
  { WithBot.semilatticeSup, WithBot.semilatticeInf with }

instance [DistribLattice α] : DistribLattice (WithBot α) :=
  { WithBot.lattice with
    le_sup_inf := fun o₁ o₂ o₃ =>
      match o₁, o₂, o₃ with
      | ⊥, ⊥, ⊥ => le_rfl
      | ⊥, ⊥, (a₁ : α) => le_rfl
      | ⊥, (a₁ : α), ⊥ => le_rfl
      | ⊥, (a₁ : α), (a₃ : α) => le_rfl
      | (a₁ : α), ⊥, ⊥ => inf_le_left
      | (a₁ : α), ⊥, (a₃ : α) => inf_le_left
      | (a₁ : α), (a₂ : α), ⊥ => inf_le_right
      | (a₁ : α), (a₂ : α), (a₃ : α) => coe_le_coe.mpr le_sup_inf }

instance decidableLe [LE α] [@DecidableRel α (· ≤ ·)] : @DecidableRel (WithBot α) (· ≤ ·)
  | none, x => is_true fun a h => Option.noConfusion h
  | some x, some y => if h : x ≤ y then isTrue (some_le_some.2 h) else is_false <| by simp [*]
  | some x, none => is_false fun h => by rcases h x rfl with ⟨y, ⟨_⟩, _⟩
#align with_bot.decidable_le WithBot.decidableLe

instance decidableLt [LT α] [@DecidableRel α (· < ·)] : @DecidableRel (WithBot α) (· < ·)
  | none, some x => is_true <| by exists x, rfl <;> rintro _ ⟨⟩
  | some x, some y => if h : x < y then is_true <| by simp [*] else is_false <| by simp [*]
  | x, none => is_false <| by rintro ⟨a, ⟨⟨⟩⟩⟩
#align with_bot.decidable_lt WithBot.decidableLt

instance is_total_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (WithBot α) (· ≤ ·) :=
  ⟨fun a b =>
    match a, b with
    | none, _ => Or.inl bot_le
    | _, none => Or.inr bot_le
    | some x, some y => (total_of (· ≤ ·) x y).imp some_le_some.2 some_le_some.2⟩
#align with_bot.is_total_le WithBot.is_total_le

instance [LinearOrder α] : LinearOrder (WithBot α) :=
  Lattice.toLinearOrder _

-- this is not marked simp because the corresponding with_top lemmas are used
@[norm_cast]
theorem coe_min [LinearOrder α] (x y : α) : ((min x y : α) : WithBot α) = min x y :=
  rfl
#align with_bot.coe_min WithBot.coe_min

-- this is not marked simp because the corresponding with_top lemmas are used
@[norm_cast]
theorem coe_max [LinearOrder α] (x y : α) : ((max x y : α) : WithBot α) = max x y :=
  rfl
#align with_bot.coe_max WithBot.coe_max

theorem well_founded_lt [Preorder α] (h : @WellFounded α (· < ·)) : @WellFounded (WithBot α) (· < ·) :=
  have acc_bot : Acc ((· < ·) : WithBot α → WithBot α → Prop) ⊥ := Acc.intro _ fun a ha => (not_le_of_gt ha bot_le).elim
  ⟨fun a =>
    Option.recOn a acc_bot fun a =>
      Acc.intro _ fun b =>
        Option.recOn b (fun _ => acc_bot) fun b =>
          WellFounded.induction h b
            (show
              ∀ b : α,
                (∀ c, c < b → (c : WithBot α) < a → Acc ((· < ·) : WithBot α → WithBot α → Prop) c) →
                  (b : WithBot α) < a → Acc ((· < ·) : WithBot α → WithBot α → Prop) b
              from fun b ih hba =>
              Acc.intro _ fun c =>
                Option.recOn c (fun _ => acc_bot) fun c hc => ih _ (some_lt_some.1 hc) (lt_trans hc hba))⟩
#align with_bot.well_founded_lt WithBot.well_founded_lt

instance [LT α] [DenselyOrdered α] [NoMinOrder α] : DenselyOrdered (WithBot α) :=
  ⟨fun a b =>
    match a, b with
    | a, none => fun h : a < ⊥ => (not_lt_none _ h).elim
    | none, some b => fun h =>
      let ⟨a, ha⟩ := exists_lt b
      ⟨a, bot_lt_coe a, coe_lt_coe.2 ha⟩
    | some a, some b => fun h =>
      let ⟨a, ha₁, ha₂⟩ := exists_between (coe_lt_coe.1 h)
      ⟨a, coe_lt_coe.2 ha₁, coe_lt_coe.2 ha₂⟩⟩

theorem lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a b : WithBot α} :
    a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
  ⟨fun h =>
    let ⟨y, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.1
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨x, hx⟩ => lt_trans hx.1 hx.2⟩
#align with_bot.lt_iff_exists_coe_btwn WithBot.lt_iff_exists_coe_btwn

instance [LE α] [NoTopOrder α] [Nonempty α] : NoTopOrder (WithBot α) :=
  ⟨by
    apply rec_bot_coe
    · exact ‹Nonempty α›.elim fun a => ⟨a, not_coe_le_bot a⟩

    · intro a
      obtain ⟨b, h⟩ := exists_not_le a
      exact ⟨b, by rwa [coe_le_coe]⟩
      ⟩

instance [LT α] [NoMaxOrder α] [Nonempty α] : NoMaxOrder (WithBot α) :=
  ⟨by
    apply WithBot.recBotCoe
    · apply ‹Nonempty α›.elim
      exact fun a => ⟨a, WithBot.bot_lt_coe a⟩

    · intro a
      obtain ⟨b, ha⟩ := exists_gt a
      exact ⟨b, with_bot.coe_lt_coe.mpr ha⟩
      ⟩

end WithBot

--TODO(Mario): Construct using order dual on with_bot
/-- Attach `⊤` to a type. -/
def WithTop (α : Type _) :=
  Option α
#align with_top WithTop

namespace WithTop

variable {a b : α}

unsafe instance [has_to_format α] :
    has_to_format (WithTop α) where to_format x :=
    match x with
    | none => "⊤"
    | some x => to_fmt x

instance [Repr α] : Repr (WithTop α) :=
  ⟨fun o =>
    match o with
    | none => "⊤"
    | some a => "↑" ++ repr a⟩

instance : CoeTC α (WithTop α) :=
  ⟨some⟩

instance : HasTop (WithTop α) :=
  ⟨none⟩

unsafe instance {α : Type} [reflected _ α] [has_reflect α] : has_reflect (WithTop α)
  | ⊤ => q(⊤)
  | (a : α) => q((coe : α → WithTop α)).subst q(a)

instance : Inhabited (WithTop α) :=
  ⟨⊤⟩

protected theorem forall {p : WithTop α → Prop} : (∀ x, p x) ↔ p ⊤ ∧ ∀ x : α, p x :=
  Option.forall
#align with_top.forall WithTop.forall

protected theorem exists {p : WithTop α → Prop} : (∃ x, p x) ↔ p ⊤ ∨ ∃ x : α, p x :=
  Option.exists
#align with_top.exists WithTop.exists

theorem none_eq_top : (none : WithTop α) = (⊤ : WithTop α) :=
  rfl
#align with_top.none_eq_top WithTop.none_eq_top

theorem some_eq_coe (a : α) : (some a : WithTop α) = (↑a : WithTop α) :=
  rfl
#align with_top.some_eq_coe WithTop.some_eq_coe

@[simp]
theorem top_ne_coe : ⊤ ≠ (a : WithTop α) :=
  fun.
#align with_top.top_ne_coe WithTop.top_ne_coe

@[simp]
theorem coe_ne_top : (a : WithTop α) ≠ ⊤ :=
  fun.
#align with_top.coe_ne_top WithTop.coe_ne_top

/-- Recursor for `with_top` using the preferred forms `⊤` and `↑a`. -/
@[elab_as_elim]
def recTopCoe {C : WithTop α → Sort _} (h₁ : C ⊤) (h₂ : ∀ a : α, C a) : ∀ n : WithTop α, C n :=
  Option.rec h₁ h₂
#align with_top.rec_top_coe WithTop.recTopCoe

@[simp]
theorem rec_top_coe_top {C : WithTop α → Sort _} (d : C ⊤) (f : ∀ a : α, C a) : @recTopCoe _ C d f ⊤ = d :=
  rfl
#align with_top.rec_top_coe_top WithTop.rec_top_coe_top

@[simp]
theorem rec_top_coe_coe {C : WithTop α → Sort _} (d : C ⊤) (f : ∀ a : α, C a) (x : α) : @recTopCoe _ C d f ↑x = f x :=
  rfl
#align with_top.rec_top_coe_coe WithTop.rec_top_coe_coe

/-- `with_top.to_dual` is the equivalence sending `⊤` to `⊥` and any `a : α` to `to_dual a : αᵒᵈ`.
See `with_top.to_dual_bot_equiv` for the related order-iso.
-/
protected def toDual : WithTop α ≃ WithBot αᵒᵈ :=
  Equiv.refl _
#align with_top.to_dual WithTop.toDual

/-- `with_top.of_dual` is the equivalence sending `⊤` to `⊥` and any `a : αᵒᵈ` to `of_dual a : α`.
See `with_top.to_dual_bot_equiv` for the related order-iso.
-/
protected def ofDual : WithTop αᵒᵈ ≃ WithBot α :=
  Equiv.refl _
#align with_top.of_dual WithTop.ofDual

/-- `with_bot.to_dual` is the equivalence sending `⊥` to `⊤` and any `a : α` to `to_dual a : αᵒᵈ`.
See `with_bot.to_dual_top_equiv` for the related order-iso.
-/
protected def _root_.with_bot.to_dual : WithBot α ≃ WithTop αᵒᵈ :=
  Equiv.refl _
#align with_top._root_.with_bot.to_dual with_top._root_.with_bot.to_dual

/-- `with_bot.of_dual` is the equivalence sending `⊥` to `⊤` and any `a : αᵒᵈ` to `of_dual a : α`.
See `with_bot.to_dual_top_equiv` for the related order-iso.
-/
protected def _root_.with_bot.of_dual : WithBot αᵒᵈ ≃ WithTop α :=
  Equiv.refl _
#align with_top._root_.with_bot.of_dual with_top._root_.with_bot.of_dual

@[simp]
theorem to_dual_symm_apply (a : WithBot αᵒᵈ) : WithTop.toDual.symm a = a.ofDual :=
  rfl
#align with_top.to_dual_symm_apply WithTop.to_dual_symm_apply

@[simp]
theorem of_dual_symm_apply (a : WithBot α) : WithTop.ofDual.symm a = a.toDual :=
  rfl
#align with_top.of_dual_symm_apply WithTop.of_dual_symm_apply

@[simp]
theorem to_dual_apply_top : WithTop.toDual (⊤ : WithTop α) = ⊥ :=
  rfl
#align with_top.to_dual_apply_top WithTop.to_dual_apply_top

@[simp]
theorem of_dual_apply_top : WithTop.ofDual (⊤ : WithTop α) = ⊥ :=
  rfl
#align with_top.of_dual_apply_top WithTop.of_dual_apply_top

open OrderDual

@[simp]
theorem to_dual_apply_coe (a : α) : WithTop.toDual (a : WithTop α) = toDual a :=
  rfl
#align with_top.to_dual_apply_coe WithTop.to_dual_apply_coe

@[simp]
theorem of_dual_apply_coe (a : αᵒᵈ) : WithTop.ofDual (a : WithTop αᵒᵈ) = ofDual a :=
  rfl
#align with_top.of_dual_apply_coe WithTop.of_dual_apply_coe

/-- Specialization of `option.get_or_else` to values in `with_top α` that respects API boundaries.
-/
def untop' (d : α) (x : WithTop α) : α :=
  recTopCoe d id x
#align with_top.untop' WithTop.untop'

@[simp]
theorem untop'_top {α} (d : α) : untop' d ⊤ = d :=
  rfl
#align with_top.untop'_top WithTop.untop'_top

@[simp]
theorem untop'_coe {α} (d x : α) : untop' d x = x :=
  rfl
#align with_top.untop'_coe WithTop.untop'_coe

@[norm_cast]
theorem coe_eq_coe : (a : WithTop α) = b ↔ a = b :=
  Option.some_inj
#align with_top.coe_eq_coe WithTop.coe_eq_coe

/-- Lift a map `f : α → β` to `with_top α → with_top β`. Implemented using `option.map`. -/
def map (f : α → β) : WithTop α → WithTop β :=
  Option.map f
#align with_top.map WithTop.map

@[simp]
theorem map_top (f : α → β) : map f ⊤ = ⊤ :=
  rfl
#align with_top.map_top WithTop.map_top

@[simp]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl
#align with_top.map_coe WithTop.map_coe

theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
    map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _
#align with_top.map_comm WithTop.map_comm

theorem map_to_dual (f : αᵒᵈ → βᵒᵈ) (a : WithBot α) : map f (WithBot.toDual a) = a.map (to_dual ∘ f) :=
  rfl
#align with_top.map_to_dual WithTop.map_to_dual

theorem map_of_dual (f : α → β) (a : WithBot αᵒᵈ) : map f (WithBot.ofDual a) = a.map (of_dual ∘ f) :=
  rfl
#align with_top.map_of_dual WithTop.map_of_dual

theorem to_dual_map (f : α → β) (a : WithTop α) :
    WithTop.toDual (map f a) = WithBot.map (to_dual ∘ f ∘ of_dual) a.toDual :=
  rfl
#align with_top.to_dual_map WithTop.to_dual_map

theorem of_dual_map (f : αᵒᵈ → βᵒᵈ) (a : WithTop αᵒᵈ) :
    WithTop.ofDual (map f a) = WithBot.map (of_dual ∘ f ∘ to_dual) a.ofDual :=
  rfl
#align with_top.of_dual_map WithTop.of_dual_map

theorem ne_top_iff_exists {x : WithTop α} : x ≠ ⊤ ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists
#align with_top.ne_top_iff_exists WithTop.ne_top_iff_exists

/-- Deconstruct a `x : with_top α` to the underlying value in `α`, given a proof that `x ≠ ⊤`. -/
def untop : ∀ x : WithTop α, x ≠ ⊤ → α :=
  WithBot.unbot
#align with_top.untop WithTop.untop

@[simp]
theorem coe_untop (x : WithTop α) (h : x ≠ ⊤) : (x.untop h : WithTop α) = x :=
  WithBot.coe_unbot x h
#align with_top.coe_untop WithTop.coe_untop

@[simp]
theorem untop_coe (x : α) (h : (x : WithTop α) ≠ ⊤ := coe_ne_top) : (x : WithTop α).untop h = x :=
  rfl
#align with_top.untop_coe WithTop.untop_coe

instance canLift : CanLift (WithTop α) α coe fun r => r ≠ ⊤ where prf x h := ⟨x.untop h, coe_untop _ _⟩
#align with_top.can_lift WithTop.canLift

section LE

variable [LE α]

instance (priority := 10) : LE (WithTop α) :=
  ⟨fun o₁ o₂ : Option α => ∀ a ∈ o₂, ∃ b ∈ o₁, b ≤ a⟩

theorem to_dual_le_iff {a : WithTop α} {b : WithBot αᵒᵈ} : WithTop.toDual a ≤ b ↔ WithBot.ofDual b ≤ a :=
  Iff.rfl
#align with_top.to_dual_le_iff WithTop.to_dual_le_iff

theorem le_to_dual_iff {a : WithBot αᵒᵈ} {b : WithTop α} : a ≤ WithTop.toDual b ↔ b ≤ WithBot.ofDual a :=
  Iff.rfl
#align with_top.le_to_dual_iff WithTop.le_to_dual_iff

@[simp]
theorem to_dual_le_to_dual_iff {a b : WithTop α} : WithTop.toDual a ≤ WithTop.toDual b ↔ b ≤ a :=
  Iff.rfl
#align with_top.to_dual_le_to_dual_iff WithTop.to_dual_le_to_dual_iff

theorem of_dual_le_iff {a : WithTop αᵒᵈ} {b : WithBot α} : WithTop.ofDual a ≤ b ↔ WithBot.toDual b ≤ a :=
  Iff.rfl
#align with_top.of_dual_le_iff WithTop.of_dual_le_iff

theorem le_of_dual_iff {a : WithBot α} {b : WithTop αᵒᵈ} : a ≤ WithTop.ofDual b ↔ b ≤ WithBot.toDual a :=
  Iff.rfl
#align with_top.le_of_dual_iff WithTop.le_of_dual_iff

@[simp]
theorem of_dual_le_of_dual_iff {a b : WithTop αᵒᵈ} : WithTop.ofDual a ≤ WithTop.ofDual b ↔ b ≤ a :=
  Iff.rfl
#align with_top.of_dual_le_of_dual_iff WithTop.of_dual_le_of_dual_iff

@[simp, norm_cast]
theorem coe_le_coe : (a : WithTop α) ≤ b ↔ a ≤ b := by
  simp only [← to_dual_le_to_dual_iff, to_dual_apply_coe, WithBot.coe_le_coe, to_dual_le_to_dual]
#align with_top.coe_le_coe WithTop.coe_le_coe

@[simp]
theorem some_le_some : @LE.le (WithTop α) _ (some a) (some b) ↔ a ≤ b :=
  coe_le_coe
#align with_top.some_le_some WithTop.some_le_some

@[simp]
theorem le_none {a : WithTop α} : @LE.le (WithTop α) _ a none :=
  to_dual_le_to_dual_iff.mp WithBot.none_le
#align with_top.le_none WithTop.le_none

instance : OrderTop (WithTop α) :=
  { WithTop.hasTop with le_top := fun a => le_none }

instance [OrderBot α] : OrderBot (WithTop α) where
  bot := some ⊥
  bot_le o a ha := by cases ha <;> exact ⟨_, rfl, bot_le⟩

instance [OrderBot α] : BoundedOrder (WithTop α) :=
  { WithTop.orderTop, WithTop.orderBot with }

theorem not_top_le_coe (a : α) : ¬(⊤ : WithTop α) ≤ ↑a :=
  WithBot.not_coe_le_bot (toDual a)
#align with_top.not_top_le_coe WithTop.not_top_le_coe

theorem le_coe : ∀ {o : Option α}, a ∈ o → (@LE.le (WithTop α) _ o b ↔ a ≤ b)
  | _, rfl => coe_le_coe
#align with_top.le_coe WithTop.le_coe

theorem le_coe_iff {x : WithTop α} : x ≤ b ↔ ∃ a : α, x = a ∧ a ≤ b := by
  simpa [← to_dual_le_to_dual_iff, WithBot.coe_le_iff]
#align with_top.le_coe_iff WithTop.le_coe_iff

theorem coe_le_iff {x : WithTop α} : ↑a ≤ x ↔ ∀ b, x = ↑b → a ≤ b := by
  simp only [← to_dual_le_to_dual_iff, to_dual_apply_coe, WithBot.le_coe_iff, OrderDual.forall, to_dual_le_to_dual]
  exact forall₂_congr fun _ _ => Iff.rfl
#align with_top.coe_le_iff WithTop.coe_le_iff

protected theorem _root_.is_min.with_top (h : IsMin a) : IsMin (a : WithTop α) := by
  -- defeq to is_max_to_dual_iff.mp (is_max.with_bot _), but that breaks API boundary
  intro _ hb
  rw [← to_dual_le_to_dual_iff] at hb
  simpa [to_dual_le_iff] using (IsMax.with_bot h : IsMax (to_dual a : WithBot αᵒᵈ)) hb
#align with_top._root_.is_min.with_top with_top._root_.is_min.with_top

end LE

section LT

variable [LT α]

instance (priority := 10) : LT (WithTop α) :=
  ⟨fun o₁ o₂ : Option α => ∃ b ∈ o₁, ∀ a ∈ o₂, b < a⟩

theorem to_dual_lt_iff {a : WithTop α} {b : WithBot αᵒᵈ} : WithTop.toDual a < b ↔ WithBot.ofDual b < a :=
  Iff.rfl
#align with_top.to_dual_lt_iff WithTop.to_dual_lt_iff

theorem lt_to_dual_iff {a : WithBot αᵒᵈ} {b : WithTop α} : a < WithTop.toDual b ↔ b < WithBot.ofDual a :=
  Iff.rfl
#align with_top.lt_to_dual_iff WithTop.lt_to_dual_iff

@[simp]
theorem to_dual_lt_to_dual_iff {a b : WithTop α} : WithTop.toDual a < WithTop.toDual b ↔ b < a :=
  Iff.rfl
#align with_top.to_dual_lt_to_dual_iff WithTop.to_dual_lt_to_dual_iff

theorem of_dual_lt_iff {a : WithTop αᵒᵈ} {b : WithBot α} : WithTop.ofDual a < b ↔ WithBot.toDual b < a :=
  Iff.rfl
#align with_top.of_dual_lt_iff WithTop.of_dual_lt_iff

theorem lt_of_dual_iff {a : WithBot α} {b : WithTop αᵒᵈ} : a < WithTop.ofDual b ↔ b < WithBot.toDual a :=
  Iff.rfl
#align with_top.lt_of_dual_iff WithTop.lt_of_dual_iff

@[simp]
theorem of_dual_lt_of_dual_iff {a b : WithTop αᵒᵈ} : WithTop.ofDual a < WithTop.ofDual b ↔ b < a :=
  Iff.rfl
#align with_top.of_dual_lt_of_dual_iff WithTop.of_dual_lt_of_dual_iff

end LT

end WithTop

namespace WithBot

open OrderDual

@[simp]
theorem to_dual_symm_apply (a : WithTop αᵒᵈ) : WithBot.toDual.symm a = a.ofDual :=
  rfl
#align with_bot.to_dual_symm_apply WithBot.to_dual_symm_apply

@[simp]
theorem of_dual_symm_apply (a : WithTop α) : WithBot.ofDual.symm a = a.toDual :=
  rfl
#align with_bot.of_dual_symm_apply WithBot.of_dual_symm_apply

@[simp]
theorem to_dual_apply_bot : WithBot.toDual (⊥ : WithBot α) = ⊤ :=
  rfl
#align with_bot.to_dual_apply_bot WithBot.to_dual_apply_bot

@[simp]
theorem of_dual_apply_bot : WithBot.ofDual (⊥ : WithBot α) = ⊤ :=
  rfl
#align with_bot.of_dual_apply_bot WithBot.of_dual_apply_bot

@[simp]
theorem to_dual_apply_coe (a : α) : WithBot.toDual (a : WithBot α) = toDual a :=
  rfl
#align with_bot.to_dual_apply_coe WithBot.to_dual_apply_coe

@[simp]
theorem of_dual_apply_coe (a : αᵒᵈ) : WithBot.ofDual (a : WithBot αᵒᵈ) = ofDual a :=
  rfl
#align with_bot.of_dual_apply_coe WithBot.of_dual_apply_coe

theorem map_to_dual (f : αᵒᵈ → βᵒᵈ) (a : WithTop α) : WithBot.map f (WithTop.toDual a) = a.map (to_dual ∘ f) :=
  rfl
#align with_bot.map_to_dual WithBot.map_to_dual

theorem map_of_dual (f : α → β) (a : WithTop αᵒᵈ) : WithBot.map f (WithTop.ofDual a) = a.map (of_dual ∘ f) :=
  rfl
#align with_bot.map_of_dual WithBot.map_of_dual

theorem to_dual_map (f : α → β) (a : WithBot α) :
    WithBot.toDual (WithBot.map f a) = map (to_dual ∘ f ∘ of_dual) a.toDual :=
  rfl
#align with_bot.to_dual_map WithBot.to_dual_map

theorem of_dual_map (f : αᵒᵈ → βᵒᵈ) (a : WithBot αᵒᵈ) :
    WithBot.ofDual (WithBot.map f a) = map (of_dual ∘ f ∘ to_dual) a.ofDual :=
  rfl
#align with_bot.of_dual_map WithBot.of_dual_map

section LE

variable [LE α] {a b : α}

theorem to_dual_le_iff {a : WithBot α} {b : WithTop αᵒᵈ} : WithBot.toDual a ≤ b ↔ WithTop.ofDual b ≤ a :=
  Iff.rfl
#align with_bot.to_dual_le_iff WithBot.to_dual_le_iff

theorem le_to_dual_iff {a : WithTop αᵒᵈ} {b : WithBot α} : a ≤ WithBot.toDual b ↔ b ≤ WithTop.ofDual a :=
  Iff.rfl
#align with_bot.le_to_dual_iff WithBot.le_to_dual_iff

@[simp]
theorem to_dual_le_to_dual_iff {a b : WithBot α} : WithBot.toDual a ≤ WithBot.toDual b ↔ b ≤ a :=
  Iff.rfl
#align with_bot.to_dual_le_to_dual_iff WithBot.to_dual_le_to_dual_iff

theorem of_dual_le_iff {a : WithBot αᵒᵈ} {b : WithTop α} : WithBot.ofDual a ≤ b ↔ WithTop.toDual b ≤ a :=
  Iff.rfl
#align with_bot.of_dual_le_iff WithBot.of_dual_le_iff

theorem le_of_dual_iff {a : WithTop α} {b : WithBot αᵒᵈ} : a ≤ WithBot.ofDual b ↔ b ≤ WithTop.toDual a :=
  Iff.rfl
#align with_bot.le_of_dual_iff WithBot.le_of_dual_iff

@[simp]
theorem of_dual_le_of_dual_iff {a b : WithBot αᵒᵈ} : WithBot.ofDual a ≤ WithBot.ofDual b ↔ b ≤ a :=
  Iff.rfl
#align with_bot.of_dual_le_of_dual_iff WithBot.of_dual_le_of_dual_iff

end LE

section LT

variable [LT α] {a b : α}

theorem to_dual_lt_iff {a : WithBot α} {b : WithTop αᵒᵈ} : WithBot.toDual a < b ↔ WithTop.ofDual b < a :=
  Iff.rfl
#align with_bot.to_dual_lt_iff WithBot.to_dual_lt_iff

theorem lt_to_dual_iff {a : WithTop αᵒᵈ} {b : WithBot α} : a < WithBot.toDual b ↔ b < WithTop.ofDual a :=
  Iff.rfl
#align with_bot.lt_to_dual_iff WithBot.lt_to_dual_iff

@[simp]
theorem to_dual_lt_to_dual_iff {a b : WithBot α} : WithBot.toDual a < WithBot.toDual b ↔ b < a :=
  Iff.rfl
#align with_bot.to_dual_lt_to_dual_iff WithBot.to_dual_lt_to_dual_iff

theorem of_dual_lt_iff {a : WithBot αᵒᵈ} {b : WithTop α} : WithBot.ofDual a < b ↔ WithTop.toDual b < a :=
  Iff.rfl
#align with_bot.of_dual_lt_iff WithBot.of_dual_lt_iff

theorem lt_of_dual_iff {a : WithTop α} {b : WithBot αᵒᵈ} : a < WithBot.ofDual b ↔ b < WithTop.toDual a :=
  Iff.rfl
#align with_bot.lt_of_dual_iff WithBot.lt_of_dual_iff

@[simp]
theorem of_dual_lt_of_dual_iff {a b : WithBot αᵒᵈ} : WithBot.ofDual a < WithBot.ofDual b ↔ b < a :=
  Iff.rfl
#align with_bot.of_dual_lt_of_dual_iff WithBot.of_dual_lt_of_dual_iff

end LT

end WithBot

namespace WithTop

section LT

variable [LT α] {a b : α}

open OrderDual

@[simp, norm_cast]
theorem coe_lt_coe : (a : WithTop α) < b ↔ a < b := by
  simp only [← to_dual_lt_to_dual_iff, to_dual_apply_coe, WithBot.coe_lt_coe, to_dual_lt_to_dual]
#align with_top.coe_lt_coe WithTop.coe_lt_coe

@[simp]
theorem some_lt_some : @LT.lt (WithTop α) _ (some a) (some b) ↔ a < b :=
  coe_lt_coe
#align with_top.some_lt_some WithTop.some_lt_some

theorem coe_lt_top (a : α) : (a : WithTop α) < ⊤ := by simpa [← to_dual_lt_to_dual_iff] using WithBot.bot_lt_coe _
#align with_top.coe_lt_top WithTop.coe_lt_top

@[simp]
theorem some_lt_none (a : α) : @LT.lt (WithTop α) _ (some a) none :=
  coe_lt_top a
#align with_top.some_lt_none WithTop.some_lt_none

@[simp]
theorem not_none_lt (a : WithTop α) : ¬@LT.lt (WithTop α) _ none a := by
  rw [← to_dual_lt_to_dual_iff]
  exact WithBot.not_lt_none _
#align with_top.not_none_lt WithTop.not_none_lt

theorem lt_iff_exists_coe {a b : WithTop α} : a < b ↔ ∃ p : α, a = p ∧ ↑p < b := by
  rw [← to_dual_lt_to_dual_iff, WithBot.lt_iff_exists_coe, OrderDual.exists]
  exact exists_congr fun _ => and_congr_left' Iff.rfl
#align with_top.lt_iff_exists_coe WithTop.lt_iff_exists_coe

theorem coe_lt_iff {x : WithTop α} : ↑a < x ↔ ∀ b, x = ↑b → a < b := by
  simp only [← to_dual_lt_to_dual_iff, WithBot.lt_coe_iff, to_dual_apply_coe, OrderDual.forall, to_dual_lt_to_dual]
  exact forall₂_congr fun _ _ => Iff.rfl
#align with_top.coe_lt_iff WithTop.coe_lt_iff

end LT

instance [Preorder α] : Preorder (WithTop α) where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := by simp [← to_dual_lt_to_dual_iff, lt_iff_le_not_le]
  le_refl _ := to_dual_le_to_dual_iff.mp le_rfl
  le_trans _ _ _ := by
    simp_rw [← to_dual_le_to_dual_iff]
    exact Function.swap le_trans

instance [PartialOrder α] : PartialOrder (WithTop α) :=
  { WithTop.preorder with
    le_antisymm := fun _ _ => by
      simp_rw [← to_dual_le_to_dual_iff]
      exact Function.swap le_antisymm }

theorem coe_strict_mono [Preorder α] : StrictMono (coe : α → WithTop α) := fun a b => some_lt_some.2
#align with_top.coe_strict_mono WithTop.coe_strict_mono

theorem coe_mono [Preorder α] : Monotone (coe : α → WithTop α) := fun a b => coe_le_coe.2
#align with_top.coe_mono WithTop.coe_mono

theorem monotone_iff [Preorder α] [Preorder β] {f : WithTop α → β} :
    Monotone f ↔ Monotone (f ∘ coe : α → β) ∧ ∀ x : α, f x ≤ f ⊤ :=
  ⟨fun h => ⟨h.comp WithTop.coe_mono, fun x => h le_top⟩, fun h =>
    WithTop.forall.2
      ⟨WithTop.forall.2 ⟨fun _ => le_rfl, fun x h => (not_top_le_coe _ h).elim⟩, fun x =>
        WithTop.forall.2 ⟨fun _ => h.2 x, fun y hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩
#align with_top.monotone_iff WithTop.monotone_iff

@[simp]
theorem monotone_map_iff [Preorder α] [Preorder β] {f : α → β} : Monotone (WithTop.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp [Monotone]
#align with_top.monotone_map_iff WithTop.monotone_map_iff

alias monotone_map_iff ↔ _ _root_.monotone.with_top_map

theorem strict_mono_iff [Preorder α] [Preorder β] {f : WithTop α → β} :
    StrictMono f ↔ StrictMono (f ∘ coe : α → β) ∧ ∀ x : α, f x < f ⊤ :=
  ⟨fun h => ⟨h.comp WithTop.coe_strict_mono, fun x => h (coe_lt_top _)⟩, fun h =>
    WithTop.forall.2
      ⟨WithTop.forall.2 ⟨flip absurd (lt_irrefl _), fun x h => (not_top_lt h).elim⟩, fun x =>
        WithTop.forall.2 ⟨fun _ => h.2 x, fun y hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩
#align with_top.strict_mono_iff WithTop.strict_mono_iff

@[simp]
theorem strict_mono_map_iff [Preorder α] [Preorder β] {f : α → β} : StrictMono (WithTop.map f) ↔ StrictMono f :=
  strict_mono_iff.trans <| by simp [StrictMono, coe_lt_top]
#align with_top.strict_mono_map_iff WithTop.strict_mono_map_iff

alias strict_mono_map_iff ↔ _ _root_.strict_mono.with_top_map

theorem map_le_iff [Preorder α] [Preorder β] (f : α → β) (a b : WithTop α) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    a.map f ≤ b.map f ↔ a ≤ b := by
  rw [← to_dual_le_to_dual_iff, to_dual_map, to_dual_map, WithBot.map_le_iff, to_dual_le_to_dual_iff]
  simp [mono_iff]
#align with_top.map_le_iff WithTop.map_le_iff

instance [SemilatticeInf α] : SemilatticeInf (WithTop α) :=
  { WithTop.partialOrder with inf := Option.liftOrGet (· ⊓ ·),
    inf_le_left := fun o₁ o₂ a ha => by cases ha <;> cases o₂ <;> simp [Option.liftOrGet],
    inf_le_right := fun o₁ o₂ a ha => by cases ha <;> cases o₁ <;> simp [Option.liftOrGet],
    le_inf := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases' o₂ with b <;> cases' o₃ with c <;> cases ha
      · exact h₂ a rfl

      · exact h₁ a rfl

      · rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩
        simp at h₂
        exact ⟨d, rfl, le_inf h₁' h₂⟩
         }

theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithTop α) = a ⊓ b :=
  rfl
#align with_top.coe_inf WithTop.coe_inf

instance [SemilatticeSup α] : SemilatticeSup (WithTop α) :=
  { WithTop.partialOrder with sup := fun o₁ o₂ => o₁.bind fun a => o₂.map fun b => a ⊔ b,
    le_sup_left := fun o₁ o₂ a ha => by
      simp [map] at ha
      rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, le_sup_left⟩,
    le_sup_right := fun o₁ o₂ a ha => by
      simp [map] at ha
      rcases ha with ⟨b, rfl, c, rfl, rfl⟩
      exact ⟨_, rfl, le_sup_right⟩,
    sup_le := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases ha
      rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩
      rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩
      exact ⟨_, rfl, sup_le ab ac⟩ }

theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithTop α) = a ⊔ b :=
  rfl
#align with_top.coe_sup WithTop.coe_sup

instance [Lattice α] : Lattice (WithTop α) :=
  { WithTop.semilatticeSup, WithTop.semilatticeInf with }

instance [DistribLattice α] : DistribLattice (WithTop α) :=
  { WithTop.lattice with
    le_sup_inf := fun o₁ o₂ o₃ =>
      match o₁, o₂, o₃ with
      | ⊤, o₂, o₃ => le_rfl
      | (a₁ : α), ⊤, ⊤ => le_rfl
      | (a₁ : α), ⊤, (a₃ : α) => le_rfl
      | (a₁ : α), (a₂ : α), ⊤ => le_rfl
      | (a₁ : α), (a₂ : α), (a₃ : α) => coe_le_coe.mpr le_sup_inf }

instance decidableLe [LE α] [@DecidableRel α (· ≤ ·)] : @DecidableRel (WithTop α) (· ≤ ·) := fun _ _ =>
  decidable_of_decidable_of_iff (WithBot.decidableLe _ _) to_dual_le_to_dual_iff
#align with_top.decidable_le WithTop.decidableLe

instance decidableLt [LT α] [@DecidableRel α (· < ·)] : @DecidableRel (WithTop α) (· < ·) := fun _ _ =>
  decidable_of_decidable_of_iff (WithBot.decidableLt _ _) to_dual_lt_to_dual_iff
#align with_top.decidable_lt WithTop.decidableLt

instance is_total_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (WithTop α) (· ≤ ·) :=
  ⟨fun _ _ => by
    simp_rw [← to_dual_le_to_dual_iff]
    exact total_of _ _ _⟩
#align with_top.is_total_le WithTop.is_total_le

instance [LinearOrder α] : LinearOrder (WithTop α) :=
  Lattice.toLinearOrder _

@[simp, norm_cast]
theorem coe_min [LinearOrder α] (x y : α) : (↑(min x y) : WithTop α) = min x y :=
  rfl
#align with_top.coe_min WithTop.coe_min

@[simp, norm_cast]
theorem coe_max [LinearOrder α] (x y : α) : (↑(max x y) : WithTop α) = max x y :=
  rfl
#align with_top.coe_max WithTop.coe_max

theorem well_founded_lt [Preorder α] (h : @WellFounded α (· < ·)) : @WellFounded (WithTop α) (· < ·) :=
  have acc_some : ∀ a : α, Acc ((· < ·) : WithTop α → WithTop α → Prop) (some a) := fun a =>
    Acc.intro _
      (WellFounded.induction h a
        (show
          ∀ b, (∀ c, c < b → ∀ d : WithTop α, d < some c → Acc (· < ·) d) → ∀ y : WithTop α, y < some b → Acc (· < ·) y
          from fun b ih c =>
          Option.recOn c (fun hc => (not_lt_of_ge le_top hc).elim) fun c hc => Acc.intro _ (ih _ (some_lt_some.1 hc))))
  ⟨fun a =>
    Option.recOn a (Acc.intro _ fun y => Option.recOn y (fun h => (lt_irrefl _ h).elim) fun _ _ => acc_some _) acc_some⟩
#align with_top.well_founded_lt WithTop.well_founded_lt

open OrderDual

theorem well_founded_gt [Preorder α] (h : @WellFounded α (· > ·)) : @WellFounded (WithTop α) (· > ·) :=
  ⟨fun a => by
    -- ideally, use rel_hom_class.acc, but that is defined later
    have : Acc (· < ·) a.to_dual := WellFounded.apply (WithBot.well_founded_lt h) _
    revert this
    generalize ha : a.to_dual = b
    intro ac
    induction' ac with _ H IH generalizing a
    subst ha
    exact ⟨_, fun a' h => IH a'.toDual (to_dual_lt_to_dual.mpr h) _ rfl⟩⟩
#align with_top.well_founded_gt WithTop.well_founded_gt

theorem _root_.with_bot.well_founded_gt [Preorder α] (h : @WellFounded α (· > ·)) : @WellFounded (WithBot α) (· > ·) :=
  ⟨fun a => by
    -- ideally, use rel_hom_class.acc, but that is defined later
    have : Acc (· < ·) a.to_dual := WellFounded.apply (WithTop.well_founded_lt h) _
    revert this
    generalize ha : a.to_dual = b
    intro ac
    induction' ac with _ H IH generalizing a
    subst ha
    exact ⟨_, fun a' h => IH a'.toDual (to_dual_lt_to_dual.mpr h) _ rfl⟩⟩
#align with_top._root_.with_bot.well_founded_gt with_top._root_.with_bot.well_founded_gt

instance Trichotomous.lt [Preorder α] [IsTrichotomous α (· < ·)] : IsTrichotomous (WithTop α) (· < ·) :=
  ⟨by
    rintro (a | _) (b | _)
    iterate 3 simp
    simpa [Option.some_inj] using @trichotomous _ (· < ·) _ a b⟩
#align with_top.trichotomous.lt WithTop.Trichotomous.lt

instance IsWellOrder.lt [Preorder α] [h : IsWellOrder α (· < ·)] :
    IsWellOrder (WithTop α) (· < ·) where wf := well_founded_lt h.wf
#align with_top.is_well_order.lt WithTop.IsWellOrder.lt

instance Trichotomous.gt [Preorder α] [IsTrichotomous α (· > ·)] : IsTrichotomous (WithTop α) (· > ·) :=
  ⟨by
    rintro (a | _) (b | _)
    iterate 3 simp
    simpa [Option.some_inj] using @trichotomous _ (· > ·) _ a b⟩
#align with_top.trichotomous.gt WithTop.Trichotomous.gt

instance IsWellOrder.gt [Preorder α] [h : IsWellOrder α (· > ·)] :
    IsWellOrder (WithTop α) (· > ·) where wf := well_founded_gt h.wf
#align with_top.is_well_order.gt WithTop.IsWellOrder.gt

instance _root_.with_bot.trichotomous.lt [Preorder α] [h : IsTrichotomous α (· < ·)] :
    IsTrichotomous (WithBot α) (· < ·) :=
  @WithTop.Trichotomous.gt αᵒᵈ _ h
#align with_top._root_.with_bot.trichotomous.lt with_top._root_.with_bot.trichotomous.lt

instance _root_.with_bot.is_well_order.lt [Preorder α] [h : IsWellOrder α (· < ·)] : IsWellOrder (WithBot α) (· < ·) :=
  @WithTop.IsWellOrder.gt αᵒᵈ _ h
#align with_top._root_.with_bot.is_well_order.lt with_top._root_.with_bot.is_well_order.lt

instance _root_.with_bot.trichotomous.gt [Preorder α] [h : IsTrichotomous α (· > ·)] :
    IsTrichotomous (WithBot α) (· > ·) :=
  @WithTop.Trichotomous.lt αᵒᵈ _ h
#align with_top._root_.with_bot.trichotomous.gt with_top._root_.with_bot.trichotomous.gt

instance _root_.with_bot.is_well_order.gt [Preorder α] [h : IsWellOrder α (· > ·)] : IsWellOrder (WithBot α) (· > ·) :=
  @WithTop.IsWellOrder.lt αᵒᵈ _ h
#align with_top._root_.with_bot.is_well_order.gt with_top._root_.with_bot.is_well_order.gt

instance [LT α] [DenselyOrdered α] [NoMaxOrder α] : DenselyOrdered (WithTop α) :=
  OrderDual.densely_ordered (WithBot αᵒᵈ)

theorem lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMaxOrder α] {a b : WithTop α} :
    a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
  ⟨fun h =>
    let ⟨y, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.2
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨x, hx⟩ => lt_trans hx.1 hx.2⟩
#align with_top.lt_iff_exists_coe_btwn WithTop.lt_iff_exists_coe_btwn

instance [LE α] [NoBotOrder α] [Nonempty α] : NoBotOrder (WithTop α) :=
  OrderDual.no_bot_order (WithBot αᵒᵈ)

instance [LT α] [NoMinOrder α] [Nonempty α] : NoMinOrder (WithTop α) :=
  OrderDual.no_min_order (WithBot αᵒᵈ)

end WithTop