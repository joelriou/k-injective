import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.MorphismProperty
import Mathlib.Order.InitialSeg

universe u

open CategoryTheory Category Limits

section

variable {α : Type*} [LinearOrder α] [IsWellOrder α (· < ·)]

noncomputable def wellOrderSucc (a : α) : α :=
  (@IsWellFounded.wf α (· < ·)).succ a

lemma self_le_wellOrderSucc (a : α) : a ≤ wellOrderSucc a := by
  by_cases h : ∃ b, a < b
  · exact (IsWellFounded.wf.lt_succ h).le
  · dsimp [wellOrderSucc, WellFounded.succ]
    rw [dif_neg h]

lemma wellOrderSucc_le {a b : α} (ha : a < b) : wellOrderSucc a ≤ b := by
  dsimp [wellOrderSucc, WellFounded.succ]
  rw [dif_pos ⟨_, ha⟩]
  exact WellFounded.min_le _ ha

lemma self_lt_wellOrderSucc {a b : α} (h : a < b) : a < wellOrderSucc a := by
  dsimp [wellOrderSucc, WellFounded.succ]
  rw [dif_pos ⟨b, h⟩]
  apply WellFounded.min_mem

lemma le_of_lt_wellOrderSucc {a b : α} (h : a < wellOrderSucc b) : a ≤ b := by
  by_contra!
  simpa using lt_of_lt_of_le h (wellOrderSucc_le this)

class IsWellOrderLimitElement (a : α) : Prop where
  not_bot : ∃ (b : α), b < a
  not_succ (b : α) (hb : b < a) : ∃ (c : α), b < c ∧ c < a

variable (a : α) [ha : IsWellOrderLimitElement a]

lemma IsWellOrderLimitElement.neq_bot [OrderBot α] : a ≠ ⊥ := by
  rintro rfl
  obtain ⟨b, hb⟩ := ha.not_bot
  simp at hb

variable {a b}

lemma IsWellOrderLimitElement.wellOrderSucc_lt {b : α} (hb : b < a) :
    wellOrderSucc b < a := by
  obtain ⟨c, hc₁, hc₂⟩ := ha.not_succ b hb
  exact lt_of_le_of_lt (wellOrderSucc_le hc₁) hc₂

lemma eq_bot_or_eq_succ_or_isWellOrderLimitElement [OrderBot α] (a : α) :
    a = ⊥ ∨ (∃ b, a = wellOrderSucc b ∧ b < a) ∨ IsWellOrderLimitElement a := by
  by_cases h₁ : a = ⊥
  · exact Or.inl (by rw [h₁])
  · by_cases h₂ : ∃ b, a = wellOrderSucc b ∧ b < a
    · exact Or.inr (Or.inl h₂)
    · refine' Or.inr (Or.inr (IsWellOrderLimitElement.mk _ _))
      · refine' ⟨⊥, _⟩
        obtain h₃|h₃ := eq_or_lt_of_le (bot_le : ⊥ ≤ a)
        · exfalso
          exact h₁ h₃.symm
        · exact h₃
      · intro b hb
        obtain h₃|h₃ := eq_or_lt_of_le (wellOrderSucc_le hb)
        · exfalso
          exact h₂ ⟨b, h₃.symm, hb⟩
        · exact ⟨wellOrderSucc b, self_lt_wellOrderSucc hb, h₃⟩

lemma IsWellOrderLimitElement.neq_succ (a : α) (ha : a < wellOrderSucc a)
    [IsWellOrderLimitElement (wellOrderSucc a)] : False := by
  simpa using IsWellOrderLimitElement.wellOrderSucc_lt ha

end

@[simp]
lemma Nat.wellOrderSucc_eq (a : ℕ) : wellOrderSucc a = succ a :=
  le_antisymm (wellOrderSucc_le (Nat.lt_succ_self a))
    (Nat.succ_le.1 (self_lt_wellOrderSucc (Nat.lt_succ_self a)))

lemma Nat.not_isWellOrderLimitElement (a : ℕ) [IsWellOrderLimitElement a] : False := by
  obtain _|a := a
  · simpa using IsWellOrderLimitElement.neq_bot (0 : ℕ)
  · simpa using IsWellOrderLimitElement.wellOrderSucc_lt (Nat.lt_succ_self a)

section

variable (α : Type*) (β : Type*) [LinearOrder α] [LinearOrder β]

namespace PrincipalSeg

variable {α β}
variable (h : PrincipalSeg (· < · : α → _) (· < · : β → _))

lemma lt (a : α) : h.toRelEmbedding a < h.top := by
  rw [h.down]
  exact ⟨a, rfl⟩

lemma le (a : α) : h.toRelEmbedding a ≤ h.top := le_of_lt (h.lt a)

@[simps]
def functorToOver : α ⥤ Over h.top where
  obj a := Over.mk (homOfLE (h.le a))
  map {a a'} φ := Over.homMk (homOfLE (by
    dsimp
    obtain hφ|rfl := (leOfHom φ).lt_or_eq
    · exact (h.map_rel_iff.2 hφ).le
    · exact le_refl _))

end PrincipalSeg

end

namespace CategoryTheory


namespace Functor

variable {J : Type u} {C' C D : Type*} [LinearOrder J] [IsWellOrder J (· < ·)]
  [Category C'] [Category C] [Category D]

section

variable (F : C ⥤ D) {X : C} (ι : C' ⥤ Over X)

@[simps]
def coconeOfFunctorToOver : Cocone (ι ⋙ Over.forget X ⋙ F) where
  pt := F.obj X
  ι :=
    { app := fun Y => F.map ((ι.obj Y).hom)
      naturality := fun Y Y' f => by
        dsimp
        rw [← F.map_comp, Over.w, comp_id] }

end

class WellOrderContinuous (F : J ⥤ D) : Prop where
  nonempty_isColimit {α : Type u} [LinearOrder α] (h : PrincipalSeg (· < · : α → α → Prop) (· < · : J → J → Prop))
      [IsWellOrderLimitElement h.top] :
    Nonempty (IsColimit (F.coconeOfFunctorToOver h.functorToOver))

instance (F : ℕ ⥤ D) : F.WellOrderContinuous where
  nonempty_isColimit h := False.elim (Nat.not_isWellOrderLimitElement h.top)

end Functor

namespace MorphismProperty

variable {C : Type*} [Category C] (W : MorphismProperty C)

class IsStableUnderTransfiniteCompositionOfShape (β : Type*) [LinearOrder β] [IsWellOrder β (· < ·)] [OrderBot β] : Prop where
  condition (F : β ⥤ C) [F.WellOrderContinuous] (hF : ∀ (a : β), W (F.map (homOfLE (self_le_wellOrderSucc a))))
    (c : Cocone F) (hc : IsColimit c) : W (c.ι.app ⊥)

abbrev IsStableUnderInfiniteComposition := W.IsStableUnderTransfiniteCompositionOfShape ℕ

class IsStableUnderTransfiniteComposition extends W.IsMultiplicative : Prop where
  isStableUnderTransfiniteCompositionOfShape (β : Type u) [LinearOrder β] [IsWellOrder β (· < ·)] [OrderBot β] :
    W.IsStableUnderTransfiniteCompositionOfShape β

end MorphismProperty

end CategoryTheory
