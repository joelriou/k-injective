import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.MorphismProperty
import Mathlib.Order.InitialSeg

universe u

open CategoryTheory Category Limits

lemma Nat.eq_zero_or_eq_succ (n : ℕ) : n = 0 ∨ ∃ (m : ℕ), n = m.succ := by cases n <;> aesop

section

variable [LinearOrder α] [IsWellOrder α (· < ·)]

noncomputable def wellOrderSucc (a : α) : α :=
  (@IsWellFounded.wf α (· < ·)).succ a

lemma le_wellOrderSucc (a : α) : a ≤ wellOrderSucc a := by
  by_cases h : ∃ b, a < b
  · exact (IsWellFounded.wf.lt_succ h).le
  · dsimp [wellOrderSucc, WellFounded.succ]
    rw [dif_neg h]
end

section

variable (α β : Type*) [LinearOrder α] [LinearOrder β]

structure InitialSegLimit extends InitialSeg (· < · : α → _) (· < · : β → _) where
  l : β
  hl : Set.range toRelEmbedding = { b | b < l }
  hl' (b : β) (hb : ∀ a, toRelEmbedding a ≤ b) : l ≤ b
  nonempty : Nonempty α

namespace InitialSegLimit

variable {α β}
variable (h : InitialSegLimit α β)

lemma lt (a : α) : h.toRelEmbedding a < h.l := by
  change h.toRelEmbedding a ∈ { b | b < h.l }
  simp [← h.hl]

lemma le (a : α) : h.toRelEmbedding a ≤ h.l := le_of_lt (h.lt a)

def functorToOver : α ⥤ Over h.l where
  obj a := Over.mk (homOfLE (h.le a))
  map {a a'} φ := Over.homMk (homOfLE (by
    dsimp
    obtain hφ|rfl := (leOfHom φ).lt_or_eq
    · exact (h.map_rel_iff.2 hφ).le
    · exact le_refl _))

lemma false (h : InitialSegLimit α ℕ) : False := by
  obtain hl|⟨m, hl⟩ := Nat.eq_zero_or_eq_succ h.l
  · have := h.lt h.nonempty.some
    omega
  · have := h.hl' m (fun a => by have := h.lt a; omega)
    omega

end InitialSegLimit

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
  nonempty_isColimit (α : Type u) [LinearOrder α] (h : InitialSegLimit α J) :
    Nonempty (IsColimit (F.coconeOfFunctorToOver h.functorToOver))

instance (F : ℕ ⥤ D) : F.WellOrderContinuous where
  nonempty_isColimit _ _ h := False.elim h.false

end Functor

namespace MorphismProperty

variable {C : Type*} [Category C] (W : MorphismProperty C)

class IsStableUnderTransfiniteCompositionOfShape (β : Type*) [LinearOrder β] [IsWellOrder β (· < ·)] [OrderBot β] : Prop where
  condition (F : β ⥤ C) [F.WellOrderContinuous] (hF : ∀ (a : β), W (F.map (homOfLE (le_wellOrderSucc a))))
    (c : Cocone F) (hc : IsColimit c) : W (c.ι.app ⊥)

abbrev IsStableUnderInfiniteComposition := W.IsStableUnderTransfiniteCompositionOfShape ℕ

class IsStableUnderTransfiniteComposition extends W.IsMultiplicative : Prop where
  isStableUnderTransfiniteCompositionOfShape (β : Type u) [LinearOrder β] [IsWellOrder β (· < ·)] [OrderBot β] :
    W.IsStableUnderTransfiniteCompositionOfShape β

end MorphismProperty

end CategoryTheory
