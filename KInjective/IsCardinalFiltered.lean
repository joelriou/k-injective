import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.ColimitLimit

namespace CategoryTheory

open Limits

universe v u

variable (I : Type v) [SmallCategory I]

class IsCardinalFiltered (κ : Cardinal.{v}) : Prop :=
  obj : ∀ (S : Set I) (_ : Cardinal.mk S < κ),
    ∃ (Y : I), Nonempty (∀ (x : S), ↑x ⟶ Y)
  hom : ∀ (X Y : I) (S : Set (X ⟶ Y)) (_ : Cardinal.mk S < κ),
    ∃ (Z : I) (g : Y ⟶ Z) (f₀ : X ⟶ Z), ∀ (f : S), f ≫ g = f₀ 

end CategoryTheory