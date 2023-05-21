import Mathlib.CategoryTheory.Category.Basic
import Mathlib.SetTheory.Cardinal.Cofinality

namespace CategoryTheory

universe w

variable (I : Type w) [SmallCategory I]

class IsCardinalFiltered (κ : Cardinal.{w}) : Prop :=
  obj : ∀ (S : Set I) (_ : Cardinal.mk S < κ),
    ∃ (Y : I), Nonempty (∀ (x : S), ↑x ⟶ Y)
  hom : ∀ (X Y : I) (S : Set (X ⟶ Y)) (_ : Cardinal.mk S < κ),
    ∃ (Z : I) (g : Y ⟶ Z) (f₀ : X ⟶ Z), ∀ (f : S), f ≫ g = f₀ 

-- TODO: show this implies IsFiltered when κ is regular

end CategoryTheory