import Mathlib.CategoryTheory.MorphismProperty

universe w v u

namespace CategoryTheory

open Category

namespace MorphismProperty

/- based on Sheafifiable Homotopy Model Category, Tibor Beke -/

variable {C : Type u} [Category.{v} C]
  (W : MorphismProperty C)

def set : Set (Arrow C) := fun f => W f.hom

structure SolutionSetConditionAtMap {X Y : C} (f : X ⟶ Y) where
  T : Type w
  w : T → Arrow C 
  condition : ∀ ⦃m w₀ : Arrow C⦄ (_ : W w₀.hom) (φ : m ⟶ w₀),
    ∃ (t : T) (φ₁ : m ⟶ w t) (φ₂ : w t ⟶ w₀), φ = φ₁ ≫ φ₂ 

def SolutionSetConditionAt (I : MorphismProperty C) :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (_ : I f), W.SolutionSetConditionAtMap f

def SolutionSetCondition :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W.SolutionSetConditionAtMap f

namespace SolutionSetConditionAtMap

-- note: this shows that `SolutionSetCondition` is interesting only
-- for a smaller universe, presumably `v`
def tautological {X Y : C} (f : X ⟶ Y) : SolutionSetConditionAtMap.{max u v} W f where
  T := W.set
  w := Subtype.val
  condition := fun m w₀ hw₀ φ => ⟨⟨_, hw₀⟩ , φ, 𝟙 _, by rw [comp_id]⟩ 

end SolutionSetConditionAtMap

end MorphismProperty

end CategoryTheory