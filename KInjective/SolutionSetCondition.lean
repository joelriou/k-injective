import Mathlib.CategoryTheory.MorphismProperty

universe v u

namespace CategoryTheory

open Category

namespace MorphismProperty

/- based on Sheafifiable Homotopy Model Category, Tibor Beke -/

variable {C : Type u} [Category.{v} C]
  (W : MorphismProperty C)

def set : Set (Arrow C) := fun f => W f.hom

structure SolutionSetConditionAtMap {X Y : C} (f : X ⟶ Y) where
  W₀ : Set (Arrow C)
  W₀_small : Small.{v} W₀
  condition : ∀ ⦃m w₀ : Arrow C⦄ (_ : W w₀.hom) (φ : m ⟶ w₀),
    ∃ (w : W₀) (φ₁ : m ⟶ w.1) (φ₂ : w.1 ⟶ w₀), φ = φ₁ ≫ φ₂ 

def SolutionSetConditionAt (I : MorphismProperty C) :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (_ : I f), W.SolutionSetConditionAtMap f

def SolutionSetCondition :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W.SolutionSetConditionAtMap f

end MorphismProperty

end CategoryTheory