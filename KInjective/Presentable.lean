import Mathlib.CategoryTheory.Limits.Preserves.Basic
import KInjective.IsCardinalFiltered

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)

namespace Functor

class Accessible (κ : Cardinal.{w}) where
  preservesLimitsOfShape' : ∀ (I : Type w) [SmallCategory I] [IsCardinalFiltered I κ],
    PreservesLimitsOfShape I F

namespace Accessible

lemma preservesLimitsOfShape
  (κ : Cardinal.{w}) [F.Accessible κ] (I : Type w) [SmallCategory I] [IsCardinalFiltered I κ] :
    PreservesLimitsOfShape I F := Accessible.preservesLimitsOfShape' κ I

end Accessible

end Functor

abbrev Presentable (X : C) (κ : Cardinal.{w}) := (coyoneda.obj (Opposite.op X)).Accessible κ

end CategoryTheory

