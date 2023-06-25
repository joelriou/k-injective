import Mathlib.CategoryTheory.Limits.Preserves.Basic
import KInjective.IsCardinalFiltered

universe w v₁ v₂ u₁ u₂ v u

namespace CategoryTheory

open Category Limits

section

noncomputable def colimitCompEvaluationEquiv {C : Type u} [Category.{v} C] {J : Type v} [SmallCategory J] (F : J ⥤ (C ⥤ Type v)) (X : C) :
    colimit (F ⋙ (evaluation C (Type v)).obj X) ≃ (colimit F).obj X :=
  Iso.toEquiv
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (F ⋙ (evaluation C (Type v)).obj X))
      (isColimitOfPreserves ((evaluation C (Type v)).obj X) (colimit.isColimit F)))

end

section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)

namespace Functor

class Accessible (κ : Cardinal.{w}) where
  preservesColimitsOfShape' : ∀ (I : Type w) [SmallCategory I] [IsCardinalFiltered I κ],
    PreservesColimitsOfShape I F

namespace Accessible

lemma preservesColimitsOfShape
  (κ : Cardinal.{w}) [F.Accessible κ] (I : Type w) [SmallCategory I] [IsCardinalFiltered I κ] :
    PreservesColimitsOfShape I F := Accessible.preservesColimitsOfShape' κ I

variable {F}

lemma of_iso {G : C ⥤ D} (e : F ≅ G) [F.Accessible κ] : G.Accessible κ where
  preservesColimitsOfShape' I _ _ := by
    have := preservesColimitsOfShape F κ I
    exact preservesColimitsOfShapeOfNatIso e

end Accessible

end Functor

abbrev Presentable (X : C) (κ : Cardinal.{w}) := (coyoneda.obj (Opposite.op X)).Accessible κ

end

namespace Accessible

variable {C : Type u} [Category.{v} C] [HasColimits C] {D : Type v} [SmallCategory D]
  (G : D ⥤ (C ⥤ Type v)) (κ : Cardinal.{v}) (hD : Cardinal.mk (Arrow D) < κ)
  (hG : ∀ (d : D), (G.obj d).Accessible κ)

lemma stable_by_colimits : (colimit G).Accessible κ where
  preservesColimitsOfShape' I _ _ := ⟨fun {K} => by
    let φ := IsColimit.desc (colimit.isColimit (K ⋙ colimit G))
      ((colimit G).mapCocone (colimit.cocone K))
    suffices IsIso φ from
      preservesColimitOfPreservesColimitCocone (colimit.isColimit K)
        (IsColimit.ofPointIso (colimit.isColimit _))
    rw [isIso_iff_bijective]
    constructor
    . sorry
    . intro x
      obtain ⟨y, hy⟩ := (colimitCompEvaluationEquiv G (colimit K)).surjective x
      let F := G ⋙ ((evaluation C (Type v)).obj (colimit K))
      obtain ⟨X, (z : (G.obj X).obj (colimit K)), hz⟩ := Types.jointly_surjective'.{v, v} y
      have := hG X
      refine' ⟨_, sorry⟩ 
      dsimp
      sorry⟩ 
end Accessible

end CategoryTheory

