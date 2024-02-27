import KInjective.SmallObject.Lifting
import KInjective.SmallObject.Iteration
import KInjective.SmallObject.Pushouts

universe w v u

namespace CategoryTheory

namespace Limits

section

variable {J : Type*} [Category J] {F : J ⥤ Type u}
    {c : Cocone F} (hc : IsColimit c)

namespace IsColimit

namespace JointlySurjective

variable (c) in
@[simps]
def cocone : Cocone F where
  pt :=  { x : c.pt // ∃ (j : J) (y : F.obj j), x = c.ι.app j y }
  ι :=
    { app := fun j y => ⟨_, j, y, rfl⟩
      naturality := fun j₁ j₂ φ => by
        ext y
        dsimp
        rw [Subtype.mk.injEq]
        exact congr_fun (c.ι.naturality φ) y }

def isColimit : IsColimit (cocone c) where
  desc s x := hc.desc s x.1
  fac s j := by
    ext x
    exact congr_fun (hc.fac s j) x
  uniq s m hm := by
    ext ⟨x, hx⟩
    obtain ⟨j, y, rfl⟩ := hx
    exact (congr_fun (hm j) y).trans (congr_fun (hc.fac s j).symm y)

def coconePointIso : (cocone c).pt ≅ c.pt := coconePointUniqueUpToIso (isColimit hc) hc

@[simp]
lemma coconePointIso_hom_apply (x : (cocone c).pt) :
    (coconePointIso hc).hom x = x.1 := by
  obtain ⟨_, j, y, rfl⟩ := x
  exact congr_fun (hc.fac c j) y

end JointlySurjective

lemma jointly_surjective (x : c.pt) :
    ∃ (j : J) (y : F.obj j), x = c.ι.app j y := by
  obtain ⟨⟨_, j, y, rfl⟩, rfl⟩ := (JointlySurjective.coconePointIso hc).toEquiv.surjective x
  exact ⟨j, y, by simp⟩

end IsColimit

end

namespace IsColimit

variable {J C : Type*} [Category J] [Category C] {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c)
  {X : C} (f : X ⟶ c.pt) [PreservesColimitsOfShape J (coyoneda.obj (Opposite.op X))]

lemma fac_of_preservesColimitsOfShape_coyoneda_obj :
    ∃ (j : J) (g : X ⟶ F.obj j), f = g ≫ c.ι.app j := by
  obtain ⟨j, y, rfl⟩ := (isColimitOfPreserves (coyoneda.obj (Opposite.op X)) hc).jointly_surjective f
  exact ⟨j, y, rfl⟩

end IsColimit

end Limits

open Limits

variable {C : Type*} [Category.{v} C] {I : Type w} {A B : I → C} (f : ∀ i, A i ⟶ B i)

namespace MorphismProperty

inductive ofHoms : MorphismProperty C
  | mk (i : I) : ofHoms (f i)

lemma ofHoms.mk_mem (i : I) : (ofHoms f) (f i) := ofHoms.mk i

end MorphismProperty

namespace SmallObject

variable (J : Type*) [LinearOrder J] [IsWellOrder J (· < ·)] [OrderBot J]
  [∀ i, PreservesColimitsOfShape J (yoneda.obj (A i))]
  [∀ {X Y: C} (πX : X ⟶ Y), HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C] [HasPushouts C]
  [∀ (Y : C), Functor.HasIterationOfShape (Over Y) J]

variable {X : C} (Y : C)

noncomputable def iter : Over Y ⥤ Over Y := (functor f Y).iter (ε f Y) J

noncomputable def ιIter : 𝟭 _ ⟶ iter f J Y :=
  ((functor f Y).iterationFunctorBotIso (ε f Y) J).inv ≫ ((functor f Y).iterationFunctorCocone (ε f Y) J).ι.app ⊥

variable {Y}
variable (g : X ⟶ Y)

noncomputable def R : C := ((iter f J Y).obj (Over.mk g)).left

noncomputable def ι : X ⟶ R f J g := ((ιIter f J Y).app (Over.mk g)).left

noncomputable def π : R f J g ⟶ Y := ((iter f J Y).obj (Over.mk g)).hom

@[reassoc (attr := simp)]
lemma fac : ι f J g ≫ π f J g = g := Over.w ((ιIter f J Y).app (Over.mk g))

instance (i : I) : HasLiftingProperty (f i) (π f J g) := sorry

lemma ι_mem_rlpWith_llpWith :
    (MorphismProperty.ofHoms f).rlpWith.llpWith (ι f J g) := sorry

lemma mem_rlpWith_llpWith_iff :
    (MorphismProperty.ofHoms f).rlpWith.llpWith g ↔
      ∃ (s : Y ⟶ R f J g), s ≫ π f J g = 𝟙 Y := sorry

end SmallObject

end CategoryTheory
