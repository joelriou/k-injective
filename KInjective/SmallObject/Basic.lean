import KInjective.SmallObject.Lifting
import KInjective.SmallObject.Iteration
import KInjective.SmallObject.Pushouts
import Mathlib.CategoryTheory.Limits.Over

universe w v u

class IsWellOrderLimit (J : Type*) [LinearOrder J] [IsWellOrder J (· < ·)] : Prop where
  nonempty : Nonempty J
  not_succ (i : J) : ∃ (j : J), i < j

lemma IsWellOrderLimit.lt_wellOrderSucc
    {J : Type*} [LinearOrder J] [IsWellOrder J (· < ·)] [IsWellOrderLimit J] (i : J) : i < wellOrderSucc i := by
  obtain ⟨j, hj⟩ := IsWellOrderLimit.not_succ i
  exact self_lt_wellOrderSucc hj

namespace CategoryTheory

open Category

namespace Over

instance {C : Type*} [Category C] {S : C} {X Y : Over S} (f : X ⟶ Y) [IsIso f] : IsIso f.left :=
  (inferInstance : IsIso ((Over.forget _ ).map f))

end Over

namespace MorphismProperty

variable {C : Type*} [Category C] (W : MorphismProperty C)

namespace RespectsIso

variable {W}
variable (hW : W.RespectsIso)

lemma over (S : C) : (W.over S).RespectsIso where
  left e f hf := hW.left ((Over.forget _).mapIso e) ((Over.forget _).map f) hf
  right e f hf := hW.right ((Over.forget _).mapIso e) ((Over.forget _).map f) hf

end RespectsIso

end MorphismProperty

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

variable {J C : Type*} [Category J] [Category C] {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
  {X : C} (f : X ⟶ c.pt) [PreservesColimitsOfShape J (coyoneda.obj (Opposite.op X))]

lemma fac_of_preservesColimitsOfShape_coyoneda_obj :
    ∃ (j : J) (g : X ⟶ F.obj j), f = g ≫ c.ι.app j := by
  obtain ⟨j, y, rfl⟩ := (isColimitOfPreserves (coyoneda.obj (Opposite.op X)) hc).jointly_surjective f
  exact ⟨j, y, rfl⟩

end IsColimit

end Limits

open Limits

variable {C : Type*} [Category.{v} C] {I : Type w} {A B : I → C} (f : ∀ i, A i ⟶ B i)

namespace SmallObject

variable (J : Type*) [LinearOrder J] [IsWellOrder J (· < ·)] [OrderBot J] [IsWellOrderLimit J]
  [∀ i, PreservesColimitsOfShape J (coyoneda.obj (Opposite.op (A i)))]
  [∀ {X Y : C} (πX : X ⟶ Y), HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C] [HasPushouts C]
  [Functor.HasIterationOfShape C J]

instance (Y : C) : Functor.HasIterationOfShape (Over Y) J where
  hasColimitsOfShape_of_limit j := inferInstance

noncomputable instance (Y : C) : Functor.PreservesWellOrderContinuousOfShape J (Over.forget Y) where
  condition j _ := by
    infer_instance

variable {X : C} (Y : C)

noncomputable def iterFunctor : J ⥤ Over Y ⥤ Over Y := (functor f Y).iterationFunctor (ε f Y) J

noncomputable def iterCocone : Cocone (iterFunctor f J Y) := colimit.cocone _

noncomputable def isColimitIterCocone : IsColimit (iterCocone f J Y) := colimit.isColimit _

noncomputable abbrev iter : Over Y ⥤ Over Y := (iterCocone f J Y).pt

noncomputable def ιIter : 𝟭 _ ⟶ iter f J Y :=
  ((functor f Y).iterationFunctorBotIso (ε f Y) J).inv ≫ (iterCocone f J Y).ι.app ⊥

variable {Y}
variable (g : X ⟶ Y)

noncomputable def R : C := ((iter f J Y).obj (Over.mk g)).left

noncomputable def ι : X ⟶ R f J g := ((ιIter f J Y).app (Over.mk g)).left

noncomputable def π : R f J g ⟶ Y := ((iter f J Y).obj (Over.mk g)).hom

@[reassoc (attr := simp)]
lemma fac : ι f J g ≫ π f J g = g := Over.w ((ιIter f J Y).app (Over.mk g))

@[simps! obj map]
noncomputable def iterApplyFunctor : J ⥤ Over Y :=
  ((whiskeringRight J _ _).obj ((evaluation (Over Y) (Over Y)).obj (Over.mk g))).obj (iterFunctor f J Y)

@[simps!]
noncomputable def iterApplyCocone : Cocone (iterApplyFunctor f J g) :=
  ((evaluation (Over Y) (Over Y)).obj (Over.mk g)).mapCocone (iterCocone f J Y)

noncomputable def isColimitIterApplyCocone : IsColimit (iterApplyCocone f J g) :=
  isColimitOfPreserves _ (isColimitIterCocone _ _ _)

@[simps!]
noncomputable def iterApplyForgetCocone : Cocone (iterApplyFunctor f J g ⋙ Over.forget _) :=
  (Over.forget _).mapCocone (iterApplyCocone f J g)

noncomputable def isColimitIterApplyForgetCocone : IsColimit (iterApplyForgetCocone f J g) :=
  isColimitOfPreserves _ (isColimitIterApplyCocone _ _ _)

lemma iter_extension {j : J} {i : I} (b : B i ⟶ Y) (t : Over.mk (f i ≫ b) ⟶ (iterApplyFunctor f J g).obj j) :
    ∃ (l : Over.mk b ⟶ (iterApplyFunctor f J g).obj (wellOrderSucc j)),
      t ≫ (iterApplyFunctor f J g).map (homOfLE (self_le_wellOrderSucc j)) = (by exact Over.homMk (f i)) ≫ l := by
  obtain ⟨e, he⟩ := ε_extension f b t
  have hj := IsWellOrderLimit.lt_wellOrderSucc j
  refine' ⟨e ≫ ((functor f Y).iterationFunctorSuccIso (ε f Y) j hj).inv.app _, _⟩
  rw [← reassoc_of% he]
  congr 1
  dsimp [iterFunctor]
  exact congr_app ((functor f Y).iterationFunctor_map_succ (ε f Y) j hj) (Over.mk g)

instance (i : I) : HasLiftingProperty (f i) (π f J g) where
  sq_hasLift {t b} sq := by
    obtain ⟨j, t, rfl⟩ := (isColimitIterApplyForgetCocone f J g).fac_of_preservesColimitsOfShape_coyoneda_obj t
    let τ : Over.mk (f i ≫ b) ⟶ (iterApplyFunctor f J g).obj j := Over.homMk t (by
      have h := Over.w (((iterCocone f J Y).ι.app j).app (Over.mk g))
      dsimp at h ⊢
      rw [← h, ← sq.w, assoc]
      rfl)
    obtain ⟨l, fac⟩ := iter_extension f J g b τ
    exact ⟨⟨{ l := l.left ≫ (((iterCocone f J Y).ι.app (wellOrderSucc j)).app (Over.mk g)).left
              fac_left := by
                have := (Over.forget _).congr_map fac
                dsimp at this
                rw [← reassoc_of% this]
                dsimp
                simp only [← Over.comp_left, ← NatTrans.comp_app, NatTrans.naturality,
                Functor.const_obj_map, Functor.const_obj_obj, comp_id]
              fac_right := by
                dsimp
                rw [assoc]
                erw [Over.w, Over.w]
                rfl }⟩⟩

lemma π_mem_rlpWith : (MorphismProperty.ofHoms f).rlpWith (π f J g) := by
  rintro _ _ _ ⟨i⟩
  infer_instance

lemma ι_mem_rlpWith_llpWith :
    (MorphismProperty.ofHoms f).rlpWith.llpWith (ι f J g) := by
  apply MorphismProperty.comp_mem
  · intro Z T p _
    infer_instance
  · change (MorphismProperty.ofHoms f).rlpWith.llpWith.over Y (((iterCocone f J Y).ι.app ⊥).app (Over.mk g))
    apply Functor.iterationFunctorCocone_ι_app_app_mem
    · apply MorphismProperty.RespectsIso.over
      apply MorphismProperty.llpWith_respectsIso
    · intro X
      simp only [Functor.id_obj, functor_obj, ε_app, MorphismProperty.mem_over_iff, Over.mk_left,
        Over.homMk_left]
      apply ιFunctorObj_mem_rlpWith_llpWith

lemma mem_rlpWith_llpWith_iff :
    (MorphismProperty.ofHoms f).rlpWith.llpWith g ↔
      ∃ (s : Y ⟶ R f J g), g ≫ s = ι f J g ∧ s ≫ π f J g = 𝟙 Y := by
  constructor
  · intro hg
    have pif := hg _ (π_mem_rlpWith f J g)
    have sq : CommSq (ι f J g) g (π f J g) (𝟙 _) := ⟨by simp only [fac, comp_id]⟩
    exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩
  · rintro ⟨s, fac₁, fac₂⟩
    refine' (MorphismProperty.llpWith_isStableUnderRetract (MorphismProperty.ofHoms f).rlpWith).condition (Arrow.mk g) (Arrow.mk (ι f J g))
      (Arrow.homMk (u := 𝟙 _) (v := s) (by simpa using fac₁.symm))
      (Arrow.homMk (u := 𝟙 _) (v := π f J g) (by simp)) (by aesop_cat) (ι_mem_rlpWith_llpWith f J g)

end SmallObject

end CategoryTheory
