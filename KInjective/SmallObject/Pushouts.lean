import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Products

universe w v u

namespace CategoryTheory

open Category Limits

namespace SmallObject

variable {C : Type u} [Category.{v} C] {I : Type w}
  {A B : I → C} (f : ∀ i, A i ⟶ B i)

-- TODO: relative version in the category `Over (_ : C)`.
section

variable (X Y Z : C) (φ : X ⟶ Y) (ψ : Y ⟶ Z)

variable (A B)

def functorObjIndex := Sigma (fun i => A i ⟶ X)

variable [HasColimitsOfShape (Discrete (functorObjIndex A X)) C]
  [HasColimitsOfShape (Discrete (functorObjIndex A Y)) C]
  [HasColimitsOfShape (Discrete (functorObjIndex A Z)) C]

abbrev functorObjSrcFamily (x : functorObjIndex A X) : C := A x.1

abbrev functorObjTgtFamily (x : functorObjIndex A X) : C := B x.1

noncomputable abbrev functorObjTop : ∐ (functorObjSrcFamily A X) ⟶ X :=
  Limits.Sigma.desc (fun x => x.2)

variable {A B}

abbrev functorObjLeftFamily (x : functorObjIndex A X) :
    functorObjSrcFamily A X x ⟶ functorObjTgtFamily A B X x := f _

noncomputable abbrev functorObjLeft :
    ∐ (functorObjSrcFamily A X) ⟶ ∐ (functorObjTgtFamily A B X) :=
  Limits.Sigma.map (functorObjLeftFamily f X)

variable [HasPushout (functorObjTop A X) (functorObjLeft f X)]
  [HasPushout (functorObjTop A Y) (functorObjLeft f Y)]
  [HasPushout (functorObjTop A Z) (functorObjLeft f Z)]

noncomputable abbrev functorObj : C :=
  pushout (functorObjTop A X) (functorObjLeft f X)

variable {X Y}

section

variable (A)

noncomputable def functorMapSrc :
    ∐ (functorObjSrcFamily A X) ⟶ ∐ (functorObjSrcFamily A Y) :=
  Sigma.map' (fun ⟨i, g⟩ => ⟨i, g ≫ φ⟩) (fun _ => 𝟙 _)

@[reassoc]
lemma ι_functorMapSrc (i : I) (g : A i ⟶ X) (g' : A i ⟶ Y) (fac : g ≫ φ = g') :
    Sigma.ι _ ⟨i, g⟩ ≫ functorMapSrc A φ =
      Sigma.ι (functorObjSrcFamily A Y) ⟨i, g'⟩ := by
  subst fac
  erw [Sigma.ι_comp_map', id_comp]

@[reassoc (attr := simp)]
lemma functorMapSrc_functorObjTop :
    functorMapSrc A φ ≫ functorObjTop A Y = functorObjTop A X ≫ φ := by
  ext ⟨i, f⟩
  rw [ι_functorMapSrc_assoc A φ i f _ rfl]
  simp

end

section

variable (A B)

noncomputable def functorMapTgt :
    ∐ (functorObjTgtFamily A B X) ⟶ ∐ (functorObjTgtFamily A B Y) :=
  Sigma.map' (fun ⟨i, g⟩ => ⟨i, g ≫ φ⟩) (fun _ => 𝟙 _)

@[reassoc]
lemma ι_functorMapTgt (i : I) (g : A i ⟶ X) (g' : A i ⟶ Y) (fac : g ≫ φ = g') :
    Sigma.ι _ ⟨i, g⟩ ≫ functorMapTgt A B φ =
      Sigma.ι (functorObjTgtFamily A B Y) ⟨i, g'⟩ := by
  subst fac
  erw [Sigma.ι_comp_map', id_comp]

end

lemma functorMap_comm :
    functorObjLeft f X ≫ functorMapTgt A B φ = functorMapSrc A φ ≫ functorObjLeft f Y := by
  ext ⟨i, g⟩
  dsimp
  simp only [ι_colimMap_assoc, Discrete.functor_obj, Discrete.natTrans_app,
    ι_functorMapTgt A B φ i g _ rfl, ι_functorMapSrc_assoc A φ i g _ rfl,
    ι_colimMap]

noncomputable abbrev functorMap : functorObj f X ⟶ functorObj f Y :=
  pushout.map _ _ _ _ φ (functorMapTgt A B φ) (functorMapSrc A φ) (by simp)
    (functorMap_comm f φ)

variable (X) in
@[simp]
lemma functorMap_id : functorMap f (𝟙 X) = 𝟙 _ := by
  ext ⟨i, g⟩
  · simp
  · simp [ι_functorMapTgt_assoc A B (𝟙 X) i g g (by simp)]

@[reassoc (attr := simp)]
lemma functorMap_comp : functorMap f (φ ≫ ψ) = functorMap f φ ≫ functorMap f ψ := by
  ext ⟨i, g⟩
  · simp
  · simp [ι_functorMapTgt_assoc A B φ i g _ rfl,
      ι_functorMapTgt_assoc A B (φ ≫ ψ) i g _ rfl,
      ι_functorMapTgt_assoc A B ψ i (g ≫ φ) (g ≫ φ ≫ ψ) (by simp)]

variable (X) in
noncomputable def ιFunctorObj : X ⟶ functorObj f X := pushout.inl

@[reassoc (attr := simp)]
lemma ιFunctorObj_naturality :
    ιFunctorObj f X ≫ functorMap f φ = φ ≫ ιFunctorObj f Y := by
  simp [ιFunctorObj, functorMap]

end

variable [∀ (X : C), HasColimitsOfShape (Discrete (functorObjIndex A X)) C]
  [HasPushouts C]

@[simps!]
noncomputable def functor : C ⥤ C where
  obj X := functorObj f X
  map φ := functorMap f φ

@[simps!]
noncomputable def ε : 𝟭 C ⟶ functor f where
  app X := ιFunctorObj f X

end SmallObject

end CategoryTheory
