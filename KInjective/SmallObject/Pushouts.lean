import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Products

universe w v u

namespace CategoryTheory

open Category Limits

namespace SmallObject

variable {C : Type u} [Category.{v} C] {I : Type w}
  {A B : I → C} (f : ∀ i, A i ⟶ B i)

section

variable {S : C} {X Y Z : C} (πX : X ⟶ S) (πY : Y ⟶ S) (πZ : Z ⟶ S)
  (φ : X ⟶ Y) (hφ : φ ≫ πY = πX) (ψ : Y ⟶ Z) (hψ : ψ ≫ πZ = πY)

structure FunctorObjIndex where
  i : I
  t : A i ⟶ X
  b : B i ⟶ S
  w : f i ≫ b = t ≫ πX

attribute [reassoc (attr := simp)] FunctorObjIndex.w

variable [HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]
  [HasColimitsOfShape (Discrete (FunctorObjIndex f πY)) C]
  [HasColimitsOfShape (Discrete (FunctorObjIndex f πZ)) C]

abbrev functorObjSrcFamily (x : FunctorObjIndex f πX) : C := A x.i

abbrev functorObjTgtFamily (x : FunctorObjIndex f πX) : C := B x.i

noncomputable abbrev functorObjTop :
    ∐ (functorObjSrcFamily f πX) ⟶ X :=
  Limits.Sigma.desc (fun x => x.t)

abbrev functorObjLeftFamily (x : FunctorObjIndex f πX) :
    functorObjSrcFamily f πX x ⟶ functorObjTgtFamily f πX x := f x.i

noncomputable abbrev functorObjLeft :
    ∐ (functorObjSrcFamily f πX) ⟶ ∐ (functorObjTgtFamily f πX) :=
  Limits.Sigma.map (functorObjLeftFamily f πX)

variable [HasPushout (functorObjTop f πX) (functorObjLeft f πX)]
  [HasPushout (functorObjTop f πY) (functorObjLeft f πY)]
  [HasPushout (functorObjTop f πZ) (functorObjLeft f πZ)]

noncomputable abbrev functorObj : C :=
  pushout (functorObjTop f πX) (functorObjLeft f πX)

noncomputable abbrev ιFunctorObj : X ⟶ functorObj f πX := pushout.inl

noncomputable abbrev ρFunctorObj : ∐ (functorObjTgtFamily f πX) ⟶ functorObj f πX := pushout.inr

@[reassoc]
lemma functorObj_comm :
    functorObjTop f πX ≫ ιFunctorObj f πX = functorObjLeft f πX ≫ ρFunctorObj f πX := pushout.condition

@[reassoc (attr := simp)]
lemma FunctorObjIndex.comm (x : FunctorObjIndex f πX) :
    f x.i ≫ Sigma.ι (functorObjTgtFamily f πX) x ≫ ρFunctorObj f πX = x.t ≫ ιFunctorObj f πX := by
  simpa using (Sigma.ι (functorObjSrcFamily f πX) x ≫= functorObj_comm f πX).symm

noncomputable abbrev π'FunctorObj : ∐ (functorObjTgtFamily f πX) ⟶ S := Sigma.desc (fun x => x.b)

noncomputable def πFunctorObj : functorObj f πX ⟶ S :=
  pushout.desc πX (π'FunctorObj f πX) (by ext; simp [π'FunctorObj])

@[reassoc (attr := simp)]
lemma ρFunctorObj_π : ρFunctorObj f πX ≫ πFunctorObj f πX = π'FunctorObj f πX := by
  simp [πFunctorObj]

@[reassoc (attr := simp)]
lemma ιFunctorObj_πFunctorObj : ιFunctorObj f πX ≫ πFunctorObj f πX = πX := by
  simp [ιFunctorObj, πFunctorObj]

noncomputable def functorMapSrc :
    ∐ (functorObjSrcFamily f πX) ⟶ ∐ (functorObjSrcFamily f πY) :=
  Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ φ) x.b (by simp [hφ])) (fun _ => 𝟙 _)

@[reassoc]
lemma ι_functorMapSrc (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : f i ≫ b = t ≫ πX)
    (t' : A i ⟶ Y) (fac : t ≫ φ = t') :
    Sigma.ι _ (FunctorObjIndex.mk i t b w) ≫ functorMapSrc f πX πY φ hφ =
      Sigma.ι (functorObjSrcFamily f πY) (FunctorObjIndex.mk i t' b (by rw [w, ← fac, assoc, hφ])) := by
  subst fac
  erw [Sigma.ι_comp_map', id_comp]

@[reassoc (attr := simp)]
lemma functorMapSrc_functorObjTop :
    functorMapSrc f πX πY φ hφ ≫ functorObjTop f πY = functorObjTop f πX ≫ φ := by
  ext ⟨i, t, b, w⟩
  simp [ι_functorMapSrc_assoc f πX πY φ hφ i t b w _ rfl]

noncomputable def functorMapTgt :
    ∐ (functorObjTgtFamily f πX) ⟶ ∐ (functorObjTgtFamily f πY) :=
  Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ φ) x.b (by simp [hφ])) (fun _ => 𝟙 _)

@[reassoc]
lemma ι_functorMapTgt (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : f i ≫ b = t ≫ πX)
    (t' : A i ⟶ Y) (fac : t ≫ φ = t') :
    Sigma.ι _ (FunctorObjIndex.mk i t b w) ≫ functorMapTgt f πX πY φ hφ =
      Sigma.ι (functorObjTgtFamily f πY) (FunctorObjIndex.mk i t' b (by rw [w, ← fac, assoc, hφ])) := by
  subst fac
  erw [Sigma.ι_comp_map', id_comp]

lemma functorMap_comm :
    functorObjLeft f πX ≫ functorMapTgt f πX πY φ hφ =
      functorMapSrc f πX πY φ hφ ≫ functorObjLeft f πY := by
  ext ⟨i, t, b, w⟩
  simp only [ι_colimMap_assoc, Discrete.natTrans_app, ι_colimMap,
    ι_functorMapTgt f πX πY φ hφ i t b w _ rfl,
    ι_functorMapSrc_assoc f πX πY φ hφ i t b w _ rfl]

noncomputable abbrev functorMap : functorObj f πX ⟶ functorObj f πY :=
  pushout.map _ _ _ _ φ (functorMapTgt f πX πY φ hφ) (functorMapSrc f πX πY φ hφ) (by simp)
    (functorMap_comm f πX πY φ hφ)

@[reassoc (attr := simp)]
lemma functorMap_π : functorMap f πX πY φ hφ ≫ πFunctorObj f πY = πFunctorObj f πX := by
  ext ⟨i, t, b, w⟩
  · simp [hφ]
  · simp [ι_functorMapTgt_assoc f πX πY φ hφ i t b w _ rfl]

variable (X) in
@[simp]
lemma functorMap_id : functorMap f πX πX (𝟙 X) (by simp) = 𝟙 _ := by
  ext ⟨i, t, b, w⟩
  · simp
  · simp [ι_functorMapTgt_assoc f πX πX (𝟙 X) (by simp) i t b w t (by simp)]


@[reassoc (attr := simp)]
lemma ιFunctorObj_naturality :
    ιFunctorObj f πX ≫ functorMap f πX πY φ hφ = φ ≫ ιFunctorObj f πY := by
  simp [ιFunctorObj, functorMap]

end

variable (S : C) [∀ {X : C} (πX : X ⟶ S), HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]
  [HasPushouts C]

@[simps!]
noncomputable def functor : Over S ⥤ Over S where
  obj w := Over.mk (πFunctorObj f w.hom)
  map {w₁ w₂} φ := Over.homMk (functorMap f w₁.hom w₂.hom φ.left (Over.w φ))
  map_id w := by ext; dsimp; simp
  map_comp {w₁ w₂ w₃} φ φ' := by
    ext1
    dsimp
    ext ⟨i, t, b, w⟩
    · simp
    · dsimp
      simp [ι_functorMapTgt_assoc f w₁.hom w₂.hom φ.left (Over.w φ) i t b w _ rfl,
        ι_functorMapTgt_assoc f w₁.hom w₃.hom (φ.left ≫ φ'.left) (Over.w (φ ≫ φ')) i t b w _ rfl,
        ι_functorMapTgt_assoc f w₂.hom w₃.hom (φ'.left) (Over.w φ') i (t ≫ φ.left) b (by simp [w]) (t ≫ φ.left ≫ φ'.left) (by simp)]

@[simps!]
noncomputable def ε : 𝟭 (Over S) ⟶ functor f S where
  app w := Over.homMk (ιFunctorObj f w.hom)

variable {S}

lemma ε_extension {i : I} (b : B i ⟶ S) {Z : Over S} (t : Over.mk (f i ≫ b) ⟶ Z) :
    ∃ (l : Over.mk b ⟶ (functor f S).obj Z), t ≫ (ε f S).app Z = (by exact Over.homMk (f i)) ≫ l :=
  ⟨Over.homMk (Sigma.ι (functorObjTgtFamily f Z.hom)
    (FunctorObjIndex.mk i t.left b (Over.w t).symm) ≫ ρFunctorObj f Z.hom), by
      ext
      exact ((FunctorObjIndex.mk i t.left b (Over.w t).symm).comm).symm⟩


end SmallObject

end CategoryTheory
