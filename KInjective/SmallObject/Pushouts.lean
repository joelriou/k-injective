/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Products
import KInjective.SmallObject.Lifting

/-!
# Construction for the small object argument

Given a family of morphisms `f i : A i ⟶ B i` in a category `C`
and an object `S : C`, we define a functor
`SmallObject.functor f S : Over S ⥤ Over S` which sends
an object given by `πX : X ⟶ S` to the pushout `functorObj f S πX`:
```
∐ (functorObjSrcFamily f πX) ⟶      X

|                                   |
|                                   |
v                                   v

∐ (functorObjTgtFamily f πX) ⟶ functorObj f S πX
```
where the morphism on the left is a coproduct (of copies of maps `f i`)
indexed by a type `FunctorObjIndex f πX` which parametrizes the
diagrams of the form
```
A i ⟶ X
 |    |
 |    |
 v    v
B i ⟶ S
```

The morphism `ιFunctorObj f S πX : X ⟶ functorObj f S πX` is part of
a natural transformation `SmallObject.ε f S : 𝟭 (Over S) ⟶ functor f S`.
The main idea in this construction is that for any commutative square
as above, there may not exist a lifting `B i ⟶ X`, but the construction
provides a tautological morphism `B i ⟶ functorObj f S πX`
(see `SmallObject.ιFunctorObj_extension`).

## TODO

* Show that `ιFunctorObj f S πX : X ⟶ functorObj f S πX` has the
left lifting property with respect to the class of morphisms that
have the right lifting property with respect to the morphisms `f i`.

## References
- https://ncatlab.org/nlab/show/small+object+argument

-/
universe w v u

namespace CategoryTheory

open Category Limits

namespace SmallObject

variable {C : Type u} [Category.{v} C] {I : Type w} {A B : I → C} (f : ∀ i, A i ⟶ B i)

section

variable {S : C} {X Y Z : C} (πX : X ⟶ S) (πY : Y ⟶ S) (πZ : Z ⟶ S)
  (φ : X ⟶ Y) (hφ : φ ≫ πY = πX) (ψ : Y ⟶ Z) (hψ : ψ ≫ πZ = πY)

/-- Given a family of morphisms `f i : A i ⟶ B i` and a morphism `πX : X ⟶ S`,
this type parametrizes the commutative squares with a morphism `f i` on the left
and `πX` in the right. -/
structure FunctorObjIndex where
  /-- an element in the index type -/
  i : I
  /-- the top morphism in the square -/
  t : A i ⟶ X
  /-- the bottom morphism in the square -/
  b : B i ⟶ S
  w : t ≫ πX = f i ≫ b

attribute [reassoc (attr := simp)] FunctorObjIndex.w

variable [HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]
  [HasColimitsOfShape (Discrete (FunctorObjIndex f πY)) C]
  [HasColimitsOfShape (Discrete (FunctorObjIndex f πZ)) C]

/-- The family of objects `A x.i` parametrized by `x : FunctorObjIndex f πX`. -/
abbrev functorObjSrcFamily (x : FunctorObjIndex f πX) : C := A x.i

/-- The family of objects `B x.i` parametrized by `x : FunctorObjIndex f πX`. -/
abbrev functorObjTgtFamily (x : FunctorObjIndex f πX) : C := B x.i

/-- The family of the morphisms `f x.i : A x.i ⟶ B x.i`
parametrized by `x : FunctorObjIndex f πX`. -/
abbrev functorObjLeftFamily (x : FunctorObjIndex f πX) :
    functorObjSrcFamily f πX x ⟶ functorObjTgtFamily f πX x := f x.i

/-- The top morphism in the pushout square in the definition of `pushoutObj f πX`. -/
noncomputable abbrev functorObjTop :
    ∐ (functorObjSrcFamily f πX) ⟶ X :=
  Limits.Sigma.desc (fun x => x.t)

/-- The left morphism in the pushout square in the definition of `pushoutObj f πX`. -/
noncomputable abbrev functorObjLeft :
    ∐ (functorObjSrcFamily f πX) ⟶ ∐ (functorObjTgtFamily f πX) :=
  Limits.Sigma.map (functorObjLeftFamily f πX)

variable [HasPushout (functorObjTop f πX) (functorObjLeft f πX)]
  [HasPushout (functorObjTop f πY) (functorObjLeft f πY)]
  [HasPushout (functorObjTop f πZ) (functorObjLeft f πZ)]

/-- The functor `SmallObject.functor f S : Over S ⥤ Over S` that is part of
the small object argument for a family of morphisms `f`, on an object given
as a morphism `πX : X ⟶ S`. -/
noncomputable abbrev functorObj : C :=
  pushout (functorObjTop f πX) (functorObjLeft f πX)

/-- The canonical morphism `X ⟶ functorObj f πX`. -/
noncomputable abbrev ιFunctorObj : X ⟶ functorObj f πX := pushout.inl

/-- The canonical morphism `∐ (functorObjTgtFamily f πX) ⟶ functorObj f πX`. -/
noncomputable abbrev ρFunctorObj : ∐ (functorObjTgtFamily f πX) ⟶ functorObj f πX := pushout.inr

@[reassoc]
lemma functorObj_comm :
    functorObjTop f πX ≫ ιFunctorObj f πX = functorObjLeft f πX ≫ ρFunctorObj f πX := pushout.condition

@[reassoc]
lemma FunctorObjIndex.comm (x : FunctorObjIndex f πX) :
    f x.i ≫ Sigma.ι (functorObjTgtFamily f πX) x ≫ ρFunctorObj f πX = x.t ≫ ιFunctorObj f πX := by
  simpa using (Sigma.ι (functorObjSrcFamily f πX) x ≫= functorObj_comm f πX).symm

/-- The canonical projection on the base object. -/
noncomputable abbrev π'FunctorObj : ∐ (functorObjTgtFamily f πX) ⟶ S := Sigma.desc (fun x => x.b)

/-- The canonical projection on the base object. -/
noncomputable def πFunctorObj : functorObj f πX ⟶ S :=
  pushout.desc πX (π'FunctorObj f πX) (by ext; simp [π'FunctorObj])

@[reassoc (attr := simp)]
lemma ρFunctorObj_π : ρFunctorObj f πX ≫ πFunctorObj f πX = π'FunctorObj f πX := by
  simp [πFunctorObj]

@[reassoc (attr := simp)]
lemma ιFunctorObj_πFunctorObj : ιFunctorObj f πX ≫ πFunctorObj f πX = πX := by
  simp [ιFunctorObj, πFunctorObj]

/-- The canonical morphism `∐ (functorObjSrcFamily f πX) ⟶ ∐ (functorObjSrcFamily f πY)`
induced by a morphism in `φ : X ⟶ Y` such that `φ ≫ πX = πY`. -/
noncomputable def functorMapSrc :
    ∐ (functorObjSrcFamily f πX) ⟶ ∐ (functorObjSrcFamily f πY) :=
  Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ φ) x.b (by simp [hφ])) (fun _ => 𝟙 _)

@[reassoc]
lemma ι_functorMapSrc (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : t ≫ πX = f i ≫ b)
    (t' : A i ⟶ Y) (fac : t ≫ φ = t') :
    Sigma.ι _ (FunctorObjIndex.mk i t b w) ≫ functorMapSrc f πX πY φ hφ =
      Sigma.ι (functorObjSrcFamily f πY) (FunctorObjIndex.mk i t' b (by rw [← w, ← fac, assoc, hφ])) := by
  subst fac
  erw [Sigma.ι_comp_map', id_comp]

@[reassoc (attr := simp)]
lemma functorMapSrc_functorObjTop :
    functorMapSrc f πX πY φ hφ ≫ functorObjTop f πY = functorObjTop f πX ≫ φ := by
  ext ⟨i, t, b, w⟩
  simp [ι_functorMapSrc_assoc f πX πY φ hφ i t b w _ rfl]

/-- The canonical morphism `∐ (functorObjTgtFamily f πX) ⟶ ∐ (functorObjTgtFamily f πY)`
induced by a morphism in `φ : X ⟶ Y` such that `φ ≫ πX = πY`. -/
noncomputable def functorMapTgt :
    ∐ (functorObjTgtFamily f πX) ⟶ ∐ (functorObjTgtFamily f πY) :=
  Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ φ) x.b (by simp [hφ])) (fun _ => 𝟙 _)

@[reassoc]
lemma ι_functorMapTgt (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : t ≫ πX = f i ≫ b)
    (t' : A i ⟶ Y) (fac : t ≫ φ = t') :
    Sigma.ι _ (FunctorObjIndex.mk i t b w) ≫ functorMapTgt f πX πY φ hφ =
      Sigma.ι (functorObjTgtFamily f πY) (FunctorObjIndex.mk i t' b (by rw [← w, ← fac, assoc, hφ])) := by
  subst fac
  erw [Sigma.ι_comp_map', id_comp]

lemma functorMap_comm :
    functorObjLeft f πX ≫ functorMapTgt f πX πY φ hφ =
      functorMapSrc f πX πY φ hφ ≫ functorObjLeft f πY := by
  ext ⟨i, t, b, w⟩
  simp only [ι_colimMap_assoc, Discrete.natTrans_app, ι_colimMap,
    ι_functorMapTgt f πX πY φ hφ i t b w _ rfl,
    ι_functorMapSrc_assoc f πX πY φ hφ i t b w _ rfl]

/-- The functor `SmallObject.functor f S : Over S ⥤ Over S` that is part of
the small object argument for a family of morphisms `f`, on morphisms. -/
noncomputable def functorMap : functorObj f πX ⟶ functorObj f πY :=
  pushout.map _ _ _ _ φ (functorMapTgt f πX πY φ hφ) (functorMapSrc f πX πY φ hφ) (by simp)
    (functorMap_comm f πX πY φ hφ)

@[reassoc (attr := simp)]
lemma functorMap_π : functorMap f πX πY φ hφ ≫ πFunctorObj f πY = πFunctorObj f πX := by
  ext ⟨i, t, b, w⟩
  · simp [functorMap, hφ]
  · simp [functorMap, ι_functorMapTgt_assoc f πX πY φ hφ i t b w _ rfl]

variable (X) in
@[simp]
lemma functorMap_id : functorMap f πX πX (𝟙 X) (by simp) = 𝟙 _ := by
  ext ⟨i, t, b, w⟩
  · simp [functorMap]
  · simp [functorMap, ι_functorMapTgt_assoc f πX πX (𝟙 X) (by simp) i t b w t (by simp)]


@[reassoc (attr := simp)]
lemma ιFunctorObj_naturality :
    ιFunctorObj f πX ≫ functorMap f πX πY φ hφ = φ ≫ ιFunctorObj f πY := by
  simp [ιFunctorObj, functorMap]

end

variable (S : C) [HasPushouts C]
  [∀ {X : C} (πX : X ⟶ S), HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]

/-- The functor `Over S ⥤ Over S` that is constructed in order to apply the small
object argument to a family of morphisms `f i : A i ⟶ B i`, see the introduction
of the file `Mathlib.CategoryTheory.SmallObject.Construction` -/
@[simps! obj map]
noncomputable def functor : Over S ⥤ Over S where
  obj π := Over.mk (πFunctorObj f π.hom)
  map {π₁ π₂} φ := Over.homMk (functorMap f π₁.hom π₂.hom φ.left (Over.w φ))
  map_id _ := by ext; dsimp; simp
  map_comp {π₁ π₂ π₃} φ φ' := by
    ext1
    dsimp
    ext ⟨i, t, b, w⟩
    · simp
    · simp [functorMap, ι_functorMapTgt_assoc f π₁.hom π₂.hom φ.left (Over.w φ) i t b w _ rfl,
        ι_functorMapTgt_assoc f π₁.hom π₃.hom (φ.left ≫ φ'.left) (Over.w (φ ≫ φ')) i t b w _ rfl,
        ι_functorMapTgt_assoc f π₂.hom π₃.hom (φ'.left) (Over.w φ') i (t ≫ φ.left) b
          (by simp [w]) (t ≫ φ.left ≫ φ'.left) (by simp)]

/-- The canonical natural transformation `𝟭 (Over S) ⟶ functor f S`. -/
@[simps! app]
noncomputable def ε : 𝟭 (Over S) ⟶ functor f S where
  app w := Over.homMk (ιFunctorObj f w.hom)

variable {S}

lemma ιFunctorObj_extension {X : C} (πX : X ⟶ S) {i : I} (t : A i ⟶ X) (b : B i ⟶ S)
    (sq : CommSq t (f i) πX b) :
    ∃ (l : B i ⟶ functorObj f πX), f i ≫ l = t ≫ ιFunctorObj f πX ∧
      l ≫ πFunctorObj f πX = b :=
  ⟨Sigma.ι (functorObjTgtFamily f πX) (FunctorObjIndex.mk i t b sq.w) ≫
    ρFunctorObj f πX, (FunctorObjIndex.mk i t b _).comm, by simp⟩

lemma ε_extension {i : I} (b : B i ⟶ S) {Z : Over S} (t : Over.mk (f i ≫ b) ⟶ Z) :
    ∃ (l : Over.mk b ⟶ (functor f S).obj Z), t ≫ (ε f S).app Z = (by exact Over.homMk (f i)) ≫ l := by
  obtain ⟨l, fac₁, fac₂⟩ := ιFunctorObj_extension f Z.hom _ _ (CommSq.mk (Over.w t))
  exact ⟨Over.homMk l fac₂, by ext; exact fac₁.symm⟩

section

variable {X : C} (πX : X ⟶ S)

lemma functorObjLeft_mem_rlpWith_llpWith :
    (MorphismProperty.ofHoms f).rlpWith.llpWith (functorObjLeft f πX) := by
  intro Z T p hp
  have pif := fun i => hp (f i) ⟨i⟩
  dsimp [functorObjLeft]
  infer_instance

lemma ιFunctorObj_mem_rlpWith_llpWith  :
    (MorphismProperty.ofHoms f).rlpWith.llpWith (ιFunctorObj f πX) := by
  intro Z T p hp
  have pif := functorObjLeft_mem_rlpWith_llpWith f πX p hp
  infer_instance

end

end SmallObject

end CategoryTheory
