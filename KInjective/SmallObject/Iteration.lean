import KInjective.SmallObject.WellOrderContinuous
import Mathlib.CategoryTheory.Limits.FunctorCategory

universe u

lemma monotone_inclusion_lt_le_of_le {α : Type*} [Preorder α] {k j : α} (hkj : k ≤ j) :
    Monotone (fun ⟨i, hi⟩ => ⟨i, hi.le.trans hkj⟩ : { i | i < k } → { i | i ≤ j}) :=
  fun _ _ h => h

lemma monotone_inclusion_le_le_of_le {α : Type*} [Preorder α] {k j : α} (hkj : k ≤ j) :
    Monotone (fun ⟨i, hi⟩ => ⟨i, hi.trans hkj⟩ : { i | i ≤ k } → { i | i ≤ j}) :=
  fun _ _ h => h

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C]
  {Φ : C ⥤ C} (ε : 𝟭 C ⟶ Φ)
  {J : Type u} [LinearOrder J] [IsWellOrder J (· < ·)] [OrderBot J]

namespace Functor

namespace Iteration

variable {j : J} (F : { i | i ≤ j } ⥤ C)

noncomputable abbrev mapSucc' (i : J) (hi : i < j) :
    F.obj ⟨i, hi.le⟩ ⟶ F.obj ⟨wellOrderSucc i, wellOrderSucc_le hi⟩ :=
  F.map (homOfLE (by simpa only [Subtype.mk_le_mk] using self_le_wellOrderSucc i))

variable {i : J} (hi : i ≤ j)

def restrictionLT : { k | k < i } ⥤ C :=
  (monotone_inclusion_lt_le_of_le hi).functor ⋙ F

@[simp]
lemma restrictionLT_obj (k : J) (hk : k < i) :
    (restrictionLT F hi).obj ⟨k, hk⟩ = F.obj ⟨k, hk.le.trans hi⟩ := rfl

@[simp]
lemma restrictionLT_map {k₁ k₂ : { k | k < i }} (φ : k₁ ⟶ k₂) :
    (restrictionLT F hi).map φ = F.map (homOfLE (by simpa using leOfHom φ)) := rfl

@[simps]
def coconeOfLE :
    Cocone (restrictionLT F hi) where
  pt := F.obj ⟨i, hi⟩
  ι :=
    { app := fun ⟨k, hk⟩ => F.map (homOfLE (by simpa using hk.le))
      naturality := fun ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ _ => by
        dsimp
        rw [comp_id, ← Functor.map_comp, homOfLE_comp] }

def restrictionLE : { k | k ≤ i } ⥤ C :=
  (monotone_inclusion_le_le_of_le hi).functor ⋙ F

@[simp]
lemma restrictionLE_obj (k : J) (hk : k ≤ i) :
    (restrictionLE F hi).obj ⟨k, hk⟩ = F.obj ⟨k, hk.trans hi⟩ := rfl

@[simp]
lemma restrictionLE_map {k₁ k₂ : { k | k ≤ i }} (φ : k₁ ⟶ k₂) :
    (restrictionLE F hi).map φ = F.map (homOfLE (by simpa using leOfHom φ)) := rfl

end Iteration

structure Iteration (j : J) where
  F : { i | i ≤ j } ⥤ C ⥤ C
  isoZero : F.obj ⟨⊥, bot_le⟩ ≅ 𝟭 C
  isoSucc (i : J) (hi : i < j) :
    F.obj ⟨wellOrderSucc i, wellOrderSucc_le hi⟩ ≅ F.obj ⟨i, hi.le⟩ ⋙ Φ
  mapSucc'_eq (i : J) (hi : i < j) :
    Iteration.mapSucc' F i hi = whiskerLeft _ ε ≫ (isoSucc i hi).inv
  isColimit (i : J) [IsWellOrderLimitElement i] (hi : i ≤ j) :
    IsColimit (Iteration.coconeOfLE F hi)

namespace Iteration

variable {ε}
variable {j : J} (iter₁ iter₂ : Φ.Iteration ε j)

noncomputable abbrev mapSucc (i : J) (hi : i < j) :
    iter₁.F.obj ⟨i, hi.le⟩ ⟶ iter₁.F.obj ⟨wellOrderSucc i, wellOrderSucc_le hi⟩ :=
  mapSucc' iter₁.F i hi

lemma mapSucc_eq (i : J) (hi : i < j) :
    iter₁.mapSucc i hi = whiskerLeft _ ε ≫ (iter₁.isoSucc i hi).inv :=
  iter₁.mapSucc'_eq _ hi

structure Hom where
  natTrans : iter₁.F ⟶ iter₂.F
  natTrans_app_zero : natTrans.app ⟨⊥, bot_le⟩ = iter₁.isoZero.hom ≫ iter₂.isoZero.inv := by aesop_cat
  natTrans_app_succ (i : J) (hi : i < j) :
    natTrans.app ⟨wellOrderSucc i, wellOrderSucc_le hi⟩ = (iter₁.isoSucc i hi).hom ≫
      whiskerRight (natTrans.app ⟨i, hi.le⟩) _ ≫ (iter₂.isoSucc i hi).inv := by aesop_cat

namespace Hom

attribute [simp] natTrans_app_zero

@[simps]
def id : Hom iter₁ iter₁ where
  natTrans := 𝟙 _

variable {iter₁ iter₂}

lemma ext' {f g : Hom iter₁ iter₂} (h : f.natTrans = g.natTrans) : f = g := by
  cases f
  cases g
  subst h
  rfl

attribute [local ext] ext'

@[simps]
def comp {iter₃ : Iteration ε j} (f : Hom iter₁ iter₂) (g : Hom iter₂ iter₃) : Hom iter₁ iter₃ where
  natTrans := f.natTrans ≫ g.natTrans
  natTrans_app_succ i hi := by simp [natTrans_app_succ _ _ hi]

instance : Category (Iteration ε j) where
  Hom := Hom
  id := id
  comp := comp

instance : Subsingleton (iter₁ ⟶ iter₂) where
  allEq f g := ext' (by
    let P := fun (i : J) => ∀ (hi : i ≤ j), f.natTrans.app ⟨i, hi⟩ = g.natTrans.app ⟨i, hi⟩
    suffices ∀ (i : J), P i by
      ext ⟨i, hi⟩ : 2
      apply this
    refine fun _ => WellFoundedLT.induction _ (fun i hi hi' => ?_)
    obtain rfl|⟨i, rfl, hi''⟩|_ := eq_bot_or_eq_succ_or_isWellOrderLimitElement i
    · simp only [natTrans_app_zero]
    · simp only [Hom.natTrans_app_succ _ i (lt_of_lt_of_le hi'' hi'), hi i hi'']
    · exact (iter₁.isColimit i hi').hom_ext (fun ⟨k, hk⟩ => by simp [hi k hk]))

end Hom

variable {iter₁ iter₂} in
@[simp, reassoc]
lemma natTrans_comp {iter₃ : Iteration ε j} (φ : iter₁ ⟶ iter₂) (ψ : iter₂ ⟶ iter₃) :
    (φ ≫ ψ).natTrans = φ.natTrans ≫ ψ.natTrans := rfl

variable {iter₁ iter₂} in
@[reassoc]
lemma natTrans_naturality (φ : iter₁ ⟶ iter₂) (i₁ i₂ : J) (h : i₁ ≤ i₂) (h' : i₂ ≤ j) :
    iter₁.F.map (by exact homOfLE h) ≫ φ.natTrans.app ⟨i₂, h'⟩ =
      φ.natTrans.app ⟨i₁, h.trans h'⟩ ≫ iter₂.F.map (by exact homOfLE h) := by
  apply φ.natTrans.naturality

variable (ε) in
@[simps]
def eval {i : J} (hi : i ≤ j) : Iteration ε j ⥤ C ⥤ C where
  obj iter := iter.F.obj ⟨i, hi⟩
  map φ := φ.natTrans.app _

@[simps F isoZero isoSucc]
def trunc {i : J} (hi : i ≤ j) : Iteration ε i where
  F := restrictionLE (iter₁.F) hi
  isoZero := iter₁.isoZero
  isoSucc k hk := iter₁.isoSucc k (lt_of_lt_of_le hk hi)
  mapSucc'_eq k hk := iter₁.mapSucc'_eq k (lt_of_lt_of_le hk hi)
  isColimit k _ hk := iter₁.isColimit k (hk.trans hi)

variable (ε) in
@[simps obj]
def truncFunctor {i : J} (hi : i ≤ j) : Iteration ε j ⥤ Iteration ε i where
  obj iter := iter.trunc hi
  map {iter₁ iter₂} φ :=
    { natTrans := whiskerLeft _ φ.natTrans
      natTrans_app_succ := fun k hk => φ.natTrans_app_succ k (lt_of_lt_of_le hk hi) }

variable {iter₁ iter₂}

@[simp]
lemma truncFunctor_map_natTrans_app
    (φ : iter₁ ⟶ iter₂) {i : J} (hi : i ≤ j) (k : J) (hk : k ≤ i) :
    ((truncFunctor ε hi).map φ).natTrans.app ⟨k, hk⟩ =
      φ.natTrans.app ⟨k, hk.trans hi⟩ := rfl

namespace Hom

lemma congr_app (φ φ' : iter₁ ⟶ iter₂) (i : J) (hi : i ≤ j) :
    φ.natTrans.app ⟨i, hi⟩ = φ'.natTrans.app ⟨i, hi⟩ := by
  obtain rfl := Subsingleton.elim φ φ'
  rfl

def mkOfZero (iter₁ iter₂ : Iteration ε (⊥ : J)) : iter₁ ⟶ iter₂ where
  natTrans :=
    { app := fun ⟨i, hi⟩ => eqToHom (by congr; simpa using hi) ≫ iter₁.isoZero.hom ≫
        iter₂.isoZero.inv ≫ eqToHom (by congr; symm; simpa using hi)
      naturality := fun ⟨i, hi⟩ ⟨k, hk⟩ _φ => by
        obtain rfl : i = ⊥ := by simpa using hi
        obtain rfl : k = ⊥ := by simpa using hk
        obtain rfl : _φ = 𝟙 _ := rfl
        simp }
  natTrans_app_succ i hi := by simp at hi

section

noncomputable def mkOfSuccNatTransApp {i : J} {iter₁ iter₂ : Iteration ε (wellOrderSucc i)}
    (hi : i < wellOrderSucc i)
    (φ : iter₁.trunc hi.le ⟶ iter₂.trunc hi.le) (k : J) (hk : k ≤ wellOrderSucc i) :
    iter₁.F.obj ⟨k, hk⟩ ⟶ iter₂.F.obj ⟨k, hk⟩ :=
  if hk' : k ≤ i then φ.natTrans.app ⟨k, hk'⟩ else by
    obtain rfl : k = wellOrderSucc i := by
      obtain hk''|rfl := hk.lt_or_eq
      · exfalso
        apply hk' (le_of_lt_wellOrderSucc hk'')
      · rfl
    exact (iter₁.isoSucc i hi).hom ≫ whiskerRight (φ.natTrans.app ⟨i, by dsimp; rfl⟩) _ ≫ (iter₂.isoSucc i hi).inv

lemma mkOfSuccNatTransApp_eq_of_le {i : J} {iter₁ iter₂ : Iteration ε (wellOrderSucc i)}
    (hi : i < wellOrderSucc i)
    (φ : iter₁.trunc hi.le ⟶ iter₂.trunc hi.le) (k : J) (hk : k ≤ i) :
    mkOfSuccNatTransApp hi φ k (hk.trans (self_le_wellOrderSucc i)) = φ.natTrans.app ⟨k, hk⟩ :=
  dif_pos hk

@[simp]
lemma mkOfSuccNatTransApp_eq_succ {i : J} {iter₁ iter₂ : Iteration ε (wellOrderSucc i)}
    (hi : i < wellOrderSucc i)
    (φ : iter₁.trunc hi.le ⟶ iter₂.trunc hi.le) :
    mkOfSuccNatTransApp hi φ (wellOrderSucc i) (by rfl) =
      (iter₁.isoSucc i hi).hom ≫ whiskerRight (φ.natTrans.app ⟨i, by dsimp; rfl⟩) _ ≫ (iter₂.isoSucc i hi).inv :=
  dif_neg (by aesop)

@[simps]
noncomputable def mkOfSuccNatTrans {i : J} {iter₁ iter₂ : Iteration ε (wellOrderSucc i)}
    (hi : i < wellOrderSucc i)
    (φ : iter₁.trunc hi.le ⟶ iter₂.trunc hi.le) :
    iter₁.F ⟶ iter₂.F where
  app := fun ⟨k, hk⟩ => mkOfSuccNatTransApp hi φ k hk
  naturality := fun ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ f => by
    dsimp at hk₁ hk₂ ⊢
    have hk : k₁ ≤ k₂ := leOfHom f
    obtain h₂|rfl := hk₂.lt_or_eq
    · replace h₂ : k₂ ≤ i := le_of_lt_wellOrderSucc h₂
      rw [mkOfSuccNatTransApp_eq_of_le hi φ k₂ h₂,
        mkOfSuccNatTransApp_eq_of_le hi φ k₁ (hk.trans h₂)]
      exact natTrans_naturality φ k₁ k₂ hk h₂
    · obtain h₁|rfl := hk.lt_or_eq
      · have h₂ : k₁ ≤ i := le_of_lt_wellOrderSucc h₁
        let f₁ : (⟨k₁, hk⟩ : { l | l ≤ wellOrderSucc i}) ⟶
          ⟨i, self_le_wellOrderSucc i⟩ := homOfLE h₂
        let f₂ : (⟨i, self_le_wellOrderSucc i⟩ : { l | l ≤ wellOrderSucc i}) ⟶
          ⟨wellOrderSucc i, by dsimp; rfl⟩ := homOfLE (self_le_wellOrderSucc i)
        obtain rfl : f = f₁ ≫ f₂ := rfl
        rw [Functor.map_comp, Functor.map_comp, assoc,
          mkOfSuccNatTransApp_eq_of_le hi φ k₁ h₂]
        erw [← natTrans_naturality_assoc φ k₁ i h₂ (by rfl)]
        rw [mkOfSuccNatTransApp_eq_succ]
        dsimp
        change _ ≫ iter₁.mapSucc i hi ≫ _ = _ ≫ _ ≫ iter₂.mapSucc i hi
        rw [iter₁.mapSucc_eq i hi, iter₂.mapSucc_eq i hi, assoc,
          Iso.inv_hom_id_assoc]
        congr 1; simp only [← assoc]; congr 1
        ext X
        exact (ε.naturality _).symm
      · obtain rfl : f = 𝟙 _ := rfl
        rw [Functor.map_id, Functor.map_id, id_comp, comp_id]

end

noncomputable def mkOfSucc {i : J} (iter₁ iter₂ : Iteration ε (wellOrderSucc i)) (hi : i < wellOrderSucc i)
    (φ : iter₁.trunc hi.le ⟶ iter₂.trunc hi.le) :
    iter₁ ⟶ iter₂ where
  natTrans := mkOfSuccNatTrans hi φ
  natTrans_app_zero := by
    dsimp
    rw [mkOfSuccNatTransApp_eq_of_le _ _ _ bot_le, φ.natTrans_app_zero]
    rfl
  natTrans_app_succ k hk := by
    obtain hk'|rfl := (le_of_lt_wellOrderSucc hk).lt_or_eq
    · dsimp
      rw [mkOfSuccNatTransApp_eq_of_le hi φ k hk'.le,
        mkOfSuccNatTransApp_eq_of_le hi φ (wellOrderSucc k) (wellOrderSucc_le hk'),
        φ.natTrans_app_succ _ hk']
      rfl
    · simp [mkOfSuccNatTransApp_eq_of_le hi φ k (by rfl)]

section

variable [IsWellOrderLimitElement j] (φ : ∀ (i : J) (hi : i < j), iter₁.trunc hi.le ⟶ iter₂.trunc hi.le)

def mkOfLimitNatTransApp (i : J) (hi : i ≤ j) : iter₁.F.obj ⟨i, hi⟩ ⟶ iter₂.F.obj ⟨i, hi⟩ :=
  if h : i < j
    then
      (φ i h).natTrans.app ⟨i, by dsimp; rfl⟩
    else by
      obtain rfl : i = j := by
        obtain h'|rfl := hi.lt_or_eq
        · exfalso
          exact h h'
        · rfl
      exact (iter₁.isColimit i (show i ≤ i by rfl)).desc (Cocone.mk _
        { app := fun ⟨k, hk⟩ => (φ k hk).natTrans.app ⟨k, by dsimp; rfl⟩ ≫
            iter₂.F.map (homOfLE (by exact hk.le))
          naturality := fun ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ f => by
            have hf : k₁ ≤ k₂ := by simpa using leOfHom f
            dsimp
            rw [comp_id, congr_app (φ k₁ hk₁) ((truncFunctor ε hf).map (φ k₂ hk₂))]
            erw [natTrans_naturality_assoc (φ k₂ hk₂) k₁ k₂ hf (by rfl)]
            dsimp
            rw [← Functor.map_comp, homOfLE_comp] })

lemma mkOfLimitNatTransApp_eq_of_lt (i : J) (hi : i < j) :
    mkOfLimitNatTransApp φ i hi.le = (φ i hi).natTrans.app ⟨i, by dsimp; rfl⟩ := dif_pos hi

lemma mkOfLimitNatTransApp_naturality_top (i : J) (hi : i < j) :
    iter₁.F.map (homOfLE (by simpa using hi.le) : ⟨i, hi.le⟩ ⟶ ⟨j, by dsimp; rfl⟩) ≫ mkOfLimitNatTransApp φ j (by rfl) =
      mkOfLimitNatTransApp φ i hi.le ≫ iter₂.F.map (homOfLE (by simpa using hi.le)) := by
  rw [mkOfLimitNatTransApp_eq_of_lt φ i hi]
  dsimp [mkOfLimitNatTransApp]
  rw [dif_neg (by simp)]
  exact (iter₁.isColimit j (by rfl)).fac _ ⟨i, hi⟩

@[simps]
def mkOfLimitNatTrans : iter₁.F ⟶ iter₂.F where
  app := fun ⟨k, hk⟩ => mkOfLimitNatTransApp φ k hk
  naturality := fun ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ f => by
    dsimp at hk₁ hk₂
    have hk : k₁ ≤ k₂ := leOfHom f
    obtain h₂|rfl := hk₂.lt_or_eq
    · dsimp
      rw [mkOfLimitNatTransApp_eq_of_lt _ k₂ h₂,
        mkOfLimitNatTransApp_eq_of_lt _ k₁ (lt_of_le_of_lt hk h₂),
        congr_app (φ k₁ (lt_of_le_of_lt hk h₂)) ((truncFunctor ε hk).map (φ k₂ h₂))]
      exact natTrans_naturality (φ k₂ h₂) k₁ k₂ hk (by rfl)
    · obtain h₁|rfl := hk₁.lt_or_eq
      · exact mkOfLimitNatTransApp_naturality_top _ _ h₁
      · obtain rfl : f = 𝟙 _ := rfl
        dsimp
        simp only [map_id, id_comp, comp_id]

def mkOfLimit  :
    iter₁ ⟶ iter₂ where
  natTrans := mkOfLimitNatTrans φ
  natTrans_app_zero := by simp [mkOfLimitNatTransApp_eq_of_lt φ ⊥
    (IsWellOrderLimitElement.bot_lt j)]
  natTrans_app_succ i h := by
    dsimp
    have h' := IsWellOrderLimitElement.wellOrderSucc_lt h
    rw [mkOfLimitNatTransApp_eq_of_lt φ _ h',
      (φ _ h').natTrans_app_succ i (self_lt_wellOrderSucc h),
      mkOfLimitNatTransApp_eq_of_lt φ _ h,
      congr_app (φ i h) ((truncFunctor ε (self_le_wellOrderSucc i)).map (φ (wellOrderSucc i) h'))]
    rfl

end

end Hom

variable (iter₁ iter₂) in
lemma nonempty_hom : Nonempty (iter₁ ⟶ iter₂) := by
  let P := fun (i : J) => ∀ (hi : i ≤ j),
    Nonempty ((truncFunctor ε hi).obj iter₁ ⟶ (truncFunctor ε hi).obj iter₂)
  suffices ∀ i, P i from this j (by rfl)
  refine fun _ => WellFoundedLT.induction _ (fun i hi hi' => ?_)
  obtain rfl|⟨i, rfl, hi''⟩|_ := eq_bot_or_eq_succ_or_isWellOrderLimitElement i
  · exact ⟨Hom.mkOfZero _ _⟩
  · exact ⟨Hom.mkOfSucc _ _ hi'' ((hi i hi'' (hi''.le.trans hi')).some)⟩
  · exact ⟨Hom.mkOfLimit (fun k hk => (hi k hk (hk.le.trans hi')).some)⟩

noncomputable instance : Unique (iter₁ ⟶ iter₂) :=
  uniqueOfSubsingleton (Nonempty.some (nonempty_hom _ _))

variable (iter₁ iter₂)

noncomputable def iso : iter₁ ≅ iter₂ where
  hom := default
  inv := default

@[simp]
lemma iso_refl : (iso iter₁ iter₁) = Iso.refl _ := by
  ext
  apply Subsingleton.elim

lemma iso_trans (iter₃ : Iteration ε j) :
    iso iter₁ iter₃ = iso iter₁ iter₂ ≪≫ iso iter₂ iter₃ := by
  ext
  apply Subsingleton.elim

variable (ε J) in
def mkOfBot : Iteration ε (⊥ : J) where
  F := (Functor.const _).obj (𝟭 C)
  isoZero := Iso.refl _
  isoSucc _ h := by simp at h
  mapSucc'_eq _ h := by simp at h
  isColimit x _ h := by
    exfalso
    exact (IsWellOrderLimitElement.neq_bot x) (by simpa using h)

section

variable {j : J} (F : { i | i ≤ j} ⥤ C) (X : C)
    (τ : F.obj ⟨j, le_refl j⟩ ⟶ X) (hj : j < wellOrderSucc j)

def mkFunctorOfSuccObj (i : J) : C :=
  if h : i ≤ j then F.obj ⟨i, h⟩ else X

def mkFunctorOfSuccObjIsoOfLE (i : J) (hi : i ≤ j) :
    mkFunctorOfSuccObj F X i ≅ F.obj ⟨i, hi⟩ := eqToIso (dif_pos hi)

noncomputable def mkFunctorOfSuccObjSuccIso :
    mkFunctorOfSuccObj F X (wellOrderSucc j) ≅ X := eqToIso (dif_neg (by aesop))

variable {X}

noncomputable def mkFunctorOfSuccMap (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ wellOrderSucc j):
    mkFunctorOfSuccObj F X i₁ ⟶ mkFunctorOfSuccObj F X i₂ :=
  if h₂ : i₂ ≤ j then
    (mkFunctorOfSuccObjIsoOfLE F X i₁ (hi.trans h₂)).hom ≫
      F.map (homOfLE (by exact hi)) ≫ (mkFunctorOfSuccObjIsoOfLE F X i₂ h₂).inv
  else
    if h₁ : i₁ ≤ j then
      (mkFunctorOfSuccObjIsoOfLE F X i₁ h₁).hom ≫ F.map (homOfLE (by exact h₁)) ≫ τ ≫
        (mkFunctorOfSuccObjSuccIso F X hj).inv ≫
        eqToHom (by rw [le_antisymm hi₂ (wellOrderSucc_le (not_le.1 h₂))])
    else
      eqToHom (by rw [le_antisymm hi (hi₂.trans (wellOrderSucc_le (not_le.1 h₁)))])

lemma mkFunctorOfSuccMap_eq_of_le₂ (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ j) :
    mkFunctorOfSuccMap F τ hj i₁ i₂ hi (hi₂.trans (self_le_wellOrderSucc j)) =
      (mkFunctorOfSuccObjIsoOfLE F X i₁ (hi.trans hi₂)).hom ≫
        F.map (homOfLE (by exact hi)) ≫ (mkFunctorOfSuccObjIsoOfLE F X i₂ hi₂).inv :=
  dif_pos hi₂

@[simp]
lemma mkFunctorOfSuccMap_id (i : J) (hi : i ≤ wellOrderSucc j) :
    mkFunctorOfSuccMap F τ hj i i (le_refl i) hi = 𝟙 _ := by
  by_cases hi' : i ≤ j
  · rw [mkFunctorOfSuccMap_eq_of_le₂ F τ hj i i (by rfl) (hi')]
    erw [Functor.map_id]
    rw [id_comp, Iso.hom_inv_id]
  · dsimp [mkFunctorOfSuccMap]
    rw [dif_neg hi', dif_neg hi']

lemma mkFunctorOfSuccMap_comp (i₁ i₂ i₃ : J) (h₁ : i₁ ≤ i₂) (h₂ : i₂ ≤ i₃) (h₃ : i₃ ≤ wellOrderSucc j) :
    mkFunctorOfSuccMap F τ hj i₁ i₃ (h₁.trans h₂) h₃ =
      mkFunctorOfSuccMap F τ hj i₁ i₂ h₁ (h₂.trans h₃) ≫ mkFunctorOfSuccMap F τ hj i₂ i₃ h₂ h₃ := by
  obtain h₄|rfl := h₃.lt_or_eq
  · replace h₄ : i₃ ≤ j := le_of_lt_wellOrderSucc h₄
    rw [mkFunctorOfSuccMap_eq_of_le₂ F τ hj i₁ i₂ _ (h₂.trans h₄),
      mkFunctorOfSuccMap_eq_of_le₂ F τ hj i₂ i₃ _ h₄,
      mkFunctorOfSuccMap_eq_of_le₂ F τ hj i₁ i₃ _ h₄]
    dsimp
    rw [assoc, assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc,
      homOfLE_comp]
  · obtain h₄|rfl := h₂.lt_or_eq
    · replace h₄ : i₂ ≤ j := le_of_lt_wellOrderSucc h₄
      rw [mkFunctorOfSuccMap_eq_of_le₂ F τ hj i₁ i₂ _ h₄]
      dsimp [mkFunctorOfSuccMap]
      rw [dif_neg (by aesop), dif_pos (h₁.trans h₄), dif_neg (by aesop), dif_pos h₄,
        comp_id, assoc, assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, homOfLE_comp]
    · rw [mkFunctorOfSuccMap_id, comp_id]

@[simps obj]
noncomputable def mkFunctorOfSucc : { i | i ≤ wellOrderSucc j } ⥤ C where
  obj i := mkFunctorOfSuccObj F X i
  map := @fun ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ φ => mkFunctorOfSuccMap F τ hj i₁ i₂ (by simpa using leOfHom φ) h₂
  map_comp := by
    rintro ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ ⟨i₃, h₃⟩ _ _
    exact mkFunctorOfSuccMap_comp F τ hj i₁ i₂ i₃ _ _ h₃

@[simp]
lemma mapSucc'_mkFunctorOfSucc :
    mapSucc' (mkFunctorOfSucc F τ hj) j hj =
      (mkFunctorOfSuccObjIsoOfLE F X j (le_refl j)).hom ≫ τ ≫ (mkFunctorOfSuccObjSuccIso F X hj).inv := by
  dsimp [mapSucc', mkFunctorOfSucc, mkFunctorOfSuccMap]
  rw [dif_neg (by aesop), dif_pos (le_refl j)]
  erw [Functor.map_id]
  simp

lemma mapSucc'_mkFunctorOfSucc_of_lt (i : J) (hi : i < j) :
    mapSucc' (mkFunctorOfSucc F τ hj) i (hi.trans hj) = (mkFunctorOfSuccObjIsoOfLE F X i hi.le).hom ≫
      F.map (homOfLE (by exact self_le_wellOrderSucc i)) ≫
        (mkFunctorOfSuccObjIsoOfLE F X (wellOrderSucc i) (wellOrderSucc_le hi)).inv := by
  apply mkFunctorOfSuccMap_eq_of_le₂

noncomputable def restrictionLEMkFunctorOfSuccIso :
    restrictionLE (mkFunctorOfSucc F τ hj) (self_le_wellOrderSucc j) ≅ F :=
  NatIso.ofComponents (fun ⟨i, hi⟩ => mkFunctorOfSuccObjIsoOfLE _ _ _ _) (by
    rintro ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩ f
    dsimp [mkFunctorOfSucc]
    rw [mkFunctorOfSuccMap_eq_of_le₂ _ _ _ _ _ _ hi₂, assoc, assoc, Iso.inv_hom_id, comp_id]
    rfl)

noncomputable def restrictionLTMkFunctorOfSucc (i : J) (h : i ≤ j) :
    restrictionLT (mkFunctorOfSucc F τ hj) (h.trans (self_le_wellOrderSucc j)) ≅
      restrictionLT F h :=
  isoWhiskerLeft (monotone_inclusion_lt_le_of_le h).functor
    (restrictionLEMkFunctorOfSuccIso F τ hj)

end

noncomputable def mkOfSucc (j : J) (hj : j < wellOrderSucc j) (iter : Iteration ε j) :
    Iteration ε (wellOrderSucc j) where
  F := mkFunctorOfSucc iter.F (whiskerLeft _ ε) hj
  isoZero := mkFunctorOfSuccObjIsoOfLE _ _ _ _ ≪≫ iter.isoZero
  isoSucc i hi :=
    if h : i < j then mkFunctorOfSuccObjIsoOfLE _ _ _ _ ≪≫ iter.isoSucc i h ≪≫
      isoWhiskerRight ((mkFunctorOfSuccObjIsoOfLE _ _ _ _).symm) Φ
    else by
      obtain rfl : j = i := le_antisymm (not_lt.1 h) (le_of_lt_wellOrderSucc hi)
      exact mkFunctorOfSuccObjSuccIso _ _ hj ≪≫
        isoWhiskerRight ((mkFunctorOfSuccObjIsoOfLE iter.F (iter.F.obj ⟨j, le_refl j⟩ ⋙ Φ) j (le_refl j)).symm) _
  mapSucc'_eq i hi := by
    dsimp
    split_ifs with h
    · rw [mapSucc'_mkFunctorOfSucc_of_lt _ _ _ _ h]
      ext X
      dsimp
      rw [assoc]
      erw [← ε.naturality_assoc, congr_app (iter.mapSucc_eq i h) X, assoc]
      rfl
    · obtain rfl : j = i := le_antisymm (not_lt.1 h) (le_of_lt_wellOrderSucc hi)
      dsimp
      simp
      ext X
      apply ε.naturality
  isColimit i _ hi := by
    have hi' : i ≤ j := by
      obtain hi''|rfl := hi.lt_or_eq
      · exact le_of_lt_wellOrderSucc hi''
      · exfalso
        exact IsWellOrderLimitElement.neq_succ j hj
    apply (IsColimit.precomposeHomEquiv (restrictionLTMkFunctorOfSucc iter.F
      (whiskerLeft _ ε) hj i hi').symm _).1
    refine' IsColimit.ofIsoColimit (iter.isColimit i hi')
      (Cocones.ext (mkFunctorOfSuccObjIsoOfLE _ _ _ _).symm (fun ⟨k, hk⟩ => _))
    dsimp [restrictionLTMkFunctorOfSucc, restrictionLEMkFunctorOfSuccIso,
      mkFunctorOfSucc]
    rw [mkFunctorOfSuccMap_eq_of_le₂ _ _ _ _ _ _ hi', Iso.inv_hom_id_assoc]

section

variable (F : { i | i < j } ⥤ C) (c : Cocone F)

def mkFunctorOfCoconeObj (i : J) : C :=
  if h : i < j then F.obj ⟨i, h⟩ else c.pt

def mkFunctorOfCoconeObjIso (i : J) (hi : i < j) :
    mkFunctorOfCoconeObj F c i ≅ F.obj ⟨i, hi⟩ := eqToIso (dif_pos hi)

def mkFunctorOfCoconeObjTopIso :
    mkFunctorOfCoconeObj F c j ≅ c.pt := eqToIso (dif_neg (by aesop))

def mkFunctorOfCoconeMap (i₁ i₂ : J) (h₁ : i₁ ≤ i₂) (h₂ : i₂ ≤ j) :
    mkFunctorOfCoconeObj F c i₁ ⟶ mkFunctorOfCoconeObj F c i₂ :=
  if h₃ : i₂ < j then
    (mkFunctorOfCoconeObjIso F c i₁ (lt_of_le_of_lt h₁ h₃)).hom ≫ F.map (homOfLE (by exact h₁)) ≫ (mkFunctorOfCoconeObjIso F c i₂ h₃).inv
  else
    if h₄ : i₁ < j then
      (mkFunctorOfCoconeObjIso F c i₁ h₄).hom ≫ c.ι.app _ ≫
        (mkFunctorOfCoconeObjTopIso F c).inv ≫ eqToHom (by
          rw [le_antisymm h₂ (by simpa using h₃)])
    else
      eqToHom (by rw [le_antisymm h₁ (h₂.trans (by simpa using h₄))])

@[simp]
lemma mkFunctorOfCoconeMap_id (i : J) (h : i ≤ j) :
    mkFunctorOfCoconeMap F c i i (le_refl i) h = 𝟙 _ := by
  dsimp [mkFunctorOfCoconeMap]
  split_ifs with h'
  · erw [Functor.map_id, id_comp, Iso.hom_inv_id]
  · rfl

lemma mkFunctorOfCoconeMap_of_lt (i₁ i₂ : J) (h₁ : i₁ ≤ i₂) (h₂ : i₂ < j) :
    mkFunctorOfCoconeMap F c i₁ i₂ h₁ h₂.le =
      (mkFunctorOfCoconeObjIso F c i₁ (lt_of_le_of_lt h₁ h₂)).hom ≫
        F.map (homOfLE (by exact h₁)) ≫
        (mkFunctorOfCoconeObjIso F c i₂ h₂).inv := dif_pos h₂

lemma mkFunctorOfCoconeMap_of_lt_top (i : J) (hi : i < j) :
    mkFunctorOfCoconeMap F c i j hi.le (le_refl j) =
      (mkFunctorOfCoconeObjIso F c i hi).hom ≫ c.ι.app _ ≫
        (mkFunctorOfCoconeObjTopIso F c).inv := by
  dsimp [mkFunctorOfCoconeMap]
  rw [dif_pos hi, dif_neg (by simp), comp_id]

lemma mkFunctorOfCoconeMap_comp (i₁ i₂ i₃ : J) (h₁ : i₁ ≤ i₂) (h₂ : i₂ ≤ i₃) (h₃ : i₃ ≤ j) :
    mkFunctorOfCoconeMap F c i₁ i₃ (h₁.trans h₂) h₃ =
      mkFunctorOfCoconeMap F c i₁ i₂ h₁ (h₂.trans h₃) ≫
        mkFunctorOfCoconeMap F c i₂ i₃ h₂ h₃ := by
  clear iter₁ iter₂
  obtain h₄|rfl := h₃.lt_or_eq
  · rw [mkFunctorOfCoconeMap_of_lt F c i₁ i₃ _ h₄,
      mkFunctorOfCoconeMap_of_lt F c i₂ i₃ _ h₄,
      mkFunctorOfCoconeMap_of_lt F c i₁ i₂ _ (lt_of_le_of_lt h₂ h₄),
      assoc, assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc,
      homOfLE_comp]
  · obtain h₄|rfl := h₂.lt_or_eq
    · rw [mkFunctorOfCoconeMap_of_lt_top F c i₂ h₄,
        mkFunctorOfCoconeMap_of_lt_top F c i₁ (lt_of_le_of_lt h₁ h₄),
        mkFunctorOfCoconeMap_of_lt F c i₁ i₂ _ h₄,
        assoc, assoc, Iso.inv_hom_id_assoc, Cocone.w_assoc]
    · simp

@[simps! obj map]
def mkFunctorOfCocone : { i | i ≤ j } ⥤ C where
  obj := fun ⟨i, _⟩ => mkFunctorOfCoconeObj F c i
  map := @fun ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ φ => mkFunctorOfCoconeMap F c i₁ i₂ (leOfHom φ) h₂
  map_comp := by
    rintro ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ ⟨i₃, h₃⟩ f g
    exact mkFunctorOfCoconeMap_comp F c i₁ i₂ i₃ _ _ h₃

end

variable (j)
variable [IsWellOrderLimitElement j] (iter : ∀ (i : J) (_ : i < j), Iteration ε i)

@[simps]
noncomputable def mkOfLimitFunctor : {i | i < j} ⥤ C ⥤ C where
  obj := fun ⟨i, hi⟩ => (iter i hi).F.obj ⟨i, le_refl _⟩
  map := @fun ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ φ => (eval ε (le_refl i₁)).map (iso (iter i₁ h₁) ((iter i₂ h₂).trunc (leOfHom φ : i₁ ≤ i₂))).hom ≫
    (iter i₂ h₂).F.map (homOfLE (by exact leOfHom φ))
  map_id := fun ⟨i, h⟩ => by
    dsimp
    erw [Functor.map_id, comp_id, iso_refl]
    rfl
  map_comp := by
    rintro ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ ⟨i₃, h₃⟩ f g
    have hf : i₁ ≤ i₂ := leOfHom f
    have hg : i₂ ≤ i₃ := leOfHom g
    dsimp
    rw [assoc, NatTrans.naturality_assoc,
      iso_trans (iter i₁ h₁) (trunc (iter i₂ h₂) (leOfHom f)) (trunc (iter i₃ h₃) _)]
    dsimp
    rw [assoc, ← Functor.map_comp, Subsingleton.elim
      (iso (trunc (iter i₂ h₂) hf) (trunc (iter i₃ h₃) (hf.trans hg))).hom
      ((truncFunctor ε hf).map ((iso (iter i₂ h₂) (trunc (iter i₃ h₃) (leOfHom g))).hom))]
    rfl

noncomputable def mkOfLimit [HasColimit (mkOfLimitFunctor j iter)] :
    Iteration ε j where
  F := mkFunctorOfCocone (mkOfLimitFunctor j iter) (colimit.cocone _)
  isoZero := mkFunctorOfCoconeObjIso _ _ _ _ ≪≫ (iter ⊥ (IsWellOrderLimitElement.bot_lt j)).isoZero
  isoSucc i hi := by
    refine' mkFunctorOfCoconeObjIso _ _ _ (IsWellOrderLimitElement.wellOrderSucc_lt hi) ≪≫
      (iter (wellOrderSucc i) _).isoSucc i (self_lt_wellOrderSucc hi) ≪≫
      isoWhiskerRight (?_ ≪≫ (mkFunctorOfCoconeObjIso _ _ _ hi).symm) Φ
    exact (eval ε (le_refl i)).mapIso (iso (iter i hi) ((iter (wellOrderSucc i) (IsWellOrderLimitElement.wellOrderSucc_lt hi)).trunc (self_le_wellOrderSucc i))).symm
  mapSucc'_eq i hi := by
    have hi' := (IsWellOrderLimitElement.wellOrderSucc_lt hi)
    have hi'' := self_lt_wellOrderSucc hi
    have h := (iter (wellOrderSucc i) hi').mapSucc_eq _ hi''
    dsimp [mapSucc', mapSucc] at h ⊢
    rw [mkFunctorOfCoconeMap_of_lt _ _ _ _ _ hi']
    dsimp
    simp only [assoc, whiskerRight_comp, h]
    ext X
    dsimp
    erw [ε.naturality_assoc, ε.naturality_assoc]
  isColimit := sorry

end Iteration

section

variable (C J)

class HasIterationOfShape : Prop where
  hasColimitsOfShape_of_limit (j : J) [IsWellOrderLimitElement j] :
    HasColimitsOfShape { i | i < j } C := by infer_instance
  hasColimitsOfShape : HasColimitsOfShape J C := by infer_instance

instance [HasColimitsOfSize.{u, u} C] : HasIterationOfShape C J where

variable [HasIterationOfShape C J]

instance : HasColimitsOfShape J C := HasIterationOfShape.hasColimitsOfShape

variable {C}

instance hasColimitsOfShape_of_hasIterationOfShape (j : J) [IsWellOrderLimitElement j] :
    HasColimitsOfShape { i | i < j } C := HasIterationOfShape.hasColimitsOfShape_of_limit _

end

variable (C J) in
def nonempty_iteration [HasIterationOfShape C J] (j : J) : Nonempty (Iteration ε j) := by
  refine' WellFoundedLT.induction (C := fun i => Nonempty (Iteration ε i)) j (fun j hj => _)
  obtain rfl|⟨i, rfl, hi⟩|_ := eq_bot_or_eq_succ_or_isWellOrderLimitElement j
  · exact ⟨Iteration.mkOfBot ε J⟩
  · exact ⟨Iteration.mkOfSucc i hi (hj i hi).some⟩
  · exact ⟨Iteration.mkOfLimit _ (fun i hi => (hj i hi).some)⟩

end Functor

end CategoryTheory
