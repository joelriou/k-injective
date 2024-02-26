import KInjective.SmallObject.WellOrderContinuous

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

variable {j : J} (F : { i | i ≤ j } ⥤ C ⥤ C)

section

variable {i : J} (hi : i ≤ j)

def restrictionLT : { k | k < i } ⥤ C ⥤ C :=
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

def restrictionLE : { k | k ≤ i } ⥤ C ⥤ C :=
  (monotone_inclusion_le_le_of_le hi).functor ⋙ F

@[simp]
lemma restrictionLE_obj (k : J) (hk : k ≤ i) :
    (restrictionLE F hi).obj ⟨k, hk⟩ = F.obj ⟨k, hk.trans hi⟩ := rfl

@[simp]
lemma restrictionLE_map {k₁ k₂ : { k | k ≤ i }} (φ : k₁ ⟶ k₂) :
    (restrictionLE F hi).map φ = F.map (homOfLE (by simpa using leOfHom φ)) := rfl

end

noncomputable abbrev mapSucc' (i : J) (hi : i < j) :
    F.obj ⟨i, hi.le⟩ ⟶ F.obj ⟨wellOrderSucc i, wellOrderSucc_le hi⟩ :=
  F.map (homOfLE (by simpa only [Subtype.mk_le_mk] using self_le_wellOrderSucc i))

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
@[reassoc]
lemma natTrans_naturality (φ : iter₁ ⟶ iter₂) (i₁ i₂ : J) (h : i₁ ≤ i₂) (h' : i₂ ≤ j) :
    iter₁.F.map (by exact homOfLE h) ≫ φ.natTrans.app ⟨i₂, h'⟩ =
      φ.natTrans.app ⟨i₁, h.trans h'⟩ ≫ iter₂.F.map (by exact homOfLE h) := by
  apply φ.natTrans.naturality

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

noncomputable def iso : iter₁ ≅ iter₂ where
  hom := default
  inv := default

end Iteration

end Functor

end CategoryTheory
