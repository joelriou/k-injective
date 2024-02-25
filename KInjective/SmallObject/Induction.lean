import KInjective.SmallObject.WellOrderContinuous

universe v u

namespace CategoryTheory

open Opposite

namespace Functor

variable {J : Type u} [LinearOrder J] [IsWellOrder J (· < ·)] (F : Jᵒᵖ ⥤ Type v)

@[simps]
def _root_.PrincipalSegLimit.ofElementSectionsMk {j : J} [IsWellOrderLimitElement j] (x : F.obj (op j)):
    (((PrincipalSegLimit.ofElement j).functorToOver ⋙
      Over.forget _).op ⋙ F).sections where
  val a := F.map (homOfLE a.unop.2.le).op x
  property _ := by
    dsimp
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp]

structure WellOrderInductionData where
  succ (j : J) : F.obj (op j) → F.obj (op (wellOrderSucc j))
  map_succ (j : J) (hj : j < wellOrderSucc j) (x : F.obj (op j)) : F.map (homOfLE (self_le_wellOrderSucc j)).op (succ j x) = x
  desc (j : J) [IsWellOrderLimitElement j] (x : (((PrincipalSegLimit.ofElement j).functorToOver ⋙
      Over.forget _).op ⋙ F).sections) : F.obj (op j)
  fac (j : J) [IsWellOrderLimitElement j]
    (x : (((PrincipalSegLimit.ofElement j).functorToOver ⋙
      Over.forget _).op ⋙ F).sections) (a : { x | x < j }) :
        x.val (op a) = F.map (homOfLE (le_of_lt a.2)).op (desc j x)

namespace WellOrderInductionData

variable {F} [OrderBot J]
variable (d : F.WellOrderInductionData)

structure Extension (val₀ : F.obj (op ⊥)) (j : J) where
  val : F.obj (op j)
  map_zero : F.map (homOfLE bot_le).op val = val₀
  map_succ (i : J) (hi : i < j) :
    F.map (homOfLE (wellOrderSucc_le hi)).op val =
      d.succ i (F.map (homOfLE hi.le).op val)
  map_desc (i : J) [IsWellOrderLimitElement i] (hi : i ≤ j) :
    F.map (homOfLE hi).op val = d.desc i (PrincipalSegLimit.ofElementSectionsMk F (F.map (homOfLE hi).op val))

namespace Extension

variable {d}
variable {val₀ : F.obj (op ⊥)}

def ofLE {j : J} (e : d.Extension val₀ j) {i : J} (h : i ≤ j) :
    d.Extension val₀ i where
  val := F.map (homOfLE h).op e.val
  map_zero := by rw [← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp, e.map_zero]
  map_succ k hk := by
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp,
      homOfLE_comp, homOfLE_comp, e.map_succ k (lt_of_lt_of_le hk h)]
  map_desc k _ hk := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp]
    exact e.map_desc k (hk.trans h)

lemma ext' {e e' : d.Extension val₀ j} (h : e.val = e'.val) : e = e' := by
  cases e
  cases e'
  subst h
  rfl

instance (j : J) : Subsingleton (d.Extension val₀ j) := by
  apply @WellFoundedLT.induction J _ _ (fun j => Subsingleton (d.Extension val₀ j))
  intro j hj
  obtain rfl|⟨i, rfl, hi⟩|_ := eq_bot_or_eq_succ_or_isWellOrderLimitElement j
  · refine Subsingleton.intro (fun e₁ e₂ => ext' ?_)
    have h₁ := e₁.map_zero
    have h₂ := e₂.map_zero
    erw [Functor.map_id] at h₁ h₂
    dsimp at h₁ h₂
    rw [h₁, h₂]
  · refine Subsingleton.intro (fun e₁ e₂ => ext' ?_)
    have h₁ := e₁.map_succ i hi
    have h₂ := e₂.map_succ i hi
    erw [Functor.map_id] at h₁ h₂
    dsimp at h₁ h₂
    rw [h₁, h₂]
    congr 1
    have := hj i hi
    exact congr_arg Extension.val (Subsingleton.elim (e₁.ofLE hi.le) (e₂.ofLE hi.le))
  · refine Subsingleton.intro (fun e₁ e₂ => ext' ?_)
    have h₁ := e₁.map_desc j (by rfl)
    have h₂ := e₂.map_desc j (by rfl)
    erw [Functor.map_id] at h₁ h₂
    dsimp at h₁ h₂
    rw [h₁, h₂]
    congr 1
    ext ⟨a, ha : a < j⟩
    dsimp
    have := hj a ha
    exact congr_arg Extension.val (Subsingleton.elim (e₁.ofLE ha.le) (e₂.ofLE ha.le))

lemma compatibility {j : J} (e : d.Extension val₀ j) {i : J}
    (e' : d.Extension val₀ i) (h : i ≤ j) :
    F.map (homOfLE h).op e.val = e'.val := by
  obtain rfl : e' = e.ofLE h := Subsingleton.elim _ _
  rfl

end Extension

variable (val₀)

def extensionZero : d.Extension val₀ ⊥ where
  val := val₀
  map_zero := by
    erw [Functor.map_id]
    rfl
  map_succ i hi := by simp at hi
  map_desc i _ hi := by
    exfalso
    exact IsWellOrderLimitElement.neq_bot i (by simpa using hi)

variable {val₀}

def extensionSucc {j : J} (e : d.Extension val₀ j) (hj : j < wellOrderSucc j) :
    d.Extension val₀ (wellOrderSucc j) where
  val := d.succ j e.val
  map_zero := by
    have h := congr_arg (F.map (homOfLE (bot_le : ⊥ ≤ j)).op) (d.map_succ j hj e.val)
    rw [e.map_zero, ← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp] at h
    exact h
  map_succ := sorry
  map_desc i _ hi := by
    obtain rfl|hi' := eq_or_lt_of_le hi
    · simpa using IsWellOrderLimitElement.neq_succ _ hj
    · have hij : i ≤ j := (le_of_lt_wellOrderSucc hi')
      have h := congr_arg (F.map (homOfLE hij).op) (d.map_succ j hj e.val)
      rw [e.map_desc i (le_of_lt_wellOrderSucc hi'), ← FunctorToTypes.map_comp_apply,
        ← op_comp, homOfLE_comp] at h
      rw [h]
      congr 1
      ext ⟨a, ha⟩
      dsimp
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp, ← d.fac i _ ⟨a, ha⟩]
      dsimp
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp]

variable (val₀) in

def extensionLimit (j : J) [IsWellOrderLimitElement j]
    (e : ∀ (i : J) (hi : i < j), d.Extension val₀ i) :
    d.Extension val₀ j := sorry

instance (j : J) : Nonempty (d.Extension val₀ j) := by
  apply @WellFoundedLT.induction J _ _ (fun j => Nonempty (d.Extension val₀ j))
  intro j hj
  obtain rfl|⟨i, rfl, hi⟩|_ := eq_bot_or_eq_succ_or_isWellOrderLimitElement j
  · exact ⟨d.extensionZero val₀⟩
  · exact ⟨d.extensionSucc (hj i hi).some hi⟩
  · exact ⟨d.extensionLimit val₀ j (fun i hi => (hj i hi).some)⟩

noncomputable instance (j : J) : Unique (d.Extension val₀ j) :=
  uniqueOfSubsingleton (Nonempty.some inferInstance)

variable (val₀ : F.obj (op ⊥))

noncomputable def sectionsMk : F.sections where
  val j := (default : d.Extension val₀ j.unop).val
  property _ := Extension.compatibility _ _ _

end WellOrderInductionData

end Functor

end CategoryTheory
