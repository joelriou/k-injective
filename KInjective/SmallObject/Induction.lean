import KInjective.SmallObject.WellOrderContinuous

universe v u

namespace CategoryTheory

open Opposite

namespace Functor

variable {J : Type u} [LinearOrder J] [IsWellOrder J (· < ·)] (F : Jᵒᵖ ⥤ Type v)

def _root_.PrincipalSegLimit.ofElementSectionsMk {j : J} [IsWellOrderLimitElement j] (x : F.obj (op j)):
    (((PrincipalSegLimit.ofElement j).functorToOver ⋙
      Over.forget _).op ⋙ F).sections where
  val a := F.map (homOfLE a.unop.2.le).op x
  property _ := by
    dsimp
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp]

structure WellOrderInductionData where
  succ (j : J) : F.obj (op j) → F.obj (op (wellOrderSucc j))
  map_succ (j : J) (x : F.obj (op j)) : F.map (homOfLE (le_wellOrderSucc j)).op (succ j x) = x
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
  map_succ (i : J) (hi : wellOrderSucc i ≤ j) :
    F.map (homOfLE hi).op val =
      d.succ i (F.map (homOfLE ((le_wellOrderSucc i).trans hi)).op val)
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
      homOfLE_comp, homOfLE_comp, e.map_succ k (hk.trans h)]
  map_desc k _ hk := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp]
    exact e.map_desc k (hk.trans h)

instance (j : J) : Subsingleton (d.Extension val₀ j) := sorry

lemma compatibility {j : J} (e : d.Extension val₀ j) {i : J}
    (e' : d.Extension val₀ i) (h : i ≤ j) :
    F.map (homOfLE h).op e.val = e'.val := by
  obtain rfl : e' = e.ofLE h := Subsingleton.elim _ _
  rfl

instance (j : J) : Unique (d.Extension val₀ j) := sorry

end Extension

variable (val₀ : F.obj (op ⊥))

def sectionsMk : F.sections where
  val j := (default : d.Extension val₀ j.unop).val
  property _ := Extension.compatibility _ _ _

end WellOrderInductionData

end Functor

end CategoryTheory
