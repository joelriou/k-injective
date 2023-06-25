import Mathlib.CategoryTheory.Limits.HasLimits
import KInjective.Presentable

universe w v u

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C]

-- TODO: should we set w = v?

class LocallyPresentable (κ : Cardinal.{w}) [HasColimitsOfSize.{w, w} C] where
  isRegular : κ.IsRegular
  obj : Set C
  small_obj : Small.{w} obj
  presentableObj (X : C) (hX : X ∈ obj) : Presentable X κ
  exists_presentation : ∀ (Y : C), ∃ (I : Type w) (_ : SmallCategory I) (_ : IsCardinalFiltered I κ)
    (G : I ⥤ C) (_ : ∀ (i : I), G.obj i ∈ obj), Nonempty (colimit G ≅ Y)

variable (κ : Cardinal.{w}) [HasColimitsOfSize.{w, w} C] [LocallyPresentable C κ]

-- show that there is obj' : β → C (with β : Type w) such that the image of obj'
-- is all presentable objects
  
end CategoryTheory


