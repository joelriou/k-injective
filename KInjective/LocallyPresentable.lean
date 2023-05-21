import Mathlib.CategoryTheory.Limits.HasLimits
import KInjective.Presentable

universe w v u

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C]

class LocallyPresentable (κ : Cardinal.{w}) [HasColimitsOfSize.{w, w} C] where
  isRegular : κ.IsRegular
  α : Type w
  obj : α → C 
  obj_presentable (a : α) : Presentable (obj a) κ
  exists_presentation : ∀ (Y : C), ∃ (I : Type w) (_ : SmallCategory I) (_ : IsCardinalFiltered I κ)
    (G : I ⥤ C) (_ : ∀ (i : I), G.obj i ∈ Set.range obj), Nonempty (colimit G ≅ Y)
  
end CategoryTheory


