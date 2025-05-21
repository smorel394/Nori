/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

universe v u u₁

open CategoryTheory.Preadditive Opposite CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

instance : (preadditiveYoneda (C := C)).Additive where
  map_add {_ _ f g} := by
    ext _ h
    change h ≫ (f + g) = h ≫ f + h ≫ g
    rw [comp_add]

instance : (preadditiveCoyoneda (C := C)).Additive where
  map_add {_ _ f g} := by
    ext _ h
    change (f + g).unop ≫ h = f.unop ≫ h + g.unop ≫ h
    rw [unop_add, add_comp]

end CategoryTheory
