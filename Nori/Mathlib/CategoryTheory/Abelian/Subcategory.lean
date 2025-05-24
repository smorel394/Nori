import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.ObjectProperty.EpiMono
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

noncomputable section

universe v u

namespace CategoryTheory

open Limits ZeroObject Category

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)

namespace ObjectProperty

/-
TODO: a version where we just require one kernel (resp. cokernel, resp. product)
satisfying `P`, so we get non-thick abelian subcategories.
-/

class IsClosedUnderKernels where
  prop_of_kernel {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ X) (zero : g ≫ f = 0) (hX : P X)
    (hY : P Y) (lim : IsLimit (KernelFork.ofι g zero)) : P Z

lemma prop_of_kernel [P.IsClosedUnderKernels] {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ X)
    (zero : g ≫ f = 0) (hX : P X) (hY : P Y) (lim : IsLimit (KernelFork.ofι g zero)) : P Z :=
  IsClosedUnderKernels.prop_of_kernel f g zero hX hY lim

/-
Should probably generalize this to limits of more general shapes, and use
in the proof that fully faithful functors reflects limits.
-/
lemma hasKernels_of_isClosedUnderKernels [P.IsClosedUnderKernels] :
    HasKernels P.FullSubcategory where
  has_limit {X Y} f := by
    let Z : P.FullSubcategory := ⟨kernel (P.ι.map f), P.prop_of_kernel (P.ι.map f)
      (kernel.ι (P.ι.map f)) (kernel.condition _) X.2 Y.2 (kernelIsKernel _)⟩
    let c : Fork f 0 := Fork.ofι (P := Z) (kernel.ι (P.ι.map f))
      (by rw [comp_zero]; exact kernel.condition _)
    refine HasLimit.mk
      {cone := c,
       isLimit := IsLimit.mk (fun  s ↦ kernel.lift (P.ι.map f) (P.ι.map (Fork.ι s))
         (KernelFork.condition s)) (fun s j ↦ ?_) (fun s m h ↦ ?_)}
    · match j with
      | WalkingParallelPair.zero => exact kernel.lift_ι (P.ι.map f) _ _
      | WalkingParallelPair.one => dsimp; simp [KernelFork.app_one]
    · rw [← cancel_mono (kernel.ι (P.ι.map f))]
      erw [kernel.lift_ι]
      exact h WalkingParallelPair.zero

lemma isClosedUnderIsomorphisms_of_isClosedUnderKernels [P.IsClosedUnderKernels]
    [P.ContainsZero] : P.IsClosedUnderIsomorphisms where
  of_iso {X Y} f hX := by
    obtain ⟨Z, h₁, h₂⟩ := P.exists_prop_of_containsZero
    have : IsLimit (KernelFork.ofι (X := X) (Y := Z) (f := 0) f.inv (by simp)) :=
      Fork.IsLimit.mk _ (fun s ↦ s.ι ≫ f.hom) (fun _ ↦ by simp)
      (fun _ _ h ↦ by dsimp; rw [← h]; simp)
    exact P.prop_of_kernel (0 : X ⟶ Z) f.inv (by simp) hX h₂ this

class IsClosedUnderCokernels where
  prop_of_cokernel {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (zero : f ≫ g = 0) (hX : P X)
    (hY : P Y) (colim : IsColimit (CokernelCofork.ofπ g zero)) : P Z

lemma prop_of_cokernel [P.IsClosedUnderCokernels] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (zero : f ≫ g = 0) (hX : P X) (hY : P Y)
    (colim : IsColimit (CokernelCofork.ofπ g zero)) : P Z :=
  IsClosedUnderCokernels.prop_of_cokernel f g zero hX hY colim

lemma hasCokernels_of_isClosedUnderCokernels [P.IsClosedUnderCokernels] :
    HasCokernels P.FullSubcategory where
  has_colimit {X Y} f := by sorry

lemma isClosedUnderIsomorphisms_of_isClosedUnderCokernels [P.IsClosedUnderCokernels]
    [P.ContainsZero] : P.IsClosedUnderIsomorphisms where
  of_iso {X Y} f hX := by
    obtain ⟨Z, h₁, h₂⟩ := P.exists_prop_of_containsZero
    have : IsColimit (CokernelCofork.ofπ (X := Z) (Y := X) (f := 0) f.hom (by simp)) := by
      refine Cofork.IsColimit.mk _ (fun s ↦ f.inv ≫ s.π) (fun _ ↦ by simp)
        (fun _ _ h ↦ by dsimp; rw [← h]; simp)
    exact P.prop_of_cokernel (0 : Z ⟶ X) f.hom (by simp) h₂ hX this

class IsClosedUnderFiniteProducts where
  prop_of_product (n : ℕ) (c : Fin n → C) (hc : ∀ i, P (c i)) : P (∏ᶜ c)
-- This should say that there exists a product satisfying `P`.

lemma hasFiniteProducts_of_isClosedUnderFiniteProducts [P.IsClosedUnderFiniteProducts] :
    HasFiniteProducts P.FullSubcategory := sorry

lemma prop_of_product' [P.IsClosedUnderFiniteProducts] (n : ℕ) (c : Fin n → C)
    (hc : ∀ i, P (c i)) : P (∏ᶜ c) := IsClosedUnderFiniteProducts.prop_of_product n c hc

lemma prop_of_product [P.IsClosedUnderFiniteProducts] [P.IsClosedUnderIsomorphisms]
    {J : Type*} [Finite J] (c : J → C) (hc : ∀ j, P (c j)) : P (∏ᶜ c) := by
  rcases Finite.exists_equiv_fin J with ⟨n, ⟨e⟩⟩
  set e := HasLimit.isoOfEquivalence (F := Discrete.functor c)
    (G := Discrete.functor (c.comp e.invFun)) (Discrete.equivalence e)
    (by refine NatIso.ofComponents (fun _ ↦ eqToIso (by simp)) ?_
        intro X Y f
        dsimp
        have := Discrete.eq_of_hom f
        have eq : f = Discrete.eqToHom this := Subsingleton.elim _ _
        rw [eq]
        simp only [eqToHom_map, Discrete.functor_obj_eq_as, Function.comp_apply, eqToHom_trans])
  exact P.prop_of_iso e.symm (P.prop_of_product' n _ (fun _ ↦ hc _))

class IsAbelian : Prop extends P.ContainsZero, P.IsClosedUnderKernels, P.IsClosedUnderCokernels,
  P.IsClosedUnderFiniteProducts

variable [P.IsAbelian]

instance : P.IsClosedUnderIsomorphisms := P.isClosedUnderIsomorphisms_of_isClosedUnderKernels

instance : Abelian P.FullSubcategory := by
  have : HasKernels P.FullSubcategory := P.hasKernels_of_isClosedUnderKernels
  have : HasCokernels P.FullSubcategory := P.hasCokernels_of_isClosedUnderCokernels
  have : HasFiniteProducts P.FullSubcategory := P.hasFiniteProducts_of_isClosedUnderFiniteProducts
  have : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := sorry
  exact Abelian.ofCoimageImageComparisonIsIso

end ObjectProperty
