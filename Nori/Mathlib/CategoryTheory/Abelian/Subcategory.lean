import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.ObjectProperty.EpiMono
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

noncomputable section

universe v u u' v'

namespace CategoryTheory

open Limits ZeroObject Category

variable {J : Type u'} [Category.{v'} J]  {C : Type u} [Category.{v} C] (P : ObjectProperty C)

namespace ObjectProperty

section ContainsLimit

class ContainsLimit (F : J ⥤ P.FullSubcategory) where
    contains_limit : ∃ (c : Cone F), Nonempty (IsLimit (F := F ⋙ P.ι) (P.ι.mapCone c))

lemma exists_limit_of_containsLimit (F : J ⥤ P.FullSubcategory) [P.ContainsLimit F] :
    ∃ (c : Cone F), Nonempty (IsLimit (P.ι.mapCone c)) := ContainsLimit.contains_limit

instance HasLimitOfContainsLimit (F : J ⥤ P.FullSubcategory) [P.ContainsLimit F] :
    HasLimit F where
  exists_limit :=
    let h := exists_limit_of_containsLimit P F
    Nonempty.intro {cone := Classical.choose h,
                    isLimit := isLimitOfReflects P.ι (Classical.choice (Classical.choose_spec h))}

instance PreservesLimitOfContainsLimit (F : J ⥤ P.FullSubcategory) [P.ContainsLimit F] :
    PreservesLimit F P.ι where
  preserves hc :=
    let ⟨_, hd⟩ := exists_limit_of_containsLimit P F
    Nonempty.intro (IsLimit.ofIsoLimit (Classical.choice hd) ((Cones.functoriality _ P.ι).mapIso
      ((isLimitOfReflects P.ι (Classical.choice hd)).uniqueUpToIso hc)))

class ContainsColimit (F : J ⥤ P.FullSubcategory) where
    contains_colimit : ∃ (c : Cocone F), Nonempty (IsColimit (F := F ⋙ P.ι) (P.ι.mapCocone c))

lemma exists_colimit_of_containsColimit (F : J ⥤ P.FullSubcategory) [P.ContainsColimit F] :
    ∃ (c : Cocone F), Nonempty (IsColimit (P.ι.mapCocone c)) := ContainsColimit.contains_colimit

instance HasColimitOfContainsColimit (F : J ⥤ P.FullSubcategory) [P.ContainsColimit F] :
    HasColimit F where
  exists_colimit :=
    let h := exists_colimit_of_containsColimit P F
    Nonempty.intro {cocone := Classical.choose h,
                    isColimit := isColimitOfReflects P.ι (Classical.choice
                                 (Classical.choose_spec h))}

instance PreservesColimitOfContainsColimit (F : J ⥤ P.FullSubcategory) [P.ContainsColimit F] :
    PreservesColimit F P.ι where
  preserves hc :=
    let ⟨_, hd⟩ := exists_colimit_of_containsColimit P F
    Nonempty.intro (IsColimit.ofIsoColimit (Classical.choice hd)
      ((Cocones.functoriality _ P.ι).mapIso ((isColimitOfReflects P.ι
      (Classical.choice hd)).uniqueUpToIso hc)))

end ContainsLimit

section KernelsCokernels

variable [Preadditive C]
/- This should be `HasZeroMorphisms`, but I'm afraid of a diamond because `Preadditive C`
gives `Preadditive P.FullSubcategory` which gives `HasZeroMorphisms P.FullSubcatgeory`...

-/

class ContainsKernels where
    contains_kernel : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y), P.ContainsLimit (parallelPair f 0)

instance [P.ContainsKernels] : HasKernels P.FullSubcategory where
  has_limit f := by
    have : P.ContainsLimit (parallelPair f 0) := ContainsKernels.contains_kernel f
    infer_instance

instance [P.ContainsKernels] {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    PreservesLimit (Limits.parallelPair f 0) P.ι := by
  have : P.ContainsLimit (parallelPair f 0) := ContainsKernels.contains_kernel f
  infer_instance

class ContainsKernelsOfEpi where
    contains_kernel : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y) [Epi f],
    P.ContainsLimit (parallelPair f 0)

class ContainsCokernels where
    contains_cokernel : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y),
    P.ContainsColimit (parallelPair f 0)

instance [P.ContainsCokernels] : HasCokernels P.FullSubcategory where
  has_colimit f := by
    have : P.ContainsColimit (parallelPair f 0) := ContainsCokernels.contains_cokernel f
    infer_instance

instance [P.ContainsCokernels] {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    PreservesColimit (Limits.parallelPair f 0) P.ι := by
  have : P.ContainsColimit (parallelPair f 0) := ContainsCokernels.contains_cokernel f
  infer_instance

class ContainsCokernelsOfMono where
    contains_cokernel : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y) [Mono f],
    P.ContainsColimit (parallelPair f 0)

class ContainsFiniteProducts where
    contains_product : ∀ (n : ℕ) (c :Fin n → P.FullSubcategory),
    P.ContainsLimit (Discrete.functor c)

instance [P.ContainsFiniteProducts] : HasFiniteProducts P.FullSubcategory where
  out n := by refine HasLimitsOfShape.mk (fun c ↦ ?_)
              have := ContainsFiniteProducts.contains_product n (c.obj ∘ Discrete.mk)
              exact hasLimit_of_iso Discrete.natIsoFunctor.symm

instance [P.ContainsFiniteProducts] : PreservesFiniteProducts P.ι where
  preserves _ := {preservesLimit := inferInstance}

instance [P.ContainsZero] : HasZeroObject P.FullSubcategory where
  zero := by
    obtain ⟨X, h₁, h₂⟩ := P.exists_prop_of_containsZero
    use ⟨X, h₂⟩
    refine {unique_to Y := ?_, unique_from Y := ?_}
    · exact (unique_iff_subsingleton_and_nonempty _).mpr ⟨Subsingleton.intro
        (fun _ _ ↦ h₁.eq_of_src _ _), Nonempty.intro 0⟩
    · exact (unique_iff_subsingleton_and_nonempty _).mpr ⟨Subsingleton.intro
        (fun _ _ ↦ h₁.eq_of_tgt _ _), Nonempty.intro 0⟩

-- Left exactness of the forgetful functor.
instance [HasZeroObject C] [P.ContainsKernels] [P.ContainsFiniteProducts] :
    PreservesFiniteLimits P.ι := by
  have := HasFiniteBiproducts.of_hasFiniteProducts (C := P.FullSubcategory)
  have := hasBinaryBiproducts_of_finite_biproducts P.FullSubcategory
  have := Preadditive.hasEqualizers_of_hasKernels (C := P.FullSubcategory)
  exact P.ι.preservesFiniteLimits_of_preservesKernels

-- Right exactness of the forgetful functor.
instance [HasZeroObject C] [P.ContainsCokernels] [P.ContainsFiniteProducts] :
    PreservesFiniteColimits P.ι := by
  have := HasFiniteBiproducts.of_hasFiniteProducts (C := P.FullSubcategory)
  have := hasBinaryBiproducts_of_finite_biproducts P.FullSubcategory
  have := Preadditive.hasCoequalizers_of_hasCokernels (C := P.FullSubcategory)
  exact P.ι.preservesFiniteColimits_of_preservesCokernels

end KernelsCokernels

section Abelian

variable [Abelian C]

class IsAbelian : Prop extends P.ContainsZero, P.ContainsKernels, P.ContainsCokernels,
  P.ContainsFiniteProducts

instance [P.IsAbelian] : Abelian P.FullSubcategory := by
  have : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    have : IsIso (P.ι.map (Abelian.coimageImageComparison f)) := by
      rw [Arrow.isIso_iff_isIso_of_isIso (Abelian.PreservesCoimageImageComparison.iso P.ι f).hom]
      infer_instance
    exact isIso_of_fully_faithful P.ι _
  exact Abelian.ofCoimageImageComparisonIsIso

lemma IsAbelian_of_containsKernelsEpiAndCokernels [P.ContainsZero] [P.ContainsKernelsOfEpi]
    [P.ContainsCokernels] : P.ContainsKernels where
  contains_kernel {X Y} f := by
    refine {contains_limit := ?_}
    set g := cokernel.π f
    have := ContainsKernelsOfEpi.contains_kernel g
    set Z := kernel g
    set h : X ⟶ Z := kernel.lift g f (cokernel.condition f)
    have : Epi h := sorry
    have := ContainsKernelsOfEpi.contains_kernel h
    set d : Cone (parallelPair f 0) := by
      refine KernelFork.ofι (kernel.ι h) ?_
      dsimp
      rw [← kernel.lift_ι g f (cokernel.condition f), ← assoc, kernel.condition, zero_comp]
    refine ⟨d, Nonempty.intro ?_⟩
    have : Mono (P.ι.map (kernel.ι g)) := sorry
    have lim := isLimitOfPreserves P.ι (kernelIsKernel h)
    set c' := P.ι.mapCone (KernelFork.ofι (f := h) (kernel.ι h) (kernel.condition _))
    set c'' : KernelFork (P.ι.map h) := KernelFork.ofι (P.ι.map (kernel.ι h))
      (by rw [← P.ι.map_comp, kernel.condition, P.ι.map_zero])
    have hc'' : IsLimit c'' := sorry
    have hh : P.ι.map f = P.ι.map h ≫ P.ι.map (kernel.ι g) := by
      rw [← P.ι.map_comp, kernel.lift_ι]
    set d' : KernelFork (P.ι.map f) := KernelFork.ofι c''.ι
      (by dsimp [c'']; rw [← kernel.lift_ι g f (cokernel.condition f)]
          erw [← assoc, kernel.condition h]; rw [zero_comp])
    have hd' : IsLimit d' := isKernelCompMono hc'' (P.ι.map (kernel.ι g)) hh
    set e : P.ι.mapCone d ≅ d' := sorry

lemma IsAbelian_of_containsKernelsAndCokernelsMono [P.ContainsZero] [P.ContainsKernels]
    [P.ContainsCokernelsOfMono] : P.IsAbelian := sorry


end Abelian


end ObjectProperty
