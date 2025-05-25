import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.ObjectProperty.EpiMono
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import Nori.Mathlib.CategoryTheory.Limits.Shapes.Equalizers

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

lemma ContainsKernels_of_containsKernelsEpiAndCokernels [P.ContainsZero] [P.ContainsKernelsOfEpi]
    [P.ContainsCokernels] : P.ContainsKernels where
  contains_kernel {X Y} f := by
    refine {contains_limit := ?_}
    have := ContainsKernelsOfEpi.contains_kernel (cokernel.π f)
    have hg : Epi (Abelian.factorThruImage f) := by
      refine P.ι.epi_of_epi_map ?_
      rw [← Abelian.PreservesImage.factorThruImage_iso_inv P.ι f]
      infer_instance
    have hι : Mono (P.ι.map (Abelian.image.ι f)) := by
      rw [← kernelComparison_comp_ι (cokernel.π f) P.ι]
      infer_instance
    have := ContainsKernelsOfEpi.contains_kernel (Abelian.factorThruImage f)
    have h₁ : kernel.ι (Abelian.factorThruImage f) ≫ f = 0 := by
      simp_rw [← Abelian.image.fac f]; rw [← assoc, kernel.condition, zero_comp]
    refine ⟨KernelFork.ofι (kernel.ι (Abelian.factorThruImage f)) h₁, Nonempty.intro
      {lift := fun s ↦ ?_, fac := fun s j ↦ ?_, uniq := fun s m hm ↦ ?_}⟩
    · have eq : s.π.app WalkingParallelPair.zero ≫ P.ι.map (Abelian.factorThruImage f) = 0 := by
        have h := s.w WalkingParallelPairHom.left
        have h' := s.w WalkingParallelPairHom.right
        dsimp at h h'
        rw [← h', comp_zero] at h
        rw [← cancel_mono (P.ι.map (Abelian.image.ι f)), zero_comp, assoc, ← P.ι.map_comp,
          Abelian.image.fac f]
        exact h
      exact kernel.lift (P.ι.map (Abelian.factorThruImage f)) (s.π.app WalkingParallelPair.zero)
        eq ≫ (PreservesKernel.iso P.ι (Abelian.factorThruImage f)).inv
    · match j with
      | WalkingParallelPair.zero =>
        dsimp
        change _ ≫ P.ι.map (kernel.ι (Abelian.factorThruImage f)) = _
        rw [assoc, PreservesKernel.iso_inv_ι]
        simp
      | WalkingParallelPair.one =>
        dsimp
        change _ ≫ P.ι.map (kernel.ι (Abelian.factorThruImage f)) ≫ f = _
        rw [assoc, ← assoc _ (P.ι.map (kernel.ι (Abelian.factorThruImage f))) f,
          PreservesKernel.iso_inv_ι]
        simp only [ι_obj, ι_map, kernel.lift_ι_assoc]
        have h := s.w WalkingParallelPairHom.left
        have h' := s.w WalkingParallelPairHom.right
        dsimp at h h'
        rw [← h', comp_zero] at h
        rw [h, ← h', comp_zero]
    · dsimp
      rw [← cancel_mono (PreservesKernel.iso P.ι (Abelian.factorThruImage f)).hom, assoc,
        Iso.inv_hom_id, comp_id, ← cancel_mono (kernel.ι (P.ι.map (Abelian.factorThruImage f))),
        PreservesKernel.iso_hom, assoc, kernelComparison_comp_ι]
      simp only [ι_obj, ι_map, kernel.lift_ι]
      exact hm WalkingParallelPair.zero

lemma ContainsCokernels_of_containsKernelsAndCokernelsMono [P.ContainsZero] [P.ContainsKernels]
    [P.ContainsCokernelsOfMono] : P.ContainsCokernels where
  contains_cokernel {X Y} f := by
    refine {contains_colimit := ?_}
    have := ContainsCokernelsOfMono.contains_cokernel (kernel.ι f)
    have hg : Mono (Abelian.factorThruCoimage f) := by
      refine P.ι.mono_of_mono_map ?_
      rw [← Abelian.PreservesCoimage.factorThruCoimage_iso_hom P.ι f]
      infer_instance
    have hι : Epi (P.ι.map (Abelian.coimage.π f)) := by
      rw [← π_comp_cokernelComparison (kernel.ι f) P.ι]
      infer_instance
    have := ContainsCokernelsOfMono.contains_cokernel (Abelian.factorThruCoimage f)
    have h₁ : f ≫ cokernel.π (Abelian.factorThruCoimage f) = 0 := by
      simp_rw [← Abelian.coimage.fac f]; rw [assoc, cokernel.condition, comp_zero]
    refine ⟨CokernelCofork.ofπ (cokernel.π (Abelian.factorThruCoimage f)) h₁, Nonempty.intro
      {desc := fun s ↦ ?_, fac := fun s j ↦ ?_, uniq := fun s m hm ↦ ?_}⟩
    · have eq : P.ι.map (Abelian.factorThruCoimage f) ≫ s.ι.app WalkingParallelPair.one = 0 := by
        have h := s.w WalkingParallelPairHom.left
        have h' := s.w WalkingParallelPairHom.right
        dsimp at h h'
        rw [← h', zero_comp] at h
        rw [← cancel_epi (P.ι.map (Abelian.coimage.π f)), comp_zero, ← assoc, ← P.ι.map_comp,
          Abelian.coimage.fac f]
        exact h
      exact (PreservesCokernel.iso P.ι (Abelian.factorThruCoimage f)).hom ≫ cokernel.desc
        (P.ι.map (Abelian.factorThruCoimage f)) (s.ι.app WalkingParallelPair.one) eq
    · match j with
      | WalkingParallelPair.zero =>
        dsimp
        change (_ ≫ P.ι.map (cokernel.π (Abelian.factorThruCoimage f))) ≫ _ = _
        rw [assoc, ← assoc (P.ι.map (cokernel.π (Abelian.factorThruCoimage f))),
          PreservesCokernel.π_iso_hom]
        simp only [ι_obj, ι_map, cokernel.π_desc]
        have h := s.w WalkingParallelPairHom.left
        have h' := s.w WalkingParallelPairHom.right
        dsimp at h h'
        rw [← h', zero_comp] at h
        rw [h, ← h', zero_comp]
      | WalkingParallelPair.one =>
        dsimp
        change P.ι.map (cokernel.π (Abelian.factorThruCoimage f)) ≫ _ = _
        rw [← assoc, PreservesCokernel.π_iso_hom]
        simp
    · dsimp
      rw [← cancel_epi (PreservesCokernel.iso P.ι (Abelian.factorThruCoimage f)).inv, ← assoc,
        Iso.inv_hom_id, id_comp, ← cancel_epi (cokernel.π (P.ι.map (Abelian.factorThruCoimage f))),
        PreservesCokernel.iso_inv, ← assoc, π_comp_cokernelComparison]
      simp only [ι_obj, ι_map, cokernel.π_desc]
      exact hm WalkingParallelPair.one

lemma IsAbelian_ofKernelsOfEpi [P.ContainsZero] [P.ContainsKernelsOfEpi]
    [P.ContainsCokernels] [P.ContainsFiniteProducts] : P.IsAbelian where
  contains_kernel := P.ContainsKernels_of_containsKernelsEpiAndCokernels.contains_kernel

lemma IsAbelian_ofCokernelsOfMono [P.ContainsZero] [P.ContainsKernels]
    [P.ContainsCokernelsOfMono] [P.ContainsFiniteProducts] : P.IsAbelian where
  contains_cokernel := P.ContainsCokernels_of_containsKernelsAndCokernelsMono.contains_cokernel

end Abelian


end ObjectProperty
