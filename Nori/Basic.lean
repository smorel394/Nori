import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.Algebra.Category.Grp.Zero
import Nori.Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Nori.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Nori.Mathlib.CategoryTheory.Limits.Shapes.Biproducts

noncomputable section

universe u v

open CategoryTheory Category Limits Opposite ObjectProperty

open scoped ZeroObject

namespace Nori

variable (C : Type u) [Category.{v} C]

abbrev RightMod := Cᵒᵖ ⥤ AddCommGrp.{v}

--def IsFinitelyPresented : ObjectProperty (RightMod C) :=
--  fun X ↦ ∃ (A B : C) (u : A ⟶ B), Nonempty (cokernel ((preadditiveYoneda).map u) ≅ X)

def IsFinitelyPresented₂ : ObjectProperty (RightMod C) :=
  fun X ↦ ∃ (A B : RightMod C) (u : A ⟶ X) (_ : Epi u) (v : B ⟶ kernel u) (_ : Epi v),
  (A ⋙ forget AddCommGrp).IsRepresentable ∧ (B ⋙ forget AddCommGrp).IsRepresentable

--abbrev FinitelyPresented := (IsFinitelyPresented C).FullSubcategory

abbrev FinitelyPresented := (IsFinitelyPresented₂ C).FullSubcategory

/-
instance : (IsFinitelyPresented C).IsClosedUnderIsomorphisms where
  of_iso α h := by
    obtain ⟨A, B, u, h⟩ := h
    use A, B, u
    exact Nonempty.intro (Classical.choice h ≪≫ α)
-/

instance : (IsFinitelyPresented₂ C).IsClosedUnderIsomorphisms where
  of_iso α h := by
    obtain ⟨A, B, u, _, v, _, _, _⟩ := h
    use A, B, u ≫ α.hom, inferInstance,
      v ≫ (kernel.mapIso u (u ≫ α.hom) (Iso.refl _) α (by simp)).hom, inferInstance

section ZeroObject

variable [HasZeroObject C]

instance (X : Cᵒᵖ) : Unique (((0 : RightMod C) ⋙ forget AddCommGrp).obj X) := by
  have : Unique ((forget AddCommGrp).obj (AddCommGrp.of PUnit.{v + 1})) := by
    change Unique PUnit.{v+1}
    infer_instance
  exact Equiv.unique ((forget AddCommGrp).mapIso (IsZero.isoZero (Functor.zero_obj X))
    ≪≫ ((forget AddCommGrp).mapIso (IsZero.isoZero (AddCommGrp.isZero_of_subsingleton
      (AddCommGrp.of.{v} PUnit)))).symm).toEquiv

instance : ((0 : RightMod C) ⋙ forget AddCommGrp).IsRepresentable where
  has_representation := by
    use 0
    exact Nonempty.intro
      {homEquiv := Equiv.ofUnique _ _, homEquiv_comp _ _ := Subsingleton.elim _ _}

lemma IsFinitelyPresented₂_of_isRepresentable (X : RightMod C)
    (hX : (X ⋙ forget AddCommGrp).IsRepresentable) : IsFinitelyPresented₂ C X := by
  use X, 0, 𝟙 X, inferInstance, 0, IsZero.epi (IsZero.of_iso (isZero_zero _)
    (kernel.ofMono (𝟙 X))) _
  refine ⟨hX, inferInstance⟩

/-instance : (IsFinitelyPresented C).ContainsZero where
  exists_zero := by
    use 0
    refine ⟨isZero_zero _, ?_⟩
    use 0, 0, 0
    exact Nonempty.intro (cokernelIsoOfEq (preadditiveYoneda.map_zero 0 0) ≪≫
      cokernelZeroIsoTarget ≪≫ Functor.mapZeroObject preadditiveYoneda)
-/

instance : (IsFinitelyPresented₂ C).ContainsZero where
  exists_zero := by
    use 0
    refine ⟨isZero_zero _, IsFinitelyPresented₂_of_isRepresentable C _ inferInstance⟩

/-instance : HasZeroObject (FinitelyPresented C) where
  zero := by
    obtain ⟨Z, h₁, h₂⟩ := exists_prop_of_containsZero (IsFinitelyPresented C)
    use ⟨Z, h₂⟩
    refine {unique_to Y := ?_, unique_from Y := ?_}
    · exact (unique_iff_subsingleton_and_nonempty _).mpr ⟨Subsingleton.intro
        (fun _ _ ↦ h₁.eq_of_src _ _), Nonempty.intro 0⟩
    · exact (unique_iff_subsingleton_and_nonempty _).mpr ⟨Subsingleton.intro
        (fun _ _ ↦ h₁.eq_of_tgt _ _), Nonempty.intro 0⟩
-/

instance : HasZeroObject (FinitelyPresented C) where
  zero := by
    obtain ⟨Z, h₁, h₂⟩ := exists_prop_of_containsZero (IsFinitelyPresented₂ C)
    use ⟨Z, h₂⟩
    refine {unique_to Y := ?_, unique_from Y := ?_}
    · exact (unique_iff_subsingleton_and_nonempty _).mpr ⟨Subsingleton.intro
        (fun _ _ ↦ h₁.eq_of_src _ _), Nonempty.intro 0⟩
    · exact (unique_iff_subsingleton_and_nonempty _).mpr ⟨Subsingleton.intro
        (fun _ _ ↦ h₁.eq_of_tgt _ _), Nonempty.intro 0⟩

end ZeroObject

section FiniteProducts

variable {C}

variable [Preadditive C] [HasFiniteProducts C]

instance : HasFiniteBiproducts C where
  out _ := {has_biproduct _ := HasBiproduct.of_hasProduct _ }

instance : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C

lemma representableBy_zero {F : Cᵒᵖ ⥤ AddCommGrp.{v}} {Y : C}
    (r : (F ⋙ forget AddCommGrp).RepresentableBy Y) (X : C) :
    r.homEquiv (X := X) 0 = 0 := by
  let π : X ⟶ 0 := 0
  have eq : (0 : X ⟶ Y) = π ≫ 0 := comp_zero.symm
  have eq' : r.homEquiv (X := 0) 0 = 0 := by
    have : Subsingleton ((F ⋙ forget AddCommGrp).obj (op 0)) :=
      Equiv.subsingleton (r.homEquiv (X := 0)).symm
    exact Subsingleton.elim _ _
  rw [eq, r.homEquiv_comp π 0, eq']
  simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_zero]

lemma representableBy_sum {F : Cᵒᵖ ⥤ AddCommGrp.{v}} {Y : C}
    (r : (F ⋙ forget AddCommGrp).RepresentableBy Y) {X : C} (f g : X ⟶ Y) :
    r.homEquiv (f + g) = r.homEquiv f + r.homEquiv g := by
  have : ∀ (u v : F.obj (op (biprod X X))),
      (F ⋙ forget AddCommGrp).map biprod.inl.op u = (F ⋙ forget AddCommGrp).map biprod.inl.op v →
      (F ⋙ forget AddCommGrp).map biprod.inr.op u = (F ⋙ forget AddCommGrp).map biprod.inr.op v →
      u = v := by
    intro u v h₁ h₂
    apply r.homEquiv.symm.injective
    have eq : biprod.inl ≫ r.homEquiv.symm u = biprod.inl ≫ r.homEquiv.symm v := by
      rw [r.comp_homEquiv_symm, r.comp_homEquiv_symm]
      congr
    have eq' : biprod.inr ≫ r.homEquiv.symm u = biprod.inr ≫ r.homEquiv.symm v := by
      rw [r.comp_homEquiv_symm, r.comp_homEquiv_symm]
      congr
    rw [← id_comp (r.homEquiv.symm u), ← biprod.total, Preadditive.add_comp, assoc, assoc, eq,
      eq', ← assoc, ← assoc, ← Preadditive.add_comp, biprod.total, id_comp]
  have eq : f + g = biprod.lift (𝟙 _) (𝟙 _) ≫ biprod.desc f g := by simp
  have eq' : r.homEquiv (biprod.desc f g) = r.homEquiv (biprod.desc f 0)
      + r.homEquiv (biprod.desc 0 g) := by
    refine this _ _ ?_ ?_
    · rw [← r.homEquiv_comp biprod.inl]
      dsimp
      rw [biprod.inl_desc, map_add]
      change _ = (F ⋙ forget AddCommGrp).map biprod.inl.op _ +
        ((F ⋙ forget AddCommGrp).map) biprod.inl.op _
      conv_rhs => erw [← r.homEquiv_comp biprod.inl (biprod.desc f 0),
                    ← r.homEquiv_comp biprod.inl (biprod.desc 0 g)]
      rw [biprod.inl_desc, biprod.inl_desc, representableBy_zero, add_zero]
      rfl
    · rw [← r.homEquiv_comp biprod.inr]
      dsimp
      rw [biprod.inr_desc, map_add]
      change _ = (F ⋙ forget AddCommGrp).map biprod.inr.op _ +
        ((F ⋙ forget AddCommGrp).map) biprod.inr.op _
      conv_rhs => erw [← r.homEquiv_comp biprod.inr (biprod.desc f 0),
                    ← r.homEquiv_comp biprod.inr (biprod.desc 0 g)]
      rw [biprod.inr_desc, biprod.inr_desc, representableBy_zero, zero_add]
      rfl
  rw [eq, r.homEquiv_comp, eq']
  simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_add]
  change (F ⋙ forget AddCommGrp).map _ _ + ((F ⋙ forget AddCommGrp).map) _ _ = _
  erw [← r.homEquiv_comp, ← r.homEquiv_comp, biprod.lift_desc, biprod.lift_desc, id_comp,
    comp_zero, add_zero, id_comp, zero_add]
  rfl

def Functor.representableByEquivAdd {F : Cᵒᵖ ⥤ AddCommGrp.{v}} {Y : C} :
    (F ⋙ forget AddCommGrp).RepresentableBy Y ≃ (preadditiveYoneda.obj Y ≅ F) where
  toFun r := by
    refine NatIso.ofComponents (fun X ↦ AddEquiv.toAddCommGrpIso ?_) (fun f ↦ ?_)
    · dsimp
      refine {r.homEquiv (X := unop X) with map_add' := representableBy_sum r}
    · ext a
      exact r.homEquiv_comp f.unop a
  invFun e := Functor.representableByEquiv.invFun (isoWhiskerRight e (forget AddCommGrp))
  left_inv r := rfl
  right_inv e := rfl

instance (n : ℕ) (c : Fin n → RightMod C) [∀ i, (c i ⋙ forget AddCommGrp).IsRepresentable] :
    (biproduct c ⋙ forget AddCommGrp).IsRepresentable where
  has_representation := ⟨biproduct (fun i ↦ (c i ⋙ forget AddCommGrp).reprX),
     Nonempty.intro (Functor.representableByEquivAdd.invFun (biproduct.uniqueUpToIso _
     (isBilimitOfPreserves (preadditiveYoneda (C := C)) (biproduct.isBilimit _)) ≪≫
     biproduct.mapIso (fun i ↦ Functor.representableByEquivAdd.toFun
    (c i ⋙ forget AddCommGrp).representableBy)))⟩

def biproduct.KernelOfMap (n : ℕ) (A : Fin n → RightMod C) (B : Fin n → RightMod C) (u : (i : Fin n) → (A i ⟶ B i)) :
    IsLimit (KernelFork.ofι (f := biproduct.map u) (biproduct.map (fun i ↦ kernel.ι (u i)))
    (by rw [← biproduct.map_comp]; simp only [Functor.comp_obj, Functor.flip_obj_obj, kernel.condition]; exact biproduct.map_zero)) where
  lift s := by
    refine biproduct.lift (fun i ↦ kernel.lift (u i) (s.π.app WalkingParallelPair.zero ≫ biproduct.π A i) ?_)
    have := biproduct.hom_ext_iff.mp (KernelFork.condition s) i
    dsimp at this
    rw [assoc, biproduct.map_π, ← assoc, zero_comp] at this
    exact this
  fac s j := by
    match j with
    | WalkingParallelPair.zero =>
      dsimp
      simp only [biproduct.lift_map, kernel.lift_ι]
      refine biproduct.hom_ext _ _ (fun j ↦ ?_)
      simp only [biproduct.lift_π]
    | WalkingParallelPair.one =>
      dsimp
      simp only [biproduct.lift_map_assoc, kernel.lift_ι, biproduct.lift_map, assoc,
        Fork.app_one_eq_ι_comp_left, Functor.const_obj_obj, parallelPair_obj_zero,
        KernelFork.condition]
      refine biproduct.hom_ext _ _ (fun j ↦ ?_)
      simp only [biproduct.lift_π, zero_comp]
      have := biproduct.hom_ext_iff.mp (KernelFork.condition s) j
      dsimp at this
      rw [assoc, biproduct.map_π, ← assoc, zero_comp] at this
      exact this
  uniq s m eq := by
    refine biproduct.hom_ext _ _ (fun j ↦ ?_)
    rw [← cancel_mono (kernel.ι (u j))]
    dsimp
    simp only [assoc, biproduct.lift_π, kernel.lift_ι]
    have := (biproduct.hom_ext_iff.mp (eq WalkingParallelPair.zero)) j
    dsimp at this
    simp only [assoc, biproduct.map_π] at this
    exact this

def biproduct.map_kernel (n : ℕ) (A : Fin n → RightMod C) (B : Fin n → RightMod C) (u : (i : Fin n) → (A i ⟶ B i)) :
    biproduct (fun i ↦ kernel (u i)) ≅ kernel (biproduct.map u) := by
  set e := IsLimit.conePointUniqueUpToIso (biproduct.KernelOfMap n A B u) (kernelIsKernel (biproduct.map u))
  exact e

lemma IsFinitelyPresented_isClosedUnderFiniteBiproduct (n : ℕ) (c : Fin n → RightMod C)
    (hc : ∀ (i : Fin n), IsFinitelyPresented₂ C (c i)) : IsFinitelyPresented₂ C (biproduct c) := by
  choose A B u hu v hv Arep Brep using hc
  have : (biproduct A ⋙ forget AddCommGrp).IsRepresentable := inferInstance
  have : (biproduct B ⋙ forget AddCommGrp).IsRepresentable := inferInstance
  use biproduct A, biproduct B, biproduct.map u, biproduct.map_epi u
  have := biproduct.map_epi v
  use biproduct.map v ≫ (biproduct.map_kernel n _ _ u).hom, inferInstance

instance : HasFiniteBiproducts (FinitelyPresented C) where
  out n :=
    {has_biproduct c := by
      refine HasBiproduct.mk {bicone := ?_, isBilimit := {isLimit := ?_, isColimit := ?_}}
      · exact {pt := ⟨biproduct (fun i ↦ (c i).1),
                 IsFinitelyPresented_isClosedUnderFiniteBiproduct n (fun i ↦ (c i).1) (fun i ↦ (c i).2)⟩,
               π := biproduct.π (fun i ↦ (c i).1),
               ι := biproduct.ι (fun i ↦ (c i).1),
               ι_π j j' := by erw [biproduct.ι_π (fun i ↦ (c i).1) j j']
                              by_cases eq : j = j'
                              · simp only [eq, ↓reduceDIte]; rfl
                              · simp only [eq, ↓reduceDIte]}
      · refine {lift s := ?_, fac s := ?_, uniq s := ?_}
        · exact (biproduct.isLimit (fun i ↦ (c i).1)).lift ((IsFinitelyPresented₂ C).ι.mapCone s)
        · exact (biproduct.isLimit (fun i ↦ (c i).1)).fac ((IsFinitelyPresented₂ C).ι.mapCone s)
        · exact (biproduct.isLimit (fun i ↦ (c i).1)).uniq ((IsFinitelyPresented₂ C).ι.mapCone s)
      · refine {desc s := ?_, fac s := ?_, uniq s := ?_}
        · exact (biproduct.isColimit (fun i ↦ (c i).1)).desc ((IsFinitelyPresented₂ C).ι.mapCocone s)
        · exact (biproduct.isColimit (fun i ↦ (c i).1)).fac ((IsFinitelyPresented₂ C).ι.mapCocone s)
        · exact (biproduct.isColimit (fun i ↦ (c i).1)).uniq ((IsFinitelyPresented₂ C).ι.mapCocone s)
    }

instance : HasBinaryBiproducts (FinitelyPresented C) := hasBinaryBiproducts_of_finite_biproducts _

end FiniteProducts

end Nori
