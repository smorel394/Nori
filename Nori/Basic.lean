import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.Algebra.Category.Grp.Zero
import Nori.Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Nori.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Nori.Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Nori.Mathlib.CategoryTheory.Abelian.Subcategory
import Nori.AbelianLemmas

noncomputable section

universe u v w

open CategoryTheory Category Limits Opposite ObjectProperty

open scoped ZeroObject

namespace Nori

variable (C : Type u) [Category.{v} C]

def IsFinitelyPresented : ObjectProperty (Cᵒᵖ ⥤ AddCommGrp.{v}) :=
  fun X ↦ ∃ (A B : Cᵒᵖ ⥤ AddCommGrp.{v}) (u : A ⟶ X) (_ : Epi u) (v : B ⟶ kernel u) (_ : Epi v),
  (A ⋙ forget AddCommGrp).IsRepresentable ∧ (B ⋙ forget AddCommGrp).IsRepresentable

abbrev FinitelyPresented := (IsFinitelyPresented C).FullSubcategory

variable {C}

lemma isFinitelyPresented_iff_shortComplex (X : Cᵒᵖ ⥤ AddCommGrp.{v}) :
    IsFinitelyPresented C X ↔ ∃ (A B : Cᵒᵖ ⥤ AddCommGrp.{v}) (f : A ⟶ B)
    (g : B ⟶ X) (_ : Epi g) (zero : f ≫ g = 0), (A ⋙ forget AddCommGrp).IsRepresentable ∧
    (B ⋙ forget AddCommGrp).IsRepresentable ∧ (ShortComplex.mk f g zero).Exact := by
  refine ⟨fun ⟨A, B, u, hu, v, hv, hA, hB⟩ ↦ ?_, fun ⟨A, B, f, g, hg, zero, hA, hB, h⟩ ↦ ?_⟩
  · use B, A, v ≫ kernel.ι u, u, hu
    simp only [Functor.comp_obj, Functor.flip_obj_obj, assoc, kernel.condition, comp_zero,
      exists_and_left, exists_true_left]
    refine ⟨hB, hA, ?_⟩
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    dsimp
    have eq : kernel.lift u (v ≫ kernel.ι u) (by simp) = v := by
      rw [← cancel_mono (kernel.ι u)]
      simp
    rw [eq]
    exact hv
  · use B, A, g, hg, kernel.lift g f zero
    simp only [Functor.comp_obj, Functor.flip_obj_obj, exists_and_left, exists_prop]
    refine ⟨hB, ?_, hA⟩
    rw [ShortComplex.exact_iff_epi_kernel_lift] at h
    exact h

instance : (IsFinitelyPresented C).IsClosedUnderIsomorphisms where
  of_iso α h := by
    obtain ⟨A, B, u, _, v, _, _, _⟩ := h
    use A, B, u ≫ α.hom, inferInstance,
      v ≫ (kernel.mapIso u (u ≫ α.hom) (Iso.refl _) α (by simp)).hom, inferInstance

section ZeroObject

variable [HasZeroObject C]

instance (X : Cᵒᵖ) : Unique (((0 : Cᵒᵖ ⥤ AddCommGrp.{w}) ⋙ forget AddCommGrp).obj X) := by
  have : Unique ((forget AddCommGrp).obj (AddCommGrp.of PUnit.{w + 1})) := by
    change Unique PUnit.{w + 1}
    infer_instance
  exact Equiv.unique ((forget AddCommGrp).mapIso (IsZero.isoZero (Functor.zero_obj X))
    ≪≫ ((forget AddCommGrp).mapIso (IsZero.isoZero (AddCommGrp.isZero_of_subsingleton
      (AddCommGrp.of.{w} PUnit)))).symm).toEquiv

instance : ((0 : Cᵒᵖ ⥤ AddCommGrp.{v}) ⋙ forget AddCommGrp).IsRepresentable where
  has_representation := by
    use 0
    exact Nonempty.intro
      {homEquiv := Equiv.ofUnique _ _, homEquiv_comp _ _ := Subsingleton.elim _ _}

lemma IsFinitelyPresented_of_isRepresentable (X : Cᵒᵖ ⥤ AddCommGrp)
    (hX : (X ⋙ forget AddCommGrp).IsRepresentable) : IsFinitelyPresented C X := by
  use X, 0, 𝟙 X, inferInstance, 0, IsZero.epi (IsZero.of_iso (isZero_zero _)
    (kernel.ofMono (𝟙 X))) _
  refine ⟨hX, inferInstance⟩

instance : (IsFinitelyPresented C).ContainsZero where
  exists_zero :=
    ⟨0, ⟨isZero_zero _, IsFinitelyPresented_of_isRepresentable _ inferInstance⟩⟩

end ZeroObject

section Additive

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

lemma Functor.representableByEquivAdd_forget {F : Cᵒᵖ ⥤ AddCommGrp.{v}} {Y : C}
    (r : (F ⋙ forget AddCommGrp).RepresentableBy Y) :
    isoWhiskerRight (Functor.representableByEquivAdd.toFun r) (forget AddCommGrp) =
    Functor.representableByEquiv.toFun r := by aesop

lemma IsRepresentable_proj (A B X : Cᵒᵖ ⥤ AddCommGrp.{v}) [(A ⋙ forget AddCommGrp).IsRepresentable]
    [(B ⋙ forget AddCommGrp).IsRepresentable] (f : A ⟶ X) (g : B ⟶ X) [Epi g] :
    ∃ (h : A ⟶ B), f = h ≫ g := by
  set eA := Functor.representableByEquiv.toFun (A ⋙ forget AddCommGrp).representableBy
  set eB := Functor.representableByEquiv.toFun (B ⋙ forget AddCommGrp).representableBy
  set fA := Functor.representableByEquivAdd.toFun (A ⋙ forget AddCommGrp).representableBy
  set fB := Functor.representableByEquivAdd.toFun (B ⋙ forget AddCommGrp).representableBy
  have : Epi (g.app ((op (A ⋙ forget AddCommGrp).reprX))) := inferInstance
  rw [AddCommGrp.epi_iff_surjective] at this
  obtain ⟨x, hx⟩ := this (yonedaEquiv (eA.hom ≫ whiskerRight f (forget AddCommGrp)))
  set h' : A ⋙ forget AddCommGrp ⟶ B ⋙ forget AddCommGrp := eA.inv ≫ yonedaEquiv.invFun x
  have eq : h' ≫  whiskerRight g (forget AddCommGrp) = whiskerRight f (forget AddCommGrp) := by
    dsimp [h']
    rw [← cancel_epi eA.hom, ← assoc, ← assoc, Iso.hom_inv_id, id_comp]
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp]; erw [Equiv.apply_symm_apply]
    simp only [Functor.comp_obj, whiskerRight_app, ConcreteCategory.forget_map_eq_coe, h']
    rw [hx]
    rfl
  set h := fA.inv ≫ preadditiveYoneda.map ((eB.symm.app
    (op (A ⋙ forget AddCommGrp).reprX)).toEquiv x) ≫ fB.hom
  have eqA : eA = isoWhiskerRight fA (forget AddCommGrp) :=
    (Functor.representableByEquivAdd_forget _).symm
  have eqB : eB = isoWhiskerRight fB (forget AddCommGrp) :=
    (Functor.representableByEquivAdd_forget _).symm
  have eq' : whiskerRight h (forget AddCommGrp) = h' := by
    have eqx : (yonedaEquiv (F := B ⋙ forget AddCommGrp)).symm x =
        yoneda.map ((eB.symm.app (op (A ⋙ forget AddCommGrp).reprX)).toEquiv x) ≫ eB.hom := by
      ext
      dsimp [eB]
      erw [yonedaEquiv_symm_app_apply]
      simp [Functor.representableByEquiv]
      erw [(B ⋙ forget AddCommGrp).representableBy.homEquiv_comp, Equiv.apply_symm_apply]
      rfl
    dsimp [h', h]
    conv_rhs => erw [eqx]
    rw [eqA, eqB]
    rfl
  use h
  ext1; ext1 Y
  apply (forget AddCommGrp).map_injective
  rw [NatTrans.comp_app, (forget AddCommGrp).map_comp, ← whiskerRight_app h, eq',
    ← whiskerRight_app g, ← NatTrans.comp_app, eq, whiskerRight_app]

end Additive

section FiniteProducts

variable [Preadditive C] [HasFiniteProducts C]

instance (n : ℕ) (c : Fin n → (Cᵒᵖ ⥤ AddCommGrp.{v}))
    [∀ i, (c i ⋙ forget AddCommGrp).IsRepresentable] :
    (biproduct c ⋙ forget AddCommGrp).IsRepresentable where
  has_representation := ⟨biproduct (fun i ↦ (c i ⋙ forget AddCommGrp).reprX),
     Nonempty.intro (Functor.representableByEquivAdd.invFun (biproduct.uniqueUpToIso _
     (isBilimitOfPreserves (preadditiveYoneda (C := C)) (biproduct.isBilimit _)) ≪≫
     biproduct.mapIso (fun i ↦ Functor.representableByEquivAdd.toFun
    (c i ⋙ forget AddCommGrp).representableBy)))⟩

lemma IsRepresentable_isClosedUnderBinaryBiproduct (A B : Cᵒᵖ ⥤ AddCommGrp.{v})
    (hc : (A ⋙ forget AddCommGrp).IsRepresentable) (hB : (B ⋙ forget AddCommGrp).IsRepresentable) :
    (biprod A B ⋙ forget AddCommGrp).IsRepresentable where
  has_representation :=
    have := preservesBinaryBiproduct_of_preservesBiproduct (preadditiveYoneda (C := C))
    ⟨biprod (A ⋙ forget AddCommGrp).reprX (B ⋙ forget AddCommGrp).reprX, Nonempty.intro
    ((Functor.representableByEquivAdd.invFun (biprod.uniqueUpToIso _ _ (isBinaryBilimitOfPreserves
    (preadditiveYoneda (C := C)) ((BinaryBiproduct.isBilimit (A ⋙ forget AddCommGrp).reprX
    (B ⋙ forget AddCommGrp).reprX))) ≪≫ biprod.mapIso (Functor.representableByEquivAdd.toFun
    (A ⋙ forget AddCommGrp).representableBy) (Functor.representableByEquivAdd.toFun
    (B ⋙ forget AddCommGrp).representableBy))))⟩

def biproduct.KernelOfMap (n : ℕ) (A : Fin n → ((Cᵒᵖ ⥤ AddCommGrp.{v})))
    (B : Fin n → ((Cᵒᵖ ⥤ AddCommGrp.{v}))) (u : (i : Fin n) → (A i ⟶ B i)) :
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

def biproduct.map_kernel (n : ℕ) (A : Fin n → ((Cᵒᵖ ⥤ AddCommGrp.{v})))
    (B : Fin n → ((Cᵒᵖ ⥤ AddCommGrp.{v}))) (u : (i : Fin n) → (A i ⟶ B i)) :
    biproduct (fun i ↦ kernel (u i)) ≅ kernel (biproduct.map u) := by
  set e := IsLimit.conePointUniqueUpToIso (biproduct.KernelOfMap n A B u) (kernelIsKernel (biproduct.map u))
  exact e

lemma IsFinitelyPresented_isClosedUnderFiniteBiproduct (n : ℕ) (c : Fin n → ((Cᵒᵖ ⥤ AddCommGrp.{v})))
    (hc : ∀ (i : Fin n), IsFinitelyPresented C (c i)) : IsFinitelyPresented C (biproduct c) := by
  choose A B u hu v hv Arep Brep using hc
  have : (biproduct A ⋙ forget AddCommGrp).IsRepresentable := inferInstance
  have : (biproduct B ⋙ forget AddCommGrp).IsRepresentable := inferInstance
  use biproduct A, biproduct B, biproduct.map u, biproduct.map_epi u
  have := biproduct.map_epi v
  use biproduct.map v ≫ (biproduct.map_kernel n _ _ u).hom, inferInstance

instance : (IsFinitelyPresented C).ContainsFiniteProducts where
  contains_product n c := by
    refine {contains_limit := ?_}
    set A := biproduct (fun (i : Fin n) ↦ (c i).1)
    have hA : IsFinitelyPresented C A := by
      exact IsFinitelyPresented_isClosedUnderFiniteBiproduct n (fun (i : Fin n) ↦ (c i).1)
       (fun i ↦ (c i).2)
    set d : Fan c := Fan.mk (⟨A, hA⟩ : FinitelyPresented C)
      (fun i ↦ biproduct.π (fun (i : Fin n) ↦ (c i).1) i)
    refine ⟨d, Nonempty.intro {lift s := ?_, fac s i := ?_, uniq s m hm := ?_}⟩
    · exact biproduct.lift (fun i ↦ s.π.app {as := i})
    · dsimp [d]
      simp
    · refine biproduct.hom_ext _ _ (fun i ↦ ?_)
      simp only [biproduct.lift_π, A, d]
      rw [← hm {as := i}]
      rfl

instance : HasBinaryBiproducts (FinitelyPresented C) := hasBinaryBiproducts_of_finite_biproducts _

end FiniteProducts

section Cokernels

variable [Preadditive C] [HasFiniteProducts C]

instance : (IsFinitelyPresented C).ContainsCokernels where
  contains_cokernel {K K'} u := by
    refine {contains_colimit := ?_}
    obtain ⟨A, B, f, g, _, zero, hA, hB, exact⟩ :=
      (isFinitelyPresented_iff_shortComplex K.1).mp K.2
    obtain ⟨A', B', f', g', _, zero', hA', hB', exact'⟩ :=
      (isFinitelyPresented_iff_shortComplex K'.1).mp K'.2
    obtain ⟨v, comm⟩ := IsRepresentable_proj B B' K'.1 (g ≫ u) g'
    set L : Cᵒᵖ ⥤ AddCommGrp := cokernel u
    have hL : IsFinitelyPresented C L := by
      rw [isFinitelyPresented_iff_shortComplex]
      set S := coker_sequence g (ShortComplex.mk f' g' zero') v u comm
      use S.X₁, S.X₂, S.f, S.g, inferInstance, S.zero
      refine ⟨?_, hB', coker_sequence_exact g _ exact' inferInstance v u comm ⟩
      exact IsRepresentable_isClosedUnderBinaryBiproduct B A' hB hA'
    refine ⟨CokernelCofork.ofπ (f := u) (Z := ⟨L, hL⟩) (cokernel.π u (C := Cᵒᵖ ⥤ AddCommGrp))
      (cokernel.condition u (C := Cᵒᵖ ⥤ AddCommGrp)),
      Nonempty.intro {desc s := ?_, fac s j := ?_, uniq s m hm := ?_}⟩
    · refine cokernel.desc u (s.ι.app WalkingParallelPair.one) ?_ (C := Cᵒᵖ ⥤ AddCommGrp)
      erw [s.ι.naturality WalkingParallelPairHom.left]
      dsimp
      have := s.ι.naturality WalkingParallelPairHom.right
      dsimp at this
      rw [← this]
      simp
    · match j with
      | WalkingParallelPair.zero =>
        dsimp
        erw [cokernel.condition u (C := Cᵒᵖ ⥤ AddCommGrp)]
        have := s.ι.naturality WalkingParallelPairHom.right
        dsimp at this
        simp only [zero_comp, comp_id] at this
        rw [zero_comp, this]
      | WalkingParallelPair.one =>
        dsimp
        simp
    · rw [← cancel_epi (cokernel.π u (C := Cᵒᵖ ⥤ AddCommGrp))]
      simp only [coequalizer_as_cokernel, cokernel.π_desc]
      exact hm WalkingParallelPair.one

end Cokernels

end Nori
