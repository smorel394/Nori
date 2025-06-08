import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Nori.Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Nori.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Nori.Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Nori.Mathlib.CategoryTheory.Abelian.Subcategory
import Nori.AbelianLemmas

noncomputable section

universe u v w u' v'

open CategoryTheory Category Limits Opposite ObjectProperty

open scoped ZeroObject

namespace Nori

variable (C : Type u) [Category.{v} C]

def IsFinitelyPresented : ObjectProperty (Cᵒᵖ ⥤ AddCommGrp.{v}) :=
  fun X ↦ ∃ (A B : Cᵒᵖ ⥤ AddCommGrp.{v}) (u : A ⟶ X) (_ : Epi u) (v : B ⟶ kernel u) (_ : Epi v),
  (A ⋙ forget AddCommGrp).IsRepresentable ∧ (B ⋙ forget AddCommGrp).IsRepresentable

abbrev FinitelyPresented := (IsFinitelyPresented C).FullSubcategory

variable {C}

lemma isFinitelyPresented_iff_shortComplex_representable (X : Cᵒᵖ ⥤ AddCommGrp.{v}) :
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
    [(X ⋙ forget AddCommGrp).IsRepresentable] : IsFinitelyPresented C X := by
  use X, 0, 𝟙 X, inferInstance, 0, IsZero.epi (IsZero.of_iso (isZero_zero _)
    (kernel.ofMono (𝟙 X))) _
  refine ⟨inferInstance, inferInstance⟩

instance : (IsFinitelyPresented C).ContainsZero where
  exists_zero :=
    ⟨0, ⟨isZero_zero _, IsFinitelyPresented_of_isRepresentable _⟩⟩

end ZeroObject

section Additive

variable [Preadditive C] [HasFiniteProducts C]

instance {X : C} : (preadditiveYoneda.obj X ⋙ forget AddCommGrp).IsRepresentable :=
  Functor.instIsRepresentableObjOppositeTypeYoneda

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

section Presentation

def IsFinitelyPresented.presentation_A {X : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X) :
    C := by
  have h := (isFinitelyPresented_iff_shortComplex_representable X).mp hX
  have := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
  exact (h.choose ⋙ forget AddCommGrp).reprX

def IsFinitelyPresented.presentation_B {X : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X) :
    C := by
  have h := (isFinitelyPresented_iff_shortComplex_representable X).mp hX
  have := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1
  exact (h.choose_spec.choose ⋙ forget AddCommGrp).reprX

def IsFinitelyPresented.presentation_map_f {X : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X) :
    hX.presentation_A ⟶ hX.presentation_B := by
  have h := (isFinitelyPresented_iff_shortComplex_representable X).mp hX
  have := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
  have := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1
  set f := h.choose_spec.choose_spec.choose
  set fA := Functor.representableByEquivAdd (h.choose ⋙ forget AddCommGrp).representableBy
  set fB := Functor.representableByEquivAdd (h.choose_spec.choose ⋙
    forget AddCommGrp).representableBy
  exact preadditiveYoneda.preimage (fA.hom ≫ f ≫ fB.inv)

def IsFinitelyPresented.presentation_map_p {X : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X) :
    preadditiveYoneda.obj hX.presentation_B ⟶ X := by
  have h := (isFinitelyPresented_iff_shortComplex_representable X).mp hX
  have := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1
  exact (Functor.representableByEquivAdd (h.choose_spec.choose ⋙
    forget AddCommGrp).representableBy).hom ≫ h.choose_spec.choose_spec.choose_spec.choose

lemma IsFinitelyPresented.presentation_map_f_p {X : Cᵒᵖ ⥤ AddCommGrp}
    (hX : IsFinitelyPresented C X) :
    preadditiveYoneda.map hX.presentation_map_f ≫ hX.presentation_map_p = 0 := by
  have h := (isFinitelyPresented_iff_shortComplex_representable X).mp hX
  dsimp [IsFinitelyPresented.presentation_map_f, IsFinitelyPresented.presentation_map_p]
  rw [Functor.map_preimage]
  simp only [assoc, Iso.inv_hom_id_assoc, Preadditive.IsIso.comp_left_eq_zero]
  exact h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

def IsFinitelyPresented.presentation_cokernel {X : Cᵒᵖ ⥤ AddCommGrp.{v}}
    (hX : IsFinitelyPresented C X) :
    IsColimit (CokernelCofork.ofπ hX.presentation_map_p hX.presentation_map_f_p) := by
  have h := (isFinitelyPresented_iff_shortComplex_representable X).mp hX
  have := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
  have := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1
  have : Epi h.choose_spec.choose_spec.choose_spec.choose :=
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose
  set fA := Functor.representableByEquivAdd (h.choose ⋙ forget AddCommGrp).representableBy
  set fB := Functor.representableByEquivAdd (h.choose_spec.choose ⋙
    forget AddCommGrp).representableBy
  have := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.gIsCokernel
  refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).toFun this
  · refine NatIso.ofComponents ?_ ?_
    · intro x
      match x with
      | WalkingParallelPair.zero => exact fA.symm
      | WalkingParallelPair.one => exact fB.symm
    · intro _ _ u
      match u with
      | WalkingParallelPairHom.id _ => simp
      | WalkingParallelPairHom.left =>
        dsimp [IsFinitelyPresented.presentation_map_f]
        rw [preadditiveYoneda.map_preimage]
        change _ = fA.inv ≫ fA.hom ≫ _
        rw [Iso.inv_hom_id_assoc]
        rfl
      | WalkingParallelPairHom.right =>
        dsimp
        simp
  · refine Cocones.ext (Iso.refl _) ?_
    intro x
    match x with
    | WalkingParallelPair.zero =>
      dsimp
      rw [hX.presentation_map_f_p, comp_id,
        h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose, comp_zero]
    | WalkingParallelPair.one =>
      dsimp
      rw [comp_id]
      rfl

instance {X : Cᵒᵖ ⥤ AddCommGrp.{v}} (hX : IsFinitelyPresented C X) :
    Epi hX.presentation_map_p := epi_of_isColimit_cofork hX.presentation_cokernel

def IsFinitelyPresented.presentation_iso {X : Cᵒᵖ ⥤ AddCommGrp} (hX : IsFinitelyPresented C X) :
    X ≅ cokernel (preadditiveYoneda.map (hX.presentation_map_f)) :=
  hX.presentation_cokernel.coconePointUniqueUpToIso (colimit.isColimit (parallelPair
    (preadditiveYoneda.map (hX.presentation_map_f)) 0))

end Presentation

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
    refine biproduct.lift (fun i ↦ kernel.lift (u i) (Fork.ι s ≫ biproduct.π A i) ?_)
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

lemma finitelyPresented_presentation (X : FinitelyPresented C) (B : Cᵒᵖ ⥤ AddCommGrp.{v})
    [(B ⋙ forget AddCommGrp).IsRepresentable] (g : B ⟶ X.1) [Epi g] :
    ∃ (A : Cᵒᵖ ⥤ AddCommGrp.{v}) (f : A ⟶ kernel g) (_ : Epi f),
    (A ⋙ forget AddCommGrp).IsRepresentable := by
  obtain ⟨A', B', f', g', _, zero, hA', hB', exact⟩ :=
    (isFinitelyPresented_iff_shortComplex_representable X.1).mp X.2
  obtain ⟨h, comm₁⟩ := IsRepresentable_proj B B' X.1 g g'
  obtain ⟨k, comm₂⟩ := IsRepresentable_proj B' B X.1 g' g
  use A' ⊞ B
  have zero' : biprod.desc (f' ≫ k) (𝟙 B - h ≫ k) ≫ g = 0 := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · simp only [biprod.inl_desc_assoc, assoc, comp_zero]
      rw [← comm₂, zero]
    · simp only [biprod.inr_desc_assoc, Preadditive.sub_comp, id_comp, assoc, comp_zero]
      rw [← comm₂, ← comm₁, sub_self]
  use kernel.lift g (biprod.desc (f' ≫ k) (𝟙 B - h ≫ k)) zero'
  simp only [exists_prop]
  refine ⟨?_, IsRepresentable_isClosedUnderBinaryBiproduct A' B hA' inferInstance⟩
  rw [epi_iff_surjective_up_to_refinements]
  intro Z a
  have ha₀ : a ≫ kernel.ι g ≫ h ≫ k ≫ g = 0 := by
    rw [← comm₂, ← comm₁, kernel.condition, comp_zero]
  have ha₁ : a ≫ kernel.ι g ≫ h ≫ g' = 0 := by rw [← comm₁, kernel.condition, comp_zero]
  rw [ShortComplex.exact_iff_epi_kernel_lift, epi_iff_surjective_up_to_refinements] at exact
  obtain ⟨Z', π, hπ, c', comp⟩ := exact (kernel.lift g' (a ≫ kernel.ι g ≫ h) ha₁)
  use Z', π, hπ, biprod.lift c' (π ≫ a ≫ kernel.ι g)
  rw [← cancel_mono (kernel.ι g)]
  dsimp at comp
  conv_rhs => rw [assoc, kernel.lift_ι, biprod.lift_desc, ← kernel.lift_ι g' f' zero,
                  ← assoc, ← assoc, ← comp, assoc π, kernel.lift_ι]
  dsimp
  simp

end FiniteProducts

section Cokernels

variable [Preadditive C] [HasFiniteProducts C]

instance : (IsFinitelyPresented C).ContainsCokernels where
  contains_cokernel {K K'} u := by
    refine {contains_colimit := ?_}
    obtain ⟨A, B, f, g, _, zero, hA, hB, exact⟩ :=
      (isFinitelyPresented_iff_shortComplex_representable K.1).mp K.2
    obtain ⟨A', B', f', g', _, zero', hA', hB', exact'⟩ :=
      (isFinitelyPresented_iff_shortComplex_representable K'.1).mp K'.2
    obtain ⟨v, comm⟩ := IsRepresentable_proj B B' K'.1 (g ≫ u) g'
    set L : Cᵒᵖ ⥤ AddCommGrp := cokernel u
    have hL : IsFinitelyPresented C L := by
      rw [isFinitelyPresented_iff_shortComplex_representable]
      set S := coker_sequence g (ShortComplex.mk f' g' zero') v u comm
      use S.X₁, S.X₂, S.f, S.g, inferInstance, S.zero
      refine ⟨?_, hB', coker_sequence_exact g _ exact' v u comm ⟩
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

instance : (IsFinitelyPresented C).ι.PreservesEpimorphisms where
  preserves f _ :=
    NormalMonoCategory.epi_of_zero_cokernel _ (cokernel ((IsFinitelyPresented C).ι.map f))
    (IsColimit.ofIsoColimit (cokernelIsCokernel ((IsFinitelyPresented C).ι.map f)) (Cofork.ext
    (Iso.refl _) (IsZero.eq_zero_of_tgt (IsZero.of_iso ((IsFinitelyPresented C).ι.map_isZero
    (IsZero.of_iso (isZero_zero _) (cokernel.ofEpi f)))
    (PreservesCokernel.iso (IsFinitelyPresented C).ι f).symm) _)))

lemma isFinitelyPresented_of_shortComplex_finitelyPresented (X : Cᵒᵖ ⥤ AddCommGrp.{v})
    (A B : Cᵒᵖ ⥤ AddCommGrp.{v}) (f : A ⟶ B) (g : B ⟶ X) [Epi g] (zero : f ≫ g = 0)
    (hA : IsFinitelyPresented C A) (hB : IsFinitelyPresented C B)
    (he : (ShortComplex.mk f g zero).Exact) : IsFinitelyPresented C X :=
  (IsFinitelyPresented C).prop_of_iso (PreservesCokernel.iso (IsFinitelyPresented C).ι f
  (X := ⟨A, hA⟩) (Y := ⟨B, hB⟩) ≪≫ (he.gIsCokernel.coconePointUniqueUpToIso
  (cokernelIsCokernel f)).symm) (cokernel f (C := FinitelyPresented C) (X := ⟨A, hA⟩)
  (Y := ⟨B, hB⟩)).2

end Cokernels

section Pseudokernels

variable [Preadditive C]

class HasPseudokernel {X Y : C} (f : X ⟶ Y) where
    exists_pseudokernel : ∃ (Z : C) (g : Z ⟶ X) (zero : g ≫ f = 0),
      Nonempty (IsLimit (KernelFork.ofι (f := preadditiveYoneda.map f) (preadditiveYoneda.map g)
      (by rw [← Functor.map_comp, zero, Functor.map_zero])))

variable (C) in
class HasPseudokernels where
    has_pseudokernel : ∀ {X Y : C} (f : X ⟶ Y), HasPseudokernel f

instance [HasPseudokernels C] {X Y : C} (f : X ⟶ Y) : HasPseudokernel f :=
  HasPseudokernels.has_pseudokernel f

def pseudokernel {X Y : C} (f : X ⟶ Y) [HasPseudokernel f] : C :=
  (HasPseudokernel.exists_pseudokernel (f := f)).choose

def pseudokernel.ι {X Y : C} (f : X ⟶ Y) [HasPseudokernel f] : pseudokernel f ⟶ X :=
  (HasPseudokernel.exists_pseudokernel (f := f)).choose_spec.choose

lemma pseudokernel.condition {X Y : C} (f : X ⟶ Y) [HasPseudokernel f] : pseudokernel.ι f ≫ f = 0 :=
  (HasPseudokernel.exists_pseudokernel (f := f)).choose_spec.choose_spec.choose

def pseudokernelIsPseudokernel {X Y : C} (f : X ⟶ Y) [HasPseudokernel f] :
    IsLimit (KernelFork.ofι (preadditiveYoneda.map (pseudokernel.ι f))
    (by rw [← Functor.map_comp, pseudokernel.condition f, Functor.map_zero])) :=
  Classical.choice (HasPseudokernel.exists_pseudokernel (f := f)).choose_spec.choose_spec.choose_spec

end Pseudokernels

section Kernels

variable [Preadditive C] [HasPseudokernels C] [HasFiniteProducts C]

lemma kernelIsRepresentable (A B : Cᵒᵖ ⥤ AddCommGrp.{v}) [(A ⋙ forget AddCommGrp).IsRepresentable]
    [(B ⋙ forget AddCommGrp).IsRepresentable] (f : A ⟶ B) :
    (kernel f ⋙ forget AddCommGrp).IsRepresentable := by
  set fA := Functor.representableByEquivAdd.toFun (A ⋙ forget AddCommGrp).representableBy
  set fB := Functor.representableByEquivAdd.toFun (B ⋙ forget AddCommGrp).representableBy
  obtain ⟨u, hu⟩ := preadditiveYoneda.map_surjective (fA.hom ≫ f ≫ fB.inv)
  refine Functor.RepresentableBy.isRepresentable (Y := pseudokernel u)
    (Functor.representableByEquivAdd.invFun ?_)
  have limc : IsLimit (KernelFork.ofι (f := preadditiveYoneda.map u) (kernel.ι f ≫ fA.inv)
      (by rw [hu]; simp)) := by
    refine KernelFork.isLimitOfIsLimitOfIff (kernelIsKernel f) _ fA.symm (fun _ _ ↦ ?_)
    rw [hu, ← assoc _ fA.hom, Iso.symm_hom, Iso.inv_hom_id, id_comp, ← assoc]
    exact ⟨fun h ↦ by rw [h, zero_comp], fun h ↦ by rw [← cancel_mono fB.inv, h, zero_comp]⟩
  exact (pseudokernelIsPseudokernel u).conePointUniqueUpToIso limc ≪≫
    KernelFork.mapIsoOfIsLimit limc (limit.isLimit (parallelPair f 0))
    (Arrow.isoMk fA fB (by dsimp; rw [hu, assoc, assoc, Iso.inv_hom_id, comp_id]))

lemma isFinitelyPresented_kernel_epi_representable_to_finitelyPresented (X : FinitelyPresented C)
    (A' : Cᵒᵖ ⥤ AddCommGrp.{v}) [(A' ⋙ forget AddCommGrp).IsRepresentable] (f : A' ⟶ X.1) [Epi f] :
    IsFinitelyPresented C (kernel f) := by
  rw [isFinitelyPresented_iff_shortComplex_representable]
  obtain ⟨A, g, _, hA⟩ := finitelyPresented_presentation  X A' f
  have hB : (kernel g ⋙ forget AddCommGrp).IsRepresentable := by
    have := kernelIsRepresentable A A' (g ≫ kernel.ι f)
    set e : kernel g ≅ kernel (g ≫ kernel.ι f) := (isKernelCompMono (kernelIsKernel g) (kernel.ι f)
       rfl).conePointUniqueUpToIso (limit.isLimit (parallelPair (g ≫ kernel.ι f) 0))
    exact isRepresentable_of_natIso _ (isoWhiskerRight e.symm (forget AddCommGrp))
  use kernel g, A, kernel.ι g, g, inferInstance, kernel.condition g
  exact ⟨hB, hA, ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel g)⟩

instance : (IsFinitelyPresented C).ContainsKernelsOfEpi where
  contains_kernel {K K'} u hu := by
    have : Epi (C := Cᵒᵖ ⥤ AddCommGrp) (u : K.1 ⟶ K'.1) := (IsFinitelyPresented C).ι.map_epi u
    refine {contains_limit := ?_}
    obtain ⟨A, B, f, g, _, zero, hA, hB, exact⟩ :=
      (isFinitelyPresented_iff_shortComplex_representable K.1).mp K.2
    obtain ⟨A', B', f', g', _, zero', hA', hB', exact'⟩ :=
      (isFinitelyPresented_iff_shortComplex_representable K'.1).mp K'.2
    set L := kernel (C := Cᵒᵖ ⥤ AddCommGrp) u
    have hL : IsFinitelyPresented C L := by
      let S := kernelCokernelCompSequence g u
      have hS := kernelCokernelCompSequence_exact g u
      have : Epi (S.map' 1 2) := ((S.sc hS.toIsComplex 1).exact_iff_epi (IsZero.eq_zero_of_tgt
        (IsZero.of_iso (isZero_zero _) (cokernel.ofEpi g)) _)).mp (hS.exact 1 (by omega))
      have h₀ : IsFinitelyPresented C (S.obj 0) :=
        isFinitelyPresented_kernel_epi_representable_to_finitelyPresented K B g
      have h₁ : IsFinitelyPresented C (S.obj 1) :=
        isFinitelyPresented_kernel_epi_representable_to_finitelyPresented K' B (g ≫ u)
      have : 2 ≤ 5 := by omega
      exact isFinitelyPresented_of_shortComplex_finitelyPresented (S.obj 2) (S.obj 0) (S.obj 1)
        (S.map' 0 1) (S.map' 1 2 one_le_two this) (hS.toIsComplex.zero 0 (by omega)) h₀ h₁
        (hS.exact 0 (by omega))
    refine ⟨KernelFork.ofι (C := FinitelyPresented C) (Z := ⟨L, hL⟩) (kernel.ι u
      (C := Cᵒᵖ ⥤ AddCommGrp)) (kernel.condition u (C := Cᵒᵖ ⥤ AddCommGrp)),
      Nonempty.intro {lift s := ?_, fac s j := ?_, uniq s m hm := ?_}⟩
    · refine kernel.lift u (C := Cᵒᵖ ⥤ AddCommGrp) (s.π.app WalkingParallelPair.zero) ?_
      have := s.π.naturality WalkingParallelPairHom.left
      dsimp at this
      rw [id_comp] at this; rw [← this]
      have := s.π.naturality WalkingParallelPairHom.right
      dsimp at this
      rw [id_comp] at this; rw [this, comp_zero]
    · match j with
      | WalkingParallelPair.zero => dsimp; simp
      | WalkingParallelPair.one =>
        dsimp
        erw [kernel.condition u (C := Cᵒᵖ ⥤ AddCommGrp)]; rw [comp_zero]
        have := s.π.naturality WalkingParallelPairHom.right
        dsimp at this
        rw [id_comp, comp_zero] at this
        exact this.symm
    · rw [← cancel_mono (kernel.ι u (C := Cᵒᵖ ⥤ AddCommGrp))]
      dsimp; simp only [kernel.lift_ι]
      exact hm WalkingParallelPair.zero

instance : (IsFinitelyPresented C).ContainsKernels :=
  ContainsKernels_of_containsKernelsEpiAndCokernels _

instance : IsAbelian (IsFinitelyPresented C) := IsAbelian_ofKernelsOfEpi _

end Kernels
