/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAzumaya
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaScalarExtensionSimple

/-!
# Hasse detection of central simplicity

Scalar extension reflects centrality. For a finite-dimensional central algebra over a field, it
also reflects simplicity: the reverse implication descends Azumaya structure along the faithfully
flat extension, then uses that an Azumaya algebra over a field is simple.

Consequently finite-dimensional central simple algebras are detected at every completion of a
number field or global function field. This is structural local--global infrastructure; it is not
the ABHN assertion that a Brauer class is split at every place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- A central algebra stays central after scalar extension. -/
theorem scalarExtension_isCentral_of_isCentral
    {K : Type u} {L : Type v} {A : Type w} [Field K] [Field L]
    [Algebra K L] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [Module.Free K A] :
    Algebra.IsCentral L (L ⊗[K] A) := by
  constructor
  intro z hz
  rw [Subalgebra.mem_center_iff] at hz
  rw [Algebra.mem_bot]
  have hz' : z ∈ Subalgebra.centralizer K
      (↑(Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).range) := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro g ⟨a, rfl⟩
    exact hz _
  rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct K L A] at hz'
  rcases hz' with ⟨x, hx⟩
  subst z
  clear hz
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul l a =>
      obtain ⟨k, hk⟩ := (Algebra.IsCentral.mem_center_iff K).mp a.prop
      refine ⟨l * algebraMap K L k, ?_⟩
      simpa [Algebra.TensorProduct.map_tmul, hk, Algebra.smul_def, mul_comm] using
        (TensorProduct.tmul_smul (R := K) (R' := K) (M := L) (N := A)
          k l (1 : A)).symm
  | add x y hx hy =>
      obtain ⟨lx, hx⟩ := hx
      obtain ⟨ly, hy⟩ := hy
      refine ⟨lx + ly, ?_⟩
      change algebraMap L (L ⊗[K] A) (lx + ly) = _
      rw [map_add, map_add, hx, hy]

/-- Centrality descends from a scalar extension. -/
theorem isCentral_of_scalarExtension_isCentral
    {K : Type u} {L : Type v} {A : Type w} [Field K] [Field L]
    [Algebra K L] [Ring A] [Algebra K A]
    (h : Algebra.IsCentral L (L ⊗[K] A)) : Algebra.IsCentral K A := by
  letI : Algebra.IsCentral L (L ⊗[K] A) := h
  by_cases hA : Nontrivial A
  · letI : Nontrivial A := hA
    let i : K →ₗ[K] A := (Algebra.ofId K A).toLinearMap
    have hi : Function.Injective i := FaithfulSMul.algebraMap_injective K A
    have hker : LinearMap.ker i = ⊥ := LinearMap.ker_eq_bot.mpr hi
    let phi : A →ₗ[K] K := i.leftInverse
    have hphi_one : phi (1 : A) = 1 := by
      simpa [phi, i] using LinearMap.leftInverse_apply_of_inj hker (1 : K)
    constructor
    intro a ha
    rw [Subalgebra.mem_center_iff] at ha
    rw [Algebra.mem_bot]
    have haL : Algebra.TensorProduct.includeRight a ∈
        Subalgebra.center L (L ⊗[K] A) := by
      rw [Subalgebra.mem_center_iff]
      intro x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro l b
        simpa [Algebra.TensorProduct.tmul_mul_tmul] using
          congrArg (fun c : A => l ⊗ₜ[K] c) (ha b)
      · intro x y hx hy
        rw [mul_add, add_mul, hx, hy]
    obtain ⟨l, hl⟩ := (Algebra.IsCentral.mem_center_iff L).mp haL
    have hscalar : l = algebraMap K L (phi a) := by
      have happly := congrArg (fun x => TensorProduct.rid K L (LinearMap.lTensor L phi x)) hl
      change phi a • (1 : L) = phi (1 : A) • l at happly
      rw [hphi_one] at happly
      simpa [Algebra.smul_def] using happly.symm
    refine ⟨phi a, ?_⟩
    apply Algebra.TensorProduct.includeRight_injective
      (FaithfulSMul.algebraMap_injective K L)
    calc
      Algebra.TensorProduct.includeRight (algebraMap K A (phi a)) =
          algebraMap L (L ⊗[K] A) (algebraMap K L (phi a)) := by
        change 1 ⊗ₜ[K] algebraMap K A (phi a) = algebraMap K L (phi a) ⊗ₜ[K] (1 : A)
        exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := K) (A := L) (B := A) (phi a)).symm
      _ = algebraMap L (L ⊗[K] A) l := by rw [hscalar]
      _ = Algebra.TensorProduct.includeRight a := hl.symm
  · letI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    constructor
    intro a _
    rw [Algebra.mem_bot]
    exact ⟨0, Subsingleton.elim _ _⟩

/-- For finite-dimensional algebras, centrality is reflected by scalar extension. -/
theorem isCentral_iff_tensorProduct_isCentral
    {K : Type u} {L : Type v} {A : Type w} [Field K] [Field L]
    [Algebra K L] [Ring A] [Algebra K A] [Module.Finite K A] :
    Algebra.IsCentral K A ↔ Algebra.IsCentral L (L ⊗[K] A) := by
  constructor
  · intro h
    letI : Algebra.IsCentral K A := h
    exact scalarExtension_isCentral_of_isCentral
  · exact isCentral_of_scalarExtension_isCentral

/-- Simplicity descends from a scalar extension for finite-dimensional central algebras. -/
theorem isSimpleRing_of_isSimpleRing_scalarExtension
    {K : Type u} {L : Type v} {A : Type w} [Field K] [Field L]
    [Algebra K L] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [Module.Finite K A]
    (h : IsSimpleRing (L ⊗[K] A)) : IsSimpleRing A := by
  letI : Algebra.IsCentral L (L ⊗[K] A) := scalarExtension_isCentral_of_isCentral
  letI : IsSimpleRing (L ⊗[K] A) := h
  letI : Module.Finite L (L ⊗[K] A) := Module.Finite.base_change K L A
  let localCSA : CSA.{v, max v w} L :=
    { carrier := L ⊗[K] A
      isCentral := inferInstance
      isSimple := inferInstance
      fin_dim := by infer_instance }
  letI : IsAzumaya L (L ⊗[K] A) := csa_isAzumaya localCSA
  letI : IsAzumaya K A := isAzumaya_of_scalarExtension (K := K) (L := L) (A := A)
  exact isSimpleRing_of_isAzumaya (K := K) A

/-- For finite-dimensional central algebras, simplicity is reflected by scalar extension. -/
theorem isSimpleRing_iff_tensorProduct_isSimpleRing
    {K : Type u} {L : Type v} {A : Type w} [Field K] [Field L]
    [Algebra K L] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [Module.Finite K A] :
    IsSimpleRing A ↔ IsSimpleRing (L ⊗[K] A) := by
  constructor
  · intro h
    letI : IsSimpleRing A := h
    let globalCSA : CSA.{u, w} K :=
      { carrier := A
        isCentral := inferInstance
        isSimple := inferInstance
        fin_dim := by infer_instance }
    letI : IsAzumaya K A := csa_isAzumaya globalCSA
    exact isSimpleRing_scalarExtension
  · exact isSimpleRing_of_isSimpleRing_scalarExtension

/-- For finite-dimensional field algebras, central simplicity is reflected by scalar extension. -/
theorem isCentral_and_isSimpleRing_iff_tensorProduct
    {K : Type u} {L : Type v} {A : Type w} [Field K] [Field L]
    [Algebra K L] [Ring A] [Algebra K A] [Module.Finite K A] :
    (Algebra.IsCentral K A ∧ IsSimpleRing A) ↔
      (Algebra.IsCentral L (L ⊗[K] A) ∧ IsSimpleRing (L ⊗[K] A)) := by
  constructor
  · rintro ⟨hcentral, hsimple⟩
    letI : Algebra.IsCentral K A := hcentral
    exact ⟨(isCentral_iff_tensorProduct_isCentral (L := L)).mp hcentral,
      (isSimpleRing_iff_tensorProduct_isSimpleRing (L := L)).mp hsimple⟩
  · rintro ⟨hcentral, hsimple⟩
    have hcentral' := (isCentral_iff_tensorProduct_isCentral (L := L)).mpr hcentral
    letI : Algebra.IsCentral K A := hcentral'
    exact ⟨hcentral',
      (isSimpleRing_iff_tensorProduct_isSimpleRing (L := L)).mpr hsimple⟩

/-- A finite-dimensional central algebra over a number field is simple exactly when all of its
completed scalar extensions are simple. -/
theorem numberField_isSimpleRing_iff_forall_place (K : Type u) [Field K] [NumberField K]
    {A : Type w} [Ring A] [Algebra K A] [Algebra.IsCentral K A] [Module.Finite K A] :
    IsSimpleRing A ↔ ∀ p : NumberFieldPlace K, IsSimpleRing (completion K p ⊗[K] A) := by
  constructor
  · intro h p
    exact (isSimpleRing_iff_tensorProduct_isSimpleRing (L := completion K p)).mp h
  · intro h
    exact (isSimpleRing_iff_tensorProduct_isSimpleRing
      (L := completion K (witnessPlace K))).mpr (h (witnessPlace K))

/-- A finite-dimensional central algebra over `F(t)` is simple exactly when all of its finite and
infinite completed scalar extensions are simple. -/
theorem rationalFunction_isSimpleRing_iff_forall_place (F : Type u) [Field F] [Finite F]
    {A : Type w} [Ring A] [Algebra (RatFunc F) A] [Algebra.IsCentral (RatFunc F) A]
    [Module.Finite (RatFunc F) A] :
    IsSimpleRing A ↔ ∀ p : RationalFunctionPlace F,
      IsSimpleRing (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h p
    exact (isSimpleRing_iff_tensorProduct_isSimpleRing
      (L := rationalFunctionCompletion F p)).mp h
  · intro h
    exact (isSimpleRing_iff_tensorProduct_isSimpleRing
      (L := rationalFunctionCompletion F .infinite)).mpr (h .infinite)

/-- A finite-dimensional field algebra over a number field is central and simple exactly when all
of its completed scalar extensions are central and simple. -/
theorem numberField_isCentral_and_isSimpleRing_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {A : Type w} [Ring A] [Algebra K A]
    [Module.Finite K A] :
    (Algebra.IsCentral K A ∧ IsSimpleRing A) ↔
      ∀ p : NumberFieldPlace K,
        Algebra.IsCentral (completion K p) (completion K p ⊗[K] A) ∧
          IsSimpleRing (completion K p ⊗[K] A) := by
  constructor
  · intro h p
    exact (isCentral_and_isSimpleRing_iff_tensorProduct (L := completion K p)).mp h
  · intro h
    exact (isCentral_and_isSimpleRing_iff_tensorProduct
      (L := completion K (witnessPlace K))).mpr (h (witnessPlace K))

/-- A finite-dimensional field algebra over `F(t)` is central and simple exactly when all of its
finite and infinite completed scalar extensions are central and simple. -/
theorem rationalFunction_isCentral_and_isSimpleRing_iff_forall_place
    (F : Type u) [Field F] [Finite F] {A : Type w} [Ring A] [Algebra (RatFunc F) A]
    [Module.Finite (RatFunc F) A] :
    (Algebra.IsCentral (RatFunc F) A ∧ IsSimpleRing A) ↔
      ∀ p : RationalFunctionPlace F,
        Algebra.IsCentral (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] A) ∧
          IsSimpleRing (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h p
    exact (isCentral_and_isSimpleRing_iff_tensorProduct
      (L := rationalFunctionCompletion F p)).mp h
  · intro h
    exact (isCentral_and_isSimpleRing_iff_tensorProduct
      (L := rationalFunctionCompletion F .infinite)).mpr (h .infinite)

/-- Centrality of a finite-dimensional number-field algebra is detected at one completion. -/
theorem numberField_isCentral_iff_exists_place (K : Type u) [Field K] [NumberField K]
    {A : Type w} [Ring A] [Algebra K A] [Module.Finite K A] :
    Algebra.IsCentral K A ↔ ∃ p : NumberFieldPlace K,
      Algebra.IsCentral (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (isCentral_iff_tensorProduct_isCentral (L := completion K (witnessPlace K))).mp h⟩
  · rintro ⟨p, hp⟩
    exact (isCentral_iff_tensorProduct_isCentral (L := completion K p)).mpr hp

/-- Centrality of a finite-dimensional rational-function-field algebra is detected at one finite
or infinite completion. -/
theorem rationalFunction_isCentral_iff_exists_place (F : Type u) [Field F] [Finite F]
    {A : Type w} [Ring A] [Algebra (RatFunc F) A] [Module.Finite (RatFunc F) A] :
    Algebra.IsCentral (RatFunc F) A ↔ ∃ p : RationalFunctionPlace F,
      Algebra.IsCentral (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (isCentral_iff_tensorProduct_isCentral
        (L := rationalFunctionCompletion F .infinite)).mp h⟩
  · rintro ⟨p, hp⟩
    exact (isCentral_iff_tensorProduct_isCentral
      (L := rationalFunctionCompletion F p)).mpr hp

/-- Simplicity of a finite-dimensional central number-field algebra is detected at one
completion. -/
theorem numberField_isSimpleRing_iff_exists_place (K : Type u) [Field K] [NumberField K]
    {A : Type w} [Ring A] [Algebra K A] [Algebra.IsCentral K A] [Module.Finite K A] :
    IsSimpleRing A ↔ ∃ p : NumberFieldPlace K, IsSimpleRing (completion K p ⊗[K] A) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (isSimpleRing_iff_tensorProduct_isSimpleRing
        (L := completion K (witnessPlace K))).mp h⟩
  · rintro ⟨p, hp⟩
    exact (isSimpleRing_iff_tensorProduct_isSimpleRing (L := completion K p)).mpr hp

/-- Simplicity of a finite-dimensional central rational-function-field algebra is detected at
one finite or infinite completion. -/
theorem rationalFunction_isSimpleRing_iff_exists_place (F : Type u) [Field F] [Finite F]
    {A : Type w} [Ring A] [Algebra (RatFunc F) A] [Algebra.IsCentral (RatFunc F) A]
    [Module.Finite (RatFunc F) A] :
    IsSimpleRing A ↔ ∃ p : RationalFunctionPlace F,
      IsSimpleRing (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (isSimpleRing_iff_tensorProduct_isSimpleRing
        (L := rationalFunctionCompletion F .infinite)).mp h⟩
  · rintro ⟨p, hp⟩
    exact (isSimpleRing_iff_tensorProduct_isSimpleRing
      (L := rationalFunctionCompletion F p)).mpr hp

/-- Central simplicity of a finite-dimensional number-field algebra is detected at one
completion. -/
theorem numberField_isCentral_and_isSimpleRing_iff_exists_place
    (K : Type u) [Field K] [NumberField K] {A : Type w} [Ring A] [Algebra K A]
    [Module.Finite K A] :
    (Algebra.IsCentral K A ∧ IsSimpleRing A) ↔ ∃ p : NumberFieldPlace K,
      Algebra.IsCentral (completion K p) (completion K p ⊗[K] A) ∧
        IsSimpleRing (completion K p ⊗[K] A) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (isCentral_and_isSimpleRing_iff_tensorProduct
        (L := completion K (witnessPlace K))).mp h⟩
  · rintro ⟨p, hp⟩
    exact (isCentral_and_isSimpleRing_iff_tensorProduct (L := completion K p)).mpr hp

/-- Central simplicity of a finite-dimensional rational-function-field algebra is detected at
one finite or infinite completion. -/
theorem rationalFunction_isCentral_and_isSimpleRing_iff_exists_place
    (F : Type u) [Field F] [Finite F] {A : Type w} [Ring A] [Algebra (RatFunc F) A]
    [Module.Finite (RatFunc F) A] :
    (Algebra.IsCentral (RatFunc F) A ∧ IsSimpleRing A) ↔ ∃ p : RationalFunctionPlace F,
      Algebra.IsCentral (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) ∧
          IsSimpleRing (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (isCentral_and_isSimpleRing_iff_tensorProduct
        (L := rationalFunctionCompletion F .infinite)).mp h⟩
  · rintro ⟨p, hp⟩
    exact (isCentral_and_isSimpleRing_iff_tensorProduct
      (L := rationalFunctionCompletion F p)).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
