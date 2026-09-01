import GaloisForLFunctions.HTGeometry.AsymmetricDifferenceTensor
import GaloisForLFunctions.HTGeometry.SigmaIdealConstantCoefficients
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearIndependence
import GaloisForLFunctions.HTGeometry.TensorProductAlgClosedReduced

/-!
# Difference-field scalar extension preserves sigma-simplicity

Let `F` be a difference field with exact constant field `C`, and let `L/C` be any field
extension on which the difference operator acts trivially.  Then `L tensor_C F` is sigma-simple
and its fixed elements are exactly its left-factor copy of `L`.

This is the algebraic scalar-extension lemma used in meromorphic parameterized
Picard--Vessiot theory.  The proof is the minimal-support argument: expand a nonzero ideal element
against a `C`-basis of `L`, use sigma-simplicity of the field `F` to replace its coefficients by
fixed coefficients, descend those coefficients to `C`, and obtain a nonzero unit from `L` in the
ideal.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C L F : Type*} [Field C] [Field L] [Field F]
  [Algebra C L] [Algebra C F]

/-- Difference action on a constant-field scalar extension. -/
def scalarExtensionSigma (sigmaF : F ≃+* F)
    (hbase : ∀ c : C, sigmaF (algebraMap C F c) = algebraMap C F c) :
    (L ⊗[C] F) ≃+* (L ⊗[C] F) :=
  asymmetricDifferenceTensorEquiv (RingEquiv.refl C) (RingEquiv.refl L) sigmaF
    (fun _ => rfl) (fun c => by simpa using hbase c)

local instance scalarExtensionRightAlgebra : Algebra F (L ⊗[C] F) :=
  Algebra.TensorProduct.rightAlgebra

/-- A constant-field basis stays independent over the difference field after scalar extension. -/
theorem scalarExtension_basisIndependent
    (bs : Module.Basis ι C L) :
    BasisIndependentOver F (fun i => bs i ⊗ₜ[C] (1 : F)) := by
  classical
  have hli : LinearIndependent F (fun i => (1 : F) ⊗ₜ[C] bs i) :=
    (ABHN.linearIndependent_one_tmul_iff (L := F) (fun i => bs i)).mp
      bs.linearIndependent
  rw [linearIndependent_iff'] at hli
  intro t r hzero j hj
  apply hli t r _ j hj
  have hzero' := congrArg (Algebra.TensorProduct.comm C L F) hzero
  have hterm : ∀ i,
      (Algebra.TensorProduct.comm C L F)
          (algebraMap F (L ⊗[C] F) (r i) * (bs i ⊗ₜ[C] (1 : F))) =
        r i ⊗ₜ[C] bs i := by
    intro i
    change (Algebra.TensorProduct.comm C L F)
        (((1 : L) ⊗ₜ[C] r i) * (bs i ⊗ₜ[C] (1 : F))) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.comm_tmul]
    simp
  rw [map_sum] at hzero'
  have hzero'' : (∑ i ∈ t, r i ⊗ₜ[C] bs i) = 0 := by
    calc
      _ = ∑ i ∈ t, (Algebra.TensorProduct.comm C L F)
          (algebraMap F (L ⊗[C] F) (r i) * (bs i ⊗ₜ[C] (1 : F))) :=
        Finset.sum_congr rfl fun i _ => (hterm i).symm
      _ = (Algebra.TensorProduct.comm C L F) 0 := hzero'
      _ = 0 := map_zero _
  simpa [Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul] using hzero''

/-- Scalar extension by an arbitrary constant field preserves sigma-simplicity. -/
theorem scalarExtension_isSigmaSimple
    (sigmaF : F ≃+* F)
    (hbase : ∀ c : C, sigmaF (algebraMap C F c) = algebraMap C F c)
    (hexact : ∀ x : F, sigmaF x = x → ∃ c : C, x = algebraMap C F c) :
    IsSigmaSimple (scalarExtensionSigma sigmaF hbase : (L ⊗[C] F) ≃+* _) := by
  classical
  let sigmaA : (L ⊗[C] F) ≃+* (L ⊗[C] F) :=
    scalarExtensionSigma (L := L) sigmaF hbase
  let bs := Module.Basis.ofVectorSpace C L
  intro I hI
  by_cases hbot : I = ⊥
  · exact Or.inl hbot
  right
  have hne : ∃ z : L ⊗[C] F, z ∈ I ∧ z ≠ 0 := by
    by_contra h
    push Not at h
    apply hbot
    apply le_antisymm
    · intro z hz
      exact Ideal.mem_bot.mpr (h z hz)
    · exact bot_le
  obtain ⟨z, hzI, hz0⟩ := hne
  obtain ⟨t, r, hzrepr⟩ := exists_basis_tmul_repr bs
    ((Algebra.TensorProduct.comm C L F) z)
  have hzrepr' : z = ∑ i ∈ t, bs i ⊗ₜ[C] r i := by
    apply (Algebra.TensorProduct.comm C L F).injective
    rw [hzrepr, map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Algebra.TensorProduct.comm_tmul]
  have hrne : ∃ i ∈ t, r i ≠ 0 := by
    by_contra h
    push Not at h
    apply hz0
    rw [hzrepr']
    apply Finset.sum_eq_zero
    intro i hi
    rw [h i hi, TensorProduct.tmul_zero]
  have hzcoeff :
      (∑ i ∈ t, algebraMap F (L ⊗[C] F) (r i) *
        (bs i ⊗ₜ[C] (1 : F))) ∈ I := by
    have heq : (∑ i ∈ t, algebraMap F (L ⊗[C] F) (r i) *
        (bs i ⊗ₜ[C] (1 : F))) = z := by
      rw [hzrepr']
      refine Finset.sum_congr rfl fun i _ => ?_
      change ((1 : L) ⊗ₜ[C] r i) * (bs i ⊗ₜ[C] (1 : F)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [heq]
    exact hzI
  obtain ⟨u, d, hdfix, hdI, hd0⟩ :=
    exists_nonzero_constant_coeff_mem_sigmaIdeal sigmaF sigmaA
      (fun x => by
        change sigmaA ((1 : L) ⊗ₜ[C] x) = (1 : L) ⊗ₜ[C] sigmaF x
        simp [sigmaA, scalarExtensionSigma])
      (fun J _ => J.eq_bot_or_top)
      (fun i => bs i ⊗ₜ[C] (1 : F))
      (fun _ => by simp [sigmaA, scalarExtensionSigma])
      (scalarExtension_basisIndependent bs) I hI t r hrne hzcoeff
  let c : Module.Basis.ofVectorSpaceIndex C L → C := fun i =>
    if hi : i ∈ u then Classical.choose (hexact (d i) (hdfix i hi)) else 0
  have hc : ∀ i ∈ u, d i = algebraMap C F (c i) := by
    intro i hi
    simp only [c, dif_pos hi]
    exact Classical.choose_spec (hexact (d i) (hdfix i hi))
  let ell : L := ∑ i ∈ u, c i • bs i
  have hsum :
      (∑ i ∈ u, algebraMap F (L ⊗[C] F) (d i) *
        (bs i ⊗ₜ[C] (1 : F))) =
      Algebra.TensorProduct.includeLeft (R := C) (S := C) (A := L) (B := F) ell := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hc i hi]
    rw [Algebra.TensorProduct.includeLeft_apply]
    rw [show algebraMap F (L ⊗[C] F) (algebraMap C F (c i)) =
        (1 : L) ⊗ₜ[C] algebraMap C F (c i) by rfl]
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    simpa [Algebra.smul_def] using
      (TensorProduct.tmul_smul (R := C) (c i) (bs i) (1 : F))
  have hell0 : ell ≠ 0 := by
    intro h
    apply hd0
    rw [hsum, h, map_zero]
  have hunit : IsUnit
      (Algebra.TensorProduct.includeLeft (R := C) (S := C) (A := L) (B := F) ell) :=
    (isUnit_iff_ne_zero.mpr hell0).map
      (Algebra.TensorProduct.includeLeft (R := C) (S := C) (A := L) (B := F))
  exact Ideal.eq_top_of_isUnit_mem I (hsum ▸ hdI) hunit

/-- Fixed elements of the scalar extension descend exactly to the adjoined constant field. -/
theorem scalarExtension_fixed_eq_includeLeft
    (sigmaF : F ≃+* F)
    (hbase : ∀ c : C, sigmaF (algebraMap C F c) = algebraMap C F c)
    (hexact : ∀ x : F, sigmaF x = x → ∃ c : C, x = algebraMap C F c)
    {z : L ⊗[C] F}
    (hz : scalarExtensionSigma (L := L) sigmaF hbase z = z) :
    ∃ ell : L, z =
      Algebra.TensorProduct.includeLeft (R := C) (S := C) (A := L) (B := F) ell := by
  classical
  let sigmaA : (L ⊗[C] F) ≃+* (L ⊗[C] F) :=
    scalarExtensionSigma (L := L) sigmaF hbase
  let bs := Module.Basis.ofVectorSpace C L
  obtain ⟨t, r, hzrepr⟩ := exists_basis_tmul_repr bs
    ((Algebra.TensorProduct.comm C L F) z)
  have hzrepr' : z = ∑ i ∈ t, bs i ⊗ₜ[C] r i := by
    apply (Algebra.TensorProduct.comm C L F).injective
    rw [hzrepr, map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Algebra.TensorProduct.comm_tmul]
  have hshift : (∑ i ∈ t, bs i ⊗ₜ[C] sigmaF (r i)) =
      ∑ i ∈ t, bs i ⊗ₜ[C] r i := by
    calc
      _ = sigmaA (∑ i ∈ t, bs i ⊗ₜ[C] r i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by
          simp [sigmaA, scalarExtensionSigma]
      _ = sigmaA z := congrArg sigmaA hzrepr'.symm
      _ = z := hz
      _ = _ := hzrepr'
  have hdiff : (∑ i ∈ t, bs i ⊗ₜ[C] (sigmaF (r i) - r i)) = 0 := by
    rw [show (∑ i ∈ t, bs i ⊗ₜ[C] (sigmaF (r i) - r i)) =
        (∑ i ∈ t, bs i ⊗ₜ[C] sigmaF (r i)) -
          ∑ i ∈ t, bs i ⊗ₜ[C] r i by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [TensorProduct.tmul_sub]]
    rw [hshift, sub_self]
  have hzero :
      (∑ i ∈ t, algebraMap F (L ⊗[C] F) (sigmaF (r i) - r i) *
        (bs i ⊗ₜ[C] (1 : F))) = 0 := by
    rw [show (∑ i ∈ t, algebraMap F (L ⊗[C] F) (sigmaF (r i) - r i) *
        (bs i ⊗ₜ[C] (1 : F))) =
      ∑ i ∈ t, bs i ⊗ₜ[C] (sigmaF (r i) - r i) by
      refine Finset.sum_congr rfl fun i _ => ?_
      change ((1 : L) ⊗ₜ[C] (sigmaF (r i) - r i)) *
          (bs i ⊗ₜ[C] (1 : F)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]]
    exact hdiff
  have hcoeff : ∀ i ∈ t, sigmaF (r i) = r i := by
    intro i hi
    exact sub_eq_zero.mp
      (scalarExtension_basisIndependent bs t (fun j => sigmaF (r j) - r j) hzero i hi)
  let c : Module.Basis.ofVectorSpaceIndex C L → C := fun i =>
    if hi : i ∈ t then Classical.choose (hexact (r i) (hcoeff i hi)) else 0
  have hc : ∀ i ∈ t, r i = algebraMap C F (c i) := by
    intro i hi
    simp only [c, dif_pos hi]
    exact Classical.choose_spec (hexact (r i) (hcoeff i hi))
  let ell : L := ∑ i ∈ t, c i • bs i
  refine ⟨ell, ?_⟩
  rw [hzrepr', map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hc i hi, Algebra.TensorProduct.includeLeft_apply]
  simpa [Algebra.smul_def] using
    (TensorProduct.tmul_smul (R := C) (c i) (bs i) (1 : F))

end

end GaloisForLFunctions.HTGeometry
