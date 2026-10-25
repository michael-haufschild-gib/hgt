import GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorDiagonalsAreHorizonEnergyRatios
import GaloisForLFunctions.HTGeometry.MonotoneMultiplicativeProfilesArePowers
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Rank-one actual cofactor magnitudes are powers

Real covariance makes every one-dimensional actual module a real
multiplicative character. Numeric horizon order fixes its magnitude to
augmentation or p^(-s), with s at least one half; it does not fix signs.
-/

section

noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- In one dimension each cofactor is its real covariance with the unit cyclic vector. -/
theorem vector_eq_kernel_smul_of_finrank_one {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (hL : Module.finrank ℂ (Hilbert L) = 1) (p : ℕ+) :
    vector L p = (L.kernel p 1 : ℂ) • vector L 1 := by
  obtain ⟨z, hz⟩ := (finrank_eq_one_iff_of_nonzero' (vector L 1) (vector_one_ne_zero L)).mp hL
    (vector L p)
  have hc := congrArg (fun v => inner ℂ (vector L 1) v) hz
  rw [inner_smul_right, inner_vector, L.kernel_one_one, Complex.ofReal_one,
    mul_one, inner_vector] at hc
  rw [hc] at hz
  exact hz.symm

/-- A rank-one actual Gram is the product of its real cyclic character values. -/
theorem kernel_eq_product_of_finrank_one {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (hL : Module.finrank ℂ (Hilbert L) = 1) (j k : ℕ+) :
    L.kernel j k = L.kernel j 1 * L.kernel k 1 := by
  have h := inner_vector L j k
  rw [vector_eq_kernel_smul_of_finrank_one L hL j,
    vector_eq_kernel_smul_of_finrank_one L hL k,
    inner_smul_left, inner_smul_right, inner_vector, L.kernel_one_one,
    Complex.ofReal_one, mul_one, Complex.conj_ofReal, ← Complex.ofReal_mul] at h
  have hh := Complex.ofReal_injective h
  linarith only [hh]

/-- Real covariance determines the multiplicative character of every actual rank-one module. -/
def rankOneCharacter {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (hL : Module.finrank ℂ (Hilbert L) = 1) : ℕ+ →* ℝ where
  toFun p := L.kernel p 1
  map_one' := L.kernel_one_one
  map_mul' p q := by
    have hv := congrArg (fun v => dilation L p v)
      (vector_eq_kernel_smul_of_finrank_one L hL q)
    rw [dilation_vector, map_smul, dilation_vector, mul_one,
      vector_eq_kernel_smul_of_finrank_one L hL (p * q),
      vector_eq_kernel_smul_of_finrank_one L hL p, smul_smul] at hv
    have h := congrArg (fun v => inner ℂ (vector L 1) v) hv
    simp only [inner_smul_right, inner_vector, L.kernel_one_one,
      Complex.ofReal_one, mul_one, ← Complex.ofReal_mul] at h
    have hh := Complex.ofReal_injective h
    simpa only [mul_comm] using hh

/-- The energy-ratio profile of an actual line is itself multiplicative. -/
def rankOneEnergyCharacter {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (hL : Module.finrank ℂ (Hilbert L) = 1) : ℕ+ →* ℝ where
  toFun p := (p : ℝ) * rankOneCharacter L hL p ^ 2
  map_one' := by norm_num
  map_mul' p q := by
    simp only [map_mul, mul_pow, PNat.mul_coe, Nat.cast_mul]
    ring

/-- Actual rank-one magnitudes are augmentation or one Archimedean power law. -/
theorem rankOneCharacter_eq_augmentation_or_abs_rpow {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (hL : Module.finrank ℂ (Hilbert L) = 1) :
    (∀ p : ℕ+, p ≠ 1 → rankOneCharacter L hL p = 0) ∨
      ∃ s : ℝ, 1 / 2 ≤ s ∧
        ∀ p : ℕ+, |rankOneCharacter L hL p| = (p : ℝ) ^ (-s) := by
  have hr0 (p : ℕ+) : 0 ≤ rankOneEnergyCharacter L hL p := by
    change 0 ≤ (p : ℝ) * rankOneCharacter L hL p ^ 2
    positivity
  have hr (p : ℕ+) : rankOneEnergyCharacter L hL p = (p : ℝ) * L.kernel p p := by
    change (p : ℝ) * L.kernel p 1 ^ 2 = _
    rw [kernel_eq_product_of_finrank_one L hL p p, pow_two]
  have hanti : Antitone (rankOneEnergyCharacter L hL) := by
    intro p q hpq
    rw [hr, hr]
    exact L.scaled_diagonal_antitone hpq
  rcases HTGeometry.antitone_nonnegative_monoidHom_eq_augmentation_or_rpow
    (rankOneEnergyCharacter L hL) hr0 hanti with hzero | ⟨α, hα, hpower⟩
  · refine Or.inl fun p hp => ?_
    have h := hzero p hp
    change (p : ℝ) * rankOneCharacter L hL p ^ 2 = 0 at h
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left (by positivity))
  · refine Or.inr ⟨(α + 1) / 2, by linarith only [hα], fun p => ?_⟩
    have hp : (0 : ℝ) < p := by exact_mod_cast p.property
    have hsq : rankOneCharacter L hL p ^ 2 = (p : ℝ) ^ (-(α + 1)) := by
      have h := hpower p
      change (p : ℝ) * rankOneCharacter L hL p ^ 2 = (p : ℝ) ^ (-α) at h
      apply (mul_left_cancel₀ hp.ne')
      rw [h]
      calc
        (p : ℝ) ^ (-α) = (p : ℝ) ^ ((1 : ℝ) + (-(α + 1))) := by congr 1; ring
        _ = (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (-(α + 1)) := Real.rpow_add hp _ _
        _ = _ := by rw [Real.rpow_one]
    apply (pow_left_inj₀ (abs_nonneg _) (Real.rpow_nonneg hp.le _) two_ne_zero).mp
    rw [sq_abs, hsq, ← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    congr 1
    ring

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.rankOneCharacter
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.rankOneCharacter_eq_augmentation_or_abs_rpow
end
end
