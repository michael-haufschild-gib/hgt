import GaloisForLFunctions.RHTower.XiPhysicalPrimeEndpointRadical
import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare

/-!
# Wiener charge law for physical prime endpoints

The signed endpoint jumps of a finite physical prime aperture packet form a finite atomic measure
on the aperture circle.  Its `n`th moment is the aperture-character rate times the exact physical
FCRJ character amplitude.  Finite atomic Wiener theory therefore computes the Cesaro mean square
of these differentiated amplitudes as the exact sum of squared endpoint jumps.

Every nonempty active packet has positive jump-square mass.  Consequently its differentiated
character amplitudes cannot converge to zero, or equivalently its raw amplitudes cannot be
uniformly `o(1/n)` along all positive integer aperture frequencies.  This closes rapid Fourier-tail
disposal as an FCRJ provider while leaving the genuinely arithmetic total-energy upper bound open.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The `n`th unit-circle moment of the signed physical prime endpoint measure. -/
def xiPhysicalPrimeLogEndpointCircleMoment
    (P : Finset Nat.Primes) (A m k : ℝ) (n : ℕ) : ℂ :=
  ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
    xiPhysicalPrimeLogEndpointCircleJump P A m k x * fourier 1 x ^ n

/-- Powers of the fundamental aperture character are the nonnegative integer characters. -/
theorem fourier_one_pow_nat
    {A : ℝ} (x : AddCircle A) (n : ℕ) :
    fourier 1 x ^ n = fourier (n : ℤ) x := by
  simp [fourier_apply, AddCircle.toCircle_nsmul]

private theorem fourier_one_injective
    {A : ℝ} (hA : 0 < A) :
    Function.Injective (fun x : AddCircle A => fourier 1 x) := by
  intro x y hxy
  change fourier 1 x = fourier 1 y at hxy
  rw [fourier_one, fourier_one] at hxy
  apply AddCircle.injective_toCircle hA.ne'
  exact Subtype.ext hxy

/-- Exact finite atomic Wiener law for the signed physical endpoint measure. -/
theorem tendsto_xiPhysicalPrimeLogEndpointCircleMoment_cesaro_norm_sq
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k n‖ ^ (2 : ℕ))
      atTop
      (nhds (∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
        ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ (2 : ℕ))) := by
  simpa only [xiPhysicalPrimeLogEndpointCircleMoment,
    finiteExponentialPencil] using
    (tendsto_finiteExponentialPencil_cesaro_norm_sq
      (xiPhysicalPrimeLogEndpointNodeSet P A m k)
      (xiPhysicalPrimeLogEndpointCircleJump P A m k)
      (fun x : AddCircle A => fourier 1 x)
      (by intro x hx; simp)
      (fourier_one_injective hA).injOn)

/-- Every positive endpoint moment is the character rate times the exact FCRJ amplitude. -/
theorem xiPhysicalPrimeLogEndpointCircleMoment_eq_rate_mul_amplitude
    {P : Finset Nat.Primes} {A m k : ℝ} (hA : 0 < A)
    {n : ℕ} (hn : n ≠ 0)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    xiPhysicalPrimeLogEndpointCircleMoment P A m k n =
      xiPhysicalApertureCharacterRate A (n : ℤ) *
        xiPhysicalPrimeLogCharacterAmplitude P A (n : ℤ) m k := by
  rw [xiPhysicalPrimeLogEndpointCircleMoment]
  simp_rw [fourier_one_pow_nat]
  exact sum_endpointCircleJump_mul_fourier hA (by exact_mod_cast hn) hactive

/-- Every nonempty active physical packet has strictly positive endpoint jump-square mass. -/
theorem sum_normSq_xiPhysicalPrimeLogEndpointCircleJump_pos
    {P : Finset Nat.Primes} {A m k : ℝ}
    (hP : P.Nonempty)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth0 : 0 < k - m) (hwidthA : k - m < A) :
    0 < ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
      ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ (2 : ℕ) := by
  have hA : 0 < A := hwidth0.trans hwidthA
  rcases exists_xiPhysicalPrimeLogCharacterAmplitude_ne_zero
      hP hactive hwidth0 hwidthA with ⟨n, hn, hamp⟩
  have hsum :
      (∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
        xiPhysicalPrimeLogEndpointCircleJump P A m k x * fourier n x) ≠ 0 := by
    rw [sum_endpointCircleJump_mul_fourier hA hn hactive]
    exact mul_ne_zero (xiPhysicalApertureCharacterRate_ne_zero hA hn) hamp
  have hexists : ∃ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
      xiPhysicalPrimeLogEndpointCircleJump P A m k x ≠ 0 := by
    by_contra h
    push Not at h
    apply hsum
    apply Finset.sum_eq_zero
    intro x hx
    rw [h x hx, zero_mul]
  rcases hexists with ⟨x, hx, hjump⟩
  have hle : ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ (2 : ℕ) ≤
      ∑ y ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
        ‖xiPhysicalPrimeLogEndpointCircleJump P A m k y‖ ^ (2 : ℕ) := by
    exact Finset.single_le_sum
      (fun y hy => sq_nonneg ‖xiPhysicalPrimeLogEndpointCircleJump P A m k y‖) hx
  exact lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hjump)) hle

/-- Endpoint moments of a nonempty active packet cannot tend to zero: their Cesaro mean square
has the strictly positive atomic jump mass as limit. -/
theorem not_tendsto_xiPhysicalPrimeLogEndpointCircleMoment_zero
    {P : Finset Nat.Primes} {A m k : ℝ}
    (hP : P.Nonempty)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth0 : 0 < k - m) (hwidthA : k - m < A) :
    ¬ Tendsto (fun n : ℕ => xiPhysicalPrimeLogEndpointCircleMoment P A m k n)
      atTop (nhds 0) := by
  intro hzero
  have hnorm : Tendsto
      (fun n : ℕ => ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k n‖ ^ (2 : ℕ))
      atTop (nhds 0) := by
    have hnorm' := Complex.continuous_normSq.continuousAt.tendsto.comp hzero
    have hnorm'' : Tendsto (fun n : ℕ =>
        Complex.normSq (xiPhysicalPrimeLogEndpointCircleMoment P A m k n))
        atTop (nhds (Complex.normSq 0)) :=
      hnorm'.congr' (Eventually.of_forall fun _ => rfl)
    simpa only [Complex.sq_norm, Complex.normSq_zero] using hnorm''
  have hcesaro := hnorm.cesaro
  have hA : 0 < A := hwidth0.trans hwidthA
  have hwiener :=
    tendsto_xiPhysicalPrimeLogEndpointCircleMoment_cesaro_norm_sq P hA m k
  have hmassZero :
      (∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
        ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ (2 : ℕ)) = 0 :=
    tendsto_nhds_unique hwiener hcesaro
  have hmassPos := sum_normSq_xiPhysicalPrimeLogEndpointCircleJump_pos
    hP hactive hwidth0 hwidthA
  linarith

/-- Equivalently, differentiated positive character amplitudes never converge to zero.  Thus the
physical FCRJ amplitudes are not `o(1/n)` along all integer aperture frequencies. -/
theorem not_tendsto_xiPhysicalPrimeLog_rate_mul_characterAmplitude_zero
    {P : Finset Nat.Primes} {A m k : ℝ}
    (hP : P.Nonempty)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hwidth0 : 0 < k - m) (hwidthA : k - m < A) :
    ¬ Tendsto (fun n : ℕ =>
        xiPhysicalApertureCharacterRate A (n : ℤ) *
          xiPhysicalPrimeLogCharacterAmplitude P A (n : ℤ) m k)
      atTop (nhds 0) := by
  intro hzero
  apply not_tendsto_xiPhysicalPrimeLogEndpointCircleMoment_zero
    hP hactive hwidth0 hwidthA
  apply hzero.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  exact (xiPhysicalPrimeLogEndpointCircleMoment_eq_rate_mul_amplitude
    (hwidth0.trans hwidthA) (Nat.ne_zero_of_lt hn) hactive).symm

end

end RHTower
