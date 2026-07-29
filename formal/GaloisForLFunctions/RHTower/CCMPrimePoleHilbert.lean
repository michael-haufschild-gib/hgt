import GaloisForLFunctions.RHTower.CCMPrimePoleLaplaceBoundary
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

/-!
# Hilbert realization of the normalized CCM prime-pole vectors

The exact scalar sequences from `CCMPrimePoleLaplaceBoundary` define honest
unit vectors in `ell^2(N)`.  This module proves summability from the geometric
pole model itself and then proves the Hilbert norm identity from the exact Gram
law.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower

theorem summable_ccmNormalizedPrimePoleSequence_star_mul_self
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Summable (fun k : ℕ =>
      star (ccmNormalizedPrimePoleSequence L n k) *
        ccmNormalizedPrimePoleSequence L n k) := by
  have hgeom : Summable (fun k : ℕ =>
      (star (ccmPrimePolePoint L n) * ccmPrimePolePoint L n) ^ k) :=
    summable_geometric_of_norm_lt_one
      (ccmPrimePolePoint_cross_norm_lt_one hL hL n n)
  let C : ℂ :=
    star ((Real.sqrt L : ℂ) * ccmPrimePoleCoefficient L n) *
      ((Real.sqrt L : ℂ) * ccmPrimePoleCoefficient L n)
  apply (hgeom.mul_left C).congr
  intro k
  simp only [ccmNormalizedPrimePoleSequence, ccmPrimePoleSequence, C,
    star_mul', star_pow]
  rw [mul_pow]
  ring

theorem summable_norm_sq_ccmNormalizedPrimePoleSequence
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    Summable (fun k : ℕ => ‖ccmNormalizedPrimePoleSequence L n k‖ ^ 2) := by
  have hs := (summable_ccmNormalizedPrimePoleSequence_star_mul_self hL n).norm
  simpa only [norm_mul, norm_star, pow_two] using hs

def ccmNormalizedPrimePoleVector (L : ℝ) (hL : 0 < L) (n : ℤ) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨ccmNormalizedPrimePoleSequence L n,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_ccmNormalizedPrimePoleSequence hL n)⟩

@[simp] theorem ccmNormalizedPrimePoleVector_apply
    (L : ℝ) (hL : 0 < L) (n : ℤ) (k : ℕ) :
    ccmNormalizedPrimePoleVector L hL n k =
      ccmNormalizedPrimePoleSequence L n k := rfl

theorem norm_sq_ccmNormalizedPrimePoleVector
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    ‖ccmNormalizedPrimePoleVector L hL n‖ ^ 2 = 1 := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  change (∑' k : ℕ, ‖ccmNormalizedPrimePoleSequence L n k‖ ^ 2) = 1
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  simp only [Complex.ofReal_one]
  calc
    (∑' k : ℕ, ((‖ccmNormalizedPrimePoleSequence L n k‖ ^ 2 : ℝ) : ℂ)) =
        ∑' k : ℕ, star (ccmNormalizedPrimePoleSequence L n k) *
          ccmNormalizedPrimePoleSequence L n k := by
      apply tsum_congr
      intro k
      rw [Complex.sq_norm, ← Complex.mul_conj]
      ac_rfl
    _ = 1 := ccmNormalizedPrimePoleSequence_self_tsum hL n

theorem norm_ccmNormalizedPrimePoleVector
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    ‖ccmNormalizedPrimePoleVector L hL n‖ = 1 := by
  nlinarith [norm_sq_ccmNormalizedPrimePoleVector hL n,
    norm_nonneg (ccmNormalizedPrimePoleVector L hL n)]

/-- The Hilbert inner product is the universal Cauchy kernel of the two
normalized prime clocks. -/
theorem inner_ccmNormalizedPrimePoleVector
    {Lp Lq : ℝ} (hp : 0 < Lp) (hq : 0 < Lq) (n r : ℤ) :
    inner ℂ (ccmNormalizedPrimePoleVector Lq hq r)
        (ccmNormalizedPrimePoleVector Lp hp n) =
      1 / (1 + 2 * Real.pi * Complex.I *
        ((r : ℝ) / Lq - (n : ℝ) / Lp)) := by
  rw [lp.inner_eq_tsum]
  simp only [ccmNormalizedPrimePoleVector_apply, RCLike.inner_apply]
  simpa only [starRingEnd_apply, mul_comm] using
    ccmNormalizedPrimePoleSequence_cross_tsum hp hq n r

/-- Exact cross-scale covariance law.  The squared Hilbert distance is the
rational Cauchy defect of the two prime-clock frequencies. -/
theorem norm_sub_sq_ccmNormalizedPrimePoleVector
    {Lp Lq : ℝ} (hp : 0 < Lp) (hq : 0 < Lq) (n r : ℤ) :
    ‖ccmNormalizedPrimePoleVector Lq hq r -
        ccmNormalizedPrimePoleVector Lp hp n‖ ^ 2 =
      2 * (2 * Real.pi * ((r : ℝ) / Lq - (n : ℝ) / Lp)) ^ 2 /
        (1 + (2 * Real.pi * ((r : ℝ) / Lq - (n : ℝ) / Lp)) ^ 2) := by
  let a : ℝ := 2 * Real.pi * ((r : ℝ) / Lq - (n : ℝ) / Lp)
  have hden : 0 < 1 + a ^ 2 := by positivity
  rw [norm_sub_sq (𝕜 := ℂ),
    norm_ccmNormalizedPrimePoleVector hq r,
    norm_ccmNormalizedPrimePoleVector hp n,
    inner_ccmNormalizedPrimePoleVector hp hq n r]
  have hkernel :
      (1 + 2 * Real.pi * Complex.I *
        ((r : ℝ) / Lq - (n : ℝ) / Lp) : ℂ) = 1 + Complex.I * a := by
    dsimp [a]
    push_cast
    ring
  rw [hkernel, one_div]
  change 1 ^ 2 - 2 * Complex.re ((1 + Complex.I * a)⁻¹) + 1 ^ 2 =
    2 * a ^ 2 / (1 + a ^ 2)
  rw [Complex.inv_re, Complex.normSq_apply]
  norm_num
  field_simp [hden.ne']
  ring

end RHTower
