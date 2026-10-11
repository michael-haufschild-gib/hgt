import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarParitySourceProfile

/-!
# Positive spatial prime jumps of the actual odd Weil pole source

The reflected odd prime–Gamma source has a continuous Gamma/radius core and
finite von Mangoldt atoms. Each prime-power atom makes an upward jump at both
reflected spatial sites. Collisions add with positive multiplicity.
-/

open Complex MeasureTheory Set Filter
open scoped Topology BigOperators
noncomputable section
namespace RHTower

private def oddVisiblePrimes (a : SuzukiPositiveAperture) : Finset ℕ :=
  Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊

/-- Continuous part of the odd physical source on the open aperture. -/
def ccmPolarOddSourceCore (a : SuzukiPositiveAperture) (x : ℝ) : ℝ :=
  Real.exp (x / 2) * (ccmGammaPolarBoundary (a.1-x) (a.1+x) + (a.1+x)) -
  Real.exp (-x / 2) * (ccmGammaPolarBoundary (a.1+x) (a.1-x) + (a.1-x))

/-- A single visible von Mangoldt atom in the odd source profile. -/
def ccmPolarOddSourcePrimeAtom (a : SuzukiPositiveAperture) (n : ℕ) (x : ℝ) : ℝ :=
  -ArithmeticFunction.vonMangoldt n *
    ((Real.exp (x / 2) - Real.exp (-x / 2) / n) *
      (if Real.log n ≤ a.1-x then 1 else 0) +
     (Real.exp (x / 2) / n - Real.exp (-x / 2)) *
      (if Real.log n ≤ a.1+x then 1 else 0))

private theorem sum_log_cutoff (a : SuzukiPositiveAperture) (f : ℕ → ℝ)
    {y : ℝ} (hy : y ≤ 2 * a.1) :
    (∑ n ∈ oddVisiblePrimes a, if Real.log n ≤ y then f n else 0) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp y⌋₊, f n := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  by_cases hn : 2 ≤ n
  · have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have heq : Real.log n ≤ y ↔ n ≤ ⌊Real.exp y⌋₊ :=
      (Real.log_le_iff_le_exp hnR).trans (Nat.le_floor_iff (Real.exp_pos y).le).symm
    have hfloor := Nat.floor_mono (Real.exp_le_exp.mpr hy)
    rw [heq]
    simp only [oddVisiblePrimes, Finset.mem_Icc] at *
    omega
  · simp [hn, oddVisiblePrimes]

private theorem psi_eq_sum_from_two (X : ℝ) :
    Chebyshev.psi X = ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n := by
  rw [Chebyshev.psi_eq_sum_Icc]
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨Nat.zero_le _, hn.2⟩
  · intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl <;> simp

/-- Full odd source equals continuous core plus all finite visible prime atoms. -/
theorem ccmPolarOddSource_eq_core_add_atoms (a : SuzukiPositiveAperture) {x : ℝ}
    (hx : x ∈ Ioo (-a.1) a.1) :
    (ccmPolarParityBoundaryProfile a (-1) x).re =
      ccmPolarOddSourceCore a x +
        ∑ n ∈ oddVisiblePrimes a, ccmPolarOddSourcePrimeAtom a n x := by
  classical
  have hpR : Chebyshev.psi (Real.exp (a.1-x)) =
      ∑ n ∈ oddVisiblePrimes a,
        if Real.log n ≤ a.1-x then ArithmeticFunction.vonMangoldt n else 0 := by
    rw [psi_eq_sum_from_two]
    exact (sum_log_cutoff a _ (by linarith [hx.1])).symm
  have hpL : Chebyshev.psi (Real.exp (a.1+x)) =
      ∑ n ∈ oddVisiblePrimes a,
        if Real.log n ≤ a.1+x then ArithmeticFunction.vonMangoldt n else 0 := by
    rw [psi_eq_sum_from_two]
    exact (sum_log_cutoff a _ (by linarith [hx.2])).symm
  have hsR : ccmReciprocalMangoldtCumulative (Real.exp (a.1-x)) =
      ∑ n ∈ oddVisiblePrimes a,
        if Real.log n ≤ a.1-x then ArithmeticFunction.vonMangoldt n / n else 0 := by
    unfold ccmReciprocalMangoldtCumulative
    exact (sum_log_cutoff a _ (by linarith [hx.1])).symm
  have hsL : ccmReciprocalMangoldtCumulative (Real.exp (a.1+x)) =
      ∑ n ∈ oddVisiblePrimes a,
        if Real.log n ≤ a.1+x then ArithmeticFunction.vonMangoldt n / n else 0 := by
    unfold ccmReciprocalMangoldtCumulative
    exact (sum_log_cutoff a _ (by linarith [hx.2])).symm
  have hre : (ccmPolarParityBoundaryProfile a (-1) x).re =
      (ccmPolarBoundaryArithmeticProfile a x).re -
        (ccmPolarBoundaryArithmeticProfile a (-x)).re := by
    unfold ccmPolarParityBoundaryProfile ccmPolarBoundaryArithmeticProfile
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
      neg_mul, one_mul, zero_mul, mul_zero, sub_zero]
    ring
  rw [hre]
  unfold ccmPolarBoundaryArithmeticProfile ccmReciprocalMangoldtError
    ccmPolarOddSourceCore ccmPolarOddSourcePrimeAtom
  simp only [Complex.ofReal_re, neg_neg, sub_neg_eq_add, hpR, hpL, hsR, hsL]
  trace_state
  sorry

end RHTower
