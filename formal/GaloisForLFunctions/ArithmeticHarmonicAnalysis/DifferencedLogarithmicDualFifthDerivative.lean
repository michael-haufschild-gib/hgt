import GaloisForLFunctions.RHTower.ZetaDifferencedDualPhase

/-! # The fifth derivative of the differenced logarithmic dual phase

The inverse stationary point gives a positive fifth derivative comparable to
`q/u⁴`. This is the derivative input for the next logarithmic block estimate.
-/

noncomputable section
open RHTower

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Fifth derivative of the negated dual phase, with `u=k-ν` and `q=√(Th/u+h²/4)`. -/
def differencedDualFifth (T h k ν : ℝ) : ℝ :=
  12 * (T * h) / ((k - ν) ^ 5 * dualQ T h (k - ν))
    - 9 * (T * h) ^ 2 / ((k - ν) ^ 6 * dualQ T h (k - ν) ^ 3)
    + 9 * (T * h) ^ 3 / (2 * (k - ν) ^ 7 * dualQ T h (k - ν) ^ 5)
    - 15 * (T * h) ^ 4 / (16 * (k - ν) ^ 8 * dualQ T h (k - ν) ^ 7)

theorem hasDerivAt_dualChain_four {T h k ν : ℝ}
    (hT : 0 < T) (hh : 0 < h) (hu : 0 < k - ν) :
    HasDerivAt (dualChain T h k 4) (differencedDualFifth T h k ν) ν := by
  have hq := dualQ_pos hT hh hu
  have hQ := hasDerivAt_dualQ_sub hT hh hu
  have hU : HasDerivAt (fun x : ℝ => k - x) (-1) ν := by
    simpa only [neg_one_mul] using (hasDerivAt_id' ν).const_sub k
  have h1 := (hU.fun_pow 4).mul hQ
  have h2 := ((hU.fun_pow 5).const_mul 2).mul (hQ.fun_pow 3)
  have h3 := ((hU.fun_pow 6).const_mul 8).mul (hQ.fun_pow 5)
  have hd := (((hasDerivAt_const ν (3 * (T * h))).div h1 (by
    change (k - ν) ^ 4 * dualQ T h (k - ν) ≠ 0
    positivity)).sub
    ((hasDerivAt_const ν (3 * (T * h) ^ 2)).div h2 (by
      change 2 * (k - ν) ^ 5 * dualQ T h (k - ν) ^ 3 ≠ 0
      positivity))).add
    ((hasDerivAt_const ν (3 * (T * h) ^ 3)).div h3 (by
      change 8 * (k - ν) ^ 6 * dualQ T h (k - ν) ^ 5 ≠ 0
      positivity))
  refine hd.congr_deriv ?_
  simp only [differencedDualFifth]
  norm_num
  field_simp [hu.ne', hq.ne']
  ring

/-- The existing dual derivative chain, extended through its fifth derivative. -/
def fifthDualChain (T h k : ℝ) (i : ℕ) : ℝ → ℝ :=
  if i = 5 then differencedDualFifth T h k else dualChain T h k i

theorem hasDerivAt_fifthDualChain {T h k ν : ℝ}
    (hT : 0 < T) (hh : 0 < h) (hu : 0 < k - ν) {i : ℕ} (hi : i < 5) :
    HasDerivAt (fifthDualChain T h k i) (fifthDualChain T h k (i + 1) ν) ν := by
  by_cases h4 : i = 4
  · subst i
    change HasDerivAt (dualChain T h k 4) (differencedDualFifth T h k ν) ν
    exact hasDerivAt_dualChain_four hT hh hu
  · have hi4 : i < 4 := by omega
    simpa only [fifthDualChain, if_neg (by omega : i ≠ 5),
      if_neg (by omega : i + 1 ≠ 5)] using hasDerivAt_dualChain hT hh hu i hi4

/-- Factoring out `q/u⁴` leaves a polynomial in the bounded ratio `Th/(u q²)`. -/
theorem differencedDualFifth_eq {T h k ν : ℝ}
    (hT : 0 < T) (hh : 0 < h) (hu : 0 < k - ν) :
    differencedDualFifth T h k ν = dualQ T h (k - ν) / (k - ν) ^ 4 *
      (12 * (T * h / ((k - ν) * dualQ T h (k - ν) ^ 2))
        - 9 * (T * h / ((k - ν) * dualQ T h (k - ν) ^ 2)) ^ 2
        + 9 / 2 * (T * h / ((k - ν) * dualQ T h (k - ν) ^ 2)) ^ 3
        - 15 / 16 * (T * h / ((k - ν) * dualQ T h (k - ν) ^ 2)) ^ 4) := by
  have hq := dualQ_pos hT hh hu
  unfold differencedDualFifth
  field_simp [hu.ne', hq.ne']

private theorem fifthRatioPolynomial_bounds {r : ℝ} (hl : 4 / 5 ≤ r) (hr : r ≤ 1) :
    1 ≤ 12 * r - 9 * r ^ 2 + 9 / 2 * r ^ 3 - 15 / 16 * r ^ 4 ∧
      12 * r - 9 * r ^ 2 + 9 / 2 * r ^ 3 - 15 / 16 * r ^ 4 ≤ 12 := by
  have h0 : 0 ≤ r := by linarith only [hl]
  have h2 : r ^ 2 ≤ r := by
    nlinarith only [mul_le_mul_of_nonneg_left hr h0]
  have h3 : r ^ 3 ≤ r ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hr (sq_nonneg r)]
  have h4 : r ^ 4 ≤ r := by
    have h43 : r ^ 4 ≤ r ^ 3 := by
      nlinarith only [mul_le_mul_of_nonneg_left hr (pow_nonneg h0 3)]
    exact h43.trans (h3.trans h2)
  constructor
  · nlinarith only [hl, h2, h4, pow_nonneg h0 3]
  · nlinarith only [hr, h3, sq_nonneg r, pow_nonneg h0 4]

/-- On the entire dual interval, the fifth derivative is positive and comparable to `q/u⁴`. -/
theorem differencedDualFifth_bounds {T h k ν : ℝ}
    (hT : 0 < T) (hh : 0 < h) (hu : 0 < k - ν) (hsmall : h * (k - ν) ≤ T) :
    dualQ T h (k - ν) / (k - ν) ^ 4 ≤ differencedDualFifth T h k ν ∧
      differencedDualFifth T h k ν ≤ 12 * (dualQ T h (k - ν) / (k - ν) ^ 4) := by
  have hq := dualQ_pos hT hh hu
  have hq2 := dualQ_sq hT.le hh.le hu
  let u := k - ν
  let q := dualQ T h u
  let r := T * h / (u * q ^ 2)
  have he : u * q ^ 2 = T * h + u * h ^ 2 / 4 := by
    dsimp only [u, q]
    rw [hq2]
    field_simp [hu.ne']
  have hden : 0 < u * q ^ 2 := by dsimp only [u, q]; positivity
  have hr1 : r ≤ 1 := by
    rw [show r = T * h / (u * q ^ 2) from rfl, div_le_one hden, he]
    exact le_add_of_nonneg_right (by dsimp only [u]; positivity)
  have hsmall' : u * h ^ 2 ≤ T * h := by
    dsimp only [u]
    nlinarith only [mul_le_mul_of_nonneg_right hsmall hh.le]
  have hr45 : 4 / 5 ≤ r := by
    rw [show r = T * h / (u * q ^ 2) from rfl, le_div_iff₀ hden, he]
    linarith only [hsmall']
  have hp := fifthRatioPolynomial_bounds hr45 hr1
  have hb : 0 ≤ q / u ^ 4 := by dsimp only [q, u]; positivity
  rw [differencedDualFifth_eq hT hh hu]
  constructor
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hp.1 hb
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp.2 hb

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.hasDerivAt_dualChain_four
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.hasDerivAt_fifthDualChain
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.differencedDualFifth_bounds
