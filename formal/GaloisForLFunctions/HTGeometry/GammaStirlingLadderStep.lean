import GaloisForLFunctions.HTGeometry.GammaStirlingLadderPolynomial
import GaloisForLFunctions.HTGeometry.PolynomialVanishingOrderBound
import GaloisForLFunctions.HTGeometry.GammaStirlingCubicLog

/-!
# The Stirling ladder at every finite order: the one-step difference

The ladder defect of order `M` is `g_M z = ψ z - log z + ∑_{m<M} c_m z^{-(m+1)}` with `c_m` the
forced ladder coefficients of `GammaStirlingLadderPolynomial`.

Its one-step difference splits, after the substitution `u = 1/z`, into

* a *rational* part `P_M(u)/(1+u)^M`, which vanishes to order `M+2` because `X^(M+2) ∣ P_M`, and
* a *transcendental* part `(u - T_M(u)) - log(1+u)`, which is exactly the tail of the logarithmic
  Taylor series and is `O(‖u‖^{M+2})` by the uniform Taylor bound.

Both estimates are already available, so the step bound holds at every order with no case analysis.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Polynomial

noncomputable section

/-- The degree-`M+1` truncation of `u - log(1+u)`. -/
def taylorTail (M : ℕ) (u : ℂ) : ℂ :=
  ∑ i ∈ Finset.range M, (-1 : ℂ) ^ (i + 2) * u ^ (i + 2) / ((i : ℂ) + 2)

/-- The rational part of the one-step difference of the order-`M` ladder defect. -/
def ladderRatPart (M : ℕ) (u : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, ladderCoeff m * u ^ (m + 1) * (((1 + u) ^ (m + 1))⁻¹ - 1)

theorem taylorTail_succ (M : ℕ) (u : ℂ) :
    taylorTail (M + 1) u = taylorTail M u + (-1 : ℂ) ^ (M + 2) * u ^ (M + 2) / ((M : ℂ) + 2) :=
  Finset.sum_range_succ _ _

theorem ladderRatPart_succ (M : ℕ) (u : ℂ) :
    ladderRatPart (M + 1) u
      = ladderRatPart M u + ladderCoeff M * u ^ (M + 1) * (((1 + u) ^ (M + 1))⁻¹ - 1) :=
  Finset.sum_range_succ _ _

/-- **The ladder polynomial is the cleared numerator of the one-step difference.** -/
theorem ladderPoly_eval : ∀ (M : ℕ) {u : ℂ}, 1 + u ≠ 0 →
    (ladderPoly M).eval u = (1 + u) ^ M * (ladderRatPart M u + taylorTail M u) := by
  intro M
  induction M with
  | zero =>
      intro u _
      simp [ladderPoly, ladderRatPart, taylorTail]
  | succ M ih =>
      intro u hu
      have hp : ((1 : ℂ) + u) ^ (M + 1) ≠ 0 := pow_ne_zero _ hu
      have hsign : ((-1 : ℂ)) ^ (M + 2) = (-1) ^ M := by rw [pow_add]; norm_num
      rw [ladderPoly_succ]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_sub]
      rw [ih hu, taylorTail_succ, ladderRatPart_succ, hsign]
      field_simp
      ring

/-- The order-`M` ladder defect of the digamma function. -/
def ladderDefect (M : ℕ) (z : ℂ) : ℂ :=
  Complex.digamma z - Complex.log z + ∑ m ∈ Finset.range M, ladderCoeff m / z ^ (m + 1)

theorem ladderDefect_step {M : ℕ} {z : ℂ} (hz : 0 < z.re) :
    ladderDefect M (z + 1) - ladderDefect M z
      = ladderRatPart M (1 / z) + (1 / z - Complex.log (1 + 1 / z)) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hre : (z + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re] at hre
    linarith
  have hdig : Complex.digamma (z + 1) = Complex.digamma z + z⁻¹ := by
    refine Complex.digamma_apply_add_one z fun m => ?_
    intro h
    rw [h] at hz
    simp only [Complex.neg_re, Complex.natCast_re] at hz
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hu1 : (1 : ℂ) + 1 / z = (z + 1) / z := by field_simp
  have hterm : ∀ m : ℕ,
      ladderCoeff m / (z + 1) ^ (m + 1) - ladderCoeff m / z ^ (m + 1)
        = ladderCoeff m * (1 / z) ^ (m + 1) * ((((1 : ℂ) + 1 / z) ^ (m + 1))⁻¹ - 1) := by
    intro m
    rw [hu1, div_pow, div_pow, one_pow]
    have hzp : z ^ (m + 1) ≠ 0 := pow_ne_zero _ hz0
    have hz1p : (z + 1) ^ (m + 1) ≠ 0 := pow_ne_zero _ hz1
    field_simp
  have hsum : (∑ m ∈ Finset.range M, ladderCoeff m / (z + 1) ^ (m + 1))
      - (∑ m ∈ Finset.range M, ladderCoeff m / z ^ (m + 1))
      = ladderRatPart M (1 / z) := by
    rw [ladderRatPart, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => hterm m
  have hlog := log_add_one_sub_log hz
  have hinv : z⁻¹ = 1 / z := by rw [one_div]
  rw [ladderDefect, ladderDefect, hdig, hinv]
  rw [← hsum, ← hlog]
  ring


/-- `u - T_M(u)` is exactly the degree-`M+1` Taylor polynomial of `log(1+u)`. -/
theorem taylorTail_eq (M : ℕ) (u : ℂ) :
    u - taylorTail M u = ∑ j ∈ Finset.range (M + 2), (-1 : ℂ) ^ (j + 1) * u ^ j / (j : ℂ) := by
  induction M with
  | zero => simp [taylorTail, Finset.sum_range_succ]
  | succ M ih =>
      rw [taylorTail_succ]
      rw [show M + 1 + 2 = (M + 2) + 1 from rfl, Finset.sum_range_succ, ← ih]
      have hs : ((-1 : ℂ)) ^ (M + 2 + 1) = -((-1 : ℂ) ^ (M + 2)) := by
        rw [pow_succ]; ring
      rw [hs]
      push_cast
      ring

/-- **The one-step difference of the order-`M` ladder defect is `O(‖z‖^{-(M+2)})`.** -/
theorem exists_norm_ladderDefect_step_le (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, 0 < z.re → 2 ≤ ‖z‖ →
      ‖ladderDefect M (z + 1) - ladderDefect M z‖ ≤ K / ‖z‖ ^ (M + 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_polyEval_div_pow_le_of_dvd (X_pow_dvd_ladderPoly M) M
  refine ⟨C + 1, by linarith, fun z hz h2 => ?_⟩
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at h2; simp at h2; linarith
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hre : (z + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, Complex.one_re] at hre
    linarith
  set u : ℂ := 1 / z with hudef
  have hunorm : ‖u‖ = 1 / ‖z‖ := by rw [hudef, norm_div, norm_one]
  have huhalf : ‖u‖ ≤ 1 / 2 := by
    rw [hunorm, div_le_div_iff₀ hzpos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hu1 : (1 : ℂ) + u ≠ 0 := by
    rw [hudef]
    have : (1 : ℂ) + 1 / z = (z + 1) / z := by field_simp
    rw [this]
    exact div_ne_zero hz1 hz0
  have hsplit : ladderDefect M (z + 1) - ladderDefect M z
      = (ladderPoly M).eval u / (1 + u) ^ M
        + ((u - taylorTail M u) - Complex.log (1 + u)) := by
    rw [ladderDefect_step hz, ← hudef, ladderPoly_eval M hu1]
    have hp : ((1 : ℂ) + u) ^ M ≠ 0 := pow_ne_zero _ hu1
    field_simp
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hb1 : ‖(ladderPoly M).eval u / (1 + u) ^ M‖ ≤ C * ‖u‖ ^ (M + 2) := hC u huhalf
  have hb2 : ‖(u - taylorTail M u) - Complex.log (1 + u)‖ ≤ ‖u‖ ^ (M + 2) := by
    rw [taylorTail_eq, ← norm_neg]
    have : -((∑ j ∈ Finset.range (M + 2), (-1 : ℂ) ^ (j + 1) * u ^ j / (j : ℂ))
        - Complex.log (1 + u))
        = Complex.log (1 + u) - ∑ j ∈ Finset.range (M + 2), (-1 : ℂ) ^ (j + 1) * u ^ j / (j : ℂ) := by
      ring
    rw [this]
    exact norm_log_one_add_sub_taylor_le' huhalf (by omega)
  have hpow : ‖u‖ ^ (M + 2) = 1 / ‖z‖ ^ (M + 2) := by
    rw [hunorm, div_pow, one_pow]
  rw [hpow] at hb1 hb2
  have : C * (1 / ‖z‖ ^ (M + 2)) + 1 / ‖z‖ ^ (M + 2) = (C + 1) / ‖z‖ ^ (M + 2) := by
    field_simp
  linarith [hb1, hb2, this.symm.le, this.le]

end

end GaloisForLFunctions.HTGeometry
