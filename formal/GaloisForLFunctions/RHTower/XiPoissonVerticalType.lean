import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import GaloisForLFunctions.RHTower.XiGaussianHeatTraceCriterion
import GaloisForLFunctions.RHTower.XiCanonicalProduct
import GaloisForLFunctions.RHTower.CCMFirstClockVolterra

/-!
# The Poisson zero trace and its unconditional exponential type

The Gaussian trace `sum_q exp (-t * w q)`, `w = xiSpectralPoint ^ 2`, grows on vertical lines at the
rate `|Im w| = 2 g delta`, which is *linear in the height* `g` and therefore unbounded over the
divisor, while the decay rate `Re w = g^2 - delta^2` is quadratic in `g`.  The mismatch is what makes
its vertical envelope Gaussian rather than exponential.

Taking the square root of the spectral parameter repairs it exactly.  Let `xiPoissonPoint q` be the
spectral point reflected into the closed right half-plane, so that it is the principal square root of
`w q`.  Its real part is the height `|g|` and its imaginary part is `-+ delta`, which the critical
strip bounds by `1/2` **uniformly over the whole divisor and with no hypothesis on the zeros**.  Thus

* the vertical growth rates all lie in the fixed compact interval `[-1/2, 1/2]`;
* the trace obeys the unconditional envelope `‖Theta(tau)‖ <= exp (|Im tau| / 2) * Theta (Re tau)`;
* RH collapses the envelope to `‖Theta(tau)‖ <= Theta (Re tau)`.

So the Poisson trace is a function of exponential type at most `1/2` on every vertical line,
unconditionally, and RH is exactly the statement that it is bounded there.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## §1 The Poisson point: the principal square root of the squared spectral point -/

/-- The spectral point reflected into the closed right half-plane. -/
def xiPoissonPoint (q : XiZeroCopy) : ℂ :=
  if 0 ≤ (xiSpectralPoint q).re then xiSpectralPoint q else -(xiSpectralPoint q)

theorem xiPoissonPoint_sq (q : XiZeroCopy) :
    xiPoissonPoint q ^ 2 = xiSpectralPoint q ^ 2 := by
  unfold xiPoissonPoint
  split_ifs with h
  · rfl
  · ring

theorem xiPoissonPoint_re_eq_abs (q : XiZeroCopy) :
    (xiPoissonPoint q).re = |(xiSpectralPoint q).re| := by
  unfold xiPoissonPoint
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · rw [Complex.neg_re, abs_of_neg (not_le.mp h)]

theorem xiPoissonPoint_re_nonneg (q : XiZeroCopy) : 0 ≤ (xiPoissonPoint q).re := by
  rw [xiPoissonPoint_re_eq_abs]
  exact abs_nonneg _

/-- **The vertical growth rates are bounded by `1/2`, unconditionally.**  This is the property the
squared coordinate lacks: there the corresponding quantity is `2 g delta`, unbounded over the
divisor. -/
theorem abs_xiPoissonPoint_im_lt_half (q : XiZeroCopy) :
    |(xiPoissonPoint q).im| < 1 / 2 := by
  obtain ⟨h1, h2⟩ := xiSpectralPoint_im_mem_openHalf q
  unfold xiPoissonPoint
  split_ifs with h
  · rw [abs_lt]; constructor <;> linarith
  · rw [Complex.neg_im, abs_lt]; constructor <;> linarith

/-- Under RH the Poisson points are real, so all vertical growth rates vanish. -/
theorem xiPoissonPoint_im_eq_zero_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    (xiPoissonPoint q).im = 0 := by
  obtain ⟨x, hx⟩ := xiSpectralPoint_real_of_rh hRH q
  unfold xiPoissonPoint
  split_ifs with h <;> simp [hx]

/-! ## §2 The Poisson multiplier and its two envelopes -/

/-- The Poisson (Cauchy semigroup) multiplier at complex time. -/
def xiPoissonTerm (τ : ℂ) (q : XiZeroCopy) : ℂ :=
  Complex.exp (-τ * xiPoissonPoint q)

/-- The real-time Poisson weight. -/
def xiPoissonWeight (σ : ℝ) (q : XiZeroCopy) : ℝ :=
  Real.exp (-(σ * (xiPoissonPoint q).re))

theorem xiPoissonWeight_pos (σ : ℝ) (q : XiZeroCopy) : 0 < xiPoissonWeight σ q :=
  Real.exp_pos _

theorem norm_xiPoissonTerm (τ : ℂ) (q : XiZeroCopy) :
    ‖xiPoissonTerm τ q‖ =
      Real.exp (-(τ.re * (xiPoissonPoint q).re - τ.im * (xiPoissonPoint q).im)) := by
  rw [xiPoissonTerm, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- **The unconditional termwise envelope: exponential type at most `1/2`.** -/
theorem norm_xiPoissonTerm_le (τ : ℂ) (q : XiZeroCopy) :
    ‖xiPoissonTerm τ q‖ ≤ Real.exp (|τ.im| / 2) * xiPoissonWeight τ.re q := by
  rw [norm_xiPoissonTerm, xiPoissonWeight, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hhalf := abs_xiPoissonPoint_im_lt_half q
  have hkey : τ.im * (xiPoissonPoint q).im ≤ |τ.im| / 2 := by
    calc τ.im * (xiPoissonPoint q).im ≤ |τ.im * (xiPoissonPoint q).im| := le_abs_self _
      _ = |τ.im| * |(xiPoissonPoint q).im| := abs_mul _ _
      _ ≤ |τ.im| * (1 / 2) := mul_le_mul_of_nonneg_left hhalf.le (abs_nonneg _)
      _ = |τ.im| / 2 := by ring
  linarith

/-- Under RH the envelope collapses: the modulus on a vertical line equals the real-time weight. -/
theorem norm_xiPoissonTerm_eq_of_rh (hRH : RiemannHypothesis) (τ : ℂ) (q : XiZeroCopy) :
    ‖xiPoissonTerm τ q‖ = xiPoissonWeight τ.re q := by
  rw [norm_xiPoissonTerm, xiPoissonWeight, xiPoissonPoint_im_eq_zero_of_rh hRH q]
  congr 1
  ring

/-- An off-critical copy's Poisson multiplier is unbounded on every vertical line, at the rate given
by its own displacement. -/
theorem exists_norm_xiPoissonTerm_gt (σ : ℝ) {q : XiZeroCopy}
    (hq : (xiPoissonPoint q).im ≠ 0) (M : ℝ) :
    ∃ y : ℝ, M < ‖xiPoissonTerm (σ + y * I) q‖ := by
  set R := (xiPoissonPoint q).re with hR
  set J := (xiPoissonPoint q).im with hJ
  refine ⟨(M + σ * R) / J, ?_⟩
  have hre : (σ + ((M + σ * R) / J : ℝ) * I).re = σ := by simp
  have him : (σ + ((M + σ * R) / J : ℝ) * I).im = (M + σ * R) / J := by simp
  rw [norm_xiPoissonTerm, hre, him, ← hR, ← hJ]
  have hcancel : (M + σ * R) / J * J = M + σ * R := div_mul_cancel₀ _ hq
  have hexp : -(σ * R - (M + σ * R) / J * J) = M := by rw [hcancel]; ring
  rw [hexp]
  linarith [Real.add_one_le_exp M]

/-! ## §3 Summability of the Poisson weight -/

/-- The Poisson weight is summable on the divisor for every positive real time, by comparison with
the canonical-product exponent `sum 1 / ‖xiSpectralPoint‖ ^ 2`. -/
theorem summable_xiPoissonWeight {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun q : XiZeroCopy => xiPoissonWeight σ q) := by
  have hbase : Summable (fun q : XiZeroCopy =>
      2 * Real.exp (σ / 2) / σ ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2)) :=
    xiSpectralPoint_inv_sq_summable.mul_left _
  refine Summable.of_nonneg_of_le (fun q => (xiPoissonWeight_pos σ q).le) (fun q => ?_) hbase
  have hN : (4 : ℝ) < ‖xiSpectralPoint q‖ := four_lt_norm_xiSpectralPoint q
  have hNpos : 0 < ‖xiSpectralPoint q‖ := by linarith
  have him : |(xiSpectralPoint q).im| < 1 / 2 := by
    obtain ⟨h1, h2⟩ := xiSpectralPoint_im_mem_openHalf q
    rw [abs_lt]; constructor <;> linarith
  have hgap : ‖xiSpectralPoint q‖ - 1 / 2 < (xiPoissonPoint q).re := by
    have h := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
    rw [xiPoissonPoint_re_eq_abs]
    linarith
  have hstep2 : xiPoissonWeight σ q ≤
      Real.exp (σ / 2) * Real.exp (-(σ * ‖xiSpectralPoint q‖)) := by
    rw [xiPoissonWeight, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hmul : σ * (‖xiSpectralPoint q‖ - 1 / 2) < σ * (xiPoissonPoint q).re :=
      mul_lt_mul_of_pos_left hgap hσ
    have hexpand : σ * (‖xiSpectralPoint q‖ - 1 / 2) = σ * ‖xiSpectralPoint q‖ - σ / 2 := by
      ring
    rw [hexpand] at hmul
    linarith
  have hstep3 : Real.exp (-(σ * ‖xiSpectralPoint q‖)) ≤
      2 / (σ * ‖xiSpectralPoint q‖) ^ 2 := by
    have hxpos : 0 < σ * ‖xiSpectralPoint q‖ := mul_pos hσ hNpos
    have hq := Real.pow_div_factorial_le_exp (σ * ‖xiSpectralPoint q‖) hxpos.le 2
    norm_num [Nat.factorial] at hq
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (σ * ‖xiSpectralPoint q‖) ^ 2),
      Real.exp_neg, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _)]
    linarith
  calc xiPoissonWeight σ q
      ≤ Real.exp (σ / 2) * Real.exp (-(σ * ‖xiSpectralPoint q‖)) := hstep2
    _ ≤ Real.exp (σ / 2) * (2 / (σ * ‖xiSpectralPoint q‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hstep3 (Real.exp_pos _).le
    _ = 2 * Real.exp (σ / 2) / σ ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        field_simp

/-! ## §4 The Poisson trace and the vertical criterion -/

/-- The real-time Poisson zero trace. -/
def xiPoissonTraceReal (σ : ℝ) : ℝ := ∑' q : XiZeroCopy, xiPoissonWeight σ q

/-- The Poisson zero trace at complex time. -/
def xiPoissonTraceC (τ : ℂ) : ℂ := ∑' q : XiZeroCopy, xiPoissonTerm τ q

theorem summable_norm_xiPoissonTerm {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun q : XiZeroCopy => ‖xiPoissonTerm τ q‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => norm_xiPoissonTerm_le τ q)
    ((summable_xiPoissonWeight hτ).mul_left _)

/-- **The unconditional vertical envelope.**  On every vertical line of the open right half-plane the
Poisson zero trace has exponential type at most `1/2`, with no hypothesis on the zeros. -/
theorem norm_xiPoissonTraceC_le {τ : ℂ} (hτ : 0 < τ.re) :
    ‖xiPoissonTraceC τ‖ ≤ Real.exp (|τ.im| / 2) * xiPoissonTraceReal τ.re := by
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_xiPoissonTerm hτ)) ?_
  rw [xiPoissonTraceReal, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun q => norm_xiPoissonTerm_le τ q)
    (summable_norm_xiPoissonTerm hτ) ((summable_xiPoissonWeight hτ).mul_left _)

/-- **The vertical bound under RH.**  RH collapses the exponential-type envelope to boundedness. -/
theorem norm_xiPoissonTraceC_le_of_rh (hRH : RiemannHypothesis) {τ : ℂ} (hτ : 0 < τ.re) :
    ‖xiPoissonTraceC τ‖ ≤ xiPoissonTraceReal τ.re := by
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_xiPoissonTerm hτ)) ?_
  rw [xiPoissonTraceReal]
  exact le_of_eq (tsum_congr fun q => norm_xiPoissonTerm_eq_of_rh hRH τ q)

/-- **An exponential-type RH-disproof endpoint.**  One complex time at which the Poisson trace
exceeds its real-axis value refutes RH. -/
theorem not_riemannHypothesis_of_xiPoissonTraceReal_lt_norm {τ : ℂ} (hτ : 0 < τ.re)
    (h : xiPoissonTraceReal τ.re < ‖xiPoissonTraceC τ‖) :
    ¬ RiemannHypothesis := fun hRH =>
  absurd (norm_xiPoissonTraceC_le_of_rh hRH hτ) (not_le.mpr h)

end

end RHTower
