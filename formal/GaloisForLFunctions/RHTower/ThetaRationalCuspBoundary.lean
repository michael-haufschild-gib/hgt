import GaloisForLFunctions.RHTower.QuadraticGaussSumFourthPower
import GaloisForLFunctions.RHTower.HalfWeightThetaMultiplier
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspComplexStrip

/-!
# Rational-cusp boundary law of the completed theta source

With `ϑ(y) = Σ_{n ∈ ℤ} e^{-π n² y}` and `κ(y) = y^{5/4}(2yϑ''(y) + 3ϑ'(y))`, the completed theta
source is `k(z) = κ(e^{2z})` on its strip `|Im z| < π/4`.

At `y₀ = 2ip/q`, residue-class Poisson summation (`HalfWeight.theta_cusp`), continued to complex
displacements by the identity theorem, gives
`ϑ(y₀ + η) = q⁻¹ η^{-1/2} Σ_ℓ G_ℓ e^{-πℓ²/(q²η)}`.  The `ℓ = 0` term `q⁻¹ G η^{-1/2}` produces
exactly `(3G/2q) y₀ ε^{-5/2}` in `2yϑ'' + 3ϑ'`, the `ε^{-3/2}` terms cancelling, and Cauchy
estimates on the disks `|η - ε| ≤ ε/2` make the remainder exponentially small.  Hence

`ε^{5/2} κ(y₀ + ε) → (3 G_{p,q}/(2q)) y₀^{9/4}`,   `G_{p,q} = Σ_{r mod q} e^{-2πi p r²/q}`.

For odd `q` coprime to `p`, `|G_{p,q}| = √q`, so the source is unbounded at a dense set of
boundary points and the strip is a natural boundary.  The fourth power of the amplitude carries the
arithmetic charge `{1, 0, -4}` of `q` modulo four; at `q ≡ 2 (mod 4)`, e.g. `y₀ = i`, the source
tends to zero.
-/
open Complex Filter Topology Set

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower.HalfWeight

/-! ## The Jacobi theta sum and the boundary source -/

/-- The Jacobi theta sum `ϑ(y) = Σ_{n ∈ ℤ} e^{-π n² y}`. -/
def jacobiThetaSum (y : ℂ) : ℂ := ∑' n : ℤ, cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * y)

/-- Its first derivative series `Σ -π n² e^{-π n² y}`. -/
def jacobiThetaSumOne (y : ℂ) : ℂ :=
  ∑' n : ℤ, -((Real.pi : ℂ) * (n : ℂ) ^ 2) * cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * y)

/-- Its second derivative series `Σ π² n⁴ e^{-π n² y}`. -/
def jacobiThetaSumTwo (y : ℂ) : ℂ :=
  ∑' n : ℤ, ((Real.pi : ℂ) * (n : ℂ) ^ 2) ^ 2 * cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * y)

theorem jacobiThetaSum_eq_theta (y : ℂ) : jacobiThetaSum y = theta (I * y / 2) := by
  rw [theta_eq_tsum]
  unfold jacobiThetaSum
  congr 1; funext n; congr 1; ring_nf; rw [I_sq]; ring

theorem norm_cexp_neg_pi_sq (n : ℤ) (y : ℂ) :
    ‖cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * y)‖ = Real.exp (-(Real.pi * (n : ℝ) ^ 2 * y.re)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, ← Complex.ofReal_intCast, pow_two]

theorem summable_int_pow_mul_exp_neg_sq (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => |(n : ℝ)| ^ k * Real.exp (-(c * (n : ℝ) ^ 2))) := by
  have hN := summable_pow_mul_exp_neg_nat_sq k hc
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hN.congr fun n => ?_
    simp [neg_mul]
  · refine hN.congr fun n => ?_
    simp [neg_mul]

/-- The theta series and its termwise derivatives converge normally on `Re y ≥ δ > 0`. -/
theorem norm_pow_mul_cexp_le (k : ℕ) {δ : ℝ} {y : ℂ} (hy : δ ≤ y.re) (n : ℤ) :
    ‖((Real.pi : ℂ) * (n : ℂ) ^ 2) ^ k * cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * y)‖ ≤
      Real.pi ^ k * (|(n : ℝ)| ^ (2 * k) * Real.exp (-((Real.pi * δ) * (n : ℝ) ^ 2))) := by
  rw [norm_mul, norm_cexp_neg_pi_sq, norm_pow, norm_mul, Complex.norm_real, norm_pow,
    Complex.norm_intCast, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have h1 : Real.exp (-(Real.pi * (n : ℝ) ^ 2 * y.re)) ≤ Real.exp (-((Real.pi * δ) * (n : ℝ) ^ 2)) := by
    refine Real.exp_le_exp.mpr ?_
    have := sq_nonneg (n : ℝ)
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le this) (sub_nonneg.mpr hy)]
  calc (Real.pi * |(n : ℝ)| ^ 2) ^ k * Real.exp (-(Real.pi * (n : ℝ) ^ 2 * y.re))
      ≤ (Real.pi * |(n : ℝ)| ^ 2) ^ k * Real.exp (-((Real.pi * δ) * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

theorem summable_theta_terms_re {k : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℤ => Real.pi ^ k * (|(n : ℝ)| ^ (2 * k) *
      Real.exp (-((Real.pi * δ) * (n : ℝ) ^ 2)))) :=
  (summable_int_pow_mul_exp_neg_sq (2 * k) (mul_pos Real.pi_pos hδ)).mul_left _

/-- Termwise differentiation of the `k`-th theta derivative series on `Re y > 0`. -/
theorem hasDerivAt_theta_series (k : ℕ) {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (fun w => ∑' n : ℤ, ((Real.pi : ℂ) * (n : ℂ) ^ 2) ^ k *
        cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * w))
      (∑' n : ℤ, -((Real.pi : ℂ) * (n : ℂ) ^ 2) ^ (k + 1) *
        cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * y)) y := by
  set δ := y.re / 2
  have hδ : 0 < δ := by positivity
  set U : Set ℂ := {w | δ < w.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hyU : y ∈ U := by show δ < y.re; dsimp only [δ]; linarith
  have hF : ∀ n : ℤ, DifferentiableOn ℂ (fun w => ((Real.pi : ℂ) * (n : ℂ) ^ 2) ^ k *
      cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * w)) U := fun n => by fun_prop
  have hle : ∀ (n : ℤ) (w : ℂ), w ∈ U → ‖((Real.pi : ℂ) * (n : ℂ) ^ 2) ^ k *
      cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * w)‖ ≤
        Real.pi ^ k * (|(n : ℝ)| ^ (2 * k) * Real.exp (-((Real.pi * δ) * (n : ℝ) ^ 2))) :=
    fun n w hw => norm_pow_mul_cexp_le k (le_of_lt hw) n
  have hsum := summable_theta_terms_re (k := k) hδ
  have hdiff := differentiableOn_tsum_of_summable_norm hsum hF hU hle
  have hderiv := hasSum_deriv_of_summable_norm hsum hF hU hle hyU
  have hD : HasDerivAt (fun w => ∑' n : ℤ, ((Real.pi : ℂ) * (n : ℂ) ^ 2) ^ k *
      cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * w)) _ y :=
    (hdiff.differentiableAt (hU.mem_nhds hyU)).hasDerivAt
  rw [← hderiv.tsum_eq] at hD
  refine hD.congr_deriv (tsum_congr fun n => ?_)
  have h1 : HasDerivAt (fun w => ((Real.pi : ℂ) * (n : ℂ) ^ 2) ^ k *
      cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * w))
      (((Real.pi : ℂ) * (n : ℂ) ^ 2) ^ k * (cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * y) *
        (-(Real.pi : ℂ) * (n : ℂ) ^ 2))) y :=
    ((Complex.hasDerivAt_exp _).comp y ((hasDerivAt_id y).const_mul _ |>.congr_deriv
      (mul_one _))).const_mul _
  rw [h1.deriv]
  ring

theorem hasDerivAt_jacobiThetaSum {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt jacobiThetaSum (jacobiThetaSumOne y) y := by
  have h := hasDerivAt_theta_series 0 hy
  simp only [pow_zero, one_mul, zero_add, pow_one] at h
  exact h

theorem hasDerivAt_jacobiThetaSumOne {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt jacobiThetaSumOne (jacobiThetaSumTwo y) y := by
  have h := hasDerivAt_theta_series 1 hy
  simp only [pow_one] at h
  have hf : jacobiThetaSumOne = fun w => -(∑' n : ℤ, ((Real.pi : ℂ) * (n : ℂ) ^ 2) *
      cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * w)) := by
    funext w; unfold jacobiThetaSumOne; rw [← tsum_neg]; congr 1; funext n; ring
  rw [hf]
  refine h.neg.congr_deriv ?_
  unfold jacobiThetaSumTwo
  rw [← tsum_neg]; congr 1; funext n; ring

theorem deriv_jacobiThetaSum_eventually {y : ℂ} (hy : 0 < y.re) :
    deriv jacobiThetaSum =ᶠ[𝓝 y] jacobiThetaSumOne := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hy] with w hw
  exact (hasDerivAt_jacobiThetaSum hw).deriv

theorem deriv_deriv_jacobiThetaSum {y : ℂ} (hy : 0 < y.re) :
    deriv (deriv jacobiThetaSum) y = jacobiThetaSumTwo y := by
  rw [(deriv_jacobiThetaSum_eventually hy).deriv_eq, (hasDerivAt_jacobiThetaSumOne hy).deriv]

/-- The boundary source `κ(y) = y^{5/4} (2 y ϑ''(y) + 3 ϑ'(y))`. -/
def thetaBoundarySource (y : ℂ) : ℂ :=
  y ^ (5 / 4 : ℂ) * (2 * y * deriv (deriv jacobiThetaSum) y + 3 * deriv jacobiThetaSum y)

/-- The boundary-source summand `(2π² n⁴ y - 3π n²) e^{-π n² y}`. -/
def thetaBoundaryTerm (y : ℂ) (n : ℤ) : ℂ :=
  (2 * (Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 4 * y - 3 * Real.pi * (n : ℂ) ^ 2) *
    cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * y)

theorem summable_theta_series (k : ℕ) {y : ℂ} (hy : 0 < y.re) :
    Summable (fun n : ℤ => ((Real.pi : ℂ) * (n : ℂ) ^ 2) ^ k *
      cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * y)) :=
  Summable.of_norm_bounded (summable_theta_terms_re (k := k) hy) fun n =>
    norm_pow_mul_cexp_le k le_rfl n

theorem thetaBoundarySource_eq_tsum {y : ℂ} (hy : 0 < y.re) :
    thetaBoundarySource y = y ^ (5 / 4 : ℂ) * ∑' n : ℤ, thetaBoundaryTerm y n := by
  unfold thetaBoundarySource
  rw [deriv_deriv_jacobiThetaSum hy, (hasDerivAt_jacobiThetaSum hy).deriv]
  congr 1
  unfold jacobiThetaSumTwo jacobiThetaSumOne
  have hA := summable_theta_series 2 hy
  have hB : Summable (fun n : ℤ => -((Real.pi : ℂ) * (n : ℂ) ^ 2) *
      cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * y)) :=
    (summable_theta_series 1 hy).neg.congr fun n => by ring
  rw [← tsum_mul_left, ← tsum_mul_left, ← (hA.mul_left (2 * y)).tsum_add (hB.mul_left 3)]
  exact tsum_congr fun n => by unfold thetaBoundaryTerm; ring

theorem thetaBoundaryTerm_neg (y : ℂ) (n : ℤ) : thetaBoundaryTerm y (-n) = thetaBoundaryTerm y n := by
  unfold thetaBoundaryTerm; push_cast; ring_nf

theorem re_cexp_two_mul_pos {z : ℂ} (hz : z ∈ thetaCuspStrip) : 0 < (cexp (2 * z)).re := by
  have hz' : |z.im| < Real.pi / 4 := hz
  rw [Complex.exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · have := (abs_lt.mp hz').1; simp [Complex.mul_im]; linarith
  · have := (abs_lt.mp hz').2; simp [Complex.mul_im]; linarith

/-- **The strip source is the boundary source in the clock variable**: `k(z) = κ(e^{2z})` on
`|Im z| < π/4`. -/
theorem thetaCuspStripSource_eq_boundarySource {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    thetaCuspStripSource z = thetaBoundarySource (cexp (2 * z)) := by
  have hy := re_cexp_two_mul_pos hz
  set y := cexp (2 * z) with hydef
  rw [thetaBoundarySource_eq_tsum hy]
  have hsum : Summable (thetaBoundaryTerm y) := by
    have h2 := (summable_theta_series 2 hy).mul_left (2 * y)
    have h1 := (summable_theta_series 1 hy).mul_left (3 : ℂ)
    refine (h2.sub h1).congr fun n => ?_
    unfold thetaBoundaryTerm; ring
  have hnat := hsum.hasSum.nat_add_neg
  have h0 : thetaBoundaryTerm y 0 = 0 := by simp [thetaBoundaryTerm]
  rw [h0, add_zero] at hnat
  simp_rw [thetaBoundaryTerm_neg] at hnat
  have hz' : |z.im| < Real.pi / 4 := hz
  have hpow : y ^ (5 / 4 : ℂ) = cexp (5 * z / 2) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp]
    · congr 1; ring
    · have := (abs_lt.mp hz').1; simp [Complex.mul_im]; linarith [Real.pi_pos]
    · have := (abs_lt.mp hz').2; simp [Complex.mul_im]; linarith [Real.pi_pos]
  rw [hpow, ← hnat.tsum_eq, ← tsum_mul_left]
  unfold thetaCuspStripSource
  refine tsum_congr fun n => ?_
  unfold thetaCuspComplexTerm thetaCuspComplexSeed thetaBoundaryTerm
  have hsq : ((n : ℂ) * cexp z) ^ 2 = (n : ℂ) ^ 2 * y := by
    rw [mul_pow, hydef, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have hq : ((n : ℂ) * cexp z) ^ 4 = (n : ℂ) ^ 4 * y ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]; ring
  rw [hsq, hq]
  have hexp : cexp (5 * z / 2) = cexp (z / 2) * y := by rw [hydef, ← Complex.exp_add]; ring_nf
  rw [hexp]
  push_cast
  ring_nf

/-! ## Poisson summation at a rational point of the clock boundary -/

/-- The twisted Gauss coefficient `G_ℓ = Σ_{r mod q} e(-p r²/q) e(r ℓ/q)`. -/
def rationalCuspCoeff (p q : ℕ) (ℓ : ℤ) : ℂ :=
  ∑ r : Fin q, cexp (2 * Real.pi * I * (-(p : ℂ) * ((r : ℕ) : ℂ) ^ 2 / q)) *
    cexp (2 * Real.pi * I * ((((r : ℕ) : ℝ) / q : ℝ) : ℂ) * ℓ)

theorem cuspCoeff_zero (p q : ℕ) : rationalCuspCoeff p q 0 = gaussQ (-(p : ℤ)) q := by
  unfold rationalCuspCoeff gaussQ
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Int.cast_zero, mul_zero, Complex.exp_zero, mul_one]
  push_cast; ring_nf

theorem norm_cuspCoeff_le (p q : ℕ) (ℓ : ℤ) : ‖rationalCuspCoeff p q ℓ‖ ≤ q := by
  unfold rationalCuspCoeff
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ r : Fin q, ‖cexp (2 * Real.pi * I * (-(p : ℂ) * ((r : ℕ) : ℂ) ^ 2 / q)) *
      cexp (2 * Real.pi * I * ((((r : ℕ) : ℝ) / q : ℝ) : ℂ) * ℓ)‖ = 1 := by
    intro r
    rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
    have h1 : (2 * (Real.pi : ℂ) * I * (-(p : ℂ) * ((r : ℕ) : ℂ) ^ 2 / q)).re = 0 := by
      have : 2 * (Real.pi : ℂ) * I * (-(p : ℂ) * ((r : ℕ) : ℂ) ^ 2 / q) =
          ((-(2 * Real.pi * p * (r : ℕ) ^ 2 / q) : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
    have h2 : (2 * (Real.pi : ℂ) * I * ((((r : ℕ) : ℝ) / q : ℝ) : ℂ) * ℓ).re = 0 := by
      have : 2 * (Real.pi : ℂ) * I * ((((r : ℕ) : ℝ) / q : ℝ) : ℂ) * ℓ =
          ((2 * Real.pi * ((r : ℕ) / q) * ℓ : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
    rw [h1, h2]; simp
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rfl

/-- The dual Poisson series `Σ_ℓ G_ℓ e^{-π ℓ²/(q² η)}`. -/
def cuspPoissonSeries (p q : ℕ) (η : ℂ) : ℂ :=
  ∑' ℓ : ℤ, rationalCuspCoeff p q ℓ * cexp (-(Real.pi : ℂ) * (ℓ : ℂ) ^ 2 / ((q : ℂ) ^ 2 * η))

theorem norm_cuspPoisson_term_le (p q : ℕ) (ℓ : ℤ) {η : ℂ} {c : ℝ}
    (hc : c ≤ (η⁻¹).re) (hq : 0 < q) :
    ‖rationalCuspCoeff p q ℓ * cexp (-(Real.pi : ℂ) * (ℓ : ℂ) ^ 2 / ((q : ℂ) ^ 2 * η))‖ ≤
      q * Real.exp (-((Real.pi * c / q ^ 2) * (ℓ : ℝ) ^ 2)) := by
  rw [norm_mul, Complex.norm_exp]
  refine mul_le_mul (norm_cuspCoeff_le p q ℓ) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
    (Nat.cast_nonneg _)
  have e : -(Real.pi : ℂ) * (ℓ : ℂ) ^ 2 / ((q : ℂ) ^ 2 * η) =
      ((-(Real.pi * (ℓ : ℝ) ^ 2 / (q : ℝ) ^ 2)) : ℝ) * η⁻¹ := by
    push_cast; field_simp
  rw [e, Complex.re_ofReal_mul]
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  have hℓ := sq_nonneg (ℓ : ℝ)
  have : Real.pi * (ℓ : ℝ) ^ 2 / (q : ℝ) ^ 2 * c ≤ Real.pi * (ℓ : ℝ) ^ 2 / (q : ℝ) ^ 2 * (η⁻¹).re :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  calc -(Real.pi * c / (q : ℝ) ^ 2 * (ℓ : ℝ) ^ 2) = -(Real.pi * (ℓ : ℝ) ^ 2 / (q : ℝ) ^ 2 * c) := by
        ring
    _ ≥ -(Real.pi * (ℓ : ℝ) ^ 2 / (q : ℝ) ^ 2 * (η⁻¹).re) := by linarith
    _ = -(Real.pi * (ℓ : ℝ) ^ 2 / (q : ℝ) ^ 2) * (η⁻¹).re := by ring

theorem summable_int_exp_neg_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun ℓ : ℤ => Real.exp (-(c * (ℓ : ℝ) ^ 2))) := by
  simpa using summable_int_pow_mul_exp_neg_sq 0 hc

theorem summable_cuspPoisson_terms (p q : ℕ) (hq : 0 < q) {η : ℂ} (hη : 0 < η.re) :
    Summable (fun ℓ : ℤ => rationalCuspCoeff p q ℓ *
      cexp (-(Real.pi : ℂ) * (ℓ : ℂ) ^ 2 / ((q : ℂ) ^ 2 * η))) := by
  have hc : 0 < (η⁻¹).re := by
    rw [Complex.inv_re]; exact div_pos hη (Complex.normSq_pos.mpr (fun h => by simp [h] at hη))
  exact Summable.of_norm_bounded
    ((summable_int_exp_neg_sq (by positivity : 0 < Real.pi * (η⁻¹).re / (q : ℝ) ^ 2)).mul_left _)
    fun ℓ => norm_cuspPoisson_term_le p q ℓ le_rfl hq

/-- The dual series is holomorphic on the right half-plane. -/
theorem differentiableOn_cuspPoissonSeries (p q : ℕ) (hq : 0 < q) :
    DifferentiableOn ℂ (cuspPoissonSeries p q) {η : ℂ | 0 < η.re} := by
  intro η₀ hη₀
  have hη₀' : 0 < η₀.re := hη₀
  set r := η₀.re / 2
  have hr : 0 < r := by positivity
  set c := r / (‖η₀‖ + r) ^ 2
  have hc : 0 < c := by
    have : 0 < ‖η₀‖ + r := by positivity
    positivity
  have hball : ∀ η ∈ Metric.ball η₀ r, c ≤ (η⁻¹).re := by
    intro η hη
    have hd : ‖η - η₀‖ < r := by rw [← dist_eq_norm]; exact hη
    have hre : r ≤ η.re := by
      have h1 := Complex.abs_re_le_norm (η - η₀)
      rw [Complex.sub_re] at h1
      have h2 := (abs_le.mp (h1.trans hd.le)).1
      dsimp only [r] at h2 ⊢; linarith
    have hn : ‖η‖ ≤ ‖η₀‖ + r := by
      calc ‖η‖ = ‖η₀ + (η - η₀)‖ := by ring_nf
        _ ≤ ‖η₀‖ + ‖η - η₀‖ := norm_add_le _ _
        _ ≤ ‖η₀‖ + r := by linarith
    have hη0 : η ≠ 0 := fun h => by simp [h] at hre; linarith
    rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
    have hpos : 0 < ‖η‖ := norm_pos_iff.mpr hη0
    rw [le_div_iff₀ (by positivity)]
    calc c * ‖η‖ ^ 2 ≤ c * (‖η₀‖ + r) ^ 2 := by gcongr
      _ = r := by dsimp only [c]; field_simp
      _ ≤ η.re := hre
  have hopen : IsOpen (Metric.ball η₀ r) := Metric.isOpen_ball
  have hdiff : DifferentiableOn ℂ (cuspPoissonSeries p q) (Metric.ball η₀ r) := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_int_exp_neg_sq (by positivity : 0 < Real.pi * c / (q : ℝ) ^ 2)).mul_left (q : ℝ))
      (fun ℓ => ?_) hopen (fun ℓ η hη => norm_cuspPoisson_term_le p q ℓ (hball η hη) hq)
    intro η hη
    have hη0 : η ≠ 0 := by
      intro h; have := hball η hη; rw [h] at this; simp at this; linarith
    have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
    fun_prop (disch := exact mul_ne_zero (pow_ne_zero 2 hq0) hη0)
  exact (hdiff.differentiableAt (hopen.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt

theorem ofReal_cpow_neg_half {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (-(1 / 2) : ℂ) = ((Real.sqrt t)⁻¹ : ℝ) := by
  rw [show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow ht.le, Real.rpow_neg ht.le, Real.sqrt_eq_rpow]

/-- **Poisson summation at `y₀ = 2ip/q`, real displacement.** -/
theorem jacobiThetaSum_cusp_ofReal (p q : ℕ) (hq : 0 < q) {t : ℝ} (ht : 0 < t) :
    jacobiThetaSum (2 * I * p / q + t) =
      (1 / q) * (t : ℂ) ^ (-(1 / 2) : ℂ) * cuspPoissonSeries p q t := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  rw [jacobiThetaSum_eq_theta]
  have hz : I * (2 * I * p / q + t) / 2 = -(((p : ℤ) : ℂ)) / q + ((t / 2 : ℝ) : ℂ) * I := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [hz, theta_cusp q (p : ℤ) (by positivity : (0 : ℝ) < t / 2), ofReal_cpow_neg_half ht]
  have hsq : Real.sqrt (2 * (t / 2) * (q : ℝ) ^ 2) = q * Real.sqrt t := by
    rw [show 2 * (t / 2) * (q : ℝ) ^ 2 = (q : ℝ) ^ 2 * t by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hqR.le]
  rw [hsq]
  have hmul : ∀ (a : ℂ) (x s : ℝ), a * dualT x s =
      ∑' n : ℤ, a * cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * s + 2 * Real.pi * I * x * n) := by
    intro a x s; unfold dualT; rw [tsum_mul_left]
  simp_rw [hmul]
  unfold cuspPoissonSeries rationalCuspCoeff
  have hsr : ∀ r : Fin q, Summable fun n : ℤ =>
      cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * ((1 / (2 * (t / 2) * (q : ℝ) ^ 2) : ℝ) : ℂ) +
        2 * Real.pi * I * ((((r : ℕ) : ℝ) / q : ℝ) : ℂ) * n) := by
    intro r
    refine Summable.of_norm ?_
    simp_rw [norm_dualT_term]
    have h := summable_int_exp_neg_sq (c := Real.pi * (1 / (2 * (t / 2) * (q : ℝ) ^ 2)))
      (by positivity)
    exact h.congr fun n => by ring_nf
  rw [← Summable.tsum_finsetSum (fun r _ => (hsr r).mul_left _), ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun ℓ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hexp : cexp (-(Real.pi : ℂ) * (ℓ : ℂ) ^ 2 * ((1 / (2 * (t / 2) * (q : ℝ) ^ 2) : ℝ) : ℂ) +
      2 * Real.pi * I * ((((r : ℕ) : ℝ) / q : ℝ) : ℂ) * ℓ) =
      cexp (-(Real.pi : ℂ) * (ℓ : ℂ) ^ 2 / ((q : ℂ) ^ 2 * (t : ℂ))) *
        cexp (2 * Real.pi * I * ((((r : ℕ) : ℝ) / q : ℝ) : ℂ) * ℓ) := by
    rw [← Complex.exp_add]
    congr 1
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    push_cast
    field_simp
  rw [hexp]
  push_cast
  ring

/-- **Poisson summation at `y₀ = 2ip/q`** for every displacement `η` with `Re η > 0`:
`ϑ(y₀ + η) = q⁻¹ η^{-1/2} Σ_ℓ G_ℓ e^{-π ℓ²/(q² η)}`. -/
theorem jacobiThetaSum_cusp (p q : ℕ) (hq : 0 < q) {η : ℂ} (hη : 0 < η.re) :
    jacobiThetaSum (2 * I * p / q + η) =
      (1 / q) * η ^ (-(1 / 2) : ℂ) * cuspPoissonSeries p q η := by
  set U : Set ℂ := {η : ℂ | 0 < η.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (fun η => jacobiThetaSum (2 * I * p / q + η)) U := by
    refine DifferentiableOn.analyticOnNhd (fun η hη' => ?_) hU
    have hre : 0 < (2 * I * p / q + η).re := by
      have : (2 * I * (p : ℂ) / q).re = 0 := by
        rw [show 2 * I * (p : ℂ) / q = ((2 * p / q : ℝ) : ℂ) * I by push_cast; ring,
          Complex.mul_I_re, Complex.ofReal_im, neg_zero]
      rw [Complex.add_re, this, zero_add]; exact hη'
    exact ((hasDerivAt_jacobiThetaSum hre).differentiableAt.comp η
      ((differentiable_const _).add differentiable_id η)).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun η => (1 / (q : ℂ)) * η ^ (-(1 / 2) : ℂ) *
      cuspPoissonSeries p q η) U := by
    refine DifferentiableOn.analyticOnNhd (fun η hη' => ?_) hU
    have hslit : η ∈ Complex.slitPlane := Or.inl hη'
    exact ((differentiableAt_const _).mul
      ((Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt.differentiableAt)).differentiableWithinAt.mul
      (differentiableOn_cuspPoissonSeries p q hq η hη')
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h1 : (1 : ℂ) ∈ U := by show (0 : ℝ) < (1 : ℂ).re; simp
  have hfreq : ∃ᶠ η in 𝓝[≠] (1 : ℂ), jacobiThetaSum (2 * I * p / q + η) =
      (1 / q) * η ^ (-(1 / 2) : ℂ) * cuspPoissonSeries p q η := by
    let u : ℕ → ℂ := fun n => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
    have hu : Tendsto u atTop (𝓝[≠] 1) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
        rw [add_zero] at h
        have h2 := (Complex.continuous_ofReal.tendsto _).comp h
        rw [Complex.ofReal_one] at h2
        exact h2
      · simp only [u, Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        have h' := congrArg Complex.re h
        rw [Complex.ofReal_re, Complex.one_re] at h'
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    exact hu.frequently (Eventually.of_forall fun n =>
      jacobiThetaSum_cusp_ofReal p q hq (by positivity)).frequently
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hpre h1 hfreq hη

/-! ## The singular main term and the exponentially small remainder -/

/-- The cusp point `y₀ = 2ip/q`. -/
def cuspPoint (p q : ℕ) : ℂ := 2 * I * p / q

/-- Remainder after the `ℓ = 0` Poisson term: `ϑ(y₀+η) - q⁻¹ G η^{-1/2}`. -/
def cuspRemainder (p q : ℕ) (η : ℂ) : ℂ :=
  jacobiThetaSum (cuspPoint p q + η) - (1 / q) * gaussQ (-(p : ℤ)) q * η ^ (-(1 / 2) : ℂ)

theorem re_inv_ge_of_mem_closedBall {ε : ℝ} (hε : 0 < ε) {η : ℂ}
    (hη : η ∈ Metric.closedBall (ε : ℂ) (ε / 2)) : 2 / (9 * ε) ≤ (η⁻¹).re ∧ ε / 2 ≤ η.re ∧
      ‖η‖ ≤ 3 * ε / 2 := by
  have hd : ‖η - ε‖ ≤ ε / 2 := by rw [← dist_eq_norm]; exact hη
  have hre : ε / 2 ≤ η.re := by
    have h1 := Complex.abs_re_le_norm (η - ε)
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    have := (abs_le.mp (h1.trans hd)).1; linarith
  have hn : ‖η‖ ≤ 3 * ε / 2 := by
    calc ‖η‖ = ‖(ε : ℂ) + (η - ε)‖ := by ring_nf
      _ ≤ ‖(ε : ℂ)‖ + ‖η - ε‖ := norm_add_le _ _
      _ ≤ ε + ε / 2 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]; linarith
      _ = 3 * ε / 2 := by ring
  have hη0 : η ≠ 0 := fun h => by simp [h] at hre; linarith
  refine ⟨?_, hre, hn⟩
  rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
  have hpos : 0 < ‖η‖ := norm_pos_iff.mpr hη0
  rw [le_div_iff₀ (by positivity)]
  calc 2 / (9 * ε) * ‖η‖ ^ 2 ≤ 2 / (9 * ε) * (3 * ε / 2) ^ 2 := by gcongr
    _ = ε / 2 := by field_simp; ring
    _ ≤ η.re := hre

/-- **Exponential smallness of the remainder** on the disks `|η - ε| ≤ ε/2`, `0 < ε ≤ 1`. -/
theorem exists_norm_cuspRemainder_le (p q : ℕ) (hq : 0 < q) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ η ∈ Metric.closedBall (ε : ℂ) (ε / 2),
        ‖cuspRemainder p q η‖ ≤ K * (Real.sqrt ε)⁻¹ * Real.exp (-(c / ε)) := by
  set A₁ : ℝ := 2 * Real.pi / (9 * (q : ℝ) ^ 2)
  have hA₁ : 0 < A₁ := by positivity
  set Ksum := ∑' ℓ : ℤ, Real.exp (-((A₁ / 2) * (ℓ : ℝ) ^ 2))
  have hsumK := summable_int_exp_neg_sq (by positivity : 0 < A₁ / 2)
  have hK0 : 0 < Ksum := by
    refine lt_of_lt_of_le (Real.exp_pos (-((A₁ / 2) * ((0 : ℤ) : ℝ) ^ 2))) ?_
    exact hsumK.le_tsum 0 (fun j _ => (Real.exp_pos _).le)
  refine ⟨Real.sqrt 2 * Ksum, A₁ / 2 * 1, by positivity, by positivity, fun ε hε hε1 η hη => ?_⟩
  obtain ⟨hinv, hre, hn⟩ := re_inv_ge_of_mem_closedBall hε hη
  have hη0 : 0 < η.re := by linarith
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  set A : ℝ := 2 * Real.pi / (9 * (q : ℝ) ^ 2 * ε)
  have hAA : A₁ ≤ A := by
    dsimp only [A, A₁]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_pos, sq_nonneg (q : ℝ), mul_pos Real.pi_pos (pow_pos (Nat.cast_pos.mpr hq) 2)]
  -- rewrite the remainder through the Poisson formula
  have hrem : cuspRemainder p q η = (1 / q) * η ^ (-(1 / 2) : ℂ) *
      ∑' ℓ : ℤ, if ℓ = 0 then 0 else rationalCuspCoeff p q ℓ *
        cexp (-(Real.pi : ℂ) * (ℓ : ℂ) ^ 2 / ((q : ℂ) ^ 2 * η)) := by
    unfold cuspRemainder cuspPoint
    rw [jacobiThetaSum_cusp p q hq hη0, cuspPoissonSeries,
      (summable_cuspPoisson_terms p q hq hη0).tsum_eq_add_tsum_ite 0]
    simp only [Int.cast_zero, zero_pow two_ne_zero, mul_zero, zero_div,
      Complex.exp_zero, mul_one, cuspCoeff_zero]
    ring
  have hterm : ∀ ℓ : ℤ, ‖(if ℓ = 0 then 0 else rationalCuspCoeff p q ℓ *
      cexp (-(Real.pi : ℂ) * (ℓ : ℂ) ^ 2 / ((q : ℂ) ^ 2 * η)))‖ ≤
        q * Real.exp (-(A / 2)) * Real.exp (-((A₁ / 2) * (ℓ : ℝ) ^ 2)) := by
    intro ℓ
    split_ifs with h
    · rw [norm_zero]; positivity
    · have hc : 2 / (9 * ε) ≤ (η⁻¹).re := hinv
      refine (norm_cuspPoisson_term_le p q ℓ hc hq).trans ?_
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
      have hℓ : (1 : ℝ) ≤ (ℓ : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ ℓ ^ 2 := by
          rcases lt_trichotomy ℓ 0 with h' | h' | h'
          · nlinarith
          · exact absurd h' h
          · nlinarith
        exact_mod_cast this
      have e : Real.pi * (2 / (9 * ε)) / (q : ℝ) ^ 2 = A := by
        dsimp only [A]; field_simp
      rw [e]
      nlinarith
  have hsum2 : Summable (fun ℓ : ℤ => q * Real.exp (-(A / 2)) *
      Real.exp (-((A₁ / 2) * (ℓ : ℝ) ^ 2))) := hsumK.mul_left _
  have hS : ‖∑' ℓ : ℤ, (if ℓ = 0 then 0 else rationalCuspCoeff p q ℓ *
      cexp (-(Real.pi : ℂ) * (ℓ : ℂ) ^ 2 / ((q : ℂ) ^ 2 * η)))‖ ≤
        q * Real.exp (-(A / 2)) * Ksum := by
    refine (tsum_of_norm_bounded hsum2.hasSum hterm).trans_eq ?_
    rw [tsum_mul_left]
  have hpow : ‖η ^ (-(1 / 2) : ℂ)‖ ≤ Real.sqrt 2 * (Real.sqrt ε)⁻¹ := by
    have hηn : ε / 2 ≤ ‖η‖ := hre.trans (Complex.re_le_norm η)
    rw [show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real]
    calc ‖η‖ ^ (-(1 / 2) : ℝ) ≤ (ε / 2) ^ (-(1 / 2) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hηn (by norm_num)
      _ = Real.sqrt 2 * (Real.sqrt ε)⁻¹ := by
          rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_div' _ (by norm_num :
            (0 : ℝ) ≤ 2), inv_div]
          field_simp
  have hexpA : Real.exp (-(A / 2)) ≤ Real.exp (-(A₁ / 2 * 1 / ε)) := by
    refine Real.exp_le_exp.mpr ?_
    have : A = A₁ / ε := by dsimp only [A, A₁]; field_simp
    rw [this]; ring_nf; rfl
  rw [hrem, norm_mul, norm_mul]
  have hq' : ‖(1 : ℂ) / q‖ = 1 / q := by simp
  rw [hq']
  calc 1 / (q : ℝ) * ‖η ^ (-(1 / 2) : ℂ)‖ * ‖∑' ℓ : ℤ, (if ℓ = 0 then 0 else rationalCuspCoeff p q ℓ *
        cexp (-(Real.pi : ℂ) * (ℓ : ℂ) ^ 2 / ((q : ℂ) ^ 2 * η)))‖
      ≤ 1 / (q : ℝ) * (Real.sqrt 2 * (Real.sqrt ε)⁻¹) * (q * Real.exp (-(A / 2)) * Ksum) := by
        gcongr
    _ = Real.sqrt 2 * Ksum * (Real.sqrt ε)⁻¹ * Real.exp (-(A / 2)) := by
        field_simp
    _ ≤ Real.sqrt 2 * Ksum * (Real.sqrt ε)⁻¹ * Real.exp (-(A₁ / 2 * 1 / ε)) := by
        gcongr
    _ = Real.sqrt 2 * Ksum * (Real.sqrt ε)⁻¹ * Real.exp (-(A₁ / 2 * 1 / ε)) := rfl

theorem cuspPoint_re (p q : ℕ) : (cuspPoint p q).re = 0 := by
  unfold cuspPoint
  rw [show 2 * I * (p : ℂ) / q = ((2 * p / q : ℝ) : ℂ) * I by push_cast; ring,
    Complex.mul_I_re, Complex.ofReal_im, neg_zero]

theorem cuspPoint_im (p q : ℕ) : (cuspPoint p q).im = 2 * p / q := by
  unfold cuspPoint
  rw [show 2 * I * (p : ℂ) / q = ((2 * p / q : ℝ) : ℂ) * I by push_cast; ring,
    Complex.mul_I_im, Complex.ofReal_re]

theorem differentiableAt_cuspRemainder (p q : ℕ) {η : ℂ} (hη : 0 < η.re) :
    DifferentiableAt ℂ (cuspRemainder p q) η := by
  have hre : 0 < (cuspPoint p q + η).re := by rw [Complex.add_re, cuspPoint_re, zero_add]; exact hη
  have h1 : DifferentiableAt ℂ (fun η => jacobiThetaSum (cuspPoint p q + η)) η :=
    (hasDerivAt_jacobiThetaSum hre).differentiableAt.comp η
      ((differentiable_const _).add differentiable_id η)
  have h2 : DifferentiableAt ℂ (fun η : ℂ => η ^ (-(1 / 2) : ℂ)) η :=
    (Complex.hasStrictDerivAt_cpow_const (Or.inl hη)).hasDerivAt.differentiableAt
  exact h1.sub ((differentiableAt_const _).mul h2)

/-- Cauchy estimates for the first two derivatives of the remainder. -/
theorem exists_norm_deriv_cuspRemainder_le (p q : ℕ) (hq : 0 < q) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖deriv (cuspRemainder p q) ε‖ ≤ 2 * K * (Real.sqrt ε)⁻¹ * Real.exp (-(c / ε)) / ε ∧
      ‖deriv (deriv (cuspRemainder p q)) ε‖ ≤
        8 * K * (Real.sqrt ε)⁻¹ * Real.exp (-(c / ε)) / ε ^ 2 := by
  obtain ⟨K, c, hK, hc, hb⟩ := exists_norm_cuspRemainder_le p q hq
  refine ⟨K, c, hK, hc, fun ε hε hε1 => ?_⟩
  have hR : 0 < ε / 2 := by positivity
  have hdcc : DiffContOnCl ℂ (cuspRemainder p q) (Metric.ball (ε : ℂ) (ε / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hR.ne']
    intro η hη
    have := (re_inv_ge_of_mem_closedBall hε hη).2.1
    exact (differentiableAt_cuspRemainder p q (by linarith)).differentiableWithinAt
  have hsph : ∀ η ∈ Metric.sphere (ε : ℂ) (ε / 2),
      ‖cuspRemainder p q η‖ ≤ K * (Real.sqrt ε)⁻¹ * Real.exp (-(c / ε)) :=
    fun η hη => hb ε hε hε1 η (Metric.sphere_subset_closedBall hη)
  have h1 := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hR hdcc hsph
  have h2 := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hR hdcc hsph
  rw [iteratedDeriv_one] at h1
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h2
  refine ⟨h1.trans_eq ?_, h2.trans_eq ?_⟩
  · simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one]; field_simp
  · simp only [Nat.factorial_two, Nat.cast_ofNat]; field_simp; ring

theorem cpow_mul_cpow_ofReal {ε : ℝ} (hε : 0 < ε) (a b : ℂ) :
    (ε : ℂ) ^ a * (ε : ℂ) ^ b = (ε : ℂ) ^ (a + b) :=
  (Complex.cpow_add a b (Complex.ofReal_ne_zero.mpr hε.ne')).symm

/-- **Exact decomposition.** `ε^{5/2} κ(y₀+ε) = (y₀+ε)^{5/4} [ (3G/2q) y₀ + ε^{5/2}(2(y₀+ε)R'' + 3R') ]`,
the singular main term cancelling exactly against the `ε^{-3/2}` contributions. -/
theorem cpow_mul_thetaBoundarySource_cusp (p q : ℕ) (hq : 0 < q) {ε : ℝ} (hε : 0 < ε) :
    (ε : ℂ) ^ (5 / 2 : ℂ) * thetaBoundarySource (cuspPoint p q + ε) =
      (cuspPoint p q + ε) ^ (5 / 4 : ℂ) *
        (3 * gaussQ (-(p : ℤ)) q / (2 * q) * cuspPoint p q +
          (ε : ℂ) ^ (5 / 2 : ℂ) * (2 * (cuspPoint p q + ε) *
            deriv (deriv (cuspRemainder p q)) ε + 3 * deriv (cuspRemainder p q) ε)) := by
  set y₀ := cuspPoint p q
  set C : ℂ := 1 / q * gaussQ (-(p : ℤ)) q
  set R := cuspRemainder p q
  set U : Set ℂ := {η : ℂ | 0 < η.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hεU : (ε : ℂ) ∈ U := by show (0 : ℝ) < (ε : ℂ).re; simpa using hε
  have hΘ : (fun η => jacobiThetaSum (y₀ + η)) = fun η => C * η ^ (-(1 / 2) : ℂ) + R η := by
    funext η; simp only [R, cuspRemainder, C, y₀]; ring
  have hRdiff : DifferentiableOn ℂ R U := fun η hη =>
    (differentiableAt_cuspRemainder p q hη).differentiableWithinAt
  have hRan := hRdiff.analyticOnNhd hU
  have hD1 : ∀ η ∈ U, deriv (fun η => jacobiThetaSum (y₀ + η)) η =
      C * ((-(1 / 2) : ℂ) * η ^ (-(1 / 2) - 1 : ℂ)) + deriv R η := by
    intro η hη
    rw [hΘ]
    have hm : HasDerivAt (fun η : ℂ => C * η ^ (-(1 / 2) : ℂ))
        (C * ((-(1 / 2) : ℂ) * η ^ (-(1 / 2) - 1 : ℂ))) η :=
      ((Complex.hasStrictDerivAt_cpow_const (Or.inl hη)).hasDerivAt).const_mul C
    exact (hm.add (hRdiff.differentiableAt (hU.mem_nhds hη)).hasDerivAt).deriv
  have hD1' : deriv (fun η => jacobiThetaSum (y₀ + η)) =ᶠ[𝓝 (ε : ℂ)]
      fun η => C * ((-(1 / 2) : ℂ) * η ^ (-(1 / 2) - 1 : ℂ)) + deriv R η :=
    Filter.eventually_of_mem (hU.mem_nhds hεU) hD1
  have hD2 : deriv (deriv (fun η => jacobiThetaSum (y₀ + η))) ε =
      C * ((-(1 / 2) : ℂ) * ((-(1 / 2) - 1 : ℂ) * (ε : ℂ) ^ (-(1 / 2) - 1 - 1 : ℂ))) +
        deriv (deriv R) ε := by
    rw [hD1'.deriv_eq]
    have hm : HasDerivAt (fun η : ℂ => C * ((-(1 / 2) : ℂ) * η ^ (-(1 / 2) - 1 : ℂ)))
        (C * ((-(1 / 2) : ℂ) * ((-(1 / 2) - 1 : ℂ) * (ε : ℂ) ^ (-(1 / 2) - 1 - 1 : ℂ)))) ε :=
      (((Complex.hasStrictDerivAt_cpow_const (Or.inl hεU)).hasDerivAt).const_mul _).const_mul C
    exact (hm.add ((hRan.deriv ε hεU).differentiableAt.hasDerivAt)).deriv
  have e1 : deriv jacobiThetaSum (y₀ + ε) = deriv (fun η => jacobiThetaSum (y₀ + η)) ε :=
    (deriv_comp_const_add jacobiThetaSum y₀ ε).symm
  have e2 : deriv (deriv jacobiThetaSum) (y₀ + ε) =
      deriv (deriv (fun η => jacobiThetaSum (y₀ + η))) ε := by
    have : deriv (fun η => jacobiThetaSum (y₀ + η)) = fun η => deriv jacobiThetaSum (y₀ + η) :=
      funext fun η => deriv_comp_const_add jacobiThetaSum y₀ η
    rw [this, deriv_comp_const_add]
  unfold thetaBoundarySource
  rw [e2, e1, hD2, hD1 _ hεU]
  have c1 : (ε : ℂ) ^ (5 / 2 : ℂ) * (ε : ℂ) ^ (-(1 / 2) - 1 - 1 : ℂ) = 1 := by
    rw [cpow_mul_cpow_ofReal hε]; norm_num
  have c2 : (ε : ℂ) ^ (5 / 2 : ℂ) * (ε : ℂ) ^ (-(1 / 2) - 1 : ℂ) = ε := by
    rw [cpow_mul_cpow_ofReal hε]; norm_num
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have key : (ε : ℂ) ^ (5 / 2 : ℂ) * (2 * (y₀ + ε) * (C * ((-(1 / 2) : ℂ) *
      ((-(1 / 2) - 1 : ℂ) * (ε : ℂ) ^ (-(1 / 2) - 1 - 1 : ℂ))) + deriv (deriv R) ε) +
      3 * (C * ((-(1 / 2) : ℂ) * (ε : ℂ) ^ (-(1 / 2) - 1 : ℂ)) + deriv R ε)) =
      3 * gaussQ (-(p : ℤ)) q / (2 * q) * y₀ +
        (ε : ℂ) ^ (5 / 2 : ℂ) * (2 * (y₀ + ε) * deriv (deriv R) ε + 3 * deriv R ε) := by
    have h : (ε : ℂ) ^ (5 / 2 : ℂ) * (2 * (y₀ + ε) * (C * ((-(1 / 2) : ℂ) *
        ((-(1 / 2) - 1 : ℂ) * (ε : ℂ) ^ (-(1 / 2) - 1 - 1 : ℂ))) + deriv (deriv R) ε) +
        3 * (C * ((-(1 / 2) : ℂ) * (ε : ℂ) ^ (-(1 / 2) - 1 : ℂ)) + deriv R ε)) =
        2 * (y₀ + ε) * C * ((-(1 / 2) : ℂ) * (-(1 / 2) - 1 : ℂ)) *
          ((ε : ℂ) ^ (5 / 2 : ℂ) * (ε : ℂ) ^ (-(1 / 2) - 1 - 1 : ℂ)) +
        3 * C * (-(1 / 2) : ℂ) * ((ε : ℂ) ^ (5 / 2 : ℂ) * (ε : ℂ) ^ (-(1 / 2) - 1 : ℂ)) +
        (ε : ℂ) ^ (5 / 2 : ℂ) * (2 * (y₀ + ε) * deriv (deriv R) ε + 3 * deriv R ε) := by ring
    rw [h, c1, c2]
    simp only [C]
    field_simp
    ring
  rw [← key]
  ring

theorem cuspPoint_mem_slitPlane (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    cuspPoint p q ∈ Complex.slitPlane := by
  refine Or.inr ?_
  rw [cuspPoint_im]; positivity

theorem cuspPoint_ne_zero (p q : ℕ) (hp : 0 < p) (hq : 0 < q) : cuspPoint p q ≠ 0 :=
  Complex.slitPlane_ne_zero (cuspPoint_mem_slitPlane p q hp hq)

theorem norm_ofReal_cpow_five_halves {ε : ℝ} (hε : 0 < ε) :
    ‖(ε : ℂ) ^ (5 / 2 : ℂ)‖ = ε ^ 2 * Real.sqrt ε := by
  rw [show (5 / 2 : ℂ) = ((5 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε,
    show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hε, Real.sqrt_eq_rpow]
  norm_cast

/-- The remainder contribution `ε^{5/2}(2(y₀+ε)R'' + 3R')` tends to zero. -/
theorem tendsto_cusp_remainder_part (p q : ℕ) (hq : 0 < q) :
    Tendsto (fun ε : ℝ => (ε : ℂ) ^ (5 / 2 : ℂ) * (2 * (cuspPoint p q + ε) *
      deriv (deriv (cuspRemainder p q)) ε + 3 * deriv (cuspRemainder p q) ε)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K, c, hK, hc, hb⟩ := exists_norm_deriv_cuspRemainder_le p q hq
  set B := 16 * K * (‖cuspPoint p q‖ + 1) + 6 * K
  have hlim : Tendsto (fun ε : ℝ => B * Real.exp (-(c / ε))) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => c / ε) (𝓝[>] 0) atTop :=
      (tendsto_inv_nhdsGT_zero).const_mul_atTop hc |>.congr fun ε => by ring
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul B
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  obtain ⟨hε0, hε1⟩ := hε
  obtain ⟨h1, h2⟩ := hb ε hε0 hε1.le
  have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε0
  have hyε : ‖cuspPoint p q + ε‖ ≤ ‖cuspPoint p q‖ + 1 := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]; linarith
  rw [norm_mul, norm_ofReal_cpow_five_halves hε0]
  calc ε ^ 2 * Real.sqrt ε * ‖2 * (cuspPoint p q + ε) * deriv (deriv (cuspRemainder p q)) ε +
        3 * deriv (cuspRemainder p q) ε‖
      ≤ ε ^ 2 * Real.sqrt ε * (2 * (‖cuspPoint p q‖ + 1) *
          (8 * K * (Real.sqrt ε)⁻¹ * Real.exp (-(c / ε)) / ε ^ 2) +
          3 * (2 * K * (Real.sqrt ε)⁻¹ * Real.exp (-(c / ε)) / ε)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, norm_mul, Complex.norm_ofNat]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hyε (by norm_num)) h2 (norm_nonneg _)
            (by positivity)
        · rw [norm_mul, Complex.norm_ofNat]
          exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = (16 * K * (‖cuspPoint p q‖ + 1) + 6 * K * ε) * Real.exp (-(c / ε)) := by
        field_simp
        ring
    _ ≤ B * Real.exp (-(c / ε)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        dsimp only [B]; nlinarith

/-- **The rational-cusp boundary law.** At `y₀ = 2ip/q` (`p, q > 0`),
`ε^{5/2} κ(y₀ + ε) → (3 G_{p,q}/(2q)) y₀^{9/4}` as `ε ↓ 0`, with
`G_{p,q} = Σ_{r mod q} e^{-2πi p r²/q}`. -/
theorem tendsto_thetaBoundarySource_cusp (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    Tendsto (fun ε : ℝ => (ε : ℂ) ^ (5 / 2 : ℂ) * thetaBoundarySource (cuspPoint p q + ε))
      (𝓝[>] 0) (𝓝 (3 * gaussQ (-(p : ℤ)) q / (2 * q) * cuspPoint p q ^ (9 / 4 : ℂ))) := by
  have hslit := cuspPoint_mem_slitPlane p q hp hq
  have hpow : Tendsto (fun ε : ℝ => (cuspPoint p q + ε) ^ (5 / 4 : ℂ)) (𝓝[>] 0)
      (𝓝 (cuspPoint p q ^ (5 / 4 : ℂ))) := by
    have hc : Tendsto (fun ε : ℝ => cuspPoint p q + (ε : ℂ)) (𝓝 0) (𝓝 (cuspPoint p q)) := by
      have h : Continuous (fun ε : ℝ => cuspPoint p q + (ε : ℂ)) := by fun_prop
      simpa using h.tendsto 0
    exact ((continuousAt_cpow_const hslit).tendsto.comp hc).mono_left nhdsWithin_le_nhds
  have hmain := hpow.mul ((tendsto_const_nhds (x := 3 * gaussQ (-(p : ℤ)) q / (2 * q) *
    cuspPoint p q)).add (tendsto_cusp_remainder_part p q hq))
  rw [add_zero] at hmain
  have hlimit : cuspPoint p q ^ (5 / 4 : ℂ) * (3 * gaussQ (-(p : ℤ)) q / (2 * q) * cuspPoint p q) =
      3 * gaussQ (-(p : ℤ)) q / (2 * q) * cuspPoint p q ^ (9 / 4 : ℂ) := by
    have h := Complex.cpow_add (5 / 4 : ℂ) 1 (cuspPoint_ne_zero p q hp hq)
    rw [Complex.cpow_one] at h
    rw [show (9 / 4 : ℂ) = 5 / 4 + 1 by norm_num, h]
    ring
  rw [hlimit] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (cpow_mul_thetaBoundarySource_cusp p q hq hε).symm

/-! ## Consequences: magnitude, charge classes, unboundedness, natural boundary -/

theorem isCoprime_neg_natCast {p q : ℕ} (h : Nat.Coprime p q) : IsCoprime (-(p : ℤ)) (q : ℤ) :=
  (Nat.isCoprime_iff_coprime.mpr h).neg_left

/-- `|G_{p,q}| = √q` for odd `q` coprime to `p`. -/
theorem norm_cuspGauss_of_odd {p q : ℕ} (hq : q % 2 = 1) (hpq : Nat.Coprime p q) :
    ‖gaussQ (-(p : ℤ)) q‖ = Real.sqrt q :=
  norm_gaussQ_of_odd hq (isCoprime_neg_natCast hpq)

/-- The boundary amplitude `L_{p,q} = (3 G_{p,q}/(2q)) y₀^{9/4}`. -/
def cuspAmplitude (p q : ℕ) : ℂ := 3 * gaussQ (-(p : ℤ)) q / (2 * q) * cuspPoint p q ^ (9 / 4 : ℂ)

/-- **Arithmetic charge modulo four.** For coprime `p, q > 0`,
`L_{p,q}^4 / i = (81/(16 q²)) (2p/q)^9 · {1, 0, -4}` for `q` odd, `q ≡ 2 mod 4`, `4 ∣ q`. -/
theorem cuspAmplitude_pow_four_div_I {p q : ℕ} (hq : 0 < q) (hpq : Nat.Coprime p q) :
    cuspAmplitude p q ^ 4 / I = 81 / (16 * (q : ℂ) ^ 2) * ((2 * p / q : ℝ) : ℂ) ^ 9 *
      (if q % 2 = 1 then 1 else if q % 4 = 2 then 0 else -4) := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hG := gaussQ_pow_four hq (isCoprime_neg_natCast hpq)
  have hy : (cuspPoint p q ^ (9 / 4 : ℂ)) ^ 4 = I * ((2 * p / q : ℝ) : ℂ) ^ 9 := by
    have hI9 : I ^ 9 = I := by
      rw [show (9 : ℕ) = 4 * 2 + 1 from rfl, pow_succ, pow_mul, Complex.I_pow_four, one_pow,
        one_mul]
    rw [← Complex.cpow_nat_mul]
    norm_num
    unfold cuspPoint
    rw [show 2 * I * (p : ℂ) / q = I * (2 * p / q) by ring, mul_pow, hI9]
  unfold cuspAmplitude
  rw [mul_pow, hy, div_pow, mul_pow, hG]
  split_ifs <;> field_simp <;> ring

/-- For odd `q` coprime to `p` the amplitude is nonzero. -/
theorem cuspAmplitude_ne_zero {p q : ℕ} (hp : 0 < p) (hq : q % 2 = 1) (hpq : Nat.Coprime p q) :
    cuspAmplitude p q ≠ 0 := by
  have hq0 : 0 < q := by omega
  have hG : gaussQ (-(p : ℤ)) q ≠ 0 := by
    intro h
    have := norm_cuspGauss_of_odd hq hpq
    rw [h, norm_zero] at this
    have : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hq0)
    linarith
  unfold cuspAmplitude
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq0.ne'
  exact mul_ne_zero (div_ne_zero (mul_ne_zero three_ne_zero hG) (mul_ne_zero two_ne_zero hqC))
    ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr (cuspPoint_ne_zero p q hp hq0))

/-- The unscaled decomposition `κ(y₀+ε) = (y₀+ε)^{5/4} [(3G/2q) y₀ ε^{-5/2} + 2(y₀+ε)R'' + 3R']`. -/
theorem thetaBoundarySource_cusp_eq (p q : ℕ) (hq : 0 < q) {ε : ℝ} (hε : 0 < ε) :
    thetaBoundarySource (cuspPoint p q + ε) =
      (cuspPoint p q + ε) ^ (5 / 4 : ℂ) *
        (3 * gaussQ (-(p : ℤ)) q / (2 * q) * cuspPoint p q * (ε : ℂ) ^ (-(5 / 2) : ℂ) +
          (2 * (cuspPoint p q + ε) * deriv (deriv (cuspRemainder p q)) ε +
            3 * deriv (cuspRemainder p q) ε)) := by
  have h := cpow_mul_thetaBoundarySource_cusp p q hq hε
  have hne : (ε : ℂ) ^ (5 / 2 : ℂ) ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr
      (Complex.ofReal_ne_zero.mpr hε.ne')
  have hinv : (ε : ℂ) ^ (5 / 2 : ℂ) * (ε : ℂ) ^ (-(5 / 2) : ℂ) = 1 := by
    rw [cpow_mul_cpow_ofReal hε]; norm_num
  apply mul_left_cancel₀ hne
  rw [h]
  linear_combination -((cuspPoint p q + ε) ^ (5 / 4 : ℂ) * (3 * gaussQ (-(p : ℤ)) q / (2 * q) *
    cuspPoint p q)) * hinv

/-- **Zero-charge points.** For `q ≡ 2 (mod 4)` coprime to `p`, the Gauss sum vanishes and
`κ(y₀+ε) → 0` as `ε ↓ 0`. -/
theorem tendsto_thetaBoundarySource_cusp_zero_charge {p q : ℕ} (hp : 0 < p) (hq : q % 4 = 2)
    (hpq : Nat.Coprime p q) :
    Tendsto (fun ε : ℝ => thetaBoundarySource (cuspPoint p q + ε)) (𝓝[>] 0) (𝓝 0) := by
  have hq0 : 0 < q := by omega
  have hG : gaussQ (-(p : ℤ)) q = 0 := gaussQ_eq_zero_of_mod_four_eq_two hq
    (isCoprime_neg_natCast hpq)
  obtain ⟨K, c, hK, hc, hb⟩ := exists_norm_deriv_cuspRemainder_le p q hq0
  have hslit := cuspPoint_mem_slitPlane p q hp hq0
  -- `ε^{-3} e^{-c/ε} → 0`
  have hdecay : Tendsto (fun ε : ℝ => (1 / ε) ^ 3 * Real.exp (-(c / ε))) (𝓝[>] 0) (𝓝 0) := by
    have hinf : Tendsto (fun ε : ℝ => c / ε) (𝓝[>] 0) atTop :=
      (tendsto_inv_nhdsGT_zero).const_mul_atTop hc |>.congr fun ε => by ring
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp hinf
    have h' := h.const_mul (1 / c ^ 3)
    rw [mul_zero] at h'
    refine h'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0 : ℝ) < ε := hε
    simp only [Function.comp]
    field_simp
  set B := 2 * (‖cuspPoint p q‖ + 1) * (8 * K) + 3 * (2 * K)
  have hbound : Tendsto (fun ε : ℝ => B * ((1 / ε) ^ 3 * Real.exp (-(c / ε)))) (𝓝[>] 0) (𝓝 0) := by
    simpa using hdecay.const_mul B
  have hrest : Tendsto (fun ε : ℝ => 2 * (cuspPoint p q + ε) * deriv (deriv (cuspRemainder p q)) ε +
      3 * deriv (cuspRemainder p q) ε) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    obtain ⟨hε0, hε1⟩ := hε
    obtain ⟨h1, h2⟩ := hb ε hε0 hε1.le
    have hsq : ε ≤ Real.sqrt ε := by
      calc ε = Real.sqrt ε * Real.sqrt ε := (Real.mul_self_sqrt hε0.le).symm
        _ ≤ Real.sqrt ε * 1 := mul_le_mul_of_nonneg_left
            (Real.sqrt_le_one.mpr hε1.le) (Real.sqrt_nonneg _)
        _ = Real.sqrt ε := mul_one _
    have hs0 : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε0
    have hinvs : (Real.sqrt ε)⁻¹ ≤ 1 / ε := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hε0 hsq
    have hyε : ‖cuspPoint p q + ε‖ ≤ ‖cuspPoint p q‖ + 1 := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]; linarith
    have he := (Real.exp_pos (-(c / ε))).le
    have hq1 : (1 : ℝ) / ε ^ 2 ≤ (1 / ε) ^ 2 := by rw [one_div_pow]
    have hA : 8 * K * (Real.sqrt ε)⁻¹ * Real.exp (-(c / ε)) / ε ^ 2 ≤
        8 * K * ((1 / ε) ^ 3 * Real.exp (-(c / ε))) := by
      rw [div_eq_mul_one_div, show (1 / ε) ^ 3 = (1 / ε) * (1 / ε) ^ 2 by ring]
      have := mul_le_mul hinvs (le_refl (Real.exp (-(c / ε)))) he (by positivity)
      calc 8 * K * (Real.sqrt ε)⁻¹ * Real.exp (-(c / ε)) * (1 / ε ^ 2)
          = 8 * K * ((Real.sqrt ε)⁻¹ * Real.exp (-(c / ε))) * (1 / ε) ^ 2 := by rw [one_div_pow]; ring
        _ ≤ 8 * K * ((1 / ε) * Real.exp (-(c / ε))) * (1 / ε) ^ 2 := by gcongr
        _ = _ := by ring
    have hB2 : 2 * K * (Real.sqrt ε)⁻¹ * Real.exp (-(c / ε)) / ε ≤
        2 * K * ((1 / ε) ^ 3 * Real.exp (-(c / ε))) := by
      have hε1' : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε0]; linarith
      calc 2 * K * (Real.sqrt ε)⁻¹ * Real.exp (-(c / ε)) / ε
          = 2 * K * ((Real.sqrt ε)⁻¹ * (1 / ε) * Real.exp (-(c / ε))) := by field_simp
        _ ≤ 2 * K * ((1 / ε) * (1 / ε) * Real.exp (-(c / ε))) := by gcongr
        _ ≤ 2 * K * ((1 / ε) * (1 / ε) * (1 / ε) * Real.exp (-(c / ε))) := by
            gcongr; nlinarith [mul_pos (one_div_pos.mpr hε0) (one_div_pos.mpr hε0)]
        _ = _ := by ring
    calc ‖2 * (cuspPoint p q + ε) * deriv (deriv (cuspRemainder p q)) ε +
          3 * deriv (cuspRemainder p q) ε‖
        ≤ 2 * (‖cuspPoint p q‖ + 1) * (8 * K * ((1 / ε) ^ 3 * Real.exp (-(c / ε)))) +
          3 * (2 * K * ((1 / ε) ^ 3 * Real.exp (-(c / ε)))) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul, norm_mul, Complex.norm_ofNat]
            exact mul_le_mul (mul_le_mul_of_nonneg_left hyε (by norm_num)) (h2.trans hA)
              (norm_nonneg _) (by positivity)
          · rw [norm_mul, Complex.norm_ofNat]
            exact mul_le_mul_of_nonneg_left (h1.trans hB2) (by norm_num)
      _ = B * ((1 / ε) ^ 3 * Real.exp (-(c / ε))) := by dsimp only [B]; ring
  have hpow : Tendsto (fun ε : ℝ => (cuspPoint p q + ε) ^ (5 / 4 : ℂ)) (𝓝[>] 0)
      (𝓝 (cuspPoint p q ^ (5 / 4 : ℂ))) := by
    have hc' : Tendsto (fun ε : ℝ => cuspPoint p q + (ε : ℂ)) (𝓝 0) (𝓝 (cuspPoint p q)) := by
      have h : Continuous (fun ε : ℝ => cuspPoint p q + (ε : ℂ)) := by fun_prop
      simpa using h.tendsto 0
    exact ((continuousAt_cpow_const hslit).tendsto.comp hc').mono_left nhdsWithin_le_nhds
  have hmain := hpow.mul hrest
  rw [mul_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [thetaBoundarySource_cusp_eq p q hq0 hε, hG]
  simp

/-- The endpoint `y₀ = i` of the unit-circle arc is a zero-charge point: `κ(i + ε) → 0`. -/
theorem tendsto_thetaBoundarySource_I_add :
    Tendsto (fun ε : ℝ => thetaBoundarySource (I + ε)) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_thetaBoundarySource_cusp_zero_charge (p := 1) (q := 2) one_pos (by norm_num)
    (by norm_num)
  have hI : cuspPoint 1 2 = I := by unfold cuspPoint; push_cast; ring
  simpa [hI] using h

/-- At odd-denominator cusps the boundary source is unbounded. -/
theorem tendsto_norm_thetaBoundarySource_cusp {p q : ℕ} (hp : 0 < p) (hq : q % 2 = 1)
    (hpq : Nat.Coprime p q) :
    Tendsto (fun ε : ℝ => ‖thetaBoundarySource (cuspPoint p q + ε)‖) (𝓝[>] 0) atTop := by
  have hq0 : 0 < q := by omega
  have hL := (tendsto_thetaBoundarySource_cusp p q hp hq0).norm
  have hLpos : 0 < ‖cuspAmplitude p q‖ := norm_pos_iff.mpr (cuspAmplitude_ne_zero hp hq hpq)
  have hinv : Tendsto (fun ε : ℝ => (ε ^ 2 * Real.sqrt ε)⁻¹) (𝓝[>] 0) atTop := by
    refine Filter.Tendsto.inv_tendsto_nhdsGT_zero ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Continuous (fun ε : ℝ => ε ^ 2 * Real.sqrt ε) := by fun_prop
      simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : (0 : ℝ) < ε := hε
      exact mul_pos (by positivity) (Real.sqrt_pos.mpr hε0)
  refine (hinv.atTop_mul_pos hLpos hL).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0 : ℝ) < ε := hε
  rw [norm_mul, norm_ofReal_cpow_five_halves hε0]
  have : 0 < ε ^ 2 * Real.sqrt ε := mul_pos (by positivity) (Real.sqrt_pos.mpr hε0)
  field_simp

/-- Odd-denominator cusp points are dense on the upper clock boundary. -/
theorem exists_cusp_log_near (a δ : ℝ) (hδ : 0 < δ) :
    ∃ p m : ℕ, 0 < p ∧ ¬ 3 ∣ p ∧ |Real.log (2 * p / (3 ^ m : ℕ)) / 2 - a| < δ := by
  set u := Real.exp (2 * a - 2 * δ)
  set v := Real.exp (2 * a + 2 * δ)
  have hu : 0 < u := Real.exp_pos _
  have huv : u < v := Real.exp_lt_exp.mpr (by linarith)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (4 / (v - u)) (by norm_num : (1 : ℝ) < 3)
  set q : ℝ := ((3 ^ m : ℕ) : ℝ)
  have hq : q = 3 ^ m := by simp [q]
  have hq0 : 0 < q := by rw [hq]; positivity
  have hwide : 4 < q * (v - u) := by
    rw [hq]; rwa [div_lt_iff₀ (by linarith)] at hm
  set p₀ := ⌊u * q / 2⌋₊ + 1
  have hp₀lo : u * q / 2 < p₀ := by push_cast [p₀]; exact Nat.lt_floor_add_one _
  have hp₀hi : (p₀ : ℝ) ≤ u * q / 2 + 1 := by
    have := Nat.floor_le (by positivity : 0 ≤ u * q / 2)
    push_cast [p₀]; linarith
  have hgood : ∀ p : ℕ, u * q / 2 < p → (p : ℝ) < v * q / 2 →
      |Real.log (2 * p / (3 ^ m : ℕ)) / 2 - a| < δ := by
    intro p h1 h2
    have hp : (0 : ℝ) < p := lt_of_le_of_lt (by positivity) h1
    have hlo : u < 2 * p / q := by rw [lt_div_iff₀ hq0]; linarith
    have hhi : 2 * p / q < v := by rw [div_lt_iff₀ hq0]; linarith
    have hpos : 0 < 2 * (p : ℝ) / q := by positivity
    have l1 := Real.log_lt_log hu hlo
    have l2 := Real.log_lt_log hpos hhi
    rw [Real.log_exp] at l1 l2
    rw [abs_lt]; constructor <;> linarith
  by_cases h3 : 3 ∣ p₀
  · refine ⟨p₀ + 1, m, by omega, fun h => ?_, hgood _ (by push_cast; linarith) (by push_cast; linarith)⟩
    omega
  · exact ⟨p₀, m, by omega, h3, hgood _ hp₀lo (by linarith)⟩

theorem cuspPoint_eq_I_mul (p q : ℕ) : cuspPoint p q = I * ((2 * p / q : ℝ) : ℂ) := by
  unfold cuspPoint; push_cast; ring

theorem log_cuspPoint_re {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (Complex.log (cuspPoint p q)).re = Real.log (2 * p / q) := by
  have hr : (0 : ℝ) < 2 * p / q := by positivity
  rw [Complex.log_re, cuspPoint_eq_I_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr]

theorem log_cuspPoint_im {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (Complex.log (cuspPoint p q)).im = Real.pi / 2 := by
  have hr : (0 : ℝ) < 2 * p / q := by positivity
  rw [Complex.log_im, cuspPoint_eq_I_mul, mul_comm, Complex.arg_real_mul _ hr, Complex.arg_I]

/-- **Upper natural boundary.** The completed theta source has no holomorphic continuation across
any point of `Im z = π/4`. -/
theorem not_exists_continuation_thetaCuspStripSource_upper {x₀ : ℂ} (hx₀ : x₀.im = Real.pi / 4) :
    ¬ ∃ F : ℂ → ℂ, AnalyticAt ℂ F x₀ ∧
      ∀ᶠ z in 𝓝 x₀, z ∈ thetaCuspStrip → F z = thetaCuspStripSource z := by
  rintro ⟨F, hF, heq⟩
  have hb : ∀ᶠ z in 𝓝 x₀, ‖F z‖ < ‖F x₀‖ + 1 :=
    hF.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (heq.and hb)
  obtain ⟨p, m, hp, h3, hnear⟩ := exists_cusp_log_near x₀.re (δ / 2) (by positivity)
  set q := 3 ^ m
  have hq0 : 0 < q := by positivity
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
  have hpq : Nat.Coprime p q :=
    Nat.Coprime.pow_right m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  set x₁ := Complex.log (cuspPoint p q) / 2
  have hx₁ : dist x₁ x₀ < δ / 2 := by
    rw [Complex.dist_eq, show x₁ - x₀ = ((Real.log (2 * p / q) / 2 - x₀.re : ℝ) : ℂ) by
      apply Complex.ext
      · simp only [x₁, Complex.sub_re, Complex.div_ofNat_re, log_cuspPoint_re hp hq0,
          Complex.ofReal_re]
      · simp only [x₁, Complex.sub_im, Complex.div_ofNat_im, log_cuspPoint_im hp hq0, hx₀,
          Complex.ofReal_im]
        ring]
    rw [Complex.norm_real, Real.norm_eq_abs]
    simpa [q] using hnear
  have hslit := cuspPoint_mem_slitPlane p q hp hq0
  have hpath : Tendsto (fun ε : ℝ => Complex.log (cuspPoint p q + ε) / 2) (𝓝[>] 0) (𝓝 x₁) := by
    have hc : Tendsto (fun ε : ℝ => cuspPoint p q + (ε : ℂ)) (𝓝 0) (𝓝 (cuspPoint p q)) := by
      have h : Continuous (fun ε : ℝ => cuspPoint p q + (ε : ℂ)) := by fun_prop
      simpa using h.tendsto 0
    exact (((continuousAt_clog hslit).tendsto.comp hc).div_const 2).mono_left nhdsWithin_le_nhds
  have hnearev : ∀ᶠ ε : ℝ in 𝓝[>] 0, dist (Complex.log (cuspPoint p q + ε) / 2) x₀ < δ := by
    filter_upwards [hpath (Metric.ball_mem_nhds x₁ (by positivity : (0 : ℝ) < δ / 2))] with ε hε
    have := dist_triangle (Complex.log (cuspPoint p q + ε) / 2) x₁ x₀
    have hε' : dist (Complex.log (cuspPoint p q + ε) / 2) x₁ < δ / 2 := hε
    linarith
  have hunb := (tendsto_norm_thetaBoundarySource_cusp hp hqodd hpq).eventually_gt_atTop
    (‖F x₀‖ + 1)
  obtain ⟨ε, ⟨hε, hdist⟩, hbig⟩ := ((eventually_mem_nhdsWithin.and hnearev).and hunb).exists
  have hε0 : (0 : ℝ) < ε := hε
  set z := Complex.log (cuspPoint p q + ε) / 2
  have hne : cuspPoint p q + ε ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [cuspPoint_re] at this; linarith
  have hre : 0 < (cuspPoint p q + ε).re := by simp [cuspPoint_re, hε0]
  have hzstrip : z ∈ thetaCuspStrip := by
    show |z.im| < Real.pi / 4
    have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
    simp only [z, Complex.div_ofNat_im, Complex.log_im]
    rw [abs_div]; norm_num; linarith
  have hexp : cexp (2 * z) = cuspPoint p q + ε := by
    simp only [z]; rw [show 2 * (Complex.log (cuspPoint p q + ε) / 2) =
      Complex.log (cuspPoint p q + ε) by ring, Complex.exp_log hne]
  obtain ⟨hFz, hbz⟩ := hball hdist
  have hk := thetaCuspStripSource_eq_boundarySource hzstrip
  rw [hexp] at hk
  rw [hFz hzstrip, hk] at hbz
  linarith

theorem thetaCuspComplexTerm_conj (z : ℂ) (n : ℕ) :
    thetaCuspComplexTerm ((starRingEnd ℂ) z) n = (starRingEnd ℂ) (thetaCuspComplexTerm z n) := by
  unfold thetaCuspComplexTerm thetaCuspComplexSeed
  simp only [map_mul, map_sub, map_pow, map_neg, map_natCast, map_ofNat, Complex.conj_ofReal,
    ← Complex.exp_conj, map_div₀]

theorem thetaCuspStripSource_conj (z : ℂ) :
    thetaCuspStripSource ((starRingEnd ℂ) z) = (starRingEnd ℂ) (thetaCuspStripSource z) := by
  unfold thetaCuspStripSource
  rw [Complex.conj_tsum]
  exact tsum_congr fun n => thetaCuspComplexTerm_conj z n

/-- **Natural boundary.** The completed theta source admits no holomorphic continuation across
any boundary point of its strip `|Im z| < π/4`. -/
theorem not_exists_continuation_thetaCuspStripSource {x₀ : ℂ} (hx₀ : |x₀.im| = Real.pi / 4) :
    ¬ ∃ F : ℂ → ℂ, AnalyticAt ℂ F x₀ ∧
      ∀ᶠ z in 𝓝 x₀, z ∈ thetaCuspStrip → F z = thetaCuspStripSource z := by
  rcases abs_eq (by positivity : (0 : ℝ) ≤ Real.pi / 4) |>.mp hx₀ with h | h
  · exact not_exists_continuation_thetaCuspStripSource_upper h
  · rintro ⟨F, hF, heq⟩
    apply not_exists_continuation_thetaCuspStripSource_upper (x₀ := (starRingEnd ℂ) x₀)
      (by simp [h])
    refine ⟨(starRingEnd ℂ) ∘ F ∘ (starRingEnd ℂ), ?_, ?_⟩
    · rw [Complex.analyticAt_iff_eventually_differentiableAt] at hF ⊢
      have hc : Tendsto (starRingEnd ℂ) (𝓝 ((starRingEnd ℂ) x₀)) (𝓝 x₀) := by
        simpa using (Complex.continuous_conj.tendsto ((starRingEnd ℂ) x₀))
      filter_upwards [hc.eventually hF] with z hz
      have := hz.conj_conj
      simpa using this
    · have hc : Tendsto (starRingEnd ℂ) (𝓝 ((starRingEnd ℂ) x₀)) (𝓝 x₀) := by
        simpa using (Complex.continuous_conj.tendsto ((starRingEnd ℂ) x₀))
      filter_upwards [hc.eventually heq] with z hz hzs
      have hzs' : (starRingEnd ℂ) z ∈ thetaCuspStrip := by
        have h' : |z.im| < Real.pi / 4 := hzs
        show |((starRingEnd ℂ) z).im| < Real.pi / 4
        simpa using h'
      simp only [Function.comp, hz hzs', ← thetaCuspStripSource_conj, Complex.conj_conj]

end RHTower
