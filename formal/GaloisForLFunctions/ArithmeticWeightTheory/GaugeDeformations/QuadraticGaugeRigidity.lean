import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PositiveSeriesBoundary
import GaloisForLFunctions.ArithmeticWeightTheory.EulerDeformationsOfZetaAreIsozeric
import GaloisForLFunctions.HTGeometry.HolomorphicRealTaylor
import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative
import GaloisForLFunctions.RHTower.ZetaRealStrip
import GaloisForLFunctions.RHTower.Reflection

/-!
# Quadratic rigidity of pole-regularized gauge fibres

For `1/2 ≤ c < 1`, let `U` be holomorphic on `Re s > c` and agree with
`(s-1) F_x(s)` on `Re s > 1`. Real nonvanishing of `U` is equivalent to
convergence of `Σ_p |χ_x(p)-1|² p^(-σ)` for every `σ > c`.

Under these equivalent conditions, the product of `U` and its Schwarz
conjugate is `Z² exp(H)`, where `Z` is the entire residue factor of ζ and
`H` is holomorphic. Consequently conjugate-paired zero multiplicities and
all zero-free half-planes contained in `Re s > c` agree with those of ζ.
Divergent quadratic
perturbations force real zeros in any such continuation.

The positive prime defect enters through a cleared logarithmic derivative.
Landau's theorem forces its convergence; analytic uniqueness then gives
the exact exponential identity across complex zeros.
-/

open Complex Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- The nonnegative prime defect from the trivial Euler fibre. -/
def primeDefect (x : GaugeTorus) (p : Nat.Primes) : ℝ := 1 - (twist x p).re

def primeFrequency (p : Nat.Primes) : ℝ := Real.log (p : ℕ)

def primeDefectSeries (x : GaugeTorus) : ℂ → ℂ :=
  gdSeries (primeDefect x) primeFrequency

def primeDefectDerivativeSeries (x : GaugeTorus) : ℂ → ℂ :=
  gdSeries (fun p => primeDefect x p * primeFrequency p) primeFrequency

/-- The paired prime-power remainder is analytic beyond the critical line. -/
def pairedRemainder (x : GaugeTorus) (s : ℂ) : ℂ :=
  hullRem s (twist x) + hullRem s (twist (-x)) - 2 * hullRem s (twist 0)

theorem twist_neg_eq_conj (x : GaugeTorus) (n : ℕ) :
    twist (-x) n = conj (twist x n) := by
  have hn : twist x n ≠ 0 := by
    intro h
    have hh := norm_twist x n
    rw [h, norm_zero] at hh
    exact zero_ne_one hh
  apply mul_left_cancel₀ hn
  rw [twist_mul_conj_self, ← twist_add, add_neg_cancel, twist_trivial]

theorem primeDefect_nonneg (x : GaugeTorus) (p : Nat.Primes) : 0 ≤ primeDefect x p := by
  have hh := Complex.re_le_norm (twist x p)
  rw [norm_twist] at hh
  exact sub_nonneg.mpr hh

theorem primeDefect_le_two (x : GaugeTorus) (p : Nat.Primes) : primeDefect x p ≤ 2 := by
  have hh := (neg_le_abs (twist x p).re).trans (Complex.abs_re_le_norm (twist x p))
  rw [norm_twist] at hh
  dsimp [primeDefect]
  linarith only [hh]

theorem norm_twist_sub_one_sq (x : GaugeTorus) (p : Nat.Primes) :
    ‖twist x p - 1‖ ^ 2 = 2 * primeDefect x p := by
  have hh := congrArg (fun r : ℝ => r ^ 2) (norm_twist x p)
  rw [Complex.sq_norm, Complex.normSq_apply] at hh
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
  dsimp [primeDefect]
  nlinarith only [hh]

theorem primeFrequency_nonneg (p : Nat.Primes) : 0 ≤ primeFrequency p :=
  Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)

theorem prime_exp_decay (p : Nat.Primes) (σ : ℝ) :
    Real.exp (-(σ * primeFrequency p)) = ((p : ℕ) : ℝ) ^ (-σ) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast p.2.pos)]
  congr 1
  dsimp [primeFrequency]
  ring

theorem prime_cexp_decay (p : Nat.Primes) (s : ℂ) :
    cexp (-(s * (primeFrequency p : ℂ))) = ((p : ℕ) : ℂ) ^ (-s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast p.2.ne_zero)]
  have hl : (primeFrequency p : ℂ) = Complex.log ((p : ℕ) : ℂ) := by
    simpa only [primeFrequency, Complex.ofReal_natCast] using
      (Complex.ofReal_log (show (0 : ℝ) ≤ (p : ℕ) by positivity))
  rw [hl]
  congr 1
  ring

theorem primeDefectSeries_eq_tsum (x : GaugeTorus) (s : ℂ) :
    primeDefectSeries x s =
      ∑' p : Nat.Primes, (primeDefect x p : ℂ) * ((p : ℕ) : ℂ) ^ (-s) := by
  exact tsum_congr fun p => by rw [prime_cexp_decay]

theorem summable_primeDefect (x : GaugeTorus) {σ : ℝ} (hσ : 1 < σ) :
    Summable (gdTwistTerm (primeDefect x) primeFrequency σ 0) := by
  refine Summable.of_nonneg_of_le
    (gdTwistTerm_nonneg (primeDefect_nonneg x) primeFrequency_nonneg σ 0)
    (fun p => ?_) ((summable_primes_rpow (show -σ < -1 by linarith only [hσ])).mul_left 2)
  simp only [gdTwistTerm, pow_zero, mul_one, prime_exp_decay]
  exact mul_le_mul_of_nonneg_right (primeDefect_le_two x p) (by positivity)

theorem summable_primeDefectDerivative (x : GaugeTorus) {σ : ℝ} (hσ : 1 < σ) :
    Summable (gdTwistTerm (fun p => primeDefect x p * primeFrequency p) primeFrequency σ 0) := by
  have hm : 1 < (1 + σ) / 2 := by linarith only [hσ]
  have hh : 0 < σ - (1 + σ) / 2 := by linarith only [hσ]
  have hsum := summable_gdTwistTerm (primeDefect_nonneg x) primeFrequency_nonneg
    (summable_primeDefect x hm) hh 1
  rw [show (1 + σ) / 2 + (σ - (1 + σ) / 2) = σ by ring] at hsum
  unfold gdTwistTerm at hsum ⊢
  simpa only [pow_one, pow_zero, mul_one] using hsum

theorem analyticOnNhd_primeDefectSeries (x : GaugeTorus) :
    AnalyticOnNhd ℂ (primeDefectSeries x) {s : ℂ | 1 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  change 1 < s.re at hs
  have hm : 1 < (1 + s.re) / 2 := by linarith only [hs]
  exact (_root_.RHTower.differentiableAt_gdSeries (primeDefect_nonneg x) primeFrequency_nonneg
    (summable_primeDefect x hm) (by linarith only [hs])).differentiableWithinAt

theorem analyticOnNhd_pairedRemainder (x : GaugeTorus) :
    AnalyticOnNhd ℂ (pairedRemainder x) rightHalf := by
  exact ((analyticOnNhd_hullRem (norm_twist_prime x)).add
    (analyticOnNhd_hullRem (norm_twist_prime (-x)))).sub
    (analyticOnNhd_const.mul (analyticOnNhd_hullRem (norm_twist_prime 0)))

/-- The conjugate pair sees the squared distance of the prime phase from one. -/
theorem paired_deformationExponent (x : GaugeTorus) {s : ℂ} (hs : 1 < s.re) :
    deformationExponent x s + deformationExponent (-x) s =
      -2 * primeDefectSeries x s + pairedRemainder x s := by
  have hsum (y : GaugeTorus) : Summable fun p : Nat.Primes =>
      (twist y p - 1) * ((p : ℕ) : ℂ) ^ (-s) := by
    refine ((summable_eulerVar (norm_twist_prime y) hs).sub
      (summable_eulerVar (norm_twist_prime 0) hs)).congr fun p => ?_
    simp only [eulerVar, powCoeff, twist_trivial]
    ring
  have hp : deformationPrimeSum x s + deformationPrimeSum (-x) s =
      -2 * primeDefectSeries x s := by
    unfold deformationPrimeSum
    rw [← (hsum x).tsum_add (hsum (-x)), primeDefectSeries_eq_tsum, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    have hc : twist x p + twist (-x) p - 2 = (-2 : ℂ) * (primeDefect x p : ℂ) := by
      rw [twist_neg_eq_conj]
      apply Complex.ext <;> simp [primeDefect]
      ring
    calc
      _ = (twist x p + twist (-x) p - 2) * ((p : ℕ) : ℂ) ^ (-s) := by ring
      _ = _ := by rw [hc]; ring
  dsimp [deformationExponent, pairedRemainder]
  rw [show deformationPrimeSum x s + hullRem s (twist x) - hullRem s (twist 0) +
      (deformationPrimeSum (-x) s + hullRem s (twist (-x)) - hullRem s (twist 0)) =
      (deformationPrimeSum x s + deformationPrimeSum (-x) s) +
        (hullRem s (twist x) + hullRem s (twist (-x)) - 2 * hullRem s (twist 0)) by ring]
  rw [hp]

/-- Pairing opposite gauge points removes the linear phase and leaves a
nonnegative prime defect plus an analytic prime-power remainder. -/
theorem gaugeFibre_pair_eq (x : GaugeTorus) {s : ℂ} (hs : 1 < s.re) :
    gaugeFibre x s * gaugeFibre (-x) s =
      riemannZeta s ^ 2 * cexp (-2 * primeDefectSeries x s + pairedRemainder x s) := by
  rw [gaugeFibre_eq_zeta_mul_exp x hs, gaugeFibre_eq_zeta_mul_exp (-x) hs]
  calc
    _ = riemannZeta s ^ 2 * cexp (deformationExponent x s + deformationExponent (-x) s) := by
      rw [Complex.exp_add]
      ring
    _ = _ := by rw [paired_deformationExponent x hs]

/-- Differentiating the prime defect introduces the positive frequency weight. -/
theorem deriv_primeDefectSeries (x : GaugeTorus) {s : ℂ} (hs : 1 < s.re) :
    deriv (primeDefectSeries x) s = -primeDefectDerivativeSeries x s := by
  let σ₀ : ℝ := (1 + s.re) / 2
  have hσ₀ : 1 < σ₀ := by dsimp [σ₀]; linarith only [hs]
  have hs₀ : σ₀ < s.re := by dsimp [σ₀]; linarith only [hs]
  let F : Nat.Primes → ℂ → ℂ := fun p z =>
    (primeDefect x p : ℂ) * cexp (-(z * (primeFrequency p : ℂ)))
  have hd (p : Nat.Primes) (z : ℂ) : HasDerivAt (F p)
      (-((primeDefect x p * primeFrequency p : ℝ) : ℂ) *
        cexp (-(z * (primeFrequency p : ℂ)))) z := by
    have hh := (((hasDerivAt_id z).mul_const (primeFrequency p : ℂ)).neg.cexp).const_mul
      (primeDefect x p : ℂ)
    apply hh.congr_deriv
    change (primeDefect x p : ℂ) * (cexp (-(z * (primeFrequency p : ℂ))) *
      -(1 * (primeFrequency p : ℂ))) = _
    push_cast
    ring
  have hF : ∀ p, DifferentiableOn ℂ (F p) {z : ℂ | σ₀ < z.re} :=
    fun p z _ => (hd p z).differentiableAt.differentiableWithinAt
  have hbound (p : Nat.Primes) (z : ℂ) (hz : σ₀ < z.re) :
      ‖F p z‖ ≤ gdTwistTerm (primeDefect x) primeFrequency σ₀ 0 p := by
    dsimp only [F]
    rw [norm_gd_term (primeDefect_nonneg x) primeFrequency_nonneg]
    simp only [gdTwistTerm, pow_zero, mul_one]
    apply mul_le_mul_of_nonneg_left _ (primeDefect_nonneg x p)
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right hz.le (primeFrequency_nonneg p))
  have hsum := (hasSum_iteratedDeriv_of_summable_bound
    (isOpen_lt continuous_const Complex.continuous_re) hF
    (summable_primeDefect x hσ₀) hbound).2 1 s hs₀
  simp only [iteratedDeriv_one] at hsum
  have ht : (fun p => deriv (F p) s) = fun p =>
      -(((primeDefect x p * primeFrequency p : ℝ) : ℂ) *
        cexp (-(s * (primeFrequency p : ℂ)))) := by
    funext p
    rw [(hd p s).deriv]
    ring
  rw [ht] at hsum
  have heq := hsum.tsum_eq
  rw [tsum_neg] at heq
  exact heq.symm

open _root_.RHTower

/-- The exponent in the paired Euler identity. -/
def pairedExponent (x : GaugeTorus) (s : ℂ) : ℂ :=
  -2 * primeDefectSeries x s + pairedRemainder x s

/-- The denominator cleared from the paired logarithmic derivative. -/
def pairedDenominator (U V : ℂ → ℂ) (s : ℂ) : ℂ :=
  2 * zetaResidueFactor s * U s * V s

/-- The analytic numerator paired with the positive prime-frequency series. -/
def pairedNumerator (x : GaugeTorus) (U V : ℂ → ℂ) (s : ℂ) : ℂ :=
  zetaResidueFactor s * (deriv U s * V s + U s * deriv V s) -
    2 * deriv zetaResidueFactor s * U s * V s -
    deriv (pairedRemainder x) s * zetaResidueFactor s * U s * V s

/-- The entire residue factor is nonzero on the positive real axis. -/
theorem zetaResidueFactor_real_ne_zero {t : ℝ} (ht : 0 < t) :
    zetaResidueFactor (t : ℂ) ≠ 0 := by
  by_cases ht1 : t = 1
  · subst t
    simp only [Complex.ofReal_one, zetaResidueFactor_one, ne_eq, one_ne_zero, not_false_eq_true]
  have htC : (t : ℂ) ≠ 1 := by exact_mod_cast ht1
  rw [zetaResidueFactor_of_ne htC]
  refine mul_ne_zero (sub_ne_zero.mpr htC) ?_
  rcases lt_or_gt_of_ne ht1 with hlt | hgt
  · exact riemannZeta_real_strip_ne_zero ht hlt
  · exact riemannZeta_ne_zero_of_one_lt_re hgt

/-- Pairing opposite regularized Euler fibres gives the paired exponential
identity in the half-plane of absolute convergence. -/
theorem regularized_pair_eq {x : GaugeTorus} {U V : ℂ → ℂ}
    (hUeq : ∀ s : ℂ, 1 < s.re → U s = (s - 1) * gaugeFibre x s)
    (hVeq : ∀ s : ℂ, 1 < s.re → V s = (s - 1) * gaugeFibre (-x) s)
    {s : ℂ} (hs : 1 < s.re) :
    U s * V s = zetaResidueFactor s ^ 2 * cexp (pairedExponent x s) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  rw [hUeq s hs, hVeq s hs, zetaResidueFactor_of_ne hs1]
  calc
    _ = (s - 1) ^ 2 * (gaugeFibre x s * gaugeFibre (-x) s) := by ring
    _ = _ := by rw [gaugeFibre_pair_eq x hs]; dsimp [pairedExponent]; ring

/-- The logarithmic derivative identity is cleared before continuation, so
complex zeros never require division. -/
theorem cleared_pair_identity {x : GaugeTorus} {c : ℝ} (hc : c < 1)
    {U V : ℂ → ℂ}
    (hU : AnalyticOnNhd ℂ U {s : ℂ | c < s.re})
    (hV : AnalyticOnNhd ℂ V {s : ℂ | c < s.re})
    (hUeq : ∀ s : ℂ, 1 < s.re → U s = (s - 1) * gaugeFibre x s)
    (hVeq : ∀ s : ℂ, 1 < s.re → V s = (s - 1) * gaugeFibre (-x) s)
    {s : ℂ} (hs : 1 < s.re) :
    pairedDenominator U V s * primeDefectDerivativeSeries x s =
      pairedNumerator x U V s := by
  have hsc : c < s.re := hc.trans hs
  have hZ := (differentiable_zetaResidueFactor s).hasDerivAt
  have hE := ((analyticOnNhd_primeDefectSeries x) s hs).differentiableAt.hasDerivAt
  rw [deriv_primeDefectSeries x hs] at hE
  have hR := ((analyticOnNhd_pairedRemainder x) s
    (show s ∈ PrimeTorusTheory.rightHalf by change 1 / 2 < s.re; linarith only [hs])).differentiableAt.hasDerivAt
  have hH : HasDerivAt (pairedExponent x)
      (2 * primeDefectDerivativeSeries x s + deriv (pairedRemainder x) s) s := by
    exact ((hE.const_mul (-2)).add hR).congr_deriv (by ring)
  have hright := (hZ.pow 2).mul hH.cexp
  have hleft := ((hU s hsc).differentiableAt.hasDerivAt).mul
    ((hV s hsc).differentiableAt.hasDerivAt)
  have heq : (fun z => U z * V z) =ᶠ[𝓝 s]
      (fun z => zetaResidueFactor z ^ 2 * cexp (pairedExponent x z)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
      with z hz
    exact regularized_pair_eq hUeq hVeq hz
  have hd := hleft.unique (hright.congr_of_eventuallyEq heq)
  norm_num only [Pi.pow_apply] at hd
  have hv := regularized_pair_eq hUeq hVeq hs
  dsimp [pairedDenominator, pairedNumerator]
  linear_combination -zetaResidueFactor s * hd +
    (2 * deriv zetaResidueFactor s + zetaResidueFactor s *
      (2 * primeDefectDerivativeSeries x s + deriv (pairedRemainder x) s)) * hv

/-- Real nonvanishing of the paired continuation forces convergence of
its nonnegative prime-frequency defect throughout the half-plane. -/
theorem summable_primeDefectDerivative_of_pair {x : GaugeTorus} {c : ℝ}
    (hc₀ : 1 / 2 ≤ c) (hc₁ : c < 1) {U V : ℂ → ℂ}
    (hU : AnalyticOnNhd ℂ U {s : ℂ | c < s.re})
    (hV : AnalyticOnNhd ℂ V {s : ℂ | c < s.re})
    (hUeq : ∀ s : ℂ, 1 < s.re → U s = (s - 1) * gaugeFibre x s)
    (hVeq : ∀ s : ℂ, 1 < s.re → V s = (s - 1) * gaugeFibre (-x) s)
    (hUne : ∀ t : ℝ, c < t → U (t : ℂ) ≠ 0)
    (hVne : ∀ t : ℝ, c < t → V (t : ℂ) ≠ 0)
    {σ : ℝ} (hσ : c < σ) :
    Summable (gdTwistTerm (fun p => primeDefect x p * primeFrequency p)
      primeFrequency σ 0) := by
  have ho : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hZ : AnalyticOnNhd ℂ zetaResidueFactor {s : ℂ | c < s.re} :=
    differentiable_zetaResidueFactor.differentiableOn.analyticOnNhd ho
  have hR : AnalyticOnNhd ℂ (pairedRemainder x) {s : ℂ | c < s.re} :=
    (analyticOnNhd_pairedRemainder x).mono (fun s hs => hc₀.trans_lt hs)
  have hUd := hU.deriv
  have hVd := hV.deriv
  have hZd := hZ.deriv
  have hRd := hR.deriv
  apply summable_of_cleared_identity
    (fun p => mul_nonneg (primeDefect_nonneg x p) (primeFrequency_nonneg p))
    primeFrequency_nonneg (summable_primeDefectDerivative x (show (1 : ℝ) < 2 by norm_num))
    (P := pairedDenominator U V) (N := pairedNumerator x U V) _ _ _ _ hσ
  · exact ((analyticOnNhd_const.mul hZ).mul hU).mul hV
  · exact ((hZ.mul ((hUd.mul hV).add (hU.mul hVd))).sub
      (((analyticOnNhd_const.mul hZd).mul hU).mul hV)).sub
      (((hRd.mul hZ).mul hU).mul hV)
  · intro t ht
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (zetaResidueFactor_real_ne_zero (by linarith only [hc₀, ht])))
      (hUne t ht)) (hVne t ht)
  · intro s hs
    exact cleared_pair_identity hc₁ hU hV hUeq hVeq (by linarith only [hs])

/-- A positive lower bound for prime frequencies removes the derivative weight. -/
theorem summable_primeDefect_of_derivative {x : GaugeTorus} {σ : ℝ}
    (hsum : Summable (gdTwistTerm (fun p => primeDefect x p * primeFrequency p)
      primeFrequency σ 0)) :
    Summable (gdTwistTerm (primeDefect x) primeFrequency σ 0) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply Summable.of_nonneg_of_le
    (gdTwistTerm_nonneg (primeDefect_nonneg x) primeFrequency_nonneg σ 0)
    (fun p => ?_) (hsum.div_const (Real.log 2))
  rw [le_div_iff₀ hlog]
  simp only [gdTwistTerm, pow_zero, mul_one]
  have hp : Real.log 2 ≤ primeFrequency p := Real.log_le_log (by norm_num)
    (by exact_mod_cast p.2.two_le)
  have hn : 0 ≤ primeDefect x p * Real.exp (-(σ * primeFrequency p)) :=
    mul_nonneg (primeDefect_nonneg x p) (Real.exp_pos _).le
  nlinarith only [mul_le_mul_of_nonneg_left hp hn]

/-- Convergence at every real abscissa in a half-plane gives holomorphy
of the prime-defect series throughout that half-plane. -/
theorem analyticOnNhd_primeDefectSeries_of_summable {x : GaugeTorus} {c : ℝ}
    (hsum : ∀ σ : ℝ, c < σ → Summable (gdTwistTerm (primeDefect x) primeFrequency σ 0)) :
    AnalyticOnNhd ℂ (primeDefectSeries x) {s : ℂ | c < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  change c < s.re at hs
  have hm : c < (c + s.re) / 2 := by linarith only [hs]
  exact (_root_.RHTower.differentiableAt_gdSeries (primeDefect_nonneg x) primeFrequency_nonneg
    (hsum _ hm) (by linarith only [hs])).differentiableWithinAt

/-- Quadratic prime convergence extends the paired Euler identity across
complex zeros without choosing a logarithm of either fibre. -/
theorem paired_identity_of_defect_summable {x : GaugeTorus} {c : ℝ}
    (hc₀ : 1 / 2 ≤ c) (hc₁ : c < 1) {U V : ℂ → ℂ}
    (hU : AnalyticOnNhd ℂ U {s : ℂ | c < s.re})
    (hV : AnalyticOnNhd ℂ V {s : ℂ | c < s.re})
    (hUeq : ∀ s : ℂ, 1 < s.re → U s = (s - 1) * gaugeFibre x s)
    (hVeq : ∀ s : ℂ, 1 < s.re → V s = (s - 1) * gaugeFibre (-x) s)
    (hsum : ∀ σ : ℝ, c < σ → Summable (gdTwistTerm (primeDefect x) primeFrequency σ 0)) :
    AnalyticOnNhd ℂ (pairedExponent x) {s : ℂ | c < s.re} ∧
    ∀ s : ℂ, c < s.re →
      U s * V s = zetaResidueFactor s ^ 2 * cexp (pairedExponent x s) := by
  have hH : AnalyticOnNhd ℂ (pairedExponent x) {s : ℂ | c < s.re} :=
    (analyticOnNhd_const.mul (analyticOnNhd_primeDefectSeries_of_summable hsum)).add
      ((analyticOnNhd_pairedRemainder x).mono (fun s hs => hc₀.trans_lt hs))
  refine ⟨hH, ?_⟩
  have hZ : AnalyticOnNhd ℂ zetaResidueFactor {s : ℂ | c < s.re} :=
    differentiable_zetaResidueFactor.differentiableOn.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)
  have hid : Set.EqOn (fun s => U s * V s)
      (fun s => zetaResidueFactor s ^ 2 * cexp (pairedExponent x s)) {s : ℂ | c < s.re} := by
    apply (hU.mul hV).eqOn_of_preconnected_of_eventuallyEq ((hZ.pow 2).mul hH.cexp)
      (convex_halfSpace_re_gt c).isPreconnected (z₀ := (2 : ℂ))
    · change c < 2
      linarith only [hc₁]
    · filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show 1 < (2 : ℂ).re by norm_num)] with s hs
      exact regularized_pair_eq hUeq hVeq hs
  exact fun s hs => hid hs

/-- Quadratic convergence and the exact exponential identity are forced by
holomorphic continuation and real nonvanishing of the opposite fibres. -/
theorem paired_rigidity {x : GaugeTorus} {c : ℝ}
    (hc₀ : 1 / 2 ≤ c) (hc₁ : c < 1) {U V : ℂ → ℂ}
    (hU : AnalyticOnNhd ℂ U {s : ℂ | c < s.re})
    (hV : AnalyticOnNhd ℂ V {s : ℂ | c < s.re})
    (hUeq : ∀ s : ℂ, 1 < s.re → U s = (s - 1) * gaugeFibre x s)
    (hVeq : ∀ s : ℂ, 1 < s.re → V s = (s - 1) * gaugeFibre (-x) s)
    (hUne : ∀ t : ℝ, c < t → U (t : ℂ) ≠ 0)
    (hVne : ∀ t : ℝ, c < t → V (t : ℂ) ≠ 0) :
    (∀ σ : ℝ, c < σ → Summable (gdTwistTerm (primeDefect x) primeFrequency σ 0)) ∧
    AnalyticOnNhd ℂ (pairedExponent x) {s : ℂ | c < s.re} ∧
    ∀ s : ℂ, c < s.re →
      U s * V s = zetaResidueFactor s ^ 2 * cexp (pairedExponent x s) := by
  have hsum : ∀ σ : ℝ, c < σ →
      Summable (gdTwistTerm (primeDefect x) primeFrequency σ 0) := fun σ hσ =>
    summable_primeDefect_of_derivative
      (summable_primeDefectDerivative_of_pair hc₀ hc₁ hU hV hUeq hVeq hUne hVne hσ)
  exact ⟨hsum, paired_identity_of_defect_summable hc₀ hc₁ hU hV hUeq hVeq hsum⟩

/-- The pair has exactly twice the zero multiplicity of the entire zeta
residue factor, including at points where either fibre vanishes. -/
theorem paired_analyticOrderAt {x : GaugeTorus} {c : ℝ}
    (hc₀ : 1 / 2 ≤ c) (hc₁ : c < 1) {U V : ℂ → ℂ}
    (hU : AnalyticOnNhd ℂ U {s : ℂ | c < s.re})
    (hV : AnalyticOnNhd ℂ V {s : ℂ | c < s.re})
    (hUeq : ∀ s : ℂ, 1 < s.re → U s = (s - 1) * gaugeFibre x s)
    (hVeq : ∀ s : ℂ, 1 < s.re → V s = (s - 1) * gaugeFibre (-x) s)
    (hUne : ∀ t : ℝ, c < t → U (t : ℂ) ≠ 0)
    (hVne : ∀ t : ℝ, c < t → V (t : ℂ) ≠ 0)
    {s : ℂ} (hs : c < s.re) :
    analyticOrderAt U s + analyticOrderAt V s =
      analyticOrderAt zetaResidueFactor s + analyticOrderAt zetaResidueFactor s := by
  obtain ⟨_, hH, hid⟩ := paired_rigidity hc₀ hc₁ hU hV hUeq hVeq hUne hVne
  have hZ : AnalyticAt ℂ zetaResidueFactor s :=
    (differentiable_zetaResidueFactor.analyticAt s)
  have heq : (fun z => U z * V z) =ᶠ[𝓝 s]
      (fun z => (zetaResidueFactor z * zetaResidueFactor z) * cexp (pairedExponent x z)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
      with z hz
    simpa only [pow_two] using hid z hz
  have hord := analyticOrderAt_congr heq
  have hzero : analyticOrderAt (fun z => cexp (pairedExponent x z)) s = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (Complex.exp_ne_zero _))
  have he : AnalyticAt ℂ (fun z => cexp (pairedExponent x z)) s := (hH s hs).cexp
  change analyticOrderAt (U * V) s = analyticOrderAt
    ((zetaResidueFactor * zetaResidueFactor) * fun z => cexp (pairedExponent x z)) s at hord
  rw [analyticOrderAt_mul (hU s hs) (hV s hs),
    analyticOrderAt_mul (hZ.mul hZ) he,
    analyticOrderAt_mul hZ hZ, hzero, add_zero] at hord
  exact hord

/-- Schwarz conjugation exchanges opposite points of the gauge torus. -/
theorem gaugeFibre_neg_eq_conj (x : GaugeTorus) (s : ℂ) :
    gaugeFibre (-x) s = conj (gaugeFibre x (conj s)) := by
  unfold gaugeFibre LSeries
  rw [Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, map_zero]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    map_div₀, twist_neg_eq_conj, ← natCast_cpow_conj, Complex.conj_conj]

/-- Holomorphic reflection across the real axis. -/
def schwarzConjugate (U : ℂ → ℂ) (s : ℂ) : ℂ := conj (U (conj s))

theorem analyticOnNhd_schwarzConjugate {U : ℂ → ℂ} {c : ℝ}
    (hU : AnalyticOnNhd ℂ U {s : ℂ | c < s.re}) :
    AnalyticOnNhd ℂ (schwarzConjugate U) {s : ℂ | c < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  have h := (hU (conj s) (by simpa using hs)).differentiableAt.conj_conj
  rw [Complex.conj_conj] at h
  exact h.differentiableWithinAt

/-- A pole-preserving fibre without real zeros has quadratically summable
prime perturbations and an exact conjugate-paired divisor equal to that of ζ². -/
theorem gauge_quadratic_rigidity {x : GaugeTorus} {c : ℝ}
    (hc₀ : 1 / 2 ≤ c) (hc₁ : c < 1) {U : ℂ → ℂ}
    (hU : AnalyticOnNhd ℂ U {s : ℂ | c < s.re})
    (hUeq : ∀ s : ℂ, 1 < s.re → U s = (s - 1) * gaugeFibre x s)
    (hUne : ∀ t : ℝ, c < t → U (t : ℂ) ≠ 0) :
    (∀ σ : ℝ, c < σ →
      Summable (fun p : Nat.Primes => ‖twist x p - 1‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-σ))) ∧
    AnalyticOnNhd ℂ (pairedExponent x) {s : ℂ | c < s.re} ∧
    (∀ s : ℂ, c < s.re → U s * conj (U (conj s)) =
      zetaResidueFactor s ^ 2 * cexp (pairedExponent x s)) ∧
    (∀ s : ℂ, c < s.re → analyticOrderAt U s + analyticOrderAt (schwarzConjugate U) s =
      analyticOrderAt zetaResidueFactor s + analyticOrderAt zetaResidueFactor s) := by
  have hV := analyticOnNhd_schwarzConjugate hU
  have hVeq : ∀ s : ℂ, 1 < s.re →
      schwarzConjugate U s = (s - 1) * gaugeFibre (-x) s := by
    intro s hs
    rw [schwarzConjugate, hUeq (conj s) (by simpa using hs), map_mul,
      map_sub, map_one, Complex.conj_conj, gaugeFibre_neg_eq_conj]
  have hVne : ∀ t : ℝ, c < t → schwarzConjugate U (t : ℂ) ≠ 0 := by
    intro t ht
    simpa only [schwarzConjugate, Complex.conj_ofReal, map_ne_zero] using hUne t ht
  obtain ⟨hsum, hH, hid⟩ := paired_rigidity hc₀ hc₁ hU hV hUeq hVeq hUne hVne
  refine ⟨?_, hH, hid, fun s hs =>
    paired_analyticOrderAt hc₀ hc₁ hU hV hUeq hVeq hUne hVne hs⟩
  intro σ hσ
  refine ((hsum σ hσ).mul_left 2).congr fun p => ?_
  rw [norm_twist_sub_one_sq]
  simp only [gdTwistTerm, pow_zero, mul_one, prime_exp_decay]
  ring

/-- The zero support of a pole-preserving fibre is contained in zeta's;
each zeta zero belongs to at least one member of the conjugate pair. -/
theorem gauge_paired_zero_iff {x : GaugeTorus} {c : ℝ}
    (hc₀ : 1 / 2 ≤ c) (hc₁ : c < 1) {U : ℂ → ℂ}
    (hU : AnalyticOnNhd ℂ U {s : ℂ | c < s.re})
    (hUeq : ∀ s : ℂ, 1 < s.re → U s = (s - 1) * gaugeFibre x s)
    (hUne : ∀ t : ℝ, c < t → U (t : ℂ) ≠ 0)
    {s : ℂ} (hs : c < s.re) :
    (U s = 0 ∨ U (conj s) = 0) ↔ zetaResidueFactor s = 0 := by
  have hid := (gauge_quadratic_rigidity hc₀ hc₁ hU hUeq hUne).2.2.1 s hs
  have hh := congrArg (fun z : ℂ => z = 0) hid
  simpa only [mul_eq_zero, map_eq_zero, pow_eq_zero_iff (by omega : (2 : ℕ) ≠ 0),
    Complex.exp_ne_zero, or_false] using Iff.of_eq hh

/-- Schwarz reflection transports the analytic order to the conjugate point. -/
theorem analyticOrderAt_schwarzConjugate {U : ℂ → ℂ} {c : ℝ}
    (hU : AnalyticOnNhd ℂ U {s : ℂ | c < s.re}) {s : ℂ} (hs : c < s.re) :
    analyticOrderAt (schwarzConjugate U) s = analyticOrderAt U (conj s) := by
  have hc : c < (conj s).re := by simpa using hs
  have h := _root_.RHTower.analyticOrderAt_conj_conj_of_analyticAt
    (hU (conj s) hc) ((analyticOnNhd_schwarzConjugate hU) (conj (conj s))
      (by simpa using hs))
  rw [Complex.conj_conj] at h
  exact h

/-- A pole-preserving fibre can distribute zeta's multiplicity only between
the two conjugate points; their total is exactly twice zeta's multiplicity. -/
theorem gauge_conjugate_multiplicities {x : GaugeTorus} {c : ℝ}
    (hc₀ : 1 / 2 ≤ c) (hc₁ : c < 1) {U : ℂ → ℂ}
    (hU : AnalyticOnNhd ℂ U {s : ℂ | c < s.re})
    (hUeq : ∀ s : ℂ, 1 < s.re → U s = (s - 1) * gaugeFibre x s)
    (hUne : ∀ t : ℝ, c < t → U (t : ℂ) ≠ 0)
    {s : ℂ} (hs : c < s.re) (hs₁ : s ≠ 1) :
    analyticOrderAt U s + analyticOrderAt U (conj s) =
      analyticOrderAt riemannZeta s + analyticOrderAt riemannZeta s := by
  have h := (gauge_quadratic_rigidity hc₀ hc₁ hU hUeq hUne).2.2.2 s hs
  rw [analyticOrderAt_schwarzConjugate hU hs] at h
  have hZ : analyticOrderAt zetaResidueFactor s = analyticOrderAt riemannZeta s := by
    have heq : zetaResidueFactor =ᶠ[𝓝 s] (fun z => (z - 1) * riemannZeta z) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs₁] with z hz
      exact zetaResidueFactor_of_ne hz
    have he := analyticOrderAt_congr heq
    have ha : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
    have hz : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs₁
    have hzero : analyticOrderAt (fun z : ℂ => z - 1) s = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (sub_ne_zero.mpr hs₁))
    change analyticOrderAt zetaResidueFactor s =
      analyticOrderAt ((fun z : ℂ => z - 1) * riemannZeta) s at he
    rwa [analyticOrderAt_mul ha hz, hzero, zero_add] at he
  rwa [hZ] at h

/-- Divergence of the quadratic prime perturbation forces a real zero in
any holomorphic pole-regularized continuation. -/
theorem real_zero_of_quadratic_divergence {x : GaugeTorus} {c σ : ℝ}
    (hc₀ : 1 / 2 ≤ c) (hc₁ : c < 1) (hσ : c < σ)
    (hdiv : ¬ Summable (fun p : Nat.Primes => ‖twist x p - 1‖ ^ 2 *
      ((p : ℕ) : ℝ) ^ (-σ))) {U : ℂ → ℂ}
    (hU : AnalyticOnNhd ℂ U {s : ℂ | c < s.re})
    (hUeq : ∀ s : ℂ, 1 < s.re → U s = (s - 1) * gaugeFibre x s) :
    ∃ t : ℝ, c < t ∧ U (t : ℂ) = 0 := by
  by_contra h
  have hne : ∀ t : ℝ, c < t → U (t : ℂ) ≠ 0 := by
    intro t ht hz
    exact h ⟨t, ht, hz⟩
  exact hdiv ((gauge_quadratic_rigidity hc₀ hc₁ hU hUeq hne).1 σ hσ)

/-- Every zero-free half-plane of a pole-preserving fibre is exactly a
zero-free half-plane of zeta. Quadratic defects cannot improve zero width. -/
theorem gauge_zeroFree_halfPlane_iff {x : GaugeTorus} {c d : ℝ}
    (hc₀ : 1 / 2 ≤ c) (hc₁ : c < 1) (hcd : c ≤ d) {U : ℂ → ℂ}
    (hU : AnalyticOnNhd ℂ U {s : ℂ | c < s.re})
    (hUeq : ∀ s : ℂ, 1 < s.re → U s = (s - 1) * gaugeFibre x s)
    (hUne : ∀ t : ℝ, c < t → U (t : ℂ) ≠ 0) :
    (∀ s : ℂ, d < s.re → U s ≠ 0) ↔
      (∀ s : ℂ, d < s.re → s ≠ 1 → riemannZeta s ≠ 0) := by
  constructor
  · intro hzero s hs hs₁ hz
    have hZ : zetaResidueFactor s = 0 := by
      rw [zetaResidueFactor_of_ne hs₁, hz, mul_zero]
    rcases (gauge_paired_zero_iff hc₀ hc₁ hU hUeq hUne (hcd.trans_lt hs)).mpr hZ with hu | hu
    · exact hzero s hs hu
    · exact hzero (conj s) (by simpa only [Complex.conj_re] using hs) hu
  · intro hzero s hs hu
    by_cases hs₁ : s = 1
    · subst s
      exact hUne 1 hc₁ (by simpa only [Complex.ofReal_one] using hu)
    have hZ := (gauge_paired_zero_iff hc₀ hc₁ hU hUeq hUne (hcd.trans_lt hs)).mp (Or.inl hu)
    rw [zetaResidueFactor_of_ne hs₁] at hZ
    exact mul_ne_zero (sub_ne_zero.mpr hs₁) (hzero s hs hs₁) hZ

/-- For a genuine simple pole, a divergent quadratic perturbation forces
a real zero away from the pole. -/
theorem real_zero_away_from_pole_of_quadratic_divergence {x : GaugeTorus} {c σ : ℝ}
    (hc₀ : 1 / 2 ≤ c) (hc₁ : c < 1) (hσ : c < σ)
    (hdiv : ¬ Summable (fun p : Nat.Primes => ‖twist x p - 1‖ ^ 2 *
      ((p : ℕ) : ℝ) ^ (-σ))) {U : ℂ → ℂ}
    (hU : AnalyticOnNhd ℂ U {s : ℂ | c < s.re})
    (hUeq : ∀ s : ℂ, 1 < s.re → U s = (s - 1) * gaugeFibre x s)
    (hUone : U 1 ≠ 0) :
    ∃ t : ℝ, c < t ∧ t ≠ 1 ∧ U (t : ℂ) = 0 := by
  obtain ⟨t, ht, hz⟩ := real_zero_of_quadratic_divergence hc₀ hc₁ hσ hdiv hU hUeq
  refine ⟨t, ht, ?_, hz⟩
  intro ht1
  subst t
  exact hUone (by simpa only [Complex.ofReal_one] using hz)

/-- For an actual holomorphic gauge continuation, the absence of real
zeros is equivalent to quadratic prime convergence throughout the half-plane.
The condition includes nonvanishing of the residue at one. -/
theorem real_nonvanishing_iff_quadratic_summable {x : GaugeTorus} {c : ℝ}
    (hc₀ : 1 / 2 ≤ c) (hc₁ : c < 1) {U : ℂ → ℂ}
    (hU : AnalyticOnNhd ℂ U {s : ℂ | c < s.re})
    (hUeq : ∀ s : ℂ, 1 < s.re → U s = (s - 1) * gaugeFibre x s) :
    (∀ t : ℝ, c < t → U (t : ℂ) ≠ 0) ↔
      (∀ σ : ℝ, c < σ → Summable (fun p : Nat.Primes =>
        ‖twist x p - 1‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-σ))) := by
  constructor
  · intro hne
    exact (gauge_quadratic_rigidity hc₀ hc₁ hU hUeq hne).1
  · intro hsum
    have hE : ∀ σ : ℝ, c < σ →
        Summable (gdTwistTerm (primeDefect x) primeFrequency σ 0) := by
      intro σ hσ
      refine ((hsum σ hσ).div_const 2).congr fun p => ?_
      rw [norm_twist_sub_one_sq]
      simp only [gdTwistTerm, pow_zero, mul_one, prime_exp_decay]
      ring
    have hV := analyticOnNhd_schwarzConjugate hU
    have hVeq : ∀ s : ℂ, 1 < s.re →
        schwarzConjugate U s = (s - 1) * gaugeFibre (-x) s := by
      intro s hs
      rw [schwarzConjugate, hUeq (conj s) (by simpa using hs), map_mul,
        map_sub, map_one, Complex.conj_conj, gaugeFibre_neg_eq_conj]
    have hid := (paired_identity_of_defect_summable hc₀ hc₁ hU hV hUeq hVeq hE).2
    intro t ht hz
    have hh := hid (t : ℂ) ht
    rw [hz, zero_mul] at hh
    exact (mul_ne_zero
      (pow_ne_zero 2 (zetaResidueFactor_real_ne_zero (by linarith only [hc₀, ht])))
      (Complex.exp_ne_zero _)) hh.symm

#print axioms deriv_primeDefectSeries
#print axioms paired_rigidity
#print axioms gauge_quadratic_rigidity
#print axioms gauge_conjugate_multiplicities
#print axioms real_nonvanishing_iff_quadratic_summable
#print axioms gauge_zeroFree_halfPlane_iff
#print axioms real_zero_away_from_pole_of_quadratic_divergence
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
