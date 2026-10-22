import GaloisForLFunctions.RHTower.XiMassPrimePowerVerticalIdeal
import GaloisForLFunctions.RHTower.EvenHorizontalCauchyResidue
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegLowBox
import GaloisForLFunctions.PNTPlus.ZetaBounds

/-!
# The prime-square layer of the mass prime source is vertically bounded

The prime-square layer is `∑_p Λ(p²) p^{-1} ĝ(2 log p)`, the part of the centered von Mangoldt
atom series carried by squares of primes, where `ĝ` is the Fourier transform of the mass test
`g(z) = exp(-τ √(z² + a²))`. Transporting each atom to the depth-`d` bottom line identifies the
layer with `∫ g(x - di) P(1 + 2d + 2ix) dx`, where `P(s) = ∑_p log p · p^{-s}` is the prime-log
Dirichlet series. On `Re s > 1`, `P(s) = 1/(s - 1) + R(s) - H(s)` with `R` the regular part of
`-ζ'/ζ` and `H` the absolutely bounded higher-valuation part. The pole term is evaluated by an even
horizontal Cauchy residue as `(π/2) g(0)`, `R` obeys a polynomial envelope `K (1 + |t|)^9` on
`1 ≤ Re s ≤ D` (from the uniform log-derivative bound of PNT+), and choosing the depth
`d = min(a/2, 1/(1 + |u|))` keeps `e^{|u| d} ≤ e`. Hence the layer is bounded on every positive
vertical line.

## Main results

- `integral_test_mul_xiPrimeLogDirichlet_eq_primeSquareLayer`: for `0 < d < a`, `0 < Re τ`, the
  prime-square layer equals `∫ g(x - di) P(1 + 2d + 2ix) dx`.
- `xiPrimeLogDirichlet_eq_pole_add_regular_sub_higherValuation`: `P(s) = 1/(s - 1) + R(s) - H(s)`
  for `Re s > 1`.
- `exists_norm_zetaLogDerivReg_right_envelope`: `‖R(σ + it)‖ ≤ K (1 + |t|)^9` for `1 ≤ σ ≤ D`.
- `integral_xiMassBottomTest_mul_naturalPole`: the pole term integrates to `(π/2) g(0)`.
- `exists_norm_xiMassPrimeSquareLayer_vertical_bound`: for `a, σ > 0` the prime-square layer is
  bounded on the line `Re τ = σ`, uniformly in `Im τ`.

## Hypotheses

All results are unconditional. They use only parameter ranges: `0 < a`, `0 < σ`, depths
`0 ≤ d < a` or `0 < d < a`, `0 < Re τ`, and `1 < Re s` or `1 ≤ Re s` for the Dirichlet series
identities and bounds.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The prime-square layer: the sum over primes `p` of the centered mass atoms at `p²`. -/
def xiMassPrimeSquareLayer (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' p : Nat.Primes,
    xiMassCenteredPrimeAtom a τ ((p : ℕ) ^ 2)

/-- Absolute von Mangoldt weight of `p²` on the Euler line `Re s = 1/2 + d`. -/
def xiMassPrimeSquareEulerWeight (d : ℝ) (p : Nat.Primes) : ℝ :=
  xiMassBottomPrimeAtomWeight d ((p : ℕ) ^ 2)

/-- Closed form of the square weight: `log p · p^{-(1 + 2d)}`. -/
theorem xiMassPrimeSquareEulerWeight_eq
    (d : ℝ) (p : Nat.Primes) :
    xiMassPrimeSquareEulerWeight d p =
      Real.log (p : ℝ) * (p : ℝ) ^ (-(1 + 2 * d)) := by
  have hpPow : 0 < (p : ℕ) ^ 2 := pow_pos p.prop.pos _
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  rw [xiMassPrimeSquareEulerWeight, xiMassBottomPrimeAtomWeight,
    LSeries.norm_term_eq, if_neg hpPow.ne']
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.log_pos hpR)]
  rw [Nat.cast_pow, div_eq_mul_inv, ← Real.rpow_neg (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 2
  norm_num
  ring

/-- For every depth `d > 0` the square weights `log p · p^{-(1 + 2d)}` are summable over primes. -/
theorem summable_xiMassPrimeSquareEulerWeight
    {d : ℝ} (hd : 0 < d) :
    Summable (xiMassPrimeSquareEulerWeight d) := by
  have hβ : (1 : ℝ) < 1 + 2 * d := by linarith
  have h := (summable_abs_log_natCast_pow_mul_rpow_neg 1 (1 + 2 * d) hβ).comp_injective
    (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
  apply h.congr
  intro p
  change |Real.log (p : ℝ)| ^ 1 * (p : ℝ) ^ (-(1 + 2 * d)) =
    xiMassPrimeSquareEulerWeight d p
  rw [xiMassPrimeSquareEulerWeight_eq, pow_one,
    abs_of_pos (Real.log_pos (by exact_mod_cast p.prop.one_lt))]

theorem xiMassBottomPoint_mem_strip_of_nonneg
    {a d x : ℝ} (hd : 0 ≤ d) (hda : d < a) :
    ((x : ℂ) - d * I) ∈ xiMassStrip a := by
  change |(((x : ℂ) - d * I)).im| < a
  simpa [Complex.mul_im, abs_of_nonneg hd] using hda

theorem continuous_xiMassBottomTest_of_nonneg
    {a d : ℝ} (hd : 0 ≤ d) (hda : d < a) (τ : ℂ) :
    Continuous (xiMassBottomTest a d τ) := by
  have ha : 0 < a := lt_of_le_of_lt hd hda
  rw [continuous_iff_continuousAt]
  intro x
  let z : ℝ → ℂ := fun y => (y : ℂ) - d * I
  have hz : HasDerivAt z 1 x := by
    dsimp only [z]
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).sub_const (d * I)
  exact ((hasDerivAt_xiMassAnalyticTest ha τ
    (xiMassBottomPoint_mem_strip_of_nonneg hd hda)).comp x hz).continuousAt

/-- For `0 ≤ d < a` and `0 ≤ Re τ`, the mass test on the depth-`d` bottom line obeys
`‖g(x - di)‖ ≤ e^{|Im τ| d} e^{-Re τ · |x|}`. -/
theorem norm_xiMassBottomTest_le_of_nonneg
    {a d x : ℝ} (hd : 0 ≤ d) (hda : d < a)
    {τ : ℂ} (hτ : 0 ≤ τ.re) :
    ‖xiMassBottomTest a d τ x‖ ≤
      Real.exp (|τ.im| * d) * Real.exp (-(τ.re * |x|)) := by
  have ha : 0 < a := lt_of_le_of_lt hd hda
  have hraw := norm_xiMassAnalyticTest_le ha hτ
    (xiMassBottomPoint_mem_strip_of_nonneg hd hda :
      ((x : ℂ) - d * I) ∈ xiMassStrip a)
  change ‖xiMassBottomTest a d τ x‖ ≤ _
  calc
    ‖xiMassBottomTest a d τ x‖ ≤
        Real.exp (-τ.re * |(((x : ℂ) - d * I)).re| +
          |τ.im| * |(((x : ℂ) - d * I)).im|) := hraw
    _ = Real.exp (|τ.im| * d) * Real.exp (-(τ.re * |x|)) := by
      simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, sub_zero, sub_im, mul_im, mul_one, add_zero, zero_sub, abs_neg]
      rw [abs_of_nonneg hd, ← Real.exp_add]
      congr 1
      ring

/-- Depth erasure for one atom, including depth zero: for `0 ≤ d < a` and `0 < Re τ`, the
depth-`d` bottom-line integral of the von Mangoldt atom at `n` equals the centered atom
`Λ(n) n^{-1/2} ĝ(log n)`. Proved by horizontal strip transport. -/
theorem integral_xiMassBottomPrimeAtom_eq_centered_of_nonneg
    {a d : ℝ} (hd : 0 ≤ d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) (n : ℕ) :
    (∫ x : ℝ, xiMassBottomPrimeAtomIntegrand a d τ n x) =
      xiMassCenteredPrimeAtom a τ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [xiMassBottomPrimeAtomIntegrand, xiMassCenteredPrimeAtom,
      LSeries.term_zero]
  · let F : ℂ → ℂ := fun z =>
      xiMassAnalyticTest a τ z *
        Complex.exp (-(I * (Real.log n : ℂ) * z))
    have hdiff : ∀ z : ℂ, |z.im| ≤ d → DifferentiableAt ℂ F z := by
      intro z hz
      have ha : 0 < a := lt_of_le_of_lt hd hda
      have hmem : z ∈ xiMassStrip a := lt_of_le_of_lt hz hda
      exact (hasDerivAt_xiMassAnalyticTest ha τ hmem).differentiableAt.mul
        (by fun_prop)
    have hbound : ∀ z : ℂ, |z.im| ≤ d →
        ‖F z‖ ≤ Real.exp ((|τ.im| + |Real.log n|) * d) *
          Real.exp (-(τ.re * |z.re|)) := by
      intro z hz
      exact norm_xiMassFourierKernel_le hda hτ (Real.log n) hz
    have hshift := integral_horizontal_shift_neg_of_decay hd hτ hdiff hbound
    have hpoint : ∀ x : ℝ,
        xiMassBottomPrimeAtomIntegrand a d τ n x =
          LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
              (1 / 2 : ℂ) n * F ((x : ℂ) - (d : ℂ) * I) := by
      intro x
      rw [xiMassBottomPrimeAtomIntegrand, xiMassBottomTest,
        xiMassBottomLSeriesTerm_eq_centered_mul_fourierPhase hn]
      dsimp only [F]
      ring
    rw [show (∫ x : ℝ, xiMassBottomPrimeAtomIntegrand a d τ n x) =
        ∫ x : ℝ,
          LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
              (1 / 2 : ℂ) n * F ((x : ℂ) - (d : ℂ) * I) by
      exact integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [MeasureTheory.integral_const_mul, hshift]
    rfl

theorem continuous_xiMassBottomPrimeSquareAtomIntegrand
    {a d : ℝ} (hd : 0 ≤ d) (hda : d < a)
    (τ : ℂ) (p : Nat.Primes) :
    Continuous (xiMassBottomPrimeAtomIntegrand a d τ ((p : ℕ) ^ 2)) := by
  let n : ℕ := (p : ℕ) ^ 2
  have hn : n ≠ 0 := (pow_pos p.prop.pos _).ne'
  change Continuous (xiMassBottomPrimeAtomIntegrand a d τ n)
  have hpoint : xiMassBottomPrimeAtomIntegrand a d τ n =
      fun x =>
        LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
            (1 / 2 : ℂ) n *
          (xiMassBottomTest a d τ x *
            Complex.exp (-(I * (Real.log n : ℂ) *
              ((x : ℂ) - (d : ℂ) * I)))) := by
    funext x
    rw [xiMassBottomPrimeAtomIntegrand,
      xiMassBottomLSeriesTerm_eq_centered_mul_fourierPhase hn]
    ring
  rw [hpoint]
  exact continuous_const.mul
    ((continuous_xiMassBottomTest_of_nonneg hd hda τ).mul
      (Complex.continuous_exp.comp (by fun_prop)))

theorem norm_xiMassBottomPrimeSquareAtomIntegrand_le
    {a d x : ℝ} (hd : 0 ≤ d) (hda : d < a)
    {τ : ℂ} (hτ : 0 ≤ τ.re) (p : Nat.Primes) :
    ‖xiMassBottomPrimeAtomIntegrand a d τ ((p : ℕ) ^ 2) x‖ ≤
      (Real.exp (|τ.im| * d) * xiMassPrimeSquareEulerWeight d p) *
        Real.exp (-(τ.re * |x|)) := by
  have hterm :
      ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          (xiMassBottomEulerPoint d x) ((p : ℕ) ^ 2)‖ =
        xiMassPrimeSquareEulerWeight d p := by
    unfold xiMassPrimeSquareEulerWeight xiMassBottomPrimeAtomWeight
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp [xiMassBottomEulerPoint, Complex.mul_re]
  rw [xiMassBottomPrimeAtomIntegrand, norm_mul, hterm]
  calc
    ‖xiMassBottomTest a d τ x‖ * xiMassPrimeSquareEulerWeight d p ≤
        (Real.exp (|τ.im| * d) * Real.exp (-(τ.re * |x|))) *
          xiMassPrimeSquareEulerWeight d p :=
      mul_le_mul_of_nonneg_right
        (norm_xiMassBottomTest_le_of_nonneg hd hda hτ)
        (norm_nonneg _)
    _ = (Real.exp (|τ.im| * d) * xiMassPrimeSquareEulerWeight d p) *
        Real.exp (-(τ.re * |x|)) := by ring

theorem integrable_xiMassBottomPrimeSquareAtomIntegrand
    {a d : ℝ} (hd : 0 ≤ d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) (p : Nat.Primes) :
    Integrable (xiMassBottomPrimeAtomIntegrand a d τ ((p : ℕ) ^ 2)) := by
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hτ).const_mul
      (Real.exp (|τ.im| * d) * xiMassPrimeSquareEulerWeight d p))
    (continuous_xiMassBottomPrimeSquareAtomIntegrand hd hda τ p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x =>
      norm_xiMassBottomPrimeSquareAtomIntegrand_le hd hda hτ.le p)

/-- For `0 < d < a` and `0 < Re τ`, the `L¹` norms of the prime-square bottom atoms are
summable over primes, which permits exchanging sum and integral. -/
theorem summable_integral_norm_xiMassBottomPrimeSquareAtomIntegrand
    {a d : ℝ} (hd : 0 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun p : Nat.Primes =>
      ∫ x : ℝ,
        ‖xiMassBottomPrimeAtomIntegrand a d τ ((p : ℕ) ^ 2) x‖) := by
  let E : ℝ := Real.exp (|τ.im| * d)
  let J : ℝ := ∫ x : ℝ, Real.exp (-(τ.re * |x|))
  have hbound : ∀ p : Nat.Primes,
      (∫ x : ℝ,
        ‖xiMassBottomPrimeAtomIntegrand a d τ ((p : ℕ) ^ 2) x‖) ≤
          (E * J) * xiMassPrimeSquareEulerWeight d p := by
    intro p
    have hmajor : Integrable (fun x : ℝ =>
        (E * xiMassPrimeSquareEulerWeight d p) *
          Real.exp (-(τ.re * |x|))) :=
      (integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hτ).const_mul _
    calc
      (∫ x : ℝ,
          ‖xiMassBottomPrimeAtomIntegrand a d τ ((p : ℕ) ^ 2) x‖) ≤
          ∫ x : ℝ,
            (E * xiMassPrimeSquareEulerWeight d p) *
              Real.exp (-(τ.re * |x|)) :=
        integral_mono
          (integrable_xiMassBottomPrimeSquareAtomIntegrand hd.le hda hτ p).norm
          hmajor
          (fun x =>
            norm_xiMassBottomPrimeSquareAtomIntegrand_le hd.le hda hτ.le p)
      _ = (E * J) * xiMassPrimeSquareEulerWeight d p := by
        rw [MeasureTheory.integral_const_mul]
        dsimp only [J]
        ring
  exact Summable.of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _)
    hbound
    ((summable_xiMassPrimeSquareEulerWeight hd).mul_left (E * J))

/-- Pointwise sum over primes of the depth-`d` bottom-line atoms at `p²`. -/
def xiMassBottomPrimeSquareIntegrand
    (a d : ℝ) (τ : ℂ) (x : ℝ) : ℂ :=
  ∑' p : Nat.Primes,
    xiMassBottomPrimeAtomIntegrand a d τ ((p : ℕ) ^ 2) x

/-- The prime-log Dirichlet series `P(s) = ∑_p Λ(p²) (p²)^{-s/2} = ∑_p log p · p^{-s}`. -/
def xiPrimeLogDirichlet (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes,
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (s / 2) ((p : ℕ) ^ 2)

/-- The prime-square bottom integrand factors as `g(x - di) · P(1 + 2d + 2ix)`. -/
theorem xiMassBottomPrimeSquareIntegrand_eq_test_mul_primeLogDirichlet
    (a d : ℝ) (τ : ℂ) (x : ℝ) :
    xiMassBottomPrimeSquareIntegrand a d τ x =
      xiMassBottomTest a d τ x *
        xiPrimeLogDirichlet (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) := by
  unfold xiMassBottomPrimeSquareIntegrand xiPrimeLogDirichlet
  simp only [xiMassBottomPrimeAtomIntegrand]
  rw [tsum_mul_left]
  congr 1
  apply tsum_congr
  intro p
  congr 2
  unfold xiMassBottomEulerPoint
  push_cast
  ring

/-- For `0 < d < a` and `0 < Re τ`, the integral of the prime-square bottom integrand is the
prime-square layer. -/
theorem integral_xiMassBottomPrimeSquareIntegrand_eq_layer
    {a d : ℝ} (hd : 0 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    (∫ x : ℝ, xiMassBottomPrimeSquareIntegrand a d τ x) =
      xiMassPrimeSquareLayer a τ := by
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun p => integrable_xiMassBottomPrimeSquareAtomIntegrand hd.le hda hτ p)
    (summable_integral_norm_xiMassBottomPrimeSquareAtomIntegrand hd hda hτ)
  calc
    (∫ x : ℝ, xiMassBottomPrimeSquareIntegrand a d τ x) =
        ∫ x : ℝ, ∑' p : Nat.Primes,
          xiMassBottomPrimeAtomIntegrand a d τ ((p : ℕ) ^ 2) x := by rfl
    _ = ∑' p : Nat.Primes,
        ∫ x : ℝ,
          xiMassBottomPrimeAtomIntegrand a d τ ((p : ℕ) ^ 2) x := hswap.symm
    _ = xiMassPrimeSquareLayer a τ := by
      unfold xiMassPrimeSquareLayer
      exact tsum_congr fun p =>
        integral_xiMassBottomPrimeAtom_eq_centered_of_nonneg hd.le hda hτ _

/-- For `0 < d < a` and `0 < Re τ`, the prime-square layer equals
`∫ g(x - di) P(1 + 2d + 2ix) dx`. -/
theorem integral_test_mul_xiPrimeLogDirichlet_eq_primeSquareLayer
    {a d : ℝ} (hd : 0 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    (∫ x : ℝ, xiMassBottomTest a d τ x *
      xiPrimeLogDirichlet (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)) =
      xiMassPrimeSquareLayer a τ := by
  rw [← integral_xiMassBottomPrimeSquareIntegrand_eq_layer hd hda hτ]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    (xiMassBottomPrimeSquareIntegrand_eq_test_mul_primeLogDirichlet a d τ x).symm)

/-- The von Mangoldt term of `p²` at `s/2` is `log p / p^s`. -/
theorem xiPrimeLogDirichlet_term_eq (s : ℂ) (p : Nat.Primes) :
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (s / 2) ((p : ℕ) ^ 2) =
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s) := by
  have hp0 : (p : ℕ) ^ 2 ≠ 0 := (pow_pos p.prop.pos _).ne'
  have harg : ((p : ℂ)).arg = 0 := by
    exact Complex.arg_ofReal_of_nonneg (show 0 ≤ (p : ℝ) by positivity)
  have hpow : (((p : ℕ) ^ 2 : ℕ) : ℂ) ^ (s / 2) = (p : ℂ) ^ s := by
    rw [Nat.cast_pow]
    rw [← Complex.cpow_nat_mul'
      (x := (p : ℂ)) (n := 2)
      (by simpa [harg] using Real.pi_pos)
      (by simpa [harg] using Real.pi_pos.le) (s / 2)]
    congr 1
    ring
  rw [LSeries.term_of_ne_zero hp0,
    ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  norm_cast
  rw [hpow]

/-- For `Re s > 1` the series `P(s)` converges absolutely. -/
theorem summable_xiPrimeLogDirichlet_term
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes =>
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (s / 2) ((p : ℕ) ^ 2)) := by
  let d : ℝ := (s.re - 1) / 2
  have hd : 0 < d := by dsimp only [d]; linarith
  apply summable_norm_iff.mp
  apply (summable_xiMassPrimeSquareEulerWeight hd).congr
  intro p
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hnormpow : ‖((p : ℂ) ^ s)‖ = (p : ℝ) ^ s.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hpR s
  rw [xiMassPrimeSquareEulerWeight_eq, xiPrimeLogDirichlet_term_eq,
    norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.log_pos (by exact_mod_cast p.prop.one_lt)), hnormpow]
  rw [div_eq_mul_inv, ← Real.rpow_neg hpR.le]
  congr 2
  dsimp only [d]
  ring

/-- `P(s) = ∑_p log p / p^s` (the hypothesis `1 < Re s` is not used in the proof). -/
theorem xiPrimeLogDirichlet_eq_tsum_primeLog_div_cpow
    {s : ℂ} (_hs : 1 < s.re) :
    xiPrimeLogDirichlet s =
      ∑' p : Nat.Primes, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s) := by
  unfold xiPrimeLogDirichlet
  exact tsum_congr (xiPrimeLogDirichlet_term_eq s)

/-- The higher-valuation part `H(s) = ∑_{p, k ≥ 0} Λ(p^{k+2}) p^{-(k+2)s}` of the von Mangoldt
Dirichlet series. -/
def xiPrimeLogHigherValuation (s : ℂ) : ℂ :=
  ∑' pk : Nat.Primes × ℕ,
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      s ((pk.1 : ℕ) ^ (pk.2 + 2))

/-- For `Re s > 1` the terms of `H(s)` are summable. -/
theorem summable_xiPrimeLogHigherValuation_term
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun pk : Nat.Primes × ℕ =>
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        s ((pk.1 : ℕ) ^ (pk.2 + 2))) := by
  have hfull : Summable (LSeries.term
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hshift : Function.Injective
      (fun pk : Nat.Primes × ℕ => (pk.1, pk.2 + 1)) := by
    rintro ⟨p, k⟩ ⟨q, l⟩ h
    have hpq : p = q := congrArg Prod.fst h
    have hkl : k + 1 = l + 1 := congrArg Prod.snd h
    exact Prod.ext hpq (Nat.succ.inj hkl)
  have hcomp := hfull.comp_injective
    (eulerPrimePowerNat_injective.comp hshift)
  apply hcomp.congr
  rintro ⟨p, k⟩
  simp only [Function.comp_apply, eulerPrimePowerNat]

theorem vonMangoldtLSeries_prime_term_eq_xiPrimeLogDirichlet_term
    (s : ℂ) (p : Nat.Primes) :
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        s (p : ℕ) =
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (s / 2) ((p : ℕ) ^ 2) := by
  rw [xiPrimeLogDirichlet_term_eq, LSeries.term_of_ne_zero p.prop.ne_zero,
    ArithmeticFunction.vonMangoldt_apply_prime p.prop]

theorem vonMangoldtLSeriesTerm_support_primePower (s : ℂ) :
    Function.support (LSeries.term
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) ⊆
      {n : ℕ | IsPrimePow n} := by
  intro n hn
  by_contra hpow
  apply hn
  have hΛ : ArithmeticFunction.vonMangoldt n = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn0, hΛ]
    simp

/-- For `Re s > 1`, `∑_n Λ(n) n^{-s} = P(s) + H(s)`: the von Mangoldt series splits into its
prime and higher-valuation parts. -/
theorem tsum_vonMangoldtLSeriesTerm_eq_primeLog_add_higherValuation
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ,
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n) =
      xiPrimeLogDirichlet s + xiPrimeLogHigherValuation s := by
  let f : ℕ → ℂ := LSeries.term
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s
  have hf : Summable f := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hreindex : (∑' n : ℕ, f n) =
      ∑' p : Nat.Primes, ∑' k : ℕ, f ((p : ℕ) ^ (k + 1)) :=
    tsum_eq_tsum_primes_of_support_subset_prime_powers hf
      (vonMangoldtLSeriesTerm_support_primePower s)
  have hpow : Summable (fun pk : Nat.Primes × ℕ =>
      f ((pk.1 : ℕ) ^ (pk.2 + 1))) := by
    simpa only [f, eulerPrimePowerNat] using!
      hf.comp_injective eulerPrimePowerNat_injective
  have hprime : Summable (fun p : Nat.Primes => f (p : ℕ)) := by
    have h := hf.comp_injective
      (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
    simpa only [Function.comp_apply] using! h
  have htail : Summable (fun pk : Nat.Primes × ℕ =>
      f ((pk.1 : ℕ) ^ (pk.2 + 2))) := by
    simpa only [f] using summable_xiPrimeLogHigherValuation_term hs
  have htailOuter : Summable (fun p : Nat.Primes =>
      ∑' k : ℕ, f ((p : ℕ) ^ (k + 2))) := htail.prod
  have hinner (p : Nat.Primes) :
      (∑' k : ℕ, f ((p : ℕ) ^ (k + 1))) =
        f (p : ℕ) + ∑' k : ℕ, f ((p : ℕ) ^ (k + 2)) := by
    have hp : Summable (fun k : ℕ => f ((p : ℕ) ^ (k + 1))) := by
      have h := hpow.comp_injective
        (i := fun k : ℕ => (p, k)) (fun _ _ h => congrArg Prod.snd h)
      simpa only [Function.comp_apply] using! h
    simpa only [zero_add, pow_one, add_assoc] using hp.tsum_eq_zero_add
  calc
    (∑' n : ℕ,
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n) =
        ∑' n : ℕ, f n := by rfl
    _ = ∑' p : Nat.Primes, ∑' k : ℕ,
        f ((p : ℕ) ^ (k + 1)) := hreindex
    _ = ∑' p : Nat.Primes,
        (f (p : ℕ) + ∑' k : ℕ, f ((p : ℕ) ^ (k + 2))) := by
      exact tsum_congr hinner
    _ = (∑' p : Nat.Primes, f (p : ℕ)) +
        ∑' p : Nat.Primes, ∑' k : ℕ,
          f ((p : ℕ) ^ (k + 2)) := hprime.tsum_add htailOuter
    _ = xiPrimeLogDirichlet s + xiPrimeLogHigherValuation s := by
      congr 1
      · unfold xiPrimeLogDirichlet
        exact tsum_congr fun p =>
          vonMangoldtLSeries_prime_term_eq_xiPrimeLogDirichlet_term s p
      · rw [← htail.tsum_prod]
        rfl

/-- For `Re s > 1`, `-ζ'(s)/ζ(s) = P(s) + H(s)`. -/
theorem infinitePrimeFlux_eq_primeLog_add_higherValuation
    {s : ℂ} (hs : 1 < s.re) :
    infinitePrimeFlux s =
      xiPrimeLogDirichlet s + xiPrimeLogHigherValuation s := by
  rw [infinitePrimeFlux_eq_vonMangoldtLSeries hs]
  exact tsum_vonMangoldtLSeriesTerm_eq_primeLog_add_higherValuation hs

/-- For `Re s > 1`, `P(s) = 1/(s - 1) + R(s) - H(s)`, where `R` is the regular part of
`-ζ'/ζ` (the negated log-derivative of `(s - 1) ζ(s)`). -/
theorem xiPrimeLogDirichlet_eq_pole_add_regular_sub_higherValuation
    {s : ℂ} (hs : 1 < s.re) :
    xiPrimeLogDirichlet s =
      (s - 1)⁻¹ + RHTower.Sieve.zetaLogDerivReg s -
        xiPrimeLogHigherValuation s := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hG : zetaResidueUnit s ≠ 0 := by
    apply (RHTower.Sieve.zetaResidueUnit_ne_zero_iff hs1).2
    exact riemannZeta_ne_zero_of_one_lt_re hs
  have hpole := RHTower.Sieve.neg_logDeriv_riemannZeta_eq hs1 hG
  have hflux := infinitePrimeFlux_eq_primeLog_add_higherValuation hs
  rw [infinitePrimeFlux, hpole] at hflux
  exact eq_sub_iff_add_eq.mpr hflux.symm

/-- Majorant `log p · p^{-(k+2)}` for the term of `H` at `p^{k+2}` on `Re s ≥ 1`. -/
def xiPrimeLogHigherValuationWeight (pk : Nat.Primes × ℕ) : ℝ :=
  Real.log (pk.1 : ℝ) * ((pk.1 : ℝ)⁻¹) ^ ((pk.2 : ℝ) + 2)

theorem summable_xiPrimeLogHigherValuationWeight :
    Summable xiPrimeLogHigherValuationWeight := by
  exact summable_primeLog_mul_inv_rpow_add 2 (by norm_num)

/-- For `Re s ≥ 1`, the von Mangoldt term at `p^{k+2}` has norm at most `log p · p^{-(k+2)}`. -/
theorem norm_vonMangoldtLSeriesTerm_primePower_le_higherValuationWeight
    {s : ℂ} (hs : 1 ≤ s.re) (pk : Nat.Primes × ℕ) :
    ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      s ((pk.1 : ℕ) ^ (pk.2 + 2))‖ ≤
      xiPrimeLogHigherValuationWeight pk := by
  calc
    ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        s ((pk.1 : ℕ) ^ (pk.2 + 2))‖ ≤
        ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (1 : ℂ) ((pk.1 : ℕ) ^ (pk.2 + 2))‖ :=
      LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) _
    _ = xiPrimeLogHigherValuationWeight pk := by
      have hpPow : 0 < (pk.1 : ℕ) ^ (pk.2 + 2) := pow_pos pk.1.prop.pos _
      have hpR : (1 : ℝ) < (pk.1 : ℝ) := by exact_mod_cast pk.1.prop.one_lt
      rw [LSeries.norm_term_eq, if_neg hpPow.ne',
        ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime pk.1.prop]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.log_pos hpR)]
      rw [xiPrimeLogHigherValuationWeight]
      simp only [Complex.one_re, Real.rpow_one]
      rw [Nat.cast_pow, div_eq_mul_inv, ← inv_pow, ← Real.rpow_natCast]
      congr 2
      push_cast
      ring

/-- For `Re s ≥ 1`, `‖H(s)‖ ≤ ∑_{p, k} log p · p^{-(k+2)}`, a bound independent of `s`. -/
theorem norm_xiPrimeLogHigherValuation_le
    {s : ℂ} (hs : 1 ≤ s.re) :
    ‖xiPrimeLogHigherValuation s‖ ≤
      ∑' pk : Nat.Primes × ℕ, xiPrimeLogHigherValuationWeight pk := by
  have hnorm : Summable (fun pk : Nat.Primes × ℕ =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        s ((pk.1 : ℕ) ^ (pk.2 + 2))‖) := by
    exact summable_xiPrimeLogHigherValuationWeight.of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (norm_vonMangoldtLSeriesTerm_primePower_le_higherValuationWeight hs)
  calc
    ‖xiPrimeLogHigherValuation s‖ ≤
        ∑' pk : Nat.Primes × ℕ,
          ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            s ((pk.1 : ℕ) ^ (pk.2 + 2))‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' pk : Nat.Primes × ℕ,
        xiPrimeLogHigherValuationWeight pk := by
      exact hnorm.tsum_le_tsum
        (norm_vonMangoldtLSeriesTerm_primePower_le_higherValuationWeight hs)
        summable_xiPrimeLogHigherValuationWeight

/-- Polynomial envelope for the regular part `R` of `-ζ'/ζ` on the closed right strip: for
`D ≥ 1` there is `K ≥ 0` with `‖R(σ + it)‖ ≤ K (1 + |t|)^9` whenever `1 ≤ σ ≤ D`. Combines a
low-height box bound with the uniform PNT+ log-derivative bound near `Re s = 1`. -/
theorem exists_norm_zetaLogDerivReg_right_envelope
    (D : ℝ) (hD : 1 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, 1 ≤ σ → σ ≤ D → ∀ t : ℝ,
      ‖RHTower.Sieve.zetaLogDerivReg
        ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K * (1 + |t|) ^ 9 := by
  obtain ⟨δ, hδ, M, hM, hlow⟩ :=
    RHTower.Sieve.exists_bound_zetaLogDerivReg_line_low D hD
  obtain ⟨A, hA, C, hC, hhigh⟩ := LogDerivZetaBndUnif
  let K : ℝ := M + C + 1
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun σ hσ hσD t => ?_⟩
  have hbase : 1 ≤ (1 + |t|) ^ 9 := by
    have : (1 : ℝ) ≤ 1 + |t| := le_add_of_nonneg_right (abs_nonneg t)
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1) this 9]
  by_cases ht : |t| ≤ 9
  · have hlo : 1 - δ ≤ σ := by linarith
    have hreg := hlow σ hlo hσD t ht
    calc
      ‖RHTower.Sieve.zetaLogDerivReg
          ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M := hreg
      _ ≤ K * (1 + |t|) ^ 9 := by
        dsimp only [K]
        nlinarith
  · have ht9 : 9 < |t| := lt_of_not_ge ht
    have ht3 : 3 < |t| := by linarith
    have ht0 : 0 < |t| := by linarith
    have htne : t ≠ 0 := abs_pos.mp ht0
    have hmem : σ ∈ Set.Ici (1 - A / Real.log |t| ^ 9) := by
      rw [Set.mem_Ici]
      have hA0 : 0 < A := hA.1
      have hlog0 : 0 < Real.log |t| := Real.log_pos (by linarith)
      have hden0 : 0 < Real.log |t| ^ 9 := pow_pos hlog0 _
      have : 0 ≤ A / Real.log |t| ^ 9 := div_nonneg hA0.le hden0.le
      linarith
    have hlogderiv := hhigh σ t ht3 hmem
    have hs1 : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      apply htne
      have him := congrArg Complex.im h
      simpa using him
    have hz : riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      simpa using hσ
    have hsplit :=
      RHTower.Sieve.neg_logDeriv_riemannZeta_eq_of_ne_zero hs1 hz
    have hpole := RHTower.Sieve.norm_inv_sub_one_le_height
      (β := σ) htne
    have hpoleOne :
        ‖((((σ : ℂ) + (t : ℂ) * I) - 1)⁻¹)‖ ≤ 1 := by
      calc
        ‖((((σ : ℂ) + (t : ℂ) * I) - 1)⁻¹)‖ ≤ |t|⁻¹ := hpole
        _ ≤ 1 := by
          rw [inv_le_one₀ ht0]
          linarith
    have hreg :
        ‖RHTower.Sieve.zetaLogDerivReg
          ((σ : ℂ) + (t : ℂ) * I)‖ ≤
            C * Real.log |t| ^ 9 + 1 := by
      have heq : RHTower.Sieve.zetaLogDerivReg
          ((σ : ℂ) + (t : ℂ) * I) =
          -(logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)) -
            ((((σ : ℂ) + (t : ℂ) * I) - 1)⁻¹) := by
        linear_combination -hsplit
      rw [heq]
      calc
        ‖-(logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)) -
            ((((σ : ℂ) + (t : ℂ) * I) - 1)⁻¹)‖ ≤
            ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ +
              ‖((((σ : ℂ) + (t : ℂ) * I) - 1)⁻¹)‖ := by
          simpa only [norm_neg] using norm_sub_le
            (-(logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)))
            ((((σ : ℂ) + (t : ℂ) * I) - 1)⁻¹)
        _ ≤ C * Real.log |t| ^ 9 + 1 := by
          rw [logDeriv_apply]
          exact add_le_add hlogderiv hpoleOne
    have hlogle : Real.log |t| ≤ 1 + |t| := by
      calc
        Real.log |t| ≤ |t| - 1 := Real.log_le_sub_one_of_pos ht0
        _ ≤ 1 + |t| := by linarith
    have hlog0 : 0 ≤ Real.log |t| := (Real.log_pos (by linarith)).le
    have hpow : Real.log |t| ^ 9 ≤ (1 + |t|) ^ 9 := by
      exact pow_le_pow_left₀ hlog0 hlogle 9
    calc
      ‖RHTower.Sieve.zetaLogDerivReg
          ((σ : ℂ) + (t : ℂ) * I)‖ ≤
          C * Real.log |t| ^ 9 + 1 := hreg
      _ ≤ C * (1 + |t|) ^ 9 + 1 := by
        simpa [add_comm] using
          (add_le_add_right (mul_le_mul_of_nonneg_left hpow hC.le) 1)
      _ ≤ K * (1 + |t|) ^ 9 := by
        dsimp only [K]
        nlinarith

/-- Even horizontal Cauchy residue: for `a, σ, d > 0` with `d < a`,
`∫ g(x - di) / (x - di) dx = π i g(0)` with `τ = σ + iu`. -/
theorem integral_xiMassBottomTest_mul_cauchy
    {a σ d : ℝ} (ha : 0 < a) (hσ : 0 < σ) (hd : 0 < d) (hda : d < a)
    (u : ℝ) :
    (∫ x : ℝ, xiMassBottomTest a d ((σ : ℂ) + u * I) x *
        (((x : ℂ) - d * I)⁻¹)) =
      Real.pi * I * xiMassAnalyticTest a ((σ : ℂ) + u * I) 0 := by
  apply integral_even_horizontal_cauchy_of_decay hd hda
      (C := Real.exp (|u| * d)) (r := σ) (by positivity) hσ
  · simpa only [xiMassStrip] using
      analyticOnNhd_xiMassAnalyticTest ha ((σ : ℂ) + u * I)
  · exact xiMassAnalyticTest_neg a ((σ : ℂ) + u * I)
  · intro z hz
    have hzstrip : z ∈ xiMassStrip a := by
      change |z.im| < a
      exact lt_of_le_of_lt hz hda
    have hraw := norm_xiMassAnalyticTest_le ha
      (show 0 ≤ (((σ : ℂ) + u * I)).re by simpa using hσ.le) hzstrip
    calc
      ‖xiMassAnalyticTest a ((σ : ℂ) + u * I) z‖ ≤
          Real.exp (-σ * |z.re| + |u| * |z.im|) := by simpa using hraw
      _ ≤ Real.exp (-σ * |z.re| + |u| * d) := by
        rw [Real.exp_le_exp]
        have hm := mul_le_mul_of_nonneg_left hz (abs_nonneg u)
        linarith
      _ = Real.exp (|u| * d) * Real.exp (-σ * |z.re|) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ = Real.exp (|u| * d) * Real.exp (-(σ * |z.re|)) := by
        rw [neg_mul]

/-- The pole term `1/(s - 1)` of `P` on the line `s = 1 + 2d + 2ix` integrates against the
bottom test to `(π/2) g(0)`, for `a, σ, d > 0` with `d < a`. -/
theorem integral_xiMassBottomTest_mul_naturalPole
    {a σ d : ℝ} (ha : 0 < a) (hσ : 0 < σ) (hd : 0 < d) (hda : d < a)
    (u : ℝ) :
    (∫ x : ℝ, xiMassBottomTest a d ((σ : ℂ) + u * I) x *
        (((((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) - 1)⁻¹)) =
      (Real.pi / 2 : ℂ) * xiMassAnalyticTest a ((σ : ℂ) + u * I) 0 := by
  have hpoint (x : ℝ) :
      xiMassBottomTest a d ((σ : ℂ) + u * I) x *
          (((((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) - 1)⁻¹) =
        (2 * I)⁻¹ * (xiMassBottomTest a d ((σ : ℂ) + u * I) x *
          (((x : ℂ) - d * I)⁻¹)) := by
    have hz : ((x : ℂ) - d * I) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    have hfactor : ((((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) - 1) =
        (2 * I) * ((x : ℂ) - d * I) := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hfactor, mul_inv_rev]
    ring
  rw [show (∫ x : ℝ, xiMassBottomTest a d ((σ : ℂ) + u * I) x *
        (((((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) - 1)⁻¹)) =
      ∫ x : ℝ, (2 * I)⁻¹ *
        (xiMassBottomTest a d ((σ : ℂ) + u * I) x *
          (((x : ℂ) - d * I)⁻¹)) by
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [MeasureTheory.integral_const_mul,
    integral_xiMassBottomTest_mul_cauchy ha hσ hd hda u]
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp

set_option maxHeartbeats 600000 in
theorem integrable_one_add_two_abs_pow_nine_mul_exp_neg
    {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun x : ℝ =>
      (1 + 2 * |x|) ^ 9 * Real.exp (-σ * |x|)) := by
  have hmono (k : ℕ) : IntegrableOn
      (fun x : ℝ => x ^ k * Real.exp (-σ * x)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (k : ℝ)) (b := σ)
      (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg k)) (by norm_num) hσ
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [Real.rpow_natCast, Real.rpow_one]
  have hpos : IntegrableOn (fun x : ℝ =>
      (1 + 2 * |x|) ^ 9 * Real.exp (-σ * |x|)) (Set.Ioi 0) := by
    have hsum := (((((((((
      (hmono 0).const_mul (1 : ℝ)).add
      ((hmono 1).const_mul (18 : ℝ))).add
      ((hmono 2).const_mul (144 : ℝ))).add
      ((hmono 3).const_mul (672 : ℝ))).add
      ((hmono 4).const_mul (2016 : ℝ))).add
      ((hmono 5).const_mul (4032 : ℝ))).add
      ((hmono 6).const_mul (5376 : ℝ))).add
      ((hmono 7).const_mul (4608 : ℝ))).add
      ((hmono 8).const_mul (2304 : ℝ))).add
      ((hmono 9).const_mul (512 : ℝ))
    refine IntegrableOn.congr_fun hsum (fun x hx => ?_) measurableSet_Ioi
    rw [abs_of_pos hx]
    simp only [Pi.add_apply]
    ring
  have hpos' : IntegrableOn (fun x : ℝ =>
      (1 + 2 * |x|) ^ 9 * Real.exp (-σ * |x|)) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (f := fun x : ℝ =>
      (1 + 2 * |x|) ^ 9 * Real.exp (-σ * |x|))).mpr hpos
  have hposneg : IntegrableOn (fun x : ℝ =>
      (1 + 2 * |x|) ^ 9 * Real.exp (-σ * |x|)) (Set.Ici (-(0 : ℝ))) := by
    simpa using hpos'
  have hneg := hposneg.comp_neg_Iic (c := (0 : ℝ))
  have hneg' : IntegrableOn (fun x : ℝ =>
      (1 + 2 * |x|) ^ 9 * Real.exp (-σ * |x|)) (Set.Iic 0) := by
    simpa only [neg_zero, abs_neg] using hneg
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi]
  exact hneg'.union hpos

/-- Height-adapted contour depth `d(u) = min(a/2, 1/(1 + |u|))`, chosen so that `|u| d ≤ 1`. -/
def xiMassPrimeSquareAdaptiveDepth (a u : ℝ) : ℝ :=
  min (a / 2) (1 / (1 + |u|))

/-- For `a > 0`, the adaptive depth satisfies `0 < d < a`, `|u| d ≤ 1` and `1 + 2d ≤ 1 + a`. -/
theorem xiMassPrimeSquareAdaptiveDepth_spec
    {a : ℝ} (ha : 0 < a) (u : ℝ) :
    0 < xiMassPrimeSquareAdaptiveDepth a u ∧
    xiMassPrimeSquareAdaptiveDepth a u < a ∧
    |u| * xiMassPrimeSquareAdaptiveDepth a u ≤ 1 ∧
    1 + 2 * xiMassPrimeSquareAdaptiveDepth a u ≤ 1 + a := by
  have hden : 0 < 1 + |u| := by positivity
  have hleft : 0 < a / 2 := by positivity
  have hright : 0 < 1 / (1 + |u|) := by positivity
  have hdpos : 0 < xiMassPrimeSquareAdaptiveDepth a u := by
    rw [xiMassPrimeSquareAdaptiveDepth]
    exact lt_min hleft hright
  have hdleft : xiMassPrimeSquareAdaptiveDepth a u ≤ a / 2 := by
    exact min_le_left _ _
  have hdright : xiMassPrimeSquareAdaptiveDepth a u ≤ 1 / (1 + |u|) := by
    exact min_le_right _ _
  refine ⟨hdpos, by linarith, ?_, by linarith⟩
  calc
    |u| * xiMassPrimeSquareAdaptiveDepth a u ≤
        |u| * (1 / (1 + |u|)) :=
      mul_le_mul_of_nonneg_left hdright (abs_nonneg u)
    _ ≤ 1 := by
      rw [one_div, ← div_eq_mul_inv, div_le_one hden]
      linarith [abs_nonneg u]

theorem integrable_xiMassBottomTest_mul_naturalPole
    {a σ d : ℝ} (hσ : 0 < σ) (hd : 0 < d) (hda : d < a)
    (u : ℝ) :
    Integrable (fun x : ℝ =>
      xiMassBottomTest a d ((σ : ℂ) + u * I) x *
        (((((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) - 1)⁻¹)) := by
  have hden0 (x : ℝ) :
      ((((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) - 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hinv (x : ℝ) :
      ‖(((((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) - 1)⁻¹)‖ ≤
        (2 * d)⁻¹ := by
    rw [norm_inv]
    have hrele := Complex.abs_re_le_norm
      ((((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) - 1)
    have hre : (((((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) - 1)).re =
        2 * d := by simp
    rw [hre, abs_of_pos (by positivity : 0 < 2 * d)] at hrele
    exact inv_anti₀ (by positivity) hrele
  have hcont : Continuous (fun x : ℝ =>
      xiMassBottomTest a d ((σ : ℂ) + u * I) x *
        (((((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) - 1)⁻¹)) := by
    apply (continuous_xiMassBottomTest_of_nonneg hd.le hda _).mul
    rw [continuous_iff_continuousAt]
    intro x
    apply ContinuousAt.inv₀
    · fun_prop
    · exact hden0 x
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hσ).const_mul
      (Real.exp (|u| * d) * (2 * d)⁻¹))
    hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  calc
    ‖xiMassBottomTest a d ((σ : ℂ) + u * I) x‖ *
        ‖(((((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) - 1)⁻¹)‖ ≤
      (Real.exp (|u| * d) * Real.exp (-σ * |x|)) * (2 * d)⁻¹ :=
        mul_le_mul
          (by simpa using (norm_xiMassBottomTest_le_of_nonneg
            (x := x) (τ := ((σ : ℂ) + u * I)) hd.le hda
              (by simpa using hσ.le)))
          (hinv x) (norm_nonneg _) (by positivity)
    _ = (Real.exp (|u| * d) * (2 * d)⁻¹) *
        Real.exp (-(σ * |x|)) := by
      have he : -σ * |x| = -(σ * |x|) := by ring
      rw [he]
      ring

theorem continuous_zetaLogDerivReg_right_line
    {c : ℝ} (hc : 1 < c) :
    Continuous (fun x : ℝ =>
      RHTower.Sieve.zetaLogDerivReg ((c : ℂ) + 2 * x * I)) := by
  rw [continuous_iff_continuousAt]
  intro x
  let s : ℂ := (c : ℂ) + 2 * x * I
  have hs : 1 < s.re := by dsimp only [s]; simpa
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [s] at hre
    simp at hre
    linarith
  have hG : zetaResidueUnit s ≠ 0 := by
    apply (RHTower.Sieve.zetaResidueUnit_ne_zero_iff hs1).2
    exact riemannZeta_ne_zero_of_one_lt_re hs
  have hpath : ContinuousAt (fun y : ℝ => (c : ℂ) + 2 * y * I) x := by
    fun_prop
  have hcomp := ContinuousAt.comp_of_eq
    (f := fun y : ℝ => (c : ℂ) + 2 * y * I)
    (g := RHTower.Sieve.zetaLogDerivReg)
    (RHTower.Sieve.differentiableAt_zetaLogDerivReg hG).continuousAt
    hpath (by rfl : ((c : ℂ) + 2 * x * I) = s)
  change ContinuousAt
    (RHTower.Sieve.zetaLogDerivReg ∘
      fun y : ℝ => (c : ℂ) + 2 * y * I) x
  exact hcomp

theorem aestronglyMeasurable_xiPrimeLogHigherValuation_line
    (c : ℝ) :
    AEStronglyMeasurable (fun x : ℝ =>
      xiPrimeLogHigherValuation ((c : ℂ) + 2 * x * I)) := by
  unfold xiPrimeLogHigherValuation
  apply AEStronglyMeasurable.tsum
  rintro ⟨p, k⟩
  apply Continuous.aestronglyMeasurable
  have hn : (p : ℕ) ^ (k + 2) ≠ 0 := (pow_pos p.prop.pos _).ne'
  simp only [LSeries.term_of_ne_zero hn]
  have hbase : (((p : ℕ) ^ (k + 2) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hn
  apply Continuous.div₀ continuous_const
  · simp only [cpow_def_of_ne_zero hbase]
    fun_prop
  · intro x
    exact cpow_ne_zero_iff.mpr (Or.inl hbase)

set_option maxHeartbeats 600000 in
/-- For `a, σ > 0`, the prime-square layer is bounded on the vertical line `Re τ = σ`, uniformly
in `Im τ`: splitting `P = pole + R - H` at the adaptive depth bounds the three contributions by
`π/2`, `e K ∫ (1 + 2|x|)^9 e^{-σ|x|} dx` and `e (∑ weights) ∫ e^{-σ|x|} dx`. -/
theorem exists_norm_xiMassPrimeSquareLayer_vertical_bound
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    ∃ B : ℝ, ∀ u : ℝ,
      ‖xiMassPrimeSquareLayer a ((σ : ℂ) + u * I)‖ ≤ B := by
  obtain ⟨K, hK, hregEnvelope⟩ :=
    exists_norm_zetaLogDerivReg_right_envelope (1 + a) (by linarith)
  let P : ℝ := ∫ x : ℝ,
    (1 + 2 * |x|) ^ 9 * Real.exp (-σ * |x|)
  let J : ℝ := ∫ x : ℝ, Real.exp (-σ * |x|)
  let T : ℝ := ∑' pk : Nat.Primes × ℕ,
    xiPrimeLogHigherValuationWeight pk
  let B : ℝ := Real.pi / 2 +
    Real.exp 1 * K * P + Real.exp 1 * T * J
  refine ⟨B, fun u => ?_⟩
  let d : ℝ := xiMassPrimeSquareAdaptiveDepth a u
  obtain ⟨hd, hda, hud, hdD⟩ := xiMassPrimeSquareAdaptiveDepth_spec ha u
  have hline : 1 < 1 + 2 * d := by linarith
  have hlineD : 1 + 2 * d ≤ 1 + a := by exact hdD
  have htest (x : ℝ) :
      ‖xiMassBottomTest a d ((σ : ℂ) + u * I) x‖ ≤
        Real.exp 1 * Real.exp (-σ * |x|) := by
    have hraw := norm_xiMassBottomTest_le_of_nonneg
      (x := x) (τ := ((σ : ℂ) + u * I)) hd.le hda
      (by simpa using hσ.le)
    calc
      ‖xiMassBottomTest a d ((σ : ℂ) + u * I) x‖ ≤
          Real.exp (|u| * d) * Real.exp (-σ * |x|) := by simpa using hraw
      _ ≤ Real.exp 1 * Real.exp (-σ * |x|) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hud) (Real.exp_nonneg _)
  have hregPoint (x : ℝ) :
      ‖RHTower.Sieve.zetaLogDerivReg
        (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)‖ ≤
          K * (1 + 2 * |x|) ^ 9 := by
    have h := hregEnvelope (1 + 2 * d) hline.le hlineD (2 * x)
    have habs : |2 * x| = 2 * |x| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [habs] at h
    convert h using 1
    push_cast
    rfl
  have hPint : Integrable (fun x : ℝ =>
      (1 + 2 * |x|) ^ 9 * Real.exp (-σ * |x|)) :=
    integrable_one_add_two_abs_pow_nine_mul_exp_neg hσ
  have hJint : Integrable (fun x : ℝ => Real.exp (-σ * |x|)) := by
    simpa only [neg_mul] using integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hσ
  let pole : ℝ → ℂ := fun x =>
    xiMassBottomTest a d ((σ : ℂ) + u * I) x *
      (((((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) - 1)⁻¹)
  let reg : ℝ → ℂ := fun x =>
    xiMassBottomTest a d ((σ : ℂ) + u * I) x *
      RHTower.Sieve.zetaLogDerivReg
        (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)
  let high : ℝ → ℂ := fun x =>
    xiMassBottomTest a d ((σ : ℂ) + u * I) x *
      xiPrimeLogHigherValuation
        (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)
  have hpoleInt : Integrable pole := by
    exact integrable_xiMassBottomTest_mul_naturalPole hσ hd hda u
  have hregInt : Integrable reg := by
    refine Integrable.mono'
      (hPint.const_mul (Real.exp 1 * K)) ?_ ?_
    · exact (continuous_xiMassBottomTest_of_nonneg hd.le hda _).mul
        (continuous_zetaLogDerivReg_right_line hline) |>.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      simp only [reg, norm_mul]
      calc
        ‖xiMassBottomTest a d ((σ : ℂ) + u * I) x‖ *
            ‖RHTower.Sieve.zetaLogDerivReg
              (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)‖ ≤
          (Real.exp 1 * Real.exp (-σ * |x|)) *
            (K * (1 + 2 * |x|) ^ 9) :=
              mul_le_mul (htest x) (hregPoint x) (norm_nonneg _) (by positivity)
        _ = (Real.exp 1 * K) *
            ((1 + 2 * |x|) ^ 9 * Real.exp (-σ * |x|)) := by ring
  have hhighInt : Integrable high := by
    refine Integrable.mono'
      (hJint.const_mul (Real.exp 1 * T)) ?_ ?_
    · exact (continuous_xiMassBottomTest_of_nonneg hd.le hda _).aestronglyMeasurable.mul
        (aestronglyMeasurable_xiPrimeLogHigherValuation_line (1 + 2 * d))
    · refine Filter.Eventually.of_forall fun x => ?_
      simp only [high, norm_mul]
      have hh := norm_xiPrimeLogHigherValuation_le
        (s := (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)) (by simpa using hline.le)
      change ‖xiMassBottomTest a d ((σ : ℂ) + u * I) x‖ *
          ‖xiPrimeLogHigherValuation
            (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)‖ ≤ _
      calc
        ‖xiMassBottomTest a d ((σ : ℂ) + u * I) x‖ *
            ‖xiPrimeLogHigherValuation
              (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)‖ ≤
          (Real.exp 1 * Real.exp (-σ * |x|)) * T :=
            mul_le_mul (htest x) (by simpa only [T] using hh)
              (norm_nonneg _) (by positivity)
        _ = (Real.exp 1 * T) * Real.exp (-σ * |x|) := by ring
  have hdecomp (x : ℝ) :
      xiMassBottomTest a d ((σ : ℂ) + u * I) x *
          xiPrimeLogDirichlet
            (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I) =
        pole x + reg x - high x := by
    have hQ := xiPrimeLogDirichlet_eq_pole_add_regular_sub_higherValuation
      (s := (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I))
      (by simpa using hline)
    simp only [pole, reg, high]
    rw [hQ]
    ring
  have hintegralDecomp :
      (∫ x : ℝ, xiMassBottomTest a d ((σ : ℂ) + u * I) x *
          xiPrimeLogDirichlet
            (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)) =
        (∫ x : ℝ, pole x) + (∫ x : ℝ, reg x) -
          (∫ x : ℝ, high x) := by
    rw [show (∫ x : ℝ, xiMassBottomTest a d ((σ : ℂ) + u * I) x *
          xiPrimeLogDirichlet
            (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)) =
        ∫ x : ℝ, pole x + reg x - high x by
      exact integral_congr_ae (Filter.Eventually.of_forall hdecomp)]
    calc
      (∫ x : ℝ, pole x + reg x - high x) =
          (∫ x : ℝ, pole x + reg x) - ∫ x : ℝ, high x := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          integral_sub (hpoleInt.add hregInt) hhighInt
      _ = (∫ x : ℝ, pole x) + (∫ x : ℝ, reg x) -
          (∫ x : ℝ, high x) := by
        rw [integral_add hpoleInt hregInt]
  have hpoleValue : (∫ x : ℝ, pole x) =
      (Real.pi / 2 : ℂ) *
        xiMassAnalyticTest a ((σ : ℂ) + u * I) 0 := by
    exact integral_xiMassBottomTest_mul_naturalPole ha hσ hd hda u
  have htestZero :
      ‖xiMassAnalyticTest a ((σ : ℂ) + u * I) 0‖ ≤ 1 := by
    have hz : (0 : ℂ) ∈ xiMassStrip a := by
      change |(0 : ℂ).im| < a
      simpa using ha
    have h := norm_xiMassAnalyticTest_le ha
      (show 0 ≤ (((σ : ℂ) + u * I)).re by simpa using hσ.le) hz
    simpa using h
  have hpoleBound : ‖∫ x : ℝ, pole x‖ ≤ Real.pi / 2 := by
    rw [hpoleValue, norm_mul]
    have hpi : 0 ≤ Real.pi / 2 := by positivity
    have hcoef : ‖(Real.pi / 2 : ℂ)‖ = Real.pi / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num
    rw [hcoef]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left htestZero hpi
  have hregBound : ‖∫ x : ℝ, reg x‖ ≤ Real.exp 1 * K * P := by
    calc
      ‖∫ x : ℝ, reg x‖ ≤
          ∫ x : ℝ, (Real.exp 1 * K) *
            ((1 + 2 * |x|) ^ 9 * Real.exp (-σ * |x|)) := by
        apply norm_integral_le_of_norm_le
        · exact hPint.const_mul (Real.exp 1 * K)
        · refine Filter.Eventually.of_forall fun x => ?_
          simp only [reg, norm_mul]
          calc
            ‖xiMassBottomTest a d ((σ : ℂ) + u * I) x‖ *
                ‖RHTower.Sieve.zetaLogDerivReg
                  (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)‖ ≤
              (Real.exp 1 * Real.exp (-σ * |x|)) *
                (K * (1 + 2 * |x|) ^ 9) :=
                  mul_le_mul (htest x) (hregPoint x) (norm_nonneg _) (by positivity)
            _ = (Real.exp 1 * K) *
                ((1 + 2 * |x|) ^ 9 * Real.exp (-σ * |x|)) := by ring
      _ = Real.exp 1 * K * P := by
        rw [MeasureTheory.integral_const_mul]
  have hhighBound : ‖∫ x : ℝ, high x‖ ≤ Real.exp 1 * T * J := by
    calc
      ‖∫ x : ℝ, high x‖ ≤
          ∫ x : ℝ, (Real.exp 1 * T) * Real.exp (-σ * |x|) := by
        apply norm_integral_le_of_norm_le
        · exact hJint.const_mul (Real.exp 1 * T)
        · refine Filter.Eventually.of_forall fun x => ?_
          simp only [high, norm_mul]
          have hh := norm_xiPrimeLogHigherValuation_le
            (s := (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I))
            (by simpa using hline.le)
          calc
            ‖xiMassBottomTest a d ((σ : ℂ) + u * I) x‖ *
                ‖xiPrimeLogHigherValuation
                  (((1 + 2 * d : ℝ) : ℂ) + 2 * x * I)‖ ≤
              (Real.exp 1 * Real.exp (-σ * |x|)) * T :=
                mul_le_mul (htest x) (by simpa only [T] using hh)
                  (norm_nonneg _) (by positivity)
            _ = (Real.exp 1 * T) * Real.exp (-σ * |x|) := by ring
      _ = Real.exp 1 * T * J := by
        rw [MeasureTheory.integral_const_mul]
  have hlayer := integral_test_mul_xiPrimeLogDirichlet_eq_primeSquareLayer
    (a := a) (d := d) (τ := ((σ : ℂ) + u * I)) hd hda
      (by simpa using hσ)
  rw [← hlayer, hintegralDecomp]
  calc
    ‖(∫ x : ℝ, pole x) + (∫ x : ℝ, reg x) -
        (∫ x : ℝ, high x)‖ ≤
      ‖∫ x : ℝ, pole x‖ + ‖∫ x : ℝ, reg x‖ +
        ‖∫ x : ℝ, high x‖ := by
      exact (norm_sub_le _ _).trans
        (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ Real.pi / 2 + (Real.exp 1 * K * P) +
        (Real.exp 1 * T * J) := by
      exact add_le_add (add_le_add hpoleBound hregBound) hhighBound
    _ = B := by rfl

end

end RHTower
