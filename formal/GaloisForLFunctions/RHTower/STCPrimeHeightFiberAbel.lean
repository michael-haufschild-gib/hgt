import GaloisForLFunctions.RHTower.PrimeTraceCriticalEnergyBudget
import GaloisForLFunctions.RHTower.PrimeLogPowZetaAbelPole

/-!
# Fixed-height cancellation of the critical Euler prime source

The literal complex prime log-square series is the derivative of the prime-log
current in its Euler half-plane. Its normalized boundary value vanishes at
every fixed nonzero vertical displacement from the pole, because the continued
prime-log current is analytic there. This supplies the arithmetic gate for
the STC spectral-height fibre theorem without an abstract source surrogate.
-/

open Complex Filter Topology
namespace RHTower
noncomputable section

/-- The literal complex log-square prime series. -/
def primeLogSquareComplex (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes,
    (Real.log ((p : ℕ) : ℝ) : ℂ) ^ 2 * (((p : ℕ) : ℂ) ^ (-s))

/-- Termwise differentiation identifies the source series with the
derivative of the existing prime-log current. -/
theorem primeLogSquareComplex_eq_neg_deriv_primeGradeSource
    {s : ℂ} (hs : 1 < s.re) :
    primeLogSquareComplex s = -deriv primeGradeSource s := by
  set b : ℝ := (1 + s.re) / 2 with hbdef
  have hb : 1 < b := by dsimp [b]; linarith
  have hbs : b < s.re := by dsimp [b]; linarith
  have hopen : IsOpen {z : ℂ | b < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmajorant : Summable (fun p : Nat.Primes =>
      |Real.log ((p : ℕ) : ℝ)| * (((p : ℕ) : ℝ) ^ (-b))) := by
    have hlog : Summable fun n : ℕ =>
        |Real.log (n : ℝ)| ^ 1 * (n : ℝ) ^ (-b) :=
      summable_abs_log_natCast_pow_mul_rpow_neg 1 b hb
    simpa only [pow_one, Function.comp_def] using hlog.comp_injective
      (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
  have hderiv := Complex.hasSum_deriv_of_summable_norm
    (u := fun p : Nat.Primes =>
      |Real.log ((p : ℕ) : ℝ)| * (((p : ℕ) : ℝ) ^ (-b)))
    (F := fun (p : Nat.Primes) (w : ℂ) =>
      (Real.log ((p : ℕ) : ℝ) : ℂ) * coronaPrimeEigenvalue w p)
    hmajorant
    (fun p => ((differentiable_primeCpowNeg p).differentiableOn).const_mul _)
    hopen
    (fun p w hw => by
      have hwre : b < w.re := hw
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_coronaPrimeEigenvalue]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast p.prop.one_lt.le) (by linarith)) (abs_nonneg _))
    (show s ∈ {z : ℂ | b < z.re} from hbs)
  have hterm : ∀ p : Nat.Primes,
      deriv (fun w : ℂ =>
        (Real.log ((p : ℕ) : ℝ) : ℂ) * coronaPrimeEigenvalue w p) s =
        -((Real.log ((p : ℕ) : ℝ) : ℂ) ^ 2 * coronaPrimeEigenvalue s p) := by
    intro p
    have h := ((hasDerivAt_coronaPrimeEigenvalue s p).const_mul
      (Real.log ((p : ℕ) : ℝ) : ℂ)).deriv
    convert h using 1 <;> ring
  have hsum : HasSum (fun p : Nat.Primes =>
      -((Real.log ((p : ℕ) : ℝ) : ℂ) ^ 2 * coronaPrimeEigenvalue s p))
      (deriv primeGradeSource s) := by
    unfold primeGradeSource
    exact hderiv.congr_fun (fun p => (hterm p).symm)
  have hsum' := hsum.neg
  rw [primeLogSquareComplex]
  simpa only [coronaPrimeEigenvalue, neg_neg] using hsum'.tsum_eq

/-- The same source identity expressed through its canonical continuation. -/
theorem primeLogSquareComplex_eq_neg_deriv_continuation
    {s : ℂ} (hs : 1 < s.re) :
    primeLogSquareComplex s = -deriv xiPrimeLogDirichletContinuation s := by
  rw [primeLogSquareComplex_eq_neg_deriv_primeGradeSource hs]
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heq : primeGradeSource =ᶠ[𝓝 s] xiPrimeLogDirichletContinuation := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact primeGradeSource_eq_continuation hz
  rw [heq.deriv_eq]

/-- The continuation is analytic at every fixed nonzero height on the one-line. -/
theorem analyticAt_primeLogContinuation_one_line {τ : ℝ} (hτ : τ ≠ 0) :
    AnalyticAt ℂ xiPrimeLogDirichletContinuation
      (1 + (τ : ℂ) * Complex.I) := by
  let w : ℂ := 1 + (τ : ℂ) * Complex.I
  have hw1 : w ≠ 1 := by
    intro h
    apply hτ
    have him := congrArg Complex.im h
    simpa [w] using him
  have hζ : riemannZeta w ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    simp [w]
  have hanζ : AnalyticAt ℂ riemannZeta w :=
    analyticOn_riemannZeta w (by simpa using hw1)
  have hanFlux : AnalyticAt ℂ infinitePrimeFlux w := by
    change AnalyticAt ℂ (-(deriv riemannZeta / riemannZeta)) w
    exact (hanζ.deriv.div hanζ hζ).neg
  have hopen : IsOpen {z : ℂ | (1 : ℝ) / 2 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hanTail : AnalyticAt ℂ xiPrimeLogHigherValuation w :=
    (differentiableOn_xiPrimeLogHigherValuation_halfPlane.analyticOnNhd hopen)
      w (by norm_num [w])
  exact hanFlux.sub hanTail

/-- Fixed nonzero height has zero normalized critical log-square prime mass. -/
theorem tendsto_primeLogSquareComplex_fixed_nonzero_height
    {c τ : ℝ} (hc : 0 < c) (hτ : τ ≠ 0) :
    Tendsto (fun v : ℝ =>
      (v : ℂ) ^ 2 * primeLogSquareComplex (1 + ((c * v : ℝ) : ℂ) + (τ : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
  let w : ℂ := 1 + (τ : ℂ) * Complex.I
  have hA : AnalyticAt ℂ xiPrimeLogDirichletContinuation w :=
    analyticAt_primeLogContinuation_one_line hτ
  have hcont : ContinuousAt (deriv xiPrimeLogDirichletContinuation) w :=
    hA.deriv.continuousAt
  have hcoord : Tendsto (fun v : ℝ =>
      (1 : ℂ) + ((c * v : ℝ) : ℂ) + (τ : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    have h : ContinuousAt (fun v : ℝ =>
      (1 : ℂ) + ((c * v : ℝ) : ℂ) + (τ : ℂ) * Complex.I) 0 := by
      fun_prop
    simpa [w] using h.tendsto.mono_left nhdsWithin_le_nhds
  have hsq : Tendsto (fun v : ℝ => (v : ℂ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have h : ContinuousAt (fun v : ℝ => (v : ℂ) ^ 2) 0 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := hsq.mul (hcont.tendsto.comp hcoord).neg
  have hlim' : Tendsto (fun v : ℝ =>
      (v : ℂ) ^ 2 * -deriv xiPrimeLogDirichletContinuation
        (1 + ((c * v : ℝ) : ℂ) + (τ : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa [w] using hlim
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hs : 1 < ((1 : ℂ) + ((c * v : ℝ) : ℂ) + (τ : ℂ) * Complex.I).re := by
    simp
    exact mul_pos hc hv
  rw [primeLogSquareComplex_eq_neg_deriv_continuation hs]

end
end RHTower
