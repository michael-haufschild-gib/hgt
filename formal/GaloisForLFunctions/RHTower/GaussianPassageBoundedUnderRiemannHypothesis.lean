import GaloisForLFunctions.RHTower.AnchoredPhasePassageRigidity
import GaloisForLFunctions.RHTower.Sieve.ChebyshevErrorPowerBound
import GaloisForLFunctions.RHTower.PrimeVacuumErrorTransfer
import GaloisForLFunctions.RHTower.CCM.CCMGeneralizedVonKoch

/-!
# Bounded Gaussian passage is exactly the Riemann hypothesis

Consider the zero-free Gaussian Euler–continuum family `Φₓ` and its passage `x → 0⁺` into the
strip.
`AnchoredPhasePassageRigidity` proves that bounded boundary argument of the relative potential
`Lₓ + Aₓ` on every circle `C(1+iγ, r)`, `0 < r < ½`, along one sequence `xₖ → 0⁺`, implies RH.

This module proves the converse, so the step is exactly RH.  Under RH the von Koch bound
`|ψ(t) - t| ≤ C t^{½+ε}` holds.  Abel summation against the Gaussian weight
`f(t) = e^{-πxt²} t^{-w}`, together with an integration by parts for the continuum current, gives

  `Jₓ(w) - Mₓ(w) = f(1) - ∫₁^∞ f'(t) (ψ(t) - t) dt`,

where `Jₓ` is the Gaussian von Mangoldt current and `Mₓ` the continuum current.  Since
`|f'(t)| ≤ t^{-Re w - 1} (2/e + |w|)` uniformly in `x > 0`, the derivative `-Jₓ + Mₓ` of the relative
potential is bounded uniformly in `x` on `Re w ≥ ½ + 2ε`.  Integrating from `w = 2` bounds the
potential, hence its boundary argument, on every strict-right circle.

The same argument works at every abscissa (`xiZeroHalfPlaneBound_iff_gaussianPassage_bounded`).
For `0 ≤ α < ½`, the passage is bounded on every circle `C(1+iγ, r)` with `r < ½ - α` exactly when Xi
has no zero with `Re ρ > ½ + α`.  The passage therefore reads the zero-free half-plane, i.e. the
abscissa `Θ = sup Re ρ`.  It cannot localize in height: one far zero with large real part already
unbounds it.

These are receivers: they identify bounded passage with RH (and with `Θ ≤ ½ + α`) and produce
nothing towards either.
-/

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

noncomputable section

/-- The Gaussian prime weight `f(t) = e^{-πxt²} t^{-w}`. -/
def gaussianPrimeWeight (x : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-Real.pi * x * t ^ 2) : ℂ) * (t : ℂ) ^ (-w)

/-- The `t`-derivative of the Gaussian prime weight. -/
def gaussianPrimeWeightDeriv (x : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  -((Real.exp (-Real.pi * x * t ^ 2) : ℂ) * (t : ℂ) ^ (-w - 1) *
    (((2 * Real.pi * x * t ^ 2 : ℝ) : ℂ) + w))

theorem hasDerivAt_gaussianPrimeWeight (x : ℝ) {w : ℂ} (hw : w ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gaussianPrimeWeight x w) (gaussianPrimeWeightDeriv x w t) t := by
  have h1 : HasDerivAt (fun t : ℝ => ((Real.exp (-Real.pi * x * t ^ 2) : ℝ) : ℂ))
      (((Real.exp (-Real.pi * x * t ^ 2) * (-Real.pi * x * (2 * t)) : ℝ)) : ℂ) t := by
    have h := ((hasDerivAt_pow 2 t).const_mul (-Real.pi * x)).exp
    have h' : HasDerivAt (fun t : ℝ => Real.exp (-Real.pi * x * t ^ 2))
        (Real.exp (-Real.pi * x * t ^ 2) * (-Real.pi * x * (2 * t))) t := by
      convert h using 1
      simp
    exact h'.ofReal_comp
  have h2 := hasDerivAt_ofReal_cpow_const (x := t) ht.ne' (r := -w) (neg_ne_zero.mpr hw)
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hA : (t : ℂ) ^ (-w) = (t : ℂ) * (t : ℂ) ^ (-w - 1) := by
    conv_lhs => rw [show -w = (-w - 1) + 1 by ring]
    rw [Complex.cpow_add _ _ ht0, Complex.cpow_one]
    ring
  have hmul := h1.mul h2
  have hfun : gaussianPrimeWeight x w = ((fun t : ℝ => ((Real.exp (-Real.pi * x * t ^ 2) : ℝ) : ℂ)) *
      fun y : ℝ => (y : ℂ) ^ (-w)) := by
    funext t
    rfl
  rw [hfun]
  refine hmul.congr_deriv ?_
  unfold gaussianPrimeWeightDeriv
  rw [hA]
  push_cast
  ring

theorem norm_gaussianPrimeWeight_le {x : ℝ} (hx : 0 ≤ x) (w : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖gaussianPrimeWeight x w t‖ ≤ t ^ (-w.re) := by
  unfold gaussianPrimeWeight
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.neg_re]
  have hexp : Real.exp (-Real.pi * x * t ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ Real.pi * x * t ^ 2 := by positivity
    linarith
  have hpow : 0 ≤ t ^ (-w.re) := Real.rpow_nonneg ht.le _
  calc Real.exp (-Real.pi * x * t ^ 2) * t ^ (-w.re) ≤ 1 * t ^ (-w.re) :=
        mul_le_mul_of_nonneg_right hexp hpow
    _ = t ^ (-w.re) := one_mul _

/-- **Uniform derivative bound.**  `|f'(t)| ≤ t^{-Re w - 1} (2/e + |w|)` for every `x ≥ 0`. -/
theorem norm_gaussianPrimeWeightDeriv_le {x : ℝ} (hx : 0 ≤ x) (w : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖gaussianPrimeWeightDeriv x w t‖ ≤ t ^ (-w.re - 1) * (2 * Real.exp (-1) + ‖w‖) := by
  unfold gaussianPrimeWeightDeriv
  rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have hre : (-w - 1).re = -w.re - 1 := by simp
  rw [hre]
  set E := Real.exp (-Real.pi * x * t ^ 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff]
    have : 0 ≤ Real.pi * x * t ^ 2 := by positivity
    linarith
  have hy : (Real.pi * x * t ^ 2) * E ≤ Real.exp (-1) := by
    have := Real.mul_exp_neg_le_exp_neg_one (Real.pi * x * t ^ 2)
    rw [hE]
    convert this using 2
    ring_nf
  have hsum : ‖(((2 * Real.pi * x * t ^ 2 : ℝ) : ℂ) + w)‖ ≤ 2 * Real.pi * x * t ^ 2 + ‖w‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hpow : 0 ≤ t ^ (-w.re - 1) := Real.rpow_nonneg ht.le _
  have hkey : E * ‖(((2 * Real.pi * x * t ^ 2 : ℝ) : ℂ) + w)‖ ≤ 2 * Real.exp (-1) + ‖w‖ := by
    calc E * ‖(((2 * Real.pi * x * t ^ 2 : ℝ) : ℂ) + w)‖
        ≤ E * (2 * Real.pi * x * t ^ 2 + ‖w‖) := mul_le_mul_of_nonneg_left hsum hE0.le
      _ = 2 * ((Real.pi * x * t ^ 2) * E) + E * ‖w‖ := by ring
      _ ≤ 2 * Real.exp (-1) + 1 * ‖w‖ := by
          gcongr
      _ = 2 * Real.exp (-1) + ‖w‖ := by ring
  calc E * t ^ (-w.re - 1) * ‖(((2 * Real.pi * x * t ^ 2 : ℝ) : ℂ) + w)‖
      = t ^ (-w.re - 1) * (E * ‖(((2 * Real.pi * x * t ^ 2 : ℝ) : ℂ) + w)‖) := by ring
    _ ≤ t ^ (-w.re - 1) * (2 * Real.exp (-1) + ‖w‖) := mul_le_mul_of_nonneg_left hkey hpow

theorem continuousOn_gaussianPrimeWeightDeriv (x : ℝ) (w : ℂ) :
    ContinuousOn (gaussianPrimeWeightDeriv x w) (Ioi 0) := by
  intro t ht
  have ht0 : (t : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr ht
  unfold gaussianPrimeWeightDeriv
  apply ContinuousAt.continuousWithinAt
  have hc : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (-w - 1)) t :=
    (Complex.continuous_ofReal.continuousAt).cpow continuousAt_const ht0
  have hA : ContinuousAt (fun t : ℝ => ((Real.exp (-Real.pi * x * t ^ 2) : ℝ) : ℂ)) t := by
    fun_prop
  have hC : ContinuousAt (fun t : ℝ => (((2 * Real.pi * x * t ^ 2 : ℝ)) : ℂ)) t := by
    fun_prop
  exact ((hA.mul hc).mul (hC.add continuousAt_const)).neg

/-- **Abel identity.**  For `N ≥ 1`,
`Σ_{2 ≤ k ≤ N} Λ(k) f(k) - ∫₁^N f = f(N)(ψ(N) - N) + f(1) - ∫₁^N f'(t)(ψ(t) - t) dt`. -/
theorem gaussianPrimeWeight_abel (x : ℝ) {w : ℂ} (hw : w ≠ 0) {N : ℕ} (hN : 1 ≤ N) :
    (∑ k ∈ Finset.Ioc 1 N, gaussianPrimeWeight x w k * (ArithmeticFunction.vonMangoldt k : ℂ)) -
        ∫ t in (1 : ℝ)..N, gaussianPrimeWeight x w t =
      gaussianPrimeWeight x w N * ((Chebyshev.psi N : ℂ) - N) + gaussianPrimeWeight x w 1 -
        ∫ t in (1 : ℝ)..N, gaussianPrimeWeightDeriv x w t * ((Chebyshev.psi t : ℂ) - t) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hderiv : ∀ t ∈ Icc (1 : ℝ) N,
      HasDerivAt (gaussianPrimeWeight x w) (gaussianPrimeWeightDeriv x w t) t :=
    fun t ht => hasDerivAt_gaussianPrimeWeight x hw (zero_lt_one.trans_le ht.1)
  have hcont : ContinuousOn (gaussianPrimeWeightDeriv x w) (Icc (1 : ℝ) N) :=
    (continuousOn_gaussianPrimeWeightDeriv x w).mono
      (fun t ht => show (0 : ℝ) < t from zero_lt_one.trans_le ht.1)
  have hderivEq : EqOn (deriv (gaussianPrimeWeight x w)) (gaussianPrimeWeightDeriv x w)
      (Icc (1 : ℝ) N) := fun t ht => (hderiv t ht).deriv
  have hint : IntegrableOn (deriv (gaussianPrimeWeight x w)) (Icc (1 : ℝ) N) volume :=
    (hcont.integrableOn_Icc).congr_fun hderivEq.symm measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul'
    (fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℂ))
    (f := gaussianPrimeWeight x w) (n := 1) (m := N) hN
    (fun t ht => by exact_mod_cast (hderiv t (by simpa using ht)).differentiableAt)
    (by simpa using hint)
  have hpsiN : (∑ k ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt k : ℂ)) =
      (Chebyshev.psi N : ℂ) := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    push_cast
    rfl
  have hpsi1 : (∑ k ∈ Finset.Icc 0 1, (ArithmeticFunction.vonMangoldt k : ℂ)) = 0 := by
    simp [Finset.sum_Icc_succ_top]
  have hpsiT : ∀ t : ℝ, (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ)) =
      (Chebyshev.psi t : ℂ) := by
    intro t
    rw [Chebyshev.psi_eq_sum_Icc]
    push_cast
    rfl
  rw [hpsiN, hpsi1, mul_zero, sub_zero] at habel
  simp only [Nat.cast_one] at habel
  have hint2 : ∫ t in Ioc (1 : ℝ) N, deriv (gaussianPrimeWeight x w) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ) =
      ∫ t in (1 : ℝ)..N, gaussianPrimeWeightDeriv x w t * (Chebyshev.psi t : ℂ) := by
    rw [intervalIntegral.integral_of_le hN1]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [hderivEq ⟨ht.1.le, ht.2⟩, hpsiT]
  rw [hint2] at habel
  -- integration by parts for the continuum
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := 1) (b := (N : ℝ)) (u := gaussianPrimeWeight x w) (v := fun t : ℝ => (t : ℂ))
    (u' := gaussianPrimeWeightDeriv x w) (v' := fun _ => (1 : ℂ))
    (fun t ht => hderiv t (by rwa [Set.uIcc_of_le hN1] at ht))
    (fun t _ => by simpa using (hasDerivAt_id t).ofReal_comp)
    ((hcont.intervalIntegrable_of_Icc hN1))
    intervalIntegrable_const
  simp only [mul_one] at hibp
  have hpsiInt : IntervalIntegrable (fun t : ℝ => gaussianPrimeWeightDeriv x w t *
      (Chebyshev.psi t : ℂ)) volume 1 N := by
    have hmono : IntervalIntegrable (fun t : ℝ => (Chebyshev.psi t : ℂ)) volume 1 N := by
      have h := (Chebyshev.psi_mono).intervalIntegrable (μ := volume) (a := 1) (b := (N : ℝ))
      exact ⟨h.1.ofReal, h.2.ofReal⟩
    exact hmono.continuousOn_mul (by rwa [Set.uIcc_of_le hN1])
  have htInt : IntervalIntegrable (fun t : ℝ => gaussianPrimeWeightDeriv x w t * (t : ℂ))
      volume 1 N :=
    (hcont.mul Complex.continuous_ofReal.continuousOn).intervalIntegrable_of_Icc hN1
  have hsplit : ∫ t in (1 : ℝ)..N, gaussianPrimeWeightDeriv x w t * ((Chebyshev.psi t : ℂ) - t) =
      (∫ t in (1 : ℝ)..N, gaussianPrimeWeightDeriv x w t * (Chebyshev.psi t : ℂ)) -
        ∫ t in (1 : ℝ)..N, gaussianPrimeWeightDeriv x w t * (t : ℂ) := by
    rw [← intervalIntegral.integral_sub hpsiInt htInt]
    congr 1
    funext t
    ring
  rw [hsplit, habel, hibp]
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_natCast]
  ring

/-- **Uniform finite bound under a von Koch estimate.** -/
theorem norm_gaussianPrimeWeight_abel_le {x : ℝ} (hx : 0 ≤ x) {w : ℂ} (hw : w ≠ 0)
    {e ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) (hσ : e + ε ≤ w.re)
    (hE : ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ e)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖(∑ k ∈ Finset.Ioc 1 N, gaussianPrimeWeight x w k * (ArithmeticFunction.vonMangoldt k : ℂ)) -
        ∫ t in (1 : ℝ)..N, gaussianPrimeWeight x w t‖ ≤
      C + 1 + C * (2 * Real.exp (-1) + ‖w‖) / ε := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [gaussianPrimeWeight_abel x hw hN]
  set K := 2 * Real.exp (-1) + ‖w‖ with hK
  have hK0 : 0 ≤ K := by positivity
  -- endpoint term
  have hend : ‖gaussianPrimeWeight x w N * ((Chebyshev.psi N : ℂ) - N)‖ ≤ C := by
    rw [norm_mul]
    have h1 := norm_gaussianPrimeWeight_le hx w (zero_lt_one.trans_le hN1)
    have h2 : ‖((Chebyshev.psi N : ℂ) - N)‖ ≤ C * (N : ℝ) ^ e := by
      have : ((Chebyshev.psi N : ℂ) - N) = ((Chebyshev.psi N - N : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs]
      exact hE N hN1
    have hprod : (N : ℝ) ^ (-w.re) * (N : ℝ) ^ e ≤ 1 := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hN1)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    calc ‖gaussianPrimeWeight x w N‖ * ‖((Chebyshev.psi N : ℂ) - N)‖
        ≤ (N : ℝ) ^ (-w.re) * (C * (N : ℝ) ^ e) :=
          mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)
      _ = C * ((N : ℝ) ^ (-w.re) * (N : ℝ) ^ e) := by ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hprod hC
      _ = C := mul_one C
  have hone : ‖gaussianPrimeWeight x w 1‖ ≤ 1 := by
    have := norm_gaussianPrimeWeight_le hx w (zero_lt_one : (0 : ℝ) < 1)
    simpa using this
  -- integral term
  have hintBound : ‖∫ t in (1 : ℝ)..N,
      gaussianPrimeWeightDeriv x w t * ((Chebyshev.psi t : ℂ) - t)‖ ≤ C * K / ε := by
    have hpt : ∀ t ∈ Icc (1 : ℝ) N,
        ‖gaussianPrimeWeightDeriv x w t * ((Chebyshev.psi t : ℂ) - t)‖ ≤
          C * K * t ^ (-1 - ε) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans_le ht.1
      rw [norm_mul]
      have h1 := norm_gaussianPrimeWeightDeriv_le hx w ht0
      have h2 : ‖((Chebyshev.psi t : ℂ) - t)‖ ≤ C * t ^ e := by
        have : ((Chebyshev.psi t : ℂ) - t) = ((Chebyshev.psi t - t : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs]
        exact hE t ht.1
      have hexp : t ^ (-w.re - 1) * t ^ e ≤ t ^ (-1 - ε) := by
        rw [← Real.rpow_add ht0]
        exact Real.rpow_le_rpow_of_exponent_le ht.1 (by linarith)
      calc ‖gaussianPrimeWeightDeriv x w t‖ * ‖((Chebyshev.psi t : ℂ) - t)‖
          ≤ (t ^ (-w.re - 1) * K) * (C * t ^ e) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = C * K * (t ^ (-w.re - 1) * t ^ e) := by ring
        _ ≤ C * K * t ^ (-1 - ε) := mul_le_mul_of_nonneg_left hexp (by positivity)
    have h0 : (0 : ℝ) ∉ Set.uIcc 1 (N : ℝ) := by
      rw [Set.uIcc_of_le hN1]
      intro h
      linarith [h.1]
    have hg : IntervalIntegrable (fun t : ℝ => C * K * t ^ (-1 - ε)) volume 1 N :=
      (intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).const_mul (C * K)
    have hle := intervalIntegral.norm_integral_le_of_norm_le hN1
      (Eventually.of_forall fun t ht => hpt t ⟨ht.1.le, ht.2⟩) hg
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, h0⟩)]
    have hfin : ((N : ℝ) ^ (-1 - ε + 1) - (1 : ℝ) ^ (-1 - ε + 1)) / (-1 - ε + 1) ≤ 1 / ε := by
      rw [Real.one_rpow, show -1 - ε + 1 = -ε by ring]
      have hNp : 0 ≤ (N : ℝ) ^ (-ε) := Real.rpow_nonneg (by linarith) _
      have heq : ((N : ℝ) ^ (-ε) - 1) / (-ε) = (1 - (N : ℝ) ^ (-ε)) / ε := by
        rw [div_neg, ← neg_div, neg_sub]
      rw [heq]
      exact div_le_div_of_nonneg_right (by linarith) hε.le
    calc C * K * (((N : ℝ) ^ (-1 - ε + 1) - (1 : ℝ) ^ (-1 - ε + 1)) / (-1 - ε + 1))
        ≤ C * K * (1 / ε) := mul_le_mul_of_nonneg_left hfin (by positivity)
      _ = C * K / ε := by ring
  calc ‖gaussianPrimeWeight x w N * ((Chebyshev.psi N : ℂ) - N) + gaussianPrimeWeight x w 1 -
        ∫ t in (1 : ℝ)..N, gaussianPrimeWeightDeriv x w t * ((Chebyshev.psi t : ℂ) - t)‖
      ≤ ‖gaussianPrimeWeight x w N * ((Chebyshev.psi N : ℂ) - N)‖ + ‖gaussianPrimeWeight x w 1‖ +
          ‖∫ t in (1 : ℝ)..N,
            gaussianPrimeWeightDeriv x w t * ((Chebyshev.psi t : ℂ) - t)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ C + 1 + C * K / ε := by gcongr

/-! ## Passing to the limit -/

theorem continuousOn_gaussianPrimeWeight (x : ℝ) (w : ℂ) :
    ContinuousOn (gaussianPrimeWeight x w) (Ioi 0) := by
  intro t ht
  have ht0 : (t : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr ht
  unfold gaussianPrimeWeight
  apply ContinuousAt.continuousWithinAt
  have hc : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (-w)) t :=
    (Complex.continuous_ofReal.continuousAt).cpow continuousAt_const ht0
  have hA : ContinuousAt (fun t : ℝ => ((Real.exp (-Real.pi * x * t ^ 2) : ℝ) : ℂ)) t := by
    fun_prop
  exact hA.mul hc

theorem integrableOn_gaussianPrimeWeight {x : ℝ} (hx : 0 < x) {w : ℂ} (hw : 0 ≤ w.re) :
    IntegrableOn (gaussianPrimeWeight x w) (Ioi 1) volume := by
  have hdom := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (p := 2) (b := Real.pi * x)
    (by norm_num) (by norm_num) (mul_pos Real.pi_pos hx)).mono_set
      (fun t (ht : 1 < t) => show (0 : ℝ) < t from zero_lt_one.trans ht)
  refine hdom.mono' ((continuousOn_gaussianPrimeWeight x w).mono
    (fun t (ht : 1 < t) => show (0 : ℝ) < t from zero_lt_one.trans ht)
      |>.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht1 : (1 : ℝ) < t := ht
  have ht0 : 0 < t := zero_lt_one.trans ht1
  unfold gaussianPrimeWeight
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.neg_re, Real.rpow_zero, one_mul,
    Real.rpow_two]
  have hp : t ^ (-w.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1.le (by linarith)
  calc Real.exp (-Real.pi * x * t ^ 2) * t ^ (-w.re) ≤ Real.exp (-Real.pi * x * t ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = Real.exp (-(Real.pi * x) * t ^ 2) := by ring_nf

theorem tendsto_integral_gaussianPrimeWeight {x : ℝ} (hx : 0 < x) {w : ℂ} (hw : 0 ≤ w.re) :
    Tendsto (fun N : ℕ => ∫ t in (1 : ℝ)..N, gaussianPrimeWeight x w t) atTop
      (𝓝 (gaussianContinuumCurrent x w)) := by
  have hlim := intervalIntegral_tendsto_integral_Ioi (μ := volume) 1
    (integrableOn_gaussianPrimeWeight hx hw) tendsto_natCast_atTop_atTop
  have heq : gaussianContinuumCurrent x w = ∫ t in Ioi (1 : ℝ), gaussianPrimeWeight x w t := by
    rw [gaussianContinuumCurrent, integral_Ici_eq_integral_Ioi]
    rfl
  rw [heq]
  exact hlim

theorem tendsto_sum_gaussianPrimeWeight_vonMangoldt {x : ℝ} (hx : 0 < x) {w : ℂ}
    (hw : 0 ≤ w.re) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Ioc 1 N,
        gaussianPrimeWeight x w k * (ArithmeticFunction.vonMangoldt k : ℂ)) atTop
      (𝓝 (gaussianVonMangoldtCurrent x w)) := by
  set G : ℕ → ℂ := fun n => gaussianPrimeWeight x w n * (ArithmeticFunction.vonMangoldt n : ℂ)
    with hG
  have hG01 : ∀ n : ℕ, n ≤ 1 → G n = 0 := by
    intro n hn
    interval_cases n <;> simp [hG]
  have hbound : ∀ n : ℕ, ‖G n‖ ≤ (n : ℝ) ^ (1 : ℝ) *
      Real.exp (-(Real.pi * x * (n : ℝ) ^ (2 : ℝ))) := by
    intro n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · rw [hG01 n (by omega), norm_zero]
      positivity
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      simp only [hG, gaussianPrimeWeight]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Real.rpow_one, Real.rpow_two]
      have hp : (n : ℝ) ^ (-w.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
      have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ n :=
        ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self hn0.le)
      have hE : Real.exp (-Real.pi * x * (n : ℝ) ^ 2) = Real.exp (-(Real.pi * x * (n : ℝ) ^ 2)) := by
        ring_nf
      rw [hE]
      calc Real.exp (-(Real.pi * x * (n : ℝ) ^ 2)) * (n : ℝ) ^ (-w.re) *
            (ArithmeticFunction.vonMangoldt n : ℝ)
          ≤ Real.exp (-(Real.pi * x * (n : ℝ) ^ 2)) * 1 * n := by
            gcongr
        _ = (n : ℝ) * Real.exp (-(Real.pi * x * (n : ℝ) ^ 2)) := by ring
  have hsum : Summable G := Summable.of_norm_bounded
    (GaloisForLFunctions.HTGeometry.summable_rpow_mul_exp_neg_rpow (A := 1)
      (mul_pos Real.pi_pos hx) (by norm_num : (0 : ℝ) < 2)) hbound
  have hsupp : Function.support G ⊆ {n : ℕ | 2 ≤ n} := by
    intro n hn
    by_contra h
    exact hn (hG01 n (by simp at h; omega))
  have hJ : gaussianVonMangoldtCurrent x w = ∑' n, G n := by
    rw [gaussianVonMangoldtCurrent_eq_tsum_cpow,
      ← tsum_subtype_eq_of_support_subset hsupp]
    refine tsum_congr fun n => ?_
    simp only [hG, gaussianPrimeWeight, Complex.ofReal_natCast]
    ring
  rw [hJ]
  have hlim := hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine hlim.congr fun N => ?_
  simp only [Function.comp_apply]
  refine (Finset.sum_subset (fun k hk => ?_) (fun k hk hk' => ?_)).symm
  · rw [Finset.mem_Ioc] at hk
    exact Finset.mem_range.mpr (by omega)
  · rw [Finset.mem_range] at hk
    rw [Finset.mem_Ioc] at hk'
    exact hG01 k (by omega)

/-- **Uniform bound on the derivative of the relative potential under a von Koch estimate.** -/
theorem norm_gaussianVonMangoldtCurrent_sub_continuum_le {x : ℝ} (hx : 0 < x) {w : ℂ}
    {e ε C : ℝ} (he : 0 ≤ e) (hε : 0 < ε) (hC : 0 ≤ C) (hσ : e + ε ≤ w.re)
    (hE : ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ e) :
    ‖gaussianVonMangoldtCurrent x w - gaussianContinuumCurrent x w‖ ≤
      C + 1 + C * (2 * Real.exp (-1) + ‖w‖) / ε := by
  have hre : 0 ≤ w.re := by linarith
  have hw : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hσ
    linarith
  have hlim := ((tendsto_sum_gaussianPrimeWeight_vonMangoldt hx hre).sub
    (tendsto_integral_gaussianPrimeWeight hx hre)).norm
  refine le_of_tendsto hlim (eventually_atTop.mpr ⟨1, fun N hN => ?_⟩)
  exact norm_gaussianPrimeWeight_abel_le hx.le hw hε hC hσ hE hN

/-! ## The potential and its boundary argument -/

theorem norm_gaussianEulerLog_two_le {x : ℝ} (hx : 0 ≤ x) : ‖gaussianEulerLog x 2‖ ≤ 2 := by
  rw [gaussianEulerLog_eq_tsum_cpow]
  have hbd : ∀ n : GaussianEulerIndex,
      ‖gaussianEulerAmplitude x n * (n.1 : ℂ) ^ (-(2 : ℂ))‖ ≤ 1 / (n.1 : ℝ) ^ 2 := by
    intro n
    have hn0 : 0 < n.1 := by have := n.2; omega
    have hnR : (0 : ℝ) < n.1 := by exact_mod_cast hn0
    rw [norm_mul, gaussianEulerAmplitude, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_natCast_cpow_of_pos hn0]
    have hc := norm_eulerLogDirichletCoeff_le_one n.1
    have hexp : Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ Real.pi * x * (n.1 : ℝ) ^ 2 := by positivity
      linarith
    have hre : (-(2 : ℂ)).re = -2 := by norm_num
    rw [hre, Real.rpow_neg hnR.le, Real.rpow_two, one_div]
    have hinv : 0 ≤ ((n.1 : ℝ) ^ 2)⁻¹ := by positivity
    calc ‖eulerLogDirichletCoeff n.1‖ * Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) *
          ((n.1 : ℝ) ^ 2)⁻¹ ≤ 1 * 1 * ((n.1 : ℝ) ^ 2)⁻¹ := by gcongr
      _ = ((n.1 : ℝ) ^ 2)⁻¹ := by ring
  have hsumB : Summable (fun n : GaussianEulerIndex => 1 / (n.1 : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Subtype.val_injective
  have hsumN : Summable (fun n : GaussianEulerIndex =>
      ‖gaussianEulerAmplitude x n * (n.1 : ℂ) ^ (-(2 : ℂ))‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbd hsumB
  have hzeta : ∑' n : ℕ, 1 / (n : ℝ) ^ 2 = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by
    have := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  calc ‖∑' n : GaussianEulerIndex, gaussianEulerAmplitude x n * (n.1 : ℂ) ^ (-(2 : ℂ))‖
      ≤ ∑' n : GaussianEulerIndex, ‖gaussianEulerAmplitude x n * (n.1 : ℂ) ^ (-(2 : ℂ))‖ :=
        norm_tsum_le_tsum_norm hsumN
    _ ≤ ∑' n : GaussianEulerIndex, 1 / (n.1 : ℝ) ^ 2 := hsumN.tsum_le_tsum hbd hsumB
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 :=
        Summable.tsum_subtype_le (fun n : ℕ => 1 / (n : ℝ) ^ 2) {n : ℕ | 2 ≤ n}
          (fun n => by positivity) (Real.summable_one_div_nat_pow.mpr one_lt_two)
    _ ≤ 2 := by rw [hzeta]; exact hpi

/-- **Uniform bound on the relative potential under a von Koch estimate.** -/
theorem norm_gaussianRelativePotential_le {x : ℝ} (hx : 0 < x) {e ε C R : ℝ} (he : 0 ≤ e)
    (hε : 0 < ε) (hε' : e + ε ≤ 2) (hC : 0 ≤ C) (hR : 2 ≤ R)
    (hE : ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ e) {s : ℂ}
    (hs : e + ε ≤ s.re) (hsR : ‖s‖ ≤ R) :
    ‖gaussianRelativePotential x s‖ ≤
      2 + (C + 1 + C * (2 * Real.exp (-1) + R) / ε) * (R + 2) := by
  set D := C + 1 + C * (2 * Real.exp (-1) + R) / ε with hDdef
  set S : Set ℂ := {w | e + ε ≤ w.re} ∩ Metric.closedBall 0 R with hSdef
  have hconv : Convex ℝ S := (convex_halfSpace_re_ge _).inter (convex_closedBall 0 R)
  have hderiv : ∀ w ∈ S, HasDerivWithinAt (gaussianRelativePotential x)
      (-gaussianVonMangoldtCurrent x w + gaussianContinuumCurrent x w) S w :=
    fun w _ => (hasDerivAt_gaussianRelativePotential hx w).hasDerivWithinAt
  have hbound : ∀ w ∈ S,
      ‖-gaussianVonMangoldtCurrent x w + gaussianContinuumCurrent x w‖ ≤ D := by
    intro w hw
    have h1 := norm_gaussianVonMangoldtCurrent_sub_continuum_le hx he hε hC hw.1 hE
    have hwR : ‖w‖ ≤ R := by simpa using hw.2
    rw [show -gaussianVonMangoldtCurrent x w + gaussianContinuumCurrent x w =
      -(gaussianVonMangoldtCurrent x w - gaussianContinuumCurrent x w) by ring, norm_neg]
    refine h1.trans ?_
    rw [hDdef]
    gcongr
  have h2S : (2 : ℂ) ∈ S := ⟨by simp; linarith, by simp; linarith⟩
  have hsS : s ∈ S := ⟨hs, by simpa using hsR⟩
  have hmv := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound h2S hsS
  have hP2 : gaussianRelativePotential x 2 = gaussianEulerLog x 2 := by
    rw [gaussianRelativePotential, gaussianContinuumPrimitive_two hx, add_zero]
  have hs2 : ‖s - 2‖ ≤ R + 2 := (norm_sub_le _ _).trans (by simp; linarith)
  have hD : 0 ≤ D := by positivity
  calc ‖gaussianRelativePotential x s‖
      ≤ ‖gaussianRelativePotential x 2‖ +
          ‖gaussianRelativePotential x s - gaussianRelativePotential x 2‖ :=
        norm_le_insert' _ _
    _ ≤ 2 + D * (R + 2) := by
        gcongr
        · rw [hP2]
          exact norm_gaussianEulerLog_two_le hx.le
        · exact hmv.trans (mul_le_mul_of_nonneg_left hs2 hD)

/-- **Bounded passage from a Chebyshev power bound.**  If `|ψ(t) - t| ≤ C tᵉ` and the circle
`C(1+iγ, r)` lies in `Re s ≥ e + ε`, the Gaussian passage has uniformly bounded boundary argument on
it along `xₖ = 1/(k+1)`. -/
theorem gaussianPassage_bounded_of_psi_bound {e ε C : ℝ} (he : 0 ≤ e) (hε : 0 < ε) (hC : 0 ≤ C)
    (hE : ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ e) {r : ℝ} (her : e + ε ≤ 1 - r)
    (γ : ℝ) (hr0 : 0 < r) :
    ∃ x : ℕ → ℝ, (∀ k, 0 < x k) ∧ Tendsto x atTop (𝓝 0) ∧ ∃ M : ℝ, ∀ k, ∃ m : ℝ,
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        |(gaussianRelativePotential (x k) (circleMap (1 + γ * I) r θ)).im - m| ≤ M := by
  have hr1 : r ≤ 1 := by linarith
  set R := |γ| + 3 with hRdef
  set B := 2 + (C + 1 + C * (2 * Real.exp (-1) + R) / ε) * (R + 2) with hB
  refine ⟨fun k => 1 / ((k : ℝ) + 1), fun k => by positivity,
    tendsto_one_div_add_atTop_nhds_zero_nat, 2 * Real.pi * B, fun k => ⟨0, ?_⟩⟩
  have hxk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hpt : ∀ θ : ℝ, |(gaussianRelativePotential (1 / ((k : ℝ) + 1))
      (circleMap (1 + γ * I) r θ)).im - 0| ≤ B := by
    intro θ
    rw [sub_zero]
    refine (Complex.abs_im_le_norm _).trans ?_
    set c : ℂ := 1 + (γ : ℂ) * I with hc
    have hcre : c.re = 1 := by simp [hc]
    have hdist : ‖circleMap c r θ - c‖ = r := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr0]
    have hsre : e + ε ≤ (circleMap c r θ).re := by
      have h1 := Complex.abs_re_le_norm (circleMap c r θ - c)
      rw [Complex.sub_re, hcre, hdist] at h1
      linarith [neg_abs_le ((circleMap c r θ).re - 1)]
    have hcnorm : ‖c‖ ≤ 1 + |γ| := by
      refine (norm_add_le _ _).trans ?_
      simp
    have hsR : ‖circleMap c r θ‖ ≤ R := by
      have : ‖circleMap c r θ‖ ≤ ‖c‖ + ‖circleMap c r θ - c‖ := norm_le_insert' _ _
      rw [hdist] at this
      rw [hRdef]
      linarith
    exact norm_gaussianRelativePotential_le hxk he hε (by linarith) hC
      (by rw [hRdef]; linarith [abs_nonneg γ]) hE hsre hsR
  have hcont : Continuous (fun θ : ℝ => |(gaussianRelativePotential (1 / ((k : ℝ) + 1))
      (circleMap (1 + γ * I) r θ)).im - 0|) :=
    (((Complex.continuous_im.comp ((differentiable_gaussianRelativePotential hxk).continuous.comp
      (continuous_circleMap _ _))).sub continuous_const).abs)
  calc ∫ θ in (0 : ℝ)..2 * Real.pi,
        |(gaussianRelativePotential (1 / ((k : ℝ) + 1)) (circleMap (1 + γ * I) r θ)).im - 0|
      ≤ ∫ _θ in (0 : ℝ)..2 * Real.pi, B :=
        intervalIntegral.integral_mono_on (by positivity) (hcont.intervalIntegrable _ _)
          intervalIntegrable_const (fun θ _ => hpt θ)
    _ = 2 * Real.pi * B := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring

/-- **Route 1 step 2 under RH.**  Under RH the Gaussian passage has uniformly bounded boundary
argument on every strict-right circle. -/
theorem gaussianPassage_boundaryArgOscillation_bounded_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∀ γ r : ℝ, 0 < r → r < 1 / 2 → ∃ x : ℕ → ℝ, (∀ k, 0 < x k) ∧
      Tendsto x atTop (𝓝 0) ∧ ∃ M : ℝ, ∀ k, ∃ m : ℝ,
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          |(gaussianRelativePotential (x k) (circleMap (1 + γ * I) r θ)).im - m| ≤ M := by
  intro γ r hr0 hr
  set ε := (1 / 2 - r) / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨C, hC0, hCb⟩ := Sieve.exists_chebyshevPsiReal_error_power_bound hRH hε
  have hE : ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ (1 / 2 + ε) := by
    intro t ht
    rw [← chebyshevPsiReal_eq_psi]
    exact hCb t ht
  exact gaussianPassage_bounded_of_psi_bound (e := 1 / 2 + ε) (ε := ε) (by positivity) hε
    hC0.le hE (by rw [hεdef]; linarith) γ hr0

/-- **Route 1, step 2 is exactly the Riemann hypothesis.**  Bounded boundary argument of the
Gaussian Euler–continuum passage on every strict-right circle, along some sequence `xₖ → 0⁺`, is
equivalent to RH. -/
theorem riemannHypothesis_iff_gaussianPassage_boundaryArgOscillation_bounded :
    RiemannHypothesis ↔
      ∀ γ r : ℝ, 0 < r → r < 1 / 2 → ∃ x : ℕ → ℝ, (∀ k, 0 < x k) ∧
        Tendsto x atTop (𝓝 0) ∧ ∃ M : ℝ, ∀ k, ∃ m : ℝ,
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            |(gaussianRelativePotential (x k) (circleMap (1 + γ * I) r θ)).im - m| ≤ M :=
  ⟨gaussianPassage_boundaryArgOscillation_bounded_of_riemannHypothesis,
    riemannHypothesis_of_gaussianPassage_boundaryArgOscillation_bounded⟩

/-! ## Every abscissa: bounded passage measures the zero-free half-plane -/

/-- Continuity of a function restricted to a circle, from continuity on the closed disc. -/
private theorem continuous_comp_circleMap_of_closedBall {G : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hG : ContinuousOn G (closedBall c r)) :
    Continuous (fun θ : ℝ => G (circleMap c r θ)) :=
  hG.comp_continuous (continuous_circleMap c r)
    (fun θ => sphere_subset_closedBall (circleMap_mem_sphere c hr θ))

/-- **Single-circle rigidity.**  Bounded boundary argument of the Gaussian passage on one circle
`C(1+iγ, r)`, `0 < r < ½`, along some `xₖ → 0⁺`, excludes every Xi zero inside the circle. -/
theorem xi_ne_zero_of_gaussianPassage_circle_bounded {γ r : ℝ} (hr0 : 0 < r) (hr : r < 1 / 2)
    (h : ∃ x : ℕ → ℝ, (∀ k, 0 < x k) ∧ Tendsto x atTop (𝓝 0) ∧ ∃ M : ℝ, ∀ k, ∃ m : ℝ,
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          |(gaussianRelativePotential (x k) (circleMap (1 + γ * I) r θ)).im - m| ≤ M) :
    ∀ z ∈ ball (1 + (γ : ℂ) * I) r, xi z ≠ 0 := by
  set c : ℂ := 1 + (γ : ℂ) * I with hc
  have hcre : c.re = 1 := by simp [hc]
  have hball_re : ∀ s ∈ ball c (1 / 2), 1 / 2 < s.re := by
    intro s hs
    rw [mem_ball, dist_eq_norm] at hs
    have h1 := Complex.abs_re_le_norm (s - c)
    rw [Complex.sub_re, hcre] at h1
    linarith [neg_abs_le (s.re - 1)]
  obtain ⟨x, hxpos, hx0, M, hosc⟩ := h
  have hhd : DifferentiableOn ℂ gaussianArchimedeanHalfFactor (ball c (1 / 2)) := fun s hs =>
    (differentiableAt_gaussianArchimedeanHalfFactor
      (by linarith [hball_re s hs])).differentiableWithinAt
  have hhne : ∀ s ∈ ball c (1 / 2), gaussianArchimedeanHalfFactor s ≠ 0 := fun s hs =>
    gaussianArchimedeanHalfFactor_ne_zero (by linarith [hball_re s hs])
  obtain ⟨g, hgd, -, hgeq⟩ :=
    GaloisForLFunctions.HTGeometry.exists_log_on_ball (by norm_num) hhd hhne
  set ℓ : ℂ := Complex.log (gaussianArchimedeanHalfFactor c) with hℓ
  have hℓexp : Complex.exp ℓ = gaussianArchimedeanHalfFactor c :=
    Complex.exp_log (hhne c (mem_ball_self (by norm_num)))
  set G : ℕ → ℂ → ℂ := fun k s => ℓ + g s + gaussianRelativePotential (x k) s with hGdef
  have hGd : ∀ k, DifferentiableOn ℂ (G k) (ball c (1 / 2)) := fun k =>
    (differentiableOn_const _).add hgd |>.add
      (differentiable_gaussianRelativePotential (hxpos k)).differentiableOn
  have hcbr : closedBall c r ⊆ ball c (1 / 2) := closedBall_subset_ball hr
  have hgcont : Continuous (fun θ : ℝ => (g (circleMap c r θ)).im) :=
    Complex.continuous_im.comp (continuous_comp_circleMap_of_closedBall hr0.le (hgd.continuousOn.mono hcbr))
  set Mg : ℝ := ∫ θ in (0 : ℝ)..2 * Real.pi, |(g (circleMap c r θ)).im| with hMg
  have hoscG : ∀ k, ∃ m : ℝ,
      ∫ θ in (0 : ℝ)..2 * Real.pi, |(G k (circleMap c r θ)).im - m| ≤ M + Mg := by
    intro k
    obtain ⟨m, hm⟩ := hosc k
    refine ⟨m + ℓ.im, ?_⟩
    have hPcont : Continuous (fun θ : ℝ =>
        (gaussianRelativePotential (x k) (circleMap c r θ)).im) :=
      Complex.continuous_im.comp
        ((differentiable_gaussianRelativePotential (hxpos k)).continuous.comp
          (continuous_circleMap c r))
    have hi1 : IntervalIntegrable (fun θ : ℝ =>
        |(gaussianRelativePotential (x k) (circleMap c r θ)).im - m|) volume 0
        (2 * Real.pi) := ((hPcont.sub continuous_const).abs).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun θ : ℝ => |(g (circleMap c r θ)).im|) volume 0
        (2 * Real.pi) := hgcont.abs.intervalIntegrable _ _
    have hle : ∫ θ in (0 : ℝ)..2 * Real.pi, |(G k (circleMap c r θ)).im - (m + ℓ.im)| ≤
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          (|(gaussianRelativePotential (x k) (circleMap c r θ)).im - m| +
            |(g (circleMap c r θ)).im|) := by
      refine intervalIntegral.integral_mono_on (by positivity) ?_ (hi1.add hi2) ?_
      · exact ((Complex.continuous_im.comp (((continuous_const.add
          (hgd.continuousOn.mono hcbr |> fun h => continuous_comp_circleMap_of_closedBall hr0.le h)).add
          ((differentiable_gaussianRelativePotential (hxpos k)).continuous.comp
            (continuous_circleMap c r))))).sub continuous_const).abs.intervalIntegrable _ _
      · intro θ _
        have heq : (G k (circleMap c r θ)).im - (m + ℓ.im) =
            ((gaussianRelativePotential (x k) (circleMap c r θ)).im - m) +
              (g (circleMap c r θ)).im := by
          simp only [hGdef, Complex.add_im]
          ring
        rw [heq]
        exact abs_add_le _ _
    rw [intervalIntegral.integral_add hi1 hi2] at hle
    linarith
  set z₁ : ℂ := c + ((r / 2 : ℝ) : ℂ) with hz₁def
  set V : Set ℂ := ball c r ∩ {s : ℂ | 1 < s.re} with hVdef
  have hVopen : IsOpen V := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hz₁V : z₁ ∈ V := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, hz₁def, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · show 1 < z₁.re
      simp [hz₁def, hcre]
      linarith
  have hxin : Tendsto x atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx0, Eventually.of_forall hxpos⟩
  have hconv : ∀ z ∈ V, Tendsto (fun k => Complex.exp (G k z)) atTop (𝓝 (xi z)) := by
    intro z hz
    have hzb : z ∈ ball c (1 / 2) := ball_subset_ball hr.le hz.1
    have heq : ∀ k, Complex.exp (G k z) = gaussianEulerContinuumFormation (x k) z := by
      intro k
      simp only [hGdef, gaussianEulerContinuumFormation, Complex.exp_add, hℓexp]
      rw [← hgeq z hzb]
    simp_rw [heq]
    exact (tendstoLocallyUniformlyOn_gaussianEulerContinuumFormation.tendsto_at
      (show z ∈ gaussianSafeEulerChart from hz.2)).comp hxin
  exact ne_zero_of_anchored_boundaryArgOscillation_bounded hr0 hr hGd hoscG
    xi_differentiable.differentiableOn hVopen inter_subset_left hz₁V
    (xi_ne_zero_of_one_le_re (le_of_lt hz₁V.2)) hconv

/-- Bounded passage on every circle inside `Re s > ½ + α` excludes zeros with `Re ρ > ½ + α`. -/
theorem xiZeroHalfPlaneBound_of_gaussianPassage_bounded {α : ℝ} (hα0 : 0 ≤ α)
    (h : ∀ γ r : ℝ, 0 < r → r < 1 / 2 - α → ∃ x : ℕ → ℝ, (∀ k, 0 < x k) ∧
      Tendsto x atTop (𝓝 0) ∧ ∃ M : ℝ, ∀ k, ∃ m : ℝ,
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          |(gaussianRelativePotential (x k) (circleMap (1 + γ * I) r θ)).im - m| ≤ M) :
    XiZeroHalfPlaneBound α := by
  intro ρ hρ
  by_contra hgt
  push Not at hgt
  have hre : ρ.re < 1 := by
    by_contra hge
    push Not at hge
    exact xi_ne_zero_of_one_le_re hge hρ
  set r := (1 - ρ.re + (1 / 2 - α)) / 2 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hrα : r < 1 / 2 - α := by rw [hrdef]; linarith
  have hr : r < 1 / 2 := by linarith
  have hmem : ρ ∈ ball (1 + (ρ.im : ℂ) * I) r := by
    rw [mem_ball, dist_eq_norm]
    have hdiff : ρ - (1 + (ρ.im : ℂ) * I) = ((ρ.re - 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith), hrdef]
    linarith
  exact xi_ne_zero_of_gaussianPassage_circle_bounded hr0 hr (h ρ.im r hr0 hrα) ρ hmem hρ

/-- A zero-free half-plane `Re s > ½ + α` gives bounded passage on every circle inside it. -/
theorem gaussianPassage_bounded_of_xiZeroHalfPlaneBound {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 1 / 2)
    (hXi : XiZeroHalfPlaneBound α) :
    ∀ γ r : ℝ, 0 < r → r < 1 / 2 - α → ∃ x : ℕ → ℝ, (∀ k, 0 < x k) ∧
      Tendsto x atTop (𝓝 0) ∧ ∃ M : ℝ, ∀ k, ∃ m : ℝ,
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          |(gaussianRelativePotential (x k) (circleMap (1 + γ * I) r θ)).im - m| ≤ M := by
  intro γ r hr0 hr
  set ε := (1 / 2 - α - r) / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨C, hC0, hCb⟩ :=
    Sieve.exists_chebyshevPsiReal_error_power_bound_of_xiZeroHalfPlaneBound hα0 hα hXi hε
  have hE : ∀ t : ℝ, 1 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ (1 / 2 + α + ε) := by
    intro t ht
    rw [← chebyshevPsiReal_eq_psi]
    exact hCb t ht
  exact gaussianPassage_bounded_of_psi_bound (e := 1 / 2 + α + ε) (ε := ε) (by linarith) hε
    hC0.le hE (by rw [hεdef]; linarith) γ hr0

/-- **Route 1's step 2 at every abscissa.**  For `0 ≤ α < ½`, Xi has no zero with
`Re ρ > ½ + α` if and only if the Gaussian passage has bounded boundary argument on every circle
`C(1+iγ, r)` with `r < ½ - α`.  The passage reads the zero-free half-plane, not a local region. -/
theorem xiZeroHalfPlaneBound_iff_gaussianPassage_bounded {α : ℝ} (hα0 : 0 ≤ α)
    (hα : α < 1 / 2) :
    XiZeroHalfPlaneBound α ↔
      ∀ γ r : ℝ, 0 < r → r < 1 / 2 - α → ∃ x : ℕ → ℝ, (∀ k, 0 < x k) ∧
        Tendsto x atTop (𝓝 0) ∧ ∃ M : ℝ, ∀ k, ∃ m : ℝ,
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            |(gaussianRelativePotential (x k) (circleMap (1 + γ * I) r θ)).im - m| ≤ M :=
  ⟨gaussianPassage_bounded_of_xiZeroHalfPlaneBound hα0 hα,
    xiZeroHalfPlaneBound_of_gaussianPassage_bounded hα0⟩

end

end RHTower
