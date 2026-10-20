import GaloisForLFunctions.BezoutValuationIncidence.EnergyMeanOfThePowerDampedSourceTendsToOne
import GaloisForLFunctions.BezoutValuationIncidence.ExactVasyuninReciprocityAsResidueDifferenceEnergy
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDiscreteEnergy

/-!
# The damped Chebyshev tangent form of the receiver

Differentiating the power-damped row `μ(d) d^{-η}` in the damping gives the tangent row
`-μ(d) d^{-η} log d`. Its response is the damped von Mangoldt function

`Λ_η(k) = -Σ_{d ∣ k} μ(d) d^{-η} log d`,

which equals `Λ` at `η = 0`. Its density is the derivative of `1/ζ(1+η)`, namely the energy mean
`m(η) = -ζ'(1+η)/ζ(1+η)²`. The centred prefix `A_ε(n)` of the source therefore has derivative
in the damping

`∂_ε A_ε(n) = E_ε(n) := Σ_{k ≤ n} Λ_ε(k) - n m(ε)`,

the centred damped Chebyshev function. At zero damping the source collapses to `A ≡ 1`, because
`Σ_{d ∣ k} μ(d) = [k = 1]` and `1/ζ(1+ε) → 0`. Hence `A_ε(n) - 1 = ∫_0^ε E_η(n) dη`. Minkowski's
inequality in the pronic norm `‖v‖_T² = Σ_{n ≤ T} v(n)²/(n(n+1))` then gives

`‖A_ε - 1‖_T ≤ ∫_0^ε ‖E_η‖_T dη`.

**One obligation for both halves.** Suppose `‖E_η‖_T ≤ g(η)` for every `T`, with `g` integrable
on `(0, ε₀)`. Then:

- the receiver holds at every damping below `ε₀`, with `E_T(ε) ≤ (1 + ∫_0^ε g)²`, and RH follows;
- the dual residual of the source on `[1, T]` is at most `(∫_0^ε g)²`, which tends to `0`.

So the receiver and the dual problem are both consequences of a single integrable bound on the
pronic energy of the centred damped Chebyshev function.

**Small-damping slope.** Unconditionally, `(A_ε(n) - 1)/ε → ψ(n) - n`. The truncated dual
residual therefore has slope `ε^{-2} Σ_{n ≤ T} (1 - A_ε(n))²/(n(n+1)) → Σ_{n ≤ T} (ψ(n) - n)²/(n(n+1))`,
the pronic energy of the Chebyshev error.

This module does not prove the integrable bound. That bound is the receiver in prime-counting
form, and for `η < 1/2` it is a zero-free statement.
-/

open Finset Filter Topology RHTower ArithmeticFunction MeasureTheory Set
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. The tangent row -/

/-- The damped von Mangoldt function `Λ_η(k) = -Σ_{d ∣ k} μ(d) d^{-η} log d`. -/
def dampedVonMangoldt (η : ℝ) (k : ℕ) : ℝ :=
  -∑ d ∈ k.divisors, (moebius d : ℝ) * Real.log d * (d : ℝ) ^ (-η)

/-- The damped readout `m(η) = Re(-ζ'(1+η)/ζ(1+η)²)`, the derivative of the density. -/
def dampedReadout (η : ℝ) : ℝ :=
  (-deriv riemannZeta (1 + (η : ℂ)) / riemannZeta (1 + (η : ℂ)) ^ 2).re

/-- The centred damped Chebyshev function `E_η(n) = Σ_{k ≤ n} Λ_η(k) - n m(η)`. -/
def dampedChebyshevError (η : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 n, dampedVonMangoldt η k - dampedReadout η * n

theorem hasDerivAt_natCast_rpow_neg {d : ℕ} (hd : 0 < d) (η : ℝ) :
    HasDerivAt (fun x : ℝ => (d : ℝ) ^ (-x)) (-(Real.log d * (d : ℝ) ^ (-η))) η := by
  have h := (hasDerivAt_neg η).const_rpow (a := (d : ℝ)) (by exact_mod_cast hd)
  convert h using 1
  ring

/-- The response of the power-damped row has damping derivative `Λ_η`. -/
theorem hasDerivAt_pmPowerDampedDivisorCoeff (η : ℝ) (k : ℕ) :
    HasDerivAt (fun x => pmPowerDampedDivisorCoeff x k) (dampedVonMangoldt η k) η := by
  unfold pmPowerDampedDivisorCoeff dampedVonMangoldt
  have h := HasDerivAt.fun_sum (u := k.divisors)
    (A := fun d x => (moebius d : ℝ) * (d : ℝ) ^ (-x))
    (A' := fun d => (moebius d : ℝ) * -(Real.log d * (d : ℝ) ^ (-η)))
    (fun d hd => (hasDerivAt_natCast_rpow_neg (Nat.pos_of_mem_divisors hd) η).const_mul _)
  refine h.congr_deriv ?_
  rw [← sum_neg_distrib]
  exact sum_congr rfl fun d _ => by ring

theorem one_add_ofReal_ne_one {η : ℝ} (hη : 0 < η) : (1 + (η : ℂ)) ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem one_lt_re_one_add_ofReal {η : ℝ} (hη : 0 < η) : 1 < (1 + (η : ℂ)).re := by
  simp
  linarith

/-- The density `Re(1/ζ(1+η))` has damping derivative `m(η)`. -/
theorem hasDerivAt_pmPowerDampedDivisorDensity_re {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun x => (pmPowerDampedDivisorDensity x).re) (dampedReadout η) η := by
  have hζ : HasDerivAt (fun z : ℂ => riemannZeta (1 + z)) (deriv riemannZeta (1 + (η : ℂ)))
      (η : ℂ) := by
    have h1 := (differentiableAt_riemannZeta (one_add_ofReal_ne_one hη)).hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ => 1 + z) 1 (η : ℂ) := (hasDerivAt_id _).const_add 1
    have h3 := h1.comp (η : ℂ) h2
    rw [mul_one] at h3
    exact h3
  have h := (hζ.inv (riemannZeta_ne_zero_of_one_lt_re (one_lt_re_one_add_ofReal hη))).real_of_complex
  unfold dampedReadout
  convert h using 1
  funext x
  simp [pmPowerDampedDivisorDensity, one_div]

/-- **The tangent law.** `∂_η A_η(n) = E_η(n)`. -/
theorem hasDerivAt_pmPowerDampedCenteredDivisorPrefix {η : ℝ} (hη : 0 < η) (n : ℕ) :
    HasDerivAt (fun x => pmPowerDampedCenteredDivisorPrefix x n) (dampedChebyshevError η n) η := by
  have hfun : (fun x => pmPowerDampedCenteredDivisorPrefix x n) = fun x =>
      (∑ k ∈ Icc 1 n, pmPowerDampedDivisorCoeff x k) - (pmPowerDampedDivisorDensity x).re * n := by
    funext x
    exact pmPowerDampedCenteredDivisorPrefix_eq x n
  rw [hfun]
  exact (HasDerivAt.fun_sum fun k _ => hasDerivAt_pmPowerDampedDivisorCoeff η k).sub
    ((hasDerivAt_pmPowerDampedDivisorDensity_re hη).mul_const _)

theorem continuous_natCast_rpow_neg {d : ℕ} (hd : 0 < d) :
    Continuous fun x : ℝ => (d : ℝ) ^ (-x) :=
  continuous_const.rpow continuous_neg fun _ => Or.inl (by exact_mod_cast hd.ne')

theorem continuous_dampedVonMangoldt (k : ℕ) : Continuous fun η => dampedVonMangoldt η k := by
  unfold dampedVonMangoldt
  exact (continuous_finsetSum _ fun d hd =>
    continuous_const.mul (continuous_natCast_rpow_neg (Nat.pos_of_mem_divisors hd))).neg

theorem continuousAt_dampedReadout {η : ℝ} (hη : 0 < η) : ContinuousAt dampedReadout η := by
  have han : AnalyticAt ℂ riemannZeta (1 + (η : ℂ)) :=
    DifferentiableOn.analyticAt (s := {1}ᶜ)
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
      (isOpen_compl_singleton.mem_nhds (one_add_ofReal_ne_one hη))
  have hc : ContinuousAt (fun x : ℝ => 1 + (x : ℂ)) η :=
    (continuous_const.add Complex.continuous_ofReal).continuousAt
  have hd : ContinuousAt (fun x : ℝ => deriv riemannZeta (1 + (x : ℂ))) η :=
    han.deriv.continuousAt.comp_of_eq hc rfl
  have hz : ContinuousAt (fun x : ℝ => riemannZeta (1 + (x : ℂ))) η := han.continuousAt.comp_of_eq hc rfl
  have hne : riemannZeta (1 + (η : ℂ)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (riemannZeta_ne_zero_of_one_lt_re (one_lt_re_one_add_ofReal hη))
  exact Complex.continuous_re.continuousAt.comp (hd.neg.div (hz.pow 2) hne)

theorem continuousOn_dampedChebyshevError (n : ℕ) :
    ContinuousOn (fun η => dampedChebyshevError η n) (Ioi 0) := by
  intro η hη
  apply ContinuousAt.continuousWithinAt
  unfold dampedChebyshevError
  exact (continuous_finsetSum _ fun k _ => continuous_dampedVonMangoldt k).continuousAt.sub
    ((continuousAt_dampedReadout hη).mul continuousAt_const)

/-! ## §2. Zero damping -/

theorem tendsto_one_add_ofReal_nhdsGT :
    Tendsto (fun x : ℝ => 1 + (x : ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun x : ℝ => 1 + (x : ℂ)) (𝓝 0) (𝓝 (1 + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact one_add_ofReal_ne_one hx

/-- The density `1/ζ(1+ε)` vanishes at zero damping. -/
theorem tendsto_pmPowerDampedDivisorDensity_re_zero :
    Tendsto (fun x => (pmPowerDampedDivisorDensity x).re) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] 1) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => s - 1) (𝓝 1) (𝓝 (1 - 1)) :=
      (continuous_id.sub continuous_const).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  have hq := h0.div riemannZeta_residue_one one_ne_zero
  rw [zero_div] at hq
  have hinv : Tendsto (fun s : ℂ => 1 / riemannZeta s) (𝓝[≠] 1) (𝓝 0) := by
    refine hq.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    simp only [Pi.div_apply]
    by_cases hz : riemannZeta s = 0
    · simp [hz]
    · field_simp
  have hc := (Complex.continuous_re.tendsto 0).comp (hinv.comp tendsto_one_add_ofReal_nhdsGT)
  simpa [pmPowerDampedDivisorDensity, Function.comp_def] using hc

theorem pmPowerDampedDivisorCoeff_zero_damping (k : ℕ) :
    pmPowerDampedDivisorCoeff 0 k = if k = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f k) (coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [coe_mul_zeta_apply, one_apply] at h
  unfold pmPowerDampedDivisorCoeff
  rw [← h]
  exact sum_congr rfl fun d _ => by simp

/-- **The source collapses to the constant one at zero damping.** -/
theorem tendsto_pmPowerDampedCenteredDivisorPrefix_zero {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun x => pmPowerDampedCenteredDivisorPrefix x n) (𝓝[>] 0) (𝓝 1) := by
  have hcont : Continuous fun x => ∑ k ∈ Icc 1 n, pmPowerDampedDivisorCoeff x k := by
    refine continuous_finsetSum _ fun k _ => ?_
    unfold pmPowerDampedDivisorCoeff
    exact continuous_finsetSum _ fun d hd =>
      continuous_const.mul (continuous_natCast_rpow_neg (Nat.pos_of_mem_divisors hd))
  have hval : ∑ k ∈ Icc 1 n, pmPowerDampedDivisorCoeff 0 k = 1 := by
    rw [sum_congr rfl fun k _ => pmPowerDampedDivisorCoeff_zero_damping k, sum_ite_eq']
    simp [hn]
  have h1 : Tendsto (fun x => ∑ k ∈ Icc 1 n, pmPowerDampedDivisorCoeff x k) (𝓝[>] 0) (𝓝 1) := by
    rw [← hval]
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := h1.sub (tendsto_pmPowerDampedDivisorDensity_re_zero.mul_const (n : ℝ))
  simp only [zero_mul, sub_zero] at h
  exact h.congr fun x => (pmPowerDampedCenteredDivisorPrefix_eq x n).symm

theorem dampedVonMangoldt_zero (k : ℕ) : dampedVonMangoldt 0 k = Λ k := by
  unfold dampedVonMangoldt
  simp only [neg_zero, Real.rpow_zero, mul_one]
  rw [show ∑ d ∈ k.divisors, ((moebius d : ℤ) : ℝ) * Real.log d =
      ∑ d ∈ k.divisors, ((moebius d : ℤ) : ℝ) * log d from
    sum_congr rfl fun d _ => by rw [log_apply], sum_moebius_mul_log_eq, neg_neg]

theorem tendsto_dampedReadout_zero : Tendsto dampedReadout (𝓝[>] 0) (𝓝 1) := by
  have hc := (Complex.continuous_re.tendsto 1).comp
    (tendsto_neg_deriv_div_sq_riemannZeta.comp tendsto_one_add_ofReal_nhdsGT)
  show Tendsto (fun x : ℝ => (-deriv riemannZeta (1 + (x : ℂ)) /
    riemannZeta (1 + (x : ℂ)) ^ 2).re) _ _
  simpa [Function.comp_def] using hc

/-- **The tangent at zero damping is the Chebyshev error** `ψ(n) - n`. -/
theorem tendsto_dampedChebyshevError_zero (n : ℕ) :
    Tendsto (fun η => dampedChebyshevError η n) (𝓝[>] 0) (𝓝 (∑ k ∈ Icc 1 n, Λ k - n)) := by
  have h1 : Tendsto (fun η => ∑ k ∈ Icc 1 n, dampedVonMangoldt η k) (𝓝[>] 0)
      (𝓝 (∑ k ∈ Icc 1 n, Λ k)) := by
    have hc : Continuous fun η => ∑ k ∈ Icc 1 n, dampedVonMangoldt η k :=
      continuous_finsetSum _ fun k _ => continuous_dampedVonMangoldt k
    have := (hc.continuousAt (x := 0)).tendsto
    simp only [dampedVonMangoldt_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h := h1.sub (tendsto_dampedReadout_zero.mul_const (n : ℝ))
  simpa [dampedChebyshevError, one_mul] using h

/-! ## §3. The pronic norm and Minkowski's inequality -/

/-- The pronic norm on `[1, T]`: `‖v‖_T² = Σ_{n ≤ T} v(n)²/(n(n+1))`. -/
def pronicNorm (T : ℕ) (v : ℕ → ℝ) : ℝ :=
  Real.sqrt (∑ n ∈ Icc 1 T, v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))

theorem pronicNorm_nonneg (T : ℕ) (v : ℕ → ℝ) : 0 ≤ pronicNorm T v := Real.sqrt_nonneg _

theorem pronicNorm_sq (T : ℕ) (v : ℕ → ℝ) :
    pronicNorm T v ^ 2 = ∑ n ∈ Icc 1 T, v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
  Real.sq_sqrt (sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (by positivity))

/-- Cauchy–Schwarz in the pronic norm. -/
theorem sum_mul_div_le_pronicNorm (T : ℕ) (a b : ℕ → ℝ) :
    ∑ n ∈ Icc 1 T, a n * b n / ((n : ℝ) * ((n : ℝ) + 1)) ≤ pronicNorm T a * pronicNorm T b := by
  set w : ℕ → ℝ := fun n => Real.sqrt (1 / ((n : ℝ) * ((n : ℝ) + 1)))
  have hw : ∀ n : ℕ, w n ^ 2 = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := fun n =>
    Real.sq_sqrt (by positivity)
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 T) (fun n => a n * w n) (fun n => b n * w n)
  have e1 : ∑ n ∈ Icc 1 T, a n * w n * (b n * w n) =
      ∑ n ∈ Icc 1 T, a n * b n / ((n : ℝ) * ((n : ℝ) + 1)) :=
    sum_congr rfl fun n _ => by
      rw [show a n * w n * (b n * w n) = a n * b n * w n ^ 2 by ring, hw, mul_one_div]
  have e2 : ∀ v : ℕ → ℝ, ∑ n ∈ Icc 1 T, (v n * w n) ^ 2 = pronicNorm T v ^ 2 := fun v => by
    rw [pronicNorm_sq]
    exact sum_congr rfl fun n _ => by rw [mul_pow, hw, mul_one_div]
  rw [e1, e2, e2, ← mul_pow] at hcs
  have hA := pronicNorm_nonneg T a
  have hB := pronicNorm_nonneg T b
  by_contra hlt
  have := pow_lt_pow_left₀ (lt_of_not_ge hlt) (mul_nonneg hA hB) two_ne_zero
  linarith

/-- The triangle inequality for the pronic norm. -/
theorem pronicNorm_add_le (T : ℕ) (a b : ℕ → ℝ) :
    pronicNorm T (fun n => a n + b n) ≤ pronicNorm T a + pronicNorm T b := by
  have hcs := sum_mul_div_le_pronicNorm T a b
  have hexp : ∑ n ∈ Icc 1 T, (a n + b n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
      ∑ n ∈ Icc 1 T, a n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) +
        2 * ∑ n ∈ Icc 1 T, a n * b n / ((n : ℝ) * ((n : ℝ) + 1)) +
        ∑ n ∈ Icc 1 T, b n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  have hsq : pronicNorm T (fun n => a n + b n) ^ 2 ≤ (pronicNorm T a + pronicNorm T b) ^ 2 := by
    rw [add_sq]
    simp only [pronicNorm_sq]
    rw [hexp]
    linarith
  exact (pow_le_pow_iff_left₀ (pronicNorm_nonneg _ _)
    (add_nonneg (pronicNorm_nonneg _ _) (pronicNorm_nonneg _ _)) two_ne_zero).mp hsq

theorem pronicNorm_one_le (T : ℕ) : pronicNorm T (fun _ => 1) ≤ 1 := by
  unfold pronicNorm
  have hIcc : Finset.Icc 1 T = Finset.Ico 1 (T + 1) := by
    ext
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hsum : ∑ n ∈ Icc 1 T, (1 : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ 1 := by
    simp only [one_pow]
    rw [hIcc, sum_Ico_pronic_mass one_pos (by omega)]
    have : (0 : ℝ) ≤ 1 / ((T + 1 : ℕ) : ℝ) := by positivity
    push_cast
    linarith
  exact (Real.sqrt_le_sqrt hsum).trans_eq Real.sqrt_one

/-- **Minkowski's inequality** for the pronic norm of an integral. -/
theorem pronicNorm_integral_le (T : ℕ) {δ ε : ℝ} (hδε : δ ≤ ε) (F : ℝ → ℕ → ℝ)
    (hF : ∀ n, ContinuousOn (fun η => F η n) (Icc δ ε)) :
    pronicNorm T (fun n => ∫ η in δ..ε, F η n) ≤ ∫ η in δ..ε, pronicNorm T (F η) := by
  set a : ℕ → ℝ := fun n => ∫ η in δ..ε, F η n with ha
  set S := pronicNorm T a
  set x : ℕ → ℝ := fun n => (n : ℝ) * ((n : ℝ) + 1)
  have hint : ∀ n, IntervalIntegrable (fun η => F η n) volume δ ε := fun n =>
    (hF n).intervalIntegrable_of_Icc hδε
  have hnormc : ContinuousOn (fun η => pronicNorm T (F η)) (Icc δ ε) := by
    unfold pronicNorm
    exact (continuousOn_finsetSum _ fun n _ => ((hF n).pow 2).div_const _).sqrt
  have hpair : ContinuousOn (fun η => ∑ n ∈ Icc 1 T, a n * F η n / x n) (Icc δ ε) :=
    continuousOn_finsetSum _ fun n _ => (continuousOn_const.mul (hF n)).div_const _
  have hS2 : S ^ 2 = ∫ η in δ..ε, ∑ n ∈ Icc 1 T, a n * F η n / x n := by
    rw [pronicNorm_sq, intervalIntegral.integral_finsetSum fun n _ =>
      ((hint n).const_mul (a n)).div_const (x n)]
    refine sum_congr rfl fun n _ => ?_
    have hfun : (fun η => a n * F η n / x n) = fun η => a n / x n * F η n := by
      funext η
      ring
    rw [hfun, intervalIntegral.integral_const_mul]
    simp only [ha, x]
    ring
  have hle : ∫ η in δ..ε, ∑ n ∈ Icc 1 T, a n * F η n / x n ≤
      ∫ η in δ..ε, S * pronicNorm T (F η) :=
    intervalIntegral.integral_mono_on hδε (hpair.intervalIntegrable_of_Icc hδε)
      ((hnormc.const_smul S).intervalIntegrable_of_Icc hδε)
      fun η _ => sum_mul_div_le_pronicNorm T a (F η)
  rw [intervalIntegral.integral_const_mul, ← hS2] at hle
  have hI : 0 ≤ ∫ η in δ..ε, pronicNorm T (F η) :=
    intervalIntegral.integral_nonneg hδε fun η _ => pronicNorm_nonneg T _
  have hS : 0 ≤ S := pronicNorm_nonneg T a
  nlinarith

/-! ## §4. The integral form and the criterion -/

/-- **The integral form.** `A_ε(n) - A_δ(n) = ∫_δ^ε E_η(n) dη` for `0 < δ ≤ ε`. -/
theorem pmPowerDampedCenteredDivisorPrefix_sub_eq_integral {δ ε : ℝ} (hδ : 0 < δ)
    (hδε : δ ≤ ε) (n : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε n - pmPowerDampedCenteredDivisorPrefix δ n =
      ∫ η in δ..ε, dampedChebyshevError η n := by
  have hsub : uIcc δ ε ⊆ Ioi 0 := by
    rw [uIcc_of_le hδε]
    intro x hx
    exact lt_of_lt_of_le hδ hx.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_pmPowerDampedCenteredDivisorPrefix (hsub hx) n)
    (((continuousOn_dampedChebyshevError n).mono hsub).intervalIntegrable)]

/-- **The source is the integral of its damped Chebyshev tangents.** An integrable bound `g` on
the pronic energy of `E_η` bounds the distance of the source from the constant one. -/
theorem pronicNorm_centeredPrefix_sub_one_le {ε₀ : ℝ} {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 ε₀)
    (hbound : ∀ η ∈ Ioo 0 ε₀, ∀ T : ℕ, pronicNorm T (dampedChebyshevError η) ≤ g η)
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀) (T : ℕ) :
    pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix ε n - 1) ≤
      ∫ η in (0 : ℝ)..ε, g η := by
  have hgsub : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ ε₀ → IntervalIntegrable g volume a b :=
    fun ha hab hb => hg.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le (ha.trans (hab.trans hb))]
      exact Icc_subset_Icc ha hb)
  have hstep : ∀ δ ∈ Ioo 0 ε, pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix ε n -
      pmPowerDampedCenteredDivisorPrefix δ n) ≤ ∫ η in (0 : ℝ)..ε, g η := by
    rintro δ ⟨hδ, hδε⟩
    have hcont : ∀ n, ContinuousOn (fun η => dampedChebyshevError η n) (Icc δ ε) := fun n =>
      (continuousOn_dampedChebyshevError n).mono fun x hx => lt_of_lt_of_le hδ hx.1
    have heq : (fun n => pmPowerDampedCenteredDivisorPrefix ε n -
        pmPowerDampedCenteredDivisorPrefix δ n) =
        fun n => ∫ η in δ..ε, dampedChebyshevError η n :=
      funext fun n => pmPowerDampedCenteredDivisorPrefix_sub_eq_integral hδ hδε.le n
    rw [heq]
    refine (pronicNorm_integral_le T hδε.le (fun η n => dampedChebyshevError η n) hcont).trans ?_
    have hnormc : ContinuousOn (fun η => pronicNorm T (dampedChebyshevError η)) (Icc δ ε) := by
      unfold pronicNorm
      exact (continuousOn_finsetSum _ fun n _ => ((hcont n).pow 2).div_const _).sqrt
    have h2 : ∫ η in δ..ε, pronicNorm T (dampedChebyshevError η) ≤ ∫ η in δ..ε, g η :=
      intervalIntegral.integral_mono_on hδε.le (hnormc.intervalIntegrable_of_Icc hδε.le)
        (hgsub hδ.le hδε.le hεε₀.le)
        fun η hη => hbound η ⟨lt_of_lt_of_le hδ hη.1, lt_of_le_of_lt hη.2 hεε₀⟩ T
    have h3 : ∫ η in δ..ε, g η ≤ ∫ η in (0 : ℝ)..ε, g η := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hgsub le_rfl hδ.le (hδε.le.trans hεε₀.le)) (hgsub hδ.le hδε.le hεε₀.le)]
      have h0 : 0 ≤ ∫ η in (0 : ℝ)..δ, g η := by
        rw [intervalIntegral.integral_of_le hδ.le]
        exact setIntegral_nonneg measurableSet_Ioc fun η hη =>
          (pronicNorm_nonneg T _).trans
            (hbound η ⟨hη.1, lt_of_le_of_lt hη.2 (hδε.trans hεε₀)⟩ T)
      linarith
    exact h2.trans h3
  have hlim : Tendsto (fun δ => pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix ε n -
      pmPowerDampedCenteredDivisorPrefix δ n)) (𝓝[>] 0)
      (𝓝 (pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix ε n - 1))) := by
    unfold pronicNorm
    refine (Real.continuous_sqrt.tendsto _).comp (tendsto_finsetSum _ fun n hn => ?_)
    exact ((tendsto_const_nhds.sub
      (tendsto_pmPowerDampedCenteredDivisorPrefix_zero (mem_Icc.mp hn).1)).pow 2).div_const _
  exact le_of_tendsto hlim (by filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ using hstep δ hδ)

theorem pmPowerDampedDivisorDiscreteEnergy_eq_pronicNorm_sq (ε : ℝ) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε T =
      pronicNorm T (pmPowerDampedCenteredDivisorPrefix ε) ^ 2 := by
  rw [pronicNorm_sq]
  rfl

/-- **The receiver from an integrable tangent bound**: `E_T(ε) ≤ (1 + ∫_0^ε g)²`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_le_of_tangent_bound {ε₀ : ℝ} {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 ε₀)
    (hbound : ∀ η ∈ Ioo 0 ε₀, ∀ T : ℕ, pronicNorm T (dampedChebyshevError η) ≤ g η)
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε T ≤ (1 + ∫ η in (0 : ℝ)..ε, g η) ^ 2 := by
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_pronicNorm_sq]
  have h1 := pronicNorm_centeredPrefix_sub_one_le hg hbound hε hεε₀ T
  have h2 := pronicNorm_add_le T (fun _ => 1) (fun n => pmPowerDampedCenteredDivisorPrefix ε n - 1)
  have hfun : (fun n => (1 : ℝ) + (pmPowerDampedCenteredDivisorPrefix ε n - 1)) =
      pmPowerDampedCenteredDivisorPrefix ε := by
    funext n
    ring
  rw [hfun] at h2
  have h3 := pronicNorm_one_le T
  exact pow_le_pow_left₀ (pronicNorm_nonneg _ _) (by linarith) 2

/-- **The Chebyshev tangent criterion.** If the pronic energy of the centred damped Chebyshev
function is bounded, uniformly in the horizon, by a function integrable near zero damping, then
the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_integrable_tangent_energy {ε₀ : ℝ} (hε₀ : 0 < ε₀) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 ε₀)
    (hbound : ∀ η ∈ Ioo 0 ε₀, ∀ T : ℕ, pronicNorm T (dampedChebyshevError η) ≤ g η) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_pmPowerDamped_cofinal_discrete_budget
  intro δ hδ
  have hm := lt_min hδ hε₀
  refine ⟨min δ ε₀ / 2, half_pos hm, by linarith [min_le_left δ ε₀], _, fun T =>
    pmPowerDampedDivisorDiscreteEnergy_le_of_tangent_bound hg hbound (half_pos hm)
      (by linarith [min_le_right δ ε₀]) T⟩

/-- **The dual half from the same bound**: the dual residual of the source on `[1, T]` is at most
`(∫_0^ε g)²`. -/
theorem dual_residual_le_of_tangent_bound {ε₀ : ℝ} {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 ε₀)
    (hbound : ∀ η ∈ Ioo 0 ε₀, ∀ T : ℕ, pronicNorm T (dampedChebyshevError η) ≤ g η)
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀) (T : ℕ) :
    ∑ n ∈ Icc 1 T, (1 - pmPowerDampedCenteredDivisorPrefix ε n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (∫ η in (0 : ℝ)..ε, g η) ^ 2 := by
  have h := pow_le_pow_left₀ (pronicNorm_nonneg _ _)
    (pronicNorm_centeredPrefix_sub_one_le hg hbound hε hεε₀ T) 2
  rw [pronicNorm_sq] at h
  refine le_trans (le_of_eq ?_) h
  exact sum_congr rfl fun n _ => by ring

/-! ## §5. The small-damping slope -/

/-- **Small-damping slope of the source.** `(A_ε(n) - 1)/ε → ψ(n) - n`. -/
theorem tendsto_centeredPrefix_sub_one_div {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun ε => (pmPowerDampedCenteredDivisorPrefix ε n - 1) / ε) (𝓝[>] 0)
      (𝓝 (∑ k ∈ Icc 1 n, Λ k - n)) := by
  set L := ∑ k ∈ Icc 1 n, Λ k - (n : ℝ)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro κ hκ
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), |dampedChebyshevError η n - L| ≤ κ / 2 := by
    filter_upwards [(tendsto_dampedChebyshevError_zero n).eventually
      (Metric.closedBall_mem_nhds L (half_pos hκ))] with η hη
    simpa [Metric.mem_closedBall, Real.dist_eq] using hη
  obtain ⟨ε₁, hε₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨ε₁, hε₁, fun ε hε hdist => ?_⟩
  have hε0 : 0 < ε := hε
  have hεε₁ : ε < ε₁ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε0] at hdist
    exact hdist
  set f : ℝ → ℝ := fun x => pmPowerDampedCenteredDivisorPrefix x n - L * x
  -- the slope of `f` stays within `κ/2` of zero on `(0, ε]`
  have hstep : ∀ δ ∈ Ioo 0 ε, |f ε - f δ| ≤ κ / 2 * ε := by
    rintro δ ⟨hδ, hδε⟩
    have hderiv : ∀ x ∈ Icc δ ε, HasDerivWithinAt f (dampedChebyshevError x n - L) (Icc δ ε) x :=
      fun x hx => by
        have h := (hasDerivAt_pmPowerDampedCenteredDivisorPrefix (lt_of_lt_of_le hδ hx.1) n).fun_sub
          ((hasDerivAt_id' x).const_mul L)
        exact (h.congr_deriv (by ring)).hasDerivWithinAt
    have hbd : ∀ x ∈ Ico δ ε, ‖dampedChebyshevError x n - L‖ ≤ κ / 2 := fun x hx => by
      rw [Real.norm_eq_abs]
      exact hsub ⟨lt_of_lt_of_le hδ hx.1, lt_trans hx.2 hεε₁⟩
    have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbd ε ⟨hδε.le, le_rfl⟩
    rw [Real.norm_eq_abs] at h
    nlinarith [half_pos hκ]
  have hfδ : Tendsto f (𝓝[>] 0) (𝓝 1) := by
    have h := (tendsto_pmPowerDampedCenteredDivisorPrefix_zero hn).sub
      ((tendsto_id.mono_left nhdsWithin_le_nhds).const_mul L)
    simpa [f] using h
  have hlim : |f ε - 1| ≤ κ / 2 * ε :=
    le_of_tendsto ((continuous_abs.tendsto _).comp (tendsto_const_nhds.sub hfδ))
      (by filter_upwards [Ioo_mem_nhdsGT hε0] with δ hδ using hstep δ hδ)
  rw [Real.dist_eq]
  have hrw : (pmPowerDampedCenteredDivisorPrefix ε n - 1) / ε - L = (f ε - 1) / ε := by
    simp only [f]
    field_simp
    ring
  rw [hrw, abs_div, abs_of_pos hε0, div_lt_iff₀ hε0]
  nlinarith

/-- **Small-damping slope of the dual residual**: the pronic energy of the Chebyshev error. -/
theorem tendsto_dual_residual_div_sq (T : ℕ) :
    Tendsto (fun ε => (∑ n ∈ Icc 1 T, (1 - pmPowerDampedCenteredDivisorPrefix ε n) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))) / ε ^ 2) (𝓝[>] 0)
      (𝓝 (∑ n ∈ Icc 1 T, (∑ k ∈ Icc 1 n, Λ k - n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))) := by
  have h : Tendsto (fun ε => ∑ n ∈ Icc 1 T,
      ((pmPowerDampedCenteredDivisorPrefix ε n - 1) / ε) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))
      (𝓝[>] 0)
      (𝓝 (∑ n ∈ Icc 1 T, (∑ k ∈ Icc 1 n, Λ k - n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))) :=
    tendsto_finsetSum _ fun n hn =>
      ((tendsto_centeredPrefix_sub_one_div (mem_Icc.mp hn).1).pow 2).div_const _
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  rw [sum_div]
  refine sum_congr rfl fun n _ => ?_
  field_simp
  ring

end

end GaloisForLFunctions.BezoutValuationIncidence
