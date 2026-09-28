import GaloisForLFunctions.HTGeometry.EvenAnchorProjection
import GaloisForLFunctions.RHTower.ThetaCuspKernelLogConcavity
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionSpectralEscape
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceSpectrumExact
import GaloisForLFunctions.RHTower.XiHorizontalStripDecay
import GaloisForLFunctions.RHTower.CausalThetaHalfLaplace
import GaloisForLFunctions.RHTower.ArchimedeanGenusZeroSum
import GaloisForLFunctions.RHTower.ThetaCuspComplexStrip
import GaloisForLFunctions.HTGeometry.DivisorPairing
import GaloisForLFunctions.RHTower.Sieve.EulerExpansion

/-!
# Tools for surgery on the theta source

The theta source `k` is strongly log-concave on the whole line, `k k'' - k'² ≤ -4 k²`. The
evaluation `E_u(b) = ∫ e^{-i(u + iv)x} b(x) dx` of `k` is `Ξ(u + iv)`, and `Ξ(u + iv) ≠ 0` at
arbitrarily large `u`. Also: polynomial and critical-charge integrals of `k`
(`∫ e^{x/2} k = 1/2`), the second logarithmic derivative of a positive smooth function, linearity
of finite prime deletion, and bounded derivatives of smooth compactly supported profiles.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate ContDiff

namespace RHTower

noncomputable section

theorem thetaCuspLogConcavityNumerator_neg_arg (x : ℝ) :
    thetaCuspLogConcavityNumerator (-x) = thetaCuspLogConcavityNumerator x := by
  unfold thetaCuspLogConcavityNumerator
  rw [iteratedDeriv_thetaCuspFullSource_neg 2, iteratedDeriv_thetaCuspFullSource_neg 1,
    thetaCuspFullSource_neg]
  ring

/-- **Strong log-concavity.** `k k'' - k'² ≤ -4 k²` on the whole line, i.e. `(log k)'' ≤ -4`. -/
theorem thetaCuspLogConcavityNumerator_le (x : ℝ) :
    thetaCuspLogConcavityNumerator x ≤ -4 * thetaCuspFullSource x ^ 2 := by
  have hpos : ∀ y, 0 < y →
      thetaCuspLogConcavityNumerator y ≤ -4 * thetaCuspFullSource y ^ 2 := by
    intro y hy
    have h1 := thetaCuspLogConcavityNumerator_le_firstAtom_sq hy
    have hsplit := thetaCuspFullDerivative_eq_one_add_higher 0 y
    rw [← iteratedDeriv_thetaCuspFullSource 0] at hsplit
    simp only [iteratedDeriv_zero] at hsplit
    have hr0 := thetaCuspHigherDerivative_zero_nonneg hy
    have hr1 := thetaCuspHigherDerivative_zero_le hy
    have hw := thetaCuspSourceTerm_one_pos_of_nonneg hy.le
    rw [hsplit]
    nlinarith [sq_nonneg (thetaCuspSourceTerm y 1)]
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [← thetaCuspLogConcavityNumerator_neg_arg, ← thetaCuspFullSource_neg x]
    exact hpos (-x) (by linarith)
  · have hc : Continuous fun y => thetaCuspLogConcavityNumerator y + 4 * thetaCuspFullSource y ^ 2 :=
      continuous_thetaCuspLogConcavityNumerator.add
        (continuous_const.mul (contDiff_thetaCuspFullSource.continuous.pow 2))
    have hlim : Tendsto (fun y => thetaCuspLogConcavityNumerator y + 4 * thetaCuspFullSource y ^ 2)
        (𝓝[>] 0) (𝓝 (thetaCuspLogConcavityNumerator 0 + 4 * thetaCuspFullSource 0 ^ 2)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hle := le_of_tendsto (b := 0) hlim (eventually_nhdsWithin_of_forall fun y hy => by
      have := hpos y hy; linarith)
    linarith
  · exact hpos x hx

theorem hasCompactSupport_iteratedDeriv_of_hasCompactSupport {φ : ℝ → ℝ} (h : HasCompactSupport φ) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n φ) := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem exists_bound_iteratedDeriv {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (h : HasCompactSupport φ)
    (n : ℕ) : ∃ M, ∀ j ≤ n, ∀ x, |iteratedDeriv j φ x| ≤ M := by
  have hb : ∀ j, ∃ C, ∀ x, ‖iteratedDeriv j φ x‖ ≤ C := fun j =>
    (hφ.continuous_iteratedDeriv j (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hasCompactSupport_iteratedDeriv_of_hasCompactSupport h j)
  choose C hC using hb
  refine ⟨∑ j ∈ Finset.range (n + 1), |C j|, fun j hj x => ?_⟩
  calc |iteratedDeriv j φ x| ≤ |C j| := (hC j x).trans (le_abs_self _)
    _ ≤ ∑ j ∈ Finset.range (n + 1), |C j| :=
        Finset.single_le_sum (fun i _ => abs_nonneg (C i))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem contDiff_evenAnchor (N : ℕ) (i : Fin (N + 2)) : ContDiff ℝ ∞ (evenAnchor N i) := by
  unfold evenAnchor; split_ifs <;> fun_prop

/-- `E_u(b) = ∫ e^{-i(u + iv)x} b(x) dx`. -/
def stripEval (v u : ℝ) (b : ℝ → ℝ) : ℂ :=
  ∫ x : ℝ, cexp (-I * ((u : ℂ) + v * I) * x) * (b x : ℂ)

/-- The theta source evaluates to `Ξ`. -/
theorem stripEval_thetaCuspFullSource (v u : ℝ) :
    stripEval v u thetaCuspFullSource = XiC ((u : ℂ) + v * I) := by
  rw [← HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all, thetaCuspFourierLaplace]
  rfl

theorem integrable_stripEval_thetaCuspFullSource (v u : ℝ) :
    Integrable fun x : ℝ => cexp (-I * ((u : ℂ) + v * I) * x) * (thetaCuspFullSource x : ℂ) :=
  HedenmalmThetaSource.integrable_thetaCuspFourierLaplaceIntegrand_all _

theorem integral_odd_real_eq_zero {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) : ∫ x, f x = 0 := by
  have h := integral_neg_eq_self f volume
  simp only [hf, integral_neg] at h
  linarith

theorem integrable_pow_mul_thetaCuspFullSource (j : ℕ) :
    Integrable fun x => x ^ j * thetaCuspFullSource x := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_thetaCuspFullSource_le 2
  refine ((integrable_exp_neg_abs_line).const_mul (C * j.factorial)).mono'
    ((by have := contDiff_thetaCuspFullSource.continuous; fun_prop :
      Continuous fun x : ℝ => x ^ j * thetaCuspFullSource x).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have h1 : |x| ^ j ≤ j.factorial * Real.exp |x| := by
    have := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) j
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have h2 := hC x
  calc |x| ^ j * |thetaCuspFullSource x| ≤ (j.factorial * Real.exp |x|) *
        (C * Real.exp (-(2 * |x|))) := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = C * j.factorial * Real.exp (-|x|) := by
        rw [mul_mul_mul_comm, ← Real.exp_add]; ring_nf

/-- `∫ e^{x/2} k = Ξ(i/2) = 1/2`. -/
theorem integral_exp_half_mul_thetaCuspFullSource :
    ∫ x, Real.exp (x / 2) * thetaCuspFullSource x = 1 / 2 := by
  have h := HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all (I / 2)
  rw [XiC_I_half, thetaCuspFourierLaplace] at h
  have hpt : ∀ x : ℝ, thetaCuspFourierLaplaceIntegrand (I / 2) x =
      ((Real.exp (x / 2) * thetaCuspFullSource x : ℝ) : ℂ) := by
    intro x
    simp only [thetaCuspFourierLaplaceIntegrand]
    push_cast
    congr 1
    congr 1
    ring_nf
    rw [Complex.I_sq]; ring
  simp_rw [hpt] at h
  rw [integral_complex_ofReal] at h
  have h' : ((∫ x, Real.exp (x / 2) * thetaCuspFullSource x : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    rw [h]; push_cast; ring
  exact_mod_cast h'

theorem tendsto_one_add_pow_mul_exp_neg (n : ℕ) :
    Tendsto (fun u : ℝ => (1 + u) ^ n * Real.exp (-(u / 4))) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    ((tendsto_atTop_add_const_left _ 1 tendsto_id).atTop_div_const (by norm_num : (0 : ℝ) < 4))
  have h2 := h.const_mul (4 ^ n * Real.exp (1 / 4))
  rw [mul_zero] at h2
  refine h2.congr fun u => ?_
  simp only [Function.comp_apply, id]
  rw [div_pow, show -((1 + u) / 4) = -(u / 4) + -(1 / 4) by ring, Real.exp_add]
  field_simp
  rw [mul_comm (Real.exp (1 / 4)), mul_assoc, ← Real.exp_add]
  simp

theorem iteratedDeriv_two_log_eq {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hpos : ∀ x, 0 < f x) (x : ℝ) :
    iteratedDeriv 2 (fun y => Real.log (f y)) x =
      (iteratedDeriv 2 f x * f x - iteratedDeriv 1 f x ^ 2) / f x ^ 2 := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hd' : Differentiable ℝ (deriv f) := by
    simpa [iteratedDeriv_one] using
      hf.differentiable_iteratedDeriv 1 (by exact_mod_cast ENat.coe_lt_top 1)
  have hlog : deriv (fun y => Real.log (f y)) = fun y => deriv f y / f y := by
    funext y; exact ((hd y).hasDerivAt.log (hpos y).ne').deriv
  rw [show iteratedDeriv 2 (fun y => Real.log (f y)) = deriv (deriv fun y => Real.log (f y)) by
      simp [iteratedDeriv_succ], hlog, iteratedDeriv_one,
    show iteratedDeriv 2 f = deriv (deriv f) by simp [iteratedDeriv_succ]]
  exact (((hd' x).hasDerivAt).div (hd x).hasDerivAt (hpos x).ne').deriv.trans (by ring)

theorem thetaPrimeDeletion_add (S : Finset ℕ) (f g : ℝ → ℝ) (x : ℝ) :
    thetaPrimeDeletion S (fun y => f y + g y) x =
      thetaPrimeDeletion S f x + thetaPrimeDeletion S g x := by
  simp only [thetaPrimeDeletion, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  ring

theorem two_lt_log_eight : 2 < Real.log 8 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  nlinarith [Real.exp_pos 1]

theorem XiC_not_eventually_zero (z : ℂ) : ¬ ∀ᶠ w in 𝓝 z, XiC w = 0 := by
  intro hev
  have han : AnalyticOnNhd ℂ XiC univ := fun w _ => XiC_differentiable.analyticAt w
  have h := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z) hev
  have := h (mem_univ (I / 2))
  rw [XiC_I_half] at this
  norm_num at this

/-- `Ξ(u + iv) ≠ 0` at arbitrarily large `u`. -/
theorem exists_XiC_horizontal_ne_zero (v U : ℝ) : ∃ u, U ≤ u ∧ XiC ((u : ℂ) + v * I) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set K : Set ℂ := (fun t : ℝ => (t : ℂ) + v * I) '' Icc U (U + 1)
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hfin := finite_zeros_of_isCompact isOpen_univ XiC_differentiable.differentiableOn
    (fun z _ => XiC_not_eventually_zero z) hK (subset_univ _)
  have hinf : (K ∩ {z | XiC z = 0}).Infinite := by
    have hK' : K ∩ {z | XiC z = 0} = K := Set.inter_eq_left.mpr fun z hz => by
      obtain ⟨t, ht, rfl⟩ := hz; exact hcon t ht.1
    rw [hK']
    refine (Set.Icc_infinite (by linarith : U < U + 1)).image fun a _ b _ h => ?_
    simpa using congrArg Complex.re h
  exact hinf hfin

end

end RHTower
