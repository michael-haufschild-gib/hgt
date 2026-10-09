import GaloisForLFunctions.RHTower.LiouvilleExponentialSumSimplicity

/-!
# The exponential Liouville sum: power bounds and the zero abscissa

Let `J(t) = Σ_{n ≥ 1} λ(n) e^{-nt}/n`.  If `J(t) = O(t^{a})` as `t → 0⁺` for some `a ≤ ½`, then
every zero of `ζ` satisfies `Re ρ ≤ 1 − a` (`re_le_of_liouvilleExpSum_isBigO`).  In particular
`J(t) = O(t^{½−δ})` for every `δ > 0` implies RH
(`riemannHypothesis_of_forall_liouvilleExpSum_isBigO`).  This is the multiplicity-blind, power-lossy
form of the Liouville receiver.  The exact forms `J ≥ −C√t(1 + log^k(1/t))` additionally cap the
orders of critical zeros (`le_of_liouvilleExpSum_lower_logPow`).

**Proof.**  The bound and the decay `|J(t)| ≤ 2e^{−t}` (`t ≥ 1`) make the Mellin transform of `J`
holomorphic on `Re s > −a` (Mathlib's `mellin_differentiableAt_of_isBigO_rpow_exp`).  On `Re s > 0`
it equals `Γ(s)L(λ, s+1) = Γ(s+1)Z(2s+2)/((2s+1)Z(s+1))`, `Z(w) = (w−1)ζ(w)`, so by the identity
theorem `𝓜J(s)·(2s+1)Z(s+1) = Γ(s+1)Z(2s+2)` on `Re s > −a`.  A zero `w` of `Z` with
`Re w > 1 − a` gives `s = w − 1` there with left side `0` and right side `Γ(w)Z(2w) ≠ 0`.
-/

open Complex Filter Topology MeasureTheory Set Asymptotics
open scoped LSeries.notation

namespace RHTower

noncomputable section

theorem liouvilleExpSum_isBigO_atTop :
    (fun t : ℝ => (liouvilleExpSum t : ℂ)) =O[atTop] fun t => Real.exp (-1 * t) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le, neg_one_mul]
  exact abs_liouvilleExpSum_le_large ht

theorem locallyIntegrableOn_liouvilleExpSum :
    LocallyIntegrableOn (fun t : ℝ => (liouvilleExpSum t : ℂ)) (Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn continuousOn_liouvilleExpSum).locallyIntegrableOn
    measurableSet_Ioi

/-- **A power bound for `J` at `0` bounds the zero abscissa.**  If `J(t) = O(t^{a})` as `t → 0⁺`
with `0 < a ≤ ½`, then every zero `w` of `(s − 1)ζ(s)` has `Re w ≤ 1 − a`. -/
theorem re_le_of_liouvilleExpSum_isBigO {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2)
    (h : (fun t : ℝ => liouvilleExpSum t) =O[𝓝[>] 0] fun t => t ^ a)
    {w : ℂ} (hzero : zetaResidueUnit w = 0) : w.re ≤ 1 - a := by
  by_contra hlt
  push Not at hlt
  set U : Set ℂ := {s : ℂ | -a < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hbot : (fun t : ℝ => (liouvilleExpSum t : ℂ)) =O[𝓝[>] 0] fun t : ℝ => t ^ (-(-a)) := by
    rw [neg_neg]
    refine IsBigO.of_norm_left ?_
    have e : (fun t : ℝ => ‖(liouvilleExpSum t : ℂ)‖) = fun t => ‖liouvilleExpSum t‖ := by
      funext t; rw [Complex.norm_real]
    rw [e]
    exact h.norm_left
  have hdiff : ∀ s ∈ U, DifferentiableAt ℂ (mellin fun t : ℝ => (liouvilleExpSum t : ℂ)) s :=
    fun s hs => mellin_differentiableAt_of_isBigO_rpow_exp one_pos
      locallyIntegrableOn_liouvilleExpSum liouvilleExpSum_isBigO_atTop hbot hs
  set F : ℂ → ℂ := fun s => mellin (fun t : ℝ => (liouvilleExpSum t : ℂ)) s *
    ((2 * s + 1) * zetaResidueUnit (s + 1)) with hF
  have hFa : AnalyticOnNhd ℂ F U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUo
    exact ((hdiff s hs).mul ((((differentiableAt_const _).mul differentiableAt_id).add
      (differentiableAt_const _)).mul ((analyticAt_zetaResidueUnit _).differentiableAt.comp s
        (differentiableAt_id.add (differentiableAt_const _))))).differentiableWithinAt
  have hGa : AnalyticOnNhd ℂ (fun s : ℂ => Gamma (s + 1) * zetaResidueUnit (2 * s + 2)) U :=
    fun s hs => ((analyticAt_Gamma_of_pos_re (by simp [hU] at hs ⊢; linarith)).comp
      (analyticAt_id.add analyticAt_const)).mul
      ((analyticAt_zetaResidueUnit _).comp ((analyticAt_const.mul analyticAt_id).add
        analyticAt_const))
  have h1U : (1 : ℂ) ∈ U := by simp [hU]; linarith
  have hev : F =ᶠ[𝓝 (1 : ℂ)] fun s : ℂ => Gamma (s + 1) * zetaResidueUnit (2 * s + 2) := by
    have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with s hs
    have hs0 : 0 < s.re := hs
    have h2 : 2 * s + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hZ : zetaResidueUnit (s + 1) ≠ 0 :=
      zetaResidueUnit_ne_zero_of_one_lt_re (by simp; linarith)
    simp only [hF]
    rw [mellin_liouvilleExpSum hs0, Gamma_mul_LSeries_eq_kernel hs0]
    unfold liouvilleExpKernel
    exact div_mul_cancel₀ _ (mul_ne_zero h2 hZ)
  have hEq := hFa.eqOn_of_preconnected_of_eventuallyEq hGa
    (convex_halfSpace_re_gt _).isPreconnected h1U hev
  have hs₀ : w - 1 ∈ U := by simp [hU]; linarith
  have hval := hEq hs₀
  simp only [hF, show w - 1 + 1 = w by ring, hzero, mul_zero] at hval
  have hG : Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hZ2 : zetaResidueUnit (2 * (w - 1) + 2) ≠ 0 := by
    rw [show 2 * (w - 1) + 2 = 2 * w by ring]
    exact zetaResidueUnit_ne_zero_of_one_lt_re (by simp; linarith)
  exact mul_ne_zero hG hZ2 hval.symm

/-- **Power-lossy Liouville bounds give RH.**  If `Σ λ(n)e^{−nt}/n = O(t^{½−δ})` as `t → 0⁺` for
every `δ > 0`, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_forall_liouvilleExpSum_isBigO
    (h : ∀ ε : ℝ, 0 < ε → (fun t : ℝ => liouvilleExpSum t) =O[𝓝[>] 0] fun t => t ^ (1 / 2 - ε)) :
    RiemannHypothesis := by
  rw [Sieve.riemannHypothesis_iff_zetaResidueUnit_ne_zero]
  intro w hw hzero
  have hw1 : w.re ≤ 1 := by
    by_contra hc; push Not at hc; exact zetaResidueUnit_ne_zero_of_one_lt_re hc hzero
  have hd0 : 0 < (w.re - 1 / 2) / 2 := by linarith
  have := re_le_of_liouvilleExpSum_isBigO (a := 1 / 2 - (w.re - 1 / 2) / 2) (by linarith)
    (by linarith) (h _ hd0) hzero
  linarith

end

end RHTower
