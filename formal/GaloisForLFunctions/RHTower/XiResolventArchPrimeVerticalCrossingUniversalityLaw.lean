import GaloisForLFunctions.RHTower.XiResolventArchPrimeSplit
import GaloisForLFunctions.RHTower.XiWardInteriorSourceBudgetDivergence

/-!
# Xi resolvent arch-prime vertical crossing universality

On every strict Euler ray, the normalized Xi logarithmic current begins below its pole-plus-Gamma
benchmark by a strictly positive prime contribution.  On the vertical line through the same point,
Gamma growth drives that current to positive infinity.  Analyticity on the zero-free half-plane
therefore forces an exact positive-height crossing of the height-zero archimedean benchmark.
-/

open Complex Filter Set Topology
open scoped Topology

namespace RHTower

noncomputable section

/-- Normalized real Xi logarithmic current on the vertical line through `1/2+x`. -/
def xiNormalizedVerticalEulerCurrent (x t : ℝ) : ℝ :=
  (logDeriv xi
    ((((1 / 2 + x : ℝ) : ℂ) + I * (t : ℂ)))).re / x

/-- Height-zero pole-plus-real-Gamma benchmark for the normalized Euler current. -/
def xiEulerArchimedeanBenchmark (x : ℝ) : ℝ :=
  ((((1 / 2 : ℂ) + (x : ℂ))⁻¹ +
      ((1 / 2 : ℂ) + (x : ℂ) - 1)⁻¹ +
      logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + (x : ℂ))) /
    (x : ℂ)).re

/-- The prime current places the height-zero Xi current strictly below its archimedean benchmark.
The strictness already follows from the prime-`2` atom. -/
theorem xiNormalizedVerticalEulerCurrent_zero_lt_benchmark
    {x : ℝ} (hx : 1 / 2 < x) :
    xiNormalizedVerticalEulerCurrent x 0 <
      xiEulerArchimedeanBenchmark x := by
  have hxpos : 0 < x := by linarith
  have hcurrent :
      xiNormalizedVerticalEulerCurrent x 0 =
        (xiResolventMoment 0 (x ^ 2)).re := by
    rw [xiNormalizedVerticalEulerCurrent]
    simp only [ofReal_zero, mul_zero, add_zero]
    have hs :
        (((1 / 2 + x : ℝ) : ℂ)) =
          (1 / 2 : ℂ) + (x : ℂ) := by
      push_cast
      ring
    rw [hs]
    rw [xiResolventMoment_zero_eq_logDeriv hxpos]
    rw [Complex.div_re, Complex.normSq_ofReal]
    simp only [ofReal_re, ofReal_im, mul_zero]
    field_simp [hxpos.ne']
    ring
  have hgap :
      0 < Real.log 2 * (2 : ℝ) ^ (-(1 / 2 + x)) / x := by
    positivity
  have hbound :=
    re_xiResolventMoment_zero_add_primeTwo_le_arch hx
  rw [hcurrent]
  unfold xiEulerArchimedeanBenchmark
  linarith

/-- The normalized vertical Euler current diverges to positive infinity on every strict Euler
ray. -/
theorem xiNormalizedVerticalEulerCurrent_tendsto_atTop
    {x : ℝ} (hx : 1 / 2 < x) :
    Tendsto (xiNormalizedVerticalEulerCurrent x) atTop atTop := by
  have hxpos : 0 < x := by linarith
  have h :=
    (re_logDeriv_xi_vertical_tendsto_atTop (h := x) hx).atTop_div_const
      hxpos
  simpa only [xiNormalizedVerticalEulerCurrent] using h

private theorem continuousOn_xiNormalizedVerticalEulerCurrent
    {x T : ℝ} (hx : 1 / 2 < x) :
    ContinuousOn (xiNormalizedVerticalEulerCurrent x) (Icc 0 T) := by
  intro t ht
  let e : ℝ → ℂ :=
    fun u => (((1 / 2 + x : ℝ) : ℂ) + I * (u : ℂ))
  have he : Continuous e := by
    unfold e
    fun_prop
  have hene : xi (e t) ≠ 0 := by
    apply xi_ne_zero_of_one_le_re
    simp [e, Complex.add_re, Complex.mul_re]
    linarith
  have hxi : AnalyticAt ℂ xi (e t) :=
    xi_analyticOnNhd_univ (e t) (Set.mem_univ _)
  have hlog : AnalyticAt ℂ (logDeriv xi) (e t) := by
    rw [show logDeriv xi = fun w => deriv xi w / xi w from rfl]
    exact hxi.deriv.div hxi hene
  have hcomp :
      ContinuousAt (fun u : ℝ => logDeriv xi (e u)) t :=
    hlog.continuousAt.comp he.continuousAt
  have hre :
      ContinuousAt (fun u : ℝ => (logDeriv xi (e u)).re) t :=
    Complex.continuous_re.continuousAt.comp hcomp
  have hdiv :
      ContinuousAt (fun u : ℝ => (logDeriv xi (e u)).re / x) t :=
    hre.div_const x
  exact
    (hdiv.congr_of_eventuallyEq (by
      filter_upwards with u
      rfl)).continuousWithinAt

/-- **Forced arch-prime crossing.**  Every strict Euler ray has a positive height where the
normalized full Xi current exactly recrosses its height-zero archimedean benchmark. -/
theorem exists_pos_xiNormalizedVerticalEulerCurrent_eq_archimedeanBenchmark
    {x : ℝ} (hx : 1 / 2 < x) :
    ∃ t : ℝ, 0 < t ∧
      xiNormalizedVerticalEulerCurrent x t =
        xiEulerArchimedeanBenchmark x := by
  have hzero :=
    xiNormalizedVerticalEulerCurrent_zero_lt_benchmark hx
  have hdiv :=
    xiNormalizedVerticalEulerCurrent_tendsto_atTop hx
  have hev :
      ∀ᶠ t : ℝ in atTop,
        xiEulerArchimedeanBenchmark x + 1 ≤
          xiNormalizedVerticalEulerCurrent x t :=
    (tendsto_atTop.1 hdiv) (xiEulerArchimedeanBenchmark x + 1)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hev
  let T := max T₀ 1
  have hTpos : 0 < T :=
    lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hhigh :
      xiEulerArchimedeanBenchmark x <
        xiNormalizedVerticalEulerCurrent x T := by
    have h := hT₀ T (le_max_left _ _)
    linarith
  have hmem :
      xiEulerArchimedeanBenchmark x ∈
        Icc (xiNormalizedVerticalEulerCurrent x 0)
          (xiNormalizedVerticalEulerCurrent x T) :=
    ⟨hzero.le, hhigh.le⟩
  obtain ⟨t, ht, heq⟩ :=
    intermediate_value_Icc hTpos.le
      (continuousOn_xiNormalizedVerticalEulerCurrent hx) hmem
  refine ⟨t, ?_, heq⟩
  have htne : t ≠ 0 := by
    intro h0
    subst t
    linarith
  exact lt_of_le_of_ne ht.1 (Ne.symm htne)

/-- **Xi resolvent arch-prime vertical crossing universality.**  The prime gap, vertical
archimedean divergence, and forced positive-height recrossing hold on every Euler ray `x>1/2`. -/
theorem xi_resolvent_archPrime_verticalCrossingUniversality
    {x : ℝ} (hx : 1 / 2 < x) :
    xiNormalizedVerticalEulerCurrent x 0 <
        xiEulerArchimedeanBenchmark x ∧
    Tendsto (xiNormalizedVerticalEulerCurrent x) atTop atTop ∧
    ∃ t : ℝ, 0 < t ∧
      xiNormalizedVerticalEulerCurrent x t =
        xiEulerArchimedeanBenchmark x := by
  exact
    ⟨xiNormalizedVerticalEulerCurrent_zero_lt_benchmark hx,
      xiNormalizedVerticalEulerCurrent_tendsto_atTop hx,
      exists_pos_xiNormalizedVerticalEulerCurrent_eq_archimedeanBenchmark hx⟩

end

end RHTower
