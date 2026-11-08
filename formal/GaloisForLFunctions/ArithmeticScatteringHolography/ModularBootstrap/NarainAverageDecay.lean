import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainTargetAverage
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanNumerator
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.ScalarMellinMainTerms

/-!
# Decay obstructions detected by one averaged Narain source

The actual double target average has a nonvanishing numerator at every
arithmetic resonance. A power remainder would extend its cleared Mellin
identity across every faster pole. This gives a zero-free half-plane
from a claimed rate, and the three-quarter rate implies RH.
-/

open Complex RHTower MeasureTheory Set Filter Topology Asymptotics
open GaloisForLFunctions.BlackHoleRingdown
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The heat sum after subtraction of its cutoff logarithmic main terms. -/
def narainAverageRemainder (Y Z : Height) (a b : ℂ) (y : ℝ) : ℂ :=
  narainScalarHeatAverage Y Z y - scalarMellinMainTerm a b y

theorem locallyIntegrableOn_narainAverageRemainder
    (Y Z : Height) (a b : ℂ) :
    LocallyIntegrableOn (narainAverageRemainder Y Z a b) (Ioi 0) :=
  (locallyIntegrableOn_narainScalarHeatAverage Y Z).sub
    (locallyIntegrableOn_scalarMellinMainTerm a b)

theorem exists_isBigO_narainAverageRemainder_exp
    (Y Z : Height) (a b : ℂ) :
    ∃ c : ℝ, 0 < c ∧ narainAverageRemainder Y Z a b =O[atTop]
      (fun y : ℝ => Real.exp (-c * y)) := by
  obtain ⟨c, hc, h⟩ := exists_isBigO_narainScalarHeatAverage_exp Y Z
  obtain ⟨B, hB⟩ := h.bound
  refine ⟨c, hc, IsBigO.of_bound B ?_⟩
  filter_upwards [hB, eventually_gt_atTop (1 : ℝ)] with y hBy hy
  simpa [narainAverageRemainder, scalarMellinMainTerm, not_le.mpr hy] using hBy

/-- Dividing a normalized power remainder by height gives its Mellin growth bound. -/
theorem isBigO_narainAverageRemainder_bot
    (Y Z : Height) {a b : ℂ} {α : ℝ}
    (hrate : (fun y : ℝ => (y : ℂ) * narainScalarHeatAverage Y Z y -
      (a * (Real.log y : ℂ) + b)) =O[𝓝[>] 0] (fun y : ℝ => y ^ α)) :
    narainAverageRemainder Y Z a b =O[𝓝[>] 0]
      (fun y : ℝ => y ^ (-(1 - α))) := by
  obtain ⟨C, hC⟩ := hrate.bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC, Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with y hCy hy
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hy.1.le _)] at hCy
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.1.ne'
  have heq : narainAverageRemainder Y Z a b y =
      ((y : ℂ) * narainScalarHeatAverage Y Z y - (a * (Real.log y : ℂ) + b)) / (y : ℂ) := by
    rw [narainAverageRemainder, scalarMellinMainTerm,
      indicator_of_mem (show y ∈ Ioc (0 : ℝ) 1 from ⟨hy.1, hy.2.le⟩)]
    field_simp [hy0]
  rw [heq, norm_div, Complex.norm_real, Real.norm_of_nonneg hy.1.le,
    Real.norm_of_nonneg (Real.rpow_nonneg hy.1.le _)]
  calc
    _ ≤ (C * y ^ α) / y := div_le_div_of_nonneg_right hCy hy.1.le
    _ = C * y ^ (-(1 - α)) := by
      rw [neg_sub, Real.rpow_sub hy.1, Real.rpow_one]
      ring

/-- A power remainder extends the cleared Mellin identity across its half-plane. -/
theorem narainAverageRemainder_mellin_cleared
    (Y Z : Height) {α : ℝ} {a b : ℂ}
    (hα0 : 0 < α)
    (hrate : (fun y : ℝ => (y : ℂ) * narainScalarHeatAverage Y Z y -
      (a * (Real.log y : ℂ) + b)) =O[𝓝[>] 0] (fun y : ℝ => y ^ α))
    {u : ℂ} (hu : 1 / 2 - α < u.re) :
    (u * (1 + 2 * u)) * xi (1 + 2 * u) *
      ((u - 1 / 2) ^ 2 * mellin (narainAverageRemainder Y Z a b) (1 / 2 + u) -
        a + b * (u - 1 / 2)) =
      filledNumeratorMean Y u * filledNumeratorMean Z u / 2 := by
  let g := narainAverageRemainder Y Z a b
  have hloc := locallyIntegrableOn_narainAverageRemainder Y Z a b
  obtain ⟨c, hc, htop⟩ := exists_isBigO_narainAverageRemainder_exp Y Z a b
  have hbot := isBigO_narainAverageRemainder_bot Y Z hrate
  have hdiff (s : ℂ) (hs : 1 - α < s.re) : DifferentiableAt ℂ (mellin g) s :=
    mellin_differentiableAt_of_isBigO_rpow_exp hc hloc htop hbot hs
  have hconv (s : ℂ) (hs : 1 - α < s.re) : MellinConvergent g s :=
    mellinConvergent_of_isBigO_rpow_exp hc hloc htop hbot hs
  have hsplit (s : ℂ) (hs : 1 < s.re) :
      mellin (narainScalarHeatAverage Y Z) s =
        mellin g s + (-a / (s - 1) ^ 2 + b / (s - 1)) := by
    have hmain := hasMellin_scalarMellinMainTerm a b hs
    have hadd := hasMellin_add (hconv s (by linarith only [hs, hα0])) hmain.1
    have heq : (fun y => g y + scalarMellinMainTerm a b y) = narainScalarHeatAverage Y Z := by
      funext y
      simp only [g, narainAverageRemainder, sub_add_cancel]
    simpa only [heq, hmain.2] using hadd.2
  let L := fun u : ℂ => (u * (1 + 2 * u)) * xi (1 + 2 * u) *
    ((u - 1 / 2) ^ 2 * mellin g (1 / 2 + u) - a + b * (u - 1 / 2))
  let R := fun u : ℂ => filledNumeratorMean Y u * filledNumeratorMean Z u / 2
  have heq (u : ℂ) (hu : 1 / 2 < u.re) : L u = R u := by
    have hs : 1 < (1 / 2 + u).re := by simp; linarith only [hu]
    have hw : u - 1 / 2 ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      linarith only [hu, hr]
    have h := narainMellinMean_cleared Y Z hu
    have hsource := mellin_narainScalarHeatAverage Y Z hs
    rw [show (1 / 2 + u) - 1 / 2 = u by ring] at hsource
    rw [← hsource] at h
    rw [hsplit (1 / 2 + u) hs, show (1 / 2 + u) - 1 = u - 1 / 2 by ring] at h
    have halg : (u - 1 / 2) ^ 2 *
        (mellin g (1 / 2 + u) + (-a / (u - 1 / 2) ^ 2 + b / (u - 1 / 2))) =
      (u - 1 / 2) ^ 2 * mellin g (1 / 2 + u) - a + b * (u - 1 / 2) := by
      generalize u - 1 / 2 = w at hw ⊢
      field_simp [hw]
      ring
    simpa only [halg] using h
  let U : Set ℂ := {u | 1 / 2 - α < u.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2 - α)).isPreconnected
  have hL : AnalyticOnNhd ℂ L U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro u hu
    have hshift : DifferentiableAt ℂ (fun u : ℂ => 1 / 2 + u) u := by fun_prop
    have hm := (hdiff (1 / 2 + u) (by
      change 1 / 2 - α < u.re at hu
      simp
      linarith only [hu])).comp u hshift
    have hw : DifferentiableAt ℂ (fun u : ℂ => u - 1 / 2) u := by fun_prop
    have hp : DifferentiableAt ℂ (fun u : ℂ => u * (1 + 2 * u)) u := by fun_prop
    exact ((hp.mul (differentiable_xi_shift u)).mul
      ((((hw.pow 2).mul hm).sub_const a).add (hw.const_mul b))).differentiableWithinAt
  have hR : AnalyticOnNhd ℂ R U := by
    have hd := ((differentiable_filledNumeratorMean Y).mul
      (differentiable_filledNumeratorMean Z)).div_const 2
    exact fun u _ => hd.analyticAt u
  have hbase : (1 : ℂ) ∈ U := by change 1 / 2 - α < (1 : ℂ).re; norm_num; linarith
  have hev : L =ᶠ[𝓝 (1 : ℂ)] R := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show 1 / 2 < (1 : ℂ).re by norm_num)] with u hu using heq u hu
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR hUc hbase hev hu

/-- Any positive power remainder fixes the logarithmic coefficient uniquely. -/
theorem narainAverageRate_log_coefficient
    (Y Z : Height) {α : ℝ} {a b : ℂ} (hα : 0 < α)
    (hrate : (fun y : ℝ => (y : ℂ) * narainScalarHeatAverage Y Z y -
      (a * (Real.log y : ℂ) + b)) =O[𝓝[>] 0] (fun y : ℝ => y ^ α)) :
    a = -(3 / (Real.pi : ℂ)) := by
  have h := narainAverageRemainder_mellin_cleared Y Z hα hrate
    (u := 1 / 2) (by simp; linarith only [hα])
  norm_num [filledNumeratorMean_half] at h
  have hv : a = -(xi 1 / xi 2) := by
    rw [xi_one, ← neg_div]
    apply (eq_div_iff xi_two_ne_zero).mpr
    linear_combination -h
  simpa only [xi_one_div_xi_two] using hv

/-- A claimed rate across a resonance would cancel the filled numerator there. -/
private theorem filled_mean_product_eq_zero_of_narain_rate
    (p : Resonance) (Y Z : Height) {α : ℝ} {a b : ℂ}
    (hα : 1 / 2 - p.val.re < α)
    (hrate : (fun y : ℝ => (y : ℂ) * narainScalarHeatAverage Y Z y -
      (a * (Real.log y : ℂ) + b)) =O[𝓝[>] 0] (fun y : ℝ => y ^ α)) :
    filledNumeratorMean Y p.val * filledNumeratorMean Z p.val = 0 := by
  have hα0 : 0 < α := by linarith only [hα, re_neg_of_xi_shift_eq_zero p.property]
  have h := narainAverageRemainder_mellin_cleared Y Z hα0 hrate
    (u := p.val) (by linarith only [hα])
  change (p.val * (1 + 2 * p.val)) * xi (1 + 2 * p.val) * _ = _ at h
  rw [p.property, mul_zero, zero_mul] at h
  exact (div_eq_zero_iff).mp h.symm |>.resolve_right two_ne_zero

/-- One fixed averaged source detects every arithmetic obstruction to faster decay. -/
theorem narainScalarHeatAverage_no_faster_decay (p : Resonance) (Y Z : Height)
    {α : ℝ} (hα : 1 / 2 - p.val.re < α) :
    ¬ ∃ a b : ℂ,
      (fun y : ℝ => (y : ℂ) * narainScalarHeatAverage Y Z y -
        (a * (Real.log y : ℂ) + b)) =O[𝓝[>] 0] (fun y : ℝ => y ^ α) := by
  rintro ⟨a, b, hrate⟩
  exact (mul_ne_zero (filledNumeratorMean_ne_zero p Y) (filledNumeratorMean_ne_zero p Z))
    (filled_mean_product_eq_zero_of_narain_rate p Y Z hα hrate)

/-- Rates for one fixed average exclude every xi zero to the right of the corresponding line. -/
theorem xi_ne_zero_of_narainAverageRate (Y Z : Height) {σ₀ : ℝ}
    (hrate : ∀ ε : ℝ, 0 < ε → ∃ a b : ℂ,
      (fun y : ℝ => (y : ℂ) * narainScalarHeatAverage Y Z y -
        (a * (Real.log y : ℂ) + b)) =O[𝓝[>] 0]
          (fun y : ℝ => y ^ (1 - σ₀ / 2 - ε)))
    {s : ℂ} (hs : σ₀ < s.re) : xi s ≠ 0 := by
  intro hz
  let p : Resonance := ⟨(s - 1) / 2, by
    rw [show 1 + 2 * ((s - 1) / 2) = s by ring]
    exact hz⟩
  have hp : p.val.re = (s.re - 1) / 2 := by simp [p]
  let ε : ℝ := (s.re - σ₀) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith only [hs]
  obtain ⟨a, b, h⟩ := hrate ε hε
  exact narainScalarHeatAverage_no_faster_decay p Y Z
    (α := 1 - σ₀ / 2 - ε) (by rw [hp]; dsimp [ε]; linarith only [hs]) ⟨a, b, h⟩

/-- The three-quarter rate of one fixed averaged Narain source implies RH. -/
theorem riemannHypothesis_of_narainAverageRate (Y Z : Height)
    (hrate : ∀ ε : ℝ, 0 < ε → ∃ a b : ℂ,
      (fun y : ℝ => (y : ℂ) * narainScalarHeatAverage Y Z y -
        (a * (Real.log y : ℂ) + b)) =O[𝓝[>] 0]
          (fun y : ℝ => y ^ (3 / 4 - ε))) : RiemannHypothesis := by
  apply rh_iff_xi_ne_zero_right.mpr
  intro s hs
  apply xi_ne_zero_of_narainAverageRate Y Z (σ₀ := 1 / 2) _ hs
  simpa only [show (1 : ℝ) - (1 / 2) / 2 = 3 / 4 by norm_num] using hrate

#print axioms narainScalarHeatAverage_no_faster_decay
#print axioms narainAverageRate_log_coefficient
#print axioms xi_ne_zero_of_narainAverageRate
#print axioms riemannHypothesis_of_narainAverageRate
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
