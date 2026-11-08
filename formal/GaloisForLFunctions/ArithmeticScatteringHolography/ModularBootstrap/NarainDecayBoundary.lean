import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainHeatRegularity
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPoleClearing
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.ScalarMellinMainTerms

/-!
# Arithmetic poles obstruct faster scalar decay

A power remainder makes its Mellin transform holomorphic on a half-plane.
After clearing the universal main pole, analytic uniqueness forces the
Eisenstein numerator to vanish at every arithmetic pole in that half-plane.
Horocycle detection supplies targets where this is impossible.
-/

open Complex RHTower MeasureTheory Set Filter Topology Asymptotics
open GaloisForLFunctions.BlackHoleRingdown

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The heat sum after subtraction of its cutoff logarithmic main terms. -/
def narainScalarRemainder (ρ σ : D4BMUpperHalfPlaneCoordinate) (a b : ℂ) (y : ℝ) : ℂ :=
  narainScalarHeat ρ σ y - scalarMellinMainTerm a b y

theorem locallyIntegrableOn_narainScalarRemainder
    (ρ σ : D4BMUpperHalfPlaneCoordinate) (a b : ℂ) :
    LocallyIntegrableOn (narainScalarRemainder ρ σ a b) (Ioi 0) :=
  (locallyIntegrableOn_narainScalarHeat ρ σ).sub
    (locallyIntegrableOn_scalarMellinMainTerm a b)

theorem exists_isBigO_narainScalarRemainder_exp
    (ρ σ : D4BMUpperHalfPlaneCoordinate) (a b : ℂ) :
    ∃ c : ℝ, 0 < c ∧ narainScalarRemainder ρ σ a b =O[atTop]
      (fun y : ℝ => Real.exp (-c * y)) := by
  obtain ⟨B, c, _, hc, h⟩ := narainScalarHeat_exp_tail ρ σ
  refine ⟨c, hc, IsBigO.of_bound B ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
  simpa [narainScalarRemainder, scalarMellinMainTerm, not_le.mpr hy,
    Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul] using h y hy.le

private theorem isBigO_narainScalarRemainder_bot
    (ρ σ : D4BMUpperHalfPlaneCoordinate) {a b : ℂ} {α : ℝ}
    (hrate : (fun y : ℝ => (y : ℂ) * narainScalarHeat ρ σ y -
      (a * (Real.log y : ℂ) + b)) =O[𝓝[>] 0] (fun y : ℝ => y ^ α)) :
    narainScalarRemainder ρ σ a b =O[𝓝[>] 0]
      (fun y : ℝ => y ^ (-(1 - α))) := by
  obtain ⟨C, hC⟩ := hrate.bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC, Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with y hCy hy
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hy.1.le _)] at hCy
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.1.ne'
  have heq : narainScalarRemainder ρ σ a b y =
      ((y : ℂ) * narainScalarHeat ρ σ y - (a * (Real.log y : ℂ) + b)) / (y : ℂ) := by
    rw [narainScalarRemainder, scalarMellinMainTerm,
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
private theorem narainScalarRemainder_mellin_cleared
    (ρ σ : D4BMUpperHalfPlaneCoordinate) {α : ℝ} {a b : ℂ}
    (hα0 : 0 < α)
    (hrate : (fun y : ℝ => (y : ℂ) * narainScalarHeat ρ σ y -
      (a * (Real.log y : ℂ) + b)) =O[𝓝[>] 0] (fun y : ℝ => y ^ α))
    {u : ℂ} (hu : 1 / 2 - α < u.re) :
    (u * (1 + 2 * u)) * xi (1 + 2 * u) *
      ((u - 1 / 2) ^ 2 * mellin (narainScalarRemainder ρ σ a b) (1 / 2 + u) -
        a + b * (u - 1 / 2)) =
      filledEisensteinNumerator ρ u * filledEisensteinNumerator σ u / 2 := by
  let g := narainScalarRemainder ρ σ a b
  have hloc := locallyIntegrableOn_narainScalarRemainder ρ σ a b
  obtain ⟨c, hc, htop⟩ := exists_isBigO_narainScalarRemainder_exp ρ σ a b
  have hbot := isBigO_narainScalarRemainder_bot ρ σ hrate
  have hdiff (s : ℂ) (hs : 1 - α < s.re) : DifferentiableAt ℂ (mellin g) s :=
    mellin_differentiableAt_of_isBigO_rpow_exp hc hloc htop hbot hs
  have hconv (s : ℂ) (hs : 1 - α < s.re) : MellinConvergent g s :=
    mellinConvergent_of_isBigO_rpow_exp hc hloc htop hbot hs
  have hsplit (s : ℂ) (hs : 1 < s.re) :
      mellin (narainScalarHeat ρ σ) s =
        mellin g s + (-a / (s - 1) ^ 2 + b / (s - 1)) := by
    have hmain := hasMellin_scalarMellinMainTerm a b hs
    have hadd := hasMellin_add (hconv s (by linarith only [hs, hα0])) hmain.1
    have heq : (fun y => g y + scalarMellinMainTerm a b y) = narainScalarHeat ρ σ := by
      funext y
      simp only [g, narainScalarRemainder, sub_add_cancel]
    simpa only [heq, hmain.2] using hadd.2
  let L := fun u : ℂ => (u * (1 + 2 * u)) * xi (1 + 2 * u) *
    ((u - 1 / 2) ^ 2 * mellin g (1 / 2 + u) - a + b * (u - 1 / 2))
  let R := fun u : ℂ => filledEisensteinNumerator ρ u * filledEisensteinNumerator σ u / 2
  have heq (u : ℂ) (hu : 1 / 2 < u.re) : L u = R u := by
    have hs : 1 < (1 / 2 + u).re := by simp; linarith only [hu]
    have hw : u - 1 / 2 ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      linarith only [hu, hr]
    have h := narainScalarHeat_mellin_cleared ρ σ hu
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
    have hd := ((differentiable_filledEisensteinNumerator ρ).mul
      (differentiable_filledEisensteinNumerator σ)).div_const 2
    exact fun u _ => hd.analyticAt u
  have hbase : (1 : ℂ) ∈ U := by change 1 / 2 - α < (1 : ℂ).re; norm_num; linarith
  have hev : L =ᶠ[𝓝 (1 : ℂ)] R := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show 1 / 2 < (1 : ℂ).re by norm_num)] with u hu using heq u hu
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR hUc hbase hev hu

/-- Any positive power remainder fixes the logarithmic coefficient uniquely. -/
theorem narainScalarRate_log_coefficient
    (ρ σ : D4BMUpperHalfPlaneCoordinate) {α : ℝ} {a b : ℂ} (hα : 0 < α)
    (hrate : (fun y : ℝ => (y : ℂ) * narainScalarHeat ρ σ y -
      (a * (Real.log y : ℂ) + b)) =O[𝓝[>] 0] (fun y : ℝ => y ^ α)) :
    a = -(3 / (Real.pi : ℂ)) := by
  have h := narainScalarRemainder_mellin_cleared ρ σ hα hrate
    (u := 1 / 2) (by simp; linarith only [hα])
  norm_num [filledEisensteinNumerator_half] at h
  have hv : a = -(xi 1 / xi 2) := by
    rw [xi_one, ← neg_div]
    apply (eq_div_iff xi_two_ne_zero).mpr
    linear_combination -h
  simpa only [xi_one_div_xi_two] using hv

/-- A claimed rate across a resonance would cancel the filled numerator there. -/
private theorem filled_product_eq_zero_of_narain_rate
    (p : Resonance) (ρ σ : D4BMUpperHalfPlaneCoordinate) {α : ℝ} {a b : ℂ}
    (hα : 1 / 2 - p.val.re < α)
    (hrate : (fun y : ℝ => (y : ℂ) * narainScalarHeat ρ σ y -
      (a * (Real.log y : ℂ) + b)) =O[𝓝[>] 0] (fun y : ℝ => y ^ α)) :
    filledEisensteinNumerator ρ p.val * filledEisensteinNumerator σ p.val = 0 := by
  have hα0 : 0 < α := by linarith only [hα, re_neg_of_xi_shift_eq_zero p.property]
  have h := narainScalarRemainder_mellin_cleared ρ σ hα0 hrate
    (u := p.val) (by linarith only [hα])
  change (p.val * (1 + 2 * p.val)) * xi (1 + 2 * p.val) * _ = _ at h
  rw [p.property, mul_zero, zero_mul] at h
  exact (div_eq_zero_iff).mp h.symm |>.resolve_right two_ne_zero

/-- Every arithmetic zero forbids faster scalar decay for some targets on any two horocycles. -/
theorem exists_narainScalarHeat_no_faster_decay (p : Resonance) (Y Z : Height) :
    ∃ x ∈ Ioc (0 : ℝ) 1, ∃ w ∈ Ioc (0 : ℝ) 1,
      ∀ α : ℝ, 1 / 2 - p.val.re < α →
        ¬ ∃ a b : ℂ,
          (fun y : ℝ => (y : ℂ) *
            narainScalarHeat ⟨x, Y.val, Y.property⟩ ⟨w, Z.val, Z.property⟩ y -
              (a * (Real.log y : ℂ) + b)) =O[𝓝[>] 0] (fun y : ℝ => y ^ α) := by
  obtain ⟨x, hx, hNx⟩ := exists_eisensteinNumerator_ne_zero p.property Y.property
  obtain ⟨w, hw, hNw⟩ := exists_eisensteinNumerator_ne_zero p.property Z.property
  refine ⟨x, hx, w, hw, ?_⟩
  intro α hα hrate
  obtain ⟨a, b, hrate⟩ := hrate
  have h := filled_product_eq_zero_of_narain_rate p
    ⟨x, Y.val, Y.property⟩ ⟨w, Z.val, Z.property⟩ hα hrate
  have hd : 2 * p.val - 1 ≠ 0 := by
    intro heq
    have hr := congrArg Complex.re heq
    simp at hr
    linarith only [hr, re_neg_of_xi_shift_eq_zero p.property]
  rw [filledEisensteinNumerator_eq _ hd, filledEisensteinNumerator_eq _ hd] at h
  exact (mul_ne_zero (mul_ne_zero hd hNx) (mul_ne_zero hd hNw)) h

#print axioms exists_narainScalarHeat_no_faster_decay
#print axioms narainScalarRate_log_coefficient

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
