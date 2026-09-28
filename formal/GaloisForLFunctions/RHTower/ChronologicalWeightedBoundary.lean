import GaloisForLFunctions.RHTower.ChronologicalWeightedMellin
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Critical Mellin boundary obstruction for weighted Möbius sources

For bounded measurable weights supported below one, a nonzero Mellin moment
at a critical zeta zero prevents the actual source `sum mu(n) * w(n*t)` from
being little-o of `t^(-1/2)`. A positive normalized source height therefore
recurs arbitrarily close to zero. No simplicity assumption on the zero enters.

The proof establishes a critical Abel boundary limit for locally integrable
sources, including sources with jumps. Analytic continuation uses the actual
weighted Mellin identity and the entire residue unit `(s-1) zeta(s)`.

This is a component of the fixed-tail geometric obstruction. It neither
proves that geometric capstone nor constructs a vanishing heat repair.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RHTower

private theorem supported_isBigO_exp {f : ℝ → ℂ}
    (htop : ∀ t, 1 < t → f t = 0) :
    f =O[atTop] (fun t : ℝ => Real.exp (-1*t)) := by
  have hz : f =ᶠ[atTop] (fun _ => (0 : ℂ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact htop t ht
  exact hz.isBigO.trans (Asymptotics.isBigO_zero _ _)

private theorem integral_Ioc_rpow_shift {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ t : ℝ in Ioc 0 a, t ^ (r-1)) = a^r / r := by
  rw [← intervalIntegral.integral_of_le ha.le, integral_rpow (Or.inl (by linarith))]
  simp [sub_add_cancel, Real.zero_rpow hr.ne']

/-- A compactly supported source bounded by `M t^(-1/2)` near zero has Abel-normalized Mellin boundary values of size at most `M` on the critical line, up to any positive margin. Measurable jumps are allowed. -/
theorem chronological_mellin_abel_bound {f : ℝ → ℂ} {D M : ℝ}
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hlocal : LocallyIntegrableOn f (Ioi 0))
    (hbound : ∀ t, 0 < t → ‖f t‖ ≤ D/t)
    (htop : ∀ t, 1 < t → f t = 0)
    (hnear : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖f t‖ ≤ M * t ^ (-(1/2 : ℝ)))
    {rho : ℂ} (hrho : rho.re = 1/2) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ‖(r : ℂ) * mellin f (rho + (r : ℂ))‖ ≤ M + η := by
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, t ∈ Ioi (0 : ℝ) → ‖f t‖ ≤ M * t ^ (-(1/2 : ℝ)) :=
    eventually_nhdsWithin_iff.mp hnear
  obtain ⟨a₀, ha₀, hnear'⟩ := Metric.eventually_nhds_iff.mp hevent
  let a := min (a₀/2) 1
  have ha : 0 < a := lt_min (by positivity) one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  have ha₀' : a < a₀ := (min_le_left _ _).trans_lt (by linarith)
  have hfsmall : ∀ t ∈ Ioc (0 : ℝ) a, ‖f t‖ ≤ M * t^(-(1/2 : ℝ)) := by
    intro t ht
    have hdist : dist t 0 < a₀ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      exact ht.2.trans_lt ha₀'
    exact hnear' hdist ht.1
  have hbig : f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(1/2 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound M ?_
    filter_upwards [hnear, self_mem_nhdsWithin] with t ht htpos
    rwa [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
  let B := D / a^2
  have hB : 0 ≤ B := by positivity
  let δ := η / (B+1)
  have hδ : 0 < δ := by positivity
  have hδmem : ∀ᶠ r : ℝ in 𝓝[>] 0, r < δ := nhdsWithin_le_nhds (Iio_mem_nhds hδ)
  filter_upwards [self_mem_nhdsWithin, hδmem] with r hrmem hrδ
  have hr : 0 < r := hrmem
  let F : ℝ → ℂ := fun t => (t : ℂ)^(rho+(r:ℂ)-1) * f t
  have hre : (rho+(r:ℂ)-1).re = r-1/2 := by simp [hrho]; ring
  have hconv : IntegrableOn F (Ioi 0) := by
    have hs : (1/2 : ℝ) < (rho+(r:ℂ)).re := by simp [hrho, hr]
    simpa [MellinConvergent, F, smul_eq_mul] using
      mellinConvergent_of_isBigO_rpow_exp one_pos hlocal
        (supported_isBigO_exp htop) hbig hs
  have hlo : IntegrableOn F (Ioc 0 a) := hconv.mono_set (fun _ ht => ht.1)
  have hhi : IntegrableOn F (Ioc a 1) := hconv.mono_set (fun _ ht => ha.trans ht.1)
  have hone : IntegrableOn F (Ioc 0 1) := hconv.mono_set (fun _ ht => ht.1)
  have htail : IntegrableOn F (Ioi 1) := hconv.mono_set (Ioi_subset_Ioi zero_le_one)
  have hsplit : mellin f (rho+(r:ℂ)) =
      (∫ t : ℝ in Ioc 0 a, F t) + ∫ t : ℝ in Ioc a 1, F t := by
    change (∫ t : ℝ in Ioi 0, F t) = _
    rw [← Ioc_union_Ioi_eq_Ioi (show (0:ℝ) ≤ 1 from zero_le_one),
      setIntegral_union (by
        rw [disjoint_left]
        exact fun t ht ht' => (not_lt_of_ge ht.2) ht') measurableSet_Ioi hone htail]
    have hz : (∫ t : ℝ in Ioi 1, F t) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      simp [F, htop t ht]
    rw [hz, add_zero, ← Ioc_union_Ioc_eq_Ioc ha.le ha1]
    exact setIntegral_union (by
      rw [disjoint_left]
      exact fun t ht ht' => (not_lt_of_ge ht.2) ht'.1) measurableSet_Ioc hlo hhi
  have hnorm (t : ℝ) (ht : 0 < t) : ‖F t‖ = t^(r-1/2)*‖f t‖ := by
    dsimp only [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, hre]
  have hrpow : IntegrableOn (fun t : ℝ => t^(r-1)) (Ioc 0 a) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff ha).mpr (by linarith)
  have hlow : ‖∫ t : ℝ in Ioc 0 a, F t‖ ≤ M/r := by
    calc
      _ ≤ ∫ t : ℝ in Ioc 0 a, ‖F t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ in Ioc 0 a, M*t^(r-1) := by
        apply integral_mono_ae hlo.norm (hrpow.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        rw [hnorm t ht.1]
        calc
          _ ≤ t^(r-1/2)*(M*t^(-(1/2:ℝ))) :=
            mul_le_mul_of_nonneg_left (hfsmall t ht) (Real.rpow_nonneg ht.1.le _)
          _ = M*t^(r-1) := by
            rw [mul_left_comm, ← Real.rpow_add ht.1]
            congr 2
            ring
      _ = M*(a^r/r) := by rw [integral_const_mul, integral_Ioc_rpow_shift ha hr]
      _ ≤ M/r := by
        have hap := Real.rpow_le_one ha.le ha1 hr.le
        exact (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hap hr.le) hM).trans_eq (by ring)
  have hhigh : ‖∫ t : ℝ in Ioc a 1, F t‖ ≤ B := by
    calc
      _ ≤ ∫ t : ℝ in Ioc a 1, ‖F t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ _t : ℝ in Ioc a 1, B := by
        apply integral_mono_ae hhi.norm (integrableOn_const (hs := measure_Ioc_lt_top.ne))
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 := ha.trans ht.1
        rw [hnorm t ht0]
        have hp : t^(r-1/2) ≤ 1/a := by
          calc
            _ ≤ t^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_ge ht0 ht.2 (by linarith)
            _ = 1/t := by rw [Real.rpow_neg_one, one_div]
            _ ≤ 1/a := one_div_le_one_div_of_le ha ht.1.le
        have hf : ‖f t‖ ≤ D/a :=
          (hbound t ht0).trans (div_le_div_of_nonneg_left hD ha ht.1.le)
        exact (mul_le_mul hp hf (norm_nonneg _) (by positivity)).trans_eq (by dsimp [B]; ring)
      _ = B*(1-a) := by simp [ha1]; ring
      _ ≤ B := by nlinarith
  rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hδB : δ * B ≤ η := by
    dsimp only [δ]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  calc
    _ ≤ r * (‖∫ t : ℝ in Ioc 0 a, F t‖ + ‖∫ t : ℝ in Ioc a 1, F t‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hr.le
    _ ≤ r*(M/r+B) :=
      mul_le_mul_of_nonneg_left (add_le_add hlow hhigh) hr.le
    _ = M + r*B := by field_simp
    _ ≤ M + η := by nlinarith [mul_le_mul_of_nonneg_right hrδ.le hB]

/-- A compactly supported source that is little-o of the critical half-power has zero Abel-normalized Mellin boundary value. Measurable jumps are allowed. -/
theorem chronological_mellin_abel_boundary {f : ℝ → ℂ} {D : ℝ}
    (hD : 0 ≤ D) (hlocal : LocallyIntegrableOn f (Ioi 0))
    (hbound : ∀ t, 0 < t → ‖f t‖ ≤ D/t)
    (htop : ∀ t, 1 < t → f t = 0)
    (hsmall : f =o[𝓝[>] 0] (fun t : ℝ => t ^ (-(1/2 : ℝ))))
    {rho : ℂ} (hrho : rho.re = 1/2) :
    Tendsto (fun r : ℝ => (r : ℂ) * mellin f (rho + (r : ℂ)))
      (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hnear : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖f t‖ ≤ (ε/2) * t ^ (-(1/2 : ℝ)) := by
    filter_upwards [hsmall.bound (half_pos hε), self_mem_nhdsWithin] with t ht htpos
    rwa [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos htpos _)] at ht
  filter_upwards [chronological_mellin_abel_bound hD (half_pos hε).le hlocal hbound htop hnear
    hrho (by positivity : (0 : ℝ) < ε/4)] with r hr
  rw [dist_zero_right]
  linarith

private theorem bounded_weight_local {w : ℝ → ℂ} {C : ℝ}
    (hm : Measurable w) (hw : ∀ x, 0 < x → ‖w x‖ ≤ C) :
    LocallyIntegrableOn w (Ioi 0) := by
  intro x hx
  have hx0 : 0 < x := hx
  refine ⟨Ioo (x/2) (x+1), mem_nhdsWithin_of_mem_nhds
    (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
  apply IntegrableOn.of_bound measure_Ioo_lt_top hm.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hw t (by linarith [ht.1])

private theorem bounded_weight_isBigO {w : ℝ → ℂ} {C : ℝ}
    (hw : ∀ x, 0 < x → ‖w x‖ ≤ C) :
    w =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  simpa using hw t ht

private theorem bounded_weight_mellin_diff {w : ℝ → ℂ} {C : ℝ}
    (hm : Measurable w) (hw : ∀ x, 0 < x → ‖w x‖ ≤ C)
    (htop : ∀ x, 1 < x → w x = 0) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin w) s :=
  mellin_differentiableAt_of_isBigO_rpow_exp one_pos
    (bounded_weight_local hm hw) (supported_isBigO_exp htop)
    (bounded_weight_isBigO hw) hs

/-- If the actual compactly weighted source is big-O of the critical half-power, its classical Mellin identity continues across the half-plane `Re s > 1/2`, with the Euler pole removed. -/
theorem chronologicalMobiusWeightedSource_mellin_product {w : ℝ → ℂ} {C : ℝ}
    (hm : Measurable w) (hC : 0 ≤ C) (hw : ∀ x, 0 < x → ‖w x‖ ≤ C)
    (htop : ∀ x, 1 < x → w x = 0)
    (hsmall : chronologicalMobiusWeightedSource w =O[𝓝[>] 0]
      (fun t : ℝ => t ^ (-(1/2 : ℝ)))) :
    ∀ s : ℂ, 1/2 < s.re →
      mellin (chronologicalMobiusWeightedSource w) s * zetaResidueUnit s =
        mellin w s * (s-1) := by
  let U : Set ℂ := {s | 1/2 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hloc := chronologicalMobiusWeightedSource_locallyIntegrable hm hC hw htop
  have hzero : ∀ t : ℝ, 1 < t → chronologicalMobiusWeightedSource w t = 0 :=
    fun t ht => chronologicalMobiusWeightedSource_eq_zero zero_le_one htop ht
  have hG : AnalyticOnNhd ℂ (mellin (chronologicalMobiusWeightedSource w)) U := by
    apply DifferentiableOn.analyticOnNhd ?_ hU
    intro s hs
    exact (mellin_differentiableAt_of_isBigO_rpow_exp one_pos hloc
      (supported_isBigO_exp hzero) hsmall hs).differentiableWithinAt
  have hleft : AnalyticOnNhd ℂ
      (fun s => mellin (chronologicalMobiusWeightedSource w) s * zetaResidueUnit s) U :=
    fun s hs => (hG s hs).mul (analyticAt_zetaResidueUnit s)
  have hW : AnalyticOnNhd ℂ (mellin w) {s : ℂ | 0 < s.re} := by
    apply DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
    intro s hs
    exact (bounded_weight_mellin_diff hm hw htop hs).differentiableWithinAt
  have hright : AnalyticOnNhd ℂ (fun s => mellin w s * (s-1)) U := by
    intro s hs
    have hs0 : 0 < s.re := by change 1/2 < s.re at hs; linarith
    exact (hW s hs0).mul (analyticAt_id.sub analyticAt_const)
  have hevent : (fun s => mellin (chronologicalMobiusWeightedSource w) s * zetaResidueUnit s)
      =ᶠ[𝓝 (2 : ℂ)] (fun s => mellin w s * (s-1)) := by
    have hgt : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by change (1 : ℝ) < 2; linarith)
    filter_upwards [hgt] with s hs
    have hs1 : s ≠ 1 := by
      intro heq
      subst s
      simp only [Complex.one_re] at hs
      linarith
    have hconv : MellinConvergent w s :=
      mellinConvergent_of_isBigO_rpow_exp one_pos (bounded_weight_local hm hw)
        (supported_isBigO_exp htop) (bounded_weight_isBigO hw) (by linarith)
    rw [chronologicalMobiusWeightedSource_mellin w hs hconv]
    simp only [zetaResidueUnit, Function.update_of_ne hs1]
    have hz := riemannZeta_ne_zero_of_one_lt_re hs
    field_simp
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright
    (convex_halfSpace_re_gt (1/2)).isPreconnected
    (by change (1/2 : ℝ) < 2; linarith) hevent

/-- At every critical zeta zero, a compactly weighted source with vanishing critical scale must have zero weight Mellin moment. This is a restriction on the actual weight, with no simplicity assumption on the zero. -/
theorem chronologicalMobiusWeightedSource_mellin_zero_of_littleO
    {w : ℝ → ℂ} {C : ℝ}
    (hm : Measurable w) (hC : 0 ≤ C) (hw : ∀ x, 0 < x → ‖w x‖ ≤ C)
    (htop : ∀ x, 1 < x → w x = 0)
    (hsmall : chronologicalMobiusWeightedSource w =o[𝓝[>] 0]
      (fun t : ℝ => t ^ (-(1/2 : ℝ))))
    {rho : ℂ} (hrho : rho.re = 1/2) (hzero : riemannZeta rho = 0) :
    mellin w rho = 0 := by
  have hrho1 : rho ≠ 1 := by
    intro heq
    subst rho
    simp only [Complex.one_re] at hrho
    linarith
  have hunit0 : zetaResidueUnit rho = 0 := by simp [zetaResidueUnit, hrho1, hzero]
  have htopS : ∀ t : ℝ, 1 < t → chronologicalMobiusWeightedSource w t = 0 :=
    fun t ht => chronologicalMobiusWeightedSource_eq_zero zero_le_one htop ht
  have habel := chronological_mellin_abel_boundary (mul_nonneg (by positivity) hC)
    (chronologicalMobiusWeightedSource_locallyIntegrable hm hC hw htop)
    (fun t ht => chronologicalMobiusWeightedSource_norm_bound hC hw htop ht)
    htopS hsmall hrho
  have hreal : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using hr.ne'
  have hslope : Tendsto (fun r : ℝ => (r : ℂ)⁻¹ * zetaResidueUnit (rho+(r:ℂ)))
      (𝓝[>] 0) (𝓝 (deriv zetaResidueUnit rho)) := by
    have hh := (analyticAt_zetaResidueUnit rho).differentiableAt.hasDerivAt.tendsto_slope_zero.comp hreal
    simpa [hunit0, smul_eq_mul] using! hh
  have hprod : Tendsto (fun r : ℝ =>
      mellin (chronologicalMobiusWeightedSource w) (rho+(r:ℂ)) * zetaResidueUnit (rho+(r:ℂ)))
      (𝓝[>] 0) (𝓝 0) := by
    have hh : Tendsto (fun r : ℝ =>
        ((r:ℂ) * mellin (chronologicalMobiusWeightedSource w) (rho+(r:ℂ))) *
          ((r:ℂ)⁻¹ * zetaResidueUnit (rho+(r:ℂ)))) (𝓝[>] 0) (𝓝 0) := by
      simpa using habel.mul hslope
    refine hh.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    field_simp
  have hid := chronologicalMobiusWeightedSource_mellin_product hm hC hw htop hsmall.isBigO
  have hrhs : Tendsto (fun r : ℝ => mellin w (rho+(r:ℂ))*(rho+(r:ℂ)-1))
      (𝓝[>] 0) (𝓝 0) := by
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hid _ (by simpa [hrho] using hr)
  have hray : Tendsto (fun r : ℝ => rho+(r:ℂ)) (𝓝[>] 0) (𝓝 rho) := by
    simpa using! ((continuous_const.add Complex.continuous_ofReal).tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun r : ℝ => mellin w (rho+(r:ℂ))*(rho+(r:ℂ)-1))
      (𝓝[>] 0) (𝓝 (mellin w rho*(rho-1))) :=
    ((bounded_weight_mellin_diff hm hw htop (by rw [hrho]; positivity)).continuousAt.tendsto.comp hray).mul
      (((continuous_id.sub continuous_const).tendsto rho).comp hray)
  have hz : mellin w rho * (rho-1) = 0 := tendsto_nhds_unique hlim hrhs
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hrho1)

/-- A nonzero weight moment at any critical zeta zero obstructs little-o critical decay of its actual weighted Möbius source. -/
theorem chronologicalMobiusWeightedSource_not_littleO
    {w : ℝ → ℂ} {C : ℝ}
    (hm : Measurable w) (hC : 0 ≤ C) (hw : ∀ x, 0 < x → ‖w x‖ ≤ C)
    (htop : ∀ x, 1 < x → w x = 0)
    {rho : ℂ} (hrho : rho.re = 1/2) (hzero : riemannZeta rho = 0)
    (hmoment : mellin w rho ≠ 0) :
    ¬ chronologicalMobiusWeightedSource w =o[𝓝[>] 0]
      (fun t : ℝ => t ^ (-(1/2 : ℝ))) :=
  fun hsmall => hmoment
    (chronologicalMobiusWeightedSource_mellin_zero_of_littleO hm hC hw htop hsmall hrho hzero)

/-- The obstruction has a positive cofinal form: a fixed critical-scale source height recurs arbitrarily close to zero. -/
theorem chronologicalMobiusWeightedSource_cofinal_critical_floor
    {w : ℝ → ℂ} {C : ℝ}
    (hm : Measurable w) (hC : 0 ≤ C) (hw : ∀ x, 0 < x → ‖w x‖ ≤ C)
    (htop : ∀ x, 1 < x → w x = 0)
    {rho : ℂ} (hrho : rho.re = 1/2) (hzero : riemannZeta rho = 0)
    (hmoment : mellin w rho ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → ∃ t : ℝ,
      0 < t ∧ t < δ ∧ ε < t^(1/2 : ℝ)*‖chronologicalMobiusWeightedSource w t‖ := by
  by_contra hfloor
  push Not at hfloor
  apply chronologicalMobiusWeightedSource_not_littleO hm hC hw htop hrho hzero hmoment
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  obtain ⟨δ, hδ, hδbound⟩ := hfloor c hc
  have hneighborhood : ∀ᶠ t : ℝ in 𝓝[>] 0, t < δ :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_id continuous_const).mem_nhds hδ)
  filter_upwards [self_mem_nhdsWithin, hneighborhood] with t ht htδ
  have ht0 : 0 < t := ht
  have hh := hδbound t ht0 htδ
  have hp : 0 < t^(1/2 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hquot : ‖chronologicalMobiusWeightedSource w t‖ ≤ c / t^(1/2 : ℝ) := by
    apply (le_div_iff₀ hp).mpr
    simpa [mul_comm] using hh
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 (-(1/2 : ℝ))),
    Real.rpow_neg ht0.le, ← div_eq_mul_inv]
  exact hquot

/-- The derivative of the entire residue unit `(s-1) ζ(s)` at a zeta zero `ρ ≠ 1` is `(ρ-1) ζ'(ρ)`. -/
theorem deriv_zetaResidueUnit_of_zero {rho : ℂ} (hrho1 : rho ≠ 1) (hzero : riemannZeta rho = 0) :
    deriv zetaResidueUnit rho = (rho - 1) * deriv riemannZeta rho := by
  rw [(zetaResidueUnit_eventuallyEq hrho1).deriv_eq]
  have hd : deriv (fun s : ℂ => (s - 1) * riemannZeta s) rho =
      deriv (fun s : ℂ => s - 1) rho * riemannZeta rho + (rho - 1) * deriv riemannZeta rho :=
    deriv_mul (differentiableAt_id.sub_const 1) (differentiableAt_riemannZeta hrho1)
  rw [hd, hzero, mul_zero, zero_add]

/-- **Quantitative critical boundary.** If the actual compactly weighted source is at most `M t^(-1/2)` near zero, then at every critical zeta zero the weight Mellin moment is at most `M |ζ'(ρ)|`. No simplicity assumption on the zero enters; at a multiple zero the moment must vanish. -/
theorem chronologicalMobiusWeightedSource_norm_mellin_le
    {w : ℝ → ℂ} {C : ℝ}
    (hm : Measurable w) (hC : 0 ≤ C) (hw : ∀ x, 0 < x → ‖w x‖ ≤ C)
    (htop : ∀ x, 1 < x → w x = 0) {M : ℝ} (hM : 0 ≤ M)
    (hnear : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖chronologicalMobiusWeightedSource w t‖ ≤ M * t ^ (-(1/2 : ℝ)))
    {rho : ℂ} (hrho : rho.re = 1/2) (hzero : riemannZeta rho = 0) :
    ‖mellin w rho‖ ≤ M * ‖deriv riemannZeta rho‖ := by
  have hrho1 : rho ≠ 1 := by
    intro heq
    subst rho
    simp only [Complex.one_re] at hrho
    linarith
  have hunit0 : zetaResidueUnit rho = 0 := by simp [zetaResidueUnit, hrho1, hzero]
  have hbig : chronologicalMobiusWeightedSource w =O[𝓝[>] 0]
      (fun t : ℝ => t ^ (-(1/2 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound M ?_
    filter_upwards [hnear, self_mem_nhdsWithin] with t ht htpos
    rwa [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
  have hid := chronologicalMobiusWeightedSource_mellin_product hm hC hw htop hbig
  have hreal : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using hr.ne'
  have hslope : Tendsto (fun r : ℝ => (r : ℂ)⁻¹ * zetaResidueUnit (rho+(r:ℂ)))
      (𝓝[>] 0) (𝓝 (deriv zetaResidueUnit rho)) := by
    have hh := (analyticAt_zetaResidueUnit rho).differentiableAt.hasDerivAt.tendsto_slope_zero.comp hreal
    simpa [hunit0, smul_eq_mul] using! hh
  have hray : Tendsto (fun r : ℝ => rho+(r:ℂ)) (𝓝[>] 0) (𝓝 rho) := by
    simpa using! ((continuous_const.add Complex.continuous_ofReal).tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun r : ℝ => ‖mellin w (rho+(r:ℂ))*(rho+(r:ℂ)-1)‖)
      (𝓝[>] 0) (𝓝 ‖mellin w rho*(rho-1)‖) :=
    (((bounded_weight_mellin_diff hm hw htop (by rw [hrho]; positivity)).continuousAt.tendsto.comp
      hray).mul (((continuous_id.sub continuous_const).tendsto rho).comp hray)).norm
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hη : 0 < ε / (‖deriv riemannZeta rho‖ + 1) := by positivity
  have hle : ‖mellin w rho*(rho-1)‖ ≤
      (M + ε / (‖deriv riemannZeta rho‖ + 1)) * ‖deriv zetaResidueUnit rho‖ := by
    refine le_of_tendsto_of_tendsto hlim (hslope.norm.const_mul _) ?_
    filter_upwards [self_mem_nhdsWithin, chronological_mellin_abel_bound
      (mul_nonneg (by positivity) hC) hM
      (chronologicalMobiusWeightedSource_locallyIntegrable hm hC hw htop)
      (fun t ht => chronologicalMobiusWeightedSource_norm_bound hC hw htop ht)
      (fun t ht => chronologicalMobiusWeightedSource_eq_zero zero_le_one htop ht)
      hnear hrho hη] with r hr habel
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
    have hfac : mellin w (rho+(r:ℂ))*(rho+(r:ℂ)-1) =
        ((r:ℂ) * mellin (chronologicalMobiusWeightedSource w) (rho+(r:ℂ))) *
          ((r:ℂ)⁻¹ * zetaResidueUnit (rho+(r:ℂ))) := by
      rw [← hid _ (by simpa [hrho] using hr)]
      field_simp
    rw [hfac, norm_mul]
    exact mul_le_mul_of_nonneg_right habel (norm_nonneg _)
  rw [deriv_zetaResidueUnit_of_zero hrho1 hzero, norm_mul, norm_mul, mul_comm (‖rho - 1‖),
    ← mul_assoc] at hle
  have hpos : 0 < ‖rho - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hrho1)
  have hle' := le_of_mul_le_mul_right hle hpos
  have hextra : ε / (‖deriv riemannZeta rho‖ + 1) * ‖deriv riemannZeta rho‖ ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (deriv riemannZeta rho)]
  nlinarith

end RHTower
