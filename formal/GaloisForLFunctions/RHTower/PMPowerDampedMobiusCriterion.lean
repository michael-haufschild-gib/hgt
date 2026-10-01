import GaloisForLFunctions.RHTower.PMPowerDampedMobiusMellin
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLineContinuity
import GaloisForLFunctions.RHTower.NymanBeurlingCriterion

/-!
# Cofinal canonical admission of the power-damped Möbius source forces RH

For a canonically admitted small positive damping, the entire residue unit clears
the shifted zeta pole and continues the literal Mellin identity across the right
critical strip. An off-line zero then forces a translated zeta zero.

Isolation of zeros shows that canonical admission at positive dampings arbitrarily
close to zero implies RH. Equivalently, failure of RH leaves a whole interval of
small positive dampings without canonical admission. The admission premise is
not proved here; the unconditional safe range remains damping greater than one half.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

theorem pmPowerDamped_cleared_mellin_initial (ε : ℝ) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsε : 1 < s.re + ε) :
    s * zetaResidueUnit (s + (ε : ℂ)) * mellin (pmPowerDampedFermiSource ε) s =
      (s + (ε : ℂ) - 1) * (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hsne : s ≠ 0 := by intro h; simp [h] at hs0
  have hshift : 1 < (s + (ε : ℂ)).re := by simpa using hsε
  have hshiftne : s + (ε : ℂ) ≠ 1 := by
    intro h
    rw [h] at hshift
    norm_num at hshift
  have hζ := riemannZeta_ne_zero_of_one_lt_re hshift
  rw [zetaResidueUnit, Function.update_of_ne hshiftne,
    (hasMellin_pmPowerDampedFermiSource ε hs0 hs1 hsε).2]
  field_simp

theorem pmPowerDamped_cleared_mellin (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi 0)))
    {s : ℂ} (hs : 1 / 2 < s.re ∧ s.re < 1) :
    s * zetaResidueUnit (s + (ε : ℂ)) * mellin (pmPowerDampedFermiSource ε) s =
      (s + (ε : ℂ) - 1) * (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  let S : Set ℂ := {z | 1 / 2 < z.re ∧ z.re < 1}
  have hF := analyticOnNhd_mellin_pmPowerDampedFermiSource ε hf
  have hleft : AnalyticOnNhd ℂ (fun z =>
      z * zetaResidueUnit (z + (ε : ℂ)) * mellin (pmPowerDampedFermiSource ε) z) S := by
    intro z hz
    have hshift : AnalyticAt ℂ (fun w : ℂ => w + (ε : ℂ)) z :=
      analyticAt_id.add analyticAt_const
    exact (analyticAt_id.mul
      ((analyticAt_zetaResidueUnit (z + (ε : ℂ))).comp
        (f := fun w : ℂ => w + (ε : ℂ)) hshift)).mul (hF z hz.1)
  have hright : AnalyticOnNhd ℂ (fun z =>
      (z + (ε : ℂ) - 1) * (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z) S := by
    intro z hz
    have hz1 : z ≠ 1 := fun h => (ne_of_lt hz.2) (congrArg Complex.re h)
    have hpow : AnalyticAt ℂ (fun w : ℂ => (2 : ℂ) ^ (1 - w)) z := by
      simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
      exact (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).cexp'
    exact (((analyticAt_id.add analyticAt_const).sub analyticAt_const).mul
      (analyticAt_const.sub hpow)).mul (Sieve.analyticAt_riemannZeta_of_ne_one hz1)
  let r : ℂ := ((1 - ε / 2 : ℝ) : ℂ)
  have hrre : r.re = 1 - ε / 2 := rfl
  have hrS : r ∈ S := by
    change 1 / 2 < r.re ∧ r.re < 1
    rw [hrre]
    constructor <;> linarith
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ 1 < z.re + ε} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt continuous_const (Complex.continuous_re.add continuous_const)))
  have hrB : r ∈ {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ 1 < z.re + ε} := by
    simp only [mem_setOf_eq, hrre]
    constructor
    · linarith
    · constructor <;> linarith
  have hevent : (fun z =>
      z * zetaResidueUnit (z + (ε : ℂ)) * mellin (pmPowerDampedFermiSource ε) z)
      =ᶠ[𝓝 r] (fun z =>
        (z + (ε : ℂ) - 1) * (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z) := by
    filter_upwards [hopen.mem_nhds hrB] with z hz
    exact pmPowerDamped_cleared_mellin_initial ε hz.1 hz.2.1 hz.2.2
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright
    ((convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_re_lt 1)).isPreconnected
    hrS hevent hs

theorem pmPowerDamped_zero_translation (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi 0)))
    {ρ : ℂ} (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1) (hzero : riemannZeta ρ = 0) :
    riemannZeta (ρ - (ε : ℂ)) = 0 := by
  have hs : 1 / 2 < (ρ - (ε : ℂ)).re ∧ (ρ - (ε : ℂ)).re < 1 := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    constructor <;> linarith
  have h := pmPowerDamped_cleared_mellin ε hε0 hε1 hf hs
  rw [sub_add_cancel] at h
  have hρne : ρ ≠ 1 := fun heq => (ne_of_lt hρ1) (congrArg Complex.re heq)
  rw [zetaResidueUnit, Function.update_of_ne hρne, hzero] at h
  simp only [mul_zero, zero_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left
    (mul_ne_zero (sub_ne_zero.mpr hρne) (one_sub_two_cpow_ne_zero hs.2))

theorem riemannHypothesis_of_pmPowerDamped_cofinal_admission
    (hadmit : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi 0))) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hzero, hρ0, hρ1⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  have hne : ∀ᶠ z in 𝓝[≠] ρ, zetaResidueUnit z ≠ 0 :=
    (analyticAt_zetaResidueUnit ρ).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun h => Sieve.zetaResidueUnit_order_ne_top ρ (analyticOrderAt_eq_top.mpr h))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp hne
  have hδ : 0 < min r (min (1 / 2 : ℝ) (ρ.re - 1 / 2)) :=
    lt_min hr (lt_min (by norm_num) (sub_pos.mpr hρ0))
  obtain ⟨ε, hε0, hεδ, hf⟩ := hadmit _ hδ
  have hεr : ε < r := hεδ.trans_le (min_le_left _ _)
  have hεhalf : ε < 1 / 2 :=
    hεδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεgap : ε < ρ.re - 1 / 2 :=
    hεδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hdist : dist (ρ - (ε : ℂ)) ρ < r := by
    rw [dist_eq_norm, show ρ - (ε : ℂ) - ρ = -(ε : ℂ) by ring,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
    exact hεr
  have hdiff : ρ - (ε : ℂ) ≠ ρ := by
    intro h
    have hreal := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re] at hreal
    linarith
  have hunit := hball (show ρ - (ε : ℂ) ∈ Metric.ball ρ r ∩ {ρ}ᶜ from
    ⟨hdist, hdiff⟩)
  have htranslate := pmPowerDamped_zero_translation ε hε0 hεhalf.le hf
    (by linarith : 1 / 2 + ε < ρ.re) hρ1 hzero
  have hs1 : (ρ - (ε : ℂ)).re < 1 := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hsne : ρ - (ε : ℂ) ≠ 1 := fun heq => (ne_of_lt hs1) (congrArg Complex.re heq)
  apply hunit
  rw [zetaResidueUnit, Function.update_of_ne hsne, htranslate, mul_zero]

theorem pmPowerDamped_admission_gap_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ¬ MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi 0)) := by
  by_contra! h
  exact hRH (riemannHypothesis_of_pmPowerDamped_cofinal_admission h)

end RHTower
