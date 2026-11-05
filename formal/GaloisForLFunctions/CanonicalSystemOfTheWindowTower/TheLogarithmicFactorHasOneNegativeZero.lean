import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheReciprocalLogarithmicFactorVanishesAtInfinity
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The unique negative zero of the logarithmic factor

Reflection continues the factor through the origin and the interval `(-1,0)`.
Its unique zero is simple; the reciprocal residue is explicitly positive.
-/

open MeasureTheory Set Filter Topology Complex Metric
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

/-- The cut begins at minus one after reflection of the logarithmic symbol. -/
def logarithmicFactorContinuationDomain : Set ℂ :=
  {z : ℂ | -1 < z.re ∨ z.im ≠ 0}

theorem isOpen_logarithmicFactorContinuationDomain :
    IsOpen logarithmicFactorContinuationDomain :=
  (isOpen_lt continuous_const Complex.continuous_re).union
    (isClosed_eq Complex.continuous_im continuous_const).isOpen_compl

/-- Reflection supplies the actual values on the negative interval above the cut. -/
def continuedLogReferenceFactor (z : ℂ) : ℂ :=
  if z.re < 0 then logarithmicLaplaceSymbol (-z ^ 2) / complexLogReferenceFactor (-z)
  else complexLogReferenceFactor z

theorem continuedLogReferenceFactor_eq {z : ℂ} (hz : z ∈ slitPlane) :
    continuedLogReferenceFactor z = complexLogReferenceFactor z := by
  unfold continuedLogReferenceFactor
  split_ifs with hr
  · have hi : z.im ≠ 0 := (Complex.mem_slitPlane_iff.mp hz).resolve_left (not_lt.mpr hr.le)
    have he : complexLogReferenceFactor z * complexLogReferenceFactor (-z) =
        logarithmicLaplaceSymbol (-z ^ 2) := by
      simpa only [logarithmicLaplaceSymbol, sub_eq_add_neg] using complexLogReferenceFactor_reflection hi
    exact ((eq_div_iff (complexLogReferenceFactor_ne_zero (-z))).mpr he).symm
  · rfl

theorem continuedLogReferenceFactor_zero : continuedLogReferenceFactor 0 = 1 := by
  simp only [continuedLogReferenceFactor, Complex.zero_re, lt_self_iff_false, if_false,
    complexLogReferenceFactor, Complex.sqrt_zero, zero_mul, zero_div,
    integral_zero, mul_zero, Complex.exp_zero]

theorem continuedLogReferenceFactor_ofReal {s : ℝ} (hs : 0 < s) :
    continuedLogReferenceFactor (s : ℂ) = (logReferenceFactor s : ℂ) := by
  rw [continuedLogReferenceFactor_eq (Or.inl hs), complexLogReferenceFactor_ofReal hs]

private theorem differentiableAt_reflectedSymbol {z : ℂ} (hz : 1 - z ^ 2 ∈ slitPlane) :
    DifferentiableAt ℂ (fun w : ℂ => logarithmicLaplaceSymbol (-w ^ 2)) z := by
  have hp : DifferentiableAt ℂ (fun w : ℂ => 1 - w ^ 2) z := by fun_prop
  have hl : DifferentiableAt ℂ (fun w : ℂ => Complex.log (1 - w ^ 2)) z := by
    simpa only [Function.comp_def] using! (Complex.hasDerivAt_log hz).differentiableAt.comp z hp
  simpa only [logarithmicLaplaceSymbol, sub_eq_add_neg] using!
    (hl.const_mul ((1 / 2 : ℝ) : ℂ)).const_add (1 : ℂ)

private theorem analyticAt_continuedLogReferenceFactor_slit {z : ℂ} (hz : z ∈ slitPlane) :
    AnalyticAt ℂ continuedLogReferenceFactor z := by
  have ha := differentiableOn_complexLogReferenceFactor.analyticAt
    (Complex.isOpen_slitPlane.mem_nhds hz)
  apply ha.congr
  filter_upwards [Complex.isOpen_slitPlane.eventually_mem hz] with w hw
  exact (continuedLogReferenceFactor_eq hw).symm

private theorem analyticAt_continuedLogReferenceFactor_left {z : ℂ}
    (hz : z.re < 0) (ha : 1 - z ^ 2 ∈ slitPlane) :
    AnalyticAt ℂ continuedLogReferenceFactor z := by
  let U : Set ℂ := {w : ℂ | w.re < 0 ∧ 1 - w ^ 2 ∈ slitPlane}
  have hU : IsOpen U := (isOpen_lt Complex.continuous_re continuous_const).inter
    (Complex.isOpen_slitPlane.preimage (by fun_prop))
  have hd : DifferentiableOn ℂ
      (fun w : ℂ => logarithmicLaplaceSymbol (-w ^ 2) / complexLogReferenceFactor (-w)) U := by
    intro w hw
    have hm : -w ∈ slitPlane := Or.inl (by simpa only [Complex.neg_re] using neg_pos.mpr hw.1)
    have hK := differentiableOn_complexLogReferenceFactor.differentiableAt
      (Complex.isOpen_slitPlane.mem_nhds hm)
    have hneg : DifferentiableAt ℂ (fun v : ℂ => -v) w := by fun_prop
    have hden : DifferentiableAt ℂ (fun v : ℂ => complexLogReferenceFactor (-v)) w := by
      simpa only [Function.comp_def] using! hK.comp w hneg
    exact ((differentiableAt_reflectedSymbol hw.2).div hden
      (complexLogReferenceFactor_ne_zero (-w))).differentiableWithinAt
  have hquot := hd.analyticAt (hU.mem_nhds (show z ∈ U from ⟨hz, ha⟩))
  apply hquot.congr
  filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).eventually_mem hz] with w hw
  exact (if_pos hw).symm

private theorem analyticAt_continuedLogReferenceFactor_off_zero {z : ℂ}
    (hz : z ∈ logarithmicFactorContinuationDomain) (hne : z ≠ 0) :
    AnalyticAt ℂ continuedLogReferenceFactor z := by
  by_cases hs : z ∈ slitPlane
  · exact analyticAt_continuedLogReferenceFactor_slit hs
  · have hp : z.re ≤ 0 ∧ z.im = 0 := by
      simpa only [Complex.mem_slitPlane_iff, not_or, not_lt, not_ne_iff] using hs
    have hr : z.re < 0 := by
      rcases lt_or_eq_of_le hp.1 with h | h
      · exact h
      · exact False.elim (hne (Complex.ext h hp.2))
    have hlo : -1 < z.re := hz.resolve_right (not_not.mpr hp.2)
    have ha : 1 - z ^ 2 ∈ slitPlane := by
      apply Or.inl
      simp only [Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re, hp.2,
        zero_mul, sub_zero]
      nlinarith only [hlo, hr]
    exact analyticAt_continuedLogReferenceFactor_left hr ha

private theorem norm_continuedLogReferenceFactor_bounded_near_zero :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖continuedLogReferenceFactor z‖ ≤
      Real.sqrt (2 * logarithmicFactorGrowthConstant) + 2 := by
  have ha0 : 1 - (0 : ℂ) ^ 2 ∈ slitPlane := by
    norm_num [Complex.mem_slitPlane_iff]
  have hc : ContinuousAt (fun z : ℂ => logarithmicLaplaceSymbol (-z ^ 2)) 0 :=
    (differentiableAt_reflectedSymbol ha0).continuousAt
  have hv : ‖logarithmicLaplaceSymbol (-(0 : ℂ) ^ 2)‖ < 2 := by
    norm_num [logarithmicLaplaceSymbol]
  have hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖logarithmicLaplaceSymbol (-z ^ 2)‖ < 2 :=
    (hc.norm.tendsto.eventually (eventually_lt_nhds hv)).filter_mono nhdsWithin_le_nhds
  have hball : ∀ᶠ z in 𝓝 (0 : ℂ), ‖z‖ < 1 := by
    have hmem : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball (0 : ℂ) 1 := ball_mem_nhds (0 : ℂ) zero_lt_one
    simpa only [Metric.mem_ball, dist_zero_right] using hmem
  filter_upwards [hb, hball.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with z hsymbol hnorm hne
  have hz0 : z ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
  by_cases hr : z.re < 0
  · rw [continuedLogReferenceFactor, if_pos hr, norm_div]
    have hn : 0 < (-z).re := by simpa only [Complex.neg_re] using neg_pos.mpr hr
    have hl := one_le_norm_complexLogReferenceFactor hn
    calc
      _ ≤ ‖logarithmicLaplaceSymbol (-z ^ 2)‖ :=
        (div_le_iff₀ (zero_lt_one.trans_le hl)).mpr (le_mul_of_one_le_right (norm_nonneg _) hl)
      _ ≤ 2 := hsymbol.le
      _ ≤ _ := by linarith only [Real.sqrt_nonneg (2 * logarithmicFactorGrowthConstant)]
  · rw [continuedLogReferenceFactor, if_neg hr]
    have hnonneg : 0 ≤ z.re := le_of_not_gt hr
    have hup : ‖complexLogReferenceFactor z‖ ^ 2 ≤
        logarithmicFactorGrowthConstant * positiveLogarithmicSymbol ‖z‖ := by
      rcases lt_or_eq_of_le hnonneg with hp | he
      · exact complexLogReferenceFactor_norm_sq_le hp
      · have hi : z.im ≠ 0 := by
          intro hi
          exact hz0 (Complex.ext he.symm hi)
        exact complexLogReferenceFactor_norm_sq_le_closed hnonneg hi
    have hsym : positiveLogarithmicSymbol ‖z‖ ≤ 2 := by
      have hl := Real.log_le_sub_one_of_pos (show 0 < 1 + ‖z‖ ^ 2 by positivity)
      have hs : ‖z‖ ^ 2 ≤ 1 := by nlinarith only [hnorm, norm_nonneg z]
      unfold positiveLogarithmicSymbol
      linarith only [hl, hs]
    have hs : ‖complexLogReferenceFactor z‖ ^ 2 ≤ 2 * logarithmicFactorGrowthConstant := by
      have h := hup.trans (mul_le_mul_of_nonneg_left hsym logarithmicFactorGrowthConstant_pos.le)
      simpa only [mul_comm] using h
    have hsqrt := Real.sqrt_le_sqrt hs
    rw [Real.sqrt_sq (norm_nonneg _)] at hsqrt
    linarith only [hsqrt]

private theorem eventually_differentiable_continuedLogReferenceFactor :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ continuedLogReferenceFactor z := by
  have hball : ∀ᶠ z in 𝓝 (0 : ℂ), ‖z‖ < 1 := by
    have hmem : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball (0 : ℂ) 1 := ball_mem_nhds (0 : ℂ) zero_lt_one
    simpa only [Metric.mem_ball, dist_zero_right] using hmem
  filter_upwards [hball.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hnorm hne
  have hz0 : z ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
  have hz : z ∈ logarithmicFactorContinuationDomain := by
    apply Or.inl
    have hr := Complex.re_le_norm (-z)
    rw [Complex.neg_re, norm_neg] at hr
    linarith only [hr, hnorm]
  exact (analyticAt_continuedLogReferenceFactor_off_zero hz hz0).differentiableAt

private theorem tendsto_continuedLogReferenceFactor_positive :
    Tendsto (fun s : ℝ => continuedLogReferenceFactor (s : ℂ))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1) := by
  have hc : Tendsto (fun s : ℝ => (logReferenceFactor s : ℂ))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1) := by
    simpa only [Function.comp_def, Complex.ofReal_one] using!
      (Complex.continuous_ofReal.tendsto 1).comp tendsto_logReferenceFactor_at_zero
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (continuedLogReferenceFactor_ofReal hs).symm

/-- The reflected factor has its actual unit value at the removable origin. -/
theorem analyticAt_continuedLogReferenceFactor_zero :
    AnalyticAt ℂ continuedLogReferenceFactor 0 := by
  have hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] (0 : ℂ))
      (fun z => ‖continuedLogReferenceFactor z - continuedLogReferenceFactor 0‖) := by
    refine ⟨Real.sqrt (2 * logarithmicFactorGrowthConstant) + 3, eventually_map.mpr ?_⟩
    filter_upwards [norm_continuedLogReferenceFactor_bounded_near_zero] with z hz
    rw [continuedLogReferenceFactor_zero]
    have h := norm_sub_le (continuedLogReferenceFactor z) (1 : ℂ)
    rw [norm_one] at h
    linarith only [h, hz]
  have hl := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
    eventually_differentiable_continuedLogReferenceFactor hb
  have hemb : Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 0 (Ioi (0 : ℝ))) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change (s : ℂ) ≠ 0
      exact_mod_cast hs.ne'
  have hval : limUnder (𝓝[≠] (0 : ℂ)) continuedLogReferenceFactor = 1 :=
    tendsto_nhds_unique (hl.comp hemb) tendsto_continuedLogReferenceFactor_positive
  rw [hval] at hl
  have hc : ContinuousAt continuedLogReferenceFactor 0 := by
    rw [← continuousWithinAt_compl_self]
    change Tendsto continuedLogReferenceFactor (𝓝[≠] (0 : ℂ))
      (nhds (continuedLogReferenceFactor 0))
    rw [continuedLogReferenceFactor_zero]
    exact hl
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    eventually_differentiable_continuedLogReferenceFactor hc

/-- The only remaining cut of the continued factor is the real ray ending at minus one. -/
theorem analyticOnNhd_continuedLogReferenceFactor :
    AnalyticOnNhd ℂ continuedLogReferenceFactor logarithmicFactorContinuationDomain := by
  intro z hz
  by_cases hne : z = 0
  · subst z
    exact analyticAt_continuedLogReferenceFactor_zero
  · exact analyticAt_continuedLogReferenceFactor_off_zero hz hne

/-- The reciprocal factor has its isolated real pole at the negative of this number. -/
def logarithmicFactorZeroRadius : ℝ := Real.sqrt (1 - Real.exp (-2))

theorem logarithmicFactorZeroRadius_pos : 0 < logarithmicFactorZeroRadius := by
  have he : Real.exp (-2) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (-2 : ℝ) < 0)
  exact Real.sqrt_pos.mpr (sub_pos.mpr he)

theorem logarithmicFactorZeroRadius_sq :
    logarithmicFactorZeroRadius ^ 2 = 1 - Real.exp (-2) := by
  have he : Real.exp (-2) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (-2 : ℝ) ≤ 0)
  exact Real.sq_sqrt (sub_nonneg.mpr he)

theorem logarithmicFactorZeroRadius_lt_one : logarithmicFactorZeroRadius < 1 := by
  nlinarith only [logarithmicFactorZeroRadius_sq, Real.exp_pos (-2), logarithmicFactorZeroRadius_pos]

private theorem logarithmicLaplaceSymbol_zero_radius :
    logarithmicLaplaceSymbol (-(logarithmicFactorZeroRadius : ℂ) ^ 2) = 0 := by
  have he : 1 + -(logarithmicFactorZeroRadius : ℂ) ^ 2 = (Real.exp (-2) : ℂ) := by
    have h : (logarithmicFactorZeroRadius : ℂ) ^ 2 = 1 - (Real.exp (-2) : ℂ) := by
      exact_mod_cast logarithmicFactorZeroRadius_sq
    linear_combination -h
  unfold logarithmicLaplaceSymbol
  rw [he, ← Complex.ofReal_log (Real.exp_pos (-2)).le, Real.log_exp]
  norm_num

theorem continuedLogReferenceFactor_neg_radius :
    continuedLogReferenceFactor (-(logarithmicFactorZeroRadius : ℂ)) = 0 := by
  have hr : (-(logarithmicFactorZeroRadius : ℂ)).re < 0 := by
    simpa only [Complex.neg_re, Complex.ofReal_re] using neg_neg_of_pos logarithmicFactorZeroRadius_pos
  rw [continuedLogReferenceFactor, if_pos hr, neg_sq, logarithmicLaplaceSymbol_zero_radius, zero_div]

private theorem logarithmicLaplaceSymbol_reflected_eq_zero {z : ℂ}
    (hz : logarithmicLaplaceSymbol (-z ^ 2) = 0) :
    z = (logarithmicFactorZeroRadius : ℂ) ∨ z = -(logarithmicFactorZeroRadius : ℂ) := by
  have harg : 1 - z ^ 2 ≠ 0 := by
    intro h
    have he : 1 + -z ^ 2 = 0 := by simpa only [sub_eq_add_neg] using h
    rw [logarithmicLaplaceSymbol, he, Complex.log_zero, mul_zero] at hz
    norm_num at hz
  have hlog : Complex.log (1 - z ^ 2) = (-2 : ℂ) := by
    unfold logarithmicLaplaceSymbol at hz
    rw [← sub_eq_add_neg] at hz
    have hh : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; rfl
    rw [hh] at hz
    linear_combination 2 * hz
  have he := congrArg Complex.exp hlog
  rw [Complex.exp_log harg] at he
  have hexp : Complex.exp (-2 : ℂ) = (Real.exp (-2) : ℂ) := by
    rw [Complex.ofReal_exp]
    norm_num
  rw [hexp] at he
  have hb : (logarithmicFactorZeroRadius : ℂ) ^ 2 = 1 - (Real.exp (-2) : ℂ) := by
    exact_mod_cast logarithmicFactorZeroRadius_sq
  have hs : z ^ 2 = (logarithmicFactorZeroRadius : ℂ) ^ 2 := by
    linear_combination -he - hb
  have hp : (z - (logarithmicFactorZeroRadius : ℂ)) * (z + (logarithmicFactorZeroRadius : ℂ)) = 0 := by
    calc
      _ = z ^ 2 - (logarithmicFactorZeroRadius : ℂ) ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hs
  rcases mul_eq_zero.mp hp with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · right
    linear_combination h

/-- The reflected factor has exactly one zero, on the negative interval above the cut. -/
theorem continuedLogReferenceFactor_eq_zero_iff (z : ℂ) :
    continuedLogReferenceFactor z = 0 ↔ z = -(logarithmicFactorZeroRadius : ℂ) := by
  constructor
  · intro hz
    by_cases hr : z.re < 0
    · rw [continuedLogReferenceFactor, if_pos hr, div_eq_mul_inv] at hz
      have hsymbol : logarithmicLaplaceSymbol (-z ^ 2) = 0 :=
        (mul_eq_zero.mp hz).resolve_right (inv_ne_zero (complexLogReferenceFactor_ne_zero (-z)))
      rcases logarithmicLaplaceSymbol_reflected_eq_zero hsymbol with hp | hn
      · have h : logarithmicFactorZeroRadius < 0 := by simpa only [hp, Complex.ofReal_re] using hr
        exact False.elim (not_lt_of_ge logarithmicFactorZeroRadius_pos.le h)
      · exact hn
    · rw [continuedLogReferenceFactor, if_neg hr] at hz
      exact False.elim (complexLogReferenceFactor_ne_zero z hz)
  · rintro rfl
    exact continuedLogReferenceFactor_neg_radius

theorem one_sub_logarithmicFactorZeroRadius_sq :
    1 - logarithmicFactorZeroRadius ^ 2 = Real.exp (-2) := by
  rw [logarithmicFactorZeroRadius_sq]
  ring

/-- The positive residue of the reciprocal factor at its unique negative pole. -/
def logarithmicFactorReciprocalResidue : ℝ :=
  logReferenceFactor logarithmicFactorZeroRadius * (1 - logarithmicFactorZeroRadius ^ 2) /
    logarithmicFactorZeroRadius

theorem logarithmicFactorReciprocalResidue_pos : 0 < logarithmicFactorReciprocalResidue := by
  unfold logarithmicFactorReciprocalResidue
  rw [one_sub_logarithmicFactorZeroRadius_sq]
  exact div_pos (mul_pos (zero_lt_one.trans_le (one_le_logReferenceFactor _)) (Real.exp_pos _))
    logarithmicFactorZeroRadius_pos

private theorem hasDerivAt_reflectedSymbol {z : ℂ} (hz : 1 - z ^ 2 ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => logarithmicLaplaceSymbol (-w ^ 2)) (-z / (1 - z ^ 2)) z := by
  have hp : HasDerivAt (fun w : ℂ => 1 - w ^ 2) (-(2 * z)) z := by
    simpa only [id_eq, Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl,
      pow_one, mul_one] using! ((hasDerivAt_id z).pow 2).const_sub (1 : ℂ)
  have hl := (Complex.hasDerivAt_log hz).comp z hp
  have hn := (hl.const_mul ((1 / 2 : ℝ) : ℂ)).const_add (1 : ℂ)
  have he : ((1 / 2 : ℝ) : ℂ) * ((1 - z ^ 2)⁻¹ * -(2 * z)) = -z / (1 - z ^ 2) := by
    push_cast
    ring
  simpa only [logarithmicLaplaceSymbol, sub_eq_add_neg] using! hn.congr_deriv he

/-- The negative zero is simple, with derivative equal to the inverse residue. -/
theorem hasDerivAt_continuedLogReferenceFactor_neg_radius :
    HasDerivAt continuedLogReferenceFactor (logarithmicFactorReciprocalResidue : ℂ)⁻¹
      (-(logarithmicFactorZeroRadius : ℂ)) := by
  let b : ℝ := logarithmicFactorZeroRadius
  let p : ℂ := -(b : ℂ)
  have hb : 0 < b := logarithmicFactorZeroRadius_pos
  have hp : p.re < 0 := by simpa only [p, Complex.neg_re, Complex.ofReal_re] using neg_neg_of_pos hb
  have harg : 1 - p ^ 2 ∈ slitPlane := by
    have he : 1 - p ^ 2 = (Real.exp (-2) : ℂ) := by
      dsimp only [p, b]
      rw [neg_sq]
      exact_mod_cast one_sub_logarithmicFactorZeroRadius_sq
    rw [he]
    exact Or.inl (Real.exp_pos _)
  have hm : -p ∈ slitPlane := Or.inl (by simpa only [Complex.neg_re] using neg_pos.mpr hp)
  have hK := differentiableOn_complexLogReferenceFactor.differentiableAt
    (Complex.isOpen_slitPlane.mem_nhds hm)
  have hneg : DifferentiableAt ℂ (fun z : ℂ => -z) p := by fun_prop
  have hden : DifferentiableAt ℂ (fun z : ℂ => complexLogReferenceFactor (-z)) p := by
    simpa only [Function.comp_def] using! hK.comp p hneg
  have hq := (hasDerivAt_reflectedSymbol harg).div hden.hasDerivAt
    (complexLogReferenceFactor_ne_zero (-p))
  have hzero : logarithmicLaplaceSymbol (-p ^ 2) = 0 := by
    simpa only [p, b, neg_sq] using logarithmicLaplaceSymbol_zero_radius
  have hval : complexLogReferenceFactor (-p) = (logReferenceFactor b : ℂ) := by
    simpa only [p, neg_neg] using complexLogReferenceFactor_ofReal hb
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hsC : 1 - (b : ℂ) ^ 2 ≠ 0 := by
    have hs : 0 < 1 - b ^ 2 := by
      dsimp only [b]
      rw [one_sub_logarithmicFactorZeroRadius_sq]
      exact Real.exp_pos _
    exact_mod_cast hs.ne'
  have hkC : (logReferenceFactor b : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (one_le_logReferenceFactor b)).ne'
  have he :
      ((-p / (1 - p ^ 2)) * complexLogReferenceFactor (-p) -
        logarithmicLaplaceSymbol (-p ^ 2) * deriv (fun z : ℂ => complexLogReferenceFactor (-z)) p) /
        complexLogReferenceFactor (-p) ^ 2 = (logarithmicFactorReciprocalResidue : ℂ)⁻¹ := by
    rw [hzero, zero_mul, sub_zero, hval]
    dsimp only [p, logarithmicFactorReciprocalResidue]
    change ((-(-(b : ℂ)) / (1 - (-(b : ℂ)) ^ 2)) * (logReferenceFactor b : ℂ)) /
      (logReferenceFactor b : ℂ) ^ 2 = ((logReferenceFactor b * (1 - b ^ 2) / b : ℝ) : ℂ)⁻¹
    simp only [neg_neg, neg_sq]
    push_cast
    field_simp [hbC, hsC, hkC]
  have hnear : continuedLogReferenceFactor =ᶠ[𝓝 p]
      (fun z : ℂ => logarithmicLaplaceSymbol (-z ^ 2) / complexLogReferenceFactor (-z)) := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).eventually_mem hp] with z hz
    exact if_pos hz
  exact (hq.congr_deriv he).congr_of_eventuallyEq hnear

/-- The reciprocal has the stated positive residue at its simple pole. -/
theorem tendsto_logarithmicFactor_reciprocal_residue :
    Tendsto (fun z : ℂ => (z + (logarithmicFactorZeroRadius : ℂ)) / continuedLogReferenceFactor z)
      (𝓝[≠] (-(logarithmicFactorZeroRadius : ℂ))) (nhds (logarithmicFactorReciprocalResidue : ℂ)) := by
  let p : ℂ := -(logarithmicFactorZeroRadius : ℂ)
  have hd := hasDerivAt_continuedLogReferenceFactor_neg_radius
  have hc : ContinuousAt (dslope continuedLogReferenceFactor p) p :=
    continuousAt_dslope_same.mpr hd.differentiableAt
  have hl : Tendsto (dslope continuedLogReferenceFactor p) (𝓝[≠] p)
      (nhds (logarithmicFactorReciprocalResidue : ℂ)⁻¹) := by
    have h : Tendsto (dslope continuedLogReferenceFactor p) (𝓝[≠] p)
        (nhds (dslope continuedLogReferenceFactor p p)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    rwa [dslope_same, hd.deriv] at h
  have hR : (logarithmicFactorReciprocalResidue : ℂ) ≠ 0 := by
    exact_mod_cast logarithmicFactorReciprocalResidue_pos.ne'
  have hi := hl.inv₀ (inv_ne_zero hR)
  rw [inv_inv] at hi
  apply hi.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzp : z ≠ p := by simpa only [mem_compl_iff, mem_singleton_iff] using hz
  rw [dslope_of_ne continuedLogReferenceFactor hzp, slope, vsub_eq_sub, smul_eq_mul]
  dsimp only [p]
  rw [continuedLogReferenceFactor_neg_radius, sub_zero, mul_inv_rev, inv_inv,
    sub_neg_eq_add, div_eq_mul_inv]
  ring

#print axioms analyticOnNhd_continuedLogReferenceFactor
#print axioms continuedLogReferenceFactor_eq_zero_iff
#print axioms hasDerivAt_continuedLogReferenceFactor_neg_radius
#print axioms tendsto_logarithmicFactor_reciprocal_residue


end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
