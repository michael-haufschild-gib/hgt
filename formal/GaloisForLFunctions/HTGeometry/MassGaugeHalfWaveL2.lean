import GaloisForLFunctions.HTGeometry.MassDispersionRadiationCorona
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Exact L2 growth of the exponentially gauged massive half-wave

The half-wave multiplier with symbol

`exp (-i * u * sqrt ((xi - i * lambda)^(2 : ℕ) + a^(2 : ℕ)))`

has exact operator norm `exp (|u| * lambda)` on `L2(ℝ)`.  Moreover, every
nonzero datum has an unbounded two-sided orbit.  The lower bounds use
positive-measure frequency packets or radiation-level pieces of the datum;
they do not assume that the pointwise radiation supremum is attained.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology MeasureTheory Set ENNReal

/-- The gauged mass radicand is continuous in frequency. -/
theorem continuous_massGaugeRadicand (a lambda : ℝ) :
    Continuous (massGaugeRadicand a lambda) := by
  unfold massGaugeRadicand
  fun_prop

/-- In the open mass chamber, the principal gauged dispersion is continuous
in frequency because its radicand stays in the open right half-plane. -/
theorem continuous_massGaugeDispersion {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 ≤ lambda) : Continuous (massGaugeDispersion a lambda) := by
  rw [continuous_iff_continuousAt]
  intro xi
  apply (Complex.continuousAt_sqrt (Or.inl ?_)).comp
    (continuous_massGaugeRadicand a lambda).continuousAt
  rw [massGaugeRadicand_re]
  nlinarith

/-- The gauged massive half-wave symbol is continuous in frequency. -/
theorem continuous_massGaugeHalfWaveSymbol {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 ≤ lambda) (u : ℝ) :
    Continuous (massGaugeHalfWaveSymbol a lambda u) := by
  unfold massGaugeHalfWaveSymbol
  exact Complex.continuous_exp.comp
    (continuous_const.mul (continuous_massGaugeDispersion ha hlambda))

/-- The half-wave symbol belongs to `L∞(ℝ)`. -/
theorem massGaugeHalfWaveSymbol_memLp {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 < lambda) (u : ℝ) :
    MemLp (massGaugeHalfWaveSymbol a lambda u) ∞ volume :=
  memLp_top_of_bound
    (continuous_massGaugeHalfWaveSymbol ha hlambda.le u).aestronglyMeasurable
    (Real.exp (|u| * lambda))
    (Filter.Eventually.of_forall (norm_massGaugeHalfWaveSymbol_le ha hlambda u))

/-- The half-wave symbol represented as an `L∞(ℝ)` function. -/
noncomputable def massGaugeHalfWaveSymbolLp {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 < lambda) (u : ℝ) : Lp ℂ ∞ (volume : Measure ℝ) :=
  (massGaugeHalfWaveSymbol_memLp ha hlambda u).toLp
    (massGaugeHalfWaveSymbol a lambda u)

/-- The `L∞` norm is bounded by the radiation envelope. -/
theorem massGaugeHalfWaveSymbolLp_norm_le {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 < lambda) (u : ℝ) :
    ‖massGaugeHalfWaveSymbolLp ha hlambda u‖ ≤ Real.exp (|u| * lambda) := by
  rw [massGaugeHalfWaveSymbolLp, Lp.norm_toLp, eLpNorm_exponent_top]
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _)
    (eLpNormEssSup_le_of_ae_bound
      (Filter.Eventually.of_forall (norm_massGaugeHalfWaveSymbol_le ha hlambda u)))

/-- Multiplication by the gauged half-wave symbol on Fourier-side `L2(ℝ)`. -/
noncomputable def massGaugeHalfWaveL2 {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 < lambda) (u : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2
    (massGaugeHalfWaveSymbolLp ha hlambda u)

/-- The `L2` operator acts almost everywhere by its half-wave multiplier. -/
theorem massGaugeHalfWaveL2_apply_ae {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 < lambda) (u : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    massGaugeHalfWaveL2 ha hlambda u f =ᵐ[volume]
      fun xi => massGaugeHalfWaveSymbol a lambda u xi * f xi := by
  apply (ContinuousLinearMap.coeFn_holder _ _ _).trans
  filter_upwards
    [MemLp.coeFn_toLp (massGaugeHalfWaveSymbol_memLp ha hlambda u)] with xi hxi
  simp [massGaugeHalfWaveSymbolLp, hxi]

/-- The half-wave symbol is the identity at time zero. -/
@[simp]
theorem massGaugeHalfWaveSymbol_zero (a lambda xi : ℝ) :
    massGaugeHalfWaveSymbol a lambda 0 xi = 1 := by
  simp [massGaugeHalfWaveSymbol]

/-- Half-wave symbols multiply according to addition of time parameters. -/
theorem massGaugeHalfWaveSymbol_add (a lambda u v xi : ℝ) :
    massGaugeHalfWaveSymbol a lambda (u + v) xi =
      massGaugeHalfWaveSymbol a lambda u xi *
        massGaugeHalfWaveSymbol a lambda v xi := by
  rw [massGaugeHalfWaveSymbol, massGaugeHalfWaveSymbol,
    massGaugeHalfWaveSymbol, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Fourier-side half-wave operator is the identity at time zero. -/
@[simp]
theorem massGaugeHalfWaveL2_zero_apply {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 < lambda) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    massGaugeHalfWaveL2 ha hlambda 0 f = f := by
  apply Lp.ext
  filter_upwards [massGaugeHalfWaveL2_apply_ae ha hlambda 0 f] with xi hxi
  simpa using hxi

/-- Exact half-wave group law on every `L2` datum. -/
theorem massGaugeHalfWaveL2_add_apply {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 < lambda) (u v : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    massGaugeHalfWaveL2 ha hlambda (u + v) f =
      massGaugeHalfWaveL2 ha hlambda u
        (massGaugeHalfWaveL2 ha hlambda v f) := by
  apply Lp.ext
  filter_upwards
    [massGaugeHalfWaveL2_apply_ae ha hlambda (u + v) f,
      massGaugeHalfWaveL2_apply_ae ha hlambda u
        (massGaugeHalfWaveL2 ha hlambda v f),
      massGaugeHalfWaveL2_apply_ae ha hlambda v f] with xi hsum houter hinner
  rw [hsum, houter, hinner, massGaugeHalfWaveSymbol_add]
  ring

/-- Operator-norm upper bound from Hölder multiplication. -/
theorem massGaugeHalfWaveL2_norm_le {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 < lambda) (u : ℝ) :
    ‖massGaugeHalfWaveL2 ha hlambda u‖ ≤ Real.exp (|u| * lambda) := by
  calc
    ‖massGaugeHalfWaveL2 ha hlambda u‖ ≤
        ‖(ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2‖ *
          ‖massGaugeHalfWaveSymbolLp ha hlambda u‖ := by
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * Real.exp (|u| * lambda) := by
      gcongr
      · exact (ContinuousLinearMap.norm_holderL_le
          (B := ContinuousLinearMap.mul ℂ ℂ)).trans
            (ContinuousLinearMap.opNorm_mul_le ℂ ℂ)
      · exact massGaugeHalfWaveSymbolLp_norm_le ha hlambda u
    _ = Real.exp (|u| * lambda) := one_mul _

/-- Every strict sub-envelope is detected by a positive-measure frequency
packet, hence is a lower bound for the `L2` operator norm. -/
theorem massGaugeHalfWaveL2_norm_ge_of_pos_lt {a lambda : ℝ}
    (ha : lambda < a) (hlambda : 0 < lambda) (u c : ℝ)
    (hcpos : 0 < c) (hc : c < Real.exp (|u| * lambda)) :
    c ≤ ‖massGaugeHalfWaveL2 ha hlambda u‖ := by
  have hex : ∃ l r : ℝ, l < r ∧
      ∀ xi ∈ Ioo l r, c < ‖massGaugeHalfWaveSymbol a lambda u xi‖ := by
    by_cases hu : 0 ≤ u
    · have hlim :=
        tendsto_norm_massGaugeHalfWaveSymbol_atBot a lambda u ha.le hlambda.le
      have hev : ∀ᶠ xi : ℝ in atBot,
          c < ‖massGaugeHalfWaveSymbol a lambda u xi‖ :=
        hlim.eventually
          (eventually_gt_nhds (by simpa [abs_of_nonneg hu] using hc))
      rw [eventually_atBot] at hev
      obtain ⟨b, hb⟩ := hev
      refine ⟨b - 2, b - 1, by linarith, ?_⟩
      intro xi hxi
      exact hb xi (by linarith [hxi.2])
    · have hu' : u < 0 := lt_of_not_ge hu
      have hlim :=
        tendsto_norm_massGaugeHalfWaveSymbol_atTop a lambda u ha.le hlambda.le
      have hev : ∀ᶠ xi : ℝ in atTop,
          c < ‖massGaugeHalfWaveSymbol a lambda u xi‖ :=
        hlim.eventually (eventually_gt_nhds (by simpa [abs_of_neg hu'] using hc))
      rw [eventually_atTop] at hev
      obtain ⟨b, hb⟩ := hev
      refine ⟨b + 1, b + 2, by linarith, ?_⟩
      intro xi hxi
      exact hb xi (by linarith [hxi.1])
  obtain ⟨l, r, hlr, hsymbol⟩ := hex
  have hfinite : (volume : Measure ℝ) (Ioo l r) ≠ ∞ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  let f : Lp ℂ 2 (volume : Measure ℝ) :=
    indicatorConstLp 2 measurableSet_Ioo hfinite (1 : ℂ)
  have hfnorm : ‖f‖ = (r - l) ^ (1 / (2 : ℝ)) := by
    simp [f, norm_indicatorConstLp, Real.volume_real_Ioo_of_le hlr.le]
  have hfnorm_pos : 0 < ‖f‖ := by
    rw [hfnorm]
    positivity
  have hT := massGaugeHalfWaveL2_apply_ae ha hlambda u f
  have hf : (f : ℝ → ℂ) =ᵐ[volume]
      (Ioo l r).indicator (fun _ => (1 : ℂ)) := by
    dsimp only [f]
    exact @indicatorConstLp_coeFn ℝ ℂ _ 2 (volume : Measure ℝ) _
      (Ioo l r) measurableSet_Ioo hfinite (1 : ℂ)
  have hpoint : ∀ᵐ xi : ℝ ∂volume,
      ‖((c : ℂ) • f) xi‖ ≤ ‖massGaugeHalfWaveL2 ha hlambda u f xi‖ := by
    filter_upwards [hT, hf, Lp.coeFn_smul (c : ℂ) f] with xi hTxi hfxi hcxi
    rw [hTxi, hcxi]
    simp only [Pi.smul_apply, hfxi]
    by_cases hxi : xi ∈ Ioo l r
    · rw [Set.indicator_of_mem hxi]
      simpa [norm_smul, abs_of_pos hcpos] using (hsymbol xi hxi).le
    · rw [Set.indicator_of_notMem hxi]
      simp
  have hnorm : ‖(c : ℂ) • f‖ ≤ ‖massGaugeHalfWaveL2 ha hlambda u f‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    exact ENNReal.toReal_mono (by finiteness) (eLpNorm_mono_ae hpoint)
  have happly := (massGaugeHalfWaveL2 ha hlambda u).le_opNorm f
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos] at hnorm
  nlinarith

/-- Exact `L2` operator norm: the two radiation ends detect the full
exponential gauge character. -/
theorem massGaugeHalfWaveL2_norm_eq {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 < lambda) (u : ℝ) :
    ‖massGaugeHalfWaveL2 ha hlambda u‖ = Real.exp (|u| * lambda) := by
  apply le_antisymm (massGaugeHalfWaveL2_norm_le ha hlambda u)
  apply le_of_forall_lt
  intro c hc
  by_cases hc0 : c < 0
  · exact hc0.trans_le (ContinuousLinearMap.opNorm_nonneg _)
  · have hc0' : 0 ≤ c := le_of_not_gt hc0
    let d := (c + Real.exp (|u| * lambda)) / 2
    have hcd : c < d := by dsimp [d]; linarith
    have hdC : d < Real.exp (|u| * lambda) := by dsimp [d]; linarith
    have hdpos : 0 < d := by
      dsimp [d]
      have hCpos : 0 < Real.exp (|u| * lambda) := Real.exp_pos _
      positivity
    exact hcd.trans_le
      (massGaugeHalfWaveL2_norm_ge_of_pos_lt ha hlambda u d hdpos hdC)

/-- An `L2` function restricted to a measurable frequency set remains in
`L2`. -/
theorem massGaugeL2Restriction_memLp (s : Set ℝ) (hs : MeasurableSet s)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (s.indicator fun xi => f xi) 2 (volume : Measure ℝ) :=
  (Lp.memLp f).indicator hs

/-- Restriction of an `L2` function to a measurable frequency set. -/
noncomputable def massGaugeL2Restriction (s : Set ℝ) (hs : MeasurableSet s)
    (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (massGaugeL2Restriction_memLp s hs f).toLp (s.indicator fun xi => f xi)

/-- The `L2` restriction agrees almost everywhere with the pointwise
indicator. -/
theorem massGaugeL2Restriction_apply_ae (s : Set ℝ) (hs : MeasurableSet s)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (massGaugeL2Restriction s hs f : ℝ → ℂ) =ᵐ[volume]
      s.indicator fun xi => f xi := by
  dsimp only [massGaugeL2Restriction]
  exact MemLp.coeFn_toLp (massGaugeL2Restriction_memLp s hs f)

/-- Positive measure of the restricted support forces a nonzero `L2`
restriction. -/
theorem massGaugeL2Restriction_ne_zero_of_measure_support_inter_ne_zero
    (s : Set ℝ) (hs : MeasurableSet s) (f : Lp ℂ 2 (volume : Measure ℝ))
    (hpos : volume ((Function.support fun xi => f xi) ∩ s) ≠ 0) :
    massGaugeL2Restriction s hs f ≠ 0 := by
  intro hzero
  have hae : (massGaugeL2Restriction s hs f : ℝ → ℂ) =ᵐ[volume] 0 :=
    Lp.eq_zero_iff_ae_eq_zero.mp hzero
  have hind : (s.indicator fun xi => f xi) =ᵐ[volume] 0 :=
    (massGaugeL2Restriction_apply_ae s hs f).symm.trans hae
  have hsupp : volume (Function.support (s.indicator fun xi => f xi)) = 0 :=
    ((volume : Measure ℝ).measure_support_eq_zero_iff).2 hind
  apply hpos
  simpa [Set.support_indicator, Set.inter_comm] using hsupp

/-- A signed radiation lower bound on a measurable frequency piece gives a
quantitative lower bound for the corresponding half-wave orbit. -/
theorem massGaugeHalfWaveL2_apply_norm_ge_restriction
    {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (s : Set ℝ) (hs : MeasurableSet s)
    (epsilon delta u : ℝ) (hu : 0 ≤ u)
    (hgrowth : ∀ xi ∈ s,
      delta ≤ epsilon * (massGaugeDispersion a lambda xi).im) :
    Real.exp (u * delta) * ‖massGaugeL2Restriction s hs f‖ ≤
      ‖massGaugeHalfWaveL2 ha hlambda (epsilon * u) f‖ := by
  let g := massGaugeL2Restriction s hs f
  have hT := massGaugeHalfWaveL2_apply_ae ha hlambda (epsilon * u) f
  have hg := massGaugeL2Restriction_apply_ae s hs f
  change (g : ℝ → ℂ) =ᵐ[volume] s.indicator (fun xi => f xi) at hg
  have hpoint : ∀ᵐ xi : ℝ ∂volume,
      ‖((Real.exp (u * delta) : ℂ) • g) xi‖ ≤
        ‖massGaugeHalfWaveL2 ha hlambda (epsilon * u) f xi‖ := by
    filter_upwards [hT, hg,
      Lp.coeFn_smul (Real.exp (u * delta) : ℂ) g] with xi hTxi hgxi hscale
    rw [hTxi, hscale]
    simp only [Pi.smul_apply, hgxi]
    by_cases hxi : xi ∈ s
    · rw [Set.indicator_of_mem hxi, norm_smul, norm_mul,
        norm_massGaugeHalfWaveSymbol, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      have h := hgrowth xi hxi
      nlinarith
    · rw [Set.indicator_of_notMem hxi]
      simp only [smul_zero, norm_zero, norm_mul]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hnorm :
      ‖(Real.exp (u * delta) : ℂ) • g‖ ≤
        ‖massGaugeHalfWaveL2 ha hlambda (epsilon * u) f‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    exact ENNReal.toReal_mono (by finiteness) (eLpNorm_mono_ae hpoint)
  simpa [g, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp, abs_of_pos (Real.exp_pos _)] using hnorm

/-- Any nonzero measurable frequency piece with a fixed signed radiation
gap forces the two-sided orbit to be unbounded. -/
theorem massGaugeHalfWaveL2_orbit_unbounded_of_restricted_growth
    {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (s : Set ℝ) (hs : MeasurableSet s)
    (epsilon delta : ℝ) (hdelta : 0 < delta)
    (hg : massGaugeL2Restriction s hs f ≠ 0)
    (hgrowth : ∀ xi ∈ s,
      delta ≤ epsilon * (massGaugeDispersion a lambda xi).im) :
    ∀ C : ℝ, ∃ u : ℝ, C < ‖massGaugeHalfWaveL2 ha hlambda u f‖ := by
  intro C
  have hgnorm : 0 < ‖massGaugeL2Restriction s hs f‖ := norm_pos_iff.mpr hg
  have hlinear : Tendsto (fun u : ℝ => u * delta) atTop atTop :=
    tendsto_id.atTop_mul_const hdelta
  have hexp : Tendsto (fun u : ℝ => Real.exp (u * delta)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlinear
  have hprod : Tendsto
      (fun u : ℝ => Real.exp (u * delta) * ‖massGaugeL2Restriction s hs f‖)
      atTop atTop := hexp.atTop_mul_const hgnorm
  have hev : ∀ᶠ u : ℝ in atTop,
      0 ≤ u ∧ C < Real.exp (u * delta) * ‖massGaugeL2Restriction s hs f‖ :=
    (eventually_ge_atTop 0).and (hprod.eventually (eventually_gt_atTop C))
  obtain ⟨u, hu, hCu⟩ := hev.exists
  refine ⟨epsilon * u, hCu.trans_le ?_⟩
  exact massGaugeHalfWaveL2_apply_norm_ge_restriction
    ha hlambda f s hs epsilon delta u hu hgrowth

/-- Frequencies whose signed radiation exponent is at least `1 / (n + 1)`. -/
def massGaugeRadiationLevelSet (a lambda epsilon : ℝ) (n : ℕ) : Set ℝ :=
  {xi | 1 / (n + 1 : ℝ) ≤
    epsilon * (massGaugeDispersion a lambda xi).im}

/-- Radiation level sets are measurable in the open mass chamber. -/
theorem massGaugeRadiationLevelSet_measurable {a lambda : ℝ}
    (ha : lambda < a) (hlambda : 0 ≤ lambda) (epsilon : ℝ) (n : ℕ) :
    MeasurableSet (massGaugeRadiationLevelSet a lambda epsilon n) := by
  have him : Continuous (fun xi : ℝ => (massGaugeDispersion a lambda xi).im) :=
    Complex.continuous_im.comp (continuous_massGaugeDispersion ha hlambda)
  exact measurableSet_le continuous_const.measurable
    (continuous_const.mul him).measurable

/-- Every nonzero Fourier-side `L2` datum has an unbounded two-sided gauged
massive half-wave orbit.  The proof extracts a positive-measure signed
radiation level from the datum's support. -/
theorem massGaugeHalfWaveL2_nonzero_orbit_unbounded
    {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0) :
    ∀ C : ℝ, ∃ u : ℝ, C < ‖massGaugeHalfWaveL2 ha hlambda u f‖ := by
  let supp : Set ℝ := Function.support fun xi => f xi
  have hsupp_ne : volume supp ≠ 0 := by
    intro hsupp
    apply hf
    rw [Lp.eq_zero_iff_ae_eq_zero]
    exact ((volume : Measure ℝ).measure_support_eq_zero_iff).1 hsupp
  have hside : volume (supp ∩ Iio 0) ≠ 0 ∨ volume (supp ∩ Ioi 0) ≠ 0 := by
    by_contra h
    push Not at h
    apply hsupp_ne
    apply measure_mono_null
      (t := (supp ∩ Iio 0) ∪ ({0} : Set ℝ) ∪ (supp ∩ Ioi 0))
    · intro xi hxi
      rcases lt_trichotomy xi 0 with hneg | hzero | hpos
      · exact Or.inl (Or.inl ⟨hxi, hneg⟩)
      · exact Or.inl (Or.inr (by simp [hzero]))
      · exact Or.inr ⟨hxi, hpos⟩
    · exact measure_union_null (measure_union_null h.1 (by simp)) h.2
  rcases hside with hneg | hpos
  · have hcover : supp ∩ Iio 0 ⊆
        ⋃ n : ℕ, supp ∩ massGaugeRadiationLevelSet a lambda 1 n := by
      intro xi hxi
      have him : 0 < (massGaugeDispersion a lambda xi).im :=
        massGaugeDispersion_im_pos_of_neg ha hlambda hxi.2
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt him
      apply Set.mem_iUnion.2
      refine ⟨n, hxi.1, ?_⟩
      dsimp [massGaugeRadiationLevelSet]
      simpa using hn.le
    have hunion : volume
        (⋃ n : ℕ, supp ∩ massGaugeRadiationLevelSet a lambda 1 n) ≠ 0 := by
      intro hz
      exact hneg (measure_mono_null hcover hz)
    obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null
      (μ := (volume : Measure ℝ)) hunion
    let s := massGaugeRadiationLevelSet a lambda 1 n
    have hs : MeasurableSet s :=
      massGaugeRadiationLevelSet_measurable ha hlambda.le 1 n
    have hg : massGaugeL2Restriction s hs f ≠ 0 := by
      apply massGaugeL2Restriction_ne_zero_of_measure_support_inter_ne_zero
      simpa [supp, s] using hn.ne'
    apply massGaugeHalfWaveL2_orbit_unbounded_of_restricted_growth
      ha hlambda f s hs 1 (1 / (n + 1 : ℝ))
      (one_div_pos.mpr (by positivity)) hg
    intro xi hxi
    exact hxi
  · have hcover : supp ∩ Ioi 0 ⊆
        ⋃ n : ℕ, supp ∩ massGaugeRadiationLevelSet a lambda (-1) n := by
      intro xi hxi
      have him : (massGaugeDispersion a lambda xi).im < 0 :=
        massGaugeDispersion_im_neg_of_pos ha hlambda hxi.2
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr him)
      apply Set.mem_iUnion.2
      refine ⟨n, hxi.1, ?_⟩
      dsimp [massGaugeRadiationLevelSet]
      nlinarith
    have hunion : volume
        (⋃ n : ℕ, supp ∩ massGaugeRadiationLevelSet a lambda (-1) n) ≠ 0 := by
      intro hz
      exact hpos (measure_mono_null hcover hz)
    obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null
      (μ := (volume : Measure ℝ)) hunion
    let s := massGaugeRadiationLevelSet a lambda (-1) n
    have hs : MeasurableSet s :=
      massGaugeRadiationLevelSet_measurable ha hlambda.le (-1) n
    have hg : massGaugeL2Restriction s hs f ≠ 0 := by
      apply massGaugeL2Restriction_ne_zero_of_measure_support_inter_ne_zero
      simpa [supp, s] using hn.ne'
    apply massGaugeHalfWaveL2_orbit_unbounded_of_restricted_growth
      ha hlambda f s hs (-1) (1 / (n + 1 : ℝ))
      (one_div_pos.mpr (by positivity)) hg
    intro xi hxi
    exact hxi

/-- No size functional equivalent to the `L2` norm can be invariant along a
nonzero two-sided gauged half-wave orbit.  In particular, no equivalent
Hilbert norm can unitarize this group. -/
theorem massGaugeHalfWaveL2_no_equivalent_invariant_size
    {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ≠ 0)
    (size : Lp ℂ 2 (volume : Measure ℝ) → ℝ) (c C : ℝ) (hc : 0 < c)
    (hlower : ∀ g, c * ‖g‖ ≤ size g)
    (hupper : ∀ g, size g ≤ C * ‖g‖)
    (hinvariant : ∀ u, size (massGaugeHalfWaveL2 ha hlambda u f) = size f) :
    False := by
  obtain ⟨u, hu⟩ := massGaugeHalfWaveL2_nonzero_orbit_unbounded
    ha hlambda f hf (C * ‖f‖ / c)
  have hscaled : c * ‖massGaugeHalfWaveL2 ha hlambda u f‖ ≤ C * ‖f‖ :=
    (hlower _).trans ((hinvariant u).trans_le (hupper f))
  have hbound : ‖massGaugeHalfWaveL2 ha hlambda u f‖ ≤ C * ‖f‖ / c := by
    exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hscaled)
  exact (not_le_of_gt hu) hbound

end GaloisForLFunctions.HTGeometry
