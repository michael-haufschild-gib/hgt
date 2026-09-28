import GaloisForLFunctions.HTGeometry.PhaseKernelAdmissionGauge
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Spectral contact localization of phase-kernel pencils

Let `μ` be a nonzero finite measure on `ℝ` and `h` an integrable density bounded below, with
`α = ess inf h`.  Rational phase polynomials approximate, uniformly boundedly and in
`L¹((1 + |h|) μ)`, the indicator of every sublevel set `{h < α + δ}`.  Hence:

* `(FKA.15)` the Rayleigh quotients `∫ h |p|² dμ / ∫ |p|² dμ` over the rational phase polynomials
  have greatest lower bound `α`;
* `(FKA.17)` normalized minimizing sequences concentrate on the contact set: for every `δ > 0`,
  `∫_{h ≥ α + δ} |p_n|² dμ → 0`;
* the admission gauge of `η = h μ` is `(-α)_+`, in particular `-α` when `α < 0`.

The rational phase polynomials are dense in `L²(ρ)` for every finite measure `ρ`.

For a finite measure carried by `[0, ∞)` with support unbounded above and the reflected scores
`h_a = e^{2ax} - 1`, the two reflection gauges are `(0,1)`, `(0,0)`, `(1,0)` for `a > 0`, `a = 0`,
`a < 0` (Corollary 8.1): the reflection tension is `1_{a ≠ 0}`, and for `a > 0` the critical
pencil `e^{-2ax}` has ground energy zero, no contact point, and every normalized minimizing
sequence escapes to `+∞`.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PhaseKernel

/-! ## Essential infimum -/

section EssInf

variable {μ : Measure ℝ} [IsFiniteMeasure μ] [NeZero μ] {h : ℝ → ℝ}

theorem measureReal_univ_pos : 0 < μ.real univ := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr (NeZero.ne μ)) (measure_ne_top _ _)

theorem isCoboundedUnder_ge_of_integrable (hh : Integrable h μ) :
    IsCoboundedUnder (· ≥ ·) (ae μ) h := by
  refine ⟨(∫ x, h x ∂μ) / μ.real univ, fun a ha => ?_⟩
  have hae : ∀ᵐ x ∂μ, a ≤ h x := Filter.eventually_map.mp ha
  have hle : a * μ.real univ ≤ ∫ x, h x ∂μ := by
    calc a * μ.real univ = ∫ _, a ∂μ := by rw [integral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x, h x ∂μ := integral_mono_ae (integrable_const a) hh hae
  exact (le_div_iff₀ measureReal_univ_pos).mpr hle

omit [IsFiniteMeasure μ] [NeZero μ] in
theorem isBoundedUnder_ge_of_ae {b : ℝ} (hb : ∀ᵐ x ∂μ, b ≤ h x) :
    IsBoundedUnder (· ≥ ·) (ae μ) h :=
  ⟨b, Filter.eventually_map.mpr hb⟩

omit [IsFiniteMeasure μ] [NeZero μ] in
theorem ae_essInf_le_of_ae {b : ℝ} (hb : ∀ᵐ x ∂μ, b ≤ h x) : ∀ᵐ x ∂μ, essInf h μ ≤ h x :=
  ae_essInf_le (isBoundedUnder_ge_of_ae hb)

/-- Every sublevel set strictly above the essential infimum has positive measure. -/
theorem measureReal_lt_essInf_add_pos (hh : Integrable h μ) {δ : ℝ} (hδ : 0 < δ) :
    0 < μ.real {x | h x < essInf h μ + δ} := by
  rw [measureReal_def]
  refine ENNReal.toReal_pos (fun h0 => ?_) (measure_ne_top _ _)
  have hae : ∀ᵐ x ∂μ, essInf h μ + δ ≤ h x := by
    rw [ae_iff]
    simpa only [not_le] using h0
  have := le_essInf_of_ae_le (essInf h μ + δ) hae (isCoboundedUnder_ge_of_integrable hh)
  linarith

theorem le_essInf_iff_ae (hh : Integrable h μ) {b c : ℝ} (hb : ∀ᵐ x ∂μ, b ≤ h x) :
    c ≤ essInf h μ ↔ ∀ᵐ x ∂μ, c ≤ h x :=
  ⟨fun hc => (ae_essInf_le_of_ae hb).mono fun _ hx => hc.trans hx,
    fun hc => le_essInf_of_ae_le c hc (isCoboundedUnder_ge_of_integrable hh)⟩

end EssInf

/-! ## Rayleigh quotients of rational phase polynomials -/

/-- The weighted packet energy `∫ h |p|² dμ`. -/
def weightedEnergy (μ : Measure ℝ) (h : ℝ → ℝ) {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) : ℝ :=
  ∫ x, h x * ‖phasePacket t z x‖ ^ 2 ∂μ

/-- `(FKA.15)`  The Rayleigh quotients `∫ h|p|² dμ / ∫ |p|² dμ` of the nonzero rational phase
polynomials `p ∈ ⋃_N span {e^{-i q_0 x}, …, e^{-i q_N x}}`. -/
def rationalRayleighSet (μ : Measure ℝ) (h : ℝ → ℝ) : Set ℝ :=
  {r | ∃ (N : ℕ) (z : Fin (N + 1) → ℂ), 0 < packetEnergy μ (fun j => ratPhase j) z ∧
    weightedEnergy μ h (fun j => ratPhase j) z / packetEnergy μ (fun j => ratPhase j) z = r}

theorem integrable_weightedEnergy {μ : Measure ℝ} [IsFiniteMeasure μ] {h : ℝ → ℝ}
    (hh : Integrable h μ) {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) :
    Integrable (fun x => h x * ‖phasePacket t z x‖ ^ 2) μ := by
  refine (hh.norm.mul_const ((∑ j, ‖z j‖) ^ 2)).mono'
    (hh.aestronglyMeasurable.mul ((continuous_phasePacket t z).norm.pow 2).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_pow, norm_norm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
    (norm_phasePacket_le t z x) 2) (norm_nonneg _)

theorem weightedEnergy_congr {μ : Measure ℝ} {h h' : ℝ → ℝ} (hae : h =ᵐ[μ] h') {m : ℕ}
    (t : Fin m → ℝ) (z : Fin m → ℂ) : weightedEnergy μ h t z = weightedEnergy μ h' t z :=
  integral_congr_ae (hae.mono fun _ hx => by simp only [hx])

section Rayleigh

variable {μ : Measure ℝ} [IsFiniteMeasure μ] [NeZero μ] {h : ℝ → ℝ}

omit [NeZero μ] in
/-- The Rayleigh lower bound `∫ h|p|² ≥ α ∫ |p|²`. -/
theorem essInf_mul_packetEnergy_le (hh : Integrable h μ) {b : ℝ} (hb : ∀ᵐ x ∂μ, b ≤ h x)
    {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) :
    essInf h μ * packetEnergy μ t z ≤ weightedEnergy μ h t z := by
  unfold packetEnergy weightedEnergy
  rw [← integral_const_mul]
  exact integral_mono_ae ((integrable_normSq_phasePacket μ t z).const_mul _)
    (integrable_weightedEnergy hh t z) ((ae_essInf_le_of_ae hb).mono fun x hx =>
      mul_le_mul_of_nonneg_right hx (by positivity))

theorem abs_clamp_sub_le (u v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    |max 0 (min 1 u) - v| ≤ |u - v| := by
  rcases le_total u 0 with hu | hu
  · rw [min_eq_right (by linarith), max_eq_left hu, abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith
  · rcases le_total u 1 with hu1 | hu1
    · rw [min_eq_right hu1, max_eq_right hu]
    · rw [min_eq_left hu1, max_eq_right zero_le_one, abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      linarith

omit [NeZero μ] in
/-- **Indicator approximation.**  For measurable `h`, rational phase polynomials bounded by `2`
approximate the indicator of a measurable set in `L¹((1 + |h|) μ)`. -/
theorem exists_ratPacket_indicator_approx (hh : Integrable h μ) (hhm : Measurable h)
    {A : Set ℝ} (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (z : Fin (N + 1) → ℂ),
      (∀ x, ‖phasePacket (fun j : Fin (N + 1) => ratPhase j) z x‖ ≤ 2) ∧
      ∫ x, (1 + |h x|) * ‖phasePacket (fun j : Fin (N + 1) => ratPhase j) z x -
        ((A.indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ)‖ ∂μ ≤ ε := by
  set w : ℝ → ℝ≥0 := fun x => (1 + |h x|).toNNReal with hwdef
  have hwm : Measurable w :=
    (measurable_const.add (continuous_abs.measurable.comp hhm)).real_toNNReal
  set ρ : Measure ℝ := μ.withDensity fun x => (w x : ℝ≥0∞) with hρdef
  haveI : IsFiniteMeasure ρ :=
    isFiniteMeasure_withDensity_ofReal ((integrable_const 1).add hh.abs).hasFiniteIntegral
  have hρint : ∀ g : ℝ → ℝ, ∫ x, g x ∂ρ = ∫ x, (1 + |h x|) * g x ∂μ := fun g => by
    rw [hρdef, integral_withDensity_eq_integral_smul₀ hwm.aemeasurable]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hwdef, NNReal.smul_def, Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ 1 + |h x|),
      smul_eq_mul]
  set ind : ℝ → ℝ := A.indicator fun _ => (1 : ℝ) with hind
  have hind01 : ∀ x, 0 ≤ ind x ∧ ind x ≤ 1 := fun x => by
    by_cases hx : x ∈ A
    · simp [hind, Set.indicator_of_mem hx]
    · simp [hind, Set.indicator_of_notMem hx]
  have hindi : Integrable ind ρ := (integrable_const (1 : ℝ)).indicator hA
  obtain ⟨g, hgs, hgapp, hgc, hgi⟩ := hindi.exists_hasCompactSupport_integral_sub_le
    (half_pos hε)
  set g' : ℝ → ℝ := fun x => max 0 (min 1 (g x)) with hg'def
  have hg'c : Continuous g' := continuous_const.max (continuous_const.min hgc)
  have hg's : HasCompactSupport g' :=
    hgs.comp_left (g := fun u : ℝ => max 0 (min 1 u)) (by simp)
  have hg'b : ∀ x, ‖((g' x : ℝ) : ℂ)‖ ≤ 1 := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le zero_le_one (min_le_left _ _)
  have hclamp : ∀ x, ‖ind x - g' x‖ ≤ ‖ind x - g x‖ := fun x => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm, abs_sub_comm (ind x)]
    exact abs_clamp_sub_le _ _ (hind01 x).1 (hind01 x).2
  obtain ⟨m, t, z, ht, hbd, happ⟩ := exists_rationalPacket_approx ρ
    (Complex.continuous_ofReal.comp hg'c)
    (hg's.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero) hg'b (half_pos hε)
  obtain ⟨N, w', hw'⟩ := exists_ratPhase_packet ht z
  refine ⟨N, w', fun x => by rw [hw']; exact (hbd x).trans (by norm_num), ?_⟩
  have hi1 : Integrable (fun x => ‖phasePacket t z x - ((g' x : ℝ) : ℂ)‖) ρ :=
    integrable_of_continuous_bounded ((continuous_phasePacket t z).sub
      (Complex.continuous_ofReal.comp hg'c)).norm (C := 1 + 1 + 1) fun x => by
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (add_le_add (hbd x) (hg'b x))
  have hi2 : Integrable (fun x => ‖ind x - g x‖) ρ := (hindi.sub hgi).norm
  have hbound : ∫ x, ‖phasePacket t z x - ((ind x : ℝ) : ℂ)‖ ∂ρ ≤ ε := by
    calc ∫ x, ‖phasePacket t z x - ((ind x : ℝ) : ℂ)‖ ∂ρ
        ≤ ∫ x, (‖phasePacket t z x - ((g' x : ℝ) : ℂ)‖ + ‖ind x - g x‖) ∂ρ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            (hi1.add hi2) (Eventually.of_forall fun x => ?_)
          calc ‖phasePacket t z x - ((ind x : ℝ) : ℂ)‖
              ≤ ‖phasePacket t z x - ((g' x : ℝ) : ℂ)‖ + ‖((g' x : ℝ) : ℂ) - ((ind x : ℝ) : ℂ)‖ :=
                norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ ≤ ‖phasePacket t z x - ((g' x : ℝ) : ℂ)‖ + ‖ind x - g x‖ := by
                gcongr
                rw [← Complex.ofReal_sub, Complex.norm_real, norm_sub_rev]
                exact hclamp x
      _ = ∫ x, ‖phasePacket t z x - ((g' x : ℝ) : ℂ)‖ ∂ρ + ∫ x, ‖ind x - g x‖ ∂ρ :=
          integral_add hi1 hi2
      _ ≤ ε / 2 + ε / 2 := add_le_add happ.le hgapp
      _ = ε := by ring
  rw [hρint] at hbound
  rw [hw']
  exact hbound

theorem abs_normSq_sub_le {w : ℂ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hr : r ^ 2 = r)
    (hw : ‖w‖ ≤ 2) : |‖w‖ ^ 2 - r| ≤ 3 * ‖w - (r : ℂ)‖ := by
  have hn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have h1 : |‖w‖ - r| ≤ ‖w - (r : ℂ)‖ := by
    have := abs_norm_sub_norm_le w (r : ℂ)
    rwa [hn] at this
  have h2 : ‖w‖ ^ 2 - r = (‖w‖ - r) * (‖w‖ + r) := by
    rw [show (‖w‖ - r) * (‖w‖ + r) = ‖w‖ ^ 2 - r ^ 2 by ring, hr]
  rw [h2, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖w‖ + r)]
  calc |‖w‖ - r| * (‖w‖ + r) ≤ ‖w - (r : ℂ)‖ * 3 :=
        mul_le_mul h1 (by linarith) (by positivity) (norm_nonneg _)
    _ = 3 * ‖w - (r : ℂ)‖ := mul_comm _ _

/-- For measurable `h`: a rational phase polynomial with Rayleigh quotient below `α + δ`. -/
theorem exists_ratPacket_rayleigh_lt_of_measurable (hh : Integrable h μ) (hhm : Measurable h)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (z : Fin (N + 1) → ℂ), 0 < packetEnergy μ (fun j => ratPhase j) z ∧
      weightedEnergy μ h (fun j => ratPhase j) z <
        (essInf h μ + δ) * packetEnergy μ (fun j => ratPhase j) z := by
  set α := essInf h μ with hαdef
  set A : Set ℝ := {x | h x < α + δ / 2} with hAdef
  have hA : MeasurableSet A := measurableSet_lt hhm measurable_const
  have hμA : 0 < μ.real A := measureReal_lt_essInf_add_pos hh (half_pos hδ)
  set K : ℝ := 1 + |α + δ| with hKdef
  have hK : 0 < K := by positivity
  set ε : ℝ := min (μ.real A / 12) (δ / 2 * μ.real A / (12 * K)) with hεdef
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨N, z, hbd, happ⟩ := exists_ratPacket_indicator_approx hh hhm hA hε
  set t : Fin (N + 1) → ℝ := fun j => ratPhase j
  set ind : ℝ → ℝ := A.indicator fun _ => (1 : ℝ) with hind
  have hind01 : ∀ x, 0 ≤ ind x ∧ ind x ≤ 1 ∧ ind x ^ 2 = ind x := fun x => by
    by_cases hx : x ∈ A
    · simp [hind, Set.indicator_of_mem hx]
    · simp [hind, Set.indicator_of_notMem hx]
  have hindm : Measurable ind := measurable_const.indicator hA
  set e : ℝ → ℝ := fun x => ‖phasePacket t z x - ((ind x : ℝ) : ℂ)‖ with hedef
  have hem : AEStronglyMeasurable e μ :=
    ((continuous_phasePacket t z).aestronglyMeasurable.sub
      (Complex.continuous_ofReal.measurable.comp hindm).aestronglyMeasurable).norm
  have he3 : ∀ x, e x ≤ 3 := fun x =>
    (norm_sub_le (phasePacket t z x) ((ind x : ℝ) : ℂ)).trans (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hind01 x).1]
      linarith [hbd x, (hind01 x).2.1])
  have he0 : ∀ x, 0 ≤ e x := fun x => norm_nonneg _
  have hwei : Integrable (fun x => (1 + |h x|) * e x) μ :=
    (((integrable_const (1 : ℝ)).add hh.abs).mul_const 3).mono'
      (((aestronglyMeasurable_const.add hh.aestronglyMeasurable.norm)).mul hem)
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          abs_of_nonneg (norm_nonneg _)]
        exact mul_le_mul_of_nonneg_left (he3 x) (by positivity))
  have hpt : ∀ x, |‖phasePacket t z x‖ ^ 2 - ind x| ≤ 3 * e x := fun x =>
    abs_normSq_sub_le (hind01 x).1 (hind01 x).2.1 (hind01 x).2.2 (hbd x)
  have hindi : Integrable ind μ := (integrable_const (1 : ℝ)).indicator hA
  have hmA : ∫ x, ind x ∂μ = μ.real A := by
    rw [hind, integral_indicator_const _ hA, smul_eq_mul, mul_one]
  have hE : |packetEnergy μ t z - μ.real A| ≤ 3 * ε := by
    rw [packetEnergy, ← hmA, ← integral_sub (integrable_normSq_phasePacket μ t z) hindi]
    calc |∫ x, (‖phasePacket t z x‖ ^ 2 - ind x) ∂μ|
        ≤ ∫ x, |‖phasePacket t z x‖ ^ 2 - ind x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, 3 * ((1 + |h x|) * e x) ∂μ := by
          refine integral_mono ((integrable_normSq_phasePacket μ t z).sub hindi).abs
            (hwei.const_mul 3) fun x => (hpt x).trans ?_
          have : e x ≤ (1 + |h x|) * e x :=
            le_mul_of_one_le_left (he0 x) (by linarith [abs_nonneg (h x)])
          linarith
      _ ≤ 3 * ε := by rw [integral_const_mul]; linarith
  have hhind : Integrable (fun x => h x * ind x) μ := by
    have : (fun x => h x * ind x) = A.indicator h := by
      funext x
      by_cases hx : x ∈ A
      · simp [hind, Set.indicator_of_mem hx]
      · simp [hind, Set.indicator_of_notMem hx]
    rw [this]
    exact hh.indicator hA
  have hW : |weightedEnergy μ h t z - ∫ x, h x * ind x ∂μ| ≤ 3 * ε := by
    rw [weightedEnergy, ← integral_sub (integrable_weightedEnergy hh t z) hhind]
    calc |∫ x, (h x * ‖phasePacket t z x‖ ^ 2 - h x * ind x) ∂μ|
        ≤ ∫ x, |h x * ‖phasePacket t z x‖ ^ 2 - h x * ind x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, 3 * ((1 + |h x|) * e x) ∂μ := by
          refine integral_mono ((integrable_weightedEnergy hh t z).sub hhind).abs
            (hwei.const_mul 3) fun x => ?_
          rw [← mul_sub, abs_mul]
          calc |h x| * |‖phasePacket t z x‖ ^ 2 - ind x| ≤ |h x| * (3 * e x) :=
                mul_le_mul_of_nonneg_left (hpt x) (abs_nonneg _)
            _ ≤ 3 * ((1 + |h x|) * e x) := by nlinarith [he0 x, abs_nonneg (h x)]
      _ ≤ 3 * ε := by rw [integral_const_mul]; linarith
  have hWA : ∫ x, h x * ind x ∂μ ≤ (α + δ / 2) * μ.real A := by
    have heq : (fun x => h x * ind x) = A.indicator h := by
      funext x
      by_cases hx : x ∈ A
      · simp [hind, Set.indicator_of_mem hx]
      · simp [hind, Set.indicator_of_notMem hx]
    rw [heq, integral_indicator hA]
    calc ∫ x in A, h x ∂μ ≤ ∫ x in A, (α + δ / 2) ∂μ :=
          setIntegral_mono_on hh.integrableOn (integrableOn_const (measure_ne_top _ _)) hA
            fun x hx => le_of_lt hx
      _ = (α + δ / 2) * μ.real A := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hε1 : ε ≤ μ.real A / 12 := min_le_left _ _
  have hε2 : ε ≤ δ / 2 * μ.real A / (12 * K) := min_le_right _ _
  have hε2' : 12 * K * ε ≤ δ / 2 * μ.real A := by
    rw [le_div_iff₀ (by positivity)] at hε2
    linarith
  rw [abs_le] at hE hW
  refine ⟨N, z, by linarith, ?_⟩
  have hkey : -(|α + δ| * |packetEnergy μ t z - μ.real A|) ≤
      (α + δ) * (packetEnergy μ t z - μ.real A) := by
    rw [← abs_mul]
    exact neg_abs_le _
  have habs : |packetEnergy μ t z - μ.real A| ≤ 3 * ε := abs_le.mpr ⟨hE.1, hE.2⟩
  have hprod : |α + δ| * |packetEnergy μ t z - μ.real A| ≤ |α + δ| * (3 * ε) :=
    mul_le_mul_of_nonneg_left habs (abs_nonneg _)
  have hKε : 3 * ε * K = 3 * ε + |α + δ| * (3 * ε) := by rw [hKdef]; ring
  nlinarith [hW.2, hWA, hkey, hprod, hKε, hε2', hμA, hε]

/-- For every `δ > 0` some rational phase polynomial has Rayleigh quotient below `α + δ`. -/
theorem exists_ratPacket_rayleigh_lt (hh : Integrable h μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (z : Fin (N + 1) → ℂ), 0 < packetEnergy μ (fun j => ratPhase j) z ∧
      weightedEnergy μ h (fun j => ratPhase j) z <
        (essInf h μ + δ) * packetEnergy μ (fun j => ratPhase j) z := by
  set hm := hh.aestronglyMeasurable.mk h
  have hae : h =ᵐ[μ] hm := hh.aestronglyMeasurable.ae_eq_mk
  have hmi : Integrable hm μ := hh.congr hae
  obtain ⟨N, z, hE, hW⟩ := exists_ratPacket_rayleigh_lt_of_measurable hmi
    hh.aestronglyMeasurable.stronglyMeasurable_mk.measurable hδ
  refine ⟨N, z, hE, ?_⟩
  rwa [weightedEnergy_congr hae, essInf_congr_ae hae]

/-- `(FKA.15)`  **Ground energy.**  The Rayleigh quotients of the nonzero rational phase
polynomials have greatest lower bound `ess inf h`. -/
theorem isGLB_rationalRayleighSet (hh : Integrable h μ) {b : ℝ} (hb : ∀ᵐ x ∂μ, b ≤ h x) :
    IsGLB (rationalRayleighSet μ h) (essInf h μ) := by
  refine ⟨?_, fun c hc => ?_⟩
  · rintro r ⟨N, z, hE, rfl⟩
    rw [le_div_iff₀ hE]
    exact essInf_mul_packetEnergy_le hh hb _ z
  · refine le_of_forall_pos_lt_add fun δ hδ => ?_
    obtain ⟨N, z, hE, hW⟩ := exists_ratPacket_rayleigh_lt hh hδ
    exact lt_of_le_of_lt (hc ⟨N, z, hE, rfl⟩) ((div_lt_iff₀ hE).mpr hW)

omit [IsFiniteMeasure μ] [NeZero μ] in
/-- `(FKA.17)`  **Contact localization.**  Along a normalized minimizing sequence, the mass on
`{h ≥ α + δ}` tends to zero. -/
theorem tendsto_contactMass_zero (hh : Integrable h μ) {b : ℝ} (hb : ∀ᵐ x ∂μ, b ≤ h x)
    {p : ℕ → ℝ → ℂ} (hp : ∀ n, Integrable (fun x => ‖p n x‖ ^ 2) μ)
    (hhp : ∀ n, Integrable (fun x => h x * ‖p n x‖ ^ 2) μ)
    (hnorm : ∀ n, ∫ x, ‖p n x‖ ^ 2 ∂μ = 1)
    (hmin : Tendsto (fun n => ∫ x, h x * ‖p n x‖ ^ 2 ∂μ) atTop (𝓝 (essInf h μ)))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => ∫ x in {x | essInf h μ + δ ≤ h x}, ‖p n x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  set α := essInf h μ
  set hm := hh.aestronglyMeasurable.mk h
  have hae : h =ᵐ[μ] hm := hh.aestronglyMeasurable.ae_eq_mk
  have hmm : Measurable hm := hh.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  set S : Set ℝ := {x | α + δ ≤ hm x}
  have hS : MeasurableSet S := measurableSet_le measurable_const hmm
  have hSeq : {x | α + δ ≤ h x} =ᵐ[μ] S :=
    hae.mono fun x hx => by
      show (α + δ ≤ h x) = (α + δ ≤ hm x)
      rw [hx]
  have hexcess : Tendsto (fun n => ∫ x, (h x - α) * ‖p n x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have h1 : ∀ n, ∫ x, (h x - α) * ‖p n x‖ ^ 2 ∂μ = ∫ x, h x * ‖p n x‖ ^ 2 ∂μ - α := by
      intro n
      simp_rw [sub_mul]
      rw [integral_sub (hhp n) ((hp n).const_mul α), integral_const_mul, hnorm n, mul_one]
    simp_rw [h1]
    simpa using hmin.sub_const α
  have hup := hexcess.div_const δ
  rw [zero_div] at hup
  refine squeeze_zero (fun n => setIntegral_nonneg_of_ae (Eventually.of_forall fun _ =>
    by positivity)) (fun n => ?_) hup
  rw [setIntegral_congr_set hSeq, le_div_iff₀ hδ]
  have hnn : 0 ≤ᵐ[μ] fun x => (h x - α) * ‖p n x‖ ^ 2 :=
    (ae_essInf_le_of_ae hb).mono fun x hx => mul_nonneg (by linarith) (by positivity)
  calc (∫ x in S, ‖p n x‖ ^ 2 ∂μ) * δ = ∫ x in S, δ * ‖p n x‖ ^ 2 ∂μ := by
        rw [integral_const_mul, mul_comm]
    _ ≤ ∫ x in S, (h x - α) * ‖p n x‖ ^ 2 ∂μ := by
        refine setIntegral_mono_ae_restrict ((hp n).const_mul δ).integrableOn
          (((hhp n).sub ((hp n).const_mul α)).integrableOn.congr_fun
            (fun x _ => by simp only [Pi.sub_apply, sub_mul]) hS) ?_
        rw [EventuallyLE, ae_restrict_iff' hS]
        filter_upwards [hae] with x hx hxS
        have hxS' : α + δ ≤ h x := by rw [hx]; exact hxS
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ ≤ ∫ x, (h x - α) * ‖p n x‖ ^ 2 ∂μ :=
        setIntegral_le_integral ((hhp n).sub ((hp n).const_mul α) |>.congr
          (Eventually.of_forall fun x => by simp only [Pi.sub_apply, sub_mul])) hnn

/-! ## The gauge of a density intervention -/

omit [NeZero μ] in
theorem nonneg_withDensityᵥ_add_iff (hh : Integrable h μ) (c : ℝ) :
    0 ≤ μ.withDensityᵥ h + c • μ.toSignedMeasure ↔ ∀ᵐ x ∂μ, -c ≤ h x := by
  have happ : ∀ s, MeasurableSet s →
      (μ.withDensityᵥ h + c • μ.toSignedMeasure) s = ∫ x in s, (h x + c) ∂μ := by
    intro s hs
    rw [add_apply, withDensityᵥ_apply hh hs, smul_apply,
      Measure.toSignedMeasure_apply_measurable hs,
      smul_eq_mul, integral_add hh.integrableOn (integrableOn_const (measure_ne_top _ _)),
      setIntegral_const, smul_eq_mul, mul_comm]
  rw [VectorMeasure.le_iff]
  constructor
  · intro H
    have hnn : 0 ≤ᵐ[μ] fun x => h x + c :=
      ae_nonneg_of_forall_setIntegral_nonneg (hh.add (integrable_const c)) fun s hs _ => by
        have := H s hs
        rwa [zero_apply, happ s hs] at this
    exact hnn.mono fun x hx => by simp only [Pi.zero_apply] at hx; linarith
  · intro H s hs
    rw [zero_apply, happ s hs]
    exact setIntegral_nonneg_of_ae (H.mono fun x hx => by simp only [Pi.zero_apply]; linarith)

/-- For `η = h μ` the admission gauge is `(-ess inf h)_+`; in particular it is `-α` when
`α < 0`. -/
theorem admissionGauge_withDensityᵥ (hh : Integrable h μ) {b : ℝ} (hb : ∀ᵐ x ∂μ, b ≤ h x) :
    admissionGauge μ (μ.withDensityᵥ h) = ENNReal.ofReal (-essInf h μ) := by
  have hfeas : ∀ c : ℝ≥0, 0 ≤ μ.withDensityᵥ h + (c : ℝ) • μ.toSignedMeasure ↔
      ENNReal.ofReal (-essInf h μ) ≤ c := by
    intro c
    rw [nonneg_withDensityᵥ_add_iff hh, ← le_essInf_iff_ae hh hb,
      ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal]
    constructor <;> intro h <;> linarith
  unfold admissionGauge
  simp_rw [hfeas]
  exact iInf_nnreal_ge _

theorem toReal_admissionGauge_withDensityᵥ_of_neg (hh : Integrable h μ) {b : ℝ}
    (hb : ∀ᵐ x ∂μ, b ≤ h x) (hα : essInf h μ < 0) :
    (admissionGauge μ (μ.withDensityᵥ h)).toReal = -essInf h μ := by
  rw [admissionGauge_withDensityᵥ hh hb, ENNReal.toReal_ofReal (by linarith)]

end Rayleigh

/-! ## Density of rational phase polynomials in `L²` -/

/-- The rational phase polynomials are dense in `L²(ρ)` for every finite measure `ρ`; in
particular in `L²((1 + |h|) μ)`. -/
theorem exists_ratPacket_eLpNorm_lt (ρ : Measure ℝ) [IsFiniteMeasure ρ] {f : ℝ → ℂ}
    (hf : MemLp f 2 ρ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (N : ℕ) (z : Fin (N + 1) → ℂ),
      eLpNorm (fun x => phasePacket (fun j : Fin (N + 1) => ratPhase j) z x - f x) 2 ρ < ε := by
  obtain ⟨r, hr0, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (pos_iff_ne_zero.mpr hε)
  have hr : (0 : ℝ) < r := by exact_mod_cast ENNReal.coe_pos.mp hr0
  set s : ℝ := r / 2 with hsdef
  have hs : 0 < s := by positivity
  obtain ⟨g, hgs, hgapp, hgc, -⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (ε := ENNReal.ofReal s) (ENNReal.ofReal_pos.mpr hs).ne'
  obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support hgs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set B : ℝ := M + 1 + M with hBdef
  have hB : 0 < B := by positivity
  obtain ⟨m, t, z, ht, hbd, happ⟩ := exists_rationalPacket_approx ρ hgc hgs hM
    (ε := s ^ 2 / (B + 1)) (by positivity)
  obtain ⟨N, w, hw⟩ := exists_ratPhase_packet ht z
  refine ⟨N, w, ?_⟩
  rw [hw]
  set u : ℝ → ℂ := fun x => phasePacket t z x - g x with hudef
  have hub : ∀ x, ‖u x‖ ≤ B := fun x =>
    (norm_sub_le _ _).trans (add_le_add (hbd x) (hM x))
  have huc : Continuous u := (continuous_phasePacket t z).sub hgc
  have huL2 : MemLp u 2 ρ :=
    MemLp.of_bound huc.aestronglyMeasurable B (Eventually.of_forall hub)
  have huint : Integrable (fun x => ‖u x‖) ρ := integrable_of_continuous_bounded huc.norm
    (C := B) fun x => by rw [norm_norm]; exact hub x
  have hsq : ∫ x, ‖u x‖ ^ (2 : ℝ) ∂ρ < s ^ 2 := by
    have hpt : ∀ x, ‖u x‖ ^ (2 : ℝ) ≤ B * ‖u x‖ := fun x => by
      rw [Real.rpow_two, sq]
      exact mul_le_mul_of_nonneg_right (hub x) (norm_nonneg _)
    calc ∫ x, ‖u x‖ ^ (2 : ℝ) ∂ρ ≤ ∫ x, B * ‖u x‖ ∂ρ :=
          integral_mono (integrable_of_continuous_bounded (huc.norm.rpow_const fun _ =>
            Or.inr zero_le_two) (C := B ^ 2) fun x => by
              rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_two]
              exact pow_le_pow_left₀ (norm_nonneg _) (hub x) 2)
            (huint.const_mul B) hpt
      _ = B * ∫ x, ‖u x‖ ∂ρ := integral_const_mul _ _
      _ ≤ B * (s ^ 2 / (B + 1)) := mul_le_mul_of_nonneg_left happ.le hB.le
      _ < s ^ 2 := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [sq_pos_of_pos hs]
  have hu : eLpNorm u 2 ρ < ENNReal.ofReal s := by
    rw [huL2.eLpNorm_eq_integral_rpow_norm two_ne_zero (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    refine (ENNReal.ofReal_lt_ofReal_iff hs).mpr ?_
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [h2, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    exact (Real.sqrt_lt' hs).mpr hsq
  have hsplit : (fun x => phasePacket t z x - f x) = u + fun x => g x - f x := by
    funext x
    simp only [hudef, Pi.add_apply]
    ring
  have hgf : eLpNorm (fun x => g x - f x) 2 ρ ≤ ENNReal.ofReal s := by
    rw [show (fun x => g x - f x) = g - f from rfl, eLpNorm_sub_comm]
    exact hgapp
  rw [hsplit]
  calc eLpNorm (u + fun x => g x - f x) 2 ρ
      ≤ eLpNorm u 2 ρ + eLpNorm (fun x => g x - f x) 2 ρ :=
        eLpNorm_add_le huc.aestronglyMeasurable
          (hgc.aestronglyMeasurable.sub hf.1) one_le_two
    _ < ENNReal.ofReal s + ENNReal.ofReal s :=
        ENNReal.add_lt_add_of_lt_of_le (hgf.trans_lt ENNReal.ofReal_lt_top).ne hu hgf
    _ = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_add hs.le hs.le, hsdef, add_halves]
    _ < ε := by rwa [ENNReal.ofReal_coe_nnreal]

/-! ## Packet scaling -/

theorem phasePacket_smul {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) (c : ℂ) (x : ℝ) :
    phasePacket t (c • z) x = c * phasePacket t z x := by
  simp only [phasePacket, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem packetEnergy_smul (ν : Measure ℝ) {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℂ) (c : ℂ) :
    packetEnergy ν t (c • z) = ‖c‖ ^ 2 * packetEnergy ν t z := by
  simp only [packetEnergy, phasePacket_smul, norm_mul, mul_pow]
  exact integral_const_mul _ _

theorem weightedEnergy_smul (ν : Measure ℝ) (h : ℝ → ℝ) {m : ℕ} (t : Fin m → ℝ)
    (z : Fin m → ℂ) (c : ℂ) :
    weightedEnergy ν h t (c • z) = ‖c‖ ^ 2 * weightedEnergy ν h t z := by
  simp only [weightedEnergy, phasePacket_smul, norm_mul, mul_pow]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

/-! ## Reflection tension -/

/-- `(FKA.19)`  The reflected exponential score `h_a(x) = e^{2ax} - 1`. -/
def reflectedScore (a x : ℝ) : ℝ := Real.exp (2 * a * x) - 1

theorem continuous_reflectedScore (a : ℝ) : Continuous (reflectedScore a) := by
  unfold reflectedScore
  fun_prop

/-- `(FKA.22)`  The critical reflected pencil has density `h_{-a} + 1 = e^{-2ax}`. -/
theorem reflectedScore_neg_add_one (a x : ℝ) :
    reflectedScore (-a) x + 1 = Real.exp (-2 * a * x) := by
  simp only [reflectedScore, neg_mul, mul_neg, sub_add_cancel]

section Reflection

variable {μ : Measure ℝ} [IsFiniteMeasure μ] [NeZero μ]

omit [IsFiniteMeasure μ] [NeZero μ] in
theorem ae_nonneg_of_measure_Iio (hsupp : μ (Iio 0) = 0) : ∀ᵐ x ∂μ, 0 ≤ x := by
  rw [ae_iff]
  simp only [not_le]
  exact hsupp

omit [NeZero μ] in
theorem integrable_reflectedScore (hsupp : μ (Iio 0) = 0) {a s : ℝ}
    (hexp : Integrable (fun x => Real.exp (2 * |a| * x)) μ) (hs : |s| ≤ |a|) :
    Integrable (reflectedScore s) μ := by
  refine (hexp.add (integrable_const 1)).mono'
    (continuous_reflectedScore s).aestronglyMeasurable
    ((ae_nonneg_of_measure_Iio hsupp).mono fun x hx => ?_)
  have he : Real.exp (2 * s * x) ≤ Real.exp (2 * |a| * x) :=
    Real.exp_le_exp.mpr (by nlinarith [le_abs_self s])
  rw [Real.norm_eq_abs, reflectedScore, abs_le]
  simp only [Pi.add_apply]
  constructor <;> nlinarith [Real.exp_pos (2 * s * x), Real.exp_pos (2 * |a| * x)]

/-- Scores that are nonnegative on the support have gauge zero. -/
theorem admissionGauge_reflectedScore_pos (hsupp : μ (Iio 0) = 0) {b : ℝ} (hb : 0 ≤ b)
    (hexp : Integrable (fun x => Real.exp (2 * |b| * x)) μ) :
    admissionGauge μ (μ.withDensityᵥ (reflectedScore b)) = 0 := by
  have hi := integrable_reflectedScore hsupp hexp le_rfl
  have hlow : ∀ᵐ x ∂μ, (-1 : ℝ) ≤ reflectedScore b x :=
    Eventually.of_forall fun x => by
      simp only [reflectedScore]
      linarith [Real.exp_pos (2 * b * x)]
  rw [admissionGauge_withDensityᵥ hi hlow, ENNReal.ofReal_eq_zero, neg_nonpos,
    le_essInf_iff_ae hi hlow]
  filter_upwards [ae_nonneg_of_measure_Iio hsupp] with x hx
  simp only [reflectedScore, sub_nonneg]
  exact Real.one_le_exp (by positivity)

omit [NeZero μ] in
theorem integrable_exp_neg (hsupp : μ (Iio 0) = 0) {b : ℝ} (hb : 0 ≤ b) :
    Integrable (fun x => Real.exp (-2 * b * x)) μ :=
  (integrable_const (1 : ℝ)).mono'
    (by fun_prop : Continuous fun x : ℝ => Real.exp (-2 * b * x)).aestronglyMeasurable
    ((ae_nonneg_of_measure_Iio hsupp).mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith))

omit [IsFiniteMeasure μ] [NeZero μ] in
/-- On a support unbounded above the decaying exponential is not bounded below by any
positive constant. -/
theorem not_ae_le_exp_neg (hunb : ∀ R, 0 < μ (Ioi R)) {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ) :
    ¬ ∀ᵐ x ∂μ, δ ≤ Real.exp (-2 * b * x) := by
  intro hae
  set R := -Real.log δ / (2 * b)
  have hbound : ∀ᵐ x ∂μ, x ≤ R := hae.mono fun x hx => by
    have hlog := (Real.log_le_iff_le_exp hδ).mpr hx
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h0 : μ (Ioi R) = 0 := by
    rw [ae_iff] at hbound
    simp only [not_le] at hbound
    exact hbound
  exact (hunb R).ne' h0

/-- The decaying exponential has essential infimum zero on a support unbounded above. -/
theorem essInf_exp_neg_eq_zero (hsupp : μ (Iio 0) = 0) (hunb : ∀ R, 0 < μ (Ioi R)) {b : ℝ}
    (hb : 0 < b) : essInf (fun x => Real.exp (-2 * b * x)) μ = 0 := by
  have hi := integrable_exp_neg hsupp hb.le
  have hlow : ∀ᵐ x ∂μ, (0 : ℝ) ≤ Real.exp (-2 * b * x) :=
    Eventually.of_forall fun x => (Real.exp_pos _).le
  refine le_antisymm (not_lt.mp fun hlt => not_ae_le_exp_neg hunb hb hlt
    ((le_essInf_iff_ae hi hlow).mp le_rfl)) ((le_essInf_iff_ae hi hlow).mpr hlow)

/-- The reflected score `e^{-2bx} - 1` has essential infimum `-1`. -/
theorem essInf_reflectedScore_neg (hsupp : μ (Iio 0) = 0) (hunb : ∀ R, 0 < μ (Ioi R))
    {b : ℝ} (hb : 0 < b) (hexp : Integrable (fun x => Real.exp (2 * |b| * x)) μ) :
    essInf (reflectedScore (-b)) μ = -1 := by
  have hi := integrable_reflectedScore hsupp hexp (s := -b) (by rw [abs_neg])
  have hlow : ∀ᵐ x ∂μ, (-1 : ℝ) ≤ reflectedScore (-b) x :=
    Eventually.of_forall fun x => by
      simp only [reflectedScore]
      linarith [Real.exp_pos (2 * -b * x)]
  refine le_antisymm (not_lt.mp fun hlt => ?_) ((le_essInf_iff_ae hi hlow).mpr hlow)
  refine not_ae_le_exp_neg hunb hb (δ := essInf (reflectedScore (-b)) μ + 1) (by linarith) ?_
  exact ((le_essInf_iff_ae hi hlow).mp le_rfl).mono fun x hx => by
    simp only [reflectedScore] at hx
    rw [show -2 * b * x = 2 * -b * x by ring]
    linarith

/-- The reflected score `e^{-2bx} - 1` has gauge one. -/
theorem admissionGauge_reflectedScore_neg (hsupp : μ (Iio 0) = 0) (hunb : ∀ R, 0 < μ (Ioi R))
    {b : ℝ} (hb : 0 < b) (hexp : Integrable (fun x => Real.exp (2 * |b| * x)) μ) :
    admissionGauge μ (μ.withDensityᵥ (reflectedScore (-b))) = 1 := by
  have hi := integrable_reflectedScore hsupp hexp (s := -b) (by rw [abs_neg])
  have hlow : ∀ᵐ x ∂μ, (-1 : ℝ) ≤ reflectedScore (-b) x :=
    Eventually.of_forall fun x => by
      simp only [reflectedScore]
      linarith [Real.exp_pos (2 * -b * x)]
  rw [admissionGauge_withDensityᵥ hi hlow, essInf_reflectedScore_neg hsupp hunb hb hexp, neg_neg,
    ENNReal.ofReal_one]

/-- `(FKA.20)`  **Reflection-tension phase transition.**  The gauges of `η_a` and `η_{-a}` are
`(0,1)`, `(0,0)`, `(1,0)` according as `a > 0`, `a = 0`, `a < 0`. -/
theorem reflectionGauge_pair (hsupp : μ (Iio 0) = 0) (hunb : ∀ R, 0 < μ (Ioi R)) {a : ℝ}
    (hexp : Integrable (fun x => Real.exp (2 * |a| * x)) μ) :
    (admissionGauge μ (μ.withDensityᵥ (reflectedScore a)),
        admissionGauge μ (μ.withDensityᵥ (reflectedScore (-a)))) =
      if 0 < a then ((0 : ℝ≥0∞), (1 : ℝ≥0∞)) else if a = 0 then (0, 0) else (1, 0) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [if_neg (by linarith), if_neg ha.ne]
    have hb : 0 < -a := by linarith
    have hexp' : Integrable (fun x => Real.exp (2 * |-a| * x)) μ := by rwa [abs_neg]
    have e1 : reflectedScore a = reflectedScore (-(-a)) := by rw [neg_neg]
    rw [e1, admissionGauge_reflectedScore_neg hsupp hunb hb hexp',
      admissionGauge_reflectedScore_pos hsupp hb.le hexp']
  · subst ha
    rw [if_neg (lt_irrefl 0), if_pos rfl, neg_zero,
      admissionGauge_reflectedScore_pos hsupp le_rfl hexp]
  · rw [if_pos ha, admissionGauge_reflectedScore_pos hsupp ha.le hexp,
      admissionGauge_reflectedScore_neg hsupp hunb ha hexp]

/-- `(FKA.21)`  The reflection tension `Θ_μ(a) = max (κ(η_a), κ(η_{-a}))` is `1_{a ≠ 0}`. -/
theorem reflectionTension_eq (hsupp : μ (Iio 0) = 0) (hunb : ∀ R, 0 < μ (Ioi R)) {a : ℝ}
    (hexp : Integrable (fun x => Real.exp (2 * |a| * x)) μ) :
    max (admissionGauge μ (μ.withDensityᵥ (reflectedScore a)))
        (admissionGauge μ (μ.withDensityᵥ (reflectedScore (-a)))) =
      if a = 0 then 0 else 1 := by
  have h := reflectionGauge_pair hsupp hunb hexp
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [if_neg (by linarith), if_neg ha.ne, Prod.mk.injEq] at h
    rw [h.1, h.2, if_neg ha.ne]
    simp
  · rw [if_neg (by linarith), if_pos ha, Prod.mk.injEq] at h
    rw [h.1, h.2, if_pos ha, max_self]
  · rw [if_pos ha, Prod.mk.injEq] at h
    rw [h.1, h.2, if_neg ha.ne']
    simp

/-- `(FKA.22)`  The critical reflected pencil `e^{-2ax}` has ground energy zero over the rational
phase polynomials. -/
theorem isGLB_criticalRayleigh (hsupp : μ (Iio 0) = 0) (hunb : ∀ R, 0 < μ (Ioi R)) {b : ℝ}
    (hb : 0 < b) : IsGLB (rationalRayleighSet μ fun x => Real.exp (-2 * b * x)) 0 := by
  have h := isGLB_rationalRayleighSet (integrable_exp_neg hsupp hb.le) (b := 0)
    (Eventually.of_forall fun x => (Real.exp_pos _).le)
  rwa [essInf_exp_neg_eq_zero hsupp hunb hb] at h

/-- `(FKA.22)`  The critical pencil has no contact point: its density never attains the ground
energy. -/
theorem criticalDensity_ne_ground (hsupp : μ (Iio 0) = 0) (hunb : ∀ R, 0 < μ (Ioi R)) {b : ℝ}
    (hb : 0 < b) (x : ℝ) :
    Real.exp (-2 * b * x) ≠ essInf (fun y => Real.exp (-2 * b * y)) μ := by
  rw [essInf_exp_neg_eq_zero hsupp hunb hb]
  exact (Real.exp_pos _).ne'

omit [IsFiniteMeasure μ] [NeZero μ] in
/-- `(FKA.23)`  **Escape to `+∞`.**  If the critical energies tend to zero, the mass on every
half-line `(-∞, R]` tends to zero. -/
theorem tendsto_mass_Iic_zero {b : ℝ} (hb : 0 < b) {p : ℕ → ℝ → ℂ}
    (hp : ∀ n, Integrable (fun x => ‖p n x‖ ^ 2) μ)
    (hpw : ∀ n, Integrable (fun x => Real.exp (-2 * b * x) * ‖p n x‖ ^ 2) μ)
    (hmin : Tendsto (fun n => ∫ x, Real.exp (-2 * b * x) * ‖p n x‖ ^ 2 ∂μ) atTop (𝓝 0))
    (R : ℝ) : Tendsto (fun n => ∫ x in Iic R, ‖p n x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hup := hmin.const_mul (Real.exp (2 * b * R))
  rw [mul_zero] at hup
  refine squeeze_zero (fun n => setIntegral_nonneg measurableSet_Iic fun x _ => by positivity)
    (fun n => ?_) hup
  calc ∫ x in Iic R, ‖p n x‖ ^ 2 ∂μ
      ≤ ∫ x in Iic R, Real.exp (2 * b * R) * (Real.exp (-2 * b * x) * ‖p n x‖ ^ 2) ∂μ :=
        setIntegral_mono_on (hp n).integrableOn ((hpw n).const_mul _).integrableOn
          measurableSet_Iic fun x hx => by
            have h1 : 1 ≤ Real.exp (2 * b * R) * Real.exp (-2 * b * x) := by
              rw [← Real.exp_add]
              exact Real.one_le_exp (by rw [mem_Iic] at hx; nlinarith)
            nlinarith [sq_nonneg ‖p n x‖]
    _ = Real.exp (2 * b * R) * ∫ x in Iic R, Real.exp (-2 * b * x) * ‖p n x‖ ^ 2 ∂μ :=
        integral_const_mul _ _
    _ ≤ Real.exp (2 * b * R) * ∫ x, Real.exp (-2 * b * x) * ‖p n x‖ ^ 2 ∂μ :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral (hpw n)
          (Eventually.of_forall fun x => by positivity)) (Real.exp_pos _).le

/-- `(FKA.23)`  A normalized minimizing rational phase sequence of the critical pencil exists, and
every such sequence escapes to `+∞`. -/
theorem exists_escaping_minimizing_sequence (hsupp : μ (Iio 0) = 0)
    (hunb : ∀ R, 0 < μ (Ioi R)) {b : ℝ} (hb : 0 < b) :
    ∃ (N : ℕ → ℕ) (z : ∀ n, Fin (N n + 1) → ℂ),
      (∀ n, packetEnergy μ (fun j => ratPhase j) (z n) = 1) ∧
      Tendsto (fun n => weightedEnergy μ (fun x => Real.exp (-2 * b * x))
        (fun j => ratPhase j) (z n)) atTop (𝓝 0) ∧
      ∀ R, Tendsto (fun n => ∫ x in Iic R,
        ‖phasePacket (fun j : Fin (N n + 1) => ratPhase j) (z n) x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hglb := isGLB_criticalRayleigh hsupp hunb hb
  have hc : ∀ n : ℕ, ∃ c ∈ rationalRayleighSet μ (fun x => Real.exp (-2 * b * x)),
      0 ≤ c ∧ c < 1 / ((n : ℝ) + 1) := fun n => hglb.exists_between (by positivity)
  choose c hcS hc0 hclt using hc
  choose N z hE hW using hcS
  set E := fun n => packetEnergy μ (fun j : Fin (N n + 1) => ratPhase j) (z n) with hEdef
  let w : ∀ n, Fin (N n + 1) → ℂ := fun n => (((Real.sqrt (E n))⁻¹ : ℝ) : ℂ) • z n
  have hsc : ∀ n, ‖(((Real.sqrt (E n))⁻¹ : ℝ) : ℂ)‖ ^ 2 * E n = 1 := fun n => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow,
      Real.sq_sqrt (hE n).le, inv_mul_cancel₀ (hE n).ne']
  have hwE : ∀ n, packetEnergy μ (fun j => ratPhase j) (w n) = 1 := fun n => by
    simp only [w]
    rw [packetEnergy_smul]
    exact hsc n
  have hwW : ∀ n, weightedEnergy μ (fun x => Real.exp (-2 * b * x)) (fun j => ratPhase j) (w n) =
      c n := fun n => by
    simp only [w]
    rw [weightedEnergy_smul, ← hW n, div_eq_inv_mul, eq_inv_of_mul_eq_one_left (hsc n)]
  have hlim : Tendsto (fun n => weightedEnergy μ (fun x => Real.exp (-2 * b * x))
      (fun j => ratPhase j) (w n)) atTop (𝓝 0) := by
    simp_rw [hwW]
    exact squeeze_zero hc0 (fun n => (hclt n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨N, w, hwE, hlim, fun R => ?_⟩
  exact tendsto_mass_Iic_zero hb (fun n => integrable_normSq_phasePacket μ _ _)
    (fun n => integrable_weightedEnergy (integrable_exp_neg hsupp hb.le) _ _) hlim R

end Reflection

end GaloisForLFunctions.HTGeometry.PhaseKernel
