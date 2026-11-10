import GaloisForLFunctions.Bottcher.Montel
import GaloisForLFunctions.HTGeometry.HolomorphicRealTaylor
import GaloisForLFunctions.HTGeometry.TwistedMobiusLambertWittSeries

/-!
# Curvature of holomorphic Euler phases

Uniform bounds on holomorphic unit phases justify termwise differentiation
of the Euler logarithm. Its negative real second derivative is a positive quadratic
sum of phase speeds, with weight `q/(1-q)^2`.

A finite boundary limit forces summability of the boundary weights.
Joint holomorphic parameter jets identify that limit with the actual
second real derivative of the logarithmic modulus.
-/

open Complex Filter Topology Metric
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- Uniformly bounded holomorphic curves through one remain uniformly close to one. -/
theorem exists_uniform_phase_ball {ι : Type*} {u : ι → ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hu : ∀ i, DifferentiableOn ℂ (u i) (ball 0 R))
    (hbd : ∀ i z, z ∈ ball 0 R → ‖u i z‖ ≤ M)
    (hu0 : ∀ i, u i 0 = 1) :
    ∃ δ > 0, δ < R ∧ ∀ i z, z ∈ ball 0 δ → ‖u i z‖ ≤ 3 / 2 := by
  let K := 2 * M / R
  have hK : 0 ≤ K := div_nonneg (mul_nonneg (by norm_num) hM) hR.le
  let δ := min (R / 4) (1 / (4 * (K + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδR : δ < R := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨δ, hδ, hδR, ?_⟩
  intro i z hz
  have hz' : z ∈ ball (0 : ℂ) (R / 2) := by
    apply mem_ball.mpr
    exact (mem_ball.mp hz).trans_le ((min_le_left _ _).trans (by linarith))
  have h := Bottcher.norm_sub_le_of_bounded_on_ball hR (hu i) (hbd i)
    hz' (mem_ball_self (by linarith : 0 < R / 2))
  rw [hu0 i, sub_zero] at h
  have hzn : ‖z‖ ≤ 1 / (4 * (K + 1)) := by
    simpa only [dist_zero_right] using (mem_ball.mp hz).le.trans (min_le_right _ _)
  have hmul : K * ‖z‖ ≤ 1 / 4 := by
    calc K * ‖z‖ ≤ (K + 1) * ‖z‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
         _ ≤ (K + 1) * (1 / (4 * (K + 1))) := mul_le_mul_of_nonneg_left hzn (by positivity)
         _ = 1 / 4 := by field_simp
  have hn := norm_add_le (u i z - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  change ‖u i z - 1‖ ≤ K * ‖z‖ at h
  linarith

/-- The principal logarithm of one Euler factor. -/
def phaseEulerLog (q : ℝ) (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  -Complex.log (1 - (q : ℂ) * u z)

theorem phaseEulerLog_bound {q : ℝ} {u : ℂ → ℂ} {z : ℂ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (hu : ‖u z‖ ≤ 3 / 2) :
    ‖phaseEulerLog q u z‖ ≤ 6 * q := by
  have hw : ‖(q : ℂ) * u z‖ ≤ 3 / 4 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
    nlinarith [mul_nonneg hq0 (norm_nonneg (u z))]
  have hn : ‖(q : ℂ) * u z‖ ≤ q * (3 / 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
    exact mul_le_mul_of_nonneg_left hu hq0
  have hlog := HTGeometry.norm_log_one_sub_le (lt_of_le_of_lt hw (by norm_num))
  rw [phaseEulerLog, norm_neg]
  refine hlog.trans ?_
  apply (div_le_iff₀ (by linarith : 0 < 1 - ‖(q : ℂ) * u z‖)).mpr
  nlinarith [mul_nonneg hq0 (by linarith : 0 ≤ 3 / 4 - ‖(q : ℂ) * u z‖)]

theorem phaseEulerLog_differentiableOn {q : ℝ} {u : ℂ → ℂ} {δ : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2)
    (hu : DifferentiableOn ℂ u (ball 0 δ))
    (hbd : ∀ z ∈ ball 0 δ, ‖u z‖ ≤ 3 / 2) :
    DifferentiableOn ℂ (phaseEulerLog q u) (ball 0 δ) := by
  intro z hz
  have hw : ‖(q : ℂ) * u z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
    have hh := hbd z hz
    nlinarith [mul_nonneg hq0 (norm_nonneg (u z))]
  have hsl : 1 - (q : ℂ) * u z ∈ Complex.slitPlane := by
    rw [sub_eq_add_neg]
    apply Complex.mem_slitPlane_of_norm_lt_one
    rwa [norm_neg]
  exact (((differentiableAt_const (1 : ℂ)).sub
    ((hu.differentiableAt (isOpen_ball.mem_nhds hz)).const_mul (q : ℂ))).clog hsl).neg.differentiableWithinAt


/-- Unimodularity determines the real parts of both initial jets. -/
theorem unit_phase_jets {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0)
    (hu0 : u 0 = 1) (hunit : ∀ᶠ t : ℝ in 𝓝 0, ‖u (t : ℂ)‖ = 1) :
    (deriv u 0).re = 0 ∧
      (deriv (deriv u) 0).re = -(deriv u 0).im ^ 2 := by
  let g : ℝ → ℂ := fun t => u t * conj (u t)
  have hg : g =ᶠ[𝓝 0] fun _ => 1 := by
    filter_upwards [hunit] with t ht
    dsimp [g]
    rw [Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq, ht]
  have hd := hu.differentiableAt.hasDerivAt
  have hdR : HasDerivAt (fun t : ℝ => u (t : ℂ)) (deriv u 0) 0 := by
    simpa using hd.comp_ofReal
  have hg1 := (hdR.mul hdR.star).deriv
  have hz : deriv g 0 = 0 := by rw [hg.deriv_eq]; simp
  change deriv g 0 = _ at hg1
  simp only [Complex.ofReal_zero, hz, hu0, star_one, mul_one, one_mul] at hg1
  change 0 = deriv u 0 + conj (deriv u 0) at hg1
  have hre : (deriv u 0).re = 0 := by
    have hh := congrArg Complex.re hg1
    simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at hh
    linarith
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, AnalyticAt ℂ u (t : ℂ) :=
    (show ContinuousAt (fun t : ℝ => (t : ℂ)) 0 from Complex.continuous_ofReal.continuousAt).tendsto.eventually
      (by simpa using hu.eventually_analyticAt)
  have hgder : deriv g =ᶠ[𝓝 0] fun t : ℝ =>
      deriv u t * conj (u t) + u t * conj (deriv u t) := by
    filter_upwards [hnear] with t ht
    exact (ht.differentiableAt.hasDerivAt.comp_ofReal.mul
      ht.differentiableAt.hasDerivAt.comp_ofReal.star).deriv
  have hd2R : HasDerivAt (fun t : ℝ => deriv u (t : ℂ))
      (deriv (deriv u) 0) 0 := by
    simpa using hu.deriv.differentiableAt.hasDerivAt.comp_ofReal
  have hg2 := ((hd2R.mul hdR.star).add (hdR.mul hd2R.star)).deriv
  have hzero : deriv (deriv g) 0 = 0 := by
    rw [hg.deriv.deriv_eq]
    simp
  rw [hgder.deriv_eq] at hzero
  change deriv (fun t : ℝ => deriv u t * conj (u t) + u t * conj (deriv u t)) 0 =
    deriv (deriv u) 0 * conj (u 0) + deriv u 0 * conj (deriv u 0) +
      (deriv u 0 * conj (deriv u 0) + u 0 * conj (deriv (deriv u) 0)) at hg2
  rw [hzero, hu0] at hg2
  have hh := congrArg Complex.re hg2
  simp only [mul_one, map_one, one_mul, Complex.add_re, Complex.conj_re,
    Complex.mul_re, Complex.conj_im, Complex.zero_re, hre] at hh
  refine ⟨hre, ?_⟩
  nlinarith only [hh]

/-- The second logarithmic Euler jet contains only the squared phase speed. -/
theorem phaseEulerLog_second_re {q : ℝ} {u : ℂ → ℂ}
    (hq : q < 1) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 = 1)
    (hunit : ∀ᶠ t : ℝ in 𝓝 0, ‖u (t : ℂ)‖ = 1) :
    (deriv (deriv (phaseEulerLog q u)) 0).re =
      -(deriv u 0).im ^ 2 * q / (1 - q) ^ 2 := by
  have hden : (1 : ℂ) - q ≠ 0 := by
    exact_mod_cast (sub_pos.mpr hq).ne'
  have hsl : 1 - (q : ℂ) * u 0 ∈ Complex.slitPlane := by
    rw [hu0, mul_one]
    apply Or.inl
    simpa using sub_pos.mpr hq
  have ha : AnalyticAt ℂ (fun z => 1 - (q : ℂ) * u z) 0 :=
    analyticAt_const.sub (analyticAt_const.mul hu)
  have hslnear : ∀ᶠ z in 𝓝 (0 : ℂ),
      1 - (q : ℂ) * u z ∈ Complex.slitPlane :=
    ha.continuousAt.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hsl)
  have heq : deriv (phaseEulerLog q u) =ᶠ[𝓝 0]
      fun z => (q : ℂ) * deriv u z / (1 - (q : ℂ) * u z) := by
    filter_upwards [hu.eventually_analyticAt, hslnear] with z hz hs
    have h := (((hasDerivAt_const z (1 : ℂ)).sub
      (hz.differentiableAt.hasDerivAt.const_mul (q : ℂ))).clog hs).neg
    change HasDerivAt (phaseEulerLog q u) _ z at h
    rw [h.deriv]
    simp only [Pi.sub_apply]
    ring
  rw [heq.deriv_eq]
  have hd := ((hu.deriv.differentiableAt.hasDerivAt.const_mul (q : ℂ)).div
    ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub
      (hu.differentiableAt.hasDerivAt.const_mul (q : ℂ)))
    (by simpa [hu0] using hden)).deriv
  change deriv (fun z => (q : ℂ) * deriv u z / (1 - (q : ℂ) * u z)) 0 =
    ((q : ℂ) * deriv (deriv u) 0 * (1 - (q : ℂ) * u 0) -
      (q : ℂ) * deriv u 0 * (0 - (q : ℂ) * deriv u 0)) /
      (1 - (q : ℂ) * u 0) ^ 2 at hd
  rw [hd, hu0]
  obtain ⟨hr1, hr2⟩ := unit_phase_jets hu hu0 hunit
  have he : (((q : ℂ) * deriv (deriv u) 0 * (1 - (q : ℂ) * 1) -
      (q : ℂ) * deriv u 0 * (0 - (q : ℂ) * deriv u 0)) /
      (1 - (q : ℂ) * 1) ^ 2) =
      ((q / (1 - q) : ℝ) : ℂ) * deriv (deriv u) 0 +
      ((q ^ 2 / (1 - q) ^ 2 : ℝ) : ℂ) * deriv u 0 ^ 2 := by
    push_cast
    field_simp
    ring
  rw [he]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, pow_two, hr1, hr2]
  field_simp
  ring

/-- Uniform logarithmic bounds justify all parameter derivatives of the Euler sum. -/
theorem phaseEulerLog_tsum_regular {ι : Type*} {q : ι → ℝ}
    {u : ι → ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hu : ∀ i, DifferentiableOn ℂ (u i) (ball 0 R))
    (hbd : ∀ i z, z ∈ ball 0 R → ‖u i z‖ ≤ M)
    (hu0 : ∀ i, u i 0 = 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∀ i, q i ≤ 1 / 2) (hqs : Summable q) :
    AnalyticAt ℂ (fun z => ∑' i, phaseEulerLog (q i) (u i) z) 0 ∧
      ∀ k : ℕ, HasSum (fun i => iteratedDeriv k (phaseEulerLog (q i) (u i)) 0)
        (iteratedDeriv k (fun z => ∑' i, phaseEulerLog (q i) (u i) z) 0) := by
  obtain ⟨δ, hδ, hδR, hb⟩ := exists_uniform_phase_ball hR hM hu hbd hu0
  have hd : ∀ i, DifferentiableOn ℂ (phaseEulerLog (q i) (u i)) (ball 0 δ) :=
    fun i => phaseEulerLog_differentiableOn (hq0 i) (hq i)
      ((hu i).mono (ball_subset_ball hδR.le)) (hb i)
  have hh := HTGeometry.hasSum_iteratedDeriv_of_summable_bound isOpen_ball hd
    (hqs.mul_left 6) (fun i z hz => phaseEulerLog_bound (hq0 i) (hq i) (hb i z hz))
  exact ⟨hh.1.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hδ)),
    fun k => hh.2 k 0 (mem_ball_self hδ)⟩

/-- Termwise Euler curvature for a uniformly holomorphic family of unit phases. -/
theorem hasSum_phaseEulerLog_curvature {ι : Type*} {q : ι → ℝ}
    {u : ι → ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hu : ∀ i, DifferentiableOn ℂ (u i) (ball 0 R))
    (hbd : ∀ i z, z ∈ ball 0 R → ‖u i z‖ ≤ M)
    (hu0 : ∀ i, u i 0 = 1)
    (hunit : ∀ i, ∀ᶠ t : ℝ in 𝓝 0, ‖u i (t : ℂ)‖ = 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∀ i, q i ≤ 1 / 2) (hqs : Summable q) :
    HasSum (fun i => (deriv (u i) 0).im ^ 2 * q i / (1 - q i) ^ 2)
      (-(deriv (deriv (fun z => ∑' i, phaseEulerLog (q i) (u i) z)) 0).re) := by
  have hh := (phaseEulerLog_tsum_regular hR hM hu hbd hu0 hq0 hq hqs).2 2
  have hreal := (Complex.hasSum_re hh).neg
  simp only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero] at hreal
  have he (i : ι) : -(deriv (deriv (phaseEulerLog (q i) (u i))) 0).re =
      (deriv (u i) 0).im ^ 2 * q i / (1 - q i) ^ 2 := by
    rw [phaseEulerLog_second_re (lt_of_le_of_lt (hq i) (by norm_num))
      ((hu i).analyticAt (isOpen_ball.mem_nhds (mem_ball_self hR))) (hu0 i) (hunit i)]
    ring
  simpa only [he] using hreal

/-- The prime quadratic form vanishes precisely when every visible phase speed vanishes. -/
theorem phase_curvature_zero_iff {ι : Type*} {a q : ι → ℝ}
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (hs : Summable (fun i => a i ^ 2 * q i / (1 - q i) ^ 2)) :
    (∑' i, a i ^ 2 * q i / (1 - q i) ^ 2) = 0 ↔ ∀ i, a i = 0 := by
  have hn : ∀ i, 0 ≤ a i ^ 2 * q i / (1 - q i) ^ 2 := fun i =>
    div_nonneg (mul_nonneg (sq_nonneg _) (hq0 i).le) (sq_nonneg _)
  constructor
  · intro h i
    have hi := hs.le_tsum i (fun j _ => hn j)
    rw [h] at hi
    have hz : a i ^ 2 * q i / (1 - q i) ^ 2 = 0 := le_antisymm hi (hn i)
    have hd : (1 - q i) ^ 2 ≠ 0 := pow_ne_zero _ (sub_pos.mpr (hq1 i)).ne'
    have hz' := (div_eq_zero_iff.mp hz).resolve_right hd
    have := (mul_eq_zero.mp hz').resolve_right (hq0 i).ne'
    exact sq_eq_zero_iff.mp this
  · intro h
    simp only [h, zero_pow (by norm_num : 2 ≠ 0), zero_mul, zero_div, tsum_zero]

/-- A finite boundary limit of positive series forces convergence at the boundary.
The pointwise boundary terms dominate the approximants, so no mass is lost in the limit. -/
theorem hasSum_of_nonneg_dominated_boundary {ι α : Type*} {l : Filter α} [l.NeBot]
    {f : α → ι → ℝ} {g : ι → ℝ} {L : ℝ}
    (hpos : ∀ᶠ x in l, ∀ i, 0 ≤ f x i)
    (hs : ∀ᶠ x in l, Summable (f x))
    (hlim : ∀ i, Tendsto (fun x => f x i) l (𝓝 (g i)))
    (hbound : ∀ᶠ x in l, ∀ i, f x i ≤ g i)
    (htotal : Tendsto (fun x => ∑' i, f x i) l (𝓝 L)) :
    HasSum g L := by
  have hg : ∀ i, 0 ≤ g i := fun i =>
    le_of_tendsto_of_tendsto tendsto_const_nhds (hlim i) (hpos.mono (fun x hx => hx i))
  have hsum : Summable g := summable_of_sum_le hg fun S => by
    have hfinite : Tendsto (fun x => ∑ i ∈ S, f x i) l (𝓝 (∑ i ∈ S, g i)) :=
      tendsto_finsetSum S (fun i _ => hlim i)
    apply le_of_tendsto_of_tendsto hfinite htotal
    filter_upwards [hs, hpos] with x hx hp
    exact hx.sum_le_tsum S (fun i _ => hp i)
  have hconv := tendsto_tsum_of_dominated_convergence hsum hlim (by
    filter_upwards [hpos, hbound] with x hp hb
    intro i
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hp i)] using hb i)
  have heq : (∑' i, g i) = L := tendsto_nhds_unique hconv htotal
  exact heq ▸ hsum.hasSum


/-- Complex derivative in the parameter coordinate, with the spectral coordinate fixed. -/
def parameterDeriv (f : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  fderiv ℂ f p (1, 0)

theorem analyticAt_parameterDeriv {f : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hf : AnalyticAt ℂ f p) : AnalyticAt ℂ (parameterDeriv f) p := by
  exact ((ContinuousLinearMap.apply ℂ ℂ ((1, 0) : ℂ × ℂ)).analyticAt _).comp hf.fderiv

theorem parameterDeriv_eq_deriv {f : ℂ × ℂ → ℂ} {t s : ℂ}
    (hf : AnalyticAt ℂ f (t, s)) :
    parameterDeriv f (t, s) = deriv (fun z => f (z, s)) t := by
  exact (hf.differentiableAt.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t s))).deriv.symm

theorem parameterDeriv_twice_eq {f : ℂ × ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f (0, s)) :
    parameterDeriv (parameterDeriv f) (0, s) =
      deriv (deriv (fun z => f (z, s))) 0 := by
  have he : deriv (fun z => f (z, s)) =ᶠ[𝓝 0]
      fun z => parameterDeriv f (z, s) := by
    have hh : ∀ᶠ z : ℂ in 𝓝 0, AnalyticAt ℂ f (z, s) :=
      (continuousAt_id.prodMk continuousAt_const).tendsto.eventually hf.eventually_analyticAt
    filter_upwards [hh] with z hz
    exact (parameterDeriv_eq_deriv hz).symm
  rw [he.deriv_eq]
  exact parameterDeriv_eq_deriv (analyticAt_parameterDeriv hf)

/-- Complex second jets restrict to the second real derivative of the real part. -/
theorem real_second_re_of_analyticAt {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    deriv (deriv (fun t : ℝ => (f (t : ℂ)).re)) 0 =
      (deriv (deriv f) 0).re := by
  have he : deriv (fun t : ℝ => (f (t : ℂ)).re) =ᶠ[𝓝 0]
      fun t => (deriv f (t : ℂ)).re := by
    have hh : ∀ᶠ t : ℝ in 𝓝 0, AnalyticAt ℂ f (t : ℂ) :=
      (show ContinuousAt (fun t : ℝ => (t : ℂ)) 0 from Complex.continuous_ofReal.continuousAt).tendsto.eventually
        (by simpa using hf.eventually_analyticAt)
    filter_upwards [hh] with t ht
    exact ht.differentiableAt.hasDerivAt.real_of_complex.deriv
  rw [he.deriv_eq]
  simpa using hf.deriv.differentiableAt.hasDerivAt.real_of_complex.deriv

/-- Logarithmic curvature written as a jointly analytic parameter jet. -/
def residueCurvature (U : ℂ × ℂ → ℂ) (s : ℂ) : ℝ :=
  -(parameterDeriv (parameterDeriv (fun p => Complex.log (U p))) (0, s)).re

theorem residueCurvature_continuousAt {U : ℂ × ℂ → ℂ} {s : ℂ}
    (hU : AnalyticAt ℂ U (0, s)) (hsl : U (0, s) ∈ Complex.slitPlane) :
    ContinuousAt (residueCurvature U) s := by
  have hh := analyticAt_parameterDeriv (analyticAt_parameterDeriv (hU.clog hsl))
  exact (Complex.continuous_re.continuousAt.comp
    (hh.continuousAt.comp (continuousAt_const.prodMk continuousAt_id))).neg

theorem residueCurvature_eq_real_second {U : ℂ × ℂ → ℂ} {s : ℂ}
    (hU : AnalyticAt ℂ U (0, s)) (hsl : U (0, s) ∈ Complex.slitPlane) :
    residueCurvature U s =
      -deriv (deriv (fun t : ℝ => Real.log ‖U ((t : ℂ), s)‖)) 0 := by
  have hh := hU.clog hsl
  have hs : AnalyticAt ℂ (fun z => Complex.log (U (z, s))) 0 :=
    hh.comp (f := fun z : ℂ => (z, s)) (analyticAt_id.prod analyticAt_const)
  have he : (fun t : ℝ => Real.log ‖U ((t : ℂ), s)‖) =
      (fun t : ℝ => (Complex.log (U ((t : ℂ), s))).re) := by
    funext t
    exact (Complex.log_re _).symm
  rw [he, real_second_re_of_analyticAt hs]
  unfold residueCurvature
  rw [parameterDeriv_twice_eq hh]



/-- Multiplying an exponential by a nonzero constant does not change its logarithmic curvature. -/
theorem real_second_logNorm_of_const_exp {g : ℝ → ℂ} {F : ℂ → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hF : AnalyticAt ℂ F 0)
    (he : ∀ᶠ t : ℝ in 𝓝 0, g t = c * Complex.exp (F (t : ℂ))) :
    deriv (deriv (fun t => Real.log ‖g t‖)) 0 = (deriv (deriv F) 0).re := by
  have heq : (fun t : ℝ => Real.log ‖g t‖) =ᶠ[𝓝 0]
      (fun t => Real.log ‖c‖ + (F (t : ℂ)).re) := by
    filter_upwards [he] with t ht
    rw [ht, norm_mul, Complex.norm_exp,
      Real.log_mul (norm_ne_zero_iff.mpr hc) (Real.exp_ne_zero _), Real.log_exp]
  have hd : deriv (fun t : ℝ => Real.log ‖c‖ + (F (t : ℂ)).re) =
      deriv (fun t : ℝ => (F (t : ℂ)).re) := funext fun _ => deriv_const_add _
  rw [heq.deriv.deriv_eq, hd, real_second_re_of_analyticAt hF]

#print axioms phaseEulerLog_tsum_regular
#print axioms unit_phase_jets
#print axioms hasSum_phaseEulerLog_curvature
#print axioms hasSum_of_nonneg_dominated_boundary
#print axioms residueCurvature_eq_real_second
#print axioms residueCurvature_continuousAt
#print axioms real_second_logNorm_of_const_exp
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
