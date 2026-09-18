import Mathlib

/-!
# Poisson-smoothed picket fence: exact cotangent law and a Cauchy limit without collapse

Najnudel–Nikeghbali (arXiv 2609.15862, Sept 2026) prove that the projected microscopic
Stieltjes transform of the zeta zeros has a `Cauchy(0,1)` limit law unconditionally, and that the
normalised critical-line logarithmic derivative has the same limit provided the horizontal moment
`H(T) = Σ_{β>1/2} m(ρ)(β − 1/2)` is `o(T)`.  They leave open whether the horizontal collapse
`H(T) = o(T)` is *necessary* for the marginal limit.

This module shows that, for abstract positive stationary configurations, it is not: the Cauchy
marginal is blind to horizontal displacement hidden in growing clusters.

The configuration is the `k`-periodic *picket fence* of atoms of mass `k` at `kℤ`, each replaced
by a Poisson kernel of width `η` (an off-line pair `{ρ, 1 − ρ̄}` with `Re ρ − 1/2 = a` contributes to
the critical-line logarithmic derivative exactly the Hilbert transform of a Poisson kernel of width
`a`; in microscopic units `η = a·log T/(2π)`).  Its Hilbert transform is an exact cotangent:

`Σ_{n ∈ ℤ} k (x − nk) / ((x − nk)² + η²) = π · Re cot (π (x − iη) / k)`.

Consequently the normalised statistic at a uniform microscopic point is `−Re cot(π(U − i η/k))`,
`U` uniform on `(0,1)`, which is a *bounded* random variable for every `η > 0` (no Cauchy tail at
all: the picket fence has no singular part), yet converges in law to `Cauchy(0,1)` as `k → ∞`
with `η` fixed.  So a configuration in which *every* zero is displaced by the same positive
microscopic amount, with the mean spacing preserved, has the Cauchy marginal of the projected
configuration.  The exact atomic case `η = 0` is Boole's law: `−cot(πU)` is exactly `Cauchy(0,1)`.

For the zeros of `ζ` such growing clusters are excluded by the unconditional counting-discrepancy
bound (Fujii); the point of the module is that the marginal law alone cannot do it.
-/

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace RHTower.PoissonSmoothedPicketFence

/-! ## The picket fence and its exact cotangent transform -/

/-- Hilbert transform at `x` of the Poisson kernel of mass `k`, width `η` and centre `c`
(for `η = 0`: the Cauchy kernel `k/(x − c)` of an atom of mass `k`). -/
noncomputable def poissonHilbert (k η c x : ℝ) : ℝ := k * (x - c) / ((x - c) ^ 2 + η ^ 2)

/-- The `k`-periodic Poisson-smoothed picket-fence transform, with the Mittag-Leffler pairing
`n ↔ −n` of the centres `± n k`. -/
noncomputable def picketTransform (k η x : ℝ) : ℝ :=
  poissonHilbert k η 0 x +
    ∑' n : ℕ, (poissonHilbert k η ((n + 1) * k) x + poissonHilbert k η (-((n + 1) * k)) x)

/-- The microscopic complex position `(x − iη)/k`. -/
noncomputable def microPosition (k η x : ℝ) : ℂ := ((x : ℂ) - (η : ℂ) * I) / (k : ℂ)

@[simp] lemma microPosition_re (k η x : ℝ) : (microPosition k η x).re = x / k := by
  simp [microPosition, Complex.div_ofReal_re]

@[simp] lemma microPosition_im (k η x : ℝ) : (microPosition k η x).im = -η / k := by
  simp [microPosition, Complex.div_ofReal_im]

lemma microPosition_mem_integerComplement {k η : ℝ} (hk : k ≠ 0) (hη : η ≠ 0) (x : ℝ) :
    microPosition k η x ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have h := congrArg Complex.im hn
  rw [microPosition_im, Complex.intCast_im] at h
  have h' : -η / k = 0 := h.symm
  rw [div_eq_zero_iff, neg_eq_zero] at h'
  exact h'.elim hη hk

lemma microPosition_mul {k : ℝ} (hk : k ≠ 0) (η u : ℝ) :
    microPosition k η (k * u) = (u : ℂ) - ((η / k : ℝ) : ℂ) * I := by
  unfold microPosition
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  rw [div_eq_iff hk']
  push_cast
  try field_simp
  try ring

/-- Real part of a single Mittag-Leffler term. -/
lemma re_one_div_microPosition_sub {k η x : ℝ} (hk : k ≠ 0) (m : ℝ)
    (hne : microPosition k η x - (m : ℂ) ≠ 0) :
    (1 / (microPosition k η x - (m : ℂ))).re = poissonHilbert k η (m * k) x := by
  have hden : (x - m * k) ^ 2 + η ^ 2 ≠ 0 := by
    intro h0
    have hx : x - m * k = 0 := by nlinarith [sq_nonneg (x - m * k), sq_nonneg η]
    have hη : η = 0 := by nlinarith [sq_nonneg (x - m * k), sq_nonneg η]
    apply hne
    refine Complex.ext ?_ ?_
    · simp only [Complex.sub_re, microPosition_re, Complex.ofReal_re, Complex.zero_re]
      rw [show x = m * k by linarith, mul_div_cancel_right₀ _ hk, sub_self]
    · simp only [Complex.sub_im, microPosition_im, Complex.ofReal_im, Complex.zero_im, hη,
        neg_zero, zero_div, sub_zero]
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, microPosition_re, microPosition_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero]
  unfold poissonHilbert
  field_simp
  try ring

/-- **Exact cotangent law of the Poisson-smoothed picket fence.** -/
theorem picketTransform_eq_pi_mul_re_cot {k η x : ℝ} (hk : k ≠ 0)
    (hz : microPosition k η x ∈ Complex.integerComplement) :
    picketTransform k η x = π * (cot (π * microPosition k η x)).re := by
  set z := microPosition k η x with hzdef
  have h := cot_series_rep' hz
  have hs : Summable fun n : ℕ => 1 / (z - ((n : ℂ) + 1)) + 1 / (z + ((n : ℂ) + 1)) :=
    summable_cotTerm hz
  have h1 : (π : ℂ) * cot (π * z) = 1 / z + ∑' n : ℕ, (1 / (z - ((n : ℂ) + 1)) + 1 / (z + ((n : ℂ) + 1))) := by
    rw [← h]; try ring
  have hre : π * (cot (π * z)).re =
      (1 / z).re + ∑' n : ℕ, ((1 / (z - ((n : ℂ) + 1))).re + (1 / (z + ((n : ℂ) + 1))).re) := by
    rw [← Complex.re_ofReal_mul, h1, Complex.add_re, Complex.re_tsum hs]
    try simp only [Complex.add_re]
  rw [hre]
  unfold picketTransform
  have hz0 : z - ((0 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    apply hz
    exact ⟨0, by simpa [sub_eq_zero] using h0.symm⟩
  have hterm : ∀ n : ℕ, (1 / (z - ((n : ℂ) + 1))).re = poissonHilbert k η ((n + 1) * k) x := by
    intro n
    have hne : z - (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
      intro h0
      apply hz
      refine ⟨(n : ℤ) + 1, ?_⟩
      rw [sub_eq_zero] at h0
      push_cast at h0 ⊢
      exact h0.symm
    have := re_one_div_microPosition_sub hk ((n : ℝ) + 1) hne
    rw [← this]
    congr 2
    push_cast; ring
  have hterm' : ∀ n : ℕ, (1 / (z + ((n : ℂ) + 1))).re = poissonHilbert k η (-((n + 1) * k)) x := by
    intro n
    have hne : z - ((-((n : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by
      intro h0
      apply hz
      refine ⟨-((n : ℤ) + 1), ?_⟩
      rw [sub_eq_zero] at h0
      push_cast at h0 ⊢
      exact h0.symm
    have := re_one_div_microPosition_sub hk (-((n : ℝ) + 1)) hne
    rw [show -((n + 1) * k) = -((n : ℝ) + 1) * k by ring, ← this]
    congr 2
    push_cast; ring
  have h0 : (1 / z).re = poissonHilbert k η 0 x := by
    have := re_one_div_microPosition_sub hk 0 hz0
    rw [zero_mul, Complex.ofReal_zero, sub_zero] at this
    exact this
  rw [h0]
  congr 1
  exact tsum_congr fun n => by rw [hterm n, hterm' n]

/-- Smoothed case: for `η ≠ 0` the cotangent law holds at every `x`. -/
theorem picketTransform_eq_of_ne {k η : ℝ} (hk : k ≠ 0) (hη : η ≠ 0) (x : ℝ) :
    picketTransform k η x = π * (cot (π * microPosition k η x)).re :=
  picketTransform_eq_pi_mul_re_cot hk (microPosition_mem_integerComplement hk hη x)

/-! ## Boole's law: the atomic fence is exactly Cauchy -/

/-- The chart `x ↦ 1/2 + arctan x / π`, a bijection `ℝ → (0,1)` whose derivative is the
standard Cauchy density. -/
noncomputable def arctanChart (x : ℝ) : ℝ := 1 / 2 + Real.arctan x / π

lemma hasDerivAt_arctanChart (x : ℝ) :
    HasDerivAt arctanChart (1 / (π * (1 + x ^ 2))) x := by
  have h := ((Real.hasDerivAt_arctan x).div_const π).const_add (1 / 2)
  have e : (1 / (1 + x ^ 2)) / π = 1 / (π * (1 + x ^ 2)) := by
    rw [div_div, mul_comm]
  rw [e] at h
  exact h

lemma arctanChart_injective : Function.Injective arctanChart := by
  intro a b h
  unfold arctanChart at h
  have hπ : π ≠ 0 := Real.pi_ne_zero
  apply Real.arctan_injective
  have : Real.arctan a / π = Real.arctan b / π := by linarith
  field_simp at this
  exact this

lemma range_arctanChart : Set.range arctanChart = Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    unfold arctanChart
    have h1 := Real.neg_pi_div_two_lt_arctan x
    have h2 := Real.arctan_lt_pi_div_two x
    have hπ := Real.pi_pos
    constructor
    · have : -(1 / 2 : ℝ) < Real.arctan x / π := by
        rw [lt_div_iff₀ hπ]; linarith
      linarith
    · have : Real.arctan x / π < 1 / 2 := by
        rw [div_lt_iff₀ hπ]; linarith
      linarith
  · intro hu
    refine ⟨Real.tan (π * (u - 1 / 2)), ?_⟩
    unfold arctanChart
    have hπ := Real.pi_pos
    rw [Real.arctan_tan (by nlinarith [hu.1]) (by nlinarith [hu.2])]
    field_simp
    ring

lemma neg_cot_pi_mul_arctanChart (x : ℝ) : -(Real.cot (π * arctanChart x)) = x := by
  unfold arctanChart
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have : π * (1 / 2 + Real.arctan x / π) = Real.arctan x + π / 2 := by
    field_simp; ring
  rw [this, Real.cot_eq_cos_div_sin, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  conv_rhs => rw [← Real.tan_arctan x, Real.tan_eq_sin_div_cos]
  rw [neg_div, neg_neg]

/-- **Boole's law for the atomic picket fence.**  For `U` uniform on `(0,1)` the statistic
`−cot(πU)` has exactly the standard Cauchy law: for every `φ : ℝ → ℝ`,
`∫_{(0,1)} φ(−cot(πu)) du = ∫ φ dCauchy(0,1)`. -/
theorem integral_neg_cot_uniform_eq_cauchy (φ : ℝ → ℝ) :
    ∫ u in Ioo (0 : ℝ) 1, φ (-(Real.cot (π * u))) =
      ∫ x, φ x ∂(ProbabilityTheory.cauchyMeasure 0 1) := by
  have hcv := integral_image_eq_integral_abs_deriv_smul (s := (univ : Set ℝ)) MeasurableSet.univ
    (f := arctanChart) (f' := fun x => 1 / (π * (1 + x ^ 2)))
    (fun x _ => (hasDerivAt_arctanChart x).hasDerivWithinAt) arctanChart_injective.injOn
    (fun u => φ (-(Real.cot (π * u))))
  rw [Set.image_univ, range_arctanChart, Measure.restrict_univ] at hcv
  rw [hcv, ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 one_ne_zero,
    integral_withDensity_eq_integral_toReal_smul (ProbabilityTheory.measurable_cauchyPDF 0 1)
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  congr 1
  ext x
  have hpos : 0 < 1 / (π * (1 + x ^ 2)) := by positivity
  rw [neg_cot_pi_mul_arctanChart, ProbabilityTheory.cauchyPDF_def, abs_of_pos hpos,
    ENNReal.toReal_ofReal (by unfold ProbabilityTheory.cauchyPDFReal; positivity),
    ProbabilityTheory.cauchyPDFReal]
  simp only [smul_eq_mul, NNReal.coe_one, sub_zero, one_pow, mul_one]
  rw [one_div, mul_inv, add_comm (1 : ℝ) (x ^ 2)]
  try ring

/-! ## The smoothed statistic and its Cauchy limit -/

/-- The normalised smoothed statistic `−(1/π)·(Hilbert transform)` in microscopic units:
`−Re cot(π(u − iε))`, the value at the uniform point `u` when every atom is displaced by `ε`. -/
noncomputable def smoothedStat (ε u : ℝ) : ℝ := -(cot (π * ((u : ℂ) - (ε : ℂ) * I))).re

lemma smoothedStat_zero (u : ℝ) : smoothedStat 0 u = -(Real.cot (π * u)) := by
  simp [smoothedStat, Real.cot]

lemma sin_pi_mul_sub_ne_zero {ε : ℝ} (hε : ε ≠ 0) (u : ℝ) :
    sin (π * ((u : ℂ) - (ε : ℂ) * I)) ≠ 0 := by
  rw [Complex.sin_ne_zero_iff]
  intro m h
  have him := congrArg Complex.im h
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im] at him
  have : π * ε = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact Real.pi_ne_zero h1
  · exact hε h1

lemma sin_pi_mul_ofReal_ne_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    sin (π * ((u : ℂ) - ((0 : ℝ) : ℂ) * I)) ≠ 0 := by
  rw [Complex.sin_ne_zero_iff]
  intro m h
  have hre := congrArg Complex.re h
  simp only [Complex.ofReal_zero, zero_mul, sub_zero, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, mul_zero, sub_zero, zero_mul] at hre
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hu' : u = m := by
    have : π * u = π * m := by linarith
    exact mul_left_cancel₀ hπ this
  have h0 : (0 : ℤ) < m := by exact_mod_cast (hu'.symm ▸ hu.1 : (0 : ℝ) < m)
  have h1 : m < (1 : ℤ) := by exact_mod_cast (hu'.symm ▸ hu.2 : (m : ℝ) < 1)
  omega

lemma continuous_smoothedStat_of_ne {ε : ℝ} (hε : ε ≠ 0) :
    Continuous fun u : ℝ => smoothedStat ε u := by
  unfold smoothedStat Complex.cot
  refine (Complex.continuous_re.comp ?_).neg
  refine Continuous.div (by fun_prop) (by fun_prop) ?_
  intro u
  exact sin_pi_mul_sub_ne_zero hε u

lemma continuousAt_smoothedStat_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt (fun ε : ℝ => smoothedStat ε u) 0 := by
  unfold smoothedStat Complex.cot
  refine (Complex.continuous_re.continuousAt.comp ?_).neg
  refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
  exact sin_pi_mul_ofReal_ne_zero hu

/-- For every `ε > 0` the smoothed statistic is bounded (the smoothed fence has no singular
part, so its law has no Cauchy tail): `|Re cot(π(u − iε))| ≤ cosh(πε)/|sinh(πε)|`. -/
theorem abs_smoothedStat_le {ε : ℝ} (hε : ε ≠ 0) (u : ℝ) :
    |smoothedStat ε u| ≤ Real.cosh (π * ε) / |Real.sinh (π * ε)| := by
  have hz : π * ((u : ℂ) - (ε : ℂ) * I) = ((π * u : ℝ) : ℂ) + ((-(π * ε) : ℝ) : ℂ) * I := by
    push_cast; ring
  have hsinh : Real.sinh (π * ε) ≠ 0 := by
    intro h
    rw [Real.sinh_eq_zero] at h
    exact (mul_ne_zero Real.pi_ne_zero hε) h
  set a := π * u
  set b := -(π * ε)
  have hcos : cos (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I) =
      ((Real.cos a * Real.cosh b : ℝ) : ℂ) + ((-(Real.sin a * Real.sinh b) : ℝ) : ℂ) * I := by
    rw [Complex.cos_add_mul_I]; push_cast; ring
  have hsin : sin (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I) =
      ((Real.sin a * Real.cosh b : ℝ) : ℂ) + ((Real.cos a * Real.sinh b : ℝ) : ℂ) * I := by
    rw [Complex.sin_add_mul_I]; push_cast; ring
  have hnormcos : ‖cos (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I)‖ ≤ Real.cosh b := by
    rw [hcos, Complex.norm_def, Complex.normSq_add_mul_I]
    rw [Real.sqrt_le_left (Real.cosh_pos b).le]
    have h1 := Real.sin_sq_add_cos_sq a
    have h2 : Real.sinh b ^ 2 ≤ Real.cosh b ^ 2 := by
      have := Real.cosh_sq b
      nlinarith [sq_nonneg (Real.sinh b)]
    nlinarith [sq_nonneg (Real.sin a), sq_nonneg (Real.cos a), sq_nonneg (Real.sinh b),
      sq_nonneg (Real.cosh b)]
  have hnormsin : |Real.sinh b| ≤ ‖sin (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I)‖ := by
    rw [hsin, Complex.norm_def, Complex.normSq_add_mul_I]
    rw [Real.le_sqrt (abs_nonneg _) (by positivity), sq_abs]
    have h1 := Real.sin_sq_add_cos_sq a
    have h2 : Real.sinh b ^ 2 ≤ Real.cosh b ^ 2 := by
      have := Real.cosh_sq b
      nlinarith [sq_nonneg (Real.sinh b)]
    nlinarith [sq_nonneg (Real.sin a), sq_nonneg (Real.cos a), sq_nonneg (Real.sinh b),
      sq_nonneg (Real.cosh b)]
  have hsinhb : Real.sinh b ≠ 0 := by
    simp only [b, Real.sinh_neg, neg_ne_zero]; exact hsinh
  have hsinne : sin (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnormsin
    exact hsinhb (abs_nonpos_iff.mp hnormsin)
  calc |smoothedStat ε u| = ‖(cot (π * ((u : ℂ) - (ε : ℂ) * I))).re‖ := by
        rw [smoothedStat, Real.norm_eq_abs, abs_neg]
    _ ≤ ‖cot (π * ((u : ℂ) - (ε : ℂ) * I))‖ := Complex.abs_re_le_norm _
    _ = ‖cos (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I)‖ / ‖sin (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I)‖ := by
        rw [hz, Complex.cot_eq_cos_div_sin, norm_div]
    _ ≤ Real.cosh b / |Real.sinh b| := by
        apply div_le_div₀ (Real.cosh_pos b).le hnormcos (abs_pos.mpr hsinhb) hnormsin
    _ = Real.cosh (π * ε) / |Real.sinh (π * ε)| := by
        simp only [b, Real.cosh_neg, Real.sinh_neg, abs_neg]

/-- **Cauchy limit of the smoothed statistic.**  As the common displacement `ε → 0⁺`, the law of
`−Re cot(π(U − iε))`, `U` uniform on `(0,1)`, converges weakly to `Cauchy(0,1)`. -/
theorem tendsto_integral_smoothedStat (φ : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun ε : ℝ => ∫ u in Ioo (0 : ℝ) 1, φ (smoothedStat ε u)) (𝓝[>] 0)
      (𝓝 (∫ x, φ x ∂(ProbabilityTheory.cauchyMeasure 0 1))) := by
  rw [← integral_neg_cot_uniform_eq_cauchy φ]
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖φ‖) ?_ ?_
    (integrable_const _) ?_
  · exact eventually_nhdsWithin_of_forall fun ε hε =>
      (φ.continuous.comp (continuous_smoothedStat_of_ne (ne_of_gt hε))).aestronglyMeasurable
  · exact Eventually.of_forall fun ε => ae_of_all _ fun u => φ.norm_coe_le_norm _
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun u hu => ?_
    have h := (continuousAt_smoothedStat_zero hu).tendsto
    rw [smoothedStat_zero] at h
    exact ((φ.continuous.tendsto _).comp h).mono_left nhdsWithin_le_nhds

/-- **Headline: Cauchy law without horizontal collapse.**  Fix a displacement `η > 0` and let the
cluster size `k → ∞`.  The normalised picket-fence statistic `−picketTransform k η (kU)/π` at a
uniform microscopic point `U` converges in law to `Cauchy(0,1)`, although every atom of the
configuration is displaced by `η` and the transform is bounded for each `k`. -/
theorem tendsto_integral_picketTransform_atTop {η : ℝ} (hη : 0 < η)
    (φ : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun k : ℕ => ∫ u in Ioo (0 : ℝ) 1, φ (-(picketTransform k η (k * u)) / π)) atTop
      (𝓝 (∫ x, φ x ∂(ProbabilityTheory.cauchyMeasure 0 1))) := by
  have hε : Tendsto (fun k : ℕ => η / (k : ℝ)) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_const_div_atTop_nhds_zero_nat η, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact div_pos hη (by exact_mod_cast hk)
  have h := (tendsto_integral_smoothedStat φ).comp hε
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  show ∫ u in Ioo (0 : ℝ) 1, φ (smoothedStat (η / (k : ℝ)) u) =
    ∫ u in Ioo (0 : ℝ) 1, φ (-(picketTransform k η (k * u)) / π)
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  show φ (smoothedStat (η / (k : ℝ)) u) = φ (-(picketTransform k η (k * u)) / π)
  congr 1
  rw [picketTransform_eq_of_ne hk' hη.ne' (k * u), microPosition_mul hk', neg_div,
    mul_div_cancel_left₀ _ Real.pi_ne_zero]
  rfl

end RHTower.PoissonSmoothedPicketFence
