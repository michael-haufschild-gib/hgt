import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRenormalizedThetaSquareUnfolds

/-!
# The squared theta series has a double pole

The Dirichlet series of the squared coefficients of the projected cubic theta function,

`D(s) = Σ_{h ≠ 0} T_s(h)² (4π|ξ_h|)^{−s}`   (absolutely convergent for `Re s > 4`),

times the Bessel factor `M(s) = ∫_0^∞ t^{s−1} K_{1/3}(t)² dt`, continues analytically to
`{1 < Re s < 13/3, Im s > 0}` and to a punctured neighbourhood of `4/3`, where it has a **double pole**
(`thetaSqDirichlet_double_pole`):

`(s − 4/3)² M(s) D(s) → 12π c² r = 108 π³ r³ ≠ 0`,   `c = 3πr`, `r` the residue constant of the cubic
Eisenstein series.

The continuation is `Λ(s) = |P|⁻¹ (S(s) + C(s) − |P| c² 2^{s−2/3}/(s − 2/3) + c² Φ₀(s) 2^{4/3−s}/(s − 4/3)²)`
(`completedThetaSq`):

* `S(s)` (`seedPair`) — the seed pairing, the Mellin transform of `χ(v) a₀(G)(v) v^{−2}`; holomorphic on
  `0 < Re s < 13/3` because `a₀(G)(v) = O(v^{−7/3})`;
* `C(s)` (`corrPair`) — the pairing of `G` with MMD's `L²` correction `R(s(2−s)) defect(s)`; holomorphic off
  the real axis (`Re s ≠ 1`) and `(s − 4/3) C(s)` is holomorphic at `4/3`;
* `Φ₀` — the cleared scattering coefficient of the rational cusp subtraction, holomorphic on `Re s > 1`
  with `Φ₀(4/3) = 12π |P| r`.

On `{4 < Re s < 13/3, Im s > 0}` the identity `Λ = M D` is the unfolding of `∫_{D_Γ} G E(s)` two ways
(`integral_mul_eisenstein_eq`, `integral_renormalized_mul_eisenstein`). Only the scattering term carries
the double pole: the Eisenstein correction contributes at most a simple pole.
-/

noncomputable section

open MeasureTheory Filter Function Asymptotics
open scoped BigOperators Classical MatrixGroups ComplexConjugate ENNReal Topology

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-! ### The seed pairing -/

/-- The seed pairing `S(s) = ∫_0^∞ χ(v) v^s a₀(G)(v) v^{−3} dv`. -/
def seedPair (s : ℂ) : ℂ :=
  ∫ v in Set.Ioi (0 : ℝ), cuspSeedProfile 2 3 s v * cuspConstantTerm renormalizedThetaSq v / (v : ℂ) ^ 3

/-- `χ(v) a₀(G)(v) v^{−2}`. -/
def seedKernel (v : ℝ) : ℂ :=
  (cuspTransition 2 3 v : ℂ) * cuspConstantTerm renormalizedThetaSq v / (v : ℂ) ^ 2

theorem cuspSeedProfile_measurable (s : ℂ) : Measurable (cuspSeedProfile 2 3 s) := by
  unfold cuspSeedProfile positiveHeightPower logRatioPower
  have h1 : Measurable (fun v : ℝ => (cuspTransition 2 3 v : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (cuspTransition_contDiff 2 3).continuous.measurable
  have h2 : Measurable (fun v : ℝ => Complex.exp (s * ((Real.log v - Real.log 1 : ℝ) : ℂ))) :=
    Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (Real.measurable_log.sub measurable_const)))
  exact h1.mul h2

theorem norm_cuspSeedProfile_le (s : ℂ) (v : ℝ) (hv : 0 < v) : ‖cuspSeedProfile 2 3 s v‖ ≤ v ^ s.re := by
  rw [cuspSeedProfile, positiveHeightPower_eq_cpow s v hv, norm_mul, Complex.norm_real,
    Complex.norm_cpow_eq_rpow_re_of_pos hv]
  have h0 : 0 ≤ cuspTransition 2 3 v := Real.smoothTransition.nonneg _
  have h1 : cuspTransition 2 3 v ≤ 1 := Real.smoothTransition.le_one _
  rw [Real.norm_of_nonneg h0]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hv.le _) h1

/-- `a₀(G)(v) = O(v^{−7/3})` above height `2`. -/
theorem norm_cuspConstantTerm_renormalized_high :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 2 ≤ v → ‖cuspConstantTerm renormalizedThetaSq v‖ ≤ C * v ^ (-(7 : ℝ) / 3) := by
  obtain ⟨C, hC, hhigh⟩ := norm_renormalizedThetaSq_high
  refine ⟨C * periodAreaReal, by positivity, fun v hv => ?_⟩
  have hv0 : 0 < v := by linarith
  have := norm_cuspConstantTerm_le renormalizedThetaSq v hv0 _ fun z => hhigh z v hv0 hv
  linarith [this]

theorem cuspConstantTerm_renormalized_bounded :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v : ℝ, 0 < v → ‖cuspConstantTerm renormalizedThetaSq v‖ ≤ B := by
  obtain ⟨B, hB⟩ := renormalizedThetaSq_bounded
  refine ⟨max B 0 * periodAreaReal, by positivity, fun v hv => ?_⟩
  exact norm_cuspConstantTerm_le _ v hv _ fun z => (hB _).trans (le_max_left _ _)

theorem seedKernel_eq_zero (v : ℝ) (hv : v ≤ 2) : seedKernel v = 0 := by
  rw [seedKernel, cuspTransition_zero 2 3 v (by norm_num) hv, Complex.ofReal_zero, zero_mul, zero_div]

theorem seedKernel_measurable : Measurable seedKernel := by
  unfold seedKernel
  exact ((Complex.continuous_ofReal.measurable.comp (cuspTransition_contDiff 2 3).continuous.measurable).mul
    (cuspConstantTerm_measurable _ renormalizedThetaSq_measurable).measurable).div
      (Complex.measurable_ofReal.pow_const 2)

theorem norm_seedKernel_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 2 ≤ v → ‖seedKernel v‖ ≤ C * v ^ (-(13 : ℝ) / 3) := by
  obtain ⟨C, hC, hb⟩ := norm_cuspConstantTerm_renormalized_high
  refine ⟨C, hC, fun v hv => ?_⟩
  have hv0 : 0 < v := by linarith
  have h0 : 0 ≤ cuspTransition 2 3 v := Real.smoothTransition.nonneg _
  have h1 : cuspTransition 2 3 v ≤ 1 := Real.smoothTransition.le_one _
  rw [seedKernel, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hv0.le]
  have hpow : v ^ (-(7 : ℝ) / 3) / v ^ 2 = v ^ (-(13 : ℝ) / 3) := by
    rw [show -(13 : ℝ) / 3 = -(7 : ℝ) / 3 - 2 by norm_num, Real.rpow_sub hv0]
    norm_cast
  calc cuspTransition 2 3 v * ‖cuspConstantTerm renormalizedThetaSq v‖ / v ^ 2
      ≤ 1 * (C * v ^ (-(7 : ℝ) / 3)) / v ^ 2 := by
        gcongr
        exact hb v hv
    _ = C * v ^ (-(13 : ℝ) / 3) := by rw [one_mul, mul_div_assoc, hpow]

theorem seedPair_eq_mellin (s : ℂ) : seedPair s = mellin seedKernel s := by
  rw [seedPair, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [cuspSeedProfile, positiveHeightPower_eq_cpow s v hv, seedKernel, smul_eq_mul,
    Complex.cpow_sub _ _ hv0, Complex.cpow_one]
  field_simp

/-- **The seed pairing is holomorphic on `0 < Re s < 13/3`.** -/
theorem seedPair_differentiableAt (s : ℂ) (hs0 : 0 < s.re) (hs : s.re < 13 / 3) :
    DifferentiableAt ℂ seedPair s := by
  obtain ⟨C, hC, hb⟩ := norm_seedKernel_le
  have hfun : seedPair = mellin seedKernel := funext seedPair_eq_mellin
  rw [hfun]
  have hint : IntegrableOn seedKernel (Set.Ioi 0) := by
    have hg : IntegrableOn (fun v : ℝ => C * v ^ (-(13 : ℝ) / 3)) (Set.Ioi 2) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul _
    have h2 : IntegrableOn seedKernel (Set.Ioi 2) :=
      hg.mono' seedKernel_measurable.aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Ioi fun v (hv : 2 < v) => hb v hv.le)
    refine h2.of_forall_sdiff_eq_zero measurableSet_Ioi fun v hv => ?_
    exact seedKernel_eq_zero v (not_lt.mp hv.2)
  refine mellin_differentiableAt_of_isBigO_rpow (a := 13 / 3) (b := 0) hint.locallyIntegrableOn ?_ hs ?_ hs0
  · refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with v hv
    have hv0 : 0 < v := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hv0.le _)]
    have := hb v hv
    rwa [show -(13 : ℝ) / 3 = -(13 / 3) by norm_num] at this
  · refine IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)] with v hv
    rw [seedKernel_eq_zero v hv.2.le, norm_zero, zero_mul]

/-! ### The correction pairing -/

/-- The correction pairing `C(s) = ⟨G, Corr(s)⟩`. -/
def corrPair (s : ℂ) : ℂ := levelPairing renormalizedThetaSq renormalizedThetaSq_memLp (eisensteinCorrection s)

/-! ### The continuation -/

/-- The continuation `Λ(s)` of `M(s) D(s)`. -/
def completedThetaSq (s : ℂ) : ℂ :=
  periodArea⁻¹ * (seedPair s + corrPair s -
    periodArea * thetaCoeff ^ 2 * ((2 : ℂ) ^ (s - 2 / 3) / (s - 2 / 3)) +
      thetaCoeff ^ 2 * clearedScatterTotal s * ((2 : ℂ) ^ (4 / 3 - s) / (s - 4 / 3) ^ 2))

/-- **The identity.** For `4 < Re s < 13/3`, `Im s > 0`: `Λ(s) = M(s) D(s)`. -/
theorem completedThetaSq_eq (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) (hi : 0 < s.im) :
    completedThetaSq s = besselSqMellin s * thetaSqDirichlet s := by
  have hσ2 : 2 < s.re := by linarith
  have hseed : IntegrableOn (fun w => renormalizedThetaSq w * smoothCuspSeed 2 3 s w) levelSet
      hyperbolicVolume := by
    simp_rw [smoothCuspSeed_eq]
    exact renormalized_integrableOn_mul_incomplete _ (cuspSeedProfile_measurable s) hσ2 hs
      (norm_cuspSeedProfile_le s)
  have hint := renormalized_integrableOn_unfolded _ (cuspSeedProfile_measurable s) hσ2 hs
    (norm_cuspSeedProfile_le s)
  have h1 := integral_mul_eisenstein_eq renormalizedThetaSq renormalizedThetaSq_memLp s hs4 hi hseed
  rw [integral_mul_seed_eq renormalizedThetaSq renormalizedThetaSq_automorphy s hint,
    integral_renormalized_mul_eisenstein s hs4 hs] at h1
  have hne : s - 4 / 3 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re] at this
    norm_num at this
    linarith
  have hΦ : scatterTotal s = clearedScatterTotal s / (s - 4 / 3) :=
    eq_div_of_mul_eq hne (by rw [mul_comm]; exact sub_mul_scatterTotal s hσ2)
  have hP : periodArea ≠ 0 := Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne'
  rw [completedThetaSq]
  change periodArea⁻¹ * (seedPair s + corrPair s - _ + _) = _
  have hS : seedPair s = ∫ v in Set.Ioi (0 : ℝ), cuspSeedProfile 2 3 s v *
      (∫ z in periodDomain, renormalizedThetaSq (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 := rfl
  have hC : corrPair s = levelPairing renormalizedThetaSq renormalizedThetaSq_memLp (eisensteinCorrection s) :=
    rfl
  rw [hS, hC, ← h1, hΦ]
  field_simp
  ring

/-- `Λ` is differentiable wherever its four pieces are. -/
theorem completedThetaSq_differentiableAt_of (s : ℂ) (hseed : DifferentiableAt ℂ seedPair s)
    (hcorr : DifferentiableAt ℂ corrPair s) (hs1 : 1 < s.re) (h23 : s - 2 / 3 ≠ 0) (h43 : s - 4 / 3 ≠ 0) :
    DifferentiableAt ℂ completedThetaSq s := by
  have hcl := clearedScatterTotal_differentiableAt s hs1
  have hp1 : DifferentiableAt ℂ (fun s : ℂ => (2 : ℂ) ^ (s - 2 / 3) / (s - 2 / 3)) s :=
    ((differentiableAt_id.sub_const _).const_cpow (Or.inl two_ne_zero)).div
      (differentiableAt_id.sub_const _) h23
  have hp2 : DifferentiableAt ℂ (fun s : ℂ => (2 : ℂ) ^ (4 / 3 - s) / (s - 4 / 3) ^ 2) s :=
    (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl two_ne_zero)).div
      ((differentiableAt_id.sub_const _).pow 2) (pow_ne_zero 2 h43)
  unfold completedThetaSq
  exact ((((hseed.add hcorr).sub (hp1.const_mul _)).add ((hcl.const_mul _).mul hp2))).const_mul _

/-- `Λ` is holomorphic on `{1 < Re s < 13/3, Im s > 0}`. -/
theorem completedThetaSq_differentiableAt (s : ℂ) (hs1 : 1 < s.re) (hs : s.re < 13 / 3) (hi : 0 < s.im) :
    DifferentiableAt ℂ completedThetaSq s := by
  have hne : ∀ a : ℝ, s - (a : ℂ) ≠ 0 := by
    intro a h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at this
    linarith
  refine completedThetaSq_differentiableAt_of s (seedPair_differentiableAt s (by linarith) hs)
    (levelPairing_correction_analyticAt renormalizedThetaSq renormalizedThetaSq_memLp s
      (by linarith) hi.ne').differentiableAt hs1 (by simpa using hne (2 / 3)) (by simpa using hne (4 / 3))

/-- Near `4/3`, `(s − 4/3) C(s)` is the holomorphic `⟨G, N(s)⟩`. -/
theorem corrPair_center :
    AnalyticAt ℂ (fun s => levelPairing renormalizedThetaSq renormalizedThetaSq_memLp (correctionNumerator s))
      (4 / 3) ∧
      ∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), (s - 4 / 3) * corrPair s =
        levelPairing renormalizedThetaSq renormalizedThetaSq_memLp (correctionNumerator s) := by
  obtain ⟨h1, h2, -⟩ := levelPairing_correction_center renormalizedThetaSq renormalizedThetaSq_memLp
  exact ⟨h1, h2⟩

theorem near_four_thirds :
    ∀ᶠ s in 𝓝 (4 / 3 : ℂ), 1 < s.re ∧ s.re < 13 / 3 ∧ s - 2 / 3 ≠ 0 := by
  have hre : (4 / 3 : ℂ).re = 4 / 3 := by norm_num
  have h1 : ∀ᶠ s in 𝓝 (4 / 3 : ℂ), 1 < s.re :=
    (continuousAt_const (y := (1 : ℝ))).eventually_lt Complex.continuous_re.continuousAt
      (by rw [hre]; norm_num)
  have h2 : ∀ᶠ s in 𝓝 (4 / 3 : ℂ), s.re < 13 / 3 :=
    Complex.continuous_re.continuousAt.eventually_lt (continuousAt_const (y := (13 / 3 : ℝ)))
      (by rw [hre]; norm_num)
  have h3 : ∀ᶠ s in 𝓝 (4 / 3 : ℂ), s ≠ 2 / 3 := isOpen_ne.mem_nhds (by norm_num)
  filter_upwards [h1, h2, h3] with s a b c
  exact ⟨a, b, sub_ne_zero.mpr c⟩

/-- `Λ` is holomorphic on a punctured neighbourhood of `4/3`. -/
theorem completedThetaSq_differentiableAt_near :
    ∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ completedThetaSq s := by
  obtain ⟨hN, hev⟩ := corrPair_center
  set N := fun s => levelPairing renormalizedThetaSq renormalizedThetaSq_memLp (correctionNumerator s)
  rw [eventually_nhdsWithin_iff] at hev
  have hP := (hN.eventually_analyticAt.and (hev.and near_four_thirds)).eventually_nhds
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hP] with t ht htc
  have htc' : t ≠ 4 / 3 := htc
  have hne : t - 4 / 3 ≠ 0 := sub_ne_zero.mpr htc'
  obtain ⟨hNt, -, hre1, hre2, h23⟩ := ht.self_of_nhds
  have hcorr_eq : corrPair =ᶠ[𝓝 t] fun u => N u / (u - 4 / 3) := by
    have hne' : ∀ᶠ u in 𝓝 t, u ≠ 4 / 3 := isOpen_ne.mem_nhds htc'
    filter_upwards [ht, hne'] with u hu hu'
    rw [eq_div_iff (sub_ne_zero.mpr hu'), mul_comm]
    exact hu.2.1 hu'
  have hcorr : DifferentiableAt ℂ corrPair t :=
    (hNt.differentiableAt.div (differentiableAt_id.sub_const _) hne).congr_of_eventuallyEq hcorr_eq
  exact completedThetaSq_differentiableAt_of t (seedPair_differentiableAt t (by linarith) hre2) hcorr hre1
    h23 hne

/-! ### The double pole -/

/-- **The double pole of `Λ` at `4/3`.** `(s − 4/3)² Λ(s) → 12π c² r`. -/
theorem completedThetaSq_double_pole :
    Tendsto (fun s => (s - 4 / 3) ^ 2 * completedThetaSq s) (𝓝[≠] (4 / 3 : ℂ))
      (𝓝 (12 * (Real.pi : ℂ) * thetaCoeff ^ 2 * constantArithmeticResidue)) := by
  obtain ⟨hN, hev⟩ := corrPair_center
  set N := fun s => levelPairing renormalizedThetaSq renormalizedThetaSq_memLp (correctionNumerator s)
  set F : ℂ → ℂ := fun s => periodArea⁻¹ * ((s - 4 / 3) ^ 2 * seedPair s + (s - 4 / 3) * N s -
    (s - 4 / 3) ^ 2 * (periodArea * thetaCoeff ^ 2 * ((2 : ℂ) ^ (s - 2 / 3) / (s - 2 / 3))) +
      thetaCoeff ^ 2 * clearedScatterTotal s * (2 : ℂ) ^ (4 / 3 - s)) with hFdef
  have hP : periodArea ≠ 0 := Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne'
  -- `F` is continuous at `4/3`
  have hseed := seedPair_differentiableAt (4 / 3) (by norm_num) (by norm_num)
  have hcl := clearedScatterTotal_differentiableAt (4 / 3) (by norm_num)
  have hp1 : ContinuousAt (fun s : ℂ => (2 : ℂ) ^ (s - 2 / 3) / (s - 2 / 3)) (4 / 3) :=
    (((continuous_id.sub continuous_const).const_cpow (Or.inl two_ne_zero)).continuousAt).div
      ((continuous_id.sub continuous_const).continuousAt) (by norm_num)
  have hp2 : ContinuousAt (fun s : ℂ => (2 : ℂ) ^ (4 / 3 - s)) (4 / 3) :=
    ((continuous_const.sub continuous_id).const_cpow (Or.inl two_ne_zero)).continuousAt
  have hFc : ContinuousAt F (4 / 3) := by
    have hlin : ContinuousAt (fun s : ℂ => s - 4 / 3) (4 / 3) := (continuous_id.sub continuous_const).continuousAt
    exact continuousAt_const.mul ((((hlin.pow 2).mul hseed.continuousAt).add
      (hlin.mul hN.continuousAt)).sub ((hlin.pow 2).mul (continuousAt_const.mul hp1)) |>.add
      ((continuousAt_const.mul hcl.continuousAt).mul hp2))
  have hF43 : F (4 / 3) = 12 * (Real.pi : ℂ) * thetaCoeff ^ 2 * constantArithmeticResidue := by
    simp only [hFdef, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      add_zero, zero_add, Complex.cpow_zero, mul_one, clearedScatterTotal_four_thirds]
    have hcA : cuspArea = periodArea := rfl
    rw [hcA]
    field_simp
  rw [← hF43]
  refine (hFc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hs'
  have hne : s - 4 / 3 ≠ 0 := sub_ne_zero.mpr hs'
  have hs2 : (s - 4 / 3) * corrPair s = N s := hs
  have key : (s - 4 / 3) ^ 2 * ((2 : ℂ) ^ (4 / 3 - s) / (s - 4 / 3) ^ 2) = (2 : ℂ) ^ (4 / 3 - s) :=
    mul_div_cancel₀ _ (pow_ne_zero 2 hne)
  rw [completedThetaSq, hFdef]
  simp only
  linear_combination (-(periodArea⁻¹ * (s - 4 / 3))) * hs2 +
    (-(periodArea⁻¹ * (thetaCoeff ^ 2 * clearedScatterTotal s))) * key

/-- **The squared theta series has a double pole at `4/3`.** `M(s) D(s)`, `D(s) = Σ_{h≠0} T_s(h)²
(4π|ξ_h|)^{−s}`, continues analytically to `{1 < Re s < 13/3, Im s > 0}` and to a punctured neighbourhood
of `4/3`, and `(s − 4/3)² M(s) D(s) → 108 π³ r³ ≠ 0` there. -/
theorem thetaSqDirichlet_double_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → Λ s = besselSqMellin s * thetaSqDirichlet s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3)) ∧
      (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3 ≠ 0) := by
  refine ⟨completedThetaSq, completedThetaSq_eq, completedThetaSq_differentiableAt,
    completedThetaSq_differentiableAt_near, ?_, ?_⟩
  · have h := completedThetaSq_double_pole
    rwa [show 12 * (Real.pi : ℂ) * thetaCoeff ^ 2 * constantArithmeticResidue =
      108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3 by rw [thetaCoeff]; ring] at h
  · have hr := constantArithmeticResidue_ne_zero
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hπ)) (pow_ne_zero 3 hr)

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
