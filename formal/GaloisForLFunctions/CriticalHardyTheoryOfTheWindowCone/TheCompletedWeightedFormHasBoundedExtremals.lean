import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheWindowSolutionsAreBounded
import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheMarginLawOfTheWindowCone
import GaloisForLFunctions.RHTower.WeilFullConeCCMBridge

/-!
# The completed `W_λ` has bounded extremals with the exact edge law

For an arbitrary real weight `λ` and a window `[−a, a]`, the Weil form completes to a closed form on
the archimedean domain,

  `Q^λ(u, v) = ⟨u, v⟩_form + ⟨B^λ u, v⟩`,  `B^λ = scalar + polar − Σ_{n ≤ e^{2a}} λ(n) T(n)`,

which agrees with `W_λ` on smooth interior tests (`weightedForm_smooth_re`).

* `weighted_window_bounded_and_edge_law`: an equation `Q^λ(u, ·) = ⟨g, ·⟩` whose forcing is dominated by
  `C₀ + c₀|u|` has an essentially bounded solution with the exact edge law `u(∓a ± t) √log(1/t) → ∫ K f`.
  The logarithmic forcing of `Q^λ` is literally dominated by a constant and translates of `u`: this
  discharges the domination hypothesis of `window_edge_law` for every weight.
* `exists_weightedGroundState`: the form has a ground state at its Rayleigh floor `μ_λ(a)`, for every `λ`.
  It is bounded and has the edge law (`weightedGroundState_bounded_and_edge_law`).
* `HasMargin.le_weightedGroundEnergy`: a margin of `W_λ` on smooth tests lies below `μ_λ(a)`.
* `exists_weightedRiesz`: if `μ_λ(a) > 0`, every `g` has a Riesz vector, which is bounded with the edge law
  when `g` is bounded (`weightedRiesz_bounded_and_edge_law`).
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
open _root_.RHTower _root_.Zeta23 CanonicalSystemOfTheWindowTower HTGeometry

/-! ### The form -/

/-- The prime operator of the weight `λ` on the window. -/
def weightedPrimeOperator (lam : ℕ → ℝ) (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊, ((lam n : ℝ) : ℂ) • ccmPrimeTransportOperator a n

theorem weightedPrimeOperator_isSelfAdjoint (lam : ℕ → ℝ) (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (weightedPrimeOperator lam a) := by
  classical
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold weightedPrimeOperator
  generalize Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊ = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
    rw [Finset.sum_insert hn, ContinuousLinearMap.adjoint.map_add, ih]
    have hnself := ccmPrimeTransportOperator_isSelfAdjoint a n
    rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hnself
    rw [ContinuousLinearMap.adjoint.map_smulₛₗ, hnself, Complex.conj_ofReal]

/-- The bounded remainder of `Q^λ`: the scalar, the polar pair and the prime translations of `λ`. -/
def weightedRemainder (lam : ℕ → ℝ) (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ccmArchimedeanRemainderScalar • 1 + ccmPolarOperator a - weightedPrimeOperator lam a

theorem weightedRemainder_isSelfAdjoint (lam : ℕ → ℝ) (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (weightedRemainder lam a) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold weightedRemainder
  rw [ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint.map_add]
  have hpolar := ccmPolarOperator_isSelfAdjoint a
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hpolar
  have hprime := weightedPrimeOperator_isSelfAdjoint lam a
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hprime
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ, ContinuousLinearMap.adjoint_one, hpolar, hprime,
    star_ccmArchimedeanRemainderScalar]

/-- The completed form of `W_λ` on the archimedean domain of the window. -/
def weightedForm (lam : ℕ → ℝ) (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) : ℂ :=
  inner ℂ u v + inner ℂ (weightedRemainder lam a (ccmArchimedeanFormToAperture a u))
    (ccmArchimedeanFormToAperture a v)

private theorem weightedForm_eq_sub (lam : ℕ → ℝ) (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    weightedForm lam a u v = ccmRestrictedWeilForm a u v -
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        (((lam n - ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
          inner ℂ (ccmPrimeTransportOperator a n (ccmArchimedeanFormToAperture a u))
            (ccmArchimedeanFormToAperture a v) := by
  obtain ⟨f, hf⟩ : ∃ f, f = ccmArchimedeanFormToAperture a u := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = ccmArchimedeanFormToAperture a v := ⟨_, rfl⟩
  rw [weightedForm, ccmRestrictedWeilForm, ← hf, ← hg]
  have hl : inner ℂ (weightedRemainder lam a f) g =
      inner ℂ (ccmRestrictedWeilBoundedRemainder a f) g -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          (((lam n - ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
            inner ℂ (ccmPrimeTransportOperator a n f) g := by
    have hs : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊, ((lam n : ℝ) : ℂ) • ccmPrimeTransportOperator a n) =
        (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) • ccmPrimeTransportOperator a n) +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          (((lam n - ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) • ccmPrimeTransportOperator a n := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← add_smul]
      congr 1
      push_cast
      ring
    have hop : weightedRemainder lam a = ccmRestrictedWeilBoundedRemainder a -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          (((lam n - ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) • ccmPrimeTransportOperator a n := by
      unfold weightedRemainder ccmRestrictedWeilBoundedRemainder weightedPrimeOperator
        ccmFinitePrimeOperator
      rw [hs]
      abel
    rw [hop, sub_apply, inner_sub_left, sum_apply, sum_inner]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [smul_apply, inner_smul_left, Complex.conj_ofReal]
  rw [hl]
  ring

/-- On the diagonal `Q^λ` is the restricted source quadratic with weights `λ`. -/
theorem weightedForm_self_re (lam : ℕ → ℝ) (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    (weightedForm lam a u u).re =
      ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊ u := by
  obtain ⟨f, hf⟩ : ∃ f, f = ccmArchimedeanFormToAperture a u := ⟨_, rfl⟩
  have hsrc : ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊ u =
      ccmRestrictedWeilSourceQuadratic a u -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          (lam n - ArithmeticFunction.vonMangoldt n) * (1 / Real.sqrt n) *
            (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
              inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re := by
    rw [hf]
    unfold ccmRestrictedWeilSourceQuadraticWith ccmRestrictedWeilSourceQuadratic
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsrc, weightedForm_eq_sub, Complex.sub_re, ccmRestrictedWeilForm_self_re_eq_source, Complex.re_sum,
    ← hf]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [inner_ccmPrimeTransportOperator, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

/-- On smooth interior tests `Q^λ` is the full Weil functional of `λ` on `v ⋆ ṽ`. -/
theorem weightedForm_smooth_re (lam : ℕ → ℝ) {a : SuzukiPositiveAperture}
    (v : CCMComplexSmoothInteriorSource a) :
    (weightedForm lam a v.toCCMFormVector v.toCCMFormVector).re =
      (weilFullFunctional lam (EF.weilTest v v)).re := by
  rw [weightedForm_self_re, ccmRestrictedWeilSourceQuadraticWith_smooth_eq]

theorem continuous_weightedForm_self (lam : ℕ → ℝ) (a : SuzukiPositiveAperture) :
    Continuous fun u : CCMArchimedeanFormDomain a => (weightedForm lam a u u).re := by
  unfold weightedForm
  have hJ := (ccmArchimedeanFormToAperture a).continuous
  have hB := (weightedRemainder lam a).continuous.comp hJ
  exact Complex.continuous_re.comp ((continuous_id.inner continuous_id).add (hB.inner hJ))

/-! ### Passage to the logarithmic equation -/

/-- The logarithmic forcing of the equation `Q^λ(u, ·) = ⟨g, ·⟩`. -/
def weightedForcing (lam : ℕ → ℝ) (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (g : suzukiApertureHilbert a) : suzukiApertureHilbert a :=
  g + (logarithmicDirichletAdjustment a - weightedRemainder lam a) (ccmArchimedeanFormToAperture a u)

/-- The equation for `Q^λ` is the logarithmic equation with the forcing `weightedForcing`. -/
theorem logarithmicFullForm_of_weighted {lam : ℕ → ℝ} {a : SuzukiPositiveAperture}
    {u : CCMArchimedeanFormDomain a} {g : suzukiApertureHilbert a}
    (h : ∀ v, weightedForm lam a u v = inner ℂ g (ccmArchimedeanFormToAperture a v))
    (f : suzukiApertureHilbert a) (hf : HasLogarithmicEnergy (f : RealLineL2)) :
    logarithmicFullForm (f : RealLineL2) (ccmArchimedeanFormToAperture a u : RealLineL2) =
      inner ℂ (f : RealLineL2) (weightedForcing lam a u g : RealLineL2) := by
  obtain ⟨v, hv⟩ := exists_ccm_form_of_logarithmicEnergy a f hf
  have hE : logarithmicDirichletForm a u v =
      inner ℂ (weightedForcing lam a u g) (ccmArchimedeanFormToAperture a v) := by
    rw [logarithmicDirichletForm_eq_adjustment, weightedForcing, inner_add_left,
      sub_apply, inner_sub_left, ← h v, weightedForm]
    ring
  rw [← logarithmicFullForm_ccm_embedding] at hE
  have hc := congrArg (star : ℂ → ℂ) hE
  rw [logarithmicFullForm_conj] at hc
  have hinner : star (inner ℂ (weightedForcing lam a u g) (ccmArchimedeanFormToAperture a v)) =
      inner ℂ (ccmArchimedeanFormToAperture a v) (weightedForcing lam a u g) :=
    inner_conj_symm (𝕜 := ℂ) (E := suzukiApertureHilbert a) _ _
  rw [hinner] at hc
  change logarithmicFullForm (ccmArchimedeanFormToAperture a v : RealLineL2)
    (ccmArchimedeanFormEmbedding a u) =
      inner ℂ (ccmArchimedeanFormToAperture a v : RealLineL2)
        (weightedForcing lam a u g : RealLineL2) at hc
  rw [hv] at hc
  exact hc

/-! ### The forcing is dominated by translates -/

private theorem aperture_zero' (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∀ᵐ x ∂volume, x ∉ centralInterval a.1 → (f : RealLineL2) x = 0 := by
  have hc := indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert] at hc
  filter_upwards [hc] with x hx hn
  rw [hx, indicator_of_notMem hn]

/-- A vector supported in the window is integrable. -/
theorem integrable_aperture (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    Integrable ((f : RealLineL2) : ℝ → ℂ) :=
  ⟨(Lp.aestronglyMeasurable _), (hasFiniteIntegral_iff_enorm.mpr
    (lt_top_iff_ne_top.mpr (lintegral_enorm_aperture_ne_top a f)))⟩

private theorem norm_compression_le (a : SuzukiPositiveAperture) (A : SoninL2 →L[ℂ] SoninL2)
    (f : suzukiApertureHilbert a) :
    ∀ᵐ x ∂volume, ‖(ccmApertureCompression a A f : RealLineL2) x‖ ≤ ‖(A f.1 : RealLineL2) x‖ := by
  rw [ccmApertureCompression_val]
  filter_upwards [indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1)
    (A f.1)] with x hx
  rw [hx]
  exact norm_indicator_le_norm_self _ _

private theorem norm_primeTransport_le (a : SuzukiPositiveAperture) (n : ℕ)
    (f : suzukiApertureHilbert a) :
    ∀ᵐ x ∂volume, ‖(ccmPrimeTransportOperator a n f : RealLineL2) x‖ ≤
      (1 / Real.sqrt n) * (‖(f : RealLineL2) (x + Real.log n)‖ +
        ‖(f : RealLineL2) (x - Real.log n)‖) := by
  have hdef : (ccmPrimeTransportOperator a n f : RealLineL2) =
      ((1 / Real.sqrt n : ℝ) : ℂ) •
        (ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n)) f : RealLineL2) := rfl
  rw [hdef]
  filter_upwards [Lp.coeFn_smul ((1 / Real.sqrt n : ℝ) : ℂ)
      (ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n)) f : RealLineL2),
    norm_compression_le a (ccmSymmetricLogTranslation (Real.log n)) f,
    Lp.coeFn_add (logTranslationCLM (Real.log n) (f : RealLineL2))
      (logTranslationCLM (-Real.log n) (f : RealLineL2)),
    logarithmicTranslation_coeFn (Real.log n) (f : RealLineL2),
    logarithmicTranslation_coeFn (-Real.log n) (f : RealLineL2)] with x h1 h2 h3 h4 h5
  rw [h1, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity)
  change ‖(logTranslationCLM (Real.log n) (f : RealLineL2) +
    logTranslationCLM (-Real.log n) (f : RealLineL2)) x‖ ≤ _
  rw [h3, Pi.add_apply, h4, h5, ← sub_eq_add_neg]
  exact norm_add_le _ _

private theorem norm_weightedPrime_le (lam : ℕ → ℝ) (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    ∀ᵐ x ∂volume, ‖(weightedPrimeOperator lam a f : RealLineL2) x‖ ≤
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊, |lam n| * (1 / Real.sqrt n) *
        (‖(f : RealLineL2) (x + Real.log n)‖ + ‖(f : RealLineL2) (x - Real.log n)‖) := by
  classical
  unfold weightedPrimeOperator
  generalize Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊ = s
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, zero_apply]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
    change ‖((0 : RealLineL2) : ℝ → ℂ) x‖ ≤ 0
    rw [hx, Pi.zero_apply, norm_zero]
  | @insert n s hn ih =>
    rw [Finset.sum_insert hn, add_apply, smul_apply]
    obtain ⟨X, hX⟩ : ∃ X : suzukiApertureHilbert a, X = ((lam n : ℝ) : ℂ) • ccmPrimeTransportOperator a n f :=
      ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y : suzukiApertureHilbert a,
        Y = (∑ k ∈ s, ((lam k : ℝ) : ℂ) • ccmPrimeTransportOperator a k) f := ⟨_, rfl⟩
    rw [← hX, ← hY]
    rw [← hY] at ih
    have hc : ((X + Y : suzukiApertureHilbert a) : RealLineL2) = (X : RealLineL2) + (Y : RealLineL2) := rfl
    have hXv : (X : RealLineL2) = ((lam n : ℝ) : ℂ) • (ccmPrimeTransportOperator a n f : RealLineL2) := by
      rw [hX]
      rfl
    rw [hc]
    filter_upwards [ih, norm_primeTransport_le a n f, Lp.coeFn_add (X : RealLineL2) (Y : RealLineL2),
      Lp.coeFn_smul ((lam n : ℝ) : ℂ) (ccmPrimeTransportOperator a n f : RealLineL2)] with x h1 h2 h3 h4
    rw [Finset.sum_insert hn, h3, Pi.add_apply]
    refine (norm_add_le _ _).trans (add_le_add ?_ h1)
    rw [hXv, h4, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

private theorem norm_polar_le (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∀ᵐ x ∂volume, ‖(ccmPolarOperator a f : RealLineL2) x‖ ≤
      (‖inner ℂ (ccmPolarApertureVector a (-1 / 2)) f‖ +
        ‖inner ℂ (ccmPolarApertureVector a (1 / 2)) f‖) * Real.exp (a.1 / 2) := by
  obtain ⟨c, hc⟩ : ∃ c, c = inner ℂ (ccmPolarApertureVector a (-1 / 2)) f := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = inner ℂ (ccmPolarApertureVector a (1 / 2)) f := ⟨_, rfl⟩
  have he : (ccmPolarOperator a f : RealLineL2) =
      c • ccmPolarL2Vector a (1 / 2) + d • ccmPolarL2Vector a (-1 / 2) := by
    rw [hc, hd]
    rfl
  rw [he, ← hc, ← hd]
  have hprof {s : ℝ} (hs : |s| ≤ 1 / 2) (x : ℝ) :
      ‖(centralInterval a.1).indicator (ccmPolarProfile s) x‖ ≤ Real.exp (a.1 / 2) := by
    by_cases hx : x ∈ centralInterval a.1
    · rw [indicator_of_mem hx, ccmPolarProfile, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.mpr
      have hxa : |x| ≤ a.1 := abs_le.mpr hx
      calc
        _ ≤ |s * x| := le_abs_self _
        _ = |s| * |x| := abs_mul _ _
        _ ≤ 1 / 2 * a.1 := mul_le_mul hs hxa (abs_nonneg _) (by norm_num)
        _ = _ := by ring
    · rw [indicator_of_notMem hx, norm_zero]
      exact (Real.exp_pos _).le
  filter_upwards [Lp.coeFn_add (c • ccmPolarL2Vector a (1 / 2)) (d • ccmPolarL2Vector a (-1 / 2)),
    Lp.coeFn_smul c (ccmPolarL2Vector a (1 / 2)), Lp.coeFn_smul d (ccmPolarL2Vector a (-1 / 2)),
    ccmPolarL2Vector_coeFn a (1 / 2), ccmPolarL2Vector_coeFn a (-1 / 2)] with x h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, h4, h5, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hprof (by rw [abs_of_pos] <;> norm_num) x) (norm_nonneg _)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hprof (by norm_num [abs_of_neg]) x) (norm_nonneg _)

/-- The convolution term of the adjustment is bounded by the `L¹` norm of the source. -/
private theorem norm_archLog_le (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∀ᵐ x ∂volume, ‖(ccmApertureCompression a archLogConvolution f : RealLineL2) x‖ ≤
      3 / 4 * ∫ t, ‖(f : RealLineL2) t‖ := by
  have hi := integrable_aperture a f
  filter_upwards [norm_compression_le a archLogConvolution f, archLogConvolution_coeFn (f.1)]
    with x h1 h2
  refine h1.trans ?_
  rw [h2]
  calc
    _ ≤ ∫ t, 3 / 4 * ‖(f : RealLineL2) t‖ := by
      apply norm_integral_le_of_norm_le (hi.norm.const_mul _)
      refine Eventually.of_forall fun t => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (archLogRemainder_abs_nonneg _)]
      exact mul_le_mul_of_nonneg_right (archLogRemainder_abs_le _) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The index set of the translates of the forcing: the identity and `±log n`. -/
abbrev WeightedIndex := Option (ℕ × Bool)

/-- The translates of the forcing. -/
def weightedShift : WeightedIndex → ℝ
  | none => 0
  | some (n, true) => -Real.log n
  | some (n, false) => Real.log n

/-- The coefficients of the translates of the forcing. -/
def weightedCoeff (lam : ℕ → ℝ) (D : ℝ) : WeightedIndex → ℝ
  | none => D
  | some (n, _) => |lam n| * (1 / Real.sqrt n)

/-- The finite set of translates of the window. -/
def weightedIndexSet (a : SuzukiPositiveAperture) : Finset WeightedIndex :=
  Finset.insertNone (Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊ ×ˢ Finset.univ)

theorem weightedCoeff_nonneg (lam : ℕ → ℝ) {D : ℝ} (hD : 0 ≤ D) (j : WeightedIndex) :
    0 ≤ weightedCoeff lam D j := by
  rcases j with _ | ⟨n, _⟩
  · exact hD
  · change 0 ≤ |lam n| * (1 / Real.sqrt n)
    positivity

private theorem sum_weightedIndex (lam : ℕ → ℝ) (D : ℝ) (a : SuzukiPositiveAperture) (w : ℝ → ℝ)
    (x : ℝ) :
    ∑ j ∈ weightedIndexSet a, weightedCoeff lam D j * w (x - weightedShift j) =
      D * w x + ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊, |lam n| * (1 / Real.sqrt n) *
        (w (x + Real.log n) + w (x - Real.log n)) := by
  rw [weightedIndexSet, Finset.sum_insertNone, Finset.sum_product]
  congr 1
  · change D * w (x - 0) = _
    rw [sub_zero]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [Fintype.sum_bool]
    change |lam n| * (1 / Real.sqrt n) * w (x - -Real.log n) +
      |lam n| * (1 / Real.sqrt n) * w (x - Real.log n) = _
    rw [sub_neg_eq_add]
    ring

/-- **The forcing of `Q^λ` is dominated by a constant and translates of the solution.** The polar pair
and the bounded convolution are constants; the prime terms are the literal translates. -/
theorem weightedForcing_dominated (lam : ℕ → ℝ) (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (g : suzukiApertureHilbert a) {C₀ c₀ : ℝ}
    (hg : ∀ᵐ x ∂volume, ‖(g : RealLineL2) x‖ ≤
      C₀ + c₀ * ‖(ccmArchimedeanFormToAperture a u : RealLineL2) x‖) :
    ∀ᵐ x ∂volume, ‖(weightedForcing lam a u g : RealLineL2) x‖ ≤
      (C₀ + 3 / 4 * (∫ t, ‖(ccmArchimedeanFormToAperture a u : RealLineL2) t‖) +
        (‖inner ℂ (ccmPolarApertureVector a (-1 / 2)) (ccmArchimedeanFormToAperture a u)‖ +
          ‖inner ℂ (ccmPolarApertureVector a (1 / 2)) (ccmArchimedeanFormToAperture a u)‖) *
            Real.exp (a.1 / 2)) +
        ∑ j ∈ weightedIndexSet a,
          weightedCoeff lam (c₀ + |logarithmicFormScalar| + ‖ccmArchimedeanRemainderScalar‖) j *
            ‖(ccmArchimedeanFormToAperture a u : RealLineL2) (x - weightedShift j)‖ := by
  obtain ⟨f, hf⟩ : ∃ f, f = ccmArchimedeanFormToAperture a u := ⟨_, rfl⟩
  rw [← hf] at hg ⊢
  have hval : (weightedForcing lam a u g : RealLineL2) =
      (g : RealLineL2) + (((-logarithmicFormScalar : ℂ) • (f : RealLineL2) +
        (ccmApertureCompression a archLogConvolution f : RealLineL2)) -
        ((ccmArchimedeanRemainderScalar • (f : RealLineL2) + (ccmPolarOperator a f : RealLineL2)) -
          (weightedPrimeOperator lam a f : RealLineL2))) := by
    rw [weightedForcing, ← hf]
    rfl
  rw [hval]
  filter_upwards [hg, norm_archLog_le a f, norm_polar_le a f, norm_weightedPrime_le lam a f,
    Lp.coeFn_add (g : RealLineL2) (((-logarithmicFormScalar : ℂ) • (f : RealLineL2) +
        (ccmApertureCompression a archLogConvolution f : RealLineL2)) -
        ((ccmArchimedeanRemainderScalar • (f : RealLineL2) + (ccmPolarOperator a f : RealLineL2)) -
          (weightedPrimeOperator lam a f : RealLineL2))),
    Lp.coeFn_sub ((-logarithmicFormScalar : ℂ) • (f : RealLineL2) +
        (ccmApertureCompression a archLogConvolution f : RealLineL2))
      ((ccmArchimedeanRemainderScalar • (f : RealLineL2) + (ccmPolarOperator a f : RealLineL2)) -
          (weightedPrimeOperator lam a f : RealLineL2)),
    Lp.coeFn_add ((-logarithmicFormScalar : ℂ) • (f : RealLineL2))
      (ccmApertureCompression a archLogConvolution f : RealLineL2),
    Lp.coeFn_sub (ccmArchimedeanRemainderScalar • (f : RealLineL2) +
        (ccmPolarOperator a f : RealLineL2)) (weightedPrimeOperator lam a f : RealLineL2),
    Lp.coeFn_add (ccmArchimedeanRemainderScalar • (f : RealLineL2))
      (ccmPolarOperator a f : RealLineL2),
    Lp.coeFn_smul (-logarithmicFormScalar : ℂ) (f : RealLineL2),
    Lp.coeFn_smul ccmArchimedeanRemainderScalar (f : RealLineL2)]
    with x h1 h2 h3 h4 e1 e2 e3 e4 e5 e6 e7
  rw [e1, Pi.add_apply, e2, Pi.sub_apply, e3, Pi.add_apply, e4, Pi.sub_apply, e5, Pi.add_apply, e6,
    e7, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    sum_weightedIndex lam _ a (fun y => ‖(f : RealLineL2) y‖) x]
  have hn1 : ‖(-(logarithmicFormScalar : ℂ))‖ = |logarithmicFormScalar| := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hmain : ∀ A B C D E F : ℂ, ‖A + (B + C - (D + E - F))‖ ≤
      ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ + ‖F‖ := by
    intro A B C D E F
    have e : A + (B + C - (D + E - F)) = A + B + C + (-D) + (-E) + F := by ring
    rw [e]
    calc
      _ ≤ ‖A + B + C + (-D) + (-E)‖ + ‖F‖ := norm_add_le _ _
      _ ≤ ‖A + B + C + (-D)‖ + ‖-E‖ + ‖F‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖A + B + C‖ + ‖-D‖ + ‖-E‖ + ‖F‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖A + B‖ + ‖C‖ + ‖-D‖ + ‖-E‖ + ‖F‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖-D‖ + ‖-E‖ + ‖F‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by rw [norm_neg, norm_neg]
  refine (hmain _ _ _ _ _ _).trans ?_
  rw [norm_mul, norm_mul, hn1]
  linarith only [h1, h2, h3, h4]

/-! ### The edge law for every weight -/

/-- The conclusion of the window theory: `U` is essentially bounded, and at both ends of the window it
agrees with the Green representative of its localized forcing, with the exact normalized limit. -/
def HasExactEdgeLaw (a : SuzukiPositiveAperture) (U F : suzukiApertureHilbert a) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂volume, ‖(U : RealLineL2) x‖ ≤ C) ∧
    (∀ᵐ x ∂volume, x ≤ 0 → (U : RealLineL2) x =
      logarithmicGreenRepresentative (logarithmicApertureLeftForcing a U F) (x + a.1)) ∧
    Tendsto (fun t : ℝ => logarithmicGreenRepresentative (logarithmicApertureLeftForcing a U F) t *
        (Real.sqrt (Real.log (1 / t)) : ℂ)) (𝓝[>] (0 : ℝ))
      (nhds (∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
        (logarithmicApertureLeftForcing a U F : RealLineL2) y)) ∧
    (∀ᵐ x ∂volume, 0 ≤ x → (U : RealLineL2) x = logarithmicGreenRepresentative
      (logarithmicApertureLeftForcing a (logarithmicApertureReflection a U)
        (logarithmicApertureReflection a F)) (a.1 - x)) ∧
    Tendsto (fun t : ℝ => logarithmicGreenRepresentative
        (logarithmicApertureLeftForcing a (logarithmicApertureReflection a U)
          (logarithmicApertureReflection a F)) t *
        (Real.sqrt (Real.log (1 / t)) : ℂ)) (𝓝[>] (0 : ℝ))
      (nhds (∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
        (logarithmicApertureLeftForcing a (logarithmicApertureReflection a U)
          (logarithmicApertureReflection a F) : RealLineL2) y))

/-- **Solutions of `Q^λ` are bounded and have the exact edge law, for every weight `λ`.** -/
theorem weighted_window_bounded_and_edge_law (lam : ℕ → ℝ) (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (g : suzukiApertureHilbert a) {C₀ c₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hc₀ : 0 ≤ c₀)
    (hg : ∀ᵐ x ∂volume, ‖(g : RealLineL2) x‖ ≤
      C₀ + c₀ * ‖(ccmArchimedeanFormToAperture a u : RealLineL2) x‖)
    (h : ∀ v, weightedForm lam a u v = inner ℂ g (ccmArchimedeanFormToAperture a v)) :
    HasExactEdgeLaw a (ccmArchimedeanFormToAperture a u) (weightedForcing lam a u g) := by
  have hU : HasLogarithmicEnergy (ccmArchimedeanFormToAperture a u : RealLineL2) :=
    hasLogarithmicEnergy_ccm_form a u
  have hsolve := logarithmicFullForm_of_weighted h
  have hD : 0 ≤ c₀ + |logarithmicFormScalar| + ‖ccmArchimedeanRemainderScalar‖ := by positivity
  have hI : 0 ≤ ∫ t, ‖(ccmArchimedeanFormToAperture a u : RealLineL2) t‖ :=
    integral_nonneg fun t => norm_nonneg _
  have hC : 0 ≤ C₀ + 3 / 4 * (∫ t, ‖(ccmArchimedeanFormToAperture a u : RealLineL2) t‖) +
      (‖inner ℂ (ccmPolarApertureVector a (-1 / 2)) (ccmArchimedeanFormToAperture a u)‖ +
        ‖inner ℂ (ccmPolarApertureVector a (1 / 2)) (ccmArchimedeanFormToAperture a u)‖) *
          Real.exp (a.1 / 2) := by positivity
  have hdom := weightedForcing_dominated lam a u g hg
  exact ⟨exists_ae_norm_le_of_window_equation a _ _ hU hsolve (weightedIndexSet a) weightedShift
      (weightedCoeff_nonneg lam hD) hC hdom,
    window_edge_law a _ _ hU hsolve (weightedIndexSet a) weightedShift
      (weightedCoeff_nonneg lam hD) hC hdom⟩

/-! ### Ground states -/

/-- The Rayleigh floor of `Q^λ` on the window. -/
def weightedGroundEnergy (lam : ℕ → ℝ) (a : SuzukiPositiveAperture) : ℝ :=
  ‖boundedPerturbedFormCovariance (ccmArchimedeanFormToAperture a) (weightedRemainder lam a)
      (weightedRemainder_isSelfAdjoint lam a)‖⁻¹ -
    boundedPerturbedFormShift (weightedRemainder lam a)

/-- `μ_λ(a)` is a floor of the form on the whole domain. -/
theorem weightedGroundEnergy_mul_le (lam : ℕ → ℝ) (a : SuzukiPositiveAperture)
    (v : CCMArchimedeanFormDomain a) :
    weightedGroundEnergy lam a * ‖ccmArchimedeanFormToAperture a v‖ ^ 2 ≤
      (weightedForm lam a v v).re :=
  boundedPerturbedForm_ground_mul_norm_sq_le (ccmArchimedeanFormToAperture a)
    (weightedRemainder lam a) (weightedRemainder_isSelfAdjoint lam a)
    (ccmArchimedeanFormToAperture_injective a) (denseRange_ccmArchimedeanFormToAperture a) v

/-- **`W_λ` has a ground state on every window, for every weight.** -/
theorem exists_weightedGroundState (lam : ℕ → ℝ) (a : SuzukiPositiveAperture) :
    ∃ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormToAperture a u ≠ 0 ∧
      ∀ v, weightedForm lam a u v = (weightedGroundEnergy lam a : ℂ) *
        inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) := by
  obtain ⟨J, hJ⟩ : ∃ J, J = ccmArchimedeanFormToAperture a := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = weightedRemainder lam a := ⟨_, rfl⟩
  have hBs : IsSelfAdjoint B := hB ▸ weightedRemainder_isSelfAdjoint lam a
  obtain ⟨e, hene, he⟩ := boundedPerturbedFormCovariance_exists_norm_eigenvector J B hBs
    (hJ ▸ ccmArchimedeanFormToAperture_injective a) (hJ ▸ denseRange_ccmArchimedeanFormToAperture a)
    (hJ ▸ isCompactOperator_ccmArchimedeanFormToAperture a)
  obtain ⟨C, hC⟩ : ∃ C, C = boundedPerturbedFormCovariance J B hBs := ⟨_, rfl⟩
  rw [← hC] at he
  have hCinj : Function.Injective C := hC ▸ boundedPerturbedFormCovariance_injective J B hBs
    (hJ ▸ ccmArchimedeanFormToAperture_injective a) (hJ ▸ denseRange_ccmArchimedeanFormToAperture a)
  have hnorm : ‖C‖ ≠ 0 := by
    intro h0
    rw [h0, Complex.ofReal_zero, zero_smul] at he
    exact hene (hCinj (he.trans (map_zero C).symm))
  have hnormC : ((‖C‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnorm
  obtain ⟨y, hy⟩ : ∃ y, y = ((‖C‖ : ℝ) : ℂ)⁻¹ • e := ⟨_, rfl⟩
  have hCy : C y = e := by
    rw [hy, map_smul, he, smul_smul, inv_mul_cancel₀ hnormC, one_smul]
  obtain ⟨u, hu⟩ : ∃ u, u = boundedPerturbedFormRieszInv J B hBs (J.adjoint y) := ⟨_, rfl⟩
  have hJu : J u = e := by
    rw [← hCy, hC, hu]
    rfl
  have hRu : boundedPerturbedFormRiesz J B u = J.adjoint y := by
    rw [hu]
    exact (boundedPerturbedFormRieszEquiv J B hBs).apply_symm_apply (J.adjoint y)
  refine ⟨u, ?_, fun v => ?_⟩
  · rw [← hJ, hJu]
    exact hene
  have hform : inner ℂ y (J v) = inner ℂ u v + inner ℂ (B (J u)) (J v) +
      (boundedPerturbedFormShift B : ℂ) * inner ℂ (J u) (J v) := by
    rw [← J.adjoint_inner_left, ← hRu, boundedPerturbedFormRiesz_apply, inner_add_left,
      inner_add_left, inner_smul_left, J.adjoint_inner_left, J.adjoint_inner_left]
    simp [boundedPerturbedFormShift]
  have hyv : inner ℂ y (J v) = ((‖C‖ : ℝ) : ℂ)⁻¹ * inner ℂ (J u) (J v) := by
    have hsm := inner_smul_left (𝕜 := ℂ) e (J v) (((‖C‖ : ℝ) : ℂ)⁻¹)
    rw [map_inv₀, Complex.conj_ofReal] at hsm
    rw [hy, hJu, hsm]
  rw [weightedForm, weightedGroundEnergy, ← hJ, ← hB, ← hC]
  push_cast
  rw [sub_mul, ← hyv, hform]
  ring

/-- **The ground state of `Q^λ` is bounded and has the exact edge law, for every weight.** -/
theorem weightedGroundState_bounded_and_edge_law (lam : ℕ → ℝ) (a : SuzukiPositiveAperture) :
    ∃ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormToAperture a u ≠ 0 ∧
      (∀ v, weightedForm lam a u v = (weightedGroundEnergy lam a : ℂ) *
        inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v)) ∧
      HasExactEdgeLaw a (ccmArchimedeanFormToAperture a u)
        (weightedForcing lam a u ((weightedGroundEnergy lam a : ℂ) •
          ccmArchimedeanFormToAperture a u)) := by
  obtain ⟨u, hne, hu⟩ := exists_weightedGroundState lam a
  refine ⟨u, hne, hu, ?_⟩
  obtain ⟨U, hU⟩ : ∃ U, U = ccmArchimedeanFormToAperture a u := ⟨_, rfl⟩
  have hg : ∀ᵐ x ∂volume, ‖(((weightedGroundEnergy lam a : ℂ) • U : suzukiApertureHilbert a) :
      RealLineL2) x‖ ≤ 0 + |weightedGroundEnergy lam a| * ‖(U : RealLineL2) x‖ := by
    filter_upwards [Lp.coeFn_smul (weightedGroundEnergy lam a : ℂ) (U : RealLineL2)] with x hx
    change ‖((weightedGroundEnergy lam a : ℂ) • (U : RealLineL2) : RealLineL2) x‖ ≤ _
    rw [hx, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, zero_add]
  have h : ∀ v, weightedForm lam a u v = inner ℂ ((weightedGroundEnergy lam a : ℂ) • U)
      (ccmArchimedeanFormToAperture a v) := fun v => by
    rw [hu v, hU, inner_smul_left, Complex.conj_ofReal]
  rw [← hU] at hg ⊢
  rw [hU] at hg h ⊢
  exact weighted_window_bounded_and_edge_law lam a u _ le_rfl (abs_nonneg _) hg h

/-! ### Margins -/

/-- A margin of `W_λ` on the window is a floor of the completed form. -/
theorem HasMargin.le_weightedForm {lam : ℕ → ℝ} {a : SuzukiPositiveAperture} {m : ℝ}
    (h : HasMargin lam a.1 m) (u : CCMArchimedeanFormDomain a) :
    m * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤ (weightedForm lam a u u).re := by
  refine (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).induction_on u
    (isClosed_le ((continuous_const.mul
      (((ccmArchimedeanFormToAperture a).continuous.norm).pow 2)))
      (continuous_weightedForm_self lam a)) fun v => ?_
  rw [weightedForm_smooth_re]
  have hv2 : ContDiff ℝ 2 (v : ℝ → ℂ) := v.smooth.of_le (WithTop.coe_le_coe.mpr le_top)
  have hs : tsupport (v : ℝ → ℂ) ⊆ Icc (-a.1) a.1 := fun x hx => by
    have := v.tsupport_subset hx
    exact ⟨this.1.le, this.2.le⟩
  have hm := h v hv2 hs
  have hnorm : ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 = ∫ t, ‖v t‖ ^ 2 := by
    change ‖((ccmArchimedeanFormToAperture a v.toCCMFormVector : suzukiApertureHilbert a) :
      RealLineL2)‖ ^ 2 = _
    rw [Lp_two_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [v.toCCMFormVector_physical_coeFn] with x hx
    rw [hx]
  rwa [hnorm]

/-- **A margin of `W_λ` lies below the Rayleigh floor of its completion.** -/
theorem HasMargin.le_weightedGroundEnergy {lam : ℕ → ℝ} {a : SuzukiPositiveAperture} {m : ℝ}
    (h : HasMargin lam a.1 m) : m ≤ weightedGroundEnergy lam a := by
  obtain ⟨u, hne, hu⟩ := exists_weightedGroundState lam a
  have hm := h.le_weightedForm u
  have he : (weightedForm lam a u u).re = weightedGroundEnergy lam a *
      ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
    rw [hu u, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [he] at hm
  have hpos : 0 < ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
    have := norm_pos_iff.mpr hne
    positivity
  exact le_of_mul_le_mul_right hm hpos

/-! ### Riesz vectors inside the cone -/

/-- The Riesz operator of the unshifted form. -/
private def weightedRiesz₀ (lam : ℕ → ℝ) (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a :=
  1 + (ccmArchimedeanFormToAperture a).adjoint ∘L weightedRemainder lam a ∘L
    ccmArchimedeanFormToAperture a

private theorem inner_weightedRiesz₀ (lam : ℕ → ℝ) (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    inner ℂ (weightedRiesz₀ lam a u) v = weightedForm lam a u v := by
  change inner ℂ (u + (ccmArchimedeanFormToAperture a).adjoint
    (weightedRemainder lam a (ccmArchimedeanFormToAperture a u))) v = _
  rw [inner_add_left, ContinuousLinearMap.adjoint_inner_left]
  rfl

private theorem weightedRiesz₀_isSelfAdjoint (lam : ℕ → ℝ) (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (weightedRiesz₀ lam a) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  have hB := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (weightedRemainder_isSelfAdjoint lam a))
  change inner ℂ (weightedRiesz₀ lam a u) v = inner ℂ u (weightedRiesz₀ lam a v)
  rw [inner_weightedRiesz₀, ← inner_conj_symm u, inner_weightedRiesz₀]
  simp only [weightedForm, map_add, inner_conj_symm]
  congr 1
  rw [inner_conj_symm]
  exact hB _ _

/-- Inside the cone the Riesz operator has a lower bound. -/
private theorem norm_weightedRiesz₀_lower (lam : ℕ → ℝ) (a : SuzukiPositiveAperture)
    (hμ : 0 < weightedGroundEnergy lam a) (u : CCMArchimedeanFormDomain a) :
    ‖u‖ ≤ (1 + ‖weightedRemainder lam a‖ / weightedGroundEnergy lam a) *
      ‖weightedRiesz₀ lam a u‖ := by
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = weightedGroundEnergy lam a := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = ‖weightedRemainder lam a‖ := ⟨_, rfl⟩
  rw [← hμd] at hμ ⊢
  rw [← hβ]
  have hβ0 : 0 ≤ β := hβ ▸ norm_nonneg _
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (weightedForm lam a u u).re := ⟨_, rfl⟩
  have hfloor := weightedGroundEnergy_mul_le lam a u
  rw [← hμd, ← hQ] at hfloor
  have hupper : Q ≤ ‖weightedRiesz₀ lam a u‖ * ‖u‖ := by
    rw [hQ, ← inner_weightedRiesz₀]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  obtain ⟨f, hf⟩ : ∃ f, f = ccmArchimedeanFormToAperture a u := ⟨_, rfl⟩
  rw [← hf] at hfloor
  have hlower : ‖u‖ ^ 2 - β * ‖f‖ ^ 2 ≤ Q := by
    rw [hQ, weightedForm, Complex.add_re, ← hf]
    have h1 : (inner ℂ u u).re = ‖u‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u]
      norm_cast
    have h2 : |(inner ℂ (weightedRemainder lam a f) f).re| ≤ β * ‖f‖ ^ 2 := by
      calc
        _ ≤ ‖inner ℂ (weightedRemainder lam a f) f‖ := Complex.abs_re_le_norm _
        _ ≤ ‖weightedRemainder lam a f‖ * ‖f‖ := norm_inner_le_norm _ _
        _ ≤ (‖weightedRemainder lam a‖ * ‖f‖) * ‖f‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ = _ := by rw [hβ]; ring
    rw [h1]
    linarith only [(abs_le.mp h2).1]
  have hf2 : ‖f‖ ^ 2 ≤ Q / μ := by
    rw [le_div_iff₀ hμ]
    linarith only [hfloor]
  have hsq : ‖u‖ ^ 2 ≤ (1 + β / μ) * Q := by
    have hb : β * ‖f‖ ^ 2 ≤ β * (Q / μ) := mul_le_mul_of_nonneg_left hf2 hβ0
    have he : (1 + β / μ) * Q = Q + β * (Q / μ) := by ring
    rw [he]
    linarith only [hlower, hb]
  have hfac : 0 ≤ 1 + β / μ := by positivity
  have hmain : ‖u‖ ^ 2 ≤ ((1 + β / μ) * ‖weightedRiesz₀ lam a u‖) * ‖u‖ :=
    hsq.trans (by
      have := mul_le_mul_of_nonneg_left hupper hfac
      linarith only [this])
  by_cases hu : ‖u‖ = 0
  · rw [hu]
    positivity
  have hpos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
  rw [sq] at hmain
  exact le_of_mul_le_mul_right hmain hpos

/-- **Riesz vectors exist inside the cone.** If `μ_λ(a) > 0`, every `g` is represented. -/
theorem exists_weightedRiesz (lam : ℕ → ℝ) (a : SuzukiPositiveAperture)
    (hμ : 0 < weightedGroundEnergy lam a) (g : suzukiApertureHilbert a) :
    ∃ u : CCMArchimedeanFormDomain a,
      ∀ v, weightedForm lam a u v = inner ℂ g (ccmArchimedeanFormToAperture a v) := by
  obtain ⟨R, hR⟩ : ∃ R, R = weightedRiesz₀ lam a := ⟨_, rfl⟩
  have hc : 0 ≤ 1 + ‖weightedRemainder lam a‖ / weightedGroundEnergy lam a := by positivity
  have hanti : AntilipschitzWith (Real.toNNReal (1 + ‖weightedRemainder lam a‖ /
      weightedGroundEnergy lam a)) R := by
    rw [hR]
    apply ContinuousLinearMap.antilipschitz_of_bound
    intro u
    rw [Real.coe_toNNReal _ hc]
    exact norm_weightedRiesz₀_lower lam a hμ u
  have hclosed : IsClosed (R.range : Set (CCMArchimedeanFormDomain a)) :=
    hanti.isClosed_range R.uniformContinuous
  have hself : IsSelfAdjoint R := hR ▸ weightedRiesz₀_isSelfAdjoint lam a
  have hinj : Function.Injective R := hanti.injective
  have hdense : Dense (R.range : Set (CCMArchimedeanFormDomain a)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      R.orthogonal_range, hself.adjoint_eq]
    exact LinearMap.ker_eq_bot.mpr hinj
  have hmem : (ccmArchimedeanFormToAperture a).adjoint g ∈ R.range := by
    have h1 := hdense ((ccmArchimedeanFormToAperture a).adjoint g)
    rwa [hclosed.closure_eq] at h1
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, fun v => ?_⟩
  rw [← inner_weightedRiesz₀, ← hR]
  change inner ℂ (R u) v = _
  rw [hu, ContinuousLinearMap.adjoint_inner_left]

/-- **Riesz vectors of bounded forcing inside the cone are bounded and have the edge law.** -/
theorem weightedRiesz_bounded_and_edge_law (lam : ℕ → ℝ) (a : SuzukiPositiveAperture)
    (hμ : 0 < weightedGroundEnergy lam a) (g : suzukiApertureHilbert a) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hg : ∀ᵐ x ∂volume, ‖(g : RealLineL2) x‖ ≤ C₀) :
    ∃ u : CCMArchimedeanFormDomain a,
      (∀ v, weightedForm lam a u v = inner ℂ g (ccmArchimedeanFormToAperture a v)) ∧
      HasExactEdgeLaw a (ccmArchimedeanFormToAperture a u) (weightedForcing lam a u g) := by
  obtain ⟨u, hu⟩ := exists_weightedRiesz lam a hμ g
  refine ⟨u, hu, weighted_window_bounded_and_edge_law lam a u g hC₀ le_rfl
    (hg.mono fun x hx => ?_) hu⟩
  rw [zero_mul, add_zero]
  exact hx

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
