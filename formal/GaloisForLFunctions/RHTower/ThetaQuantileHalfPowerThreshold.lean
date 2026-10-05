import GaloisForLFunctions.RHTower.ThetaQuantileFlatNormalForm
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments

/-!
# The critical half-power of the theta one-port metric

On the mean-zero space `H₀` the metric `T = P M_h P` is a positive operator, so its real powers
`T^α` are defined by the continuous functional calculus.  The reflection `t ↦ 1 − t` commutes
with `T` (the theta source is even), and on the odd sector `T` is multiplication by `h`; uniform
polynomial approximation of `x ↦ x^α` then shows that `T^α` is multiplication by `h^α` there.  As
`Q` is odd,

`Q ∈ range(T^α) ⟺ ∫ Q²/h^{2α} < ∞ ⟺ ∫ x² ρ^{1−2α} < ∞ ⟺ α < 1/2`.

The output vector `b = P h` lies in `range(T^{1/2})` by the positive-operator range criterion
(`|⟨b, f⟩| ≤ ‖ρ‖₂ ‖T^{1/2} f‖`), but not in `range(T)`: `Tf = b` would force `f = 1 + c q`, and
`q ∉ L²(0,1)`.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open HedenmalmThetaSource HedenmalmQuantile HedenmalmHilbertSchmidt GaloisForLFunctions.HTGeometry

local notation "ThetaL2" => Lp ℂ 2 unitIntervalMeasure

/-! ## The positive-operator range criterion -/

/-- **Range criterion.**  If `|⟨b, f⟩| ≤ K ‖S f‖` for a self-adjoint `S`, then `b ∈ range S`. -/
theorem mem_range_of_norm_inner_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {S : E →L[ℂ] E} (hS : IsSelfAdjoint S) {b : E} {K : ℝ}
    (hK : ∀ f, ‖⟪b, f⟫_ℂ‖ ≤ K * ‖S f‖) : ∃ w, S w = b := by
  let S' : E →ₗ[ℂ] E := S
  let L : E →ₗ[ℂ] ℂ := innerₛₗ ℂ b
  have hker : LinearMap.ker S' ≤ LinearMap.ker L := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    have h := hK f
    rw [show S f = S' f from rfl, hf, norm_zero, mul_zero] at h
    exact norm_le_zero_iff.1 h
  let ℓ₁ : LinearMap.range S' →ₗ[ℂ] ℂ :=
    ((LinearMap.ker S').liftQ L hker).comp (LinearMap.quotKerEquivRange S').symm.toLinearMap
  have hℓ₁ : ∀ f, ℓ₁ ⟨S' f, LinearMap.mem_range_self S' f⟩ = ⟪b, f⟫_ℂ := by
    intro f
    have h : (LinearMap.quotKerEquivRange S').symm ⟨S' f, LinearMap.mem_range_self S' f⟩ =
        Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [ℓ₁, LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.liftQ_apply]
    rfl
  have hK0 : 0 ≤ K ∨ ∀ f, ⟪b, f⟫_ℂ = 0 := by
    rcases le_or_gt 0 K with h | h
    · exact Or.inl h
    · right; intro f
      have := hK f
      have h2 : K * ‖S f‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h.le (norm_nonneg _)
      exact norm_le_zero_iff.1 (this.trans h2)
  rcases hK0 with hK0 | hzero
  · let ℓ : StrongDual ℂ (LinearMap.range S') := LinearMap.mkContinuous ℓ₁ K fun y => by
      obtain ⟨f, hf⟩ := y.2
      have hy : y = ⟨S' f, LinearMap.mem_range_self S' f⟩ := Subtype.ext hf.symm
      rw [hy, hℓ₁]
      exact hK f
    obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range S') ℓ
    set w := (InnerProductSpace.toDual ℂ E).symm g
    refine ⟨w, ext_inner_right ℂ fun f => ?_⟩
    have h1 : ⟪w, S f⟫_ℂ = ⟪b, f⟫_ℂ := by
      rw [InnerProductSpace.toDual_symm_apply]
      have := hg ⟨S' f, LinearMap.mem_range_self S' f⟩
      simp only at this
      rw [show S f = S' f from rfl, this]
      simp only [ℓ, LinearMap.mkContinuous_apply]
      exact hℓ₁ f
    rw [← h1, ← ContinuousLinearMap.adjoint_inner_left, hS.adjoint_eq]
  · exact ⟨0, ext_inner_right ℂ fun f => by rw [map_zero, inner_zero_left, hzero]⟩

/-- The spectrum of a positive operator of norm at most `C` lies in `[0, C]`. -/
theorem spectrum_subset_Icc_of_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [Nontrivial E] {T : E →L[ℂ] E} (h0 : 0 ≤ T) {C : ℝ} (hC : ‖T‖ ≤ C) :
    spectrum ℝ T ⊆ Icc 0 C := by
  intro x hx
  have hxC : (algebraMap ℝ ℂ x) ∈ spectrum ℂ T := (spectrum.algebraMap_mem_iff ℂ).2 hx
  have h : ‖(algebraMap ℝ ℂ x)‖ ≤ ‖T‖ := spectrum.norm_le_norm_of_mem hxC
  rw [Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs] at h
  exact ⟨spectrum_nonneg_of_nonneg h0 hx, (le_abs_self x).trans (h.trans hC)⟩

/-- **Functional calculus by polynomial approximation.**  If `v` is approximated by `p(T) g`
whenever `p` approximates `F` uniformly on an interval containing the spectrum, then
`F(T) g = v`. -/
theorem cfc_apply_eq_of_approx {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {a b : ℝ} (hspec : spectrum ℝ T ⊆ Icc a b)
    {F : ℝ → ℝ} (hF : ContinuousOn F (Icc a b)) (g v : E) {K : ℝ}
    (happrox : ∀ (p : Polynomial ℝ) (ε : ℝ), 0 < ε → (∀ x ∈ Icc a b, |p.eval x - F x| ≤ ε) →
      ‖Polynomial.aeval T p g - v‖ ≤ K * ε) :
    cfc F T g = v := by
  have hbound : ∀ ε > 0, ‖cfc F T g - v‖ ≤ (‖g‖ + K) * ε := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b F hF ε hε
    have hp' : ∀ x ∈ Icc a b, |p.eval x - F x| ≤ ε := fun x hx => (hp x hx).le
    have hdiff : ‖cfc F T - Polynomial.aeval T p‖ ≤ ε := by
      rw [← cfc_polynomial p T hT, ← cfc_sub F (fun x => p.eval x) T (hF.mono hspec)
        (p.continuous.continuousOn)]
      refine norm_cfc_le hε.le fun x hx => ?_
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hp' x (hspec hx)
    have h1 : ‖(cfc F T - Polynomial.aeval T p) g‖ ≤ ε * ‖g‖ :=
      ((cfc F T - Polynomial.aeval T p).le_opNorm g).trans (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))
    have h2 := happrox p ε hε hp'
    calc ‖cfc F T g - v‖ = ‖(cfc F T - Polynomial.aeval T p) g + (Polynomial.aeval T p g - v)‖ := by
          rw [sub_apply]; congr 1; abel
      _ ≤ ε * ‖g‖ + K * ε := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = (‖g‖ + K) * ε := by ring
  have hK : 0 ≤ ‖g‖ + K ∨ ‖cfc F T g - v‖ = 0 := by
    rcases le_or_gt 0 (‖g‖ + K) with h | h
    · exact Or.inl h
    · right
      have := hbound 1 one_pos
      exact le_antisymm (this.trans (by linarith)) (norm_nonneg _)
  rcases hK with hK | hK
  · have h0 : ‖cfc F T g - v‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖cfc F T g - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      have := hbound (‖cfc F T g - v‖ / (2 * (‖g‖ + K + 1))) (by positivity)
      have hden : 0 < 2 * (‖g‖ + K + 1) := by linarith
      rw [mul_div_assoc', le_div_iff₀ hden] at this
      nlinarith
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  · exact sub_eq_zero.1 (norm_eq_zero.1 hK)

section OperatorPowers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Real powers `T^α` of operators on a Hilbert space, by the continuous functional calculus. -/
def opRpow (T : E →L[ℂ] E) (α : ℝ) : E →L[ℂ] E := T ^ α

theorem opRpow_eq_cfc {T : E →L[ℂ] E} (h0 : 0 ≤ T) (α : ℝ) :
    opRpow T α = cfc (fun x : ℝ => x ^ α) T :=
  CFC.rpow_eq_cfc_real h0

theorem opRpow_apply_eq_of_approx {T : E →L[ℂ] E} (h0 : 0 ≤ T) (hT : IsSelfAdjoint T) {C : ℝ}
    (hspec : spectrum ℝ T ⊆ Icc 0 C) {α : ℝ} (hα : 0 ≤ α) (g v : E) {K : ℝ}
    (happrox : ∀ (p : Polynomial ℝ) (ε : ℝ), 0 < ε → (∀ x ∈ Icc 0 C, |p.eval x - x ^ α| ≤ ε) →
      ‖Polynomial.aeval T p g - v‖ ≤ K * ε) :
    opRpow T α g = v := by
  rw [opRpow_eq_cfc h0]
  exact cfc_apply_eq_of_approx hT hspec (Real.continuous_rpow_const hα).continuousOn g v happrox

theorem opRpow_commute {T R : E →L[ℂ] E} (h0 : 0 ≤ T) (h : Commute T R) (α : ℝ) :
    Commute (opRpow T α) R := by
  rw [opRpow_eq_cfc h0]
  exact h.cfc_real _

theorem isSelfAdjoint_opRpow (T : E →L[ℂ] E) (α : ℝ) : IsSelfAdjoint (opRpow T α) :=
  IsSelfAdjoint.of_nonneg CFC.rpow_nonneg

theorem opRpow_half_mul_self {T : E →L[ℂ] E} (h0 : 0 ≤ T) : opRpow T (1 / 2) * opRpow T (1 / 2) = T := by
  rw [opRpow, ← CFC.sqrt_eq_rpow]
  exact CFC.sqrt_mul_sqrt_self T h0

/-- `‖T^{1/2} f‖² = ⟨f, T f⟩`. -/
theorem norm_sq_opRpow_half {T : E →L[ℂ] E} (h0 : 0 ≤ T) (f : E) :
    (‖opRpow T (1 / 2) f‖ ^ 2 : ℝ) = (⟪f, T f⟫_ℂ).re := by
  rw [@norm_sq_eq_re_inner ℂ, ← ContinuousLinearMap.adjoint_inner_right,
    (isSelfAdjoint_opRpow T (1 / 2)).adjoint_eq]
  conv_rhs => rw [← opRpow_half_mul_self h0]
  rfl

end OperatorPowers

/-! ## The metric on the mean-zero space -/

/-- The mean-zero space `H₀`. -/
abbrev MeanZeroL2 : Type := ↥meanZeroSpace

instance : CompleteSpace MeanZeroL2 := (Submodule.isClosed_orthogonal _).completeSpace_coe

/-- `T = P M_h P` as an operator on `H₀`. -/
def meanZeroMetric : MeanZeroL2 →L[ℂ] MeanZeroL2 :=
  meanZeroSpace.orthogonalProjectionOnto ∘L thetaMetricOperator ∘L meanZeroSpace.subtypeL

theorem coe_meanZeroMetric (f : MeanZeroL2) :
    (meanZeroMetric f : ThetaL2) = meanZeroProj (thetaMetricOperator f) := by
  rw [meanZeroProj, Submodule.starProjection_apply]
  rfl

theorem coe_meanZeroMetric_eq_onePortMetric (f : MeanZeroL2) :
    (meanZeroMetric f : ThetaL2) = onePortMetric f := by
  rw [coe_meanZeroMetric, onePortMetric, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    meanZeroProj_eq_self f.2]

theorem inner_meanZeroMetric (f g : MeanZeroL2) :
    ⟪f, meanZeroMetric g⟫_ℂ = ⟪(f : ThetaL2), thetaMetricOperator g⟫_ℂ := by
  rw [Submodule.coe_inner, coe_meanZeroMetric, ← inner_meanZeroProj_left, meanZeroProj_eq_self f.2]

theorem thetaMetricOperator_inner (f g : ThetaL2) :
    ⟪thetaMetricOperator f, g⟫_ℂ = ⟪f, thetaMetricOperator g⟫_ℂ :=
  metricOperator_inner thetaSource thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le f g

theorem isSelfAdjoint_meanZeroMetric : IsSelfAdjoint meanZeroMetric := by
  refine ContinuousLinearMap.isSelfAdjoint_iff'.2 ?_
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_
  rw [← inner_conj_symm, inner_meanZeroMetric, inner_conj_symm, thetaMetricOperator_inner,
    ← inner_meanZeroMetric]

theorem nonneg_meanZeroMetric : 0 ≤ meanZeroMetric := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def]
  refine ⟨isSelfAdjoint_meanZeroMetric.isSymmetric, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← inner_conj_symm, RCLike.conj_re,
    inner_meanZeroMetric, inner_thetaMetricOperator, RCLike.re_to_complex, Complex.ofReal_re]
  exact integral_nonneg fun t => by positivity

instance : Nontrivial MeanZeroL2 :=
  ⟨⟨⟨unitFourierBasis 1, unitFourierBasis_mem_meanZeroSpace one_ne_zero⟩, 0, fun h => by
    have h1 := congrArg Subtype.val h
    have := unitFourierBasis.orthonormal.1 1
    simp only [Submodule.coe_zero] at h1
    rw [h1, norm_zero] at this
    exact zero_ne_one this⟩⟩

/-- The sup bound `C` of the metric symbol. -/
abbrev metricBound : ℝ := thetaBound / thetaSource.mass

theorem norm_thetaMetricOperator_le : ‖thetaMetricOperator‖ ≤ metricBound :=
  norm_metricOperator_le thetaSource thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le

theorem norm_meanZeroProj_apply_le (x : ThetaL2) : ‖meanZeroProj x‖ ≤ ‖x‖ := by
  rw [meanZeroProj]
  exact meanZeroSpace.norm_starProjection_apply_le x

theorem norm_meanZeroMetric_le : ‖meanZeroMetric‖ ≤ metricBound := by
  refine ContinuousLinearMap.opNorm_le_bound _ thetaMetricBound_nonneg fun f => ?_
  have h1 : ‖meanZeroMetric f‖ = ‖meanZeroProj (thetaMetricOperator f)‖ := by
    rw [← coe_meanZeroMetric]; rfl
  have h3 : ‖thetaMetricOperator f‖ ≤ metricBound * ‖(f : ThetaL2)‖ :=
    (thetaMetricOperator.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right norm_thetaMetricOperator_le (norm_nonneg _))
  rw [h1]
  exact (norm_meanZeroProj_apply_le _).trans h3

theorem spectrum_meanZeroMetric_subset : spectrum ℝ meanZeroMetric ⊆ Icc 0 metricBound :=
  spectrum_subset_Icc_of_nonneg nonneg_meanZeroMetric norm_meanZeroMetric_le

/-! ## The reflection `t ↦ 1 − t` -/

theorem measurePreserving_unitReflection :
    MeasurePreserving (fun t : ℝ => 1 - t) unitIntervalMeasure unitIntervalMeasure := by
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℝ) 1).restrict_preimage
    (measurableSet_Icc (a := (0 : ℝ)) (b := 1))
  have hpre : (fun t : ℝ => 1 - t) ⁻¹' Icc 0 1 = Icc 0 1 := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hpre] at h
  exact h

/-- The reflection `(Rg)(t) = g(1 − t)` of `L²(0,1)`. -/
def unitReflection : ThetaL2 →L[ℂ] ThetaL2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun t : ℝ => 1 - t) measurePreserving_unitReflection).toContinuousLinearMap

theorem unitReflection_ae (g : ThetaL2) :
    (unitReflection g : ℝ → ℂ) =ᵐ[unitIntervalMeasure] fun t => g (1 - t) :=
  Lp.coeFn_compMeasurePreserving g measurePreserving_unitReflection

theorem integral_comp_unitReflection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → E) :
    ∫ t, F (1 - t) ∂unitIntervalMeasure = ∫ t, F t ∂unitIntervalMeasure :=
  measurePreserving_unitReflection.integral_comp (Homeomorph.subLeft (1 : ℝ)).measurableEmbedding F

theorem ae_comp_unitReflection {P : ℝ → Prop} (h : ∀ᵐ t ∂unitIntervalMeasure, P t) :
    ∀ᵐ t ∂unitIntervalMeasure, P (1 - t) :=
  measurePreserving_unitReflection.quasiMeasurePreserving.ae h

/-- An odd function integrates to zero. -/
theorem integral_eq_zero_of_odd {F : ℝ → ℂ} (hF : ∀ᵐ t ∂unitIntervalMeasure, F (1 - t) = -F t) :
    ∫ t, F t ∂unitIntervalMeasure = 0 := by
  have h := integral_comp_unitReflection F
  rw [integral_congr_ae hF, integral_neg] at h
  have : (2 : ℂ) * ∫ t, F t ∂unitIntervalMeasure = 0 := by linear_combination -h
  simpa using this

/-- The real metric symbol `h(t) = k(Q(t))/M`. -/
abbrev metricReal (t : ℝ) : ℝ := ‖metricSymbol thetaSource t‖

theorem metricReal_one_sub {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : metricReal (1 - t) = metricReal t := by
  simp only [metricReal, norm_metricSymbol]
  rw [quantileFun_one_sub ht, thetaSource_even]

theorem ae_metricReal_one_sub : ∀ᵐ t ∂unitIntervalMeasure, metricReal (1 - t) = metricReal t := by
  filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with t ht
  exact metricReal_one_sub ht

theorem metricReal_nonneg (t : ℝ) : 0 ≤ metricReal t := norm_nonneg _

theorem metricReal_le (t : ℝ) : metricReal t ≤ metricBound := norm_metricSymbol_thetaSource_le t

theorem metricReal_pos (t : ℝ) : 0 < metricReal t :=
  norm_pos_iff.2 (metricSymbol_ne_zero thetaSource t)

/-- A vector is odd when `g(1 − t) = −g(t)`. -/
def IsOddVec (g : ThetaL2) : Prop := ∀ᵐ t ∂unitIntervalMeasure, g (1 - t) = -g t

theorem isOddVec_iff (g : ThetaL2) : IsOddVec g ↔ unitReflection g = -g := by
  constructor
  · intro hg
    apply Lp.ext
    filter_upwards [unitReflection_ae g, hg, Lp.coeFn_neg g] with t h1 h2 h3
    rw [h1, h2, h3, Pi.neg_apply]
  · intro hg
    have h := unitReflection_ae g
    rw [hg] at h
    filter_upwards [h, Lp.coeFn_neg g] with t h1 h2
    rw [← h1, h2, Pi.neg_apply]

theorem IsOddVec.mem_meanZeroSpace {g : ThetaL2} (hg : IsOddVec g) : g ∈ meanZeroSpace := by
  rw [mem_meanZeroSpace_iff, inner_constMode_eq_pinnedMean, pinnedMean]
  exact integral_eq_zero_of_odd hg

/-- An even symbol times an odd vector integrates to zero. -/
theorem integral_mul_eq_zero_of_odd {φ : ℝ → ℂ} (hφ : ∀ᵐ t ∂unitIntervalMeasure, φ (1 - t) = φ t)
    {g : ThetaL2} (hg : IsOddVec g) : ∫ t, φ t * g t ∂unitIntervalMeasure = 0 := by
  refine integral_eq_zero_of_odd ?_
  filter_upwards [hφ, hg] with t h1 h2
  rw [h1, h2, mul_neg]

/-! ## Powers of the metric on the odd sector -/

/-- `T` acts as `M_h` on every mean-zero vector whose metric image is again mean zero. -/
theorem coe_meanZeroMetric_ae {y : MeanZeroL2} {φ : ℝ → ℂ} (hy : ((y : ThetaL2) : ℝ → ℂ) =ᵐ[unitIntervalMeasure] φ)
    (h0 : ∫ t, (metricReal t : ℂ) * φ t ∂unitIntervalMeasure = 0) :
    ((meanZeroMetric y : ThetaL2) : ℝ → ℂ) =ᵐ[unitIntervalMeasure] fun t => (metricReal t : ℂ) * φ t := by
  have hin : ⟪constMode, thetaMetricOperator (y : ThetaL2)⟫_ℂ = 0 := by
    rw [inner_constMode_eq_pinnedMean, pinnedMean, ← h0]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_thetaMetricOperator (y : ThetaL2), hy] with t h1 h2
    rw [h1, h2, metricSymbol_eq_norm]
  rw [coe_meanZeroMetric, meanZeroProj_apply, hin, zero_smul, sub_zero]
  filter_upwards [coeFn_thetaMetricOperator (y : ThetaL2), hy] with t h1 h2
  rw [h1, h2, metricSymbol_eq_norm]

theorem coe_meanZeroMetric_pow_ae {g : MeanZeroL2} (hg : IsOddVec g) (n : ℕ) :
    (((meanZeroMetric ^ n) g : ThetaL2) : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      fun t => ((metricReal t ^ n : ℝ) : ℂ) * (g : ThetaL2) t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (((meanZeroMetric ((meanZeroMetric ^ n) g)) : ThetaL2) : ℝ → ℂ) =ᵐ[unitIntervalMeasure] _
    have h := coe_meanZeroMetric_ae ih ?_
    · filter_upwards [h] with t ht
      rw [ht]; push_cast; ring
    · have hφ : ∀ᵐ t ∂unitIntervalMeasure,
          (fun t => ((metricReal t : ℂ) * ((metricReal t ^ n : ℝ) : ℂ))) (1 - t) =
            (fun t => ((metricReal t : ℂ) * ((metricReal t ^ n : ℝ) : ℂ))) t := by
        filter_upwards [ae_metricReal_one_sub] with t ht
        simp only [ht]
      have h0 := integral_mul_eq_zero_of_odd
        (φ := fun t => (metricReal t : ℂ) * ((metricReal t ^ n : ℝ) : ℂ)) hφ hg
      rw [← h0]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only
      ring

theorem coe_aeval_meanZeroMetric_ae {g : MeanZeroL2} (hg : IsOddVec g) (p : Polynomial ℝ) :
    (((Polynomial.aeval meanZeroMetric p) g : ThetaL2) : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      fun t => ((p.eval (metricReal t) : ℝ) : ℂ) * (g : ThetaL2) t := by
  induction p using Polynomial.induction_on with
  | C a =>
    rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_apply,
      one_apply_eq_self, Submodule.coe_smul_of_tower]
    filter_upwards [Lp.coeFn_smul a (g : ThetaL2)] with t ht
    rw [ht, Pi.smul_apply, Polynomial.eval_C, Complex.real_smul]
  | add p q hp hq =>
    rw [map_add, add_apply, Submodule.coe_add]
    filter_upwards [Lp.coeFn_add ((Polynomial.aeval meanZeroMetric p g : MeanZeroL2) : ThetaL2)
      ((Polynomial.aeval meanZeroMetric q g : MeanZeroL2) : ThetaL2), hp, hq] with t h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Polynomial.eval_add]
    push_cast; ring
  | monomial n a _ =>
    rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, smul_apply, Submodule.coe_smul_of_tower]
    filter_upwards [Lp.coeFn_smul a (((meanZeroMetric ^ (n + 1)) g : MeanZeroL2) : ThetaL2),
      coe_meanZeroMetric_pow_ae hg (n + 1)] with t h1 h2
    rw [h1, Pi.smul_apply, h2, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Complex.real_smul]
    push_cast; ring

/-! ## `T^α` is multiplication by `h^α` on the odd sector -/

/-- The symbol `h^α`. -/
def metricPowSymbol (α : ℝ) (t : ℝ) : ℂ := ((metricReal t ^ α : ℝ) : ℂ)

theorem measurable_metricPowSymbol (α : ℝ) : Measurable (metricPowSymbol α) :=
  Complex.measurable_ofReal.comp ((measurable_metricSymbol thetaSource).norm.pow_const α)

theorem norm_metricPowSymbol_le {α : ℝ} (hα : 0 ≤ α) (t : ℝ) :
    ‖metricPowSymbol α t‖ ≤ metricBound ^ α := by
  rw [metricPowSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (metricReal_nonneg t) α)]
  exact Real.rpow_le_rpow (metricReal_nonneg t) (metricReal_le t) hα

/-- Multiplication by `h^α` on `L²(0,1)`. -/
def metricPowMul (α : ℝ) (hα : 0 ≤ α) : ThetaL2 →L[ℂ] ThetaL2 :=
  lpBoundedMulCLM (p := 2) (μ := unitIntervalMeasure) (measurable_metricPowSymbol α)
    (Real.rpow_nonneg thetaMetricBound_nonneg α) (norm_metricPowSymbol_le hα)

theorem metricPowMul_ae {α : ℝ} (hα : 0 ≤ α) (g : ThetaL2) :
    (metricPowMul α hα g : ℝ → ℂ) =ᵐ[unitIntervalMeasure] fun t => metricPowSymbol α t * g t :=
  lpBoundedMulCLM_coeFn _ _ _ g

theorem isOddVec_metricPowMul {α : ℝ} (hα : 0 ≤ α) {g : ThetaL2} (hg : IsOddVec g) :
    IsOddVec (metricPowMul α hα g) := by
  have h1 := metricPowMul_ae hα g
  have h1' := ae_comp_unitReflection h1
  filter_upwards [h1, h1', hg, ae_metricReal_one_sub] with t a b c d
  rw [b, a, c, metricPowSymbol, metricPowSymbol, d, mul_neg]

/-- **The odd-sector law** `T^α g = h^α g` for `α ≥ 0`. -/
theorem coe_rpow_meanZeroMetric {α : ℝ} (hα : 0 ≤ α) {g : MeanZeroL2} (hg : IsOddVec g) :
    ((opRpow meanZeroMetric α g : MeanZeroL2) : ThetaL2) = metricPowMul α hα g := by
  set v : MeanZeroL2 := ⟨metricPowMul α hα g, (isOddVec_metricPowMul hα hg).mem_meanZeroSpace⟩
  have hcfc : opRpow meanZeroMetric α g = v := by
    refine opRpow_apply_eq_of_approx nonneg_meanZeroMetric isSelfAdjoint_meanZeroMetric
      spectrum_meanZeroMetric_subset hα
      g v (K := ‖g‖) fun p ε hε hp => ?_
    rw [← Submodule.norm_coe, Submodule.coe_sub]
    refine (Lp.norm_le_mul_norm_of_ae_le_mul (c := ε) (g := (g : ThetaL2)) ?_).trans
      (le_of_eq (by rw [Submodule.norm_coe]; ring))
    filter_upwards [Lp.coeFn_sub (((Polynomial.aeval meanZeroMetric p) g : MeanZeroL2) : ThetaL2) (v : ThetaL2),
      coe_aeval_meanZeroMetric_ae hg p, metricPowMul_ae hα (g : ThetaL2)] with t h1 h2 h3
    erw [h1]
    rw [Pi.sub_apply, h2, show ((v : ThetaL2) : ℝ → ℂ) t = (metricPowMul α hα g : ℝ → ℂ) t from rfl, h3,
      metricPowSymbol, ← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hp _ ⟨metricReal_nonneg t, metricReal_le t⟩) (norm_nonneg _)
  rw [hcfc]

/-! ## The quantile vector and the critical power -/

theorem memLp_quantileFun : MemLp (fun t => (thetaSource.quantileFun t : ℂ)) 2 unitIntervalMeasure := by
  have hm : AEStronglyMeasurable (fun t => (thetaSource.quantileFun t : ℂ)) unitIntervalMeasure :=
    (Complex.continuous_ofReal.measurable.comp thetaSource.measurable_quantileFun).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  have h : Integrable (fun t => thetaSource.quantileFun t ^ 2) unitIntervalMeasure := by
    rw [unitIntervalMeasure_eq]; exact integrableOn_sq_quantileFun_thetaSource
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The quantile vector `Q ∈ L²(0,1)`. -/
def quantileVec : ThetaL2 := memLp_quantileFun.toLp

theorem quantileVec_ae : (quantileVec : ℝ → ℂ) =ᵐ[unitIntervalMeasure] fun t => (thetaSource.quantileFun t : ℂ) :=
  MemLp.coeFn_toLp _

theorem isOddVec_quantileVec : IsOddVec quantileVec := by
  have h1 := quantileVec_ae
  have h1' := ae_comp_unitReflection h1
  filter_upwards [h1, h1', ae_unitIntervalMeasure_mem_Ioo] with t a b c
  rw [b, a, quantileFun_one_sub c]; push_cast; ring

/-- The quantile vector as an element of `H₀`. -/
def quantileVec₀ : MeanZeroL2 := ⟨quantileVec, isOddVec_quantileVec.mem_meanZeroSpace⟩

theorem normalized_le_metricBound (x : ℝ) : thetaSource.normalized x ≤ metricBound :=
  div_le_div_of_nonneg_right (thetaSource_le x) thetaSource.mass_pos.le

/-- **The physical-space weight**: `∫ x² ρ^{1−2α} < ∞ ⟺ α < 1/2`. -/
theorem integrable_sq_mul_normalized_rpow_iff (α : ℝ) :
    Integrable (fun x : ℝ => x ^ 2 * thetaSource.normalized x ^ (1 - 2 * α)) ↔ α < 1 / 2 := by
  have hm : ∀ β : ℝ, AEStronglyMeasurable (fun x : ℝ => x ^ 2 * thetaSource.normalized x ^ β) volume :=
    fun β => ((continuous_pow 2).measurable.mul
      (continuous_normalized_theta.measurable.pow_const β)).aestronglyMeasurable
  constructor
  · intro hint
    by_contra hα
    push Not at hα
    set β := 1 - 2 * α
    have hβ : β ≤ 0 := by simp only [β]; linarith
    have hB : 0 < metricBound := (thetaSource.normalized_pos 0).trans_le (normalized_le_metricBound 0)
    have hlow : ∀ x, metricBound ^ β ≤ thetaSource.normalized x ^ β := fun x =>
      Real.rpow_le_rpow_of_nonpos (thetaSource.normalized_pos x) (normalized_le_metricBound x) hβ
    have hcB : 0 < metricBound ^ β := Real.rpow_pos_of_pos hB β
    have hsq : Integrable (fun x : ℝ => x ^ 2) := by
      refine (hint.div_const (metricBound ^ β)).mono' ((continuous_pow 2).aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x), le_div_iff₀ hcB]
      exact mul_le_mul_of_nonneg_left (hlow x) (sq_nonneg x)
    have hon : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici 1) := by
      refine (hsq.integrableOn (s := Ici 1)).mono' aestronglyMeasurable_const ?_
      refine (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun x hx => ?_)
      have hx1 : (1 : ℝ) ≤ x := hx
      rw [Real.norm_eq_abs, abs_one]
      nlinarith
    rw [integrableOn_const_iff] at hon
    rcases hon with h0 | hfin
    · simp at h0
    · rw [Real.volume_Ici] at hfin; exact lt_irrefl _ hfin
  · intro hα
    set β := 1 - 2 * α
    have hβ : 0 < β := by simp only [β]; linarith
    set A := thetaCuspDerivativeExpConstant 0 / thetaSource.mass
    have hA : 0 ≤ A := div_nonneg (thetaCuspDerivativeExpConstant_nonneg 0) thetaSource.mass_pos.le
    have hupp : ∀ x, thetaSource.normalized x ≤ A * Real.exp (-|x|) := by
      intro x
      have h := abs_thetaCuspFullSource_le x
      rw [abs_of_pos (thetaCuspFullSource_pos x)] at h
      show thetaSource.k x / thetaSource.mass ≤ _
      rw [div_le_iff₀ thetaSource.mass_pos]
      have : A * Real.exp (-|x|) * thetaSource.mass = thetaCuspDerivativeExpConstant 0 * Real.exp (-|x|) := by
        have hM := thetaSource.mass_pos.ne'
        simp only [A]; field_simp
      rw [this]; exact h
    have hdom := (HTGeometry.integrable_abs_pow_mul_exp_neg_abs 2 hβ).const_mul (A ^ β)
    refine hdom.mono' (hm β) (Eventually.of_forall fun x => ?_)
    have hρ := thetaSource.normalized_pos x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg x) (Real.rpow_nonneg hρ.le β))]
    have h1 : thetaSource.normalized x ^ β ≤ (A * Real.exp (-|x|)) ^ β :=
      Real.rpow_le_rpow hρ.le (hupp x) hβ.le
    have h2 : (A * Real.exp (-|x|)) ^ β = A ^ β * Real.exp (-β * |x|) := by
      rw [Real.mul_rpow hA (Real.exp_pos _).le, ← Real.exp_mul]; ring_nf
    rw [h2] at h1
    calc x ^ 2 * thetaSource.normalized x ^ β ≤ x ^ 2 * (A ^ β * Real.exp (-β * |x|)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg x)
      _ = A ^ β * (|x| ^ 2 * Real.exp (-β * |x|)) := by rw [sq_abs]; ring

/-- The quotient `Q/h^α`. -/
def quantilePowQuotient (α : ℝ) (t : ℝ) : ℂ := (thetaSource.quantileFun t : ℂ) / metricPowSymbol α t

theorem measurable_quantilePowQuotient (α : ℝ) : Measurable (quantilePowQuotient α) :=
  (Complex.measurable_ofReal.comp thetaSource.measurable_quantileFun).div (measurable_metricPowSymbol α)

theorem metricReal_cdfFun (x : ℝ) : metricReal (thetaSource.cdfFun x) = thetaSource.normalized x :=
  metricSymbol_cdfFun x

/-- **`∫ Q²/h^{2α} = ∫ x² ρ^{1−2α}`**, so `Q/h^α ∈ L²(0,1) ⟺ α < 1/2`. -/
theorem memLp_quantilePowQuotient_iff (α : ℝ) :
    MemLp (quantilePowQuotient α) 2 unitIntervalMeasure ↔ α < 1 / 2 := by
  have hm := (measurable_quantilePowQuotient α).aestronglyMeasurable (μ := unitIntervalMeasure)
  rw [memLp_two_iff_integrable_sq_norm hm, integrable_unitInterval_iff_cdf
    ((measurable_quantilePowQuotient α).norm.pow_const 2).aestronglyMeasurable,
    ← integrable_sq_mul_normalized_rpow_iff]
  refine integrable_congr (Eventually.of_forall fun x => ?_)
  have hρ := thetaSource.normalized_pos x
  have hpow : 0 < thetaSource.normalized x ^ α := Real.rpow_pos_of_pos hρ α
  simp only [quantilePowQuotient, metricPowSymbol, metricReal_cdfFun, thetaSource.quantile_cdfFun, smul_eq_mul]
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpow,
    div_pow, sq_abs]
  have h2 : (thetaSource.normalized x ^ α) ^ 2 = thetaSource.normalized x ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]; ring_nf
  have h3 : thetaSource.normalized x ^ (1 - 2 * α) =
      thetaSource.normalized x / thetaSource.normalized x ^ (2 * α) := by
    rw [Real.rpow_sub hρ, Real.rpow_one]
  rw [h2, h3]
  ring

/-! ## Reflection symmetry of the metric -/

theorem unitReflection_constMode : unitReflection constMode = constMode := by
  apply Lp.ext
  filter_upwards [unitReflection_ae constMode, coeFn_unitFourierBasis 0,
    ae_comp_unitReflection (coeFn_unitFourierBasis 0)] with t h1 h2 h3
  rw [h1, show (constMode : ThetaL2) = unitFourierBasis 0 from rfl, h3, h2]
  simp only [fourierMode_zero]

theorem inner_constMode_unitReflection (x : ThetaL2) : ⟪constMode, unitReflection x⟫_ℂ = ⟪constMode, x⟫_ℂ := by
  rw [inner_constMode_eq_pinnedMean, inner_constMode_eq_pinnedMean, pinnedMean, pinnedMean,
    integral_congr_ae (unitReflection_ae x), integral_comp_unitReflection (fun t => x t)]

theorem unitReflection_unitReflection (x : ThetaL2) : unitReflection (unitReflection x) = x := by
  apply Lp.ext
  filter_upwards [unitReflection_ae (unitReflection x), ae_comp_unitReflection (unitReflection_ae x)] with t h1 h2
  rw [h1, h2, sub_sub_cancel]

theorem unitReflection_meanZeroProj (x : ThetaL2) : unitReflection (meanZeroProj x) = meanZeroProj (unitReflection x) := by
  rw [meanZeroProj_apply, meanZeroProj_apply, map_sub, map_smul, unitReflection_constMode,
    inner_constMode_unitReflection]

theorem unitReflection_thetaMetricOperator (x : ThetaL2) :
    unitReflection (thetaMetricOperator x) = thetaMetricOperator (unitReflection x) := by
  apply Lp.ext
  filter_upwards [unitReflection_ae (thetaMetricOperator x), coeFn_thetaMetricOperator (unitReflection x),
    ae_comp_unitReflection (coeFn_thetaMetricOperator x), unitReflection_ae x, ae_metricReal_one_sub] with
    t h1 h2 h3 h4 h5
  have e : metricSymbol thetaSource (1 - t) = metricSymbol thetaSource t := by
    rw [metricSymbol_eq_norm (1 - t), metricSymbol_eq_norm t]
    exact congrArg (fun r : ℝ => (r : ℂ)) h5
  rw [h1, h3, h2, h4, e]

theorem unitReflection_mem {x : ThetaL2} (hx : x ∈ meanZeroSpace) : unitReflection x ∈ meanZeroSpace := by
  rw [mem_meanZeroSpace_iff, inner_constMode_unitReflection]; exact (mem_meanZeroSpace_iff x).1 hx

/-- The reflection of `H₀`. -/
def meanZeroReflection : MeanZeroL2 →L[ℂ] MeanZeroL2 :=
  (unitReflection ∘L meanZeroSpace.subtypeL).codRestrict meanZeroSpace fun y => unitReflection_mem y.2

theorem coe_meanZeroReflection (y : MeanZeroL2) : (meanZeroReflection y : ThetaL2) = unitReflection y := rfl

theorem commute_meanZeroMetric_reflection : Commute meanZeroMetric meanZeroReflection := by
  refine ContinuousLinearMap.ext fun y => Subtype.ext ?_
  change ((meanZeroMetric (meanZeroReflection y) : MeanZeroL2) : ThetaL2) =
    ((meanZeroReflection (meanZeroMetric y) : MeanZeroL2) : ThetaL2)
  rw [coe_meanZeroMetric, coe_meanZeroReflection, coe_meanZeroReflection, coe_meanZeroMetric,
    unitReflection_meanZeroProj, unitReflection_thetaMetricOperator]

theorem meanZeroReflection_quantileVec₀ : meanZeroReflection quantileVec₀ = -quantileVec₀ := by
  apply Subtype.ext
  rw [coe_meanZeroReflection, Submodule.coe_neg]
  exact (isOddVec_iff _).1 isOddVec_quantileVec

/-! ## The sharp half-power threshold -/

/-- **The critical half-power**: for `α ≥ 0`, `Q ∈ range(T^α) ⟺ α < 1/2`. -/
theorem exists_opRpow_eq_quantileVec_iff {α : ℝ} (hα : 0 ≤ α) :
    (∃ y : MeanZeroL2, opRpow meanZeroMetric α y = quantileVec₀) ↔ α < 1 / 2 := by
  constructor
  · rintro ⟨y, hy⟩
    set yo : MeanZeroL2 := (1 / 2 : ℂ) • (y - meanZeroReflection y)
    have hodd : IsOddVec (yo : ThetaL2) := by
      rw [isOddVec_iff]
      simp only [yo, Submodule.coe_smul, Submodule.coe_sub, map_smul, map_sub, coe_meanZeroReflection,
        unitReflection_unitReflection]
      module
    have hcomm := opRpow_commute nonneg_meanZeroMetric commute_meanZeroMetric_reflection α
    have hyo : opRpow meanZeroMetric α yo = quantileVec₀ := by
      have hR : opRpow meanZeroMetric α (meanZeroReflection y) = -quantileVec₀ := by
        have h := DFunLike.congr_fun hcomm.eq y
        change opRpow meanZeroMetric α (meanZeroReflection y) =
          meanZeroReflection (opRpow meanZeroMetric α y) at h
        rw [h, hy, meanZeroReflection_quantileVec₀]
      simp only [yo, map_smul, map_sub, hy, hR]
      module
    have hlaw := coe_rpow_meanZeroMetric hα hodd
    rw [hyo] at hlaw
    have hQ : MemLp (quantilePowQuotient α) 2 unitIntervalMeasure := by
      refine (Lp.memLp (yo : ThetaL2)).ae_eq ?_
      filter_upwards [metricPowMul_ae hα (yo : ThetaL2), quantileVec_ae,
        show ((quantileVec₀ : ThetaL2) : ℝ → ℂ) =ᵐ[unitIntervalMeasure] (metricPowMul α hα yo : ℝ → ℂ)
          from by rw [hlaw]] with t h1 h2 h3
      change (quantileVec : ℝ → ℂ) t = _ at h3
      rw [h2, h1] at h3
      have hpos : metricPowSymbol α t ≠ 0 := by
        rw [metricPowSymbol]; exact_mod_cast (Real.rpow_pos_of_pos (metricReal_pos t) α).ne'
      rw [quantilePowQuotient, h3]
      field_simp
    exact (memLp_quantilePowQuotient_iff α).1 hQ
  · intro hlt
    have hQ := (memLp_quantilePowQuotient_iff α).2 hlt
    set g : ThetaL2 := hQ.toLp
    have hgae : (g : ℝ → ℂ) =ᵐ[unitIntervalMeasure] quantilePowQuotient α := MemLp.coeFn_toLp _
    have hodd : IsOddVec g := by
      filter_upwards [hgae, ae_comp_unitReflection hgae, ae_unitIntervalMeasure_mem_Ioo,
        ae_metricReal_one_sub] with t a b c d
      rw [b, a, quantilePowQuotient, quantilePowQuotient, quantileFun_one_sub c, metricPowSymbol,
        metricPowSymbol, d]
      push_cast; ring
    refine ⟨⟨g, hodd.mem_meanZeroSpace⟩, Subtype.ext ?_⟩
    rw [coe_rpow_meanZeroMetric hα (g := ⟨g, hodd.mem_meanZeroSpace⟩) hodd]
    apply Lp.ext
    filter_upwards [metricPowMul_ae hα g, hgae, quantileVec_ae] with t h1 h2 h3
    change _ = (quantileVec : ℝ → ℂ) t
    rw [h1, h2, h3, quantilePowQuotient]
    have hpos : metricPowSymbol α t ≠ 0 := by
      rw [metricPowSymbol]; exact_mod_cast (Real.rpow_pos_of_pos (metricReal_pos t) α).ne'
    field_simp

/-! ## The two ports in the fractional scale -/

/-- The output vector `b = P h` as an element of `H₀`. -/
def outputVec₀ : MeanZeroL2 := ⟨onePortOutputVector, meanZeroProj_mem _⟩

theorem norm_opRpow_half_meanZeroMetric (f : MeanZeroL2) :
    ‖opRpow meanZeroMetric (1 / 2) f‖ = Real.sqrt (metricEnergy f) := by
  have h := norm_sq_opRpow_half nonneg_meanZeroMetric f
  rw [inner_meanZeroMetric, inner_thetaMetricOperator, Complex.ofReal_re] at h
  rw [metricEnergy, ← h, Real.sqrt_sq (norm_nonneg _)]

/-- **`b ∈ range(T^{1/2})`**. -/
theorem exists_opRpow_half_eq_outputVec : ∃ w : MeanZeroL2, opRpow meanZeroMetric (1 / 2) w = outputVec₀ := by
  refine mem_range_of_norm_inner_le (isSelfAdjoint_opRpow _ _) (K := ‖outPortLp‖) fun f => ?_
  rw [norm_opRpow_half_meanZeroMetric]
  exact norm_inner_onePortOutputVector_le f.2

/-- The quantile speed `q = 1/h` is not integrable on the unit interval: `∫₀¹ q = ∫_ℝ dx = ∞`. -/
theorem not_integrable_thetaQuantileSpeed : ¬ Integrable (fun t => thetaQuantileSpeed t) unitIntervalMeasure := by
  intro h
  have h2 := (integrable_unitInterval_iff_cdf h.1).1 h
  have h3 : Integrable (fun _ : ℝ => (1 : ℝ)) volume := by
    refine h2.congr (Eventually.of_forall fun x => ?_)
    have hρ := thetaSource.normalized_pos x
    have hq : thetaQuantileSpeed (thetaSource.cdfFun x) = (thetaSource.normalized x)⁻¹ := by
      have e := metricSymbol_eq_inv_quantileSpeed thetaSource (thetaSource.cdfFun x)
      rw [metricSymbol_cdfFun_eq] at e
      have e' : thetaSource.normalized x = (quantileSpeed thetaSource (thetaSource.cdfFun x))⁻¹ := by
        exact_mod_cast e
      rw [thetaQuantileSpeed, e', inv_inv]
    simp only [smul_eq_mul]
    rw [hq, mul_inv_cancel₀ hρ.ne']
  have := (integrable_const_iff (μ := (volume : Measure ℝ)) (c := (1 : ℝ))).1 h3
  rcases this with h0 | hfin
  · norm_num at h0
  · exact absurd hfin (by simp [isFiniteMeasure_iff])

/-- **`b ∉ range(T)`**: `Tf = b` would force `f = 1 + c q` with `q ∉ L²`. -/
theorem not_exists_meanZeroMetric_eq_outputVec : ¬ ∃ f : MeanZeroL2, meanZeroMetric f = outputVec₀ := by
  rintro ⟨f, hf⟩
  have hcoe := congrArg Subtype.val hf
  change (meanZeroMetric f : ThetaL2) = onePortOutputVector at hcoe
  rw [coe_meanZeroMetric, onePortOutputVector, ← sub_eq_zero, ← map_sub, ← map_sub] at hcoe
  set w := (f : ThetaL2) - constMode
  set c := ⟪constMode, thetaMetricOperator w⟫_ℂ
  rw [meanZeroProj_apply, sub_eq_zero] at hcoe
  -- `h (f − 1) = c` almost everywhere
  have hcoeae : ((thetaMetricOperator w : ThetaL2) : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      ((c • constMode : ThetaL2) : ℝ → ℂ) := by rw [← hcoe]
  have hae : ∀ᵐ t ∂unitIntervalMeasure, (metricReal t : ℂ) * ((f : ThetaL2) t - 1) = c := by
    filter_upwards [coeFn_thetaMetricOperator w, Lp.coeFn_sub (f : ThetaL2) constMode,
      coeFn_unitFourierBasis 0, hcoeae, Lp.coeFn_smul c constMode] with t h1 h2 h3 h4 h5
    have hconst : (constMode : ThetaL2) t = 1 := by
      rw [show (constMode : ThetaL2) = unitFourierBasis 0 from rfl, h3, fourierMode_zero]
    calc (metricReal t : ℂ) * ((f : ThetaL2) t - 1) = metricSymbol thetaSource t * (w : ℝ → ℂ) t := by
          rw [h2, Pi.sub_apply, hconst, ← metricSymbol_eq_norm]
      _ = (thetaMetricOperator w : ℝ → ℂ) t := h1.symm
      _ = ((c • constMode : ThetaL2) : ℝ → ℂ) t := h4
      _ = c := by rw [h5, Pi.smul_apply, hconst, smul_eq_mul, mul_one]
  by_cases hc : c = 0
  · -- then `f = 1`, which is not mean zero
    have hf1 : ∀ᵐ t ∂unitIntervalMeasure, (f : ThetaL2) t = 1 := by
      filter_upwards [hae] with t ht
      rw [hc] at ht
      have hpos : (metricReal t : ℂ) ≠ 0 := by exact_mod_cast (metricReal_pos t).ne'
      have := (mul_eq_zero.1 ht).resolve_left hpos
      exact sub_eq_zero.1 this
    have hmean := (mem_meanZeroSpace_iff (f : ThetaL2)).1 f.2
    rw [inner_constMode_eq_pinnedMean, pinnedMean, integral_congr_ae hf1] at hmean
    simp at hmean
  · -- then `q = (f − 1)/c` would be integrable
    apply not_integrable_thetaQuantileSpeed
    have hint : Integrable (fun t => ((f : ThetaL2) t - 1) / c) unitIntervalMeasure :=
      ((integrable_coe_unitInterval (f : ThetaL2)).sub (integrable_const 1)).div_const c
    have hint' := hint.norm
    refine hint'.congr ?_
    filter_upwards [hae] with t ht
    have hpos : (metricReal t : ℂ) ≠ 0 := by exact_mod_cast (metricReal_pos t).ne'
    have hval : ((f : ThetaL2) t - 1) / c = ((metricReal t)⁻¹ : ℝ) := by
      rw [div_eq_iff hc, ← ht]
      push_cast
      field_simp
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (metricReal_pos t))]
    have e := metricSymbol_eq_inv_quantileSpeed thetaSource t
    have e' : metricReal t = (thetaQuantileSpeed t)⁻¹ := by
      simp only [metricReal, e, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 (thetaQuantileSpeed_pos t))]
    rw [e', inv_inv]

end

end RHTower
