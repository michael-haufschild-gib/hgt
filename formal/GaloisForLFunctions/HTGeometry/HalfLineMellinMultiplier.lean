import GaloisForLFunctions.HTGeometry.HalfLineMellinUnitary
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.HTGeometry.InjectiveDenseRangePolarUnitary

/-!
# Dilations and Mellin multipliers on the half line

On `H = L²((0,∞), dt)` the unitary dilations `(D_κ u)(t) = √κ u(κt)` become translations by `log κ`
under the half-density exponential unitary, hence modulations under the Mellin unitary
`𝓜 = 𝓕 ∘ U`: `𝓜 D_κ = e^{2πi log κ ·} 𝓜`.

A bounded measurable symbol `m` defines the Mellin multiplier `M = 𝓜^{-1} m 𝓜`.  It commutes with
every dilation; `⟨Mu, Mv⟩ = ∫ |m|² conj(𝓜u) 𝓜v`; its adjoint is the multiplier `conj m`.  If `m`
never vanishes, `M` is injective with dense range; if moreover `|m|` is arbitrarily small on
intervals, `M` is not bounded below, so its range is not closed.  A nowhere-vanishing symbol
factors as `M = U|M|` with `U` the unitary multiplier `m/|m|` and `|M|` the multiplier `|m|`.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace FourierTransform ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local notation "L2R" => Lp ℂ 2 (volume : Measure ℝ)

/-! ## Dilations -/

/-- The dilation `(D_κ u)(t) = √κ u(κ t)`, realized as `U^{-1} τ_{log κ} U`. -/
def halfLineDilation (κ : ℝ) : HalfLineL2 →L[ℂ] HalfLineL2 :=
  halfLineExpUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L
    (translateL2 (Real.log κ)).toContinuousLinearMap ∘L
      halfLineExpUnitary.toLinearIsometry.toContinuousLinearMap

theorem halfLineExpUnitary_halfLineDilation (κ : ℝ) (u : HalfLineL2) :
    halfLineExpUnitary (halfLineDilation κ u) = translateL2 (Real.log κ) (halfLineExpUnitary u) := by
  simp [halfLineDilation]

/-- **Dilations are Mellin modulations.**  `𝓜(D_κ u) = e^{2πi log κ ·} 𝓜u`. -/
theorem halfLineMellinUnitary_halfLineDilation (κ : ℝ) (u : HalfLineL2) :
    halfLineMellinUnitary (halfLineDilation κ u) = modulationMul (Real.log κ) (halfLineMellinUnitary u) := by
  change 𝓕 (halfLineExpUnitary (halfLineDilation κ u)) = modulationMul (Real.log κ) (𝓕 (halfLineExpUnitary u))
  rw [halfLineExpUnitary_halfLineDilation]
  exact fourierTransform_translateL2 _ _

/-- The half-density pullback of an a.e. representative. -/
theorem halfLineExpUnitary_ae_halfDensityPullback {u : HalfLineL2} {g : ℝ → ℂ}
    (hug : (u : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] g) :
    (halfLineExpUnitary u : ℝ → ℂ) =ᵐ[volume] halfDensityPullback g := by
  have hpull : ∀ᵐ x ∂expWeightMeasure, (u : ℝ → ℂ) (Real.exp x) = g (Real.exp x) :=
    measurePreserving_exp_expWeightMeasure.quasiMeasurePreserving.ae hug
  have hpull' : ∀ᵐ x ∂(volume : Measure ℝ), (u : ℝ → ℂ) (Real.exp x) = g (Real.exp x) :=
    (withDensity_realDensity_ae_eq (μ := volume) Real.measurable_exp Real.exp_pos
      (f := fun x => (u : ℝ → ℂ) (Real.exp x)) (g := fun x => g (Real.exp x))).1 hpull
  filter_upwards [halfLineExpUnitary_ae u, hpull'] with x hx1 hx2
  rw [hx1, halfDensityPullback, hx2]

/-- **Dilation formula.**  If `g'(t) = √κ g(κ t)` for `t > 0`, then `D_κ` maps the vector with
representative `g` to the vector with representative `g'`. -/
theorem halfLineDilation_eq_of_ae {κ : ℝ} (hκ : 0 < κ) {u v : HalfLineL2} {g g' : ℝ → ℂ}
    (hug : (u : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] g)
    (hvg : (v : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] g')
    (hrel : ∀ t, 0 < t → g' t = (Real.sqrt κ : ℂ) * g (κ * t)) :
    halfLineDilation κ u = v := by
  apply halfLineExpUnitary.injective
  rw [halfLineExpUnitary_halfLineDilation]
  refine Lp.ext ?_
  have hU := halfLineExpUnitary_ae_halfDensityPullback hug
  have hV := halfLineExpUnitary_ae_halfDensityPullback hvg
  have hshift : ∀ᵐ x ∂(volume : Measure ℝ),
      (halfLineExpUnitary u : ℝ → ℂ) (x + Real.log κ) = halfDensityPullback g (x + Real.log κ) :=
    (measurePreserving_add_right (volume : Measure ℝ) (Real.log κ)).quasiMeasurePreserving.ae hU
  filter_upwards [coeFn_translateL2 (Real.log κ) (halfLineExpUnitary u), hshift, hV] with x h1 h2 h3
  rw [h1, h2, h3, halfDensityPullback, halfDensityPullback, hrel _ (Real.exp_pos x), Real.exp_add,
    Real.exp_log hκ, Real.sqrt_mul (Real.exp_pos x).le, mul_comm κ]
  push_cast
  ring

/-! ## Mellin multipliers -/

variable {m : ℝ → ℂ} (hm : Measurable m) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖m ξ‖ ≤ C)

/-- The Mellin multiplier `M = 𝓜^{-1} m 𝓜`. -/
def mellinMultiplier : HalfLineL2 →L[ℂ] HalfLineL2 :=
  halfLineMellinUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L
    lpBoundedMulCLM (p := 2) (μ := volume) hm hC0 hC ∘L
      halfLineMellinUnitary.toLinearIsometry.toContinuousLinearMap

theorem halfLineMellinUnitary_mellinMultiplier (u : HalfLineL2) :
    halfLineMellinUnitary (mellinMultiplier hm hC0 hC u) =
      lpBoundedMulCLM (p := 2) (μ := volume) hm hC0 hC (halfLineMellinUnitary u) := by
  simp [mellinMultiplier]

theorem coeFn_halfLineMellinUnitary_mellinMultiplier (u : HalfLineL2) :
    (halfLineMellinUnitary (mellinMultiplier hm hC0 hC u) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => m ξ * (halfLineMellinUnitary u : ℝ → ℂ) ξ := by
  rw [halfLineMellinUnitary_mellinMultiplier]
  exact lpBoundedMulCLM_coeFn hm hC0 hC _

/-- **Equivariance.**  Every Mellin multiplier commutes with every dilation. -/
theorem mellinMultiplier_halfLineDilation (κ : ℝ) (u : HalfLineL2) :
    mellinMultiplier hm hC0 hC (halfLineDilation κ u) = halfLineDilation κ (mellinMultiplier hm hC0 hC u) := by
  apply halfLineMellinUnitary.injective
  refine Lp.ext ?_
  have e1 := coeFn_halfLineMellinUnitary_mellinMultiplier hm hC0 hC (halfLineDilation κ u)
  rw [halfLineMellinUnitary_halfLineDilation] at e1 ⊢
  filter_upwards [e1, coeFn_modulationMul (Real.log κ) (halfLineMellinUnitary u),
    coeFn_modulationMul (Real.log κ) (halfLineMellinUnitary (mellinMultiplier hm hC0 hC u)),
    coeFn_halfLineMellinUnitary_mellinMultiplier hm hC0 hC u] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  ring

/-- `⟨Mu, Mv⟩ = ∫ |m|² conj(𝓜u) 𝓜v`. -/
theorem inner_mellinMultiplier (u v : HalfLineL2) :
    ⟪mellinMultiplier hm hC0 hC u, mellinMultiplier hm hC0 hC v⟫_ℂ =
      ∫ ξ, ((‖m ξ‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ ((halfLineMellinUnitary u : ℝ → ℂ) ξ) *
        (halfLineMellinUnitary v : ℝ → ℂ) ξ) := by
  rw [← halfLineMellinUnitary.inner_map_map, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_halfLineMellinUnitary_mellinMultiplier hm hC0 hC u,
    coeFn_halfLineMellinUnitary_mellinMultiplier hm hC0 hC v] with ξ h1 h2
  rw [h1, h2, RCLike.inner_apply, map_mul]
  rw [show ((‖m ξ‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ (m ξ) * m ξ by
    rw [Complex.conj_mul']; push_cast; rfl]
  ring

theorem inner_halfLine_eq_integral (u v : HalfLineL2) :
    ⟪u, v⟫_ℂ = ∫ ξ, starRingEnd ℂ ((halfLineMellinUnitary u : ℝ → ℂ) ξ) *
      (halfLineMellinUnitary v : ℝ → ℂ) ξ := by
  rw [← halfLineMellinUnitary.inner_map_map, MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [RCLike.inner_apply]
  ring

omit hm in
theorem measurable_conj_symbol (hm : Measurable m) : Measurable fun ξ => starRingEnd ℂ (m ξ) :=
  Complex.continuous_conj.measurable.comp hm

omit hC in
theorem norm_conj_symbol_le (hC : ∀ ξ, ‖m ξ‖ ≤ C) (ξ : ℝ) : ‖starRingEnd ℂ (m ξ)‖ ≤ C := by
  rw [Complex.norm_conj]
  exact hC ξ

/-- The adjoint relation: the adjoint multiplier has symbol `conj m`. -/
theorem inner_mellinMultiplier_left (u v : HalfLineL2) :
    ⟪mellinMultiplier hm hC0 hC u, v⟫_ℂ =
      ⟪u, mellinMultiplier (measurable_conj_symbol hm) hC0 (norm_conj_symbol_le hC) v⟫_ℂ := by
  rw [inner_halfLine_eq_integral, inner_halfLine_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_halfLineMellinUnitary_mellinMultiplier hm hC0 hC u,
    coeFn_halfLineMellinUnitary_mellinMultiplier (measurable_conj_symbol hm) hC0
      (norm_conj_symbol_le hC) v] with ξ h1 h2
  rw [h1, h2, map_mul]
  ring

/-- A nowhere-vanishing symbol gives an injective multiplier. -/
theorem mellinMultiplier_injective (hm0 : ∀ ξ, m ξ ≠ 0) :
    Function.Injective (mellinMultiplier hm hC0 hC) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
  apply halfLineMellinUnitary.injective
  rw [map_zero]
  refine Lp.ext ?_
  have h0 : (halfLineMellinUnitary (mellinMultiplier hm hC0 hC u) : ℝ → ℂ) =ᵐ[volume] 0 := by
    rw [hu, map_zero]
    exact Lp.coeFn_zero _ _ _
  filter_upwards [coeFn_halfLineMellinUnitary_mellinMultiplier hm hC0 hC u, h0,
    Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with ξ h1 h2 h3
  rw [h1] at h2
  rw [h3]
  exact (mul_eq_zero.1 h2).resolve_left (hm0 ξ)

/-- A nowhere-vanishing symbol gives a multiplier with dense range. -/
theorem denseRange_mellinMultiplier (hm0 : ∀ ξ, m ξ ≠ 0) :
    DenseRange (mellinMultiplier hm hC0 hC) := by
  have hadj : mellinMultiplier hm hC0 hC = ContinuousLinearMap.adjoint
      (mellinMultiplier (measurable_conj_symbol hm) hC0 (norm_conj_symbol_le hC)) := by
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun u v => ?_
    exact inner_mellinMultiplier_left hm hC0 hC u v
  rw [hadj]
  exact denseRange_adjoint_of_injective (mellinMultiplier_injective _ _ _ fun ξ => by
    simpa using hm0 ξ)

/-- If `|m| ≤ ε` on a nondegenerate interval for every `ε > 0`, the multiplier is not bounded
below. -/
theorem not_boundedBelow_mellinMultiplier
    (hsmall : ∀ ε > 0, ∃ a b : ℝ, a < b ∧ ∀ ξ ∈ Icc a b, ‖m ξ‖ ≤ ε) :
    ¬ ∃ c > 0, ∀ u : HalfLineL2, c * ‖u‖ ≤ ‖mellinMultiplier hm hC0 hC u‖ := by
  rintro ⟨c, hc, hbd⟩
  obtain ⟨a, b, hab, hm_small⟩ := hsmall (c / 2) (by positivity)
  have hmeas : MeasurableSet (Icc a b) := measurableSet_Icc
  have hfin : volume (Icc a b) ≠ ∞ := by simp
  set w : L2R := indicatorConstLp 2 hmeas hfin (1 : ℂ)
  have hw : w ≠ 0 := by
    intro h0
    have := congrArg norm h0
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_zero] at this
    simp only [norm_one, one_mul] at this
    rw [Real.volume_real_Icc_of_le hab.le] at this
    have hp : (0 : ℝ) < (b - a) ^ (1 / (2 : ℝ≥0∞).toReal) := Real.rpow_pos_of_pos (by linarith) _
    linarith
  set u := halfLineMellinUnitary.symm w
  have hu : ‖u‖ = ‖w‖ := halfLineMellinUnitary.symm.norm_map w
  have hMu : ‖mellinMultiplier hm hC0 hC u‖ ≤ c / 2 * ‖u‖ := by
    rw [← halfLineMellinUnitary.norm_map, halfLineMellinUnitary_mellinMultiplier,
      LinearIsometryEquiv.apply_symm_apply, hu]
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := volume) hm hC0 hC w,
      indicatorConstLp_coeFn (p := 2) (hs := hmeas) (hμs := hfin) (c := (1 : ℂ))] with ξ h1 h2
    rw [h1, norm_mul]
    by_cases h : ξ ∈ Icc a b
    · exact mul_le_mul_of_nonneg_right (hm_small ξ h) (norm_nonneg _)
    · have hw0 : (w : ℝ → ℂ) ξ = 0 := by rw [h2, Set.indicator_of_notMem h]
      rw [hw0, norm_zero, mul_zero, mul_zero]
  have h1 := hbd u
  have hpos : 0 < ‖u‖ := by rw [hu]; exact norm_pos_iff.2 hw
  nlinarith

/-- **Non-closed range.**  A nowhere-vanishing symbol that is arbitrarily small on intervals gives an
injective multiplier with dense, non-closed range (its inverse is unbounded). -/
theorem not_isClosed_range_mellinMultiplier (hm0 : ∀ ξ, m ξ ≠ 0)
    (hsmall : ∀ ε > 0, ∃ a b : ℝ, a < b ∧ ∀ ξ ∈ Icc a b, ‖m ξ‖ ≤ ε) :
    ¬ IsClosed (Set.range (mellinMultiplier hm hC0 hC)) := by
  intro hclosed
  have hsurj : Function.Surjective (mellinMultiplier hm hC0 hC) := by
    have hd := denseRange_mellinMultiplier hm hC0 hC hm0
    rw [← Set.range_eq_univ, ← hclosed.closure_eq]
    exact hd.closure_range
  set E := ContinuousLinearEquiv.ofBijective (mellinMultiplier hm hC0 hC)
    (LinearMap.ker_eq_bot.2 (mellinMultiplier_injective hm hC0 hC hm0))
    (LinearMap.range_eq_top.2 hsurj)
  apply not_boundedBelow_mellinMultiplier hm hC0 hC hsmall
  refine ⟨1 / (‖(E.symm : HalfLineL2 →L[ℂ] HalfLineL2)‖ + 1), by positivity, fun u => ?_⟩
  have h1 : ‖u‖ ≤ ‖(E.symm : HalfLineL2 →L[ℂ] HalfLineL2)‖ * ‖mellinMultiplier hm hC0 hC u‖ := by
    have : E.symm (mellinMultiplier hm hC0 hC u) = u := E.symm_apply_apply u
    calc ‖u‖ = ‖E.symm (mellinMultiplier hm hC0 hC u)‖ := by rw [this]
      _ ≤ _ := (E.symm : HalfLineL2 →L[ℂ] HalfLineL2).le_opNorm _
  have hn := norm_nonneg (mellinMultiplier hm hC0 hC u)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (E.symm : HalfLineL2 →L[ℂ] HalfLineL2)]

/-! ## Phase and modulus -/

omit hm hC in
theorem measurable_norm_symbol (hm : Measurable m) : Measurable fun ξ => ((‖m ξ‖ : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp hm.norm

omit hm hC in
theorem measurable_phase_symbol (hm : Measurable m) :
    Measurable fun ξ => m ξ / ((‖m ξ‖ : ℝ) : ℂ) :=
  hm.div (measurable_norm_symbol hm)

omit hC in
theorem norm_phase_symbol (hm0 : ∀ ξ, m ξ ≠ 0) (ξ : ℝ) : ‖m ξ / ((‖m ξ‖ : ℝ) : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.2 (hm0 ξ))]

/-- **Polar decomposition** `M = U|M|`: `U` the unitary multiplier `m/|m|`, `|M|` the multiplier `|m|`. -/
theorem mellinMultiplier_eq_phase_comp_modulus (hm0 : ∀ ξ, m ξ ≠ 0) :
    mellinMultiplier hm hC0 hC =
      mellinMultiplier (measurable_phase_symbol hm) zero_le_one (fun ξ => (norm_phase_symbol hm0 ξ).le) ∘L
        mellinMultiplier (measurable_norm_symbol hm) hC0 (fun ξ => by
          rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]; exact hC ξ) := by
  refine ContinuousLinearMap.ext fun u => halfLineMellinUnitary.injective (Lp.ext ?_)
  rw [ContinuousLinearMap.comp_apply]
  filter_upwards [coeFn_halfLineMellinUnitary_mellinMultiplier hm hC0 hC u,
    coeFn_halfLineMellinUnitary_mellinMultiplier (measurable_phase_symbol hm) zero_le_one
      (fun ξ => (norm_phase_symbol hm0 ξ).le) (mellinMultiplier (measurable_norm_symbol hm) hC0
        (fun ξ => by rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]; exact hC ξ) u),
    coeFn_halfLineMellinUnitary_mellinMultiplier (measurable_norm_symbol hm) hC0
      (fun ξ => by rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]; exact hC ξ) u]
    with ξ h1 h2 h3
  rw [h1, h2, h3, ← mul_assoc, div_mul_cancel₀ _ (by
    exact_mod_cast norm_ne_zero_iff.2 (hm0 ξ))]

/-- The phase multiplier is an isometry. -/
theorem inner_phase_mellinMultiplier (hm0 : ∀ ξ, m ξ ≠ 0) (u v : HalfLineL2) :
    ⟪mellinMultiplier (measurable_phase_symbol hm) zero_le_one (fun ξ => (norm_phase_symbol hm0 ξ).le) u,
      mellinMultiplier (measurable_phase_symbol hm) zero_le_one (fun ξ => (norm_phase_symbol hm0 ξ).le) v⟫_ℂ =
      ⟪u, v⟫_ℂ := by
  rw [← halfLineMellinUnitary.inner_map_map, halfLineMellinUnitary_mellinMultiplier,
    halfLineMellinUnitary_mellinMultiplier, lpBoundedMulCLM_inner_unimodular, halfLineMellinUnitary.inner_map_map]
  intro ξ
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, norm_phase_symbol hm0]
  norm_num

/-- **Phase quotient.**  Positive Grams see only the modulus: `⟨Mu, Mv⟩ = ⟨|M|u, |M|v⟩`. -/
theorem inner_mellinMultiplier_eq_modulus (hm0 : ∀ ξ, m ξ ≠ 0) (u v : HalfLineL2) :
    ⟪mellinMultiplier hm hC0 hC u, mellinMultiplier hm hC0 hC v⟫_ℂ =
      ⟪mellinMultiplier (measurable_norm_symbol hm) hC0 (fun ξ => by
          rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]; exact hC ξ) u,
        mellinMultiplier (measurable_norm_symbol hm) hC0 (fun ξ => by
          rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]; exact hC ξ) v⟫_ℂ := by
  rw [mellinMultiplier_eq_phase_comp_modulus hm hC0 hC hm0, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, inner_phase_mellinMultiplier hm hm0]

end GaloisForLFunctions.HTGeometry
