import GaloisForLFunctions.RHTower.LiClockThetaGammaCumulativeReserve
import GaloisForLFunctions.HTGeometry.HalfLineQuantileTransport

/-!
# Unequal-mass quantile transport of the actual Gamma reserve

On the reserve domain `D` remove the positive first-row reserve `δ(p) Γ_{2,p}` from `τ_p⁺`:

* the remainder `ρ_p = τ_p⁺ - δ(p) Γ_{2,p}` is a positive finite measure with density at least
  `T̄(p) f_{1,p} > 0`, mass `Λ⁺ - δ > Λ⁻`, and `ρ_p ≥ T̄ Γ_{2,p}`, `τ_p⁻ ≥ |ℓ₂| Γ_{4,p}`;
* both cumulative functions `R(T) = ρ_p(0,T]` and `G(T) = τ_p⁻(0,T]` are continuous and strictly
  increasing on `[0, ∞)`, start at `0`, tend to the masses, and `R(T) > G(T)` for `T > 0`;
* (D11) with the unique `a_p > 0` such that `R(a_p) = Λ⁻`, `χ = ρ_p|(0,a_p]` and `ζ = ρ_p|(a_p,∞)`,
  `τ_p⁺ = δ Γ_{2,p} + χ + ζ`; the quantiles `X = R⁻¹`, `Y = G⁻¹` on `(0, Λ⁻)` push Lebesgue measure
  onto `χ` and `τ_p⁻` respectively, and `X < Y` everywhere on `(0, Λ⁻)`;
* (D12) every bounded measurable nonnegative test that is nonincreasing on `(0, ∞)` satisfies
  `∫ h d(τ⁺ - τ⁻) ≥ δ ∫ h dΓ_{2,p} ≥ 0`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

namespace RHTower

local notation "ℓ" => liClockThetaLogJumpCoefficient
local notation "T̄" => liClockThetaGammaTailBudget
local notation "δ" => liClockThetaGammaReserve
local notation "W" => liClockThetaWideThreshold
local notation "F" => liClockThetaGammaRowCDF
local notation "τ" => liClockThetaGammaJumpMeasure
local notation "Λ" => liClockThetaJumpMass
local notation "H" => liClockThetaReciprocalLog

/-! ## Cumulative functions of half-line densities -/

private theorem withDensity_Ioc_toReal {f : ℝ → ℝ} (hf : Integrable f) (hnn : ∀ t, 0 ≤ f t)
    (hzero : ∀ t, t ≤ 0 → f t = 0) (T : ℝ) :
    (volume.withDensity (fun t => ENNReal.ofReal (f t)) (Ioc 0 T)).toReal =
      ∫ t in (0 : ℝ)..T, f t := by
  rcases le_or_gt 0 T with hT | hT
  · rw [withDensity_apply _ measurableSet_Ioc, ← ofReal_integral_eq_lintegral_ofReal
      hf.integrableOn (ae_of_all _ hnn), ENNReal.toReal_ofReal
      (setIntegral_nonneg measurableSet_Ioc fun t _ => hnn t), intervalIntegral.integral_of_le hT]
  · rw [Ioc_eq_empty (not_lt.2 hT.le), measure_empty, ENNReal.toReal_zero,
      intervalIntegral.integral_of_ge hT.le, setIntegral_congr_fun measurableSet_Ioc
        (g := fun _ => (0 : ℝ)) fun t ht => hzero t ht.2, integral_zero, neg_zero]

private theorem strictMonoOn_primitive {f : ℝ → ℝ} (hf : Integrable f) (hnn : ∀ t, 0 ≤ f t)
    (hpos : ∀ t, 0 < t → 0 < f t) :
    StrictMonoOn (fun T => ∫ t in (0 : ℝ)..T, f t) (Ici 0) := by
  intro T₁ hT₁ T₂ _ hlt
  simp only
  rw [← sub_pos, intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable)
    (hf.intervalIntegrable), intervalIntegral.integral_of_le hlt.le]
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ hnn) hf.integrableOn]
  have hsub : Ioc T₁ T₂ ⊆ Function.support f ∩ Ioc T₁ T₂ := fun t ht =>
    ⟨(hpos t (lt_of_le_of_lt (mem_Ici.1 hT₁) ht.1)).ne', ht⟩
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_pos.2 (sub_pos.2 hlt)

private theorem tendsto_primitive {f : ℝ → ℝ} (hf : Integrable f)
    (hzero : ∀ t, t ≤ 0 → f t = 0) :
    Tendsto (fun T => ∫ t in (0 : ℝ)..T, f t) atTop (𝓝 (∫ t, f t)) := by
  have h := intervalIntegral_tendsto_integral_Ioi 0 hf.integrableOn tendsto_id
  have e : ∫ t in Ioi (0 : ℝ), f t = ∫ t, f t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0) fun t ht =>
      hzero t (not_lt.1 ht)
  rw [e] at h
  exact h

private theorem measure_Iic_eq_Ioc {μ : Measure ℝ} (h0 : μ (Iic 0) = 0) {T : ℝ} (hT : 0 ≤ T) :
    μ (Iic T) = μ (Ioc 0 T) := by
  refine le_antisymm ?_ (measure_mono Ioc_subset_Iic_self)
  rw [← Iic_union_Ioc_eq_Iic hT]
  exact (measure_union_le _ _).trans (by rw [h0, zero_add])

private theorem measure_Iic_zero_of_ae_pos {μ : Measure ℝ} (h : ∀ᵐ t ∂μ, 0 < t) :
    μ (Iic 0) = 0 := by
  have h' := ae_iff.1 h
  have e : {a : ℝ | ¬0 < a} = Iic 0 := by ext; simp
  rwa [e] at h'

/-! ## The jump densities on the half-line -/

theorem liClockThetaGammaJumpDensity_of_nonpos (p : ℝ) (b : Bool) {t : ℝ} (ht : t ≤ 0) :
    liClockThetaGammaJumpDensity p b t = 0 := by
  have h0 : ∀ i, liClockThetaGammaRowDensity p i t = 0 := fun i => by
    unfold liClockThetaGammaRowDensity
    split_ifs
    · rfl
    · exact indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.2 ht) _
  simp [liClockThetaGammaJumpDensity, h0]

theorem liClockThetaGammaJumpDensity_true_pos {p : ℝ} (hp : W < p) {t : ℝ} (ht : 0 < t) :
    0 < liClockThetaGammaJumpDensity p true t := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  obtain ⟨h1, -, hpos, -⟩ := liClockThetaLogJumpCoefficient_first_two hp0
  have hpart : liClockThetaJumpPart p true 1 = ℓ p 1 := by
    simp only [liClockThetaJumpPart, if_true]
    exact max_eq_left hpos.le
  have h := liClockThetaGammaJumpDensity_ge_row hp true 1 t
  rw [hpart, liClockThetaGammaRowDensity_one ht] at h
  exact lt_of_lt_of_le (by positivity) h

theorem liClockThetaGammaJumpDensity_false_pos {p : ℝ} (hp : W < p) {t : ℝ} (ht : 0 < t) :
    0 < liClockThetaGammaJumpDensity p false t := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have hneg := (liClockThetaLogJumpCoefficient_first_two hp0).2.2.2
  have h := liClockThetaGammaJumpDensity_false_ge_second_row hp ht
  rw [liClockThetaGammaRowDensity_two ht] at h
  have : 0 < |ℓ p 2| := abs_pos.2 hneg.ne
  exact lt_of_lt_of_le (by positivity) h

/-! ## The reserve-removed measure -/

/-- `ρ_p(t) = τ_p⁺(t) - δ(p) f_{1,p}(t)`. -/
def liClockThetaGammaReserveRemovedDensity (p t : ℝ) : ℝ :=
  liClockThetaGammaJumpDensity p true t - δ p * liClockThetaGammaRowDensity p 1 t

/-- The positive measure `ρ_p = τ_p⁺ - δ(p) Γ_{2,p}`. -/
def liClockThetaGammaReserveRemovedMeasure (p : ℝ) : Measure ℝ :=
  volume.withDensity fun t => ENNReal.ofReal (liClockThetaGammaReserveRemovedDensity p t)

/-- The cumulative function `G_p^±(T) = τ_p^±(0,T]`. -/
def liClockThetaGammaJumpCDF (p : ℝ) (b : Bool) (T : ℝ) : ℝ := (τ p b (Ioc 0 T)).toReal

/-- The cumulative function `R_p(T) = ρ_p(0,T]`. -/
def liClockThetaGammaReserveRemovedCDF (p T : ℝ) : ℝ :=
  (liClockThetaGammaReserveRemovedMeasure p (Ioc 0 T)).toReal

local notation "ρ" => liClockThetaGammaReserveRemovedMeasure
local notation "ρd" => liClockThetaGammaReserveRemovedDensity
local notation "G" => liClockThetaGammaJumpCDF
local notation "R" => liClockThetaGammaReserveRemovedCDF

/-- `ρ_p(t) ≥ T̄(p) f_{1,p}(t)`. -/
theorem liClockThetaGammaReserveRemovedDensity_ge {p : ℝ} (hp : W < p) (t : ℝ) :
    T̄ p * liClockThetaGammaRowDensity p 1 t ≤ ρd p t := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  obtain ⟨h1, -, hpos, -⟩ := liClockThetaLogJumpCoefficient_first_two hp0
  have hpart : liClockThetaJumpPart p true 1 = ℓ p 1 := by
    simp only [liClockThetaJumpPart, if_true]
    exact max_eq_left hpos.le
  have h := liClockThetaGammaJumpDensity_ge_row hp true 1 t
  rw [hpart, h1] at h
  unfold liClockThetaGammaReserveRemovedDensity liClockThetaGammaReserve
  nlinarith

theorem liClockThetaGammaReserveRemovedDensity_nonneg {p : ℝ} (hp : W < p) (t : ℝ) :
    0 ≤ ρd p t :=
  (mul_nonneg (liClockThetaGammaTailBudget_pos hp).le
    (liClockThetaGammaRowDensity_nonneg (liClockThetaWideThreshold_pos.trans hp) 1 t)).trans
    (liClockThetaGammaReserveRemovedDensity_ge hp t)

theorem liClockThetaGammaReserveRemovedDensity_pos {p : ℝ} (hp : W < p) {t : ℝ} (ht : 0 < t) :
    0 < ρd p t := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have hT := liClockThetaGammaTailBudget_pos hp
  refine lt_of_lt_of_le ?_ (liClockThetaGammaReserveRemovedDensity_ge hp t)
  rw [liClockThetaGammaRowDensity_one ht]
  positivity

theorem liClockThetaGammaReserveRemovedDensity_of_nonpos (p : ℝ) {t : ℝ} (ht : t ≤ 0) :
    ρd p t = 0 := by
  have h1 : liClockThetaGammaRowDensity p 1 t = 0 := by
    simp [liClockThetaGammaRowDensity, indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.2 ht)]
  simp [liClockThetaGammaReserveRemovedDensity, h1,
    liClockThetaGammaJumpDensity_of_nonpos p true ht]

private theorem jumpDensity_facts {p : ℝ} (hp : W < p) (b : Bool) :
    Integrable (liClockThetaGammaJumpDensity p b) ∧
    (∀ t, 0 ≤ liClockThetaGammaJumpDensity p b t) ∧
    (∫ t, liClockThetaGammaJumpDensity p b t) = Λ p b ∧
    τ p b = volume.withDensity (fun t => ENNReal.ofReal (liClockThetaGammaJumpDensity p b t)) :=
  (liClockThetaGammaJumpDensity_admission_wide hp).1 b

/-- The Gamma jump densities are measurable. -/
theorem measurable_liClockThetaGammaJumpDensity (p : ℝ) (b : Bool) :
    Measurable (liClockThetaGammaJumpDensity p b) := by
  unfold liClockThetaGammaJumpDensity
  exact Measurable.tsum fun j => (measurable_liClockThetaGammaRowDensity p j).const_mul _

private theorem rowLaw_one_eq {p : ℝ} (hp : 0 < p) :
    liClockThetaGammaRowLaw p 1 =
      volume.withDensity (fun t => ENNReal.ofReal (liClockThetaGammaRowDensity p 1 t)) :=
  (liClockThetaGammaRowLaw_admission hp 1).2.2.2 one_pos

private theorem integrable_rowDensity_one {p : ℝ} (hp : 0 < p) :
    Integrable (liClockThetaGammaRowDensity p 1) := by
  have hprob := (liClockThetaGammaRowLaw_admission hp 1).1
  have hm := measurable_liClockThetaGammaRowDensity p 1
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have e : ∫⁻ t, ENNReal.ofReal (liClockThetaGammaRowDensity p 1 t) =
      liClockThetaGammaRowLaw p 1 univ := by
    rw [rowLaw_one_eq hp, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (liClockThetaGammaRowDensity_nonneg hp 1)), e,
    measure_univ]
  exact ENNReal.one_lt_top

theorem integrable_liClockThetaGammaReserveRemovedDensity {p : ℝ} (hp : W < p) :
    Integrable (ρd p) :=
  (jumpDensity_facts hp true).1.sub
    ((integrable_rowDensity_one (liClockThetaWideThreshold_pos.trans hp)).const_mul _)

/-- **(D11)** `τ_p⁺ = δ(p) Γ_{2,p} + ρ_p`. -/
theorem liClockThetaGammaJumpMeasure_true_eq_reserve_add {p : ℝ} (hp : W < p)
    (hδ : 0 ≤ δ p) :
    τ p true = ENNReal.ofReal (δ p) • liClockThetaGammaRowLaw p 1 + ρ p := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  rw [rowLaw_one_eq hp0, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top,
    liClockThetaGammaReserveRemovedMeasure, ← withDensity_add_left
      ((measurable_liClockThetaGammaRowDensity p 1).ennreal_ofReal.const_smul _),
    (jumpDensity_facts hp true).2.2.2]
  congr 1
  funext t
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul hδ, ← ENNReal.ofReal_add
    (mul_nonneg hδ (liClockThetaGammaRowDensity_nonneg hp0 1 t))
    (liClockThetaGammaReserveRemovedDensity_nonneg hp t)]
  unfold liClockThetaGammaReserveRemovedDensity
  ring_nf

theorem isFiniteMeasure_liClockThetaGammaReserveRemovedMeasure {p : ℝ} (hp : W < p) :
    IsFiniteMeasure (ρ p) :=
  isFiniteMeasure_withDensity_ofReal (integrable_liClockThetaGammaReserveRemovedDensity hp).2

/-- **(D11)** `ρ_p ≥ T̄(p) Γ_{2,p}`. -/
theorem liClockThetaGammaRowLaw_one_smul_le_reserveRemoved {p : ℝ} (hp : W < p) :
    ENNReal.ofReal (T̄ p) • liClockThetaGammaRowLaw p 1 ≤ ρ p := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  rw [rowLaw_one_eq hp0, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top,
    liClockThetaGammaReserveRemovedMeasure]
  refine withDensity_mono (ae_of_all _ fun t => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (liClockThetaGammaTailBudget_pos hp).le]
  exact ENNReal.ofReal_le_ofReal (liClockThetaGammaReserveRemovedDensity_ge hp t)

/-- **(D11)** `τ_p⁻ ≥ |ℓ₂(p)| Γ_{4,p}`. -/
theorem liClockThetaGammaRowLaw_two_smul_le_jump_false {p : ℝ} (hp : W < p) :
    ENNReal.ofReal |ℓ p 2| • liClockThetaGammaRowLaw p 2 ≤ τ p false := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  rw [(liClockThetaGammaRowLaw_admission hp0 2).2.2.2 two_pos,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top, (jumpDensity_facts hp false).2.2.2]
  refine withDensity_mono (ae_of_all _ fun t => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases le_or_gt t 0 with ht | ht
  · have h2 : liClockThetaGammaRowDensity p 2 t = 0 := by
      simp [liClockThetaGammaRowDensity,
        indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.2 ht)]
    rw [h2, mul_zero]
    exact (jumpDensity_facts hp false).2.1 t
  · exact liClockThetaGammaJumpDensity_false_ge_second_row hp ht

/-! ## Cumulative functions -/

theorem liClockThetaGammaJumpCDF_eq_primitive {p : ℝ} (hp : W < p) (b : Bool) (T : ℝ) :
    G p b T = ∫ t in (0 : ℝ)..T, liClockThetaGammaJumpDensity p b t := by
  obtain ⟨hi, hnn, -, he⟩ := jumpDensity_facts hp b
  unfold liClockThetaGammaJumpCDF
  rw [he]
  exact withDensity_Ioc_toReal hi hnn (fun t ht => liClockThetaGammaJumpDensity_of_nonpos p b ht) T

theorem liClockThetaGammaReserveRemovedCDF_eq_primitive {p : ℝ} (hp : W < p) (T : ℝ) :
    R p T = ∫ t in (0 : ℝ)..T, ρd p t :=
  withDensity_Ioc_toReal (integrable_liClockThetaGammaReserveRemovedDensity hp)
    (liClockThetaGammaReserveRemovedDensity_nonneg hp)
    (fun _ ht => liClockThetaGammaReserveRemovedDensity_of_nonpos p ht) T

theorem continuous_liClockThetaGammaJumpCDF {p : ℝ} (hp : W < p) (b : Bool) :
    Continuous (G p b) := by
  have e : G p b = fun T => ∫ t in (0 : ℝ)..T, liClockThetaGammaJumpDensity p b t :=
    funext (liClockThetaGammaJumpCDF_eq_primitive hp b)
  rw [e]
  exact intervalIntegral.continuous_primitive
    (fun _ _ => (jumpDensity_facts hp b).1.intervalIntegrable) 0

theorem continuous_liClockThetaGammaReserveRemovedCDF {p : ℝ} (hp : W < p) :
    Continuous (R p) := by
  have e : R p = fun T => ∫ t in (0 : ℝ)..T, ρd p t :=
    funext (liClockThetaGammaReserveRemovedCDF_eq_primitive hp)
  rw [e]
  exact intervalIntegral.continuous_primitive
    (fun _ _ => (integrable_liClockThetaGammaReserveRemovedDensity hp).intervalIntegrable) 0

theorem strictMonoOn_liClockThetaGammaJumpCDF {p : ℝ} (hp : W < p) (b : Bool) :
    StrictMonoOn (G p b) (Ici 0) := by
  have e : G p b = fun T => ∫ t in (0 : ℝ)..T, liClockThetaGammaJumpDensity p b t :=
    funext (liClockThetaGammaJumpCDF_eq_primitive hp b)
  rw [e]
  refine strictMonoOn_primitive (jumpDensity_facts hp b).1 (jumpDensity_facts hp b).2.1
    fun t ht => ?_
  cases b
  · exact liClockThetaGammaJumpDensity_false_pos hp ht
  · exact liClockThetaGammaJumpDensity_true_pos hp ht

theorem strictMonoOn_liClockThetaGammaReserveRemovedCDF {p : ℝ} (hp : W < p) :
    StrictMonoOn (R p) (Ici 0) := by
  have e : R p = fun T => ∫ t in (0 : ℝ)..T, ρd p t :=
    funext (liClockThetaGammaReserveRemovedCDF_eq_primitive hp)
  rw [e]
  exact strictMonoOn_primitive (integrable_liClockThetaGammaReserveRemovedDensity hp)
    (liClockThetaGammaReserveRemovedDensity_nonneg hp)
    fun _ ht => liClockThetaGammaReserveRemovedDensity_pos hp ht

theorem liClockThetaGammaJumpCDF_zero (p : ℝ) (b : Bool) : G p b 0 = 0 := by
  simp [liClockThetaGammaJumpCDF]

theorem liClockThetaGammaReserveRemovedCDF_zero (p : ℝ) : R p 0 = 0 := by
  simp [liClockThetaGammaReserveRemovedCDF]

theorem monotone_liClockThetaGammaJumpCDF {p : ℝ} (hp : W < p) (b : Bool) : Monotone (G p b) := by
  haveI := ((liClockThetaJumpMeasure_admission_wide hp).2 b).2.2.1
  intro T₁ T₂ h
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Ioc_subset_Ioc_right h))

theorem monotone_liClockThetaGammaReserveRemovedCDF {p : ℝ} (hp : W < p) : Monotone (R p) := by
  haveI := isFiniteMeasure_liClockThetaGammaReserveRemovedMeasure hp
  intro T₁ T₂ h
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Ioc_subset_Ioc_right h))

theorem tendsto_liClockThetaGammaJumpCDF {p : ℝ} (hp : W < p) (b : Bool) :
    Tendsto (G p b) atTop (𝓝 (Λ p b)) := by
  have e : G p b = fun T => ∫ t in (0 : ℝ)..T, liClockThetaGammaJumpDensity p b t :=
    funext (liClockThetaGammaJumpCDF_eq_primitive hp b)
  rw [e, ← (jumpDensity_facts hp b).2.2.1]
  exact tendsto_primitive (jumpDensity_facts hp b).1
    fun _ ht => liClockThetaGammaJumpDensity_of_nonpos p b ht

/-- The mass of `ρ_p` is `Λ⁺ - δ(p)`. -/
theorem integral_liClockThetaGammaReserveRemovedDensity {p : ℝ} (hp : W < p) :
    ∫ t, ρd p t = Λ p true - δ p := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have h1 : ∫ t, liClockThetaGammaRowDensity p 1 t = 1 := by
    have h := integral_eq_lintegral_of_nonneg_ae (μ := volume)
      (ae_of_all _ (liClockThetaGammaRowDensity_nonneg hp0 1))
      (measurable_liClockThetaGammaRowDensity p 1).aestronglyMeasurable
    have e : ∫⁻ t, ENNReal.ofReal (liClockThetaGammaRowDensity p 1 t) =
        liClockThetaGammaRowLaw p 1 univ := by
      rw [rowLaw_one_eq hp0, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    haveI := (liClockThetaGammaRowLaw_admission hp0 1).1
    rw [h, e, measure_univ, ENNReal.toReal_one]
  unfold liClockThetaGammaReserveRemovedDensity
  rw [integral_sub (jumpDensity_facts hp true).1
    ((integrable_rowDensity_one hp0).const_mul _), integral_const_mul, h1, mul_one,
    (jumpDensity_facts hp true).2.2.1]

theorem tendsto_liClockThetaGammaReserveRemovedCDF {p : ℝ} (hp : W < p) :
    Tendsto (R p) atTop (𝓝 (Λ p true - δ p)) := by
  have e : R p = fun T => ∫ t in (0 : ℝ)..T, ρd p t :=
    funext (liClockThetaGammaReserveRemovedCDF_eq_primitive hp)
  rw [e, ← integral_liClockThetaGammaReserveRemovedDensity hp]
  exact tendsto_primitive (integrable_liClockThetaGammaReserveRemovedDensity hp)
    fun _ ht => liClockThetaGammaReserveRemovedDensity_of_nonpos p ht

theorem liClockThetaGammaReserveRemovedMeasure_univ {p : ℝ} (hp : W < p) :
    ρ p univ = ENNReal.ofReal (Λ p true - δ p) := by
  rw [liClockThetaGammaReserveRemovedMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← integral_liClockThetaGammaReserveRemovedDensity hp,
    ofReal_integral_eq_lintegral_ofReal (integrable_liClockThetaGammaReserveRemovedDensity hp)
      (ae_of_all _ (liClockThetaGammaReserveRemovedDensity_nonneg hp))]

/-- **(D10, D11)** `Λ⁺ - δ(p) > Λ⁻`: the reserve-removed mass still exceeds the negative mass. -/
theorem liClockThetaJumpMass_false_lt_reserveRemoved {p : ℝ} (hp : W < p) :
    Λ p false < Λ p true - δ p := by
  have h := (liClockThetaJumpMeasure_admission_wide hp).1
  have h2 := (liClockThetaGammaReserve_add_le_reciprocalLog hp).2
  linarith

/-- `R_p(T) = τ_p⁺(0,T] - δ(p) F_{1,p}(T)` for `T ≥ 0`. -/
theorem liClockThetaGammaReserveRemovedCDF_eq {p : ℝ} (hp : W < p) {T : ℝ} (hT : 0 ≤ T) :
    R p T = G p true T - δ p * F p 1 T := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  rw [liClockThetaGammaReserveRemovedCDF_eq_primitive hp,
    liClockThetaGammaJumpCDF_eq_primitive hp, ← integral_liClockThetaGammaRowDensity p one_pos hT,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (jumpDensity_facts hp true).1.intervalIntegrable
      ((integrable_rowDensity_one hp0).const_mul _).intervalIntegrable]
  rfl

/-- **(D11)** `R_p(T) > G_p⁻(T)` for every `T > 0` on the reserve domain. -/
theorem liClockThetaGammaJumpCDF_false_lt_reserveRemoved {p : ℝ}
    (hp : LiClockThetaGammaReserveDomain p) {T : ℝ} (hT : 0 < T) :
    G p false T < R p T := by
  have h := (liEvenCrossActualClockDampedCutoff_gt_gammaReserve hp hT).2
  rw [liEvenCrossActualClockDampedCutoff_eq_gammaJump hp.wide hT.le] at h
  rw [liClockThetaGammaReserveRemovedCDF_eq hp.wide hT.le]
  unfold liClockThetaGammaJumpCDF
  linarith

theorem liClockThetaGammaJumpCDF_le_mass {p : ℝ} (hp : W < p) (b : Bool) (T : ℝ) :
    G p b T ≤ Λ p b :=
  (monotone_liClockThetaGammaJumpCDF hp b).ge_of_tendsto (tendsto_liClockThetaGammaJumpCDF hp b) T

/-! ## (D11) The split point and the quantile coupling -/

theorem ae_pos_liClockThetaGammaReserveRemovedMeasure (p : ℝ) : ∀ᵐ t ∂ρ p, 0 < t := by
  rw [liClockThetaGammaReserveRemovedMeasure, ae_withDensity_iff (by
    unfold liClockThetaGammaReserveRemovedDensity
    exact (((measurable_liClockThetaGammaJumpDensity p true).sub
      ((measurable_liClockThetaGammaRowDensity p 1).const_mul _))).ennreal_ofReal)]
  refine ae_of_all _ fun t ht => ?_
  by_contra hle
  exact ht (by rw [liClockThetaGammaReserveRemovedDensity_of_nonpos p (not_lt.1 hle),
    ENNReal.ofReal_zero])

/-- The split point `a_p` of `ρ_p` at the negative mass `Λ⁻`. -/
def liClockThetaGammaQuantileSplit (p : ℝ) : ℝ := by
  classical
  exact if h : ∃ a, 0 < a ∧ R p a = Λ p false then h.choose else 0

local notation "aₚ" => liClockThetaGammaQuantileSplit

theorem exists_liClockThetaGammaReserveRemovedCDF_eq {p : ℝ}
    (hp : LiClockThetaGammaReserveDomain p) : ∃ a, 0 < a ∧ R p a = Λ p false := by
  have hw := hp.wide
  have hlt := liClockThetaJumpMass_false_lt_reserveRemoved hw
  have hΛ := ((liClockThetaJumpMeasure_admission_wide hw).2 false).1
  obtain ⟨T, hT, hT0⟩ := (((tendsto_liClockThetaGammaReserveRemovedCDF hw).eventually
    (lt_mem_nhds hlt)).and (eventually_ge_atTop 0)).exists
  have hmem : Λ p false ∈ Icc (R p 0) (R p T) := by
    rw [liClockThetaGammaReserveRemovedCDF_zero]
    exact ⟨hΛ.le, hT.le⟩
  obtain ⟨a, ha, hRa⟩ := intermediate_value_Icc hT0
    (continuous_liClockThetaGammaReserveRemovedCDF hw).continuousOn hmem
  refine ⟨a, lt_of_le_of_ne ha.1 ?_, hRa⟩
  rintro rfl
  rw [liClockThetaGammaReserveRemovedCDF_zero] at hRa
  linarith

/-- **(D11)** `a_p > 0` and `R_p(a_p) = Λ⁻`, and `a_p` is the only positive such point. -/
theorem liClockThetaGammaQuantileSplit_spec {p : ℝ} (hp : LiClockThetaGammaReserveDomain p) :
    0 < aₚ p ∧ R p (aₚ p) = Λ p false ∧ ∀ a, 0 < a → R p a = Λ p false → a = aₚ p := by
  classical
  have h := exists_liClockThetaGammaReserveRemovedCDF_eq hp
  have hspec : 0 < aₚ p ∧ R p (aₚ p) = Λ p false := by
    unfold liClockThetaGammaQuantileSplit
    rw [dif_pos h]
    exact h.choose_spec
  refine ⟨hspec.1, hspec.2, fun a ha hRa => ?_⟩
  exact (strictMonoOn_liClockThetaGammaReserveRemovedCDF hp.wide).injOn (mem_Ici.2 ha.le)
    (mem_Ici.2 hspec.1.le) (hRa.trans hspec.2.symm)

/-- `χ_p = ρ_p|(0, a_p]`. -/
def liClockThetaGammaQuantileHead (p : ℝ) : Measure ℝ := (ρ p).restrict (Ioc 0 (aₚ p))

/-- `ζ_p = ρ_p|(a_p, ∞)`. -/
def liClockThetaGammaQuantileTail (p : ℝ) : Measure ℝ := (ρ p).restrict (Ioi (aₚ p))

/-- The upper quantile `X = R_p⁻¹`. -/
def liClockThetaGammaQuantileUpper (p : ℝ) : ℝ → ℝ := halfLineQuantile (R p)

/-- The lower quantile `Y = (G_p⁻)⁻¹`. -/
def liClockThetaGammaQuantileLower (p : ℝ) : ℝ → ℝ := halfLineQuantile (G p false)

local notation "χ" => liClockThetaGammaQuantileHead
local notation "ζ" => liClockThetaGammaQuantileTail
local notation "X" => liClockThetaGammaQuantileUpper
local notation "Y" => liClockThetaGammaQuantileLower

/-- **(D11)** `ρ_p = χ_p + ζ_p`. -/
theorem liClockThetaGammaReserveRemovedMeasure_eq_head_add_tail {p : ℝ}
    (hp : LiClockThetaGammaReserveDomain p) : ρ p = χ p + ζ p := by
  have ha := (liClockThetaGammaQuantileSplit_spec hp).1
  have h0 : ρ p = (ρ p).restrict (Ioi 0) :=
    (Measure.restrict_eq_self_of_ae_mem (ae_pos_liClockThetaGammaReserveRemovedMeasure p)).symm
  rw [liClockThetaGammaQuantileHead, liClockThetaGammaQuantileTail,
    ← Measure.restrict_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi,
    Ioc_union_Ioi_eq_Ioi ha.le, ← h0]

/-- **(D11)** `τ_p⁺ = δ(p) Γ_{2,p} + χ_p + ζ_p`. -/
theorem liClockThetaGammaJumpMeasure_true_eq_quantile {p : ℝ}
    (hp : LiClockThetaGammaReserveDomain p) :
    τ p true = ENNReal.ofReal (δ p) • liClockThetaGammaRowLaw p 1 + χ p + ζ p := by
  rw [liClockThetaGammaJumpMeasure_true_eq_reserve_add hp.wide (liClockThetaGammaReserve_pos hp).le,
    liClockThetaGammaReserveRemovedMeasure_eq_head_add_tail hp, add_assoc]

theorem liClockThetaGammaReserveRemovedMeasure_Ioc {p : ℝ} (hp : W < p) (T : ℝ) :
    ρ p (Ioc 0 T) = ENNReal.ofReal (R p T) := by
  haveI := isFiniteMeasure_liClockThetaGammaReserveRemovedMeasure hp
  rw [liClockThetaGammaReserveRemovedCDF, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **(D11)** `χ_p` has mass `Λ⁻`. -/
theorem liClockThetaGammaQuantileHead_univ {p : ℝ} (hp : LiClockThetaGammaReserveDomain p) :
    χ p univ = ENNReal.ofReal (Λ p false) := by
  rw [liClockThetaGammaQuantileHead, Measure.restrict_apply_univ,
    liClockThetaGammaReserveRemovedMeasure_Ioc hp.wide, (liClockThetaGammaQuantileSplit_spec hp).2.1]

/-- **(D11)** `ζ_p` has mass `H(p) - δ(p) > 0`. -/
theorem liClockThetaGammaQuantileTail_univ {p : ℝ} (hp : LiClockThetaGammaReserveDomain p) :
    ζ p univ = ENNReal.ofReal (H p - δ p) ∧ 0 < H p - δ p := by
  have hw := hp.wide
  haveI := isFiniteMeasure_liClockThetaGammaReserveRemovedMeasure hw
  have hadd := congrArg (fun μ : Measure ℝ => (μ univ).toReal)
    (liClockThetaGammaReserveRemovedMeasure_eq_head_add_tail hp)
  simp only [Measure.add_apply] at hadd
  have hχ : χ p univ ≠ ∞ := by rw [liClockThetaGammaQuantileHead_univ hp]; exact ENNReal.ofReal_ne_top
  have hζ : ζ p univ ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top (ρ p) univ)
    (Measure.restrict_le_self _)
  rw [ENNReal.toReal_add hχ hζ, liClockThetaGammaReserveRemovedMeasure_univ hw,
    liClockThetaGammaQuantileHead_univ hp, ENNReal.toReal_ofReal
      (by linarith [liClockThetaJumpMass_false_lt_reserveRemoved hw,
        ((liClockThetaJumpMeasure_admission_wide hw).2 false).1] : 0 ≤ Λ p true - δ p),
    ENNReal.toReal_ofReal ((liClockThetaJumpMeasure_admission_wide hw).2 false).1.le] at hadd
  have hH := (liClockThetaJumpMeasure_admission_wide hw).1
  refine ⟨?_, by linarith [(liClockThetaGammaReserve_add_le_reciprocalLog hw).2]⟩
  rw [← ENNReal.ofReal_toReal hζ]
  congr 1
  linarith

theorem liClockThetaGammaReserveRemovedCDF_nonneg (p T : ℝ) : 0 ≤ R p T :=
  ENNReal.toReal_nonneg

/-- **(D11)** For `T ≥ 0`, `χ_p(-∞, T] = min(R_p(T), Λ⁻)`; and `χ_p(-∞, T] = 0` for `T < 0`. -/
theorem liClockThetaGammaQuantileHead_Iic {p : ℝ} (hp : LiClockThetaGammaReserveDomain p) (T : ℝ) :
    χ p (Iic T) = if 0 ≤ T then ENNReal.ofReal (min (R p T) (Λ p false)) else 0 := by
  have hspec := liClockThetaGammaQuantileSplit_spec hp
  rw [liClockThetaGammaQuantileHead, Measure.restrict_apply measurableSet_Iic]
  have e : Iic T ∩ Ioc 0 (aₚ p) = Ioc 0 (min T (aₚ p)) := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]
    tauto
  rw [e, liClockThetaGammaReserveRemovedMeasure_Ioc hp.wide]
  split_ifs with hT
  · rw [(monotone_liClockThetaGammaReserveRemovedCDF hp.wide).map_min, hspec.2.1]
  · rw [show min T (aₚ p) = T from min_eq_left (by linarith [hspec.1]),
      show R p T = 0 by simp [liClockThetaGammaReserveRemovedCDF, Ioc_eq_empty (by linarith :
        ¬(0 : ℝ) < T)], ENNReal.ofReal_zero]

theorem liClockThetaGammaJumpMeasure_Iic {p : ℝ} (hp : W < p) (b : Bool) (T : ℝ) :
    τ p b (Iic T) = if 0 ≤ T then ENNReal.ofReal (min (G p b T) (Λ p b)) else 0 := by
  haveI := ((liClockThetaJumpMeasure_admission_wide hp).2 b).2.2.1
  have h0 := measure_Iic_zero_of_ae_pos ((liClockThetaJumpMeasure_admission_wide hp).2 b).2.2.2.2.2.2
  split_ifs with hT
  · rw [measure_Iic_eq_Ioc h0 hT, min_eq_left (liClockThetaGammaJumpCDF_le_mass hp b T),
      liClockThetaGammaJumpCDF, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · exact measure_mono_null (Iic_subset_Iic.2 (not_le.1 hT).le) h0

/-- **(D11)** The CDF of `χ_p` dominates that of `τ_p⁻`. -/
theorem liClockThetaGammaJumpMeasure_false_Iic_le_head {p : ℝ}
    (hp : LiClockThetaGammaReserveDomain p) (T : ℝ) : τ p false (Iic T) ≤ χ p (Iic T) := by
  rw [liClockThetaGammaQuantileHead_Iic hp, liClockThetaGammaJumpMeasure_Iic hp.wide]
  split_ifs with hT
  · refine ENNReal.ofReal_le_ofReal (min_le_min_right _ ?_)
    rcases hT.eq_or_lt with rfl | hT'
    · rw [liClockThetaGammaJumpCDF_zero, liClockThetaGammaReserveRemovedCDF_zero]
    · exact (liClockThetaGammaJumpCDF_false_lt_reserveRemoved hp hT').le
  · exact le_rfl

theorem liClockThetaGammaReserveRemovedCDF_hit {p : ℝ} (hp : LiClockThetaGammaReserveDomain p) :
    ∀ v ∈ Ioo 0 (Λ p false), ∃ t, 0 < t ∧ R p t = v := by
  intro v hv
  have hspec := liClockThetaGammaQuantileSplit_spec hp
  have hmem : v ∈ Icc (R p 0) (R p (aₚ p)) := by
    rw [liClockThetaGammaReserveRemovedCDF_zero, hspec.2.1]
    exact ⟨hv.1.le, hv.2.le⟩
  obtain ⟨t, ht, hRt⟩ := intermediate_value_Icc hspec.1.le
    (continuous_liClockThetaGammaReserveRemovedCDF hp.wide).continuousOn hmem
  refine ⟨t, lt_of_le_of_ne ht.1 ?_, hRt⟩
  rintro rfl
  rw [liClockThetaGammaReserveRemovedCDF_zero] at hRt
  linarith [hv.1]

theorem liClockThetaGammaJumpCDF_false_hit {p : ℝ} (hp : W < p) :
    ∀ v ∈ Ioo 0 (Λ p false), ∃ t, 0 < t ∧ G p false t = v := by
  intro v hv
  obtain ⟨T, hT, hT0⟩ := (((tendsto_liClockThetaGammaJumpCDF hp false).eventually
    (lt_mem_nhds hv.2)).and (eventually_ge_atTop 0)).exists
  have hmem : v ∈ Icc (G p false 0) (G p false T) := by
    rw [liClockThetaGammaJumpCDF_zero]
    exact ⟨hv.1.le, hT.le⟩
  obtain ⟨t, ht, hGt⟩ := intermediate_value_Icc hT0
    (continuous_liClockThetaGammaJumpCDF hp false).continuousOn hmem
  refine ⟨t, lt_of_le_of_ne ht.1 ?_, hGt⟩
  rintro rfl
  rw [liClockThetaGammaJumpCDF_zero] at hGt
  linarith [hv.1]

/-- **(D11)** Both quantiles are positive on `(0, Λ⁻)` and `X < Y` there. -/
theorem liClockThetaGammaQuantile_lt {p : ℝ} (hp : LiClockThetaGammaReserveDomain p) {v : ℝ}
    (hv : v ∈ Ioo 0 (Λ p false)) : 0 < X p v ∧ 0 < Y p v ∧ X p v < Y p v := by
  obtain ⟨hX, hRX⟩ := halfLineQuantile_spec (liClockThetaGammaReserveRemovedCDF_hit hp v hv)
  obtain ⟨hY, hGY⟩ := halfLineQuantile_spec (liClockThetaGammaJumpCDF_false_hit hp.wide v hv)
  refine ⟨hX, hY, ?_⟩
  by_contra hle
  rw [not_lt] at hle
  have h1 := (strictMonoOn_liClockThetaGammaReserveRemovedCDF hp.wide).monotoneOn
    (mem_Ici.2 hY.le) (mem_Ici.2 hX.le) hle
  have h2 := liClockThetaGammaJumpCDF_false_lt_reserveRemoved hp hY
  change R p (halfLineQuantile (R p) v) = v at hRX
  change G p false (halfLineQuantile (G p false) v) = v at hGY
  change R p (halfLineQuantile (G p false) v) ≤ R p (halfLineQuantile (R p) v) at h1
  change G p false (halfLineQuantile (G p false) v) < R p (halfLineQuantile (G p false) v) at h2
  linarith

/-- **(D11)** `X` pushes Lebesgue measure on `(0, Λ⁻)` onto `χ_p`. -/
theorem map_liClockThetaGammaQuantileUpper {p : ℝ} (hp : LiClockThetaGammaReserveDomain p) :
    Measure.map (X p) (volume.restrict (Ioo 0 (Λ p false))) = χ p := by
  haveI : IsFiniteMeasure (χ p) := ⟨by
    rw [liClockThetaGammaQuantileHead_univ hp]; exact ENNReal.ofReal_lt_top⟩
  refine map_halfLineQuantile_eq (strictMonoOn_liClockThetaGammaReserveRemovedCDF hp.wide)
    (liClockThetaGammaReserveRemovedCDF_hit hp) _ (fun T hT => ?_) (fun T hT => ?_)
  · rw [liClockThetaGammaQuantileHead_Iic hp, if_neg (not_le.2 hT)]
  · rw [liClockThetaGammaQuantileHead_Iic hp, if_pos hT]

/-- **(D11)** `Y` pushes Lebesgue measure on `(0, Λ⁻)` onto `τ_p⁻`. -/
theorem map_liClockThetaGammaQuantileLower {p : ℝ} (hp : W < p) :
    Measure.map (Y p) (volume.restrict (Ioo 0 (Λ p false))) = τ p false := by
  haveI := ((liClockThetaJumpMeasure_admission_wide hp).2 false).2.2.1
  refine map_halfLineQuantile_eq (strictMonoOn_liClockThetaGammaJumpCDF hp false)
    (liClockThetaGammaJumpCDF_false_hit hp) _ (fun T hT => ?_) (fun T hT => ?_)
  · rw [liClockThetaGammaJumpMeasure_Iic hp, if_neg (not_le.2 hT)]
  · rw [liClockThetaGammaJumpMeasure_Iic hp, if_pos hT]

/-- The uniform probability law on `(0, Λ⁻)`. -/
def liClockThetaGammaQuantileUniform (p : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (Λ p false))⁻¹ • volume.restrict (Ioo 0 (Λ p false))

theorem isProbabilityMeasure_liClockThetaGammaQuantileUniform {p : ℝ} (hp : W < p) :
    IsProbabilityMeasure (liClockThetaGammaQuantileUniform p) := by
  have hΛ := ((liClockThetaJumpMeasure_admission_wide hp).2 false).1
  constructor
  rw [liClockThetaGammaQuantileUniform, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Ioo, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hΛ).ne' ENNReal.ofReal_ne_top

/-- **(D11)** `Law(X) = χ_p/Λ⁻` and `Law(Y) = τ_p⁻/Λ⁻` under the uniform law on `(0, Λ⁻)`. -/
theorem map_liClockThetaGammaQuantileUniform {p : ℝ} (hp : LiClockThetaGammaReserveDomain p) :
    Measure.map (X p) (liClockThetaGammaQuantileUniform p) =
        (ENNReal.ofReal (Λ p false))⁻¹ • χ p ∧
      Measure.map (Y p) (liClockThetaGammaQuantileUniform p) =
        (ENNReal.ofReal (Λ p false))⁻¹ • τ p false := by
  unfold liClockThetaGammaQuantileUniform
  rw [Measure.map_smul, Measure.map_smul, map_liClockThetaGammaQuantileUpper hp,
    map_liClockThetaGammaQuantileLower hp.wide]
  exact ⟨rfl, rfl⟩

/-! ## (D12) Nonincreasing tests -/

private theorem integrable_of_bdd {μ : Measure ℝ} [IsFiniteMeasure μ] {h : ℝ → ℝ}
    (hm : Measurable h) (hb : ∃ C, ∀ t, |h t| ≤ C) : Integrable h μ := by
  obtain ⟨C, hC⟩ := hb
  exact (integrable_const C).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hC t)

private theorem integrable_of_bdd' {μ : Measure ℝ} [IsFiniteMeasure μ] {h g : ℝ → ℝ}
    (hm : Measurable h) (hb : ∃ C, ∀ t, |h t| ≤ C) (hg : AEMeasurable g μ) :
    Integrable (fun v => h (g v)) μ := by
  obtain ⟨C, hC⟩ := hb
  exact (integrable_const C).mono' (hm.comp_aemeasurable hg).aestronglyMeasurable
    (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hC _)

/-- **(D12)** Every bounded measurable nonnegative `h`, nonincreasing on `(0, ∞)`, satisfies
`∫ h dτ_p⁺ - ∫ h dτ_p⁻ ≥ δ(p) ∫ h dΓ_{2,p} ≥ 0`, strictly when `∫ h dΓ_{2,p} > 0`. -/
theorem liClockThetaGammaJump_integral_sub_ge_of_antitoneOn {p : ℝ}
    (hp : LiClockThetaGammaReserveDomain p) {h : ℝ → ℝ} (hm : Measurable h)
    (hb : ∃ C, ∀ t, |h t| ≤ C) (hnn : ∀ t, 0 ≤ h t) (hanti : AntitoneOn h (Ioi 0)) :
    δ p * ∫ t, h t ∂liClockThetaGammaRowLaw p 1 ≤
        (∫ t, h t ∂τ p true) - ∫ t, h t ∂τ p false ∧
      0 ≤ δ p * ∫ t, h t ∂liClockThetaGammaRowLaw p 1 ∧
      (0 < ∫ t, h t ∂liClockThetaGammaRowLaw p 1 →
        0 < (∫ t, h t ∂τ p true) - ∫ t, h t ∂τ p false) := by
  have hw := hp.wide
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hw
  have hδ := liClockThetaGammaReserve_pos hp
  haveI := (liClockThetaGammaRowLaw_admission hp0 1).1
  haveI : IsFiniteMeasure (ENNReal.ofReal (δ p) • liClockThetaGammaRowLaw p 1) :=
    ⟨by rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure (ρ p) := isFiniteMeasure_liClockThetaGammaReserveRemovedMeasure hw
  haveI : IsFiniteMeasure (χ p) := by unfold liClockThetaGammaQuantileHead; infer_instance
  haveI : IsFiniteMeasure (ζ p) := by unfold liClockThetaGammaQuantileTail; infer_instance
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) (Λ p false))) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  have hXm : AEMeasurable (X p) (volume.restrict (Ioo 0 (Λ p false))) :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Ioo
      (halfLineQuantile_strictMonoOn (strictMonoOn_liClockThetaGammaReserveRemovedCDF hw)
        (liClockThetaGammaReserveRemovedCDF_hit hp)).monotoneOn
  have hYm : AEMeasurable (Y p) (volume.restrict (Ioo 0 (Λ p false))) :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Ioo
      (halfLineQuantile_strictMonoOn (strictMonoOn_liClockThetaGammaJumpCDF hw false)
        (liClockThetaGammaJumpCDF_false_hit hw)).monotoneOn
  have hχ : ∫ t, h t ∂χ p = ∫ v, h (X p v) ∂volume.restrict (Ioo 0 (Λ p false)) := by
    rw [← map_liClockThetaGammaQuantileUpper hp, integral_map hXm hm.aestronglyMeasurable]
  have hτ : ∫ t, h t ∂τ p false = ∫ v, h (Y p v) ∂volume.restrict (Ioo 0 (Λ p false)) := by
    rw [← map_liClockThetaGammaQuantileLower hw, integral_map hYm hm.aestronglyMeasurable]
  have hXY : ∫ v, h (Y p v) ∂volume.restrict (Ioo 0 (Λ p false)) ≤
      ∫ v, h (X p v) ∂volume.restrict (Ioo 0 (Λ p false)) := by
    refine integral_mono_ae (integrable_of_bdd' hm hb hYm) (integrable_of_bdd' hm hb hXm) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun v hv => ?_)
    obtain ⟨hX, hY, hlt⟩ := liClockThetaGammaQuantile_lt hp hv
    exact hanti hX hY hlt.le
  have hplus : ∫ t, h t ∂τ p true = δ p * ∫ t, h t ∂liClockThetaGammaRowLaw p 1 +
      ∫ t, h t ∂χ p + ∫ t, h t ∂ζ p := by
    rw [liClockThetaGammaJumpMeasure_true_eq_quantile hp,
      integral_add_measure ((integrable_of_bdd hm hb).add_measure (integrable_of_bdd hm hb))
        (integrable_of_bdd hm hb),
      integral_add_measure (integrable_of_bdd hm hb) (integrable_of_bdd hm hb),
      integral_smul_measure, ENNReal.toReal_ofReal hδ.le, smul_eq_mul]
  have hζ : 0 ≤ ∫ t, h t ∂ζ p := integral_nonneg hnn
  have hΓ : 0 ≤ ∫ t, h t ∂liClockThetaGammaRowLaw p 1 := integral_nonneg hnn
  refine ⟨by linarith, mul_nonneg hδ.le hΓ, fun hpos => ?_⟩
  have := mul_pos hδ hpos
  linarith

end RHTower
