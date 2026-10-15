import GaloisForLFunctions.RHTower.CHMDKleinGordonSeparationLawAndApproximateRealisation

/-!
# CHMD: The Forced Spectral Measure and the Off-Line Defect Wave

The growth–positivity collapse reduced the Riemann Hypothesis to the existence of a spectral
realisation of the causal wave `φ_Λ(y) = cosineShiftFn Λ sechHalf y`: a finite positive measure
`ν` on the frequency line with `charFun ν = φ_Λ`, allowed to carry a bounded defect. This module
settles **which** measure that can be, unconditionally.

1. **The Klein–Gordon zero measure exists unconditionally.**
   `kgZeroMeasure := Σ_ρ m_ρ (Re w_ρ / 2) (δ_{Re ρ_ρ} + δ_{−Re ρ_ρ})`, with `ρ_ρ = √(γ_ρ² + 2)` and
   `w_ρ = sech²(γ_ρ/2)`, is a finite positive measure on `ℝ` with no hypothesis, since `Re w_ρ > 0`
   at every zero on or off the line. Its characteristic function is the **shadow wave**
   `shadowWave t = Σ_ρ m_ρ (Re w_ρ) cos(t Re ρ_ρ)`, a bounded positive-definite function with
   `shadowWave 0 = φ_Λ(0)` (`charFun_kgZeroMeasure`, `abs_shadowWave_le_zero_value`).
2. **The off-line defect wave.** `offLineDefectWave = φ_Λ − shadowWave` is a series over the zeros
   whose on-line terms vanish identically (`defectTerm_eq_zero_of_im_kgFreq_eq_zero`). Hence
   `RiemannHypothesis ⟺ offLineDefectWave ≡ 0 ⟺ offLineDefectWave` is bounded above on `[0, ∞)`
   (`riemannHypothesis_iff_offLineDefectWave_eq_zero`,
   `riemannHypothesis_iff_offLineDefectWave_bddAbove`).
3. **Forcing and uniqueness.** `RiemannHypothesis ⟺ charFun kgZeroMeasure = φ_Λ`
   (`riemannHypothesis_iff_charFun_kgZeroMeasure_eq`), and under `RiemannHypothesis` every finite
   measure whose characteristic function is `φ_Λ` equals `kgZeroMeasure`
   (`eq_kgZeroMeasure_of_charFun_eq`). The realisation class with bounded defect is nonempty iff
   `RiemannHypothesis` (`riemannHypothesis_iff_exists_finiteMeasure_charFun_defect`), and its
   unique exact member is the zero measure itself.

So the object demanded by the spectral-realisation programme is produced: it is `kgZeroMeasure`,
the only candidate, and it realises the causal wave exactly when the off-line defect wave vanishes.
There is no second object to construct, and no construction can avoid the zeros.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators ComplexConjugate ENNReal

noncomputable section

namespace RHTower.CHMDForcedMeasure

open WeilOneSided WeilSpectral GaloisForLFunctions.HTGeometry RHTower.EvenSector
open RHTower.CHMDStage4 RHTower.CHMDGrowthCollapse

/-! ## Section 1: Atoms, weights, and the Klein–Gordon zero measure -/

/-- The atom `Re √(γ_ρ² + 2)` of a nontrivial zero. -/
def kgAtom (ρ : zetaZeroConfig.carrier) : ℝ := (kgFreq ρ).re

/-- The half-weight `m_ρ (Re sech²(γ_ρ/2)) / 2 ≥ 0` of a nontrivial zero. -/
def kgAtomWeight (ρ : zetaZeroConfig.carrier) : ℝ :=
  (zetaZeroConfig.mult ρ : ℝ) * (kgWeight ρ).re / 2

theorem kgAtomWeight_nonneg (ρ : zetaZeroConfig.carrier) : 0 ≤ kgAtomWeight ρ := by
  unfold kgAtomWeight
  have := (re_kgWeight_pos ρ).le
  positivity

theorem kgAtomWeight_le (ρ : zetaZeroConfig.carrier) :
    kgAtomWeight ρ ≤ (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ := by
  unfold kgAtomWeight
  have h1 : (kgWeight ρ).re ≤ ‖kgWeight ρ‖ := Complex.re_le_norm _
  have h2 : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have h3 : 0 ≤ (kgWeight ρ).re := (re_kgWeight_pos ρ).le
  nlinarith [mul_le_mul_of_nonneg_left h1 h2]

theorem summable_kgAtomWeight : Summable kgAtomWeight :=
  Summable.of_nonneg_of_le kgAtomWeight_nonneg kgAtomWeight_le summable_mult_mul_norm_kgWeight

/-- **The Klein–Gordon zero measure** `Σ_ρ m_ρ (Re w_ρ / 2) (δ_{Re ρ_ρ} + δ_{−Re ρ_ρ})`. -/
def kgZeroMeasure : Measure ℝ :=
  Measure.sum fun ρ : zetaZeroConfig.carrier =>
    ENNReal.ofReal (kgAtomWeight ρ) • (Measure.dirac (kgAtom ρ) + Measure.dirac (-kgAtom ρ))

theorem kgZeroMeasure_univ :
    kgZeroMeasure univ = ENNReal.ofReal (∑' ρ : zetaZeroConfig.carrier, 2 * kgAtomWeight ρ) := by
  unfold kgZeroMeasure
  rw [Measure.sum_apply _ MeasurableSet.univ,
    ENNReal.ofReal_tsum_of_nonneg (fun ρ => by linarith [kgAtomWeight_nonneg ρ])
      (summable_kgAtomWeight.mul_left 2)]
  refine tsum_congr fun ρ => ?_
  rw [Measure.smul_apply, Measure.add_apply, Measure.dirac_apply_of_mem (mem_univ _),
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_comm (2 : ℝ),
    ENNReal.ofReal_mul (kgAtomWeight_nonneg ρ), ENNReal.ofReal_ofNat]
  norm_num

instance : IsFiniteMeasure kgZeroMeasure :=
  ⟨by rw [kgZeroMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

/-- Bounded measurable functions are integrable against the zero measure. -/
theorem integrable_kgZeroMeasure_of_bounded {f : ℝ → ℂ} (hf : AEStronglyMeasurable f kgZeroMeasure)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) : Integrable f kgZeroMeasure :=
  (integrable_const B).mono' hf (ae_of_all _ hB)

/-- **Integration against the zero measure** is the weighted sum over the atoms. -/
theorem integral_kgZeroMeasure {f : ℝ → ℂ} (hint : Integrable f kgZeroMeasure) :
    ∫ x, f x ∂kgZeroMeasure =
      ∑' ρ : zetaZeroConfig.carrier, (kgAtomWeight ρ : ℂ) * (f (kgAtom ρ) + f (-kgAtom ρ)) := by
  unfold kgZeroMeasure at hint ⊢
  rw [integral_sum_measure hint]
  refine tsum_congr fun ρ => ?_
  rw [integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp)), integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (kgAtomWeight_nonneg ρ), Complex.real_smul]

/-! ## Section 2: The shadow wave is the characteristic function of the zero measure -/

/-- **The shadow wave** `Σ_ρ m_ρ (Re w_ρ) cos(t Re ρ_ρ)`: the on-line shadow of the causal wave. -/
def shadowWave (t : ℝ) : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) * (kgWeight ρ).re * Real.cos (t * kgAtom ρ)

theorem summable_shadowTerm (t : ℝ) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (kgWeight ρ).re * Real.cos (t * kgAtom ρ) := by
  refine Summable.of_norm_bounded (summable_kgAtomWeight.mul_left 2) fun ρ => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, Nat.abs_cast, abs_of_nonneg (re_kgWeight_pos ρ).le]
  have h1 := Real.abs_cos_le_one (t * kgAtom ρ)
  have h2 : (0 : ℝ) ≤ (zetaZeroConfig.mult ρ : ℝ) * (kgWeight ρ).re :=
    mul_nonneg (Nat.cast_nonneg _) (re_kgWeight_pos ρ).le
  unfold kgAtomWeight
  nlinarith

theorem abs_shadowWave_le_zero_value (t : ℝ) : |shadowWave t| ≤ shadowWave 0 := by
  unfold shadowWave
  have h0 := summable_shadowTerm 0
  have ht := summable_shadowTerm t
  have hterm : ∀ ρ : zetaZeroConfig.carrier,
      |(zetaZeroConfig.mult ρ : ℝ) * (kgWeight ρ).re * Real.cos (t * kgAtom ρ)| ≤
        (zetaZeroConfig.mult ρ : ℝ) * (kgWeight ρ).re * Real.cos (0 * kgAtom ρ) := by
    intro ρ
    rw [zero_mul, Real.cos_zero, mul_one, abs_mul, abs_mul, Nat.abs_cast,
      abs_of_nonneg (re_kgWeight_pos ρ).le]
    have h2 : (0 : ℝ) ≤ (zetaZeroConfig.mult ρ : ℝ) * (kgWeight ρ).re :=
      mul_nonneg (Nat.cast_nonneg _) (re_kgWeight_pos ρ).le
    exact mul_le_of_le_one_right h2 (Real.abs_cos_le_one _)
  calc |∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) * (kgWeight ρ).re * Real.cos (t * kgAtom ρ)|
      ≤ ∑' ρ : zetaZeroConfig.carrier,
          |(zetaZeroConfig.mult ρ : ℝ) * (kgWeight ρ).re * Real.cos (t * kgAtom ρ)| := by
        have := norm_tsum_le_tsum_norm (f := fun ρ : zetaZeroConfig.carrier =>
          (zetaZeroConfig.mult ρ : ℝ) * (kgWeight ρ).re * Real.cos (t * kgAtom ρ)) ht.abs
        simpa only [Real.norm_eq_abs] using this
    _ ≤ _ := Summable.tsum_le_tsum hterm ht.abs h0

theorem shadowWave_zero : shadowWave 0 = chmdWave 0 := by
  rw [chmdWave_eq_tsum_re]
  unfold shadowWave
  refine tsum_congr fun ρ => ?_
  rw [zero_mul, Real.cos_zero, mul_one]
  have : ((0 : ℝ) : ℂ) * kgFreq ρ = 0 := by simp
  rw [this, Complex.cos_zero, one_mul]

theorem exp_add_exp_neg_eq (x : ℝ) :
    Complex.exp ((x : ℂ) * I) + Complex.exp (((-x : ℝ) : ℂ) * I) = ((2 * Real.cos x : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  field_simp

/-- **The characteristic function of the zero measure is the shadow wave.** -/
theorem charFun_kgZeroMeasure (t : ℝ) : charFun kgZeroMeasure t = (shadowWave t : ℂ) := by
  rw [charFun_apply]
  have hcont : Continuous fun x : ℝ => Complex.exp (((inner ℝ x t : ℝ) : ℂ) * I) := by
    have : Continuous fun x : ℝ => (inner ℝ x t : ℝ) := by
      simp only [RCLike.inner_apply, conj_trivial]
      exact continuous_const.mul continuous_id
    exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp this).mul continuous_const)
  have hint : Integrable (fun x : ℝ => Complex.exp (((inner ℝ x t : ℝ) : ℂ) * I)) kgZeroMeasure :=
    integrable_kgZeroMeasure_of_bounded hcont.aestronglyMeasurable (B := 1) fun x => by
      rw [Complex.norm_exp]
      simp
  rw [integral_kgZeroMeasure hint]
  unfold shadowWave
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun ρ => ?_
  have hinner : ∀ x : ℝ, (inner ℝ x t : ℝ) = t * x := by
    intro x; simp [RCLike.inner_apply]
  rw [hinner, hinner, show t * -kgAtom ρ = -(t * kgAtom ρ) by ring, exp_add_exp_neg_eq]
  unfold kgAtomWeight
  push_cast
  ring

/-! ## Section 3: The off-line defect wave -/

/-- **The off-line defect wave** `φ_Λ − shadowWave`. -/
def offLineDefectWave (t : ℝ) : ℝ := chmdWave t - shadowWave t

/-- One defect term: `Re(cos(t ρ_ρ) w_ρ) − (Re w_ρ) cos(t Re ρ_ρ)`. -/
def defectTerm (t : ℝ) (ρ : zetaZeroConfig.carrier) : ℝ :=
  (zetaZeroConfig.mult ρ : ℝ) *
    ((Complex.cos (t * kgFreq ρ) * kgWeight ρ).re - (kgWeight ρ).re * Real.cos (t * kgAtom ρ))

theorem offLineDefectWave_eq_tsum (t : ℝ) :
    offLineDefectWave t = ∑' ρ : zetaZeroConfig.carrier, defectTerm t ρ := by
  unfold offLineDefectWave
  rw [chmdWave_eq_tsum_re]
  unfold shadowWave
  rw [← (summable_re_cosTerm t).tsum_sub (summable_shadowTerm t)]
  refine tsum_congr fun ρ => ?_
  unfold defectTerm
  ring

/-- **On-line zeros contribute nothing to the defect wave.** -/
theorem defectTerm_eq_zero_of_im_kgFreq_eq_zero {ρ : zetaZeroConfig.carrier}
    (h : (kgFreq ρ).im = 0) (t : ℝ) : defectTerm t ρ = 0 := by
  unfold defectTerm kgAtom
  have hreal : kgFreq ρ = (((kgFreq ρ).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [h]
  rw [hreal, Complex.ofReal_re, ← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.re_ofReal_mul]
  ring

/-- **Under the Riemann Hypothesis the causal wave is its own shadow.** -/
theorem chmdWave_eq_shadowWave_of_rh (hRH : RiemannHypothesis) (t : ℝ) :
    chmdWave t = shadowWave t := by
  have h : offLineDefectWave t = 0 := by
    rw [offLineDefectWave_eq_tsum,
      tsum_congr fun ρ => defectTerm_eq_zero_of_im_kgFreq_eq_zero (kgFreq_kgWeight_of_rh hRH ρ).1 t]
    exact tsum_zero
  unfold offLineDefectWave at h
  linarith

/-- **Riemann Hypothesis ⟺ the off-line defect wave vanishes identically.** -/
theorem riemannHypothesis_iff_offLineDefectWave_eq_zero :
    RiemannHypothesis ↔ ∀ t : ℝ, offLineDefectWave t = 0 := by
  constructor
  · intro hRH t
    unfold offLineDefectWave
    rw [chmdWave_eq_shadowWave_of_rh hRH t, sub_self]
  · intro h
    refine riemannHypothesis_iff_chmdWave_bddAbove.mpr ⟨shadowWave 0, fun u _ => ?_⟩
    have h1 := h u
    unfold offLineDefectWave at h1
    have h2 := abs_shadowWave_le_zero_value u
    linarith [le_abs_self (shadowWave u)]

/-- **Riemann Hypothesis ⟺ the off-line defect wave is bounded above on `[0, ∞)`.** -/
theorem riemannHypothesis_iff_offLineDefectWave_bddAbove :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → offLineDefectWave u ≤ C := by
  constructor
  · intro hRH
    exact ⟨0, fun u _ => by
      rw [riemannHypothesis_iff_offLineDefectWave_eq_zero.mp hRH u]⟩
  · rintro ⟨C, hC⟩
    refine riemannHypothesis_iff_chmdWave_bddAbove.mpr ⟨shadowWave 0 + C, fun u hu => ?_⟩
    have h1 := hC u hu
    unfold offLineDefectWave at h1
    have h2 := abs_shadowWave_le_zero_value u
    linarith [le_abs_self (shadowWave u)]

/-! ## Section 4: Forcing and uniqueness of the spectral measure -/

/-- **Riemann Hypothesis ⟺ the zero measure realises the causal wave.** -/
theorem riemannHypothesis_iff_charFun_kgZeroMeasure_eq :
    RiemannHypothesis ↔ ∀ t : ℝ, charFun kgZeroMeasure t = (chmdWave t : ℂ) := by
  rw [riemannHypothesis_iff_offLineDefectWave_eq_zero]
  refine forall_congr' fun t => ?_
  rw [charFun_kgZeroMeasure]
  unfold offLineDefectWave
  constructor
  · intro h; rw [sub_eq_zero] at h; rw [h]
  · intro h; rw [sub_eq_zero]; exact_mod_cast h.symm

/-- **Uniqueness**: under the Riemann Hypothesis, every finite measure whose characteristic function
is the causal wave is the Klein–Gordon zero measure. -/
theorem eq_kgZeroMeasure_of_charFun_eq (hRH : RiemannHypothesis) {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hν : ∀ t : ℝ, charFun ν t = (chmdWave t : ℂ)) : ν = kgZeroMeasure := by
  apply Measure.ext_of_charFun
  funext t
  rw [hν t, (riemannHypothesis_iff_charFun_kgZeroMeasure_eq.mp hRH) t]

/-- **The realisation class with bounded defect is nonempty exactly under the Riemann Hypothesis**,
and its unique exact member is the zero measure. -/
theorem riemannHypothesis_iff_exists_finiteMeasure_charFun_defect :
    RiemannHypothesis ↔ ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → chmdWave u ≤ (charFun ν u).re + C := by
  constructor
  · intro hRH
    refine ⟨kgZeroMeasure, inferInstance, 0, fun u _ => ?_⟩
    rw [(riemannHypothesis_iff_charFun_kgZeroMeasure_eq.mp hRH) u, Complex.ofReal_re, add_zero]
  · rintro ⟨ν, hfin, C, hC⟩
    refine riemannHypothesis_iff_chmdWave_bddAbove.mpr ⟨ν.real univ + C, fun u hu => ?_⟩
    have h1 := hC u hu
    have h2 : (charFun ν u).re ≤ ν.real univ := (Complex.re_le_norm _).trans (norm_charFun_le u)
    linarith

/-- **Uniqueness of the exact realisation, without assuming the Riemann Hypothesis separately**:
any finite measure realising the causal wave is the zero measure (its existence implies the
Riemann Hypothesis by the Stage 4 criterion). -/
theorem eq_kgZeroMeasure_of_charFun_eq' {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ∀ t : ℝ, charFun ν t = (chmdWave t : ℂ)) : ν = kgZeroMeasure :=
  eq_kgZeroMeasure_of_charFun_eq
    (riemannHypothesis_iff_exists_sechHalf_measure_vonMangoldt.mpr ⟨ν, inferInstance, hν⟩) hν

end RHTower.CHMDForcedMeasure

end
