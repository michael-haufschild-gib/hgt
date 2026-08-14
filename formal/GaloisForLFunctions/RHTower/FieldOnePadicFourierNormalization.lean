import GaloisForLFunctions.RHTower.FieldOnePadicUnitBallNormalizedHaar
import GaloisForLFunctions.RHTower.FieldOnePadicStandardWeylCharacter
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-!
# Exact `p`-adic Fourier normalization

This file identifies every scalar entering the finite-level reduction of the
standard Fourier transform on `ℚ_p`:

* `p⁻ⁿℤ_p` is the literal denominator stage;
* pullback of unit-ball-normalized Haar measure along `u ↦ p⁻ⁿu` is exactly
  `pⁿ` times probability Haar measure on `ℤ_p`; and
* the standard source additive character at `-p⁻ⁿu` is exactly the standard
  cyclic character of `u mod pⁿ`.

These are equalities on the actual local field and its actual Haar integral,
not hypotheses attached to an abstract Fourier operator.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Pointwise

variable (p : ℕ) [Fact p.Prime]

/-- The unit of `ℚ_p` represented by `p⁻ⁿ`. -/
def fieldOnePadicPrimeInvPowUnit (n : ℕ) : ℚ_[p]ˣ :=
  (fieldOnePadicPrimeUnit p)⁻¹ ^ n

@[simp]
theorem fieldOnePadicPrimeInvPowUnit_val (n : ℕ) :
    (fieldOnePadicPrimeInvPowUnit p n : ℚ_[p]) =
      ((p : ℚ_[p]) ^ n)⁻¹ := by
  simp [fieldOnePadicPrimeInvPowUnit, fieldOnePadicPrimeUnit]

/-- Additive embedding `ℤ_p → ℚ_p`, `u ↦ p⁻ⁿu`. -/
def fieldOnePadicInvPowIntCoeAddMonoidHom (n : ℕ) : ℤ_[p] →+ ℚ_[p] where
  toFun u := (fieldOnePadicPrimeInvPowUnit p n : ℚ_[p]) * (u : ℚ_[p])
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

theorem fieldOnePadicInvPowIntCoeAddMonoidHom_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding
      (fieldOnePadicInvPowIntCoeAddMonoidHom p n) := by
  change Topology.IsOpenEmbedding (fun u : ℤ_[p] =>
    (fieldOnePadicPrimeInvPowUnit p n : ℚ_[p]) * (u : ℚ_[p]))
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · fun_prop
  · intro x y hxy
    apply PadicInt.ext
    exact mul_left_cancel₀
      (Units.ne_zero (fieldOnePadicPrimeInvPowUnit p n)) hxy
  · have hopenUnitBall : IsOpen {x : ℚ_[p] | ‖x‖ ≤ 1} := by
      simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
        IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero
    have hcoe : IsOpenMap ((↑) : ℤ_[p] → ℚ_[p]) :=
      hopenUnitBall.isOpenMap_subtype_val
    intro U hU
    have hUcoe : IsOpen (((↑) : ℤ_[p] → ℚ_[p]) '' U) := hcoe U hU
    have hUscaled :=
      (Homeomorph.isOpenMap (Homeomorph.smul (α := ℚ_[p])
        (fieldOnePadicPrimeInvPowUnit p n)))
          (((↑) : ℤ_[p] → ℚ_[p]) '' U) hUcoe
    convert hUscaled using 1
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(u : ℚ_[p]), ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, rfl⟩

theorem fieldOnePadicInvPowIntCoeAddMonoidHom_image (n : ℕ) :
    fieldOnePadicInvPowIntCoeAddMonoidHom p n ''
        (Set.univ : Set ℤ_[p]) =
      fieldOnePadicPrimeInvPowUnit p n •
        Set.range ((↑) : ℤ_[p] → ℚ_[p]) := by
  ext x
  constructor
  · rintro ⟨u, -, rfl⟩
    rw [Set.mem_smul_set]
    exact ⟨(u : ℚ_[p]), ⟨u, rfl⟩, rfl⟩
  · rw [Set.mem_smul_set]
    rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, Set.mem_univ _, rfl⟩

/-- Exact identification of `p⁻ⁿℤ_p` with the denominator stage used by the
canonical all-depth additive character. -/
theorem fieldOnePadicInvPowIntCoeAddMonoidHom_range (n : ℕ) :
    Set.range (fieldOnePadicInvPowIntCoeAddMonoidHom p n) =
      (fieldOnePadicDenominatorStage p n : Set ℚ_[p]) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    change ‖(p : ℚ_[p]) ^ n *
      ((fieldOnePadicPrimeInvPowUnit p n : ℚ_[p]) * (u : ℚ_[p]))‖ ≤ 1
    rw [fieldOnePadicPrimeInvPowUnit_val, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero n hp0), one_mul]
    exact u.property
  · intro hx
    let u := fieldOnePadicDenominatorStageIntegral p n ⟨x, hx⟩
    refine ⟨u, ?_⟩
    change (fieldOnePadicPrimeInvPowUnit p n : ℚ_[p]) *
      (u : ℚ_[p]) = x
    rw [fieldOnePadicPrimeInvPowUnit_val]
    change ((p : ℚ_[p]) ^ n)⁻¹ * ((p : ℚ_[p]) ^ n * x) = x
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hp0), one_mul]

theorem fieldOnePadicPrimeInvPowUnit_distribHaarChar (n : ℕ) :
    distribHaarChar ℚ_[p] (fieldOnePadicPrimeInvPowUnit p n) =
      (p : ℝ≥0) ^ n := by
  rw [fieldOnePadicPrimeInvPowUnit, map_pow, map_inv,
    fieldOnePadicPrimeUnit_distribHaarChar]
  simp

theorem fieldOnePadicUnitBallNormalizedHaar_scaledUnitBall (n : ℕ) :
    fieldOnePadicUnitBallNormalizedHaar p
      (fieldOnePadicPrimeInvPowUnit p n •
        Set.range ((↑) : ℤ_[p] → ℚ_[p])) =
      (p : ℝ≥0∞) ^ n := by
  rw [← MeasureTheory.distribHaarChar_mul
    (fieldOnePadicUnitBallNormalizedHaar p)
    (fieldOnePadicPrimeInvPowUnit p n)
    (Set.range ((↑) : ℤ_[p] → ℚ_[p])),
    fieldOnePadicPrimeInvPowUnit_distribHaarChar,
    fieldOnePadicUnitBallNormalizedHaar_unitBall]
  simp

/-- Pullback of ambient Haar measure along `u ↦ p⁻ⁿu`. -/
def fieldOnePadicInvPowIntHaarComap (n : ℕ) : Measure ℤ_[p] :=
  (fieldOnePadicUnitBallNormalizedHaar p).comap
    (fieldOnePadicInvPowIntCoeAddMonoidHom p n)

instance fieldOnePadicInvPowIntHaarComap_isAddHaar (n : ℕ) :
    (fieldOnePadicInvPowIntHaarComap p n).IsAddHaarMeasure := by
  unfold fieldOnePadicInvPowIntHaarComap
  exact Measure.IsAddHaarMeasure.comap
    (mH := fieldOnePadicMeasurableAdd p)
    (fieldOnePadicUnitBallNormalizedHaar p)
    (fieldOnePadicInvPowIntCoeAddMonoidHom_isOpenEmbedding p n)

@[simp]
theorem fieldOnePadicInvPowIntHaarComap_univ (n : ℕ) :
    fieldOnePadicInvPowIntHaarComap p n Set.univ =
      (p : ℝ≥0∞) ^ n := by
  rw [fieldOnePadicInvPowIntHaarComap,
    (fieldOnePadicInvPowIntCoeAddMonoidHom_isOpenEmbedding p n).measurableEmbedding.comap_apply,
    fieldOnePadicInvPowIntCoeAddMonoidHom_image,
    fieldOnePadicUnitBallNormalizedHaar_scaledUnitBall]

/-- Exact Haar Jacobian of `u ↦ p⁻ⁿu`. -/
theorem fieldOnePadicInvPowIntHaarComap_eq_smul (n : ℕ) :
    fieldOnePadicInvPowIntHaarComap p n =
      ((p : ℝ≥0∞) ^ n) • fieldOnePadicIntNormalizedHaar p := by
  let c : ℝ≥0∞ := (p : ℝ≥0∞) ^ n
  have hc0 : c ≠ 0 := by
    exact pow_ne_zero n (by simp [(Fact.out : Nat.Prime p).ne_zero])
  have hctop : c ≠ ∞ := by simp [c]
  let νprob : Measure ℤ_[p] :=
    c⁻¹ • fieldOnePadicInvPowIntHaarComap p n
  letI : νprob.IsAddHaarMeasure := by
    dsimp [νprob]
    exact Measure.IsAddHaarMeasure.smul
      (fieldOnePadicInvPowIntHaarComap p n)
      (ENNReal.inv_ne_zero.mpr hctop) (ENNReal.inv_ne_top.mpr hc0)
  have hνprob_univ : νprob Set.univ = 1 := by
    dsimp [νprob]
    rw [fieldOnePadicInvPowIntHaarComap_univ]
    change c⁻¹ * c = 1
    exact ENNReal.inv_mul_cancel hc0 hctop
  letI : IsProbabilityMeasure νprob := ⟨hνprob_univ⟩
  letI : IsProbabilityMeasure (fieldOnePadicIntNormalizedHaar p) :=
    ⟨fieldOnePadicIntNormalizedHaar_univ p⟩
  have hprob : νprob = fieldOnePadicIntNormalizedHaar p :=
    Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure
      νprob (fieldOnePadicIntNormalizedHaar p)
  have hprob' : c⁻¹ • fieldOnePadicInvPowIntHaarComap p n =
      fieldOnePadicIntNormalizedHaar p := by
    simpa only [νprob] using hprob
  calc
    fieldOnePadicInvPowIntHaarComap p n =
        (1 : ℝ≥0∞) • fieldOnePadicInvPowIntHaarComap p n := by
      ext s hs
      simp
    _ = (c * c⁻¹) • fieldOnePadicInvPowIntHaarComap p n := by
      exact congrArg
        (fun q : ℝ≥0∞ => q • fieldOnePadicInvPowIntHaarComap p n)
        (ENNReal.mul_inv_cancel hc0 hctop).symm
    _ = c • (c⁻¹ • fieldOnePadicInvPowIntHaarComap p n) := by
      rw [smul_smul]
    _ = c • fieldOnePadicIntNormalizedHaar p := by rw [hprob']
    _ = ((p : ℝ≥0∞) ^ n) • fieldOnePadicIntNormalizedHaar p := rfl

/-- Exact change of variables from a denominator stage to `ℤ_p`. -/
theorem fieldOnePadic_setIntegral_invPowIntCoe (n : ℕ)
    (h : ℚ_[p] → ℂ) :
    ∫ x in Set.range (fieldOnePadicInvPowIntCoeAddMonoidHom p n), h x
        ∂fieldOnePadicUnitBallNormalizedHaar p =
      ((p : ℝ) ^ n : ℂ) *
        ∫ u, h (fieldOnePadicInvPowIntCoeAddMonoidHom p n u)
          ∂fieldOnePadicIntNormalizedHaar p := by
  have hemb :=
    (fieldOnePadicInvPowIntCoeAddMonoidHom_isOpenEmbedding p n).measurableEmbedding
  rw [← hemb.map_comap (fieldOnePadicUnitBallNormalizedHaar p)]
  rw [hemb.integral_map]
  rw [show (fieldOnePadicUnitBallNormalizedHaar p).comap
      (fieldOnePadicInvPowIntCoeAddMonoidHom p n) =
        fieldOnePadicInvPowIntHaarComap p n by rfl]
  rw [fieldOnePadicInvPowIntHaarComap_eq_smul, integral_smul_measure]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_natCast,
    Complex.ofReal_pow, Complex.ofReal_natCast, Complex.real_smul]

/-- Real-valued form of exact change of variables from a denominator stage
to `ℤ_p`. -/
theorem fieldOnePadic_setIntegral_invPowIntCoe_real (n : ℕ)
    (h : ℚ_[p] → ℝ) :
    ∫ x in Set.range (fieldOnePadicInvPowIntCoeAddMonoidHom p n), h x
        ∂fieldOnePadicUnitBallNormalizedHaar p =
      (p : ℝ) ^ n *
        ∫ u, h (fieldOnePadicInvPowIntCoeAddMonoidHom p n u)
          ∂fieldOnePadicIntNormalizedHaar p := by
  have hemb :=
    (fieldOnePadicInvPowIntCoeAddMonoidHom_isOpenEmbedding p n).measurableEmbedding
  rw [← hemb.map_comap (fieldOnePadicUnitBallNormalizedHaar p)]
  rw [hemb.integral_map]
  rw [show (fieldOnePadicUnitBallNormalizedHaar p).comap
      (fieldOnePadicInvPowIntCoeAddMonoidHom p n) =
        fieldOnePadicInvPowIntHaarComap p n by rfl]
  rw [fieldOnePadicInvPowIntHaarComap_eq_smul, integral_smul_measure]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_natCast, smul_eq_mul]

/-- On a denominator stage, the canonical all-depth source character is
exactly the standard cyclic character of the integral coordinate. -/
theorem fieldOnePadicStandardAddChar_neg_invPow_mul_coe
    (n : ℕ) (u : ℤ_[p]) :
    fieldOnePadicStandardAddChar p
      (-((p : ℚ_[p]) ^ n)⁻¹ * (u : ℚ_[p])) =
      ZMod.stdAddChar (-(PadicInt.toZModPow n u)) := by
  letI : NeZero (p ^ n) :=
    ⟨pow_ne_zero n (Fact.out : Nat.Prime p).ne_zero⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hx : -((p : ℚ_[p]) ^ n)⁻¹ * (u : ℚ_[p]) ∈
      fieldOnePadicDenominatorStage p n := by
    have hprod : (p : ℚ_[p]) ^ n *
        (-((p : ℚ_[p]) ^ n)⁻¹ * (u : ℚ_[p])) =
        -(u : ℚ_[p]) := by
      calc
        (p : ℚ_[p]) ^ n *
            (-((p : ℚ_[p]) ^ n)⁻¹ * (u : ℚ_[p])) =
            -((p : ℚ_[p]) ^ n * ((p : ℚ_[p]) ^ n)⁻¹) *
              (u : ℚ_[p]) := by ring
        _ = -(u : ℚ_[p]) := by
          rw [mul_inv_cancel₀ (pow_ne_zero n hp0)]
          simp
    change ‖(p : ℚ_[p]) ^ n *
      (-((p : ℚ_[p]) ^ n)⁻¹ * (u : ℚ_[p]))‖ ≤ 1
    rw [hprod, norm_neg]
    exact u.property
  rw [show fieldOnePadicStandardAddChar p
      (-((p : ℚ_[p]) ^ n)⁻¹ * (u : ℚ_[p])) =
      Circle.coeHom (AddCircle.toCircle
        (fieldOnePadicDenominatorStageCharacter p n
          ⟨-((p : ℚ_[p]) ^ n)⁻¹ * (u : ℚ_[p]), hx⟩)) by
    change Circle.coeHom (AddCircle.toCircle
      (fieldOnePadicStandardUnitAddCircleCharacter p
        (-((p : ℚ_[p]) ^ n)⁻¹ * (u : ℚ_[p])))) = _
    rw [fieldOnePadicStandardUnitAddCircleCharacter_eq_stage p hx]]
  have hstageInt :
      fieldOnePadicDenominatorStageIntegral p n
          ⟨-((p : ℚ_[p]) ^ n)⁻¹ * (u : ℚ_[p]), hx⟩ = -u := by
    apply PadicInt.ext
    change (p : ℚ_[p]) ^ n *
      (-((p : ℚ_[p]) ^ n)⁻¹ * (u : ℚ_[p])) = -(u : ℚ_[p])
    calc
      (p : ℚ_[p]) ^ n *
          (-((p : ℚ_[p]) ^ n)⁻¹ * (u : ℚ_[p])) =
          -((p : ℚ_[p]) ^ n * ((p : ℚ_[p]) ^ n)⁻¹) *
            (u : ℚ_[p]) := by ring
      _ = -(u : ℚ_[p]) := by
        rw [mul_inv_cancel₀ (pow_ne_zero n hp0)]
        simp
  have hstageVal :
      fieldOnePadicDenominatorStageCharacter p n
          ⟨-((p : ℚ_[p]) ^ n)⁻¹ * (u : ℚ_[p]), hx⟩ =
        ZMod.toAddCircle (PadicInt.toZModPow n
          (fieldOnePadicDenominatorStageIntegral p n
            ⟨-((p : ℚ_[p]) ^ n)⁻¹ * (u : ℚ_[p]), hx⟩)) := rfl
  rw [hstageVal, hstageInt, map_neg]
  rfl

end

end GaloisForLFunctions.RHTower
