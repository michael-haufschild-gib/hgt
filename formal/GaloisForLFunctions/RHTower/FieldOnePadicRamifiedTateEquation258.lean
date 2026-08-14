import GaloisForLFunctions.RHTower.FieldOnePadicMultiplicativeHaarShellIntegral

/-!
# Literal ramified p-adic Tate equation at the critical exponent

This file proves the positive-conductor local equation (2.258) on primitive
radial packets using the literal Fourier integral on `ℚ_p`, literal
multiplicative Haar measure on `ℚ_pˣ`, and the source half-density
`|x|^(1/2)`.  The epsilon factor is derived as the unit complex number

`χ(-1) * ρ^n * τ(χ⁻¹) / sqrt(p^n)`.

No local functional equation is assumed.  Positive conductor and primitive
character are encoded by `ℕ+` and `FieldOnePadicPrimitiveAngularCharacter`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

variable (p : ℕ) [Fact p.Prime]

def fieldOnePadicRamifiedCriticalCharacter (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) (ρ : Circle)
    (a : ℚ_[p]ˣ) : ℂ :=
  ((ρ : ℂ) ^ Padic.valuation (a : ℚ_[p])) *
    χ.1 (fieldOnePadicUnitReduction p n (fieldOnePadicAngularUnit p a))

@[simp] theorem fieldOnePadicRamifiedCriticalCharacter_coordinates
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) (k : ℤ) (u : ℤ_[p]ˣ) :
    fieldOnePadicRamifiedCriticalCharacter p n χ ρ
        (fieldOnePadicValuationUnitContinuousMulEquiv p
          (Multiplicative.ofAdd k, u)) =
      ((ρ : ℂ) ^ k) * χ.1 (fieldOnePadicUnitReduction p n u) := by
  unfold fieldOnePadicRamifiedCriticalCharacter
  have hval : Padic.valuation
      (((fieldOnePadicValuationUnitContinuousMulEquiv p
        (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p])) = k := by
    exact fieldOnePadic_valuation_forward p (Multiplicative.ofAdd k, u)
  rw [hval]
  rw [show fieldOnePadicAngularUnit p
      (fieldOnePadicValuationUnitContinuousMulEquiv p
        (Multiplicative.ofAdd k, u)) = u by
      exact fieldOnePadicAngularUnit_coordinates p k u]

def fieldOnePadicCriticalHalfDensity (a : ℚ_[p]ˣ) : ℂ :=
  (Real.sqrt (p : ℝ) : ℂ) ^ (-Padic.valuation (a : ℚ_[p]))

@[simp] theorem fieldOnePadicCriticalHalfDensity_coordinates
    (k : ℤ) (u : ℤ_[p]ˣ) :
    fieldOnePadicCriticalHalfDensity p
        (fieldOnePadicValuationUnitContinuousMulEquiv p
          (Multiplicative.ofAdd k, u)) =
      (Real.sqrt (p : ℝ) : ℂ) ^ (-k) := by
  unfold fieldOnePadicCriticalHalfDensity
  have hval : Padic.valuation
      (((fieldOnePadicValuationUnitContinuousMulEquiv p
        (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p])) = k := by
    exact fieldOnePadic_valuation_forward p (Multiplicative.ofAdd k, u)
  rw [hval]

theorem fieldOneReal_sqrt_pow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = (Real.sqrt x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih, pow_succ]

theorem fieldOneReal_sqrt_zpow (x : ℝ) (hx : 0 ≤ x) (k : ℤ) :
    Real.sqrt (x ^ k) = (Real.sqrt x) ^ k := by
  cases k with
  | ofNat n =>
      simpa using fieldOneReal_sqrt_pow x hx n
  | negSucc n =>
      rw [zpow_negSucc, zpow_negSucc, Real.sqrt_inv]
      congr 1
      exact fieldOneReal_sqrt_pow x hx (n + 1)

theorem fieldOnePadicCriticalHalfDensity_eq_sqrt_norm (a : ℚ_[p]ˣ) :
    fieldOnePadicCriticalHalfDensity p a =
      (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ) := by
  rw [fieldOnePadicCriticalHalfDensity,
    Padic.norm_eq_zpow_neg_valuation (Units.ne_zero a),
    fieldOneReal_sqrt_zpow]
  · exact (Complex.ofReal_zpow _ _).symm
  · exact_mod_cast (Fact.out : Nat.Prime p).pos.le

def fieldOnePadicCriticalTateIntegrand (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) (ρ : Circle)
    (f : ℚ_[p] → ℂ) (a : ℚ_[p]ˣ) : ℂ :=
  f (a : ℚ_[p]) * fieldOnePadicRamifiedCriticalCharacter p n χ ρ a *
    fieldOnePadicCriticalHalfDensity p a

def fieldOnePadicDualCriticalTateIntegrand (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) (ρ : Circle)
    (f : ℚ_[p] → ℂ) (a : ℚ_[p]ˣ) : ℂ :=
  f (a : ℚ_[p]) * (fieldOnePadicRamifiedCriticalCharacter p n χ ρ a)⁻¹ *
    fieldOnePadicCriticalHalfDensity p a

theorem fieldOnePadicPrimitiveCharacter_inv_mul_self_unit
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (u : ℤ_[p]ˣ) :
    χ.1⁻¹ (fieldOnePadicUnitReduction p n u) *
      χ.1 (fieldOnePadicUnitReduction p n u) = 1 := by
  let r := fieldOnePadicUnitReduction p n u
  have hχnorm : ‖χ.1 (r : ZMod (p ^ n))‖ = 1 :=
    DirichletCharacter.unit_norm_eq_one χ.1 r
  have hχ : χ.1 (r : ZMod (p ^ n)) ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hχnorm
    exact zero_ne_one hχnorm
  rw [MulChar.inv_apply_eq_inv']
  exact inv_mul_cancel₀ hχ

theorem fieldOnePadicCriticalTateIntegrand_radialPacketInv_coordinates
    (n : ℕ) (hn : 0 < n)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) (ρ : Circle)
    (m k : ℤ) (u : ℤ_[p]ˣ) :
    fieldOnePadicCriticalTateIntegrand p n χ ρ
        (fieldOnePadicPrimitiveRadialPacket p n
          (fieldOnePadicPrimitiveAngularCharacterInv p n χ) m)
        (fieldOnePadicValuationUnitContinuousMulEquiv p
          (Multiplicative.ofAdd k, u)) =
      if k = m then
        ((ρ : ℂ) ^ m) * (Real.sqrt (p : ℝ) : ℂ) ^ (-m)
      else 0 := by
  rw [fieldOnePadicCriticalTateIntegrand,
    fieldOnePadicPrimitiveRadialPacket_coordinates p n hn,
    fieldOnePadicRamifiedCriticalCharacter_coordinates,
    fieldOnePadicCriticalHalfDensity_coordinates]
  by_cases hkm : k = m
  · subst k
    rw [if_pos rfl]
    rw [fieldOnePadicPrimitiveAngularCharacterInv_apply]
    calc
      χ.1⁻¹ (fieldOnePadicUnitReduction p n u) *
            ((ρ : ℂ) ^ m * χ.1 (fieldOnePadicUnitReduction p n u)) *
            (Real.sqrt (p : ℝ) : ℂ) ^ (-m) =
          (χ.1⁻¹ (fieldOnePadicUnitReduction p n u) *
            χ.1 (fieldOnePadicUnitReduction p n u)) *
            (((ρ : ℂ) ^ m) * (Real.sqrt (p : ℝ) : ℂ) ^ (-m)) := by
              ring
      _ = _ := by
        rw [fieldOnePadicPrimitiveCharacter_inv_mul_self_unit]
        simp
  · simp [hkm]

theorem fieldOnePadicCriticalTateIntegral_radialPacketInv
    (n : ℕ) (hn : 0 < n)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) (ρ : Circle)
    (m : ℤ) :
    ∫ a, fieldOnePadicCriticalTateIntegrand p n χ ρ
        (fieldOnePadicPrimitiveRadialPacket p n
          (fieldOnePadicPrimitiveAngularCharacterInv p n χ) m) a
        ∂fieldOnePadicMultiplicativeHaar p =
      ((ρ : ℂ) ^ m) * (Real.sqrt (p : ℝ) : ℂ) ^ (-m) := by
  let c : ℂ := ((ρ : ℂ) ^ m) *
    (Real.sqrt (p : ℝ) : ℂ) ^ (-m)
  rw [fieldOnePadicMultiplicativeHaar_integral_singleShell p
    (fieldOnePadicCriticalTateIntegrand p n χ ρ
      (fieldOnePadicPrimitiveRadialPacket p n
        (fieldOnePadicPrimitiveAngularCharacterInv p n χ) m))
    m (fun _ => c) (integrable_const c)]
  · rw [integral_const, Measure.real,
      fieldOnePadicUnitNormalizedHaar_univ]
    simp [c]
  · intro k u
    exact fieldOnePadicCriticalTateIntegrand_radialPacketInv_coordinates
      p n hn χ ρ m k u

theorem fieldOnePadicPrimitiveCharacter_neg_mul_inv_unit
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (u : ℤ_[p]ˣ) :
    χ.1 (-(fieldOnePadicUnitReduction p n u :
        (ZMod (p ^ n))ˣ)) *
      (χ.1 (fieldOnePadicUnitReduction p n u))⁻¹ =
        χ.1 (-1 : ZMod (p ^ n)) := by
  let r := fieldOnePadicUnitReduction p n u
  have hχnorm : ‖χ.1 (r : ZMod (p ^ n))‖ = 1 :=
    DirichletCharacter.unit_norm_eq_one χ.1 r
  have hχ : χ.1 (r : ZMod (p ^ n)) ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hχnorm
    exact zero_ne_one hχnorm
  change χ.1 (-(r : ZMod (p ^ n))) * (χ.1 r)⁻¹ = χ.1 (-1)
  rw [show -(r : ZMod (p ^ n)) = (-1) * r by ring,
    map_mul, mul_assoc, mul_inv_cancel₀ hχ, mul_one]

def fieldOnePadicRamifiedFourierShellConstant (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) (ρ : Circle)
    (m : ℤ) : ℂ :=
  ((p : ℝ≥0) ^ (-m)) •
    (((((p ^ n : ℕ) : ℂ)⁻¹ * χ.1 (-1 : ZMod (p ^ n))) *
          gaussSum
            (fieldOnePadicPrimitiveAngularCharacterInv p n χ).1
            ZMod.stdAddChar) *
        ((ρ : ℂ) ^ (-m - n))⁻¹) *
      (Real.sqrt (p : ℝ) : ℂ) ^ (m + n)

theorem fieldOnePadicDualCriticalTateIntegrand_fourier_radialPacketInv_coordinates
    (n : ℕ) (hn : 0 < n)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) (ρ : Circle)
    (m k : ℤ) (u : ℤ_[p]ˣ) :
    fieldOnePadicDualCriticalTateIntegrand p n χ ρ
        (fieldOnePadicBruhatFourier p
          (fieldOnePadicPrimitiveRadialPacket p n
            (fieldOnePadicPrimitiveAngularCharacterInv p n χ) m))
        (fieldOnePadicValuationUnitContinuousMulEquiv p
          (Multiplicative.ofAdd k, u)) =
      if k = -m - n then
        fieldOnePadicRamifiedFourierShellConstant p n χ ρ m
      else 0 := by
  rw [fieldOnePadicDualCriticalTateIntegrand,
    fieldOnePadicPrimitiveRadialPacket_fourier_coordinates p n hn,
    fieldOnePadicRamifiedCriticalCharacter_coordinates,
    fieldOnePadicCriticalHalfDensity_coordinates]
  by_cases hk : k = -m - n
  · subst k
    simp only [if_true]
    rw [MulChar.inv_apply_eq_inv',
      fieldOnePadicPrimitiveAngularCharacterInv_apply,
      MulChar.inv_apply_eq_inv', inv_inv]
    rw [mul_inv]
    have hparity := fieldOnePadicPrimitiveCharacter_neg_mul_inv_unit
      p n χ u
    unfold fieldOnePadicRamifiedFourierShellConstant
    rw [show -(-m - (n : ℤ)) = m + n by omega]
    calc
      ((p : ℝ≥0) ^ (-m)) •
            ((((p ^ n : ℕ) : ℂ)⁻¹ *
                χ.1 (-(fieldOnePadicUnitReduction p n u :
                  (ZMod (p ^ n))ˣ))) *
              gaussSum
                (fieldOnePadicPrimitiveAngularCharacterInv p n χ).1
                ZMod.stdAddChar) *
            (((ρ : ℂ) ^ (-m - n))⁻¹ *
              (χ.1 (fieldOnePadicUnitReduction p n u))⁻¹) *
            (Real.sqrt (p : ℝ) : ℂ) ^ (m + n) =
          ((p : ℝ≥0) ^ (-m)) •
            (((((p ^ n : ℕ) : ℂ)⁻¹ *
                (χ.1 (-(fieldOnePadicUnitReduction p n u :
                  (ZMod (p ^ n))ˣ)) *
                  (χ.1 (fieldOnePadicUnitReduction p n u))⁻¹)) *
              gaussSum
                (fieldOnePadicPrimitiveAngularCharacterInv p n χ).1
                ZMod.stdAddChar) *
              (((ρ : ℂ) ^ (-m - n))⁻¹)) *
              (Real.sqrt (p : ℝ) : ℂ) ^ (m + n) := by
                simp only [NNReal.smul_def, Complex.real_smul]
                ring
      _ = _ := by rw [hparity]
  · simp [hk]

theorem fieldOnePadicDualCriticalTateIntegral_fourier_radialPacketInv
    (n : ℕ) (hn : 0 < n)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) (ρ : Circle)
    (m : ℤ) :
    ∫ a, fieldOnePadicDualCriticalTateIntegrand p n χ ρ
        (fieldOnePadicBruhatFourier p
          (fieldOnePadicPrimitiveRadialPacket p n
            (fieldOnePadicPrimitiveAngularCharacterInv p n χ) m)) a
        ∂fieldOnePadicMultiplicativeHaar p =
      fieldOnePadicRamifiedFourierShellConstant p n χ ρ m := by
  let c := fieldOnePadicRamifiedFourierShellConstant p n χ ρ m
  rw [fieldOnePadicMultiplicativeHaar_integral_singleShell p
    (fieldOnePadicDualCriticalTateIntegrand p n χ ρ
      (fieldOnePadicBruhatFourier p
        (fieldOnePadicPrimitiveRadialPacket p n
          (fieldOnePadicPrimitiveAngularCharacterInv p n χ) m)))
    (-m - n) (fun _ => c) (integrable_const c)]
  · rw [integral_const, Measure.real,
      fieldOnePadicUnitNormalizedHaar_univ]
    simp [c]
  · intro k u
    exact
      fieldOnePadicDualCriticalTateIntegrand_fourier_radialPacketInv_coordinates
        p n hn χ ρ m k u

def fieldOnePadicRamifiedTatePhase (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) (ρ : Circle) : ℂ :=
  χ.1 (-1 : ZMod (p ^ n)) * ((ρ : ℂ) ^ n) *
    fieldOnePadicPrimitiveGaussPhase p n
      (fieldOnePadicPrimitiveAngularCharacterInv p n χ)

theorem fieldOnePadicRamifiedFourierShellConstant_eq_phase_mul
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) (m : ℤ) :
    fieldOnePadicRamifiedFourierShellConstant p n χ ρ m =
      fieldOnePadicRamifiedTatePhase p n χ ρ *
        (((ρ : ℂ) ^ m) * (Real.sqrt (p : ℝ) : ℂ) ^ (-m)) := by
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hs0 : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hpR).ne'
  have hpC : (p : ℂ) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hsquare : (Real.sqrt (p : ℝ) : ℂ) ^ 2 = (p : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hpR.le
  have hsqrtN : (Real.sqrt ((p : ℝ) ^ n) : ℂ) =
      (Real.sqrt (p : ℝ) : ℂ) ^ n := by
    rw [fieldOneReal_sqrt_pow (p : ℝ) hpR.le n,
      Complex.ofReal_pow]
  have hNinv : (((p ^ n : ℕ) : ℂ)⁻¹) =
      (p : ℂ) ^ (-(n : ℤ)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, zpow_natCast] using
      (zpow_neg (p : ℂ) (n : ℤ)).symm
  have hrho : (((ρ : ℂ) ^ (-m - n))⁻¹) =
      (ρ : ℂ) ^ (m + n) := by
    rw [← zpow_neg]
    congr 1
    omega
  unfold fieldOnePadicRamifiedFourierShellConstant
  unfold fieldOnePadicRamifiedTatePhase
  unfold fieldOnePadicPrimitiveGaussPhase
  rw [hsqrtN, hNinv, hrho]
  simp only [NNReal.smul_def]
  have hscalar : (((p : ℝ≥0) ^ (-m) : ℝ≥0) : ℝ) =
      (p : ℝ) ^ (-m) := NNReal.coe_zpow (p : ℝ≥0) (-m)
  rw [hscalar, Complex.real_smul, Complex.ofReal_zpow]
  have hpRC : ((p : ℝ) : ℂ) = (p : ℂ) := by norm_cast
  rw [hpRC]
  rw [show ((p : ℂ) ^ (-m)) =
      (Real.sqrt (p : ℝ) : ℂ) ^ (-2 * m) by
    rw [← hsquare, ← zpow_natCast, ← zpow_mul]
    congr 1
    ring]
  rw [show (p : ℂ) ^ (-(n : ℤ)) =
      (Real.sqrt (p : ℝ) : ℂ) ^ ((-2 : ℤ) * (n : ℤ)) by
    rw [← hsquare, ← zpow_natCast, ← zpow_mul]
    congr 1
    ring]
  have hinvsn : ((Real.sqrt (p : ℝ) : ℂ) ^ n)⁻¹ =
      (Real.sqrt (p : ℝ) : ℂ) ^ (-(n : ℤ)) := by
    simpa only [zpow_natCast] using
      (zpow_neg (Real.sqrt (p : ℝ) : ℂ) (n : ℤ)).symm
  rw [hinvsn]
  have hr0 : (ρ : ℂ) ≠ 0 := by
    intro hzero
    have hnorm := Circle.norm_coe ρ
    rw [hzero, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hrcombine : (ρ : ℂ) ^ (m + n) =
      (ρ : ℂ) ^ (n : ℤ) * (ρ : ℂ) ^ m := by
    rw [zpow_add₀ hr0]
    ring
  have hscombine :
      (Real.sqrt (p : ℝ) : ℂ) ^ (-2 * m) *
          (Real.sqrt (p : ℝ) : ℂ) ^ ((-2 : ℤ) * n) *
          (Real.sqrt (p : ℝ) : ℂ) ^ (m + n) =
        (Real.sqrt (p : ℝ) : ℂ) ^ (-(n : ℤ)) *
          (Real.sqrt (p : ℝ) : ℂ) ^ (-m) := by
    rw [← zpow_add₀ hs0, ← zpow_add₀ hs0, ← zpow_add₀ hs0]
    congr 1
    ring
  calc
    (Real.sqrt (p : ℝ) : ℂ) ^ (-2 * m) *
          (((Real.sqrt (p : ℝ) : ℂ) ^ ((-2 : ℤ) * n) *
              χ.1 (-1 : ZMod (p ^ n)) *
              gaussSum
                (fieldOnePadicPrimitiveAngularCharacterInv p n χ).1
                ZMod.stdAddChar *
              (ρ : ℂ) ^ (m + n))) *
          (Real.sqrt (p : ℝ) : ℂ) ^ (m + n) =
        (χ.1 (-1 : ZMod (p ^ n)) *
          gaussSum
            (fieldOnePadicPrimitiveAngularCharacterInv p n χ).1
            ZMod.stdAddChar) *
          (ρ : ℂ) ^ (m + n) *
          ((Real.sqrt (p : ℝ) : ℂ) ^ (-2 * m) *
            (Real.sqrt (p : ℝ) : ℂ) ^ ((-2 : ℤ) * n) *
            (Real.sqrt (p : ℝ) : ℂ) ^ (m + n)) := by ring
    _ = (χ.1 (-1 : ZMod (p ^ n)) *
          gaussSum
            (fieldOnePadicPrimitiveAngularCharacterInv p n χ).1
            ZMod.stdAddChar) *
          ((ρ : ℂ) ^ (n : ℤ) * (ρ : ℂ) ^ m) *
          ((Real.sqrt (p : ℝ) : ℂ) ^ (-(n : ℤ)) *
            (Real.sqrt (p : ℝ) : ℂ) ^ (-m)) := by
      rw [hrcombine, hscombine]
    _ = _ := by
      rw [zpow_natCast]
      ring

theorem norm_fieldOnePadicRamifiedTatePhase
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) :
    ‖fieldOnePadicRamifiedTatePhase p n χ ρ‖ = 1 := by
  unfold fieldOnePadicRamifiedTatePhase
  rw [norm_mul, norm_mul, norm_pow, Circle.norm_coe, one_pow,
    norm_fieldOnePadicPrimitiveGaussPhase]
  simp only [mul_one]
  let r : (ZMod (p ^ n))ˣ := -1
  have h := DirichletCharacter.unit_norm_eq_one χ.1 r
  exact h

/-- Literal positive-conductor local Tate equation (2.258) on every radial
primitive packet.  Positive conductor and primitivity are encoded in the
input types, so the statement has no mathematical hypotheses. -/
theorem fieldOnePadicRamifiedTateEquation258_radialPacket
    (n : ℕ+)
    (χ : FieldOnePadicPrimitiveAngularCharacter p (n : ℕ))
    (ρ : Circle) (m : ℤ) :
    (∫ a : ℚ_[p]ˣ,
        fieldOnePadicBruhatFourier p
            (fieldOnePadicPrimitiveRadialPacket p (n : ℕ)
              (fieldOnePadicPrimitiveAngularCharacterInv p (n : ℕ) χ) m)
            (a : ℚ_[p]) *
          (fieldOnePadicRamifiedCriticalCharacter p (n : ℕ) χ ρ a)⁻¹ *
          (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ)
        ∂fieldOnePadicMultiplicativeHaar p) =
      fieldOnePadicRamifiedTatePhase p (n : ℕ) χ ρ *
        (∫ a : ℚ_[p]ˣ,
          (fieldOnePadicPrimitiveRadialPacket p (n : ℕ)
              (fieldOnePadicPrimitiveAngularCharacterInv p (n : ℕ) χ) m).1
              (a : ℚ_[p]) *
            fieldOnePadicRamifiedCriticalCharacter p (n : ℕ) χ ρ a *
            (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ)
          ∂fieldOnePadicMultiplicativeHaar p) := by
  have hdual : (fun a : ℚ_[p]ˣ =>
        fieldOnePadicBruhatFourier p
            (fieldOnePadicPrimitiveRadialPacket p (n : ℕ)
              (fieldOnePadicPrimitiveAngularCharacterInv p (n : ℕ) χ) m)
            (a : ℚ_[p]) *
          (fieldOnePadicRamifiedCriticalCharacter p (n : ℕ) χ ρ a)⁻¹ *
          (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ)) =
      fieldOnePadicDualCriticalTateIntegrand p (n : ℕ) χ ρ
        (fieldOnePadicBruhatFourier p
          (fieldOnePadicPrimitiveRadialPacket p (n : ℕ)
            (fieldOnePadicPrimitiveAngularCharacterInv p (n : ℕ) χ) m)) := by
    funext a
    unfold fieldOnePadicDualCriticalTateIntegrand
    rw [fieldOnePadicCriticalHalfDensity_eq_sqrt_norm]
  have hprimal : (fun a : ℚ_[p]ˣ =>
        (fieldOnePadicPrimitiveRadialPacket p (n : ℕ)
            (fieldOnePadicPrimitiveAngularCharacterInv p (n : ℕ) χ) m).1
            (a : ℚ_[p]) *
          fieldOnePadicRamifiedCriticalCharacter p (n : ℕ) χ ρ a *
          (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ)) =
      fieldOnePadicCriticalTateIntegrand p (n : ℕ) χ ρ
        (fieldOnePadicPrimitiveRadialPacket p (n : ℕ)
          (fieldOnePadicPrimitiveAngularCharacterInv p (n : ℕ) χ) m) := by
    funext a
    unfold fieldOnePadicCriticalTateIntegrand
    rw [fieldOnePadicCriticalHalfDensity_eq_sqrt_norm]
  rw [hdual, hprimal,
    fieldOnePadicDualCriticalTateIntegral_fourier_radialPacketInv
      p (n : ℕ) n.pos χ ρ m,
    fieldOnePadicCriticalTateIntegral_radialPacketInv
      p (n : ℕ) n.pos χ ρ m,
    fieldOnePadicRamifiedFourierShellConstant_eq_phase_mul]

end
end GaloisForLFunctions.RHTower
