import GaloisForLFunctions.RHTower.FieldOnePadicRamifiedRadialPackets

/-!
# The Connes--Consani--Moscovici local Sonin vector

Literal finite-place construction in Proposition 4.4 of
`Zeta zeros and prolate wave operators`: the shell vector
`σ_p = ε_0 - p⁻¹ ε_1` in the Bruhat space of `ℚ_p`, with its exact
Fourier fixed-point identity.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory
open scoped NNReal

variable (p : ℕ) [Fact p.Prime]

/-- Trivial exact conductor-zero character. -/
def fieldOnePadicConductorZeroCharacter :
    FieldOnePadicPrimitiveAngularCharacter p 0 :=
  ⟨1, by
    change DirichletCharacter.IsPrimitive (1 : DirichletCharacter ℂ 1)
    exact DirichletCharacter.isPrimitive_one_level_one⟩

omit [Fact p.Prime] in
@[simp] theorem fieldOnePadicConductorZeroCharacter_apply
    (x : ZMod (p ^ 0)) :
    (fieldOnePadicConductorZeroCharacter p).1 x = 1 := by
  letI : Subsingleton (ZMod (p ^ 0)) := by
    rw [pow_zero]
    infer_instance
  rw [show x = 1 from Subsingleton.elim _ _]
  exact map_one _

omit [Fact p.Prime] in
@[simp] theorem fieldOnePadicConductorZeroCharacter_gaussSum :
    gaussSum (fieldOnePadicConductorZeroCharacter p).1
        ZMod.stdAddChar = 1 := by
  letI : Unique (ZMod (p ^ 0)) := by
    rw [pow_zero]
    infer_instance
  rw [gaussSum, Fintype.sum_unique,
    fieldOnePadicConductorZeroCharacter_apply]
  have hdefault : (default : ZMod (p ^ 0)) = 0 :=
    Subsingleton.elim _ _
  change 1 * ZMod.stdAddChar default = 1
  rw [hdefault, one_mul]
  exact (ZMod.stdAddChar (N := p ^ 0)).map_zero_eq_one

/-- The characteristic function of `ℤ_p`, represented in the literal
`ℚ_p` Bruhat space. -/
def fieldOnePadicSoninUnitBall :
    compactlySupportedLocallyConstant ℚ_[p] :=
  fieldOnePadicPrimitiveAngularPacket p 0
    (fieldOnePadicConductorZeroCharacter p)

@[simp] theorem fieldOnePadicSoninUnitBall_apply_coe (u : ℤ_[p]) :
    (fieldOnePadicSoninUnitBall p).1 (u : ℚ_[p]) = 1 := by
  change fieldOnePadicPrimitiveAngularPacketLC p 0
      (fieldOnePadicConductorZeroCharacter p) (u : ℚ_[p]) = 1
  rw [fieldOnePadicPrimitiveAngularPacketLC_coe]
  exact fieldOnePadicConductorZeroCharacter_apply p _

theorem fieldOnePadicSoninUnitBall_apply_eq_zero_of_notMem
    {x : ℚ_[p]} (hx : x ∉ fieldOnePadicUnitBall p) :
    (fieldOnePadicSoninUnitBall p).1 x = 0 := by
  exact fieldOnePadicPrimitiveAngularPacketLC_eq_zero_of_notMem
    p 0 (fieldOnePadicConductorZeroCharacter p) hx

theorem fieldOnePadicDenominatorStage_zero_eq_unitBall :
    (fieldOnePadicDenominatorStage p 0 : Set ℚ_[p]) =
      fieldOnePadicUnitBall p := by
  rw [← fieldOnePadicInvPowIntCoeAddMonoidHom_range p 0]
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, by simp [fieldOnePadicInvPowIntCoeAddMonoidHom]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, by simp [fieldOnePadicInvPowIntCoeAddMonoidHom]⟩

/-- Self-duality of the unit-ball characteristic function for the canonical
additive character and unit-ball-normalized Haar measure. -/
theorem fieldOnePadicBruhatFourier_soninUnitBall (x : ℚ_[p]) :
    fieldOnePadicBruhatFourier p (fieldOnePadicSoninUnitBall p) x =
      (fieldOnePadicSoninUnitBall p).1 x := by
  by_cases hx : x ∈ fieldOnePadicUnitBall p
  · obtain ⟨u, rfl⟩ := hx
    have harg :
        ((u : ℤ_[p]) : ℚ_[p]) =
          fieldOnePadicInvPowIntCoeAddMonoidHom p 0 u := by
      simp [fieldOnePadicInvPowIntCoeAddMonoidHom]
    calc
      fieldOnePadicBruhatFourier p (fieldOnePadicSoninUnitBall p)
          (u : ℚ_[p]) =
          fieldOnePadicBruhatFourier p (fieldOnePadicSoninUnitBall p)
            (fieldOnePadicInvPowIntCoeAddMonoidHom p 0 u) :=
        congrArg _ harg
      _ = 1 := by
        rw [fieldOnePadicSoninUnitBall,
          fieldOnePadicPrimitiveAngularPacket_fourier_invPow]
        rw [fieldOnePadicConductorZeroCharacter_gaussSum, mul_one]
        letI : Subsingleton (ZMod (p ^ 0)) := by
          rw [pow_zero]
          infer_instance
        rw [show -(PadicInt.toZModPow 0 u) = 1 from
          Subsingleton.elim _ _]
        simp only [pow_zero, Nat.cast_one, inv_one, one_mul]
        exact map_one ((fieldOnePadicConductorZeroCharacter p).1⁻¹)
      _ = (fieldOnePadicSoninUnitBall p).1 (u : ℚ_[p]) := by
        symm
        exact fieldOnePadicSoninUnitBall_apply_coe p u
  · have hxstage : x ∉ fieldOnePadicDenominatorStage p 0 := by
      intro hxstage
      apply hx
      rw [← fieldOnePadicDenominatorStage_zero_eq_unitBall p]
      exact hxstage
    have hfourier :
        fieldOnePadicBruhatFourier p (fieldOnePadicSoninUnitBall p) x = 0 := by
      by_contra hne
      exact hxstage
        (fieldOnePadicPrimitiveAngularPacket_fourier_support p 0
          (fieldOnePadicConductorZeroCharacter p) hne)
    rw [hfourier,
      fieldOnePadicSoninUnitBall_apply_eq_zero_of_notMem p hx]

/-- Source ball `B_m(x)=1_{ℤ_p}(p^m x)`, for every integral index. -/
def fieldOnePadicSoninBall (m : ℤ) :
    compactlySupportedLocallyConstant ℚ_[p] :=
  fieldOnePadicBruhatDilation p ((fieldOnePadicPrimeUnit p) ^ m)
    (fieldOnePadicSoninUnitBall p)

@[simp] theorem fieldOnePadicSoninBall_apply (m : ℤ) (x : ℚ_[p]) :
    (fieldOnePadicSoninBall p m).1 x =
      (fieldOnePadicSoninUnitBall p).1
        (((fieldOnePadicPrimeUnit p) ^ m : ℚ_[p]ˣ) * x) :=
  rfl

/-- Source shell `ε_n=B_n-B_{n-1}`. -/
def fieldOnePadicSoninShell (n : ℤ) :
    compactlySupportedLocallyConstant ℚ_[p] :=
  fieldOnePadicSoninBall p n - fieldOnePadicSoninBall p (n - 1)

/-- Literal local Sonin vector `σ_p=ε_0-p⁻¹ε_1`. -/
def fieldOnePadicSoninSigma :
    compactlySupportedLocallyConstant ℚ_[p] :=
  fieldOnePadicSoninShell p 0 -
    ((p : ℂ)⁻¹) • fieldOnePadicSoninShell p 1

theorem fieldOnePadicBruhatFourier_soninBall
    (m : ℤ) (x : ℚ_[p]) :
    fieldOnePadicBruhatFourier p (fieldOnePadicSoninBall p m) x =
      ((p : ℂ) ^ m) * (fieldOnePadicSoninBall p (-m)).1 x := by
  rw [fieldOnePadicSoninBall,
    fieldOnePadicBruhatFourier_primeZPowDilation,
    fieldOnePadicBruhatFourier_soninUnitBall,
    fieldOnePadicSoninBall_apply]
  have hcoef : (((p : ℝ≥0) ^ m : ℝ≥0) : ℂ) = (p : ℂ) ^ m := by
    calc
      (((p : ℝ≥0) ^ m : ℝ≥0) : ℂ) =
          ((((p : ℝ) ^ m : ℝ)) : ℂ) := by rfl
      _ = (p : ℂ) ^ m := Complex.ofReal_zpow (p : ℝ) m
  change (((p : ℝ≥0) ^ m : ℝ≥0) : ℂ) * _ =
    (p : ℂ) ^ m * _
  rw [hcoef]

theorem fieldOnePadicBruhatFourierLinear_soninBall (m : ℤ) :
    fieldOnePadicBruhatFourierLinear p
        (fieldOnePadicSoninBall p m) =
      ((p : ℂ) ^ m) • fieldOnePadicSoninBall p (-m) := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  change fieldOnePadicBruhatFourier p
      (fieldOnePadicSoninBall p m) x =
    ((p : ℂ) ^ m) * (fieldOnePadicSoninBall p (-m)).1 x
  exact fieldOnePadicBruhatFourier_soninBall p m x

/-- Exact Fourier fixed-point identity in Proposition 4.4. -/
theorem fieldOnePadicBruhatFourier_soninSigma :
    fieldOnePadicBruhatFourierLinear p (fieldOnePadicSoninSigma p) =
      fieldOnePadicSoninSigma p := by
  rw [fieldOnePadicSoninSigma, map_sub, map_smul]
  simp only [fieldOnePadicSoninShell]
  rw [map_sub, map_sub,
    fieldOnePadicBruhatFourierLinear_soninBall,
    fieldOnePadicBruhatFourierLinear_soninBall,
    fieldOnePadicBruhatFourierLinear_soninBall,
    fieldOnePadicBruhatFourierLinear_soninBall]
  simp only [Int.reduceNeg, Int.reduceSub, zpow_zero, one_smul,
    neg_zero, zpow_one, smul_sub, smul_smul]
  have hpC : (p : ℂ) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  field_simp
  module

end

end GaloisForLFunctions.RHTower


