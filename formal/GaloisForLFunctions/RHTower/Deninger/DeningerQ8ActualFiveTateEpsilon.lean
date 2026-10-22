import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualFiveTameRatio
import GaloisForLFunctions.RHTower.FieldOnePadicRamifiedTateEquation258Full

/-!
# Actual Q8 Tate epsilon pair at 5

The literal SST quartic inertia source at `5`, after intrinsic tame transport,
has exact conductor `5`.  Hence it enters the independently proved field-one
Tate functional equation.  The local Tate phases of the source character and
its inverse have product `-1`.

This is a local analytic epsilon theorem.  It does not assume or name a global
Artin epsilon factor.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- At prime conductor, the Tate phases of a primitive character and its
inverse are exactly the probability-normalized same-additive Gaussian
product. -/
theorem fieldOnePadicPrimeRamifiedTatePhase_mul_inverse_eq_gaussianPhase
    (χ : FieldOnePadicPrimitiveAngularCharacter p 1) :
    fieldOnePadicRamifiedTatePhase p 1 χ 1 *
        fieldOnePadicRamifiedTatePhase p 1
          (fieldOnePadicPrimitiveAngularCharacterInv p 1 χ) 1 =
      (p : ℂ)⁻¹ *
        (gaussSum χ.1 ZMod.stdAddChar * gaussSum χ.1⁻¹ ZMod.stdAddChar) := by
  have hχ : χ.1 (-1 : ZMod (p ^ 1)) ≠ 0 := by
    rw [MulChar.apply_ne_zero_iff]
    exact ⟨-1, by simp⟩
  have hpR : (0 : ℝ) ≤ p := by positivity
  have hsqrt : ((Real.sqrt (p : ℝ) : ℂ)⁻¹) ^ 2 = (p : ℂ)⁻¹ := by
    rw [inv_pow, show (Real.sqrt (p : ℝ) : ℂ) ^ 2 = (p : ℂ) by
      norm_cast
      exact Real.sq_sqrt hpR]
  have hinv :
      (fieldOnePadicPrimitiveAngularCharacterInv p 1 χ).1 = χ.1⁻¹ := rfl
  have hinvinv :
      (fieldOnePadicPrimitiveAngularCharacterInv p 1
        (fieldOnePadicPrimitiveAngularCharacterInv p 1 χ)).1 = χ.1 := by
    change (χ.1⁻¹)⁻¹ = χ.1
    exact inv_inv χ.1
  simp only [fieldOnePadicRamifiedTatePhase,
    fieldOnePadicPrimitiveGaussPhase,
    fieldOnePadicPrimitiveAngularCharacterInv_apply, pow_one, Circle.coe_one,
    mul_one]
  rw [hinv, hinvinv, MulChar.inv_apply_eq_inv']
  rw [show χ.1 (-1 : ZMod (p ^ 1)) * ((Real.sqrt (p : ℝ) : ℂ)⁻¹ *
        gaussSum χ.1⁻¹ ZMod.stdAddChar) *
        ((χ.1 (-1 : ZMod (p ^ 1)))⁻¹ * ((Real.sqrt (p : ℝ) : ℂ)⁻¹ *
          gaussSum χ.1 ZMod.stdAddChar)) =
      (χ.1 (-1 : ZMod (p ^ 1)) * (χ.1 (-1 : ZMod (p ^ 1)))⁻¹) *
        (((Real.sqrt (p : ℝ) : ℂ)⁻¹) ^ 2) *
        (gaussSum χ.1 ZMod.stdAddChar * gaussSum χ.1⁻¹ ZMod.stdAddChar) by ring]
  rw [mul_inv_cancel₀ hχ, one_mul, hsqrt]

local instance q8FiveTateGaussianFactPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Conductor-five specialization used by the literal SST source. -/
theorem fieldOnePadicFiveRamifiedTatePhase_mul_inverse_eq_gaussianPhase
    (χ : FieldOnePadicPrimitiveAngularCharacter 5 1) :
    fieldOnePadicRamifiedTatePhase 5 1 χ 1 *
        fieldOnePadicRamifiedTatePhase 5 1
          (fieldOnePadicPrimitiveAngularCharacterInv 5 1 χ) 1 =
      (5 : ℂ)⁻¹ *
        (gaussSum χ.1 ZMod.stdAddChar * gaussSum χ.1⁻¹ ZMod.stdAddChar) :=
  fieldOnePadicPrimeRamifiedTatePhase_mul_inverse_eq_gaussianPhase 5 χ

end
end GaloisForLFunctions.RHTower

namespace RHTower

open scoped NumberField Pointwise
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.ValuationInertia
open GaloisForLFunctions.RHTower
noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

local instance q8FiveTateCharZeroK3 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
noncomputable local instance q8FiveTateFiniteDimensionalRatK1 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance q8FiveTateFiniteDimensionalK1K2 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance q8FiveTateFiniteDimensionalRatK2 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance q8FiveTateFiniteDimensionalK2K3 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance q8FiveTateFiniteDimensionalRatK3 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance q8FiveTateNumberFieldK3 : NumberField K3 := NumberField.mk
noncomputable local instance q8FiveTateIsGaloisRatK3 : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois
local instance q8FiveTateFactPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance q8FiveTateSpanFiveIsPrime : (Ideal.span {(5 : ℤ)}).IsPrime := by
  rw [Ideal.span_singleton_prime (by norm_num), Int.prime_iff_natAbs_prime]
  norm_num
local instance q8FiveTateSpanFiveIsMaximal : (Ideal.span {(5 : ℤ)}).IsMaximal :=
  Ideal.IsPrime.isMaximal (inferInstance : (Ideal.span {(5 : ℤ)}).IsPrime) (by
    intro h
    have : (5 : ℤ) = 0 := by
      rw [← Ideal.mem_bot, ← h]
      exact Ideal.mem_span_singleton_self 5
    norm_num at this)

/-- Exact order four at prime modulus `5` forces the literal transported SST
source character to have conductor `5`. -/
theorem q8ActualFiveZModSourceCharacter_isPrimitive
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W)
    (finiteRes : Finite (IsLocalRing.ResidueField W))
    (π : W) (hπ : Irreducible π)
    (eI : P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ)
    (hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5)
    (hRatioBij : Function.Bijective
      (residueRatioHom hπ
        (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
          smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)).toHomUnits) :
    DirichletCharacter.IsPrimitive
      (q8ActualFiveZModSourceCharacter P hPover W dvr finiteRes π hπ eI
        hResidueCard hRatioBij : DirichletCharacter ℂ 5) := by
  let χ := q8ActualFiveZModSourceCharacter P hPover W dvr finiteRes π hπ eI
    hResidueCard hRatioBij
  have horder : orderOf χ = 4 :=
    q8ActualFiveZModSourceCharacter_orderOf P hPover W dvr finiteRes π hπ eI
      hResidueCard hRatioBij
  have hne : χ ≠ 1 := by
    intro hχ
    rw [hχ, orderOf_one] at horder
    norm_num at horder
  rw [DirichletCharacter.isPrimitive_def]
  have hdiv : DirichletCharacter.conductor
      (χ : DirichletCharacter ℂ 5) ∣ 5 :=
    DirichletCharacter.conductor_dvd_level (χ : DirichletCharacter ℂ 5)
  rcases (Nat.dvd_prime Nat.prime_five).mp hdiv with h | h
  · exact (hne ((DirichletCharacter.eq_one_iff_conductor_eq_one
      (χ := (χ : DirichletCharacter ℂ 5))).mpr h)).elim
  · exact h

/-- Literal SST source character packaged at its exact field-one Tate
conductor. -/
noncomputable def q8ActualFivePrimitiveTateCharacter
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W)
    (finiteRes : Finite (IsLocalRing.ResidueField W))
    (π : W) (hπ : Irreducible π)
    (eI : P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ)
    (hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5)
    (hRatioBij : Function.Bijective
      (residueRatioHom hπ
        (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
          smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)).toHomUnits) :
    FieldOnePadicPrimitiveAngularCharacter 5 1 :=
  ⟨q8ActualFiveZModSourceCharacter P hPover W dvr finiteRes π hπ eI
      hResidueCard hRatioBij,
    by simpa using (q8ActualFiveZModSourceCharacter_isPrimitive P hPover W dvr
      finiteRes π hπ eI hResidueCard hRatioBij)⟩

/-- Analytic local Tate epsilon of the actual source orientation at trivial
unramified radial character. -/
noncomputable def q8ActualFiveLocalTateEpsilon
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W)
    (finiteRes : Finite (IsLocalRing.ResidueField W))
    (π : W) (hπ : Irreducible π)
    (eI : P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ)
    (hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5)
    (hRatioBij : Function.Bijective
      (residueRatioHom hπ
        (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
          smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)).toHomUnits) : ℂ :=
  fieldOnePadicRamifiedTatePhase 5 1
    (q8ActualFivePrimitiveTateCharacter P hPover W dvr finiteRes π hπ eI
      hResidueCard hRatioBij) 1

/-- Analytic local Tate epsilon of the inverse SST orientation. -/
noncomputable def q8ActualFiveInverseLocalTateEpsilon
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W)
    (finiteRes : Finite (IsLocalRing.ResidueField W))
    (π : W) (hπ : Irreducible π)
    (eI : P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ)
    (hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5)
    (hRatioBij : Function.Bijective
      (residueRatioHom hπ
        (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
          smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)).toHomUnits) : ℂ :=
  fieldOnePadicRamifiedTatePhase 5 1
    (fieldOnePadicPrimitiveAngularCharacterInv 5 1
      (q8ActualFivePrimitiveTateCharacter P hPover W dvr finiteRes π hπ eI
        hResidueCard hRatioBij)) 1

/-- Both actual five-adic Tate phases are unitary. -/
theorem q8ActualFiveLocalTateEpsilon_norms
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W)
    (finiteRes : Finite (IsLocalRing.ResidueField W))
    (π : W) (hπ : Irreducible π)
    (eI : P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ)
    (hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5)
    (hRatioBij : Function.Bijective
      (residueRatioHom hπ
        (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
          smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)).toHomUnits) :
    ‖q8ActualFiveLocalTateEpsilon P hPover W dvr finiteRes π hπ eI
        hResidueCard hRatioBij‖ = 1 ∧
      ‖q8ActualFiveInverseLocalTateEpsilon P hPover W dvr finiteRes π hπ eI
        hResidueCard hRatioBij‖ = 1 := by
  constructor
  · exact norm_fieldOnePadicRamifiedTatePhase 5 1 _ 1
  · exact norm_fieldOnePadicRamifiedTatePhase 5 1 _ 1

/-- The independently defined analytic Tate epsilon pair of the actual SST
source at `5` has product `-1`. -/
theorem q8ActualFiveLocalTateEpsilon_mul_inverse_eq_neg_one
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W)
    (finiteRes : Finite (IsLocalRing.ResidueField W))
    (π : W) (hπ : Irreducible π)
    (eI : P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ)
    (hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5)
    (hRatioBij : Function.Bijective
      (residueRatioHom hπ
        (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
          smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)).toHomUnits) :
    q8ActualFiveLocalTateEpsilon P hPover W dvr finiteRes π hπ eI
        hResidueCard hRatioBij *
      q8ActualFiveInverseLocalTateEpsilon P hPover W dvr finiteRes π hπ eI
        hResidueCard hRatioBij = -1 := by
  rw [q8ActualFiveLocalTateEpsilon, q8ActualFiveInverseLocalTateEpsilon,
    fieldOnePadicFiveRamifiedTatePhase_mul_inverse_eq_gaussianPhase]
  exact q8ActualFiveZModSourceCharacter_phase P hPover W dvr finiteRes π hπ eI
    hResidueCard hRatioBij

/-- The actual source orientation satisfies the literal field-one Tate
functional equation on every five-adic Bruhat test. -/
theorem q8ActualFiveLocalTateEquation258
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W)
    (finiteRes : Finite (IsLocalRing.ResidueField W))
    (π : W) (hπ : Irreducible π)
    (eI : P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ)
    (hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5)
    (hRatioBij : Function.Bijective
      (residueRatioHom hπ
        (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
          smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)).toHomUnits)
    (f : compactlySupportedLocallyConstant ℚ_[5]) :
    (∫ a : ℚ_[5]ˣ,
        fieldOnePadicBruhatFourier 5 f (a : ℚ_[5]) *
          (fieldOnePadicRamifiedCriticalCharacter 5 1
            (q8ActualFivePrimitiveTateCharacter P hPover W dvr finiteRes π hπ eI
              hResidueCard hRatioBij) 1 a)⁻¹ *
          (Real.sqrt ‖(a : ℚ_[5])‖ : ℂ)
        ∂fieldOnePadicMultiplicativeHaar 5) =
      q8ActualFiveLocalTateEpsilon P hPover W dvr finiteRes π hπ eI
          hResidueCard hRatioBij *
        (∫ a : ℚ_[5]ˣ,
          f.1 (a : ℚ_[5]) *
            fieldOnePadicRamifiedCriticalCharacter 5 1
              (q8ActualFivePrimitiveTateCharacter P hPover W dvr finiteRes π hπ eI
                hResidueCard hRatioBij) 1 a *
            (Real.sqrt ‖(a : ℚ_[5])‖ : ℂ)
          ∂fieldOnePadicMultiplicativeHaar 5) := by
  exact fieldOnePadicRamifiedTateEquation258 5 1
    (q8ActualFivePrimitiveTateCharacter P hPover W dvr finiteRes π hπ eI
      hResidueCard hRatioBij) 1 f

/-- The inverse SST orientation satisfies the same literal Tate equation,
with the independently defined inverse local epsilon. -/
theorem q8ActualFiveInverseLocalTateEquation258
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W)
    (finiteRes : Finite (IsLocalRing.ResidueField W))
    (π : W) (hπ : Irreducible π)
    (eI : P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ)
    (hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5)
    (hRatioBij : Function.Bijective
      (residueRatioHom hπ
        (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
          smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W g.property y)).toHomUnits)
    (f : compactlySupportedLocallyConstant ℚ_[5]) :
    (∫ a : ℚ_[5]ˣ,
        fieldOnePadicBruhatFourier 5 f (a : ℚ_[5]) *
          (fieldOnePadicRamifiedCriticalCharacter 5 1
            (fieldOnePadicPrimitiveAngularCharacterInv 5 1
              (q8ActualFivePrimitiveTateCharacter P hPover W dvr finiteRes π hπ eI
                hResidueCard hRatioBij)) 1 a)⁻¹ *
          (Real.sqrt ‖(a : ℚ_[5])‖ : ℂ)
        ∂fieldOnePadicMultiplicativeHaar 5) =
      q8ActualFiveInverseLocalTateEpsilon P hPover W dvr finiteRes π hπ eI
          hResidueCard hRatioBij *
        (∫ a : ℚ_[5]ˣ,
          f.1 (a : ℚ_[5]) *
            fieldOnePadicRamifiedCriticalCharacter 5 1
              (fieldOnePadicPrimitiveAngularCharacterInv 5 1
                (q8ActualFivePrimitiveTateCharacter P hPover W dvr finiteRes π hπ eI
                  hResidueCard hRatioBij)) 1 a *
            (Real.sqrt ‖(a : ℚ_[5])‖ : ℂ)
          ∂fieldOnePadicMultiplicativeHaar 5) := by
  exact fieldOnePadicRamifiedTateEquation258 5 1
    (fieldOnePadicPrimitiveAngularCharacterInv 5 1
      (q8ActualFivePrimitiveTateCharacter P hPover W dvr finiteRes π hπ eI
        hResidueCard hRatioBij)) 1 f

end
end RHTower
