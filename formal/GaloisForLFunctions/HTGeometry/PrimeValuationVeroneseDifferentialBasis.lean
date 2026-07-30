import GaloisForLFunctions.HTGeometry.FiniteRangePrimeDirichletModuli
import GaloisForLFunctions.HTGeometry.PrimePowerTailPacket

/-!
# Differential bases across prime-power valuation layers

For a finite collection of prime-power layers, give every layer its own finite-range coefficient
basis and finite shift palette.  Tail independence inside each layer, together with the distinct
prime-power supports, forces differential independence of the whole palette.  The logarithmic
derivation contributes the exact homogeneous weight `(e + 1)^k` on the `k`-th jet of layer `e`.

This is the differential-basis component of the prime-valuation Veronese correspondence.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction
open scoped Differential

noncomputable section

universe u

set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 60000

local instance complexFinitePrimeRationalAmbientScalarTowerPrimePower :
    IsScalarTower ℂ finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField :=
  .of_algebraMap_eq fun z => by
    change algebraMap ℂ arithmeticFunctionRationalCoordinateField z =
      finitePrimeRationalCoefficientFieldToFormalRatFunc
        (algebraMap ℂ finitePrimeRationalCoefficientField z)
    rw [IsScalarTower.algebraMap_apply ℂ finitePrimeCoefficientField
      finitePrimeRationalCoefficientField]
    rw [finitePrimeRationalCoefficientFieldToFormalRatFunc_algebraMap]
    rw [← IsScalarTower.algebraMap_apply ℂ finitePrimeCoefficientField
      arithmeticFunctionFractionField]
    rw [IsScalarTower.algebraMap_apply ℂ arithmeticFunctionFractionField
      arithmeticFunctionRationalCoordinateField]

/-- The order-`k` shifted rotated jet in prime-power layer `e`.  The parameter `a` is the
effective exponent shift: analytically this column is
`sum_p c(p) p^-((e+1)s+a)`. -/
def primePowerCoefficientShiftedRotatedJet
    (e : ℕ) (c : Nat.Primes → ℂ) (a : ℂ) (k : ℕ) : ArithmeticFunction ℂ :=
  arithmeticOfPrimePowerColumn e fun p ↦
    c p * primeShiftFactor a p *
      ((((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ k)

/-- Rotated logarithmic differentiation of a prime-power column multiplies its prime coefficient
by the valuation weight `(e+1)` and one additional rotated logarithmic clock. -/
theorem rotatedLogArithmetic_primePowerColumn
    (e : ℕ) (a : Nat.Primes → ℂ) :
    Complex.I • logWeight (arithmeticOfPrimePowerColumn e a) =
      arithmeticOfPrimePowerColumn e fun p ↦
        (((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) * a p := by
  classical
  ext n
  simp only [ArithmeticFunction.smul_map, smul_eq_mul, logWeight_apply]
  by_cases hpow : ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + 1)
  · let p : Nat.Primes := chosenPrimePowerBase (e + 1) n hpow
    have hn : n = (p : ℕ) ^ (e + 1) := chosenPrimePowerBase_spec (e + 1) n hpow
    rw [hn, arithmeticOfPrimePowerColumn_apply, arithmeticOfPrimePowerColumn_apply]
    have hlog : Real.log (((p : ℕ) ^ (e + 1) : ℕ) : ℝ) =
        ((e + 1 : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) := by
      rw [show (((p : ℕ) ^ (e + 1) : ℕ) : ℝ) =
          ((p : ℕ) : ℝ) ^ (e + 1) by norm_num, Real.log_pow]
    have hlogC : (Real.log (((p : ℕ) ^ (e + 1) : ℕ) : ℝ) : ℂ) =
        ((e + 1 : ℕ) : ℂ) * (Real.log ((p : ℕ) : ℝ) : ℂ) := by
      exact_mod_cast hlog
    rw [hlogC]
    simp only [rotatedPrimeLogClock, primeLogClock]
    ring
  · have hzero : arithmeticOfPrimePowerColumn e a n = 0 := by
      simp [arithmeticOfPrimePowerColumn, hpow]
    have hzero' : arithmeticOfPrimePowerColumn e
        (fun p ↦ (((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) * a p) n = 0 := by
      simp [arithmeticOfPrimePowerColumn, hpow]
    rw [hzero, hzero']
    ring

/-- A prime-power column with only finitely many nonzero prime coefficients belongs to the
intrinsic finite-prime coefficient field. -/
theorem arithmeticOfPrimePowerColumn_mem_finitePrimeCoefficientField_of_support_finite
    (e : ℕ) (a : Nat.Primes → ℂ) (ha : {p | a p ≠ 0}.Finite) :
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticOfPrimePowerColumn e a) ∈ finitePrimeCoefficientField := by
  rw [mem_finitePrimeCoefficientField_iff]
  apply ha.subset
  intro p hp
  simp only [finitePrimeActivity, Set.mem_setOf_eq] at hp ⊢
  intro hap
  apply hp
  rw [primeFractionDerivation_arithmeticOfPrimePowerColumn, hap, mul_zero]
  have hpoint : arithmeticPointMass ((p : ℕ) ^ e) 0 = 0 := by
    ext n
    rw [arithmeticPointMass_apply_of_ne_zero (pow_ne_zero e p.2.ne_zero)]
    simp
  rw [hpoint, _root_.map_zero]

@[simp]
theorem rotatedLogFractionDerivation_primePowerCoefficientShiftedRotatedJet
    (e : ℕ) (c : Nat.Primes → ℂ) (a : ℂ) (k : ℕ) :
    rotatedLogFractionDerivation
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (primePowerCoefficientShiftedRotatedJet e c a k)) =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primePowerCoefficientShiftedRotatedJet e c a (k + 1)) := by
  rw [rotatedLogFractionDerivation_algebraMap]
  unfold primePowerCoefficientShiftedRotatedJet
  rw [rotatedLogArithmetic_primePowerColumn]
  congr 1
  ext n
  by_cases hpow : ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + 1)
  · let p : Nat.Primes := chosenPrimePowerBase (e + 1) n hpow
    have hn : n = (p : ℕ) ^ (e + 1) := chosenPrimePowerBase_spec (e + 1) n hpow
    rw [hn, arithmeticOfPrimePowerColumn_apply, arithmeticOfPrimePowerColumn_apply]
    simp only [pow_succ]
    ring
  · simp [arithmeticOfPrimePowerColumn, hpow]

/-- The rational-coordinate differential carrier of a shifted coefficient column in valuation
layer `e`. -/
def primePowerCoefficientShiftCarrier
    (e : ℕ) (c : Nat.Primes → ℂ) (a : ℂ) :
    arithmeticFunctionRationalCoordinateField :=
  algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
    (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (primePowerCoefficientShiftedRotatedJet e c a 0))

/-- The complete differential jet has the exact valuation weight `(e+1)^k`. -/
@[simp]
theorem differentialJet_primePowerCoefficientShiftCarrier
    (e : ℕ) (c : Nat.Primes → ℂ) (a : ℂ) (k : ℕ) :
    GaloisForLFunctions.differentialJet k
        (primePowerCoefficientShiftCarrier e c a) =
      algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (primePowerCoefficientShiftedRotatedJet e c a k)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [GaloisForLFunctions.differentialJet_succ, ih,
        arithmeticFunctionRationalCoordinateField_deriv_algebraMap,
        arithmeticFunctionFractionField_deriv_apply,
        rotatedLogFractionDerivation_primePowerCoefficientShiftedRotatedJet]

/-- Prime-power shifted jets commute with finite complex linear combinations of their source
columns. -/
theorem primePowerCoefficientShiftedRotatedJet_linearCombination
    {B : Type*} [Fintype B]
    (e : ℕ) (c : B → Nat.Primes → ℂ) (z : B → ℂ) (a : ℂ) (k : ℕ) :
    primePowerCoefficientShiftedRotatedJet e (fun p ↦ ∑ b, z b * c b p) a k =
      ∑ b, algebraMap ℂ (ArithmeticFunction ℂ) (z b) *
        primePowerCoefficientShiftedRotatedJet e (c b) a k := by
  classical
  simp_rw [← Algebra.smul_def]
  ext n
  let ev : ArithmeticFunction ℂ →+ ℂ :=
    { toFun := fun f ↦ f n
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  rw [show (∑ b, z b • primePowerCoefficientShiftedRotatedJet e (c b) a k) n =
      ∑ b, (z b • primePowerCoefficientShiftedRotatedJet e (c b) a k) n by
      exact map_sum ev _ Finset.univ]
  by_cases hpow : ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + 1)
  · let p : Nat.Primes := chosenPrimePowerBase (e + 1) n hpow
    have hn : n = (p : ℕ) ^ (e + 1) := chosenPrimePowerBase_spec (e + 1) n hpow
    rw [show primePowerCoefficientShiftedRotatedJet e
        (fun p ↦ ∑ b, z b * c b p) a k n =
          (∑ b, z b * c b p) * primeShiftFactor a p *
            ((((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ k) by
      rw [hn]
      exact arithmeticOfPrimePowerColumn_apply e _ p]
    simp only [ArithmeticFunction.smul_map, smul_eq_mul]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    rw [show primePowerCoefficientShiftedRotatedJet e (c b) a k n =
        c b p * primeShiftFactor a p *
          ((((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ k) by
      rw [hn]
      exact arithmeticOfPrimePowerColumn_apply e _ p]
    ring
  · simp [primePowerCoefficientShiftedRotatedJet,
      arithmeticOfPrimePowerColumn, hpow, ArithmeticFunction.smul_map]

/-- The finite linear-combination law survives in the rational-coordinate ambient field at every
differential jet. -/
theorem differentialJet_primePowerCoefficientShiftCarrier_linearCombination
    {B : Type*} [Fintype B]
    (e : ℕ) (c : B → Nat.Primes → ℂ) (z : B → ℂ) (a : ℂ) (k : ℕ) :
    GaloisForLFunctions.differentialJet k
        (primePowerCoefficientShiftCarrier e (fun p ↦ ∑ b, z b * c b p) a) =
      ∑ b, algebraMap ℂ arithmeticFunctionRationalCoordinateField (z b) *
        GaloisForLFunctions.differentialJet k
          (primePowerCoefficientShiftCarrier e (c b) a) := by
  classical
  simp_rw [differentialJet_primePowerCoefficientShiftCarrier]
  rw [primePowerCoefficientShiftedRotatedJet_linearCombination]
  rw [map_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [map_mul, map_mul]
  congr 1

/-- At every jet order, a finite prime-tail residual in one valuation layer contributes only a
base-field correction. -/
theorem primePowerCoefficientShiftCarrier_residual_jet_mem_base
    (e : ℕ) (c d : Nat.Primes → ℂ) (z : ℂ)
    (hsupport : {p | c p - z * d p ≠ 0}.Finite) (a : ℂ) (k : ℕ) :
    ∃ b : finitePrimeRationalCoefficientField,
      GaloisForLFunctions.differentialJet k (primePowerCoefficientShiftCarrier e c a) -
          algebraMap ℂ arithmeticFunctionRationalCoordinateField z *
            GaloisForLFunctions.differentialJet k
              (primePowerCoefficientShiftCarrier e d a) =
        algebraMap finitePrimeRationalCoefficientField
          arithmeticFunctionRationalCoordinateField b := by
  let coeff : Nat.Primes → ℂ := fun p ↦
    (c p - z * d p) * primeShiftFactor a p *
      ((((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ k)
  have hcoeff : {p | coeff p ≠ 0}.Finite := by
    apply hsupport.subset
    intro p hp
    simp only [Set.mem_setOf_eq, coeff] at hp ⊢
    intro hzero
    exact hp (by rw [hzero, zero_mul, zero_mul])
  let kF : finitePrimeCoefficientField :=
    ⟨algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (arithmeticOfPrimePowerColumn e coeff),
      arithmeticOfPrimePowerColumn_mem_finitePrimeCoefficientField_of_support_finite
        e coeff hcoeff⟩
  let b : finitePrimeRationalCoefficientField :=
    algebraMap finitePrimeCoefficientField finitePrimeRationalCoefficientField kF
  refine ⟨b, ?_⟩
  rw [differentialJet_primePowerCoefficientShiftCarrier,
    differentialJet_primePowerCoefficientShiftCarrier,
    IsScalarTower.algebraMap_apply ℂ arithmeticFunctionFractionField
      arithmeticFunctionRationalCoordinateField,
    ← map_mul, ← map_sub,
    IsScalarTower.algebraMap_apply ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField,
    ← map_mul, ← map_sub]
  have hcolumn :
      primePowerCoefficientShiftedRotatedJet e c a k -
          algebraMap ℂ (ArithmeticFunction ℂ) z *
            primePowerCoefficientShiftedRotatedJet e d a k =
        arithmeticOfPrimePowerColumn e coeff := by
    rw [← Algebra.smul_def]
    ext n
    change primePowerCoefficientShiftedRotatedJet e c a k n -
        z * primePowerCoefficientShiftedRotatedJet e d a k n =
      arithmeticOfPrimePowerColumn e coeff n
    by_cases hpow : ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + 1)
    · let p : Nat.Primes := chosenPrimePowerBase (e + 1) n hpow
      have hn : n = (p : ℕ) ^ (e + 1) := chosenPrimePowerBase_spec (e + 1) n hpow
      rw [show primePowerCoefficientShiftedRotatedJet e c a k n =
          c p * primeShiftFactor a p *
            ((((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ k) by
        rw [hn]
        exact arithmeticOfPrimePowerColumn_apply e _ p]
      rw [show primePowerCoefficientShiftedRotatedJet e d a k n =
          d p * primeShiftFactor a p *
            ((((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ k) by
        rw [hn]
        exact arithmeticOfPrimePowerColumn_apply e _ p]
      rw [show arithmeticOfPrimePowerColumn e coeff n = coeff p by
        rw [hn]
        exact arithmeticOfPrimePowerColumn_apply e _ p]
      simp only [coeff]
      ring
    · simp [primePowerCoefficientShiftedRotatedJet, coeff,
        arithmeticOfPrimePowerColumn, hpow]
  rw [hcolumn]
  change algebraMap arithmeticFunctionFractionField
      arithmeticFunctionRationalCoordinateField kF.1 =
    algebraMap finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField b
  exact (finitePrimeRationalCoefficientFieldToFormalRatFunc_algebraMap kF).symm

/-- Within one layer, the valuation-weighted shifted jet rectangle has exactly the tail rank of
its underlying finite-range coefficient family. -/
theorem primePowerCoefficientShiftedRotatedJet_tailIndependent_iff
    {J A : Type*} [Fintype J] [Fintype A] [Nonempty A]
    (e : ℕ) (c : J → Nat.Primes → ℂ) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a ↦ (alpha a).re))
    (hrange : (Set.range (coefficientPattern c)).Finite) (m : ℕ) :
    TailCoefficientIndependent
        (fun jak : J × (A × Fin (m + 1)) ↦ fun p ↦
          c jak.1 p * primeShiftFactor (alpha jak.2.1) p *
            ((((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^
              (jak.2.2 : ℕ))) ↔
      TailCoefficientIndependent c := by
  classical
  let raw : J × (A × Fin (m + 1)) → Nat.Primes → ℂ := fun jak p ↦
    c jak.1 p * primeShiftFactor (alpha jak.2.1) p *
      rotatedPrimeLogClock p ^ (jak.2.2 : ℕ)
  let u : J × (A × Fin (m + 1)) → ℂ := fun jak ↦
    (((e + 1 : ℕ) : ℂ) ^ (jak.2.2 : ℕ))
  have hu : ∀ jak, u jak ≠ 0 := by
    intro jak
    apply pow_ne_zero
    exact_mod_cast Nat.succ_ne_zero e
  have hscale :
      TailCoefficientIndependent (fun jak p ↦ u jak * raw jak p) ↔
        TailCoefficientIndependent raw :=
    tailCoefficientIndependent_scale_columns_iff raw u hu
  have hraw : TailCoefficientIndependent raw ↔ TailCoefficientIndependent c := by
    simpa only [raw] using
      (primeCoefficientShiftedRotatedJet_tailIndependent_iff
        c alpha hdistinct hrange m)
  rw [← hraw, ← hscale]
  have hfamily :
      (fun jak : J × (A × Fin (m + 1)) ↦ fun p ↦
        c jak.1 p * primeShiftFactor (alpha jak.2.1) p *
          ((((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^
            (jak.2.2 : ℕ))) =
        (fun jak p ↦ u jak * raw jak p) := by
    funext jak p
    simp only [u, raw, mul_pow]
    ring
  rw [hfamily]

/-- **Finite valuation-window basis theorem.**  Every layer may carry its own finite-range
coefficient basis, shift palette, and jet cutoff.  If the coefficient columns are tail-independent
inside each layer, then all valuation-resolved shifted jets are jointly algebraically independent
over the intrinsic finite-prime rational coefficient field. -/
theorem primePowerCoefficientShiftedJets_algebraicIndependent
    {d : ℕ} (J B : Fin d → Type u)
    [∀ r, Fintype (J r)] [∀ r, DecidableEq (J r)]
    [∀ r, Fintype (B r)] [∀ r, DecidableEq (B r)] [∀ r, Nonempty (B r)]
    (c : ∀ r, J r → Nat.Primes → ℂ) (alpha : ∀ r, B r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun b ↦ (alpha r b).re))
    (hrange : ∀ r, (Set.range (coefficientPattern (c r))).Finite)
    (htail : ∀ r, TailCoefficientIndependent (c r)) (m : Fin d → ℕ) :
    AlgebraicIndependent finitePrimeRationalCoefficientField
      (fun x : Σ r, J r × (B r × Fin (m r + 1)) ↦
        algebraMap arithmeticFunctionFractionField
          arithmeticFunctionRationalCoordinateField
          (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (primePowerCoefficientShiftedRotatedJet
              x.1 (c x.1 x.2.1) (alpha x.1 x.2.2.1) x.2.2.2))) := by
  let A : Fin d → Type u := fun r ↦ J r × (B r × Fin (m r + 1))
  letI (r : Fin d) : Fintype (A r) := inferInstance
  letI (r : Fin d) : DecidableEq (A r) := inferInstance
  let a : ∀ r, A r → Nat.Primes → ℂ := fun r x p ↦
    c r x.1 p * primeShiftFactor (alpha r x.2.1) p *
      ((((r.1 + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ (x.2.2 : ℕ))
  have hatail : ∀ r, TailCoefficientIndependent (a r) := by
    intro r
    exact (primePowerCoefficientShiftedRotatedJet_tailIndependent_iff
      r (c r) (alpha r) (hdistinct r) (hrange r) (m r)).mpr (htail r)
  have hraw := algebraicIndependent_primePowerSigmaTower_over_finitePrimeCoefficientField
    d A a hatail
  apply algebraicIndependent_constants_over_finitePrimeRationalCoefficientField at hraw
  simpa only [A, a, primePowerSigmaExponent, primePowerSigmaCoefficient,
    primePowerCoefficientShiftedRotatedJet] using hraw

/-- **Prime-valuation differential basis law.**  The union of all layer bases and finite shift
palettes is differentially independent.  Hence distinct valuation layers create no hidden
nonlinear or cross-layer differential relations. -/
theorem primePowerCoefficientShiftPalettes_differentialIndependent
    {d : ℕ} (J B : Fin d → Type u)
    [∀ r, Fintype (J r)] [∀ r, DecidableEq (J r)]
    [∀ r, Fintype (B r)] [∀ r, DecidableEq (B r)] [∀ r, Nonempty (B r)]
    [Nonempty (Σ r, J r × B r)]
    (c : ∀ r, J r → Nat.Primes → ℂ) (alpha : ∀ r, B r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun b ↦ (alpha r b).re))
    (hrange : ∀ r, (Set.range (coefficientPattern (c r))).Finite)
    (htail : ∀ r, TailCoefficientIndependent (c r)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (fun x : Σ r, J r × B r ↦
        primePowerCoefficientShiftCarrier x.1 (c x.1 x.2.1) (alpha x.1 x.2.2)) := by
  unfold GaloisForLFunctions.DifferentialIndependent
  simp_rw [differentialJet_primePowerCoefficientShiftCarrier]
  let x : (Σ r, J r × B r) → ℕ → arithmeticFunctionRationalCoordinateField :=
    fun rb k ↦
      algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (primePowerCoefficientShiftedRotatedJet
            rb.1 (c rb.1 rb.2.1) (alpha rb.1 rb.2.2) k))
  apply algebraicIndependent_prod_nat_of_fin x
  intro m
  let f : ((Σ r, J r × B r) × Fin (m + 1)) →
      (Σ r, J r × (B r × Fin (m + 1))) := fun rbk ↦
    ⟨rbk.1.1, (rbk.1.2.1, (rbk.1.2.2, rbk.2))⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨r, j, b⟩, k⟩ ⟨⟨r', j', b'⟩, k'⟩ h
    cases h
    rfl
  have hrect := primePowerCoefficientShiftedJets_algebraicIndependent
    J B c alpha hdistinct hrange htail (fun _ ↦ m)
  have hsub := hrect.comp f hf
  simpa only [Function.comp_apply, f, x] using! hsub

end

end GaloisForLFunctions.HTGeometry
