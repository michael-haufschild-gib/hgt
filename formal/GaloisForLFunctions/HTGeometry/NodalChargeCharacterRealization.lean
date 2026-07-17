import GaloisForLFunctions.HTGeometry.MeromorphicExponentialGaugeDA
import GaloisForLFunctions.Hurwitz.ExpIndependence

/-!
# Nodal charge character realization

Fix a nonzero selected period `ω`.  The charge-`m` nodal coordinate is the exponential mode with
frequency

```text
λ(ω,m) = 2π i m / ω.
```

It is fixed by translation through `ω`, while every other source translation acts through its
actual character and differentiation acts with eigenvalue `λ(ω,m)`.  Distinct integral charges
give linearly independent analytic modes.  Thus the complete nodal receiver is character-graded;
it is not one ungraded rank-one fibre.

For two rationally independent periods, their integral charge-frequency lattices meet only at
zero.  Consequently nonzero charge lines belonging to distinct source faces cannot be glued by
identifying their source characters.  The positive global shape forced by this theorem is a
face-separated character object whose rays meet in the neutral sector.

These are exact Fourier/character-theoretic bridge statements.  They do not construct the open
source-presentation-invariant realization from a Tate localization class to a Barnes face module.
-/

open Filter Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open Bottcher

noncomputable section

open scoped BigOperators

local instance nodalChargeIncidenceDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance nodalChargeComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance nodalChargeComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance nodalChargeDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- The differential eigenfrequency of charge `m` on the face selected by the period `ω`. -/
def nodalChargeFrequency (ω : ℂ) (m : ℤ) : ℂ :=
  (m : ℂ) * (2 * Real.pi * Complex.I) / ω

@[simp]
theorem nodalChargeFrequency_zero (ω : ℂ) :
    nodalChargeFrequency ω 0 = 0 := by
  simp [nodalChargeFrequency]

/-- Reversing the integral orientation negates the differential character. -/
@[simp]
theorem nodalChargeFrequency_neg (ω : ℂ) (m : ℤ) :
    nodalChargeFrequency ω (-m) = -nodalChargeFrequency ω m := by
  simp only [nodalChargeFrequency, Int.cast_neg]
  ring

/-- Multiplying the charge frequency by its selected period recovers the integral logarithmic
character. -/
theorem nodalChargeFrequency_mul_period
    (ω : ℂ) (hω : ω ≠ 0) (m : ℤ) :
    nodalChargeFrequency ω m * ω =
      (m : ℂ) * (2 * Real.pi * Complex.I) := by
  simpa [nodalChargeFrequency] using
    div_mul_cancel₀ ((m : ℂ) * (2 * Real.pi * Complex.I)) hω

/-- Every integral charge frequency has trivial character on its selected period. -/
theorem exp_nodalChargeFrequency_mul_period
    (ω : ℂ) (hω : ω ≠ 0) (m : ℤ) :
    Complex.exp (nodalChargeFrequency ω m * ω) = 1 := by
  apply Complex.exp_eq_one_iff.mpr
  exact ⟨m, nodalChargeFrequency_mul_period ω hω m⟩

/-- Charge is faithfully recorded by the differential frequency on every nonzero period face. -/
theorem nodalChargeFrequency_injective
    (ω : ℂ) (hω : ω ≠ 0) :
    Function.Injective (nodalChargeFrequency ω) := by
  intro m n hmn
  have hscaled := congrArg (fun z : ℂ ↦ z * ω) hmn
  simp only [nodalChargeFrequency_mul_period ω hω] at hscaled
  have htwoPiI : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  exact_mod_cast mul_right_cancel₀ htwoPiI hscaled

/-- The analytic nodal mode of integral charge `m`. -/
def nodalChargeMode (ω : ℂ) (m : ℤ) : ℂ → ℂ :=
  physicalExponentialMode (nodalChargeFrequency ω m)

/-- Opposite charge sectors are multiplicative duals.  The unpolarized family is invariant under
orientation reversal, while a choice of positive ray is not. -/
theorem nodalChargeMode_neg_mul (ω : ℂ) (m : ℤ) (z : ℂ) :
    nodalChargeMode ω (-m) z * nodalChargeMode ω m z = 1 := by
  simp [nodalChargeMode, physicalExponentialMode, ← Complex.exp_add]

/-- Every complementary source translation acts on a nodal mode by its actual character. -/
theorem nodalChargeMode_add
    (ω : ℂ) (m : ℤ) (τ z : ℂ) :
    nodalChargeMode ω m (z + τ) =
      Complex.exp (nodalChargeFrequency ω m * τ) * nodalChargeMode ω m z := by
  exact physicalExponentialMode_add (nodalChargeFrequency ω m) τ z

/-- A charge mode is fixed by the selected period. -/
theorem nodalChargeMode_periodic
    (ω : ℂ) (hω : ω ≠ 0) (m : ℤ) :
    Function.Periodic (nodalChargeMode ω m) ω := by
  intro z
  rw [nodalChargeMode_add, exp_nodalChargeFrequency_mul_period ω hω m, one_mul]

/-- Every finite packet of distinct charges is linearly independent.  Equivalently, the analytic
nodal receiver is the algebraic direct sum of its charge-character lines. -/
theorem nodalChargeModes_linearIndependent
    {n : ℕ} (ω : ℂ) (hω : ω ≠ 0) (charge : Fin n → ℤ)
    (hcharge : Function.Injective charge) :
    LinearIndependent ℂ (fun i : Fin n ↦ nodalChargeMode ω (charge i)) := by
  have hfrequency : Function.Injective
      (fun i : Fin n ↦ nodalChargeFrequency ω (charge i)) :=
    (nodalChargeFrequency_injective ω hω).comp hcharge
  simpa [nodalChargeMode, physicalExponentialMode] using
    HurwitzExp.expLin_linearIndependent hfrequency

/-- The genuine meromorphic representative of one nodal charge line. -/
def nodalChargeMero (ω : ℂ) (m : ℤ) : meroField (Set.univ : Set ℂ) :=
  physicalExponentialMero (nodalChargeFrequency ω m)

/-- The meromorphic charge vector is nonzero. -/
theorem nodalChargeMero_ne_zero (ω : ℂ) (m : ℤ) :
    nodalChargeMero ω m ≠ 0 :=
  physicalExponentialMero_ne_zero (nodalChargeFrequency ω m)

/-- Complementary translations retain their full source character on the meromorphic
realization. -/
theorem addTranslationMeroEquiv_nodalChargeMero
    (ω : ℂ) (m : ℤ) (τ : ℂ) :
    addTranslationMeroEquiv τ (nodalChargeMero ω m) =
      algebraMap ℂ (meroField Set.univ)
          (Complex.exp (nodalChargeFrequency ω m * τ)) *
        nodalChargeMero ω m := by
  exact addTranslationMeroEquiv_physicalExponentialMero
    τ (nodalChargeFrequency ω m)

/-- The selected source operator `T_ω - 1` annihilates the meromorphic charge vector. -/
theorem addTranslationMeroEquiv_nodalChargeMero_selected
    (ω : ℂ) (hω : ω ≠ 0) (m : ℤ) :
    addTranslationMeroEquiv ω (nodalChargeMero ω m) = nodalChargeMero ω m := by
  rw [addTranslationMeroEquiv_nodalChargeMero,
    exp_nodalChargeFrequency_mul_period ω hω m]
  simp

/-- Differentiation separates the charge lines by their integral frequencies. -/
theorem nodalChargeMero_deriv (ω : ℂ) (m : ℤ) :
    (nodalChargeMero ω m)′ =
      algebraMap ℂ (meroField Set.univ) (nodalChargeFrequency ω m) *
        nodalChargeMero ω m := by
  exact physicalExponentialMero_deriv (nodalChargeFrequency ω m)

/-- **Face-separation law.**  For two rationally independent periods, the two integral nodal
frequency lattices intersect only in their neutral charge. -/
theorem nodalChargeFrequency_pair_eq_iff_neutral
    (period : Fin 2 → ℂ) (hperiod : LinearIndependent ℚ period)
    (m n : ℤ) :
    nodalChargeFrequency (period 0) m = nodalChargeFrequency (period 1) n ↔
      m = 0 ∧ n = 0 := by
  have hperiod0 : period 0 ≠ 0 := hperiod.ne_zero 0
  have hperiod1 : period 1 ≠ 0 := hperiod.ne_zero 1
  constructor
  · intro hfrequency
    have hfirst : Complex.exp
        (nodalChargeFrequency (period 0) m * period 0) = 1 :=
      exp_nodalChargeFrequency_mul_period (period 0) hperiod0 m
    have hsecond : Complex.exp
        (nodalChargeFrequency (period 0) m * period 1) = 1 := by
      rw [hfrequency]
      exact exp_nodalChargeFrequency_mul_period (period 1) hperiod1 n
    have hzero : nodalChargeFrequency (period 0) m = 0 :=
      (exp_mul_pair_eq_one_eq_one_iff_of_linearIndependent period hperiod
        (nodalChargeFrequency (period 0) m)).mp ⟨hfirst, hsecond⟩
    have hm : m = 0 := (nodalChargeFrequency_injective (period 0) hperiod0) (by
      simpa using hzero)
    have hnFrequency : nodalChargeFrequency (period 1) n = 0 := by
      rw [← hfrequency, hzero]
    have hn : n = 0 := (nodalChargeFrequency_injective (period 1) hperiod1) (by
      simpa using hnFrequency)
    exact ⟨hm, hn⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- The analytic realization of the oriented charge interval `[0,m)`: pair every charge sector
with its orientation-reversed dual and sum all sectors retained by the boundary. -/
def nodalChargeBoundaryIntervalPairing
    (ω : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range m,
    nodalChargeMode ω (-(k : ℤ)) z * nodalChargeMode ω (k : ℤ) z

/-- **Charge-interval multiplicity law.** The analytic pairing of the complete oriented boundary
interval has value `m`. Thus its decategorified weight remembers the thickness of the boundary. -/
theorem nodalChargeBoundaryIntervalPairing_eq
    (ω : ℂ) (m : ℕ) (z : ℂ) :
    nodalChargeBoundaryIntervalPairing ω m z = (m : ℂ) := by
  simp [nodalChargeBoundaryIntervalPairing, nodalChargeMode_neg_mul]

/-- **Endpoint no-go, with sharp positive exception.** The complete interval pairing agrees with
the pairing of its charge-`m` endpoint exactly in the primitive one-step case `m = 1`. -/
theorem nodalChargeBoundaryIntervalPairing_eq_endpoint_iff
    (ω : ℂ) (m : ℕ) (z : ℂ) :
    nodalChargeBoundaryIntervalPairing ω m z =
        nodalChargeMode ω (-(m : ℤ)) z * nodalChargeMode ω (m : ℤ) z ↔
      m = 1 := by
  rw [nodalChargeBoundaryIntervalPairing_eq, nodalChargeMode_neg_mul]
  exact_mod_cast Nat.cast_eq_one

end

end GaloisForLFunctions.HTGeometry
