import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittCanonicity
import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixGreenGibbsPhysicalReader

namespace RHTower

noncomputable section

open PowerSeries
open scoped BigOperators

variable {A : Type*} [CommRing A]

/-- Literal power series carried by the canonical big-Witt ring. -/
def deningerBigWittRingSeries (w : DeningerBigWittRing A) : PowerSeries A :=
  deningerBigWittSeries (Additive.toMul w.additiveVal)

@[simp] theorem deningerBigWittRingSeries_zero :
    deningerBigWittRingSeries (0 : DeningerBigWittRing A) = 1 := by
  rw [deningerBigWittRingSeries, deningerBigWittRing_additiveVal_zero]
  rfl

@[simp] theorem deningerBigWittRingSeries_add
    (x y : DeningerBigWittRing A) :
    deningerBigWittRingSeries (x + y) =
      deningerBigWittRingSeries x * deningerBigWittRingSeries y := by
  rw [deningerBigWittRingSeries, deningerBigWittRing_additiveVal_add]
  rfl

@[simp] theorem deningerBigWittRingSeries_teichmuller (a : A) :
    deningerBigWittRingSeries (deningerBigWittRingTeichmuller a) =
      deningerBigWittFactor a 1 := by
  exact deningerBigWittSeries_teichCarrier a

theorem deningerBigWittRingSeries_injective :
    Function.Injective (deningerBigWittRingSeries (A := A)) := by
  intro x y hxy
  apply DeningerBigWittRing.ext
  have hmul : Additive.toMul x.additiveVal = Additive.toMul y.additiveVal := by
    apply Subtype.ext
    apply Units.ext
    exact hxy
  exact congrArg Additive.ofMul hmul

/-- Unique first-ghost-null Teichmüller codiagonal of `a` and `b`. -/
def deningerBigWittTeichmullerCrossEffect (a b : A) : DeningerBigWittRing A :=
  deningerBigWittRingTeichmuller a +
    deningerBigWittRingTeichmuller b -
      deningerBigWittRingTeichmuller (a + b)

theorem deningerBigWittTeichmullerCrossEffect_balance (a b : A) :
    deningerBigWittTeichmullerCrossEffect a b +
        deningerBigWittRingTeichmuller (a + b) =
      deningerBigWittRingTeichmuller a +
        deningerBigWittRingTeichmuller b := by
  simp [deningerBigWittTeichmullerCrossEffect]

theorem deningerBigWittTeichmullerCodiagonal_ghost_one_eq_zero_iff
    (a b c : A) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittRingTeichmuller a +
          deningerBigWittRingTeichmuller b -
            deningerBigWittRingTeichmuller c) = 0 ↔
      c = a + b := by
  simp [sub_eq_zero]
  constructor <;> intro h <;> exact h.symm

theorem deningerBigWittTeichmullerCrossEffect_ghost_one (a b : A) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittTeichmullerCrossEffect a b) = 0 := by
  rw [deningerBigWittTeichmullerCrossEffect]
  simp

/-- Denominator-cleared literal series identity for the cross-effect. -/
theorem deningerBigWittTeichmullerCrossEffect_series_mul_factor (a b : A) :
    deningerBigWittRingSeries (deningerBigWittTeichmullerCrossEffect a b) *
        deningerBigWittFactor (a + b) 1 =
      deningerBigWittFactor a 1 * deningerBigWittFactor b 1 := by
  have h := congrArg deningerBigWittRingSeries
    (deningerBigWittTeichmullerCrossEffect_balance a b)
  simpa only [deningerBigWittRingSeries_add,
    deningerBigWittRingSeries_teichmuller] using h

/-- Division-free Green equation: the first-ghost-null codiagonal has exact quadratic source. -/
theorem deningerBigWittTeichmullerCrossEffect_green (a b : A) :
    deningerBigWittFactor (a + b) 1 *
        (deningerBigWittRingSeries
            (deningerBigWittTeichmullerCrossEffect a b) - 1) =
      PowerSeries.C (a * b) * PowerSeries.X ^ 2 := by
  calc
    deningerBigWittFactor (a + b) 1 *
        (deningerBigWittRingSeries
            (deningerBigWittTeichmullerCrossEffect a b) - 1) =
      deningerBigWittRingSeries
          (deningerBigWittTeichmullerCrossEffect a b) *
          deningerBigWittFactor (a + b) 1 -
        deningerBigWittFactor (a + b) 1 := by ring
    _ = deningerBigWittFactor a 1 * deningerBigWittFactor b 1 -
        deningerBigWittFactor (a + b) 1 := by
      rw [deningerBigWittTeichmullerCrossEffect_series_mul_factor]
    _ = PowerSeries.C (a * b) * PowerSeries.X ^ 2 := by
      simp only [deningerBigWittFactor, pow_one, map_add, map_mul]
      ring

theorem deningerBigWittTeichmullerCrossEffect_eq_zero_iff (a b : A) :
    deningerBigWittTeichmullerCrossEffect a b = 0 ↔ a * b = 0 := by
  constructor
  · intro hzero
    have hgreen := deningerBigWittTeichmullerCrossEffect_green a b
    rw [hzero, deningerBigWittRingSeries_zero, sub_self, mul_zero] at hgreen
    have hc := congrArg (PowerSeries.coeff 2) hgreen
    simpa only [map_zero, PowerSeries.coeff_C_mul_X_pow, if_pos] using hc.symm
  · intro hab
    have hfac :
        deningerBigWittFactor a 1 * deningerBigWittFactor b 1 =
          deningerBigWittFactor (a + b) 1 := by
      have hCab : PowerSeries.C a * PowerSeries.C b = 0 := by
        rw [← map_mul, hab, map_zero]
      simp only [deningerBigWittFactor, pow_one, map_add]
      calc
        (1 - PowerSeries.C a * PowerSeries.X) *
            (1 - PowerSeries.C b * PowerSeries.X) =
          1 - (PowerSeries.C a + PowerSeries.C b) * PowerSeries.X +
            (PowerSeries.C a * PowerSeries.C b) * PowerSeries.X ^ 2 := by ring
        _ = 1 - (PowerSeries.C a + PowerSeries.C b) * PowerSeries.X := by
          rw [hCab]
          ring
    have hsum :
        deningerBigWittRingTeichmuller a +
            deningerBigWittRingTeichmuller b =
          deningerBigWittRingTeichmuller (a + b) := by
      apply deningerBigWittRingSeries_injective
      simpa only [deningerBigWittRingSeries_add,
        deningerBigWittRingSeries_teichmuller] using hfac
    rw [deningerBigWittTeichmullerCrossEffect, hsum, sub_self]

theorem deningerBigWittTeichmullerCrossEffect_eq_zero_iff_mul_zero
    (a b : A) :
    deningerBigWittTeichmullerCrossEffect a b = 0 ↔
      deningerBigWittRingTeichmuller a *
        deningerBigWittRingTeichmuller b = 0 := by
  rw [deningerBigWittTeichmullerCrossEffect_eq_zero_iff,
    deningerBigWittRingTeichmuller_mul]
  constructor
  · intro hab
    rw [hab, deningerBigWittRingTeichmuller_zero]
  · intro h
    exact deningerBigWittRingTeichmuller_injective
      (h.trans deningerBigWittRingTeichmuller_zero.symm)

def deningerGammaSixBigWittAtom : ℚ := 1 / 6

def deningerGammaSixBigWittTail : ℚ := 5 / 6

def deningerGammaSixBigWittStokesSource : DeningerBigWittRing ℚ :=
  deningerBigWittTeichmullerCrossEffect (1 / 2 : ℚ) (1 / 3 : ℚ)

theorem deningerGammaSixBigWittStokesSource_balance :
    deningerGammaSixBigWittStokesSource +
        deningerBigWittRingTeichmuller deningerGammaSixBigWittTail =
      deningerBigWittRingTeichmuller (1 / 2 : ℚ) +
        deningerBigWittRingTeichmuller (1 / 3 : ℚ) := by
  have hs : (1 / 2 : ℚ) + 1 / 3 = deningerGammaSixBigWittTail := by
    norm_num [deningerGammaSixBigWittTail]
  rw [deningerGammaSixBigWittStokesSource, ← hs]
  exact deningerBigWittTeichmullerCrossEffect_balance
    (1 / 2 : ℚ) (1 / 3 : ℚ)

theorem deningerGammaSixBigWittStokesSource_green :
    deningerBigWittFactor deningerGammaSixBigWittTail 1 *
        (deningerBigWittRingSeries deningerGammaSixBigWittStokesSource - 1) =
      PowerSeries.C deningerGammaSixBigWittAtom * PowerSeries.X ^ 2 := by
  have hs : (1 / 2 : ℚ) + 1 / 3 = deningerGammaSixBigWittTail := by
    norm_num [deningerGammaSixBigWittTail]
  have hp : (1 / 2 : ℚ) * (1 / 3) = deningerGammaSixBigWittAtom := by
    norm_num [deningerGammaSixBigWittAtom]
  rw [deningerGammaSixBigWittStokesSource, ← hs, ← hp]
  exact deningerBigWittTeichmullerCrossEffect_green
    (1 / 2 : ℚ) (1 / 3 : ℚ)

theorem deningerGammaSixBigWittStokesSource_ne_zero :
    deningerGammaSixBigWittStokesSource ≠ 0 := by
  rw [deningerGammaSixBigWittStokesSource,
    ne_eq, deningerBigWittTeichmullerCrossEffect_eq_zero_iff]
  norm_num

theorem deningerGammaSixBigWittAtom_eq_teichmuller_product :
    deningerBigWittRingTeichmuller (1 / 2 : ℚ) *
        deningerBigWittRingTeichmuller (1 / 3 : ℚ) =
      deningerBigWittRingTeichmuller deningerGammaSixBigWittAtom := by
  rw [deningerBigWittRingTeichmuller_mul]
  congr 1
  norm_num [deningerGammaSixBigWittAtom]

theorem deningerGammaSixBigWittTail_eq_one_sub_atom :
    deningerGammaSixBigWittTail = 1 - deningerGammaSixBigWittAtom := by
  norm_num [deningerGammaSixBigWittTail, deningerGammaSixBigWittAtom]

theorem deningerGammaSixBigWittFaces_rigid
    {a b : ℚ}
    (hsum : a + b = deningerGammaSixBigWittTail)
    (hprod : a * b = deningerGammaSixBigWittAtom) :
    (a = 1 / 2 ∧ b = 1 / 3) ∨ (a = 1 / 3 ∧ b = 1 / 2) := by
  have hfac : (2 * a - 1) * (3 * a - 1) = 0 := by
    simp only [deningerGammaSixBigWittTail] at hsum
    simp only [deningerGammaSixBigWittAtom] at hprod
    have hb : b = 5 / 6 - a := by linarith
    rw [hb] at hprod
    have hquad : 6 * a ^ 2 - 5 * a + 1 = 0 := by nlinarith
    calc
      (2 * a - 1) * (3 * a - 1) = 6 * a ^ 2 - 5 * a + 1 := by ring
      _ = 0 := hquad
  rcases mul_eq_zero.mp hfac with ha | ha
  · left
    constructor
    · linarith
    · simp only [deningerGammaSixBigWittTail] at hsum
      linarith
  · right
    constructor
    · linarith
    · simp only [deningerGammaSixBigWittTail] at hsum
      linarith

theorem deningerGammaSixBigWittCoefficients_control_wold
    (n : ℕ) {m : ℕ} (hm : 3 ≤ m) :
    deningerGammaSixShellEigenvalue (deningerGammaSixWoldCoordinate n) =
        ((deningerGammaSixBigWittAtom : ℚ) : ℝ) *
          deningerGammaSixShellEigenvalue n ∧
      (∑ k ∈ deningerGammaSixShellCoordinates m,
          deningerGammaSixShellEigenvalue k) =
        (6 : ℝ) * ((deningerGammaSixBigWittTail : ℚ) : ℝ) := by
  constructor
  · simpa [deningerGammaSixBigWittAtom] using
      deningerGammaSixShellEigenvalue_wold n
  · rw [deningerGammaSixShellTraceMass_eq_five hm]
    norm_num [deningerGammaSixBigWittTail]

theorem deningerGammaSixGreenGibbsContinuation_eq_bigWittAtom
    (delta : ℝ) :
    deningerGammaSixGreenGibbsContinuation delta =
      ((deningerGammaSixBigWittAtom : ℚ) : ℝ) *
        (1 - ((deningerGammaSixBigWittAtom : ℚ) : ℝ) ^ delta) := by
  simp [deningerGammaSixGreenGibbsContinuation,
    deningerGammaSixBigWittAtom]

theorem DAC_DENINGER_GAMMA_SIX_BIG_WITT_STOKES_SOURCE :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
          deningerGammaSixBigWittStokesSource = 0 ∧
      deningerGammaSixBigWittStokesSource ≠ 0 ∧
      deningerBigWittFactor deningerGammaSixBigWittTail 1 *
          (deningerBigWittRingSeries deningerGammaSixBigWittStokesSource - 1) =
        PowerSeries.C deningerGammaSixBigWittAtom * PowerSeries.X ^ 2 ∧
      deningerBigWittRingTeichmuller (1 / 2 : ℚ) *
          deningerBigWittRingTeichmuller (1 / 3 : ℚ) =
        deningerBigWittRingTeichmuller deningerGammaSixBigWittAtom := by
  refine ⟨?_, deningerGammaSixBigWittStokesSource_ne_zero,
    deningerGammaSixBigWittStokesSource_green,
    deningerGammaSixBigWittAtom_eq_teichmuller_product⟩
  exact deningerBigWittTeichmullerCrossEffect_ghost_one
    (1 / 2 : ℚ) (1 / 3 : ℚ)

end

end RHTower
