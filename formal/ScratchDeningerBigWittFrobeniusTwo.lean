import GaloisForLFunctions.RHTower.DeningerGammaSixBigWittStokesSource
import Mathlib.RingTheory.PowerSeries.Expand

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

open PowerSeries

variable {A B : Type*} [CommRing A] [CommRing B]

def scratchBigWittFrobeniusTwoNormSeries
    (w : DeningerBigWittRing A) : PowerSeries A :=
  let f := deningerBigWittRingSeries w
  PowerSeries.mk fun n =>
    PowerSeries.coeff (2 * n) (f * PowerSeries.rescale (-1 : A) f)

@[simp] theorem scratchBigWittFrobeniusTwoNormSeries_constantCoeff
    (w : DeningerBigWittRing A) :
    PowerSeries.constantCoeff (scratchBigWittFrobeniusTwoNormSeries w) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [scratchBigWittFrobeniusTwoNormSeries,
    deningerBigWittRingSeries, PowerSeries.coeff_mul]

def scratchBigWittFrobeniusTwo
    (w : DeningerBigWittRing A) : DeningerBigWittRing A :=
  ⟨Additive.ofMul
    (deningerBigWittOfSeries
      (scratchBigWittFrobeniusTwoNormSeries w)
      (scratchBigWittFrobeniusTwoNormSeries_constantCoeff w))⟩

@[simp] theorem scratchBigWittRingSeries_frobeniusTwo
    (w : DeningerBigWittRing A) :
    deningerBigWittRingSeries (scratchBigWittFrobeniusTwo w) =
      scratchBigWittFrobeniusTwoNormSeries w := by
  rfl

theorem scratch_ghost_one_eq_neg_coeff_one
    (w : DeningerBigWittRing A) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one w =
      -PowerSeries.coeff 1 (deningerBigWittRingSeries w) := by
  let x := (deningerBigWittEulerEquiv A).symm
    (Additive.toMul w.additiveVal)
  have hw : deningerBigWittRingSeries w = deningerBigWittEulerSeries x := by
    rw [deningerBigWittRingSeries, show Additive.toMul w.additiveVal =
      deningerBigWittEulerEquiv A x from
        ((deningerBigWittEulerEquiv A).apply_symm_apply _).symm,
      deningerBigWittSeries_eulerEquiv]
  change deningerBigWittGhostCoeff (Additive.toMul w.additiveVal) 1 = _
  rw [show Additive.toMul w.additiveVal = deningerBigWittEulerEquiv A x from
    ((deningerBigWittEulerEquiv A).apply_symm_apply _).symm,
    deningerBigWittGhostCoeff_euler x Nat.zero_lt_one]
  rw [hw]
  simp [deningerBigWittEulerGhost, deningerBigWittEulerSeries_coeff,
    deningerBigWittEulerPartial, deningerBigWittFactor]

theorem scratch_ghost_two_eq_coeff_formula
    (w : DeningerBigWittRing A) :
    deningerBigWittGhostComponent 2 (by norm_num) w =
      PowerSeries.coeff 1 (deningerBigWittRingSeries w) ^ 2 -
        2 * PowerSeries.coeff 2 (deningerBigWittRingSeries w) := by
  let x := (deningerBigWittEulerEquiv A).symm
    (Additive.toMul w.additiveVal)
  have hw : deningerBigWittRingSeries w = deningerBigWittEulerSeries x := by
    rw [deningerBigWittRingSeries, show Additive.toMul w.additiveVal =
      deningerBigWittEulerEquiv A x from
        ((deningerBigWittEulerEquiv A).apply_symm_apply _).symm,
      deningerBigWittSeries_eulerEquiv]
  change deningerBigWittGhostCoeff (Additive.toMul w.additiveVal) 2 = _
  rw [show Additive.toMul w.additiveVal = deningerBigWittEulerEquiv A x from
    ((deningerBigWittEulerEquiv A).apply_symm_apply _).symm,
    deningerBigWittGhostCoeff_euler x (by norm_num)]
  rw [hw]
  have hc1 : PowerSeries.coeff 1 (deningerBigWittEulerSeries x) = -x 0 := by
    simp [deningerBigWittEulerSeries_coeff, deningerBigWittEulerPartial,
      deningerBigWittFactor]
  have hc2 : PowerSeries.coeff 2 (deningerBigWittEulerSeries x) = -x 1 := by
    rw [deningerBigWittEulerSeries_coeff]
    rw [show deningerBigWittEulerPartial x 2 =
        deningerBigWittFactor (x 0) 1 * deningerBigWittFactor (x 1) 2 by
      norm_num [deningerBigWittEulerPartial, Finset.prod_range_succ]]
    rw [coeff_mul_deningerBigWittFactor_self]
    simp [deningerBigWittFactor]
  rw [hc1, hc2]
  have hg : deningerBigWittEulerGhost x 2 = x 0 ^ 2 + 2 * x 1 := by
    norm_num [deningerBigWittEulerGhost, Finset.sum_range_succ]
  rw [hg]
  ring

theorem scratch_frobeniusTwo_ghost_one
    (w : DeningerBigWittRing A) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (scratchBigWittFrobeniusTwo w) =
      deningerBigWittGhostComponent 2 (by norm_num) w := by
  rw [scratch_ghost_one_eq_neg_coeff_one,
    scratchBigWittRingSeries_frobeniusTwo,
    scratchBigWittFrobeniusTwoNormSeries,
    PowerSeries.coeff_mk,
    scratch_ghost_two_eq_coeff_formula]
  rw [PowerSeries.coeff_mul]
  simp only [Nat.mul_one]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_rescale]
  norm_num [Finset.sum_range_succ]
  rw [show PowerSeries.constantCoeff (deningerBigWittRingSeries w) = 1 by
    exact deningerBigWittSeries_constantCoeff _]
  ring

#check Complex.mul_conj
#check Complex.normSq_eq_norm_sq
#check deningerBigWittRingMap
#check PowerSeries.coeff_map

end

end RHTower
