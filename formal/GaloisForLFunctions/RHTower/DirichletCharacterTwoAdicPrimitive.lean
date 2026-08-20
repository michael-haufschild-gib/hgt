/-
# Primitivity of explicit two-adic quadratic characters

This begins the conductor layer with a closed local proof at level four.  The
proof eliminates every proper positive divisor directly from explicit values.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicQuadratic
import Mathlib.NumberTheory.DirichletCharacter.Basic

noncomputable section

namespace RHTower

/-- The explicit level-four character is nontrivial. -/
theorem quadraticCharacterFour_ne_one : quadraticCharacterFour ≠ 1 := by
  intro h
  have h3 := congrArg (fun χ : DirichletCharacter ℂ 4 => χ (3 : ZMod 4)) h
  have hunit : IsUnit (3 : ZMod 4) :=
    (ZMod.isUnit_iff_coprime 3 4).mpr (by decide)
  have hone : (1 : DirichletCharacter ℂ 4) (3 : ZMod 4) = 1 :=
    MulChar.one_apply hunit
  rw [hone] at h3
  norm_num [quadraticCharacterFour, ZMod.χ₄] at h3

/-- The first explicit level-eight character is nontrivial. -/
theorem quadraticCharacterEight_ne_one : quadraticCharacterEight ≠ 1 := by
  intro h
  have h5 := congrArg (fun χ : DirichletCharacter ℂ 8 => χ (5 : ZMod 8)) h
  have hunit : IsUnit (5 : ZMod 8) :=
    (ZMod.isUnit_iff_coprime 5 8).mpr (by decide)
  have hone : (1 : DirichletCharacter ℂ 8) (5 : ZMod 8) = 1 :=
    MulChar.one_apply hunit
  rw [hone] at h5
  norm_num [quadraticCharacterEight, ZMod.χ₈] at h5

/-- The second explicit level-eight character is nontrivial. -/
theorem quadraticCharacterEightPrime_ne_one : quadraticCharacterEightPrime ≠ 1 := by
  intro h
  have h5 := congrArg (fun χ : DirichletCharacter ℂ 8 => χ (5 : ZMod 8)) h
  have hunit : IsUnit (5 : ZMod 8) :=
    (ZMod.isUnit_iff_coprime 5 8).mpr (by decide)
  have hone : (1 : DirichletCharacter ℂ 8) (5 : ZMod 8) = 1 :=
    MulChar.one_apply hunit
  rw [hone] at h5
  norm_num [quadraticCharacterEightPrime, ZMod.χ₈'] at h5

/-- The explicit level-four quadratic character has conductor exactly four. -/
theorem quadraticCharacterFour_isPrimitive :
    DirichletCharacter.IsPrimitive quadraticCharacterFour := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdiv : DirichletCharacter.conductor quadraticCharacterFour ∣ 4 :=
    DirichletCharacter.conductor_dvd_level quadraticCharacterFour
  have hnonzero : DirichletCharacter.conductor quadraticCharacterFour ≠ 0 :=
    DirichletCharacter.conductor_ne_zero quadraticCharacterFour
  have hle : DirichletCharacter.conductor quadraticCharacterFour ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hdiv
  interval_cases hc : DirichletCharacter.conductor quadraticCharacterFour
  · exact (hnonzero rfl).elim
  · exact (quadraticCharacterFour_ne_one
      ((DirichletCharacter.eq_one_iff_conductor_eq_one
        (χ := quadraticCharacterFour)).mpr hc)).elim
  · exfalso
    let hfac := DirichletCharacter.factorsThrough_conductor quadraticCharacterFour
    rw [hc] at hfac
    have hcop1 : IsCoprime (1 : ℤ) (4 : ℤ) := by decide
    have hcop3 : IsCoprime (3 : ℤ) (4 : ℤ) := by decide
    have hval : quadraticCharacterFour ((1 : ℤ) : ZMod 4) =
        quadraticCharacterFour ((3 : ℤ) : ZMod 4) := by
      calc
        _ = (DirichletCharacter.changeLevel hfac.dvd hfac.χ₀) (1 : ℤ) :=
          congrArg (fun χ : DirichletCharacter ℂ 4 => χ ((1 : ℤ) : ZMod 4)) hfac.eq_changeLevel
        _ = hfac.χ₀ (1 : ℤ) :=
          DirichletCharacter.changeLevel_eq_cast_of_dvd' hfac.χ₀ hfac.dvd hcop1
        _ = hfac.χ₀ (3 : ℤ) := by congr 1
        _ = (DirichletCharacter.changeLevel hfac.dvd hfac.χ₀) (3 : ℤ) :=
          (DirichletCharacter.changeLevel_eq_cast_of_dvd' hfac.χ₀ hfac.dvd hcop3).symm
        _ = _ := (congrArg
          (fun χ : DirichletCharacter ℂ 4 => χ ((3 : ℤ) : ZMod 4)) hfac.eq_changeLevel).symm
    norm_num [quadraticCharacterFour, ZMod.χ₄] at hval
  · norm_num at hdiv
  · rfl

/-- The first explicit level-eight quadratic character has conductor exactly eight. -/
theorem quadraticCharacterEight_isPrimitive :
    DirichletCharacter.IsPrimitive quadraticCharacterEight := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdiv : DirichletCharacter.conductor quadraticCharacterEight ∣ 8 :=
    DirichletCharacter.conductor_dvd_level quadraticCharacterEight
  have hnonzero : DirichletCharacter.conductor quadraticCharacterEight ≠ 0 :=
    DirichletCharacter.conductor_ne_zero quadraticCharacterEight
  have hle : DirichletCharacter.conductor quadraticCharacterEight ≤ 8 :=
    Nat.le_of_dvd (by norm_num) hdiv
  interval_cases hc : DirichletCharacter.conductor quadraticCharacterEight
  · exact (hnonzero rfl).elim
  · exact (quadraticCharacterEight_ne_one
      ((DirichletCharacter.eq_one_iff_conductor_eq_one
        (χ := quadraticCharacterEight)).mpr hc)).elim
  · exfalso
    let hfac := DirichletCharacter.factorsThrough_conductor quadraticCharacterEight
    rw [hc] at hfac
    have hcop1 : IsCoprime (1 : ℤ) (8 : ℤ) := by decide
    have hcop3 : IsCoprime (3 : ℤ) (8 : ℤ) := by decide
    have hval : quadraticCharacterEight ((1 : ℤ) : ZMod 8) =
        quadraticCharacterEight ((3 : ℤ) : ZMod 8) := by
      calc
        _ = (DirichletCharacter.changeLevel hfac.dvd hfac.χ₀) (1 : ℤ) :=
          congrArg (fun χ : DirichletCharacter ℂ 8 => χ ((1 : ℤ) : ZMod 8)) hfac.eq_changeLevel
        _ = hfac.χ₀ (1 : ℤ) :=
          DirichletCharacter.changeLevel_eq_cast_of_dvd' hfac.χ₀ hfac.dvd hcop1
        _ = hfac.χ₀ (3 : ℤ) := by congr 1
        _ = (DirichletCharacter.changeLevel hfac.dvd hfac.χ₀) (3 : ℤ) :=
          (DirichletCharacter.changeLevel_eq_cast_of_dvd' hfac.χ₀ hfac.dvd hcop3).symm
        _ = _ := (congrArg
          (fun χ : DirichletCharacter ℂ 8 => χ ((3 : ℤ) : ZMod 8)) hfac.eq_changeLevel).symm
    norm_num [quadraticCharacterEight, ZMod.χ₈] at hval
  · norm_num at hdiv
  · exfalso
    let hfac := DirichletCharacter.factorsThrough_conductor quadraticCharacterEight
    rw [hc] at hfac
    have hcop1 : IsCoprime (1 : ℤ) (8 : ℤ) := by decide
    have hcop5 : IsCoprime (5 : ℤ) (8 : ℤ) := by decide
    have hval : quadraticCharacterEight ((1 : ℤ) : ZMod 8) =
        quadraticCharacterEight ((5 : ℤ) : ZMod 8) := by
      calc
        _ = (DirichletCharacter.changeLevel hfac.dvd hfac.χ₀) (1 : ℤ) :=
          congrArg (fun χ : DirichletCharacter ℂ 8 => χ ((1 : ℤ) : ZMod 8)) hfac.eq_changeLevel
        _ = hfac.χ₀ (1 : ℤ) :=
          DirichletCharacter.changeLevel_eq_cast_of_dvd' hfac.χ₀ hfac.dvd hcop1
        _ = hfac.χ₀ (5 : ℤ) := by congr 1
        _ = (DirichletCharacter.changeLevel hfac.dvd hfac.χ₀) (5 : ℤ) :=
          (DirichletCharacter.changeLevel_eq_cast_of_dvd' hfac.χ₀ hfac.dvd hcop5).symm
        _ = _ := (congrArg
          (fun χ : DirichletCharacter ℂ 8 => χ ((5 : ℤ) : ZMod 8)) hfac.eq_changeLevel).symm
    norm_num [quadraticCharacterEight, ZMod.χ₈] at hval
  · norm_num at hdiv
  · norm_num at hdiv
  · norm_num at hdiv
  · rfl

/-- The second explicit level-eight quadratic character has conductor exactly eight. -/
theorem quadraticCharacterEightPrime_isPrimitive :
    DirichletCharacter.IsPrimitive quadraticCharacterEightPrime := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdiv : DirichletCharacter.conductor quadraticCharacterEightPrime ∣ 8 :=
    DirichletCharacter.conductor_dvd_level quadraticCharacterEightPrime
  have hnonzero : DirichletCharacter.conductor quadraticCharacterEightPrime ≠ 0 :=
    DirichletCharacter.conductor_ne_zero quadraticCharacterEightPrime
  have hle : DirichletCharacter.conductor quadraticCharacterEightPrime ≤ 8 :=
    Nat.le_of_dvd (by norm_num) hdiv
  interval_cases hc : DirichletCharacter.conductor quadraticCharacterEightPrime
  · exact (hnonzero rfl).elim
  · exact (quadraticCharacterEightPrime_ne_one
      ((DirichletCharacter.eq_one_iff_conductor_eq_one
        (χ := quadraticCharacterEightPrime)).mpr hc)).elim
  · exfalso
    let hfac := DirichletCharacter.factorsThrough_conductor quadraticCharacterEightPrime
    rw [hc] at hfac
    have hcop1 : IsCoprime (1 : ℤ) (8 : ℤ) := by decide
    have hcop5 : IsCoprime (5 : ℤ) (8 : ℤ) := by decide
    have hval : quadraticCharacterEightPrime ((1 : ℤ) : ZMod 8) =
        quadraticCharacterEightPrime ((5 : ℤ) : ZMod 8) := by
      calc
        _ = (DirichletCharacter.changeLevel hfac.dvd hfac.χ₀) (1 : ℤ) :=
          congrArg (fun χ : DirichletCharacter ℂ 8 => χ ((1 : ℤ) : ZMod 8)) hfac.eq_changeLevel
        _ = hfac.χ₀ (1 : ℤ) :=
          DirichletCharacter.changeLevel_eq_cast_of_dvd' hfac.χ₀ hfac.dvd hcop1
        _ = hfac.χ₀ (5 : ℤ) := by congr 1
        _ = (DirichletCharacter.changeLevel hfac.dvd hfac.χ₀) (5 : ℤ) :=
          (DirichletCharacter.changeLevel_eq_cast_of_dvd' hfac.χ₀ hfac.dvd hcop5).symm
        _ = _ := (congrArg
          (fun χ : DirichletCharacter ℂ 8 => χ ((5 : ℤ) : ZMod 8)) hfac.eq_changeLevel).symm
    norm_num [quadraticCharacterEightPrime, ZMod.χ₈'] at hval
  · norm_num at hdiv
  · exfalso
    let hfac := DirichletCharacter.factorsThrough_conductor quadraticCharacterEightPrime
    rw [hc] at hfac
    have hcop1 : IsCoprime (1 : ℤ) (8 : ℤ) := by decide
    have hcop5 : IsCoprime (5 : ℤ) (8 : ℤ) := by decide
    have hval : quadraticCharacterEightPrime ((1 : ℤ) : ZMod 8) =
        quadraticCharacterEightPrime ((5 : ℤ) : ZMod 8) := by
      calc
        _ = (DirichletCharacter.changeLevel hfac.dvd hfac.χ₀) (1 : ℤ) :=
          congrArg (fun χ : DirichletCharacter ℂ 8 => χ ((1 : ℤ) : ZMod 8)) hfac.eq_changeLevel
        _ = hfac.χ₀ (1 : ℤ) :=
          DirichletCharacter.changeLevel_eq_cast_of_dvd' hfac.χ₀ hfac.dvd hcop1
        _ = hfac.χ₀ (5 : ℤ) := by congr 1
        _ = (DirichletCharacter.changeLevel hfac.dvd hfac.χ₀) (5 : ℤ) :=
          (DirichletCharacter.changeLevel_eq_cast_of_dvd' hfac.χ₀ hfac.dvd hcop5).symm
        _ = _ := (congrArg
          (fun χ : DirichletCharacter ℂ 8 => χ ((5 : ℤ) : ZMod 8)) hfac.eq_changeLevel).symm
    norm_num [quadraticCharacterEightPrime, ZMod.χ₈'] at hval
  · norm_num at hdiv
  · norm_num at hdiv
  · norm_num at hdiv
  · rfl

end RHTower
