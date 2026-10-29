import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep
import GaloisForLFunctions.ArithmeticIndexDescent.TheCriticalSourceRateHasACanonicalEnergy

/-!
# Index is energy

The price list of the Weil kernel of `ζ`. Its Gram matrices are prime-side Weil Gram matrices of
translates of the cubic spline (`gram_zetaKernel_eq_weilGram`), so the canonical critical source
energy `E_crit` (the height-square energy of the off-line zeros) pays for every negative square:

* **Quadratic price** (`resolventIndexCharge_gram_zetaKernel_le`): a family with `m` negative squares
  forces `E_crit ≥ 50 m² − 3m/2`.
* **Index bound by energy** (`negIndex_zetaKernel_le_of_energy`): if `E_crit` is finite, then
  `κ(K_ζ)² ≤ 2 E_crit / 97`: the index grows at most like the square root of the critical energy.
* **RH as an energy threshold** (`riemannHypothesis_tfae_energy`): `κ(K_ζ) = 0` iff `E_crit` is at most
  one exclusion quantum.

Index is energy: negative squares are not errors but charges, each one with a price that grows
quadratically with the index.
-/

open Complex Finset
open Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx weilGram weilGram_eq_zeroGram cx_contDiff
  cx_hasCompactSupport translate_contDiff translate_hasCompactSupport)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri renaming translate → shiftTest
open GaloisForLFunctions.ArithmeticIndexDescent (xiCriticalSourceEnergy resolventIndexCharge
  resolventIndexCharge_le_criticalEnergy quadraticExclusionQuantum
  riemannHypothesis_iff_criticalEnergy_le_quantum)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- The Gram matrices of the Weil kernel of `ζ` are prime-side Weil Gram matrices. -/
theorem gram_zetaKernel_eq_weilGram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → HeckeLattice) :
    gram zetaKernel x = weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      fun a => shiftTest (scale heckeLogScale (x a)) (cx cubicSpline) := by
  rw [zetaKernel, gram_orbitKernel, weilGram_eq_zeroGram _
    (fun a => translate_contDiff (cx_contDiff cubicSpline_mem_realTests.1) _)
    (fun a => translate_hasCompactSupport (cx_hasCompactSupport cubicSpline_mem_realTests.2) _)]

/-- **The quadratic price of the index.** -/
theorem resolventIndexCharge_gram_zetaKernel_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → HeckeLattice) :
    ENNReal.ofReal (resolventIndexCharge (hermNegIndex (gram zetaKernel x))) ≤
      xiCriticalSourceEnergy := by
  rw [gram_zetaKernel_eq_weilGram]
  exact resolventIndexCharge_le_criticalEnergy _
    (fun a => translate_contDiff (cx_contDiff cubicSpline_mem_realTests.1) _)
    (fun a => translate_hasCompactSupport (cx_hasCompactSupport cubicSpline_mem_realTests.2) _)

/-- The quadratic charge dominates `(97/2) m²`. -/
theorem le_resolventIndexCharge (m : ℕ) : (97 / 2 : ℝ) * (m : ℝ) ^ 2 ≤ resolventIndexCharge m := by
  rw [resolventIndexCharge]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith

/-- **Index bound by energy.** On finite critical energy, `κ(K_ζ)² ≤ 2 E_crit / 97`. -/
theorem negIndex_zetaKernel_le_of_energy (hE : xiCriticalSourceEnergy ≠ ⊤) :
    negIndex zetaKernel ≤ ⌊Real.sqrt (2 * xiCriticalSourceEnergy.toReal / 97)⌋₊ := by
  classical
  rw [negIndex_le_iff]
  intro n x
  set m := hermNegIndex (gram zetaKernel x)
  have hprice := resolventIndexCharge_gram_zetaKernel_le x
  have hreal : resolventIndexCharge m ≤ xiCriticalSourceEnergy.toReal := by
    have := ENNReal.toReal_mono hE hprice
    rw [ENNReal.toReal_ofReal'] at this
    exact (le_max_left _ _).trans this
  have hm2 : (m : ℝ) ^ 2 ≤ 2 * xiCriticalSourceEnergy.toReal / 97 := by
    have := (le_resolventIndexCharge m).trans hreal
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hms : (m : ℝ) ≤ Real.sqrt (2 * xiCriticalSourceEnergy.toReal / 97) :=
    (le_abs_self _).trans (Real.abs_le_sqrt hm2)
  exact_mod_cast Nat.le_floor hms

/-- **RH as an energy threshold.** -/
theorem riemannHypothesis_tfae_energy :
    [RiemannHypothesis,
      negIndex zetaKernel = 0,
      xiCriticalSourceEnergy ≤ ENNReal.ofReal quadraticExclusionQuantum].TFAE := by
  tfae_have 1 ↔ 2 := riemannHypothesis_iff_negIndex_zetaKernel_eq_zero
  tfae_have 1 ↔ 3 := riemannHypothesis_iff_criticalEnergy_le_quantum
  tfae_finish

end GaloisForLFunctions.HeckeKreinToeplitz
