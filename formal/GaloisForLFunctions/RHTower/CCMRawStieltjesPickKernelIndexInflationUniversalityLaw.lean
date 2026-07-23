import GaloisForLFunctions.HTGeometry.ChamberLawPickKernel
import GaloisForLFunctions.RHTower.CCMRawStieltjesChamberIndexInflation

/-!
# Critical-Mellin actual-Pick index inflation universality

The raw critical-Mellin chamber theorem gives cofinally unbounded negative index for the scaled
Stieltjes Gram.  The generic chamber theorem separately identifies that Gram with squared boundary
height times the Pick kernel of the actual regularized Herglotz transform.  Their closure removes
the surrogate: actual Pick kernels of finite critical-Mellin apertures realize arbitrarily large
finite negative index.
-/

open scoped BigOperators ComplexConjugate Classical ComplexOrder ENNReal
open MeasureTheory Set Finset Filter Topology ArithmeticFunction

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry Matrix

/-- The actual Pick kernel of a selected critical-Mellin prime-power chamber. -/
def criticalMellinSelectedPickKernel {d : ℕ} (A : ℝ) (k : Fin d → ℕ) (y : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  chamberPickKernel (criticalMellinPolarMeasure A) (criticalMellinSelectedNodes k)
    (criticalMellinSelectedCoefficients k) y

/-- The regularized Herglotz kernel is integrable against every finite-aperture polar measure. -/
theorem integrable_regularizedHerglotzKernel_criticalMellinPolarMeasure
    (A a : ℝ) {y : ℝ} (hy : y ≠ 0) :
    Integrable (fun t : ℝ => regularizedHerglotzKernel t (upperNode a y))
      (criticalMellinPolarMeasure A) := by
  letI : IsFiniteMeasure (criticalMellinPolarMeasure A) :=
    criticalMellinPolarMeasure_isFinite A
  have hz : (upperNode a y).im ≠ 0 := by
    simpa [upperNode] using hy
  have hregularizer :
      Integrable (fun t : ℝ => (t : ℂ) / (1 + (t : ℂ) ^ 2))
        (criticalMellinPolarMeasure A) := by
    have hfun : (fun t : ℝ => (t : ℂ) / (1 + (t : ℂ) ^ 2)) =
        fun t : ℝ => ((t / (1 + t ^ 2) : ℝ) : ℂ) := by
      funext t
      push_cast
      rfl
    rw [hfun]
    have hreal : Continuous (fun t : ℝ => t / (1 + t ^ 2)) :=
      continuous_id.div₀ (continuous_const.add (continuous_id.pow 2))
        (fun t => by positivity)
    refine Integrable.of_bound (C := 1)
      (Complex.continuous_ofReal.comp hreal).aestronglyMeasurable ?_
    filter_upwards with t
    have ht : |t| ≤ 1 + t ^ 2 := by
      have habs : |t| ^ 2 = t ^ 2 := sq_abs t
      nlinarith [sq_nonneg (|t| - 1), abs_nonneg t]
    rw [Complex.norm_real, Real.norm_eq_abs]
    simpa [abs_div, abs_of_nonneg (show 0 ≤ 1 + t ^ 2 by positivity)] using
      (div_le_one (show 0 < 1 + t ^ 2 by positivity)).2 ht
  simpa only [regularizedHerglotzKernel, one_div] using
    (integrable_cauchyKernel (criticalMellinPolarMeasure A) hz).sub hregularizer

/-- The raw RHT Gram is exactly the actual Pick kernel scaled by squared boundary height. -/
theorem criticalMellinSelectedStieltjesGram_eq_smul_pickKernel
    {d : ℕ} (A : ℝ) (k : Fin d → ℕ) {y : ℝ} (hy : y ≠ 0) :
    criticalMellinSelectedStieltjesGram A k y =
      ((y : ℂ) ^ 2) • criticalMellinSelectedPickKernel A k y := by
  simpa [criticalMellinSelectedStieltjesGram, criticalMellinSelectedPickKernel] using
    totalGram_eq_smul_chamberPickKernel
      (criticalMellinPolarMeasure A) (criticalMellinSelectedNodes k)
        (criticalMellinSelectedCoefficients k) hy
        (fun l => integrable_regularizedHerglotzKernel_criticalMellinPolarMeasure
          A (criticalMellinSelectedNodes k l) hy)

/-- Every active selected prime-power packet has full negative index in the actual Pick kernel. -/
theorem criticalMellinSelectedPickKernel_chamber {d : ℕ} {A : ℝ} {k : Fin d → ℕ}
    (hk : ∀ j, IsPrimePow (k j)) (hkinj : Function.Injective k)
    (hactive : ∀ j, Real.log (k j) ≤ 2 * A) :
    (∀ᶠ y : ℝ in 𝓝[≠] 0, ∀ x : Fin d → ℂ, x ≠ 0 →
      (star x ⬝ᵥ (criticalMellinSelectedPickKernel A k y).mulVec x).re < 0) ∧
      (∀ j, criticalMellinSelectedNodes k j ∈ Ioc 0 (2 * A)) ∧
      hammingDist (signPattern (criticalMellinSelectedCoefficients k))
        (positiveChamber d) = d := by
  have hscaled := criticalMellinSelectedStieltjes_chamber hk hkinj hactive
  refine ⟨?_, hscaled.2.1, hscaled.2.2⟩
  filter_upwards [hscaled.1, self_mem_nhdsWithin] with y hy hy0
  intro x hx
  have hneg := hy x hx
  rw [criticalMellinSelectedStieltjesGram_eq_smul_pickKernel A k hy0,
    re_quadForm_smul_neg_iff _ hy0] at hneg
  exact hneg

/-- The complete finite-aperture actual Pick kernel has one negative direction per active atom. -/
theorem activeCriticalMellinPickKernel_chamber (A : ℝ) :
    (∀ᶠ y : ℝ in 𝓝[≠] 0,
      ∀ x : Fin (activeCriticalMellinAtoms A).card → ℂ, x ≠ 0 →
        (star x ⬝ᵥ
          (criticalMellinSelectedPickKernel A (activeCriticalMellinAtom A) y).mulVec x).re < 0) ∧
      hammingDist
        (signPattern (criticalMellinSelectedCoefficients (activeCriticalMellinAtom A)))
        (positiveChamber (activeCriticalMellinAtoms A).card)
        = (activeCriticalMellinAtoms A).card := by
  have h := criticalMellinSelectedPickKernel_chamber
    (fun j => activeCriticalMellinAtom_isPrimePow A j)
    (activeCriticalMellinAtom_injective A)
    (fun j => activeCriticalMellinAtom_log_le A j)
  exact ⟨h.1, h.2.2⟩

/-- **Critical-Mellin actual-Pick index inflation universality.** Actual Pick kernels of the raw
critical-Mellin source realize arbitrarily large finite negative index. -/
theorem exists_activeCriticalMellinPickKernel_chamber_grade_ge (d : ℕ) :
    ∃ A : ℝ,
      d ≤ (activeCriticalMellinAtoms A).card ∧
      hammingDist
        (signPattern (criticalMellinSelectedCoefficients (activeCriticalMellinAtom A)))
        (positiveChamber (activeCriticalMellinAtoms A).card) =
          (activeCriticalMellinAtoms A).card ∧
      (∀ᶠ y : ℝ in 𝓝[≠] 0,
        ∀ x : Fin (activeCriticalMellinAtoms A).card → ℂ, x ≠ 0 →
          (star x ⬝ᵥ
            (criticalMellinSelectedPickKernel A (activeCriticalMellinAtom A) y).mulVec x).re < 0) := by
  refine ⟨(Nat.nth Nat.Prime d : ℝ) / 2, activeCriticalMellinAtoms_card_ge d, ?_, ?_⟩
  · exact (activeCriticalMellinPickKernel_chamber _).2
  · exact (activeCriticalMellinPickKernel_chamber _).1

end RHTower
