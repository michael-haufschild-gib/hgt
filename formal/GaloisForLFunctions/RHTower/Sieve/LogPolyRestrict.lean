import GaloisForLFunctions.RHTower.Sieve.LogPolyDirPoly
import GaloisForLFunctions.RHTower.Sieve.LadderProductDefect

/-!
# Gallagher polynomials over a subset, as Dirichlet polynomials

The ladder of `Sieve/JointLadderProduct` is written in the Gallagher variable `w` and its factors
sum over arbitrary finite subsets of an initial segment.  The §4 machinery — the mean value theorem,
the level-set bound of Lemma 2.5 and the Halász–Montgomery bound of Lemma 2.6 — is stated in the
Dirichlet variable `t = 2πw` for a polynomial indexed by `Fin N`.

This module supplies the two bridges: extending a coefficient by zero off its support, and the
change of variables on a symmetric window.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- A coefficient extended by zero off a finite support. -/
def restrictCoeff (S : Finset ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ := if n ∈ S then a n else 0

theorem norm_restrictCoeff_le {S : Finset ℕ} {a : ℕ → ℂ} {Ω : ℝ} (hΩ : 0 ≤ Ω)
    (ha : ∀ n, ‖a n‖ ≤ Ω) (n : ℕ) : ‖restrictCoeff S a n‖ ≤ Ω := by
  rw [restrictCoeff]
  by_cases h : n ∈ S
  · rw [if_pos h]; exact ha n
  · rw [if_neg h]; simpa using hΩ

/-- Extending by zero does not change the polynomial. -/
theorem logPoly_restrictCoeff (a : ℕ → ℂ) {S T : Finset ℕ} (hST : S ⊆ T) (w : ℝ) :
    logPoly (restrictCoeff S a) T w = logPoly a S w := by
  classical
  rw [logPoly, logPoly]
  rw [← Finset.sum_filter_add_sum_filter_not T (fun n => n ∈ S)]
  have hfil : T.filter (fun n => n ∈ S) = S := by
    ext n
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hST h, h⟩⟩
  have hzero : (∑ n ∈ T.filter (fun n => ¬ n ∈ S),
      restrictCoeff S a n * Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ)
        * Complex.I)) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [restrictCoeff, if_neg (Finset.mem_filter.1 hn).2, zero_mul]
  rw [hfil, hzero, add_zero]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [restrictCoeff, if_pos hn]

/-- The Gallagher polynomial over a subset of an initial segment is a Dirichlet polynomial. -/
theorem logPoly_subset_eq_dirPoly (a : ℕ → ℂ) {S : Finset ℕ} {N : ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (w : ℝ) :
    logPoly a S w
      = dirPoly N (fun n : Fin N => restrictCoeff S a ((n : ℕ) + 1)) (2 * Real.pi * w) := by
  rw [← logPoly_restrictCoeff a hS w, logPoly_eq_dirPoly]

/-- The prime block polynomial is a Gallagher polynomial with Möbius coefficients. -/
theorem primeBlockPoly_eq_logPoly (B : Finset ℕ) (w : ℝ) :
    primeBlockPoly B w = logPoly moebiusCoeff B w := by
  rw [primeBlockPoly, logPoly]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [moebiusPhase, moebiusCoeff, unitLogPhase]

/-! ## The change of variables -/

/-- **The frequency scaling on a symmetric window.** -/
theorem integral_Icc_comp_mul_left (g : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W) :
    (∫ w in Set.Icc (-W) W, g (2 * Real.pi * w))
      = (2 * Real.pi)⁻¹ * ∫ t in Set.Icc (-(2 * Real.pi * W)) (2 * Real.pi * W), g t := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hle : -W ≤ W := by linarith
  have hstep : (∫ w in Set.Icc (-W) W, g (2 * Real.pi * w))
      = ∫ w in (-W : ℝ)..W, g (2 * Real.pi * w) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  rw [hstep, intervalIntegral.integral_comp_mul_left g (ne_of_gt hpi)]
  have hsub : (∫ t in (2 * Real.pi * -W : ℝ)..(2 * Real.pi * W), g t)
      = ∫ t in Set.Icc (-(2 * Real.pi * W)) (2 * Real.pi * W), g t := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by nlinarith : -(2 * Real.pi * W) ≤ 2 * Real.pi * W)]
    congr 1
    ring
  rw [hsub, smul_eq_mul]

/-- **The product mean square of two Gallagher polynomials over subsets, in the Dirichlet
variable.** -/
theorem integral_Icc_normSq_mul_logPoly_eq (a b : ℕ → ℂ) {S D : Finset ℕ} {NA NB : ℕ}
    (hS : S ⊆ Finset.Icc 1 NA) (hD : D ⊆ Finset.Icc 1 NB) {W : ℝ} (hW : 0 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a S w‖ ^ 2 * ‖logPoly b D w‖ ^ 2)
      = (2 * Real.pi)⁻¹ * ∫ t in Set.Icc (-(2 * Real.pi * W)) (2 * Real.pi * W),
          ‖dirPoly NA (fun n : Fin NA => restrictCoeff S a ((n : ℕ) + 1)) t‖ ^ 2
            * ‖dirPoly NB (fun n : Fin NB => restrictCoeff D b ((n : ℕ) + 1)) t‖ ^ 2 := by
  set g : ℝ → ℝ := fun t =>
    ‖dirPoly NA (fun n : Fin NA => restrictCoeff S a ((n : ℕ) + 1)) t‖ ^ 2
      * ‖dirPoly NB (fun n : Fin NB => restrictCoeff D b ((n : ℕ) + 1)) t‖ ^ 2 with hg
  have hpt : ∀ w : ℝ, ‖logPoly a S w‖ ^ 2 * ‖logPoly b D w‖ ^ 2 = g (2 * Real.pi * w) := by
    intro w
    rw [hg, logPoly_subset_eq_dirPoly a hS w, logPoly_subset_eq_dirPoly b hD w]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => hpt w]
  exact integral_Icc_comp_mul_left g hW

end

end RHTower.Sieve
