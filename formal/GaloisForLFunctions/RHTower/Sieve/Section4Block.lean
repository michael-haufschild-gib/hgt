import GaloisForLFunctions.RHTower.Sieve.LogPolyRestrict
import GaloisForLFunctions.RHTower.Sieve.Section4Core
import GaloisForLFunctions.RHTower.Sieve.PlainKernelMass
import GaloisForLFunctions.RHTower.Sieve.DirichletPowerMeasure

/-!
# One block of exposé §4, end to end

The §4 estimate for a single step of the ladder: a short prime polynomial times a cofactor
polynomial, integrated over a symmetric window in the Gallagher variable.  Off the exceptional set
the prime polynomial has cancellation and the mean value theorem (Lemma 2.4) finishes; on the
exceptional set the prime polynomial is bounded trivially and Halász–Montgomery (Lemma 2.6) bounds
the cofactor's mean square in terms of the *measure* of that set, which Lemma 2.5 controls.

Every constant is explicit.  The three inputs are corpus theorems:

* `Sieve/Section4Core.section4_product_bound_mvt` — the split with the mean value theorem;
* `Sieve/PlainKernelMass.setIntegral_normSq_dirPoly_le_explicit` — Lemma 2.6;
* `Sieve/PrimePowerSupport.volume_largeValues_pow_symm_le_of_prime_support` — Lemma 2.5.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The coefficient of a Gallagher polynomial over a subset, as a `Fin`-indexed family. -/
def finCoeff (S : Finset ℕ) (a : ℕ → ℂ) (N : ℕ) : Fin N → ℂ :=
  fun n => restrictCoeff S a ((n : ℕ) + 1)

/-- The exceptional set of a block, in the Dirichlet variable. -/
def blockExceptional (S : Finset ℕ) (a : ℕ → ℂ) (NA : ℕ) (T V : ℝ) : Set ℝ :=
  {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly NA (finCoeff S a NA) t‖}

theorem measurableSet_blockExceptional (S : Finset ℕ) (a : ℕ → ℂ) (NA : ℕ) (T V : ℝ) :
    MeasurableSet (blockExceptional S a NA T V) :=
  measurableSet_Icc.inter
    (measurableSet_le measurable_const ((continuous_dirPoly NA (finCoeff S a NA)).norm).measurable)

theorem blockExceptional_subset (S : Finset ℕ) (a : ℕ → ℂ) (NA : ℕ) (T V : ℝ) :
    blockExceptional S a NA T V ⊆ Set.Icc (-T) T := fun _ ht => ht.1

/-- **The §4 estimate for one block, with the exceptional measure as a parameter.** -/
theorem section4_block_bound (a b : ℕ → ℂ) {S D : Finset ℕ} {NA NB : ℕ}
    (hS : S ⊆ Finset.Icc 1 NA) (hD : D ⊆ Finset.Icc 1 NB) (hNB : 1 ≤ NB)
    {W V Bf EV : ℝ} (hW : 0 ≤ W)
    (hBf : ∀ t : ℝ, ‖dirPoly NA (finCoeff S a NA) t‖ ≤ Bf)
    (hEV : volume.real (blockExceptional S a NA (2 * Real.pi * W) V) ≤ EV) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a S w‖ ^ 2 * ‖logPoly b D w‖ ^ 2)
      ≤ (2 * Real.pi)⁻¹
        * (V ^ 2 * (2 * (((2 * Real.pi * W) + 4 * (NB : ℝ) * (1 + Real.log NB))
              * ∑ n : Fin NB, ‖finCoeff D b NB n‖ ^ 2))
          + Bf ^ 2 * ((2 * (NB : ℝ)
              + (((Nat.log 2 NB : ℝ) + 1) * (214 * Real.sqrt (2 * (2 * Real.pi * W)))
                  + 3072 * (NB : ℝ)) * EV) * ∑ n : Fin NB, ‖finCoeff D b NB n‖ ^ 2)) := by
  classical
  set T : ℝ := 2 * Real.pi * W with hT
  have hT0 : (0 : ℝ) ≤ T := by rw [hT]; positivity
  set cA : Fin NA → ℂ := finCoeff S a NA with hcA
  set cB : Fin NB → ℂ := finCoeff D b NB with hcB
  set EB : ℝ := ∑ n : Fin NB, ‖cB n‖ ^ 2 with hEB
  have hEB0 : (0 : ℝ) ≤ EB := Finset.sum_nonneg fun n _ => by positivity
  -- Halász–Montgomery on the exceptional set
  have hHM' := setIntegral_normSq_dirPoly_le_explicit (N := NB) hNB cB (T := T)
    (measurableSet_blockExceptional S a NA T V) (blockExceptional_subset S a NA T V)
  have hvol : (0 : ℝ) ≤ volume.real (blockExceptional S a NA T V) := ENNReal.toReal_nonneg
  have hcoefpos : (0 : ℝ) ≤ ((Nat.log 2 NB : ℝ) + 1) * (214 * Real.sqrt (2 * T))
      + 3072 * (NB : ℝ) := by
    have h1 : (0 : ℝ) ≤ (Nat.log 2 NB : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ Real.sqrt (2 * T) := Real.sqrt_nonneg _
    have h3 : (0 : ℝ) ≤ (NB : ℝ) := Nat.cast_nonneg _
    nlinarith [h1, h2, h3]
  have hA₂ : (∫ t in Set.Icc (-T) T ∩ {t : ℝ | V ≤ ‖dirPoly NA cA t‖}, ‖dirPoly NB cB t‖ ^ 2)
      ≤ (2 * (NB : ℝ)
          + (((Nat.log 2 NB : ℝ) + 1) * (214 * Real.sqrt (2 * T)) + 3072 * (NB : ℝ)) * EV)
        * EB := by
    refine hHM'.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hEB0
    have := mul_le_mul_of_nonneg_left hEV hcoefpos
    linarith
  -- the §4 split
  have hcore := section4_product_bound_mvt NA NB cA cB (T := T) (V := V) (Bf := Bf) hT0 hBf hA₂
  -- change of variables
  rw [integral_Icc_normSq_mul_logPoly_eq a b hS hD hW]
  exact mul_le_mul_of_nonneg_left hcore (by positivity)

end

end RHTower.Sieve
