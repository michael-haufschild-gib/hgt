import GaloisForLFunctions.RHTower.Sieve.Section4ExceptionalCofactor
import GaloisForLFunctions.RHTower.Sieve.CofactorLowFreqBound

/-!
# The cofactor of a ladder step on the exceptional annulus

`Sieve/Section4ExceptionalCofactor.setIntegral_normSq_logPoly_shortExceptionalOn_le` gives the
Halász–Montgomery mean square of an arbitrary coefficient sequence over the exceptional set of a
part of the window.  Here it is specialised to the Möbius coefficient on a cofactor block of the
long ladder, and every quantity that depends on the step is replaced by a majorant that does not —
the step's cofactor length by the top length divided by the step's left endpoint, the two
Halász–Montgomery constants by parameters.  This is the shape the annulus sum consumes.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The cofactor of a long ladder step over the exceptional annulus.** -/
theorem setIntegral_normSq_cofactor_annulus_le {B : Finset ℕ} {B₁ NA m : ℕ}
    {RQ ηQ W w₀ VP Cw Ej : ℝ} (hRQ : 1 ≤ RQ) (hηQ : 0 ≤ ηQ) (k : ℕ)
    (hBprime : ∀ p ∈ B, p.Prime) (hB : B ⊆ Finset.Icc 1 NA) (hNA : 1 ≤ NA)
    (hm : 1 ≤ m) (hW : 0 ≤ W) (hVP : 0 < VP)
    (hND : 1 ≤ ⌊(B₁ : ℝ) / (RQ * (1 + ηQ) ^ k)⌋₊)
    (hCw : ((Nat.log 2 ⌊(B₁ : ℝ) / (RQ * (1 + ηQ) ^ k)⌋₊ : ℝ) + 1)
             * (214 * Real.sqrt (2 * (2 * Real.pi * W)))
           + 3072 * ((⌊(B₁ : ℝ) / (RQ * (1 + ηQ) ^ k)⌋₊ : ℕ) : ℝ) ≤ Cw)
    (hEj : 2 * (((2 * Real.pi * W)
              + 4 * ((NA ^ m : ℕ) : ℝ) * (1 + Real.log ((NA ^ m : ℕ) : ℝ)))
            * ((m : ℝ) ^ m * (B.card : ℝ) ^ m)) / VP ^ (2 * m) ≤ Ej) :
    (∫ w in shortExceptionalOn (windowAnnulus w₀ W) B VP,
        ‖logPoly moebiusCoeff (geomCofactorBlockAt 1 B₁ RQ ηQ k) w‖ ^ (2 : ℕ))
      ≤ (2 * Real.pi)⁻¹ * (2 * ((B₁ : ℝ) / (RQ * (1 + ηQ) ^ k)) + Cw * Ej)
          * ((B₁ : ℝ) / (RQ * (1 + ηQ) ^ k)) := by
  classical
  set ND : ℕ := ⌊(B₁ : ℝ) / (RQ * (1 + ηQ) ^ k)⌋₊ with hNDdef
  have hbase : (0 : ℝ) < RQ * (1 + ηQ) ^ k := by
    have : (0 : ℝ) < RQ := by linarith
    positivity
  have hDeq : geomCofactorBlockAt 1 B₁ RQ ηQ k = Finset.Icc 1 ND :=
    geomCofactorBlockAt_one_eq hRQ hηQ k
  have hDsub : geomCofactorBlockAt 1 B₁ RQ ηQ k ⊆ Finset.Icc 1 ND := by rw [hDeq]
  have hDcard : ((geomCofactorBlockAt 1 B₁ RQ ηQ k).card : ℝ) = (ND : ℝ) := by
    rw [hDeq, Nat.card_Icc]
    simp
  have hSs : windowAnnulus w₀ W ⊆ Set.Icc (-W) W := windowAnnulus_subset w₀ W
  have hbound := setIntegral_normSq_logPoly_shortExceptionalOn_le moebiusCoeff
    (B := B) (D := geomCofactorBlockAt 1 B₁ RQ ηQ k) (NA := NA) (ND := ND) (k := m)
    hBprime hB hND hDsub hm hW hVP (Ω := 1) zero_le_one norm_moebiusCoeff_le_one hSs
  refine hbound.trans ?_
  rw [hDcard]
  -- the step's cofactor length against the top length
  have hNDle : (ND : ℝ) ≤ (B₁ : ℝ) / (RQ * (1 + ηQ) ^ k) := Nat.floor_le (by positivity)
  have hND0 : (0 : ℝ) ≤ (ND : ℝ) := Nat.cast_nonneg _
  set Cwk : ℝ := ((Nat.log 2 ND : ℝ) + 1) * (214 * Real.sqrt (2 * (2 * Real.pi * W)))
      + 3072 * (ND : ℝ) with hCwk
  set Ejk : ℝ := 2 * (((2 * Real.pi * W)
              + 4 * ((NA ^ m : ℕ) : ℝ) * (1 + Real.log ((NA ^ m : ℕ) : ℝ)))
            * ((m : ℝ) ^ m * (B.card : ℝ) ^ m)) / VP ^ (2 * m) with hEjk
  have hCwk0 : (0 : ℝ) ≤ Cwk := by
    rw [hCwk]
    have h1 : (0 : ℝ) ≤ (Nat.log 2 ND : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ Real.sqrt (2 * (2 * Real.pi * W)) := Real.sqrt_nonneg _
    nlinarith [h1, h2, hND0]
  have hNApow : (1 : ℝ) ≤ ((NA ^ m : ℕ) : ℝ) := by
    have : 1 ≤ NA ^ m := Nat.one_le_pow _ _ hNA
    exact_mod_cast this
  have hEjk0 : (0 : ℝ) ≤ Ejk := by
    rw [hEjk]
    have hlog : (0 : ℝ) ≤ Real.log ((NA ^ m : ℕ) : ℝ) := Real.log_nonneg hNApow
    have hpi : (0 : ℝ) < 2 * Real.pi * W + 4 * ((NA ^ m : ℕ) : ℝ) * (1 + Real.log ((NA ^ m : ℕ) : ℝ)) := by
      have h1 : (0 : ℝ) ≤ 2 * Real.pi * W := by positivity
      nlinarith [hNApow, hlog]
    have h2 : (0 : ℝ) ≤ (m : ℝ) ^ m * (B.card : ℝ) ^ m := by positivity
    have h3 : (0 : ℝ) < VP ^ (2 * m) := by positivity
    have h4 : (0 : ℝ) ≤ 2 * ((2 * Real.pi * W
        + 4 * ((NA ^ m : ℕ) : ℝ) * (1 + Real.log ((NA ^ m : ℕ) : ℝ)))
      * ((m : ℝ) ^ m * (B.card : ℝ) ^ m)) := by nlinarith [hpi, h2]
    positivity
  have hprod : Cwk * Ejk ≤ Cw * Ej := by
    have h1 : Cwk * Ejk ≤ Cw * Ejk := mul_le_mul_of_nonneg_right hCw hEjk0
    have h2 : Cw * Ejk ≤ Cw * Ej :=
      mul_le_mul_of_nonneg_left hEj (le_trans hCwk0 hCw)
    linarith
  have hfin : (2 * (ND : ℝ) + Cwk * Ejk) * (ND : ℝ)
      ≤ (2 * ((B₁ : ℝ) / (RQ * (1 + ηQ) ^ k)) + Cw * Ej)
        * ((B₁ : ℝ) / (RQ * (1 + ηQ) ^ k)) := by
    have hCE0 : (0 : ℝ) ≤ Cwk * Ejk := mul_nonneg hCwk0 hEjk0
    have hle : 2 * (ND : ℝ) + Cwk * Ejk
        ≤ 2 * ((B₁ : ℝ) / (RQ * (1 + ηQ) ^ k)) + Cw * Ej := by linarith
    have hnn : (0 : ℝ) ≤ 2 * (ND : ℝ) + Cwk * Ejk := by linarith
    exact mul_le_mul hle hNDle hND0 (by linarith)
  have hpi0 : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  calc (2 * Real.pi)⁻¹ * ((2 * (ND : ℝ) + Cwk * Ejk) * ((1 : ℝ) ^ (2 : ℕ) * (ND : ℝ)))
      = (2 * Real.pi)⁻¹ * ((2 * (ND : ℝ) + Cwk * Ejk) * (ND : ℝ)) := by ring
    _ ≤ (2 * Real.pi)⁻¹ * ((2 * ((B₁ : ℝ) / (RQ * (1 + ηQ) ^ k)) + Cw * Ej)
          * ((B₁ : ℝ) / (RQ * (1 + ηQ) ^ k))) := by
        exact mul_le_mul_of_nonneg_left hfin hpi0
    _ = (2 * Real.pi)⁻¹ * (2 * ((B₁ : ℝ) / (RQ * (1 + ηQ) ^ k)) + Cw * Ej)
          * ((B₁ : ℝ) / (RQ * (1 + ηQ) ^ k)) := by ring

end

end RHTower.Sieve
