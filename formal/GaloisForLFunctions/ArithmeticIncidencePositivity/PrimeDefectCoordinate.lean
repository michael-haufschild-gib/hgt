import GaloisForLFunctions.ArithmeticIncidencePositivity.TranslatePairingCalculus
import GaloisForLFunctions.BiScaleUncertainty.KreinIncrementAndChordCascade

/-!
# The cost side in defect coordinates

Read through the shift defect `δ(t) = A(0) − A(t)` the cost side of the ledger changes sign:

    Σ_n (Λ(n)/√n) A(log n) = (Σ_n Λ(n)/√n) A(0) − D(F),    D(F) = Σ_n (Λ(n)/√n) δ(log n),

so an upper bound on the prime charge is a **lower bound on the atom-weighted defect**: the demand
of the ledger is that the test be sufficiently *non-invariant* under the prime shifts, measured in
the `ℓ¹` of the atoms. In this coordinate the trivial estimate is `D ≥ 0` and the demand is
`D ≥ (ℓ¹ − C) A(0)`, with `ℓ¹ = Σ_{n ≤ e^{2r}} Λ(n)/√n ≍ 2e^{r}`: the test must decorrelate at
essentially *every* prime-power lag, in the atom-weighted average — the large-aperture shape of the
obstruction.

Part of that is automatic. The chord cascade of `BiScaleUncertainty` gives `A(0)/m² ≤ δ(x₀/m)`
whenever `A(x₀) ≤ 0`, and every lag past the aperture has a vanishing double, so each shift longer
than the aperture has defect at least a quarter of the mass. The atoms above `e^{r}` carry the bulk
of the `ℓ¹` mass, so the high range is discounted unconditionally,

    Σ_{log n > r} (Λ(n)/√n) A(log n) ≤ (3/4) (Σ_{log n > r} Λ(n)/√n) A(0),

and what the ledger still needs is the remaining quarter — a statement about the arithmetic of the
shifts, not about the geometry of the test.
-/

open MeasureTheory
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

variable {F : ℝ → ℝ}

/-- The two autocorrelations of the corpus agree by definition. -/
theorem autoCorr_eq_autocorr (F : ℝ → ℝ) (t : ℝ) :
    autoCorr F t = RHTower.ArchimedeanAnomaly.autocorr F t := rfl

/-- The shift defect `δ(t) = A(0) − A(t)`. -/
def shiftDefect (F : ℝ → ℝ) (t : ℝ) : ℝ := autoCorr F 0 - autoCorr F t

/-- The atom-weighted defect functional `D(F) = Σ_n (Λ(n)/√n) δ(log n)`. -/
def primeDefect (F : ℝ → ℝ) (s : Finset ℕ) : ℝ :=
  ∑ n ∈ s, RHTower.vonMangoldtAtom n * shiftDefect F (Real.log n)

/-- The von Mangoldt atoms are nonnegative. -/
theorem vonMangoldtAtom_nonneg (n : ℕ) : 0 ≤ RHTower.vonMangoldtAtom n := by
  simp only [RHTower.vonMangoldtAtom]
  split_ifs with h
  · exact div_nonneg (ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)
  · exact le_rfl

/-- **The cost side in defect coordinates.** The prime charge is the mass times the atom `ℓ¹` norm
minus the atom-weighted defect. -/
theorem sum_atom_mul_autoCorr_eq (F : ℝ → ℝ) (s : Finset ℕ) :
    ∑ n ∈ s, RHTower.vonMangoldtAtom n * autoCorr F (Real.log n)
      = (∑ n ∈ s, RHTower.vonMangoldtAtom n) * autoCorr F 0 - primeDefect F s := by
  rw [primeDefect, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [shiftDefect]
  ring

/-- An upper bound on the prime charge is exactly a lower bound on the atom-weighted defect. -/
theorem sum_atom_mul_autoCorr_le_iff (F : ℝ → ℝ) (s : Finset ℕ) (C : ℝ) :
    (∑ n ∈ s, RHTower.vonMangoldtAtom n * autoCorr F (Real.log n)) ≤ C * autoCorr F 0
      ↔ ((∑ n ∈ s, RHTower.vonMangoldtAtom n) - C) * autoCorr F 0 ≤ primeDefect F s := by
  rw [sum_atom_mul_autoCorr_eq]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **The quarter floor past the aperture.** A shift longer than the aperture has defect at least a
quarter of the mass: the double of such a shift is beyond the horizon, where the autocorrelation
vanishes, and the harmonic sub-grid bound of the chord cascade halves it back. -/
theorem quarter_le_shiftDefect {B t : ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hB : 0 ≤ B) (hsupp : ∀ x, B < |x| → F x = 0) (ht : B < t) :
    autoCorr F 0 / 4 ≤ shiftDefect F t := by
  have hzero : autoCorr F (2 * t) = 0 := by
    refine autoCorr_eq_zero_of_support hsupp ?_
    have htpos : 0 < t := lt_of_le_of_lt hB ht
    rw [abs_of_pos (by linarith)]
    linarith
  have hnonpos : RHTower.ArchimedeanAnomaly.autocorr F (2 * t) ≤ 0 := by
    rw [← autoCorr_eq_autocorr, hzero]
  have h := GaloisForLFunctions.BiScaleUncertainty.autocorr_harmonic_subgrid_ge_of_nonpos
    hFc hF hnonpos (m := 2) (by norm_num)
  have hcast : (2 * t) / ((2 : ℕ) : ℝ) = t := by
    norm_num
  rw [hcast] at h
  simp only [shiftDefect, ← autoCorr_eq_autocorr] at *
  have hm : (((2 : ℕ) : ℝ)) ^ 2 = 4 := by norm_num
  rw [hm] at h
  exact h

/-- **The high range is discounted unconditionally.** For a set of shifts all longer than the
aperture, the atom-weighted defect is at least a quarter of the atom `ℓ¹` norm times the mass. -/
theorem quarter_mul_sum_atom_le_primeDefect {B : ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (hB : 0 ≤ B) (hsupp : ∀ x, B < |x| → F x = 0) (s : Finset ℕ)
    (hhigh : ∀ n ∈ s, B < Real.log n) :
    (autoCorr F 0 / 4) * (∑ n ∈ s, RHTower.vonMangoldtAtom n) ≤ primeDefect F s := by
  rw [Finset.mul_sum, primeDefect]
  refine Finset.sum_le_sum fun n hn => ?_
  have hd := quarter_le_shiftDefect hF hFc hB hsupp (hhigh n hn)
  have ha := vonMangoldtAtom_nonneg n
  calc autoCorr F 0 / 4 * RHTower.vonMangoldtAtom n
      = RHTower.vonMangoldtAtom n * (autoCorr F 0 / 4) := by ring
    _ ≤ RHTower.vonMangoldtAtom n * shiftDefect F (Real.log n) :=
        mul_le_mul_of_nonneg_left hd ha

/-- **The three-quarter law on the high range.** The prime charge of the shifts past the aperture
is at most three quarters of what the trivial bound allows. -/
theorem sum_atom_mul_autoCorr_le_three_quarters {B : ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (hB : 0 ≤ B) (hsupp : ∀ x, B < |x| → F x = 0) (s : Finset ℕ)
    (hhigh : ∀ n ∈ s, B < Real.log n) :
    ∑ n ∈ s, RHTower.vonMangoldtAtom n * autoCorr F (Real.log n)
      ≤ (3 / 4) * (∑ n ∈ s, RHTower.vonMangoldtAtom n) * autoCorr F 0 := by
  have hkey := quarter_mul_sum_atom_le_primeDefect hF hFc hB hsupp s hhigh
  rw [sum_atom_mul_autoCorr_eq]
  nlinarith [hkey]

end GaloisForLFunctions.ArithmeticIncidencePositivity
