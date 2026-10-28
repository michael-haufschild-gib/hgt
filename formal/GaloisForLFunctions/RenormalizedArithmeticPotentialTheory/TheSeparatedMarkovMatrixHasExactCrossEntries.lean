import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSeparatedAtomPairingsAreThePrimeKernel
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanPairingOfTwoAtoms

/-!
# Exact Markov entries of separated logarithmic atoms

The common self-energy forms the diagonal. Every off-diagonal archimedean
entry is the negative of the literal positive-lag cross integral, and every
prime entry is the atom mass times the integer prime kernel.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticLorentzianGeometry ArithmeticElectrostatics
  ArithmeticEffectivityTheory SpacingScaleHarmonicAnalysis

variable {g : ℝ → ℝ} {w : ℝ}

/-- Translation reduces a positive logarithmic atom pair to its center lag. -/
theorem levyMixed_atom_pair_of_lt {N m n : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w < atomSpacing N)
    (hm : m ∈ Icc 1 N) (hmn : m < n) {y : ℝ} (hy : 0 < y) :
    levyMixed (atom g m) (atom g n) y =
      -(archLevyDensity y * bumpAutocorr g (y - (Real.log n - Real.log m))) := by
  have hsep : w < Real.log n - Real.log m :=
    hw.trans_le (atomSpacing_le_log_sub (mem_Icc.mp hm).1 (mem_Icc.mp hm).2 hmn)
  have htranslate : levyMixed (atom g m) (atom g n) y =
      levyMixed g (fun u => g (u - (Real.log n - Real.log m))) y := by
    unfold levyMixed atom
    congr 1
    rw [← integral_sub_right_eq_self
      (fun u => (g u - g (u + y)) *
        (g (u - (Real.log n - Real.log m)) -
          g (u + y - (Real.log n - Real.log m)))) (Real.log m)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by ring_nf
  rw [htranslate, levyMixed_atom_shift hsupp hsep hy]

/-- The mixed Levy energy of distinct ordered atoms is one negative cross integral. -/
theorem integral_levyMixed_atom_pair_of_lt {N m n : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w < atomSpacing N)
    (hm : m ∈ Icc 1 N) (hmn : m < n) :
    (∫ y in Set.Ioi 0, levyMixed (atom g m) (atom g n) y) =
      -atomCrossTerm g (Real.log n - Real.log m) := by
  rw [atomCrossTerm, ← integral_neg]
  exact setIntegral_congr_fun measurableSet_Ioi fun y hy =>
    levyMixed_atom_pair_of_lt hsupp hw hm hmn hy

private theorem markovPair_atom_of_lt {N m n : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w < atomSpacing N)
    (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) (hmn : m < n) :
    markovPair (atom g m) (atom g n) =
      -atomCrossTerm g (Real.log n - Real.log m) -
        (∫ u, g u ^ 2) * weilPrimeKernel m n := by
  rw [markovPair, integral_atom_mul_atom hsupp hw hm hn, if_neg (ne_of_lt hmn),
    mul_zero, zero_add, integral_levyMixed_atom_pair_of_lt hsupp hw hm hmn,
    primePair_atom_eq hsupp hw hm hn]

/-- Exact separated Markov entries, with diagonal self-energy and full prime kernel. -/
theorem markovPair_atom_eq {N m n : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w < atomSpacing N)
    (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) :
    markovPair (atom g m) (atom g n) =
      (if m = n then 2 * gammaHardyPhaseRate 0 * (∫ u, g u ^ 2) + levyEnergy g
       else -atomCrossTerm g |Real.log n - Real.log m|) -
        (∫ u, g u ^ 2) * weilPrimeKernel m n := by
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · rw [if_neg (ne_of_lt hmn),
      abs_of_pos (sub_pos.mpr (Real.log_lt_log
        (by exact_mod_cast (mem_Icc.mp hm).1) (by exact_mod_cast hmn))),
      markovPair_atom_of_lt hsupp hw hm hn hmn]
  · subst n
    have hlevy : (∫ y in Set.Ioi 0, levyMixed (atom g m) (atom g m) y) = levyEnergy g := by
      simp only [levyMixed, ← sq]
      change levyEnergy (atom g m) = levyEnergy g
      exact levyEnergy_translate (Real.log m)
    rw [if_pos rfl, markovPair, integral_atom_mul_atom hsupp hw hm hm, if_pos rfl,
      hlevy, primePair_atom_eq hsupp hw hm hm]
  · rw [if_neg (ne_of_gt hnm), markovPair_comm,
      markovPair_atom_of_lt hsupp hw hn hm hnm,
      abs_sub_comm, abs_of_pos (sub_pos.mpr (Real.log_lt_log
        (by exact_mod_cast (mem_Icc.mp hn).1) (by exact_mod_cast hnm)))]
    congr 1
    exact congrArg (fun z => (∫ u, g u ^ 2) * z) (weilPrimeKernel_comm n m)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

