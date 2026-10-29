import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTouchingCrossMatrixHasAUniformErrorBudget

/-!
# The actual archimedean matrix through touching

The internal integer log gaps exceed `1/N`. At every width at most `1/N`,
the atom mass Gram is diagonal and the archimedean cross entries retain their
separated formula. The literal prime pairing remains in the identity; no
non-ratio arithmetic term is discarded.
-/

noncomputable section

open MeasureTheory Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open ArithmeticLorentzianGeometry SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory
open _root_.RHTower (archLevyDensity gammaHardyPhaseRate levyEnergy)

/-- Internal atom supports remain disjoint at every ratio up to one. -/
theorem integral_atom_mul_atom_at_touching {g : ℝ → ℝ} {w : ℝ} {N m n : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w ≤ 1 / (N : ℝ))
    (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) :
    (∫ u, atom g m u * atom g n u) = if m = n then (∫ u, g u ^ 2) else 0 := by
  by_cases hmn : m = n
  · subst n
    simp only [ite_true, atom, ← pow_two]
    exact integral_sub_right_eq_self (fun u => g u ^ 2) (Real.log m)
  · rw [if_neg hmn]
    have hgap := hw.trans_lt (inv_horizon_lt_integer_log_gap hm hn hmn)
    apply integral_eq_zero_of_ae
    filter_upwards [] with u
    change atom g m u * atom g n u = 0
    by_cases hmu : u - Real.log m ∈ Set.Icc 0 w
    · have hnu : u - Real.log n ∉ Set.Icc 0 w := by
        intro hnu
        have hle : |Real.log n - Real.log m| ≤ w := by
          rw [abs_le]
          constructor <;> linarith only [hmu.1, hmu.2, hnu.1, hnu.2]
        exact (not_lt_of_ge hle) hgap
      simp only [atom, hsupp _ hnu, mul_zero]
    · simp only [atom, hsupp _ hmu, zero_mul]

/-- The actual mixed Lévy integrand keeps its translated cross formula through touching. -/
theorem levyMixed_atom_pair_at_touching {g : ℝ → ℝ} {w : ℝ} {N m n : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w ≤ 1 / (N : ℝ))
    (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) (hmn : m < n) {y : ℝ} (hy : 0 < y) :
    levyMixed (atom g m) (atom g n) y =
      -(archLevyDensity y * bumpAutocorr g (y - (Real.log n - Real.log m))) := by
  have hlog : 0 < Real.log n - Real.log m := sub_pos.mpr (Real.log_lt_log
    (by exact_mod_cast (mem_Icc.mp hm).1) (by exact_mod_cast hmn))
  have hsep : w < Real.log n - Real.log m := by
    have h := hw.trans_lt (inv_horizon_lt_integer_log_gap hm hn (ne_of_lt hmn))
    rwa [abs_of_pos hlog] at h
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

/-- The exact integrated cross entry uses only the actual internal spacing. -/
theorem integral_levyMixed_atom_pair_at_touching {g : ℝ → ℝ} {w : ℝ} {N m n : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w ≤ 1 / (N : ℝ))
    (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) (hmn : m < n) :
    (∫ y in Set.Ioi 0, levyMixed (atom g m) (atom g n) y) =
      -atomCrossTerm g (Real.log n - Real.log m) := by
  rw [atomCrossTerm, ← integral_neg]
  exact setIntegral_congr_fun measurableSet_Ioi fun y hy =>
    levyMixed_atom_pair_at_touching hsupp hw hm hn hmn hy

/-- Restoring the literal prime pairing leaves the exact archimedean entry at touching. -/
theorem markovPair_add_primePair_at_touching {g : ℝ → ℝ} {w : ℝ} {N m n : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w ≤ 1 / (N : ℝ))
    (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) :
    markovPair (atom g m) (atom g n) + primePair (atom g m) (atom g n) =
      if m = n then 2 * gammaHardyPhaseRate 0 * (∫ u, g u ^ 2) + levyEnergy g
      else -atomCrossTerm g |Real.log n - Real.log m| := by
  have hordered : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, a < b →
      markovPair (atom g a) (atom g b) + primePair (atom g a) (atom g b) =
        -atomCrossTerm g (Real.log b - Real.log a) := by
    intro a ha b hb hab
    rw [markovPair, sub_add_cancel, integral_atom_mul_atom_at_touching hsupp hw ha hb,
      if_neg (ne_of_lt hab), mul_zero, zero_add,
      integral_levyMixed_atom_pair_at_touching hsupp hw ha hb hab]
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · rw [if_neg (ne_of_lt hmn), hordered m hm n hn hmn,
      abs_of_pos (sub_pos.mpr (Real.log_lt_log
        (by exact_mod_cast (mem_Icc.mp hm).1) (by exact_mod_cast hmn)))]
  · subst n
    have hlevy : (∫ y in Set.Ioi 0, levyMixed (atom g m) (atom g m) y) = levyEnergy g := by
      simp only [levyMixed, ← sq]
      change levyEnergy (atom g m) = levyEnergy g
      exact levyEnergy_translate (Real.log m)
    rw [if_pos rfl, markovPair, sub_add_cancel,
      integral_atom_mul_atom_at_touching hsupp hw hm hm, if_pos rfl, hlevy]
  · rw [if_neg (ne_of_gt hnm), markovPair_comm, primePair_comm, hordered n hn m hm hnm,
      abs_sub_comm, abs_of_pos (sub_pos.mpr (Real.log_lt_log
        (by exact_mod_cast (mem_Icc.mp hn).1) (by exact_mod_cast hnm)))]

/-- The literal complete matrix through touching retains every prime pairing. -/
theorem fullWeilHorizonMatrix_apply_at_touching {g : ℝ → ℝ} {w : ℝ} {N : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w ≤ 1 / (N : ℝ))
    (n j : PrimeHorizonIndex N) :
    fullWeilHorizonMatrix g N n j =
      (if (n : ℕ) = j then 2 * gammaHardyPhaseRate 0 * (∫ u, g u ^ 2) + levyEnergy g
       else -atomCrossTerm g |Real.log (j : ℕ) - Real.log (n : ℕ)|) -
      primePair (atom g n) (atom g j) +
      ((∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2))) *
        arithmeticPoleKernel n j := by
  have hmarkov := markovPair_add_primePair_at_touching hsupp hw n.property j.property
  have heq : markovPair (atom g n) (atom g j) =
      (if (n : ℕ) = j then 2 * gammaHardyPhaseRate 0 * (∫ u, g u ^ 2) + levyEnergy g
       else -atomCrossTerm g |Real.log (j : ℕ) - Real.log (n : ℕ)|) -
        primePair (atom g n) (atom g j) := by linarith only [hmarkov]
  simp only [fullWeilHorizonMatrix, atomicWeilGram, atomicMarkovGram, Matrix.of_apply,
    primeHorizonFinEquiv_val_add_one, heq,
    atomPoleRow_primeHorizonFinEquiv_zero, atomPoleRow_primeHorizonFinEquiv_one,
    arithmeticPoleKernel]
  ring

/-- Atom-mass normalization preserves the full prime pairing at the endpoint ratio. -/
theorem normalizedFullWeilHorizonMatrix_apply_at_touching
    {g : ℝ → ℝ} {w : ℝ} {N : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w ≤ 1 / (N : ℝ))
    (hG : (∫ u, g u ^ 2) ≠ 0) (n j : PrimeHorizonIndex N) :
    normalizedFullWeilHorizonMatrix g N n j =
      (if (n : ℕ) = j then 2 * gammaHardyPhaseRate 0 + levyEnergy g / (∫ u, g u ^ 2)
       else -atomCrossTerm g |Real.log (j : ℕ) - Real.log (n : ℕ)| / (∫ u, g u ^ 2)) -
      primePair (atom g n) (atom g j) / (∫ u, g u ^ 2) +
      ((∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2)) /
        (∫ u, g u ^ 2)) * arithmeticPoleKernel n j := by
  rw [normalizedFullWeilHorizonMatrix, fullWeilHorizonMatrix_apply_at_touching hsupp hw]
  split_ifs <;> field_simp [hG]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.markovPair_add_primePair_at_touching

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.normalizedFullWeilHorizonMatrix_apply_at_touching
