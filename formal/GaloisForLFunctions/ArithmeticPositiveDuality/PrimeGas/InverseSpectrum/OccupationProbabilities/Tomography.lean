import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.PoleScans

/-! # Removing the single blind level in coherent pole tomography -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

private theorem opposite_increments (z : ℂ) : probeIncrement z 1+probeIncrement z (-1) = 2 := by
  simp [probeIncrement]
  ring

/-- All references in one mode are silent exactly at that mode's native level. -/
theorem all_references_silent_iff (v : MissingWave) (k : ℕ) :
    (∀ c, poleReading (addNative v k c) = poleReading v) ↔ poleReading v = occupationWeight k := by
  constructor
  · intro h
    by_contra hb
    have hp := ((poleReading_fixed_iff v k 1).mp (h 1)).resolve_left hb
    have hm := ((poleReading_fixed_iff v k (-1)).mp (h (-1))).resolve_left hb
    have hs := opposite_increments (v.val (number k))
    rw [hp,hm] at hs
    norm_num at hs
  · intro h c
    exact (poleReading_fixed_iff v k c).mpr (Or.inl h)

theorem blind_level_unique (v : MissingWave) {i j : ℕ}
    (hi : poleReading v = occupationWeight i) (hj : poleReading v = occupationWeight j) : i = j :=
  occupationWeight_strictAnti.injective (hi.symm.trans hj)

private theorem adjacent_reference_moves (v : MissingWave) (k : ℕ) (h : poleReading v = occupationWeight k) :
    poleReading (addNative v (k+1) 1) ≠ occupationWeight k ∨
      poleReading (addNative v (k+1) (-1)) ≠ occupationWeight k := by
  have hn : poleReading v ≠ occupationWeight (k+1) := fun he => (Nat.ne_of_lt (Nat.lt_succ_self k)) (blind_level_unique v h he)
  by_contra! hf
  have hp := ((poleReading_fixed_iff v (k+1) 1).mp (hf.1.trans h.symm)).resolve_left hn
  have hm := ((poleReading_fixed_iff v (k+1) (-1)).mp (hf.2.trans h.symm)).resolve_left hn
  have hs := opposite_increments (v.val (number (k+1)))
  rw [hp,hm] at hs
  norm_num at hs

/-- Select a scan with nonblind baseline using only the measured values. The two auxiliary references occupy the next mode. -/
noncomputable def readPoleCoordinate (a : ℝ) (bare plus minus : PoleScan) : ℂ := by
  classical
  exact if bare.base ≠ a then bare.coordinate a else if plus.base ≠ a then plus.coordinate a else minus.coordinate a

def poleCoordinate (v : MissingWave) (k : ℕ) :=
  readPoleCoordinate (occupationWeight k) (poleScan v k) (poleScan (addNative v (k+1) 1) k)
    (poleScan (addNative v (k+1) (-1)) k)

/-- Single-temperature pole measurements reconstruct the complex coordinate of an arbitrary exterior wave, in its original normalization. -/
theorem poleCoordinate_eq (v : MissingWave) (k : ℕ) : poleCoordinate v k = v.val (number k) := by
  classical
  by_cases h : poleReading v ≠ occupationWeight k
  · rw [poleCoordinate,readPoleCoordinate,if_pos (show (poleScan v k).base ≠ occupationWeight k from h)]
    exact poleScan_coordinate v k h
  · have hb := not_ne_iff.mp h
    rw [poleCoordinate,readPoleCoordinate,if_neg (show ¬(poleScan v k).base ≠ occupationWeight k from h)]
    by_cases hp : poleReading (addNative v (k+1) 1) ≠ occupationWeight k
    · rw [if_pos (show (poleScan (addNative v (k+1) 1) k).base ≠ occupationWeight k from hp),poleScan_coordinate _ _ hp,
        addNative_off v (Nat.ne_of_lt (Nat.lt_succ_self k))]
    · have hm := (adjacent_reference_moves v k hb).resolve_left hp
      rw [if_neg (show ¬(poleScan (addNative v (k+1) 1) k).base ≠ occupationWeight k from hp),poleScan_coordinate _ _ hm,
        addNative_off v (Nat.ne_of_lt (Nat.lt_succ_self k))]

theorem poleCoordinate_injective : Function.Injective poleCoordinate := by
  intro v w h
  apply Subtype.ext
  apply lp.ext
  funext n
  obtain ⟨k,rfl⟩ := number_surjective n
  simpa only [poleCoordinate_eq] using congrFun h k

#print axioms all_references_silent_iff
#print axioms blind_level_unique
#print axioms poleCoordinate_eq
#print axioms poleCoordinate_injective

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
