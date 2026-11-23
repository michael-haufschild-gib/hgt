import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.HeightSpectrum
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.NativeKnots

/-! # First active coordinate of a physical omission -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

def FirstOccupied (v : MissingWave) (j : ℕ) : Prop := (∀ k < j, v.val (number k) = 0) ∧ v.val (number j) ≠ 0

theorem first_move_iff_first_occupied (v : MissingWave) (j : ℕ) : FirstMove (missingSpectrum v) j ↔ FirstOccupied v j := by
  have forward (i : ℕ) (hi : FirstMove (missingSpectrum v) i) : FirstOccupied v i := by
    refine ⟨fun k hk => (native_level_occurs_iff v k).mp ⟨k,hi.1 k hk⟩,?_⟩
    intro hzero
    obtain ⟨n,hn⟩ := (native_level_occurs_iff v i).mpr hzero
    rcases lt_trichotomy n i with h | h | h
    · exact (occupationWeight_strictAnti h).ne (hn.symm.trans (hi.1 n h))
    · exact hi.2 (h ▸ hn)
    · exact (occupationWeight_strictAnti h).not_ge (hn.symm.trans_le (missingSpectrum v n).property.2)
  refine ⟨forward j,fun hj => ?_⟩
  obtain ⟨i,hi⟩ := physical_first_move (missingSpectrum_physical v)
  have h := forward i hi
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact False.elim (h.2 (hj.1 i hlt))
  · exact heq ▸ hi
  · exact False.elim (hj.2 (h.1 j hgt))

/-- The cutoff inferred from an entire family of moment readings is precisely the first occupied native energy of the missing wave. -/
theorem support_passing_interval {v : MissingWave} {j : ℕ} (hj : FirstOccupied v j) :
    passingHeights (missingSpectrum v) = Ioc 0 (Real.sqrt ((j:ℝ)+1)) :=
  passing_heights_interval ((first_move_iff_first_occupied v j).mpr hj)

theorem last_height_from_support {v : MissingWave} {j : ℕ} (hj : FirstOccupied v j) :
    lastHeight (missingSpectrum v) = Real.sqrt ((j:ℝ)+1) :=
  lastHeight_of_first_move ((first_move_iff_first_occupied v j).mpr hj)

/-- A full prefix survives in its original slots exactly when the missing direction vanishes there. -/
theorem native_prefix_iff_zero_coordinates (v : MissingWave) (N : ℕ) :
    (∀ k < N, (missingSpectrum v k).val = occupationWeight k) ↔ ∀ k < N, v.val (number k) = 0 := by
  constructor
  · exact fun h k hk => (native_level_occurs_iff v k).mp ⟨k,h k hk⟩
  · intro h
    obtain ⟨j,hj⟩ := physical_first_move (missingSpectrum_physical v)
    have hN : N ≤ j := le_of_not_gt (fun hlt => ((first_move_iff_first_occupied v j).mp hj).2 (h j hlt))
    exact fun k hk => hj.1 k (hk.trans_le hN)

#print axioms first_move_iff_first_occupied
#print axioms support_passing_interval
#print axioms last_height_from_support
#print axioms native_prefix_iff_zero_coordinates

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
