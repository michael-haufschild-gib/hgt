import GaloisForLFunctions.RHTower.Sieve.KloostermanHybridResidueParseval

/-!
# Normalized finite-modulus Kloosterman hybrid energy
-/

open Complex MeasureTheory Set Finset

noncomputable section

namespace RHTower.Sieve

/-- Kloosterman hybrid energy over a finite modulus family, normalized by the exact cubic
Plancherel factor at each modulus. -/
def normalizedKloostermanHybridModulusEnergy
    (Q : Finset ℕ) (N : ℕ) (a : ℕ → ℕ → ℂ) (T : ℝ) : ℝ :=
  ∑ q ∈ Q,
    (∑ n : ZMod (q + 1),
      (∫ t in Set.Icc (-T) T,
        ‖kloostermanHybridTransform q N (a q) n t‖ ^ 2)) /
      (((q + 1 : ℕ) : ℝ) ^ 3)

/-- Physical unit-residue energy over the same finite modulus family. -/
def unitResidueHybridModulusEnergy
    (Q : Finset ℕ) (N : ℕ) (a : ℕ → ℕ → ℂ) (T : ℝ) : ℝ :=
  ∑ q ∈ Q, ∑ x : (ZMod (q + 1))ˣ,
    (∫ t in Set.Icc (-T) T,
      ‖physicalResidueDirichletPoly q N (a q)
        (-(x : ZMod (q + 1))) t‖ ^ 2)

/-- Exact direct-sum Parseval law across any finite family of moduli. -/
theorem normalizedKloostermanHybridModulusEnergy_eq_unitResidue
    (Q : Finset ℕ) (N : ℕ) (a : ℕ → ℕ → ℂ) (T : ℝ) :
    normalizedKloostermanHybridModulusEnergy Q N a T =
      unitResidueHybridModulusEnergy Q N a T := by
  unfold normalizedKloostermanHybridModulusEnergy unitResidueHybridModulusEnergy
  apply Finset.sum_congr rfl
  intro q hq
  rw [sum_integral_normSq_kloostermanHybridTransform_eq_unitResidueEnergy]
  field_simp

/-- Elementary finite-modulus baseline.  It is the exact scale obtained before any spectral
cancellation between moduli. -/
theorem normalizedKloostermanHybridModulusEnergy_le_baseline
    (Q : Finset ℕ) (N : ℕ) (a : ℕ → ℕ → ℂ) {T : ℝ} (hT : 1 ≤ T) :
    normalizedKloostermanHybridModulusEnergy Q N a T ≤
      ∑ q ∈ Q,
        (5 * Real.pi * Real.exp 1 * (N : ℝ) / ((q + 1 : ℕ) : ℝ) +
          5 * Real.pi * T) *
        ∑ m ∈ Finset.Icc 1 N, ‖a q m‖ ^ 2 := by
  unfold normalizedKloostermanHybridModulusEnergy
  apply Finset.sum_le_sum
  intro q hq
  have hbase := sum_integral_normSq_kloostermanHybridTransform_le q N (a q) hT
  have hqpos : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  calc
    (∑ n : ZMod (q + 1),
        ∫ t in Set.Icc (-T) T,
          ‖kloostermanHybridTransform q N (a q) n t‖ ^ 2) /
          (((q + 1 : ℕ) : ℝ) ^ 3) ≤
      ((((q + 1 : ℕ) : ℝ) ^ 2 *
        (5 * Real.pi * Real.exp 1 * (N : ℝ) +
          5 * Real.pi * ((q + 1 : ℕ) : ℝ) * T) *
        ∑ m ∈ Finset.Icc 1 N, ‖a q m‖ ^ 2) /
          (((q + 1 : ℕ) : ℝ) ^ 3)) :=
      div_le_div_of_nonneg_right hbase (by positivity)
    _ = (5 * Real.pi * Real.exp 1 * (N : ℝ) / ((q + 1 : ℕ) : ℝ) +
          5 * Real.pi * T) *
        ∑ m ∈ Finset.Icc 1 N, ‖a q m‖ ^ 2 := by
      field_simp

end RHTower.Sieve

