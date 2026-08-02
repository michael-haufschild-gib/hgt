import GaloisForLFunctions.HTGeometry.ProductStabilizerPauliTwirlLaw
import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarMeasureLaw

/-!
# Permanent operational locality--Haar separation

This module compares two exact quantities already derived in the corpus.
A conserved fixed-`q` Pauli coordinate forces product-stabilizer two-query
signal at least `3^{-q}/M` at every time.  An operator-norm-one balanced
probe under Haar-random unitary evolution has exact mean-square signal
`1/(D+1)`.

Consequently, whenever `M 3^q < D+1`, the local Hamiltonian signal is
strictly larger than the exact Haar benchmark.  No late-time or
high-complexity limit erases this separator: the proof uses only the
conserved Hamiltonian coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Matrix

/-- The inverse-dimension Haar benchmark is strictly below the
dimension-linear conserved-local lower bound precisely in the regime
`M 3^q < D+1`. -/
theorem haarBenchmark_lt_conservedLocalLowerBound
    (q M D : ℕ) (hM : 0 < M)
    (hsep : M * 3 ^ q < D + 1) :
    1 / ((D + 1 : ℕ) : ℝ) <
      ((1 : ℝ) / 3) ^ q / (M : ℝ) := by
  have hden : (0 : ℝ) < ((M * 3 ^ q : ℕ) : ℝ) := by
    positivity
  have hsepR :
      ((M * 3 ^ q : ℕ) : ℝ) < ((D + 1 : ℕ) : ℝ) := by
    exact_mod_cast hsep
  have hrecip :
      1 / ((D + 1 : ℕ) : ℝ) <
        1 / ((M * 3 ^ q : ℕ) : ℝ) :=
    one_div_lt_one_div_of_lt hden hsepR
  calc
    1 / ((D + 1 : ℕ) : ℝ) <
        1 / ((M * 3 ^ q : ℕ) : ℝ) := hrecip
    _ = ((1 : ℝ) / 3) ^ q / (M : ℝ) := by
      have hM0 : (M : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hM)
      field_simp [hM0]
      rw [div_pow]
      norm_num

/-- **Permanent operational separator.**  For any time slice whose Pauli
transfer matrix fixes one nonzero local Hamiltonian coordinate, the exact
product-stabilizer two-query signal is strictly above the Haar benchmark
whenever `M 3^q < D+1`. -/
theorem productStabilizerTwoQueryProtocolSignal_gt_haarBenchmark
    {σ ι : Type*} [Fintype σ] [Fintype ι] [Nonempty ι]
    (q D : ℕ) (label : ι → σ → Option (Fin 3))
    (hinj : Function.Injective label)
    (hweight : ∀ j, finitePauliWeight (label j) ≤ q)
    (C : Matrix ι ι ℝ) (h : ι → ℝ) (hh : h ≠ 0)
    (hfix : C *ᵥ h = h)
    (hsep : Fintype.card ι * 3 ^ q < D + 1) :
    1 / ((D + 1 : ℕ) : ℝ) <
      productStabilizerTwoQueryProtocolSignal label C := by
  have hM : 0 < Fintype.card ι :=
    Fintype.card_pos
  calc
    1 / ((D + 1 : ℕ) : ℝ) <
        ((1 : ℝ) / 3) ^ q / (Fintype.card ι : ℝ) :=
      haarBenchmark_lt_conservedLocalLowerBound
        q (Fintype.card ι) D hM hsep
    _ ≤ productStabilizerTwoQueryProtocolSignal label C :=
      productStabilizerTwoQueryProtocolSignal_ge
        q label hinj hweight C h hh hfix

/-- The benchmark in the permanent separator is realized exactly by an
explicit balanced operator-norm-one probe in every even Hilbert dimension
`D = 2(n+1)`. -/
theorem explicitBalancedHaarProbe_lt_productStabilizerSignal
    {σ ι : Type*} [Fintype σ] [Fintype ι] [Nonempty ι]
    (q n : ℕ) (j : Fin 2 ⊕ Fin (n + n))
    (label : ι → σ → Option (Fin 3))
    (hinj : Function.Injective label)
    (hweight : ∀ k, finitePauliWeight (label k) ≤ q)
    (C : Matrix ι ι ℝ) (h : ι → ℝ) (hh : h ≠ 0)
    (hfix : C *ᵥ h = h)
    (hsep : Fintype.card ι * 3 ^ q < n + n + 3) :
    finiteUnitaryDiagonalProbeHaarSignal
        (n + n) (finiteUnitaryBalancedDiagonalSign n) j <
      productStabilizerTwoQueryProtocolSignal label C := by
  rw [finiteUnitaryBalancedDiagonalProbeHaarSignal_eq]
  have h := productStabilizerTwoQueryProtocolSignal_gt_haarBenchmark
    q (n + n + 2) label hinj hweight C h hh hfix
      (by simpa [Nat.add_assoc] using hsep)
  convert h using 1
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring

end

end GaloisForLFunctions.HTGeometry
