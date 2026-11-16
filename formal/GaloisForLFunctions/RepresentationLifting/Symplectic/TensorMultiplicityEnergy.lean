import GaloisForLFunctions.RepresentationLifting.Symplectic.SL2TensorCharacters
import GaloisForLFunctions.SelbergClass.Primon.SemicircleMoments
import Mathlib.Data.Nat.Sqrt

/-!
# Exact tensor multiplicity energy

Semicircle orthogonality extracts the actual multiplicity of each
constituent in a tensor power. Parseval's identity then identifies the
sum of squared multiplicities with a Catalan number. This transfers the
character-integral mechanism in Zehavi, Proposition 4.9, arXiv:2611.18218,
to the corpus's explicit rank-one tensor decomposition.
-/

namespace GaloisForLFunctions.RepresentationLifting.Symplectic

open GaloisForLFunctions.SelbergClass.Primon MeasureTheory

/-- Multiplicity of a highest weight in the actual branching list. -/
def tensorSpinMultiplicity (n k : ℕ) : ℕ := (tensorSpinWeights n).count k

private theorem continuous_character_list (l : List ℕ) :
    Continuous (fun x : ℝ => (l.map fun j => spectralCharacter j x).sum) := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact continuous_const
  | cons j l ih =>
    simpa only [List.map_cons, List.sum_cons] using (spectralCharacter j).continuous.add ih

private theorem integral_character_list (f : C(ℝ, ℝ)) (l : List ℕ) :
    (∫ x, f x * (l.map fun j => spectralCharacter j x).sum
      ∂(semicircleSpectralLaw : Measure ℝ)) =
        (l.map fun j => ∫ x, f x * spectralCharacter j x
          ∂(semicircleSpectralLaw : Measure ℝ)).sum := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    rw [integral_add, ih]
    · exact integrable_semicircleSpectralLaw_continuous (f * spectralCharacter j)
    · exact integrable_semicircleSpectralLaw_continuous
        ⟨_, f.continuous.mul (continuous_character_list l)⟩

private theorem character_indicator_count (l : List ℕ) (k : ℕ) :
    (l.map fun j => if k = j then (1 : ℝ) else 0).sum = (l.count k : ℝ) := by
  have h := List.sum_map_eq_nsmul_single k (fun j => if k = j then (1 : ℝ) else 0)
    (l := l) (fun j hj _ => if_neg hj.symm)
  simpa using h

/-- Multiplicity is an exact coefficient against the actual semicircle law. -/
theorem tensorSpinMultiplicity_integral (n k : ℕ) :
    (tensorSpinMultiplicity n k : ℝ) =
      ∫ x, x ^ n * spectralCharacter k x ∂(semicircleSpectralLaw : Measure ℝ) := by
  have he : (fun x : ℝ => x ^ n * spectralCharacter k x) =
      fun x => spectralCharacter k x *
        ((tensorSpinWeights n).map fun j => spectralCharacter j x).sum := by
    funext x
    rw [tensorSpin_character]
    ring
  rw [he, integral_character_list]
  simp_rw [integral_spectralCharacter_mul]
  exact (character_indicator_count _ _).symm

/-- Counting multiplicity once for each occurrence gives exactly the Catalan number. -/
theorem tensorSpinMultiplicity_energy_list (n : ℕ) :
    ((tensorSpinWeights n).map (tensorSpinMultiplicity n)).sum = catalan n := by
  have h := integral_character_list (⟨fun x : ℝ => x ^ n, by fun_prop⟩ : C(ℝ, ℝ))
    (tensorSpinWeights n)
  simp only [ContinuousMap.coe_mk, tensorSpin_character] at h
  simp_rw [← tensorSpinMultiplicity_integral] at h
  have he : (∫ x : ℝ, x ^ n * x ^ n ∂(semicircleSpectralLaw : Measure ℝ)) =
      (catalan n : ℝ) := by
    have hm := integral_semicircleSpectralLaw
      (⟨fun x : ℝ => x ^ (2 * n), by fun_prop⟩ : C(ℝ, ℝ))
    change (∫ x : ℝ, x ^ (2 * n) ∂(semicircleSpectralLaw : Measure ℝ)) = semicircleMoment (2 * n) at hm
    simp_rw [← pow_add, ← two_mul]
    exact hm.trans (semicircleMoment_even n)
  rw [he] at h
  exact_mod_cast h.symm

private theorem list_sum_eq_range_count (l : List ℕ) (N : ℕ)
    (hN : ∀ j ∈ l, j < N) (f : ℕ → ℕ) :
    (l.map f).sum = ∑ j ∈ Finset.range N, l.count j * f j := by
  induction l with
  | nil => simp
  | cons k l ih =>
    have hk : k < N := hN k (by simp)
    have hl : ∀ j ∈ l, j < N := fun j hj => hN j (by simp [hj])
    simp only [List.map_cons, List.sum_cons, List.count_cons]
    rw [ih hl]
    simp only [add_mul, Finset.sum_add_distrib]
    have he : (∑ j ∈ Finset.range N, (if k == j then 1 else 0) * f j) = f k := by
      simp [Finset.mem_range.mpr hk]
    omega

/-- The squared multiplicities sum to the dimension of the multiplicity algebra. -/
theorem tensorSpinMultiplicity_energy (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), tensorSpinMultiplicity n k ^ 2) = catalan n := by
  rw [← tensorSpinMultiplicity_energy_list]
  rw [list_sum_eq_range_count (tensorSpinWeights n) (n + 1)
    (fun j hj => Nat.lt_succ_of_le (tensorSpinWeights_le n j hj))]
  simp only [tensorSpinMultiplicity, pow_two]

/-- The multiplicity algebra has Catalan dimension, including every matrix block. -/
theorem tensorMultiplicityAlgebra_finrank (n : ℕ) :
    Module.finrank ℝ (∀ k : Fin (n + 1),
      Matrix (Fin (tensorSpinMultiplicity n k)) (Fin (tensorSpinMultiplicity n k)) ℝ) =
        catalan n := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi, Fintype.card_fin, Module.finrank_pi_fintype,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simpa only [pow_two, Fin.sum_univ_eq_sum_range] using tensorSpinMultiplicity_energy n

/-- Dimension carried by highest weights at most the cutoff. -/
def tensorSpinLowDimension (n L : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (· ≤ L), tensorSpinMultiplicity n k * (k + 1)

/-- Low and high highest weights partition the full tensor dimension. -/
theorem tensorSpin_low_add_tail (n L : ℕ) :
    tensorSpinLowDimension n L + tensorSpinTailDimension n L = 2 ^ n := by
  have hl := list_sum_eq_range_count (tensorSpinWeights n) (n + 1)
    (fun j hj => Nat.lt_succ_of_le (tensorSpinWeights_le n j hj))
    (fun j => if j ≤ L then j + 1 else 0)
  simp_rw [mul_ite, mul_zero] at hl
  rw [← Finset.sum_filter] at hl
  change _ = tensorSpinLowDimension n L at hl
  rw [← hl, tensorSpinTailDimension, ← List.sum_map_add]
  have he (j : ℕ) : (if j ≤ L then j + 1 else 0) +
      (if L + 1 ≤ j then j + 1 else 0) = j + 1 := by
    by_cases hj : j ≤ L
    · simp [hj, show ¬ L + 1 ≤ j by omega]
    · simp [hj, show L + 1 ≤ j by omega]
  simp_rw [he]
  exact tensorSpin_dimension n

/-- Cauchy--Schwarz controls low-weight dimension by exact multiplicity energy. -/
theorem tensorSpin_low_square_bound (n L : ℕ) :
    tensorSpinLowDimension n L ^ 2 ≤ catalan n * (L + 1) ^ 3 := by
  let s := (Finset.range (n + 1)).filter (· ≤ L)
  have he : (∑ k ∈ s, tensorSpinMultiplicity n k ^ 2) ≤ catalan n := by
    rw [← tensorSpinMultiplicity_energy n]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hs : s ⊆ Finset.range (L + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hk).2)
  have hc : s.card ≤ L + 1 := by
    simpa only [Finset.card_range] using Finset.card_le_card hs
  have hw : (∑ k ∈ s, (k + 1) ^ 2) ≤ (L + 1) ^ 3 := by
    calc
      _ ≤ ∑ _k ∈ s, (L + 1) ^ 2 := Finset.sum_le_sum fun k hk =>
        Nat.pow_le_pow_left (by have := (Finset.mem_filter.mp hk).2; omega)
      _ = s.card * (L + 1) ^ 2 := by simp
      _ ≤ (L + 1) * (L + 1) ^ 2 := Nat.mul_le_mul_right _ hc
      _ = (L + 1) ^ 3 := by ring
  exact (Finset.sum_mul_sq_le_sq_mul_sq s (tensorSpinMultiplicity n) (fun k => k + 1)).trans
    (Nat.mul_le_mul he hw)

/-- A square-root cutoff captures at least half of the tensor dimension. -/
theorem tensorSpin_sqrt_cutoff (n : ℕ) :
    2 ^ n ≤ 2 * tensorSpinLowDimension n (Nat.sqrt (6 * n) + 1) := by
  let L := Nat.sqrt (6 * n) + 1
  have hs : 6 * n < (L + 1) * (L + 3) := by
    have h := Nat.lt_succ_sqrt' (6 * n)
    dsimp [L]
    nlinarith only [h]
  have ht := tensorSpin_tail_bound n L
  have hd := tensorSpin_low_add_tail n L
  have hhalf : 2 * tensorSpinTailDimension n L ≤ 2 ^ n := by
    by_contra h
    have hpos : 0 < tensorSpinTailDimension n L := by omega
    have hh : 3 * n * 2 ^ n ≤ 6 * n * tensorSpinTailDimension n L := by
      nlinarith only [show 2 ^ n ≤ 2 * tensorSpinTailDimension n L by omega]
    have hstrict := Nat.mul_lt_mul_of_pos_right hs hpos
    omega
  dsimp [L] at hd hhalf
  omega

/-- The low/high-weight split recovers a Catalan lower bound at the three-halves scale. -/
theorem catalan_lower_bound_from_tensor_split (n : ℕ) :
    (2 ^ n) ^ 2 ≤ 4 * catalan n * (Nat.sqrt (6 * n) + 2) ^ 3 := by
  have h := tensorSpin_sqrt_cutoff n
  have hs := Nat.pow_le_pow_left (n := 2) h
  have hl := tensorSpin_low_square_bound n (Nat.sqrt (6 * n) + 1)
  nlinarith only [hs, hl]

end GaloisForLFunctions.RepresentationLifting.Symplectic

#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.tensorSpinMultiplicity_integral
#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.tensorSpinMultiplicity_energy
#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.tensorMultiplicityAlgebra_finrank
#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.catalan_lower_bound_from_tensor_split
