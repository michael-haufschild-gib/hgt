/-
# Separated linear-to-bilinear decomposition

Consecutive blocks are colored modulo three.  Distinct blocks of one color
are automatically separated by at least one intervening block.  Applying the
finite diagonal/bilinear inequality inside each color and Jensen across the
three colors gives a pointwise version of Bourgain's equation (2.25) in which
every bilinear pair is separated.
-/
import GaloisForLFunctions.RHTower.BourgainLinearBilinearDecomposition
import Mathlib.Algebra.Order.Chebyshev

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Residue class modulo three used to separate consecutive blocks. -/
def bourgainBlockColor {K : ℕ} (i : Fin K) : Fin 3 :=
  ⟨i.1 % 3, Nat.mod_lt _ (by norm_num)⟩

/-- Two block indices have at least one full intervening block. -/
def BourgainSeparatedBlocks {K : ℕ} (i j : Fin K) : Prop :=
  i.1 + 1 < j.1 ∨ j.1 + 1 < i.1

/-- Distinct indices with the same modulo-three color are separated. -/
theorem bourgainSeparatedBlocks_of_color_eq
    {K : ℕ} {i j : Fin K}
    (hcolor : bourgainBlockColor i = bourgainBlockColor j)
    (hne : i ≠ j) :
    BourgainSeparatedBlocks i j := by
  have hmod : i.1 % 3 = j.1 % 3 :=
    congrArg Fin.val hcolor
  have hval : i.1 ≠ j.1 := by
    exact fun h => hne (Fin.ext h)
  unfold BourgainSeparatedBlocks
  omega

/-- Blocks of one fixed residue color. -/
def bourgainColorBlockFinset (K : ℕ) (c : Fin 3) : Finset (Fin K) :=
  (Finset.univ : Finset (Fin K)).filter
    (fun i => bourgainBlockColor i = c)

/-- The modulo-three block fibers partition all block indices. -/
theorem sum_bourgainColorBlockFinset
    {K : ℕ} (z : Fin K → ℂ) :
    (∑ c : Fin 3, ∑ i ∈ bourgainColorBlockFinset K c, z i) =
      ∑ i : Fin K, z i := by
  classical
  exact Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin K)))
    (t := (Finset.univ : Finset (Fin 3)))
    (g := bourgainBlockColor)
    (fun i hi => Finset.mem_univ _)
    z

/-- Every off-diagonal pair appearing inside one color is separated. -/
theorem separated_of_mem_colorBlock_filter_ne
    {K : ℕ} {c : Fin 3} {i j : Fin K}
    (hi : i ∈ bourgainColorBlockFinset K c)
    (hj :
      j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i)) :
    BourgainSeparatedBlocks i j := by
  have hicolor := (Finset.mem_filter.mp hi).2
  have hjmem := (Finset.mem_filter.mp hj).1
  have hjcolor := (Finset.mem_filter.mp hjmem).2
  have hjne := (Finset.mem_filter.mp hj).2
  exact bourgainSeparatedBlocks_of_color_eq
    (hicolor.trans hjcolor.symm) hjne.symm

/-- **Separated pointwise linear-to-bilinear decomposition.**

The three color classes contribute the harmless fixed factor `3^(11 : ℕ)`.
Within each class the diagonal coefficient is fixed and every bilinear pair
is separated by `separated_of_mem_colorBlock_filter_ne`. -/
theorem norm_finSum_pow_twelve_le_threeColor_bilinear
    (K : ℕ) (z : Fin K → ℂ) :
    ‖∑ i : Fin K, z i‖ ^ (12 : ℕ) ≤
      (3 : ℝ) ^ (11 : ℕ) *
        ∑ c : Fin 3,
          ((2 : ℝ) ^ (12 : ℕ) *
              ∑ i ∈ bourgainColorBlockFinset K c,
                ‖z i‖ ^ (12 : ℕ) +
            ((bourgainColorBlockFinset K c).card : ℝ) ^ (18 : ℕ) *
              ∑ i ∈ bourgainColorBlockFinset K c,
                ∑ j ∈ (bourgainColorBlockFinset K c).filter
                    (fun j => j ≠ i),
                  ‖z i‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ)) := by
  classical
  let B : Fin 3 → Finset (Fin K) :=
    fun c => bourgainColorBlockFinset K c
  let Z : Fin 3 → ℂ := fun c => ∑ i ∈ B c, z i
  have hpartition :
      (∑ i : Fin K, z i) = ∑ c : Fin 3, Z c := by
    rw [← sum_bourgainColorBlockFinset z]
  have hnorm :
      ‖∑ i : Fin K, z i‖ ≤ ∑ c : Fin 3, ‖Z c‖ := by
    rw [hpartition]
    exact norm_sum_le _ _
  have hpow :
      ‖∑ i : Fin K, z i‖ ^ (12 : ℕ) ≤
        (∑ c : Fin 3, ‖Z c‖) ^ (12 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 12
  have hjensen :
      (∑ c : Fin 3, ‖Z c‖) ^ (12 : ℕ) ≤
        (3 : ℝ) ^ (11 : ℕ) *
          ∑ c : Fin 3, ‖Z c‖ ^ (12 : ℕ) := by
    simpa using
      (pow_sum_le_card_mul_sum_pow
        (s := (Finset.univ : Finset (Fin 3)))
        (f := fun c => ‖Z c‖)
        (fun c hc => norm_nonneg _) 11)
  have hblocks :
      (∑ c : Fin 3, ‖Z c‖ ^ (12 : ℕ)) ≤
        ∑ c : Fin 3,
          ((2 : ℝ) ^ (12 : ℕ) *
              ∑ i ∈ B c, ‖z i‖ ^ (12 : ℕ) +
            ((B c).card : ℝ) ^ (18 : ℕ) *
              ∑ i ∈ B c, ∑ j ∈ (B c).filter (fun j => j ≠ i),
                ‖z i‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ)) := by
    apply Finset.sum_le_sum
    intro c hc
    exact norm_finsetSum_pow_twelve_le_diagonal_add_bilinear (B c) z
  calc
    ‖∑ i : Fin K, z i‖ ^ (12 : ℕ) ≤
        (∑ c : Fin 3, ‖Z c‖) ^ (12 : ℕ) := hpow
    _ ≤ (3 : ℝ) ^ (11 : ℕ) *
        ∑ c : Fin 3, ‖Z c‖ ^ (12 : ℕ) := hjensen
    _ ≤ (3 : ℝ) ^ (11 : ℕ) *
        ∑ c : Fin 3,
          ((2 : ℝ) ^ (12 : ℕ) *
              ∑ i ∈ B c, ‖z i‖ ^ (12 : ℕ) +
            ((B c).card : ℝ) ^ (18 : ℕ) *
              ∑ i ∈ B c, ∑ j ∈ (B c).filter (fun j => j ≠ i),
                ‖z i‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ)) :=
      mul_le_mul_of_nonneg_left hblocks (by positivity)
    _ = (3 : ℝ) ^ (11 : ℕ) *
        ∑ c : Fin 3,
          ((2 : ℝ) ^ (12 : ℕ) *
              ∑ i ∈ bourgainColorBlockFinset K c,
                ‖z i‖ ^ (12 : ℕ) +
            ((bourgainColorBlockFinset K c).card : ℝ) ^ (18 : ℕ) *
              ∑ i ∈ bourgainColorBlockFinset K c,
                ∑ j ∈ (bourgainColorBlockFinset K c).filter
                    (fun j => j ≠ i),
                  ‖z i‖ ^ (6 : ℕ) * ‖z j‖ ^ (6 : ℕ)) := by rfl

end

end RHTower
