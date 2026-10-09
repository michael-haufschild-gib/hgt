import GaloisForLFunctions.RHTower.Sieve.UnitBlockReflectionMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenDualPerron

/-!
# The dual sum of a reflected unit block, in three Perron blocks

The dual frequencies `D = [k₁ + 1, k₂ − 1] ∩ ℤ` of a unit block move with the height `t`.  If they
lie in `(M, 8M]`, the dual sum splits over the dyadic blocks `(M, 2M]`, `(2M, 4M]`, `(4M, 8M]`
(`sum_ubDual_eq_blocks`), and on each block Perron's formula with half-integer cutoffs bounds the
moving partial sum by a weighted vertical integral of the fixed unit block
(`norm_sum_filter_block_le`).

A unit block at height `−s` is the complex conjugate of the block at `s`
(`norm_mtWattUnitBlock_neg`).
-/

open Complex Set MeasureTheory Filter
open GaloisForLFunctions.HTGeometry
open scoped Real ComplexConjugate

namespace RHTower.Sieve

noncomputable section

/-- `(n : ℂ)^{conj z} = conj (n^z)` for a positive integer `n`. -/
theorem natCast_cpow_conj_eq_conj_cpow {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (n : ℂ) ^ (conj z) = conj ((n : ℂ) ^ z) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_conj,
    map_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n),
    Complex.conj_ofReal]

/-- **A unit block at `−s` is conjugate to the block at `s`.** -/
theorem norm_mtWattUnitBlock_neg (M M' : ℕ) (s : ℝ) :
    ‖mtWattUnitBlock M M' (-s)‖ = ‖mtWattUnitBlock M M' s‖ := by
  rw [mtWattUnitBlock_eq_sum_Ico, mtWattUnitBlock_eq_sum_Ico, ← Complex.norm_conj (∑ n ∈ _, _),
    map_sum]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : 0 < n := by have := (Finset.mem_Ico.1 hn).1; omega
  rw [← natCast_cpow_conj_eq_conj_cpow hn0]
  congr 1
  simp [Complex.conj_ofReal]
  ring

/-- `(a + b)⁴ ≤ 8(a⁴ + b⁴)`. -/
theorem add_pow_four_le (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ 2 - b ^ 2),
    mul_nonneg (sq_nonneg (a + b)) (sq_nonneg (a - b)), sq_nonneg (a * b),
    mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a - b))]

/-- `(a + b + c + d)⁴ ≤ 64(a⁴ + b⁴ + c⁴ + d⁴)`. -/
theorem add_pow_four_le_four (a b c d : ℝ) :
    (a + b + c + d) ^ 4 ≤ 64 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by
  have h1 := add_pow_four_le (a + b) (c + d)
  have h2 := add_pow_four_le a b
  have h3 := add_pow_four_le c d
  rw [show a + b + c + d = (a + b) + (c + d) by ring]
  linarith

/-- **The dual sum in three dyadic blocks.**  If `M ≤ m₁` and `m₂ ≤ 8M`, the sum over
`[m₁ + 1, m₂] ∩ ℤ` is the sum of the three filtered block sums. -/
theorem sum_Icc_eq_blocks (f : ℤ → ℂ) {M : ℕ} {m₁ m₂ : ℤ} (hm₁ : (M : ℤ) ≤ m₁)
    (hm₂ : m₂ ≤ 8 * M) :
    ∑ k ∈ Finset.Icc (m₁ + 1) m₂, f k =
      (∑ k ∈ (Finset.Ioc M (2 * M)).filter (fun k : ℕ => m₁ < (k : ℤ) ∧ (k : ℤ) ≤ m₂), f k) +
      (∑ k ∈ (Finset.Ioc (2 * M) (4 * M)).filter (fun k : ℕ => m₁ < (k : ℤ) ∧ (k : ℤ) ≤ m₂),
        f k) +
      ∑ k ∈ (Finset.Ioc (4 * M) (8 * M)).filter (fun k : ℕ => m₁ < (k : ℤ) ∧ (k : ℤ) ≤ m₂),
        f k := by
  classical
  set P : ℕ → Prop := fun k => m₁ < (k : ℤ) ∧ (k : ℤ) ≤ m₂ with hP
  have hmap : Finset.Icc (m₁ + 1) m₂ = ((Finset.Ioc M (8 * M)).filter P).map Nat.castEmbedding := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_filter, Finset.mem_Ioc,
      Nat.castEmbedding_apply, hP]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨k.toNat, ⟨⟨by omega, by omega⟩, by omega, by omega⟩, by omega⟩
    · rintro ⟨n, ⟨-, h1, h2⟩, rfl⟩
      exact ⟨by omega, h2⟩
  rw [hmap, Finset.sum_map]
  simp only [Nat.castEmbedding_apply]
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_Ioc_consecutive _ (show M ≤ 2 * M by omega) (show 2 * M ≤ 8 * M by omega),
    ← Finset.sum_Ioc_consecutive _ (show 2 * M ≤ 4 * M by omega) (show 4 * M ≤ 8 * M by omega)]
  ring

/-- **Perron on one block with moving endpoints.**  For `0 ≤ m₁` and `−1 ≤ m₂`, the filtered sum
over `(B, 2B]` is bounded by the weighted vertical integral of the unit block, with cutoff weight
`m₁ + min(m₂, 2B) + 1`. -/
theorem norm_sum_filter_block_le {B : ℕ} (hB : 1 ≤ B) {m₁ m₂ : ℤ} (hm₁ : 0 ≤ m₁)
    (hm₂ : -1 ≤ m₂) {U τ : ℝ} (hU : 0 < U) :
    ‖∑ k ∈ (Finset.Ioc B (2 * B)).filter (fun k : ℕ => m₁ < (k : ℤ) ∧ (k : ℤ) ≤ m₂),
        (k : ℂ) ^ ((τ : ℂ) * I)‖ ≤
      ((m₁ + min m₂ (2 * B) + 1 : ℝ) / (2 * π)) * (∫ u in (-U)..U,
        ‖mtWattUnitBlock B (2 * B) (u - τ)‖ / ‖(1 : ℂ) + (u : ℂ) * I‖) +
      100 * (B : ℝ) ^ 2 / U := by
  classical
  have hfilt : (Finset.Ioc B (2 * B)).filter (fun k : ℕ => m₁ < (k : ℤ) ∧ (k : ℤ) ≤ m₂) =
      (Finset.Ioc B (2 * B)).filter
        (fun k : ℕ => m₁ < (k : ℤ) ∧ (k : ℤ) ≤ min m₂ (2 * B)) := by
    refine Finset.filter_congr fun k hk => ?_
    have := (Finset.mem_Ioc.1 hk).2
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, le_min h2 (by exact_mod_cast this)⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, le_trans h2 (min_le_left _ _)⟩
  have hcast : ((min m₂ (2 * B) : ℤ) : ℝ) = min (m₂ : ℝ) (2 * B) := by push_cast; rfl
  rw [hfilt, hcast]
  by_cases h : m₁ ≤ min m₂ (2 * B)
  · have := norm_sum_dual_le_perron hB hm₁ h (by have := min_le_right m₂ (2 * (B : ℤ)); omega)
      (τ := τ) hU
    rwa [hcast] at this
  · have hempty : (Finset.Ioc B (2 * B)).filter
        (fun k : ℕ => m₁ < (k : ℤ) ∧ (k : ℤ) ≤ min m₂ (2 * B)) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun k _ hk => h (by omega)
    rw [hempty, Finset.sum_empty, norm_zero]
    have hw : 0 ≤ ∫ u in (-U)..U, ‖mtWattUnitBlock B (2 * B) (u - τ)‖ /
        ‖(1 : ℂ) + (u : ℂ) * I‖ :=
      intervalIntegral.integral_nonneg (by linarith) fun u _ => by positivity
    have hc : (0 : ℝ) ≤ (m₁ : ℝ) + min (m₂ : ℝ) (2 * (B : ℝ)) + 1 := by
      have : (-1 : ℝ) ≤ min (m₂ : ℝ) (2 * B) := le_min (by exact_mod_cast hm₂)
        (by have : (0 : ℝ) ≤ B := Nat.cast_nonneg B; linarith)
      have : (0 : ℝ) ≤ m₁ := by exact_mod_cast hm₁
      linarith
    exact add_nonneg (mul_nonneg (div_nonneg hc (by positivity)) hw) (by positivity)

end

end RHTower.Sieve
