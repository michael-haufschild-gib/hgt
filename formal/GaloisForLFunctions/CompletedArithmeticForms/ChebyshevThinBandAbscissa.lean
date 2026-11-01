import GaloisForLFunctions.CompletedArithmeticForms.ChebyshevCyclotomicIntrinsicTail

/-!
# Every positive-power band retains the Chebyshev zero width

The far packet has a strict exponent saving at the intrinsic abscissa.
Consequently every band `K = ceil(N^δ)`, `δ > 0`, has the same infimum
energy exponent `2Θ` as the full cyclotomic remainder.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open _root_.RHTower GaloisForLFunctions.RHTower

/-- The actual near packet at an arbitrary positive-power frequency cutoff. -/
def chebyshevPowerBand (δ : ℝ) (N : ℕ) : ℝ :=
  chebyshevCyclotomicNear N ⌈(N : ℝ) ^ δ⌉₊

private theorem near_le_remainder (N K : ℕ) :
    chebyshevCyclotomicNear N K ≤ chebyshevCyclotomicRemainder N := by
  rw [chebyshevCyclotomicRemainder_eq_far_add_near N K]
  apply le_add_of_nonneg_left
  exact div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

private theorem remainder_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      chebyshevCyclotomicRemainder N ≤ C * (N : ℝ) ^ (2 * zetaZeroAbscissa + ε) := by
  obtain ⟨C, hC, hE⟩ := exists_sum_sq_le_rpow_zetaZeroAbscissa_of_linear_bridge
    (by norm_num : (0 : ℝ) < 1 / 2)
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear ε hε
  refine ⟨4 * C, by positivity, fun N hN => ?_⟩
  exact (chebyshevEnergy_cyclotomic_bounds N).1.trans
    ((mul_le_mul_of_nonneg_left (hE N hN) (by norm_num : (0 : ℝ) ≤ 4)).trans_eq
      (by ring))

/-- Every near packet admits the intrinsic upper exponents, uniformly in its bandwidth. -/
theorem chebyshevPowerBand_subpower (δ ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      chebyshevPowerBand δ N ≤ C * (N : ℝ) ^ (2 * zetaZeroAbscissa + ε) := by
  obtain ⟨C, hC, hR⟩ := remainder_subpower ε hε
  exact ⟨C, hC, fun N hN => (near_le_remainder N _).trans (hR N hN)⟩

private theorem far_powerBand_subpower (δ ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      chebyshevCyclotomicFar N ⌈(N : ℝ) ^ δ⌉₊ ≤
        C * (N : ℝ) ^ (2 * zetaZeroAbscissa - δ + ε) := by
  obtain ⟨C, hC, hF⟩ := chebyshevCyclotomicFar_subpower ε hε
  refine ⟨C, hC, fun N hN => ?_⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow := Real.rpow_pos_of_pos hNp δ
  have hceil := Nat.le_ceil ((N : ℝ) ^ δ)
  have hKp : (0 : ℝ) < (⌈(N : ℝ) ^ δ⌉₊ : ℕ) := hpow.trans_le hceil
  have hK : 1 ≤ ⌈(N : ℝ) ^ δ⌉₊ := by exact_mod_cast hKp
  calc
    _ ≤ C * (N : ℝ) ^ (2 * zetaZeroAbscissa + ε) / ⌈(N : ℝ) ^ δ⌉₊ := hF N _ hN hK
    _ ≤ C * (N : ℝ) ^ (2 * zetaZeroAbscissa + ε) / (N : ℝ) ^ δ :=
      div_le_div_of_nonneg_left (by positivity) hpow hceil
    _ = _ := by
      rw [mul_div_assoc, ← Real.rpow_sub hNp]
      congr 2
      ring

private theorem powerBand_exponent_lower {δ r C : ℝ} (hδ : 0 < δ)
    (hr : 1 ≤ r) (hC : 0 ≤ C)
    (hB : ∀ N : ℕ, 2 ≤ N → chebyshevPowerBand δ N ≤ C * (N : ℝ) ^ r) :
    2 * zetaZeroAbscissa ≤ r := by
  by_contra hnot
  have hrΘ : r < 2 * zetaZeroAbscissa := lt_of_not_ge hnot
  obtain ⟨D, hD, hF⟩ := far_powerBand_subpower δ (δ / 2) (by positivity)
  let s := max r (2 * zetaZeroAbscissa - δ + δ / 2)
  have hs1 : 1 ≤ s := hr.trans (le_max_left _ _)
  have hsΘ : s < 2 * zetaZeroAbscissa := max_lt hrΘ (by linarith only [hδ])
  have hR : ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 2 ≤ N →
      chebyshevCyclotomicRemainder N ≤ A * (N : ℝ) ^ s := by
    refine ⟨D + C, add_nonneg hD hC, fun N hN => ?_⟩
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    rw [chebyshevCyclotomicRemainder_eq_far_add_near N ⌈(N : ℝ) ^ δ⌉₊]
    calc
      _ ≤ D * (N : ℝ) ^ (2 * zetaZeroAbscissa - δ + δ / 2) + C * (N : ℝ) ^ r :=
        add_le_add (hF N hN) (hB N hN)
      _ ≤ D * (N : ℝ) ^ s + C * (N : ℝ) ^ s :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hN1 (le_max_right _ _)) hD)
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)) hC)
      _ = _ := by ring
  obtain ⟨A, hA, hE⟩ := (chebyshevEnergy_power_bound_iff_cyclotomic hs1).mpr hR
  have hΘ := zetaZeroAbscissa_le_half_of_chebyshevNormalizedCesaroMeanSquareEnergy_le_rpow
    hA hs1 hE
  linarith only [hΘ, hsΘ]

/-- An arbitrarily thin positive-power band has the full intrinsic energy abscissa. -/
theorem chebyshevPowerBand_exponent_inf (δ : ℝ) (hδ : 0 < δ) :
    sInf {r : ℝ | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      chebyshevPowerBand δ N ≤ C * (N : ℝ) ^ r} = 2 * zetaZeroAbscissa := by
  let E := {r : ℝ | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    chebyshevPowerBand δ N ≤ C * (N : ℝ) ^ r}
  have hbdd : BddBelow E := ⟨1, fun _ h => h.1⟩
  have hmem (ε : ℝ) (hε : 0 < ε) : 2 * zetaZeroAbscissa + ε ∈ E := by
    exact ⟨by linarith only [half_le_zetaZeroAbscissa, hε],
      chebyshevPowerBand_subpower δ ε hε⟩
  have hne : E.Nonempty := ⟨2 * zetaZeroAbscissa + 1, hmem 1 (by norm_num)⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact csInf_le hbdd (hmem ε hε)
  · apply le_csInf hne
    rintro r ⟨hr, C, hC, hB⟩
    exact powerBand_exponent_lower hδ hr hC hB

/-- Subpower bounds for every positive-power near band are exactly the zero-width bounds. -/
theorem chebyshevPowerBand_subpower_iff (δ r : ℝ) (hδ : 0 < δ) (hr : 1 ≤ r) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      chebyshevPowerBand δ N ≤ C * (N : ℝ) ^ (r + ε)) ↔
        2 * zetaZeroAbscissa ≤ r := by
  constructor
  · intro h
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨C, hC, hB⟩ := h ε hε
    exact powerBand_exponent_lower hδ (by linarith only [hr, hε]) hC hB
  · intro h ε hε
    obtain ⟨C, hC, hB⟩ := chebyshevPowerBand_subpower δ ε hε
    refine ⟨C, hC, fun N hN => (hB N hN).trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hC
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [h])

private theorem remainder_subpower_iff {r : ℝ} (hr : 1 ≤ r) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      chebyshevCyclotomicRemainder N ≤ C * (N : ℝ) ^ (r + ε)) ↔
        2 * zetaZeroAbscissa ≤ r := by
  constructor
  · intro h
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨C, hC, hE⟩ := (chebyshevEnergy_power_bound_iff_cyclotomic
      (by linarith only [hr, hε])).mpr (h ε hε)
    have hΘ := zetaZeroAbscissa_le_half_of_chebyshevNormalizedCesaroMeanSquareEnergy_le_rpow
      hC (by linarith only [hr, hε]) hE
    linarith only [hΘ]
  · intro h ε hε
    obtain ⟨C, hC, hR⟩ := remainder_subpower ε hε
    refine ⟨C, hC, fun N hN => (hR N hN).trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hC
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [h])

/-- The five-sixths strip can be tested on any positive-power frequency band. -/
theorem five_sixths_strip_iff_chebyshevPowerBand (δ : ℝ) (hδ : 0 < δ) :
    (∀ ρ : ℂ, xi ρ = 0 → (1 / 6 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 5 / 6) ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
        chebyshevPowerBand δ N ≤ C * (N : ℝ) ^ ((5 / 3 : ℝ) + ε) := by
  rw [five_sixths_strip_iff_chebyshevCyclotomicRemainder_subpower,
    remainder_subpower_iff (by norm_num : (1 : ℝ) ≤ 5 / 3),
    chebyshevPowerBand_subpower_iff δ (5 / 3) hδ (by norm_num)]

/-- The three-quarters strip can be tested on any positive-power frequency band. -/
theorem three_quarters_strip_iff_chebyshevPowerBand (δ : ℝ) (hδ : 0 < δ) :
    (∀ ρ : ℂ, xi ρ = 0 → (1 / 4 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3 / 4) ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
        chebyshevPowerBand δ N ≤ C * (N : ℝ) ^ ((3 / 2 : ℝ) + ε) := by
  rw [three_quarters_strip_iff_chebyshevCyclotomicRemainder_subpower,
    remainder_subpower_iff (by norm_num : (1 : ℝ) ≤ 3 / 2),
    chebyshevPowerBand_subpower_iff δ (3 / 2) hδ (by norm_num)]

end GaloisForLFunctions.CompletedArithmeticForms
