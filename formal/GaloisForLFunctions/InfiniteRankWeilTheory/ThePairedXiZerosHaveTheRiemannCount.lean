import GaloisForLFunctions.InfiniteRankWeilTheory.ThePairedXiDivisorIsAnEntireFunction
import GaloisForLFunctions.RHTower.XiZeroCountRVMRemainder

/-!
# The exact zero count of the paired Xi model

Every positive quartet contributes two simple zeros. Consequently the
count through height `T` is `2⌊Nξ(T)/2⌋`. Its discrepancy from the actual
Xi divisor count is at most one, so the full logarithmic Riemann–von
Mangoldt remainder survives.
-/

noncomputable section
open Complex Set Filter Topology
open _root_.RHTower

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- The positive zeros through height `T`, as a finite set of actual points. -/
def pairedXiPositiveZeros (T : ℝ) : Finset ℂ := by
  classical
  exact ((Finset.range ((xiZeroCount T).toNat / 2)) ×ˢ (Finset.univ : Finset Bool)).image
    (fun q : ℕ × Bool => (1 / 2 : ℂ) + pairedXiPoint (q.1, q.2, true))

theorem mem_pairedXiPositiveZeros {T : ℝ} {s : ℂ} :
    s ∈ pairedXiPositiveZeros T ↔ pairedXiModel s = 0 ∧ 0 < s.im ∧ s.im ≤ T := by
  classical
  constructor
  · intro hs
    obtain ⟨⟨n, b⟩, hn, rfl⟩ := Finset.mem_image.mp hs
    have hn' : n < (xiZeroCount T).toNat / 2 :=
      Finset.mem_range.mp (Finset.mem_product.mp hn).1
    refine ⟨(pairedXiModel_eq_zero_iff _).mpr ⟨(n, b, true), rfl⟩, ?_, ?_⟩
    · simpa [quartetSign] using pairedXiHeight_pos n
    · simpa [quartetSign] using (pairedXiHeight_le_iff n T).mpr hn'
  · rintro ⟨hs, hpos, hT⟩
    obtain ⟨⟨n, b, c⟩, rfl⟩ := (pairedXiModel_eq_zero_iff s).mp hs
    cases c
    · have hneg : 0 < -pairedXiHeight n := by simpa [quartetSign] using hpos
      linarith only [hneg, pairedXiHeight_pos n]
    · have hn : n < (xiZeroCount T).toNat / 2 := (pairedXiHeight_le_iff n T).mp
        (by simpa [quartetSign] using hT)
      exact Finset.mem_image.mpr ⟨(n, b),
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr hn, Finset.mem_univ _⟩, rfl⟩

theorem card_pairedXiPositiveZeros (T : ℝ) :
    (pairedXiPositiveZeros T).card = 2 * ((xiZeroCount T).toNat / 2) := by
  classical
  have hinj : Function.Injective (fun q : ℕ × Bool =>
      (1 / 2 : ℂ) + pairedXiPoint (q.1, q.2, true)) := by
    rintro ⟨n, b⟩ ⟨m, c⟩ h
    have hp := pairedXiPoint_injective (add_left_cancel h)
    have hn : n = m := congrArg Prod.fst hp
    have hb : b = c := congrArg (fun q : ℕ × Bool × Bool => q.2.1) hp
    exact Prod.ext hn hb
  rw [pairedXiPositiveZeros, Finset.card_image_of_injective _ hinj,
    Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_bool]
  omega

/-- Literal counting of the analytic zeros agrees with the paired integer count. -/
theorem ncard_pairedXiModel_positive_zeros (T : ℝ) :
    {s : ℂ | pairedXiModel s = 0 ∧ 0 < s.im ∧ s.im ≤ T}.ncard =
      2 * ((xiZeroCount T).toNat / 2) := by
  have heq : {s : ℂ | pairedXiModel s = 0 ∧ 0 < s.im ∧ s.im ≤ T} =
      (pairedXiPositiveZeros T : Set ℂ) := by
    ext s
    exact mem_pairedXiPositiveZeros.symm
  rw [heq, Set.ncard_coe_finset, card_pairedXiPositiveZeros]

/-- Pairing changes the actual Xi zero count by at most one. -/
theorem pairedXi_zero_count_discrepancy (T : ℝ) :
    |({s : ℂ | pairedXiModel s = 0 ∧ 0 < s.im ∧ s.im ≤ T}.ncard : ℝ) -
      (xiZeroCount T : ℝ)| ≤ 1 := by
  rw [ncard_pairedXiModel_positive_zeros]
  have hcast := Int.toNat_of_nonneg (xiZeroCount_nonneg T)
  have hupp : 2 * ((xiZeroCount T).toNat / 2) ≤ (xiZeroCount T).toNat := by omega
  have hgap : (xiZeroCount T).toNat ≤ 2 * ((xiZeroCount T).toNat / 2) + 1 := by omega
  have hc : ((xiZeroCount T).toNat : ℝ) = (xiZeroCount T : ℝ) := by exact_mod_cast hcast
  have hu : (2 * ((xiZeroCount T).toNat / 2) : ℕ) ≤ (xiZeroCount T).toNat := hupp
  have huR : ((2 * ((xiZeroCount T).toNat / 2) : ℕ) : ℝ) ≤ (xiZeroCount T : ℝ) := by
    rw [← hc]
    exact_mod_cast hu
  have hlR : (xiZeroCount T : ℝ) ≤ ((2 * ((xiZeroCount T).toNat / 2) : ℕ) : ℝ) + 1 := by
    rw [← hc]
    exact_mod_cast hgap
  rw [abs_le]
  constructor <;> linarith only [huR, hlR]

/-- The full `O(log T)` Riemann–von Mangoldt remainder holds for the paired analytic zeros. -/
theorem pairedXiModel_riemannVonMangoldt :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      |({s : ℂ | pairedXiModel s = 0 ∧ 0 < s.im ∧ s.im ≤ T}.ncard : ℝ) -
        routeKSmoothRVMCount T| ≤ C * Real.log T := by
  obtain ⟨C, hC, T₀, hT₀, hbound⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  refine ⟨C + 1, by linarith only [hC], max T₀ (Real.exp 1),
    hT₀.trans (le_max_left _ _), fun T hT => ?_⟩
  have hTbase : T₀ ≤ T := (le_max_left _ _).trans hT
  have he : Real.exp 1 ≤ T := (le_max_right _ _).trans hT
  have hlog : 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  calc
    _ ≤ |({s : ℂ | pairedXiModel s = 0 ∧ 0 < s.im ∧ s.im ≤ T}.ncard : ℝ) -
        (xiZeroCount T : ℝ)| + |(xiZeroCount T : ℝ) - routeKSmoothRVMCount T| :=
      abs_sub_le _ _ _
    _ ≤ 1 + C * Real.log T := add_le_add (pairedXi_zero_count_discrepancy T) (hbound T hTbase)
    _ ≤ (C + 1) * Real.log T := by linarith only [hlog]

#print axioms ncard_pairedXiModel_positive_zeros
#print axioms pairedXi_zero_count_discrepancy
#print axioms pairedXiModel_riemannVonMangoldt

end GaloisForLFunctions.InfiniteRankWeilTheory
