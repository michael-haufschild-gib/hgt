import GaloisForLFunctions.RHTower.PaperWoldEssentialFloor
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount

/-! # Actual prime index windows for the full Wold matrix

The native increment at index `n` carries the prime at `n+2`. Prime-count
bounds are transported to exactly those indices, with no distributional premise.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions.HTGeometry
open scoped BigOperators

def paperWoldPrimeIndices (N : ℕ) : Finset ℕ :=
  (primesInIoc N (2 * N)).image (fun p => p - 2)

theorem paperWoldPrimeIndices_mem (N n : ℕ) :
    n ∈ paperWoldPrimeIndices N ↔ (n + 2).Prime ∧ N < n + 2 ∧ n + 2 ≤ 2 * N := by
  constructor
  · rintro hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    have h := mem_primesInIoc hp
    simpa only [Nat.sub_add_cancel h.1.two_le] using h
  · intro hn
    apply Finset.mem_image.mpr
    refine ⟨n + 2, ?_, by omega⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hn.2.1, hn.2.2⟩, hn.1⟩

theorem paperWoldPrimeIndices_card (N : ℕ) :
    (paperWoldPrimeIndices N).card = (primesInIoc N (2 * N)).card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq he
  have hp2 := (mem_primesInIoc hp).1.two_le
  have hq2 := (mem_primesInIoc hq).1.two_le
  dsimp at he
  omega

theorem paperWoldPrimeIndices_eventual_card :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / (2 * Real.log N) ≤ ((paperWoldPrimeIndices N).card : ℝ) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_primeCount_window_ge (K := 2) (by norm_num))
  filter_upwards [h] with N hN
  have hf : ⌊(2 : ℝ) * (N : ℝ)⌋₊ = 2 * N := by
    rw [show (2 : ℝ) * (N : ℝ) = ((2 * N : ℕ) : ℝ) by push_cast; rfl,
      Nat.floor_natCast]
  rw [hf, Nat.floor_natCast] at hN
  rw [paperWoldPrimeIndices_card, card_primesInIoc (by omega : N ≤ 2 * N)]
  calc
    (N : ℝ) / (2 * Real.log N) = (2 - 1) / 2 * ((N : ℝ) / Real.log N) := by ring
    _ ≤ _ := hN

/-- Both separated native windows have the same positive cardinality budget. -/
theorem paperWoldPrimeIndices_eventual_pair_card :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧ 64 ≤ Real.log N ∧
      (N : ℝ) / (2 * Real.log N) ≤ ((paperWoldPrimeIndices N).card : ℝ) ∧
      (N : ℝ) / (2 * Real.log N) ≤ ((paperWoldPrimeIndices (2 * N)).card : ℝ) := by
  have h2 : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun N => by change N ≤ 2 * N; omega) tendsto_id
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [paperWoldPrimeIndices_eventual_card, h2.eventually paperWoldPrimeIndices_eventual_card,
    eventually_ge_atTop 2, hl.eventually (eventually_ge_atTop 64)] with N hN h2N hN2 hlog
  refine ⟨hN2, hlog, hN, ?_⟩
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNp : (0 : ℝ) < N := by linarith
  have hlp : 0 < Real.log (N : ℝ) := by linarith
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  have hlogmul : Real.log ((2 * N : ℕ) : ℝ) = Real.log 2 + Real.log N := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNp.ne']
  have hlogmulpos : 0 < Real.log ((2 * N : ℕ) : ℝ) := by
    rw [hlogmul]
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  apply le_trans _ h2N
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.log (N : ℝ))
    (mul_pos (by norm_num) hlogmulpos)).mpr
  rw [hlogmul]
  push_cast
  nlinarith

end
end RHTower
