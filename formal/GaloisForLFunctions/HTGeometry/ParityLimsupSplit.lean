import GaloisForLFunctions.HTGeometry.LimsupUnitFactor

/-!
# Splitting the growth functional along parities

Every tail of the natural numbers contains all large even numbers and all large
odd numbers, and conversely a set containing both is a tail.  So `atTop` is the
supremum of the two pushforward filters, and in the extended non-negative reals —
a complete lattice, where `limsup` distributes over a supremum of filters — the
growth functional splits as the maximum of its even and odd parts.

This is what a shift lattice of degree two needs: its coefficients are given by
one formula at even indices and another at odd indices, so the two root `limsup`s
must be computed separately and then combined.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

section ParitySplit

/-- **`atTop` is the supremum of the even and odd pushforwards.** -/
theorem atTop_eq_sup_parity :
    (atTop : Filter ℕ)
      = map (fun m : ℕ => 2 * m) atTop ⊔ map (fun m : ℕ => 2 * m + 1) atTop := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro s hs
    rw [Filter.mem_sup] at hs
    obtain ⟨hs1, hs2⟩ := hs
    rw [Filter.mem_map, Filter.mem_atTop_sets] at hs1 hs2
    obtain ⟨M₁, hM₁⟩ := hs1
    obtain ⟨M₂, hM₂⟩ := hs2
    rw [Filter.mem_atTop_sets]
    refine ⟨2 * (max M₁ M₂) + 1, fun n hn => ?_⟩
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hmge : M₁ ≤ m := by omega
      have := hM₁ m hmge
      simpa [hm, two_mul] using this
    · have hmge : M₂ ≤ m := by omega
      have := hM₂ m hmge
      simpa [hm] using this
  · exact tendsto_atTop_mono (fun m => by show m ≤ 2 * m; omega) tendsto_id
  · exact tendsto_atTop_mono (fun m => by show m ≤ 2 * m + 1; omega) tendsto_id

theorem limsup_map_comp {α : Type*} [CompleteLattice α] (G : ℕ → α) (f : ℕ → ℕ) :
    limsup G (map f atTop) = limsup (fun m => G (f m)) atTop := by
  rw [Filter.limsup, Filter.limsup, Filter.map_map]
  rfl

/-- **The growth functional is the larger of its two parity parts.** -/
theorem hadamardLimsup_eq_parity_sup (c : ℕ → ℂ) :
    hadamardLimsup c
      = limsup (fun m : ℕ =>
          ((‖c (2 * m)‖₊ ^ (1 / ((2 * m : ℕ) : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop
        ⊔ limsup (fun m : ℕ =>
          ((‖c (2 * m + 1)‖₊ ^ (1 / ((2 * m + 1 : ℕ) : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop := by
  set G : ℕ → ℝ≥0∞ := fun n => ((‖c n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞) with hG
  have hstep : hadamardLimsup c = limsup G (map (fun m : ℕ => 2 * m) atTop
      ⊔ map (fun m : ℕ => 2 * m + 1) atTop) := by
    rw [hadamardLimsup, ← hG]
    congr 1
    exact atTop_eq_sup_parity
  rw [hstep, limsup_sup_filter, limsup_map_comp, limsup_map_comp]

end ParitySplit

section Transfer

/-- The extended-real image of a bounded real `limsup`. -/
theorem limsup_ofReal_eq {h : ℕ → ℝ} (hnn : ∀ m, 0 ≤ h m)
    (hbdd : IsBoundedUnder (· ≤ ·) atTop h) :
    limsup (fun m : ℕ => ENNReal.ofReal (h m)) atTop
      = ENNReal.ofReal (limsup h atTop) := by
  have hmono : Monotone ENNReal.ofReal := fun _ _ hle => ENNReal.ofReal_le_ofReal hle
  have hcob : IsCoboundedUnder (· ≤ ·) atTop h := by
    refine IsBoundedUnder.isCoboundedUnder_le ⟨0, ?_⟩
    rw [Filter.eventually_map]
    exact Filter.Eventually.of_forall hnn
  have hmap := hmono.map_limsup_of_continuousAt h
    ENNReal.continuous_ofReal.continuousAt hbdd hcob
  rw [hmap]
  rfl

/-- The root sequence in extended non-negative reals is the image of the real one. -/
theorem coe_nnnorm_rpow_eq_ofReal (z : ℂ) (p : ℝ) :
    ((‖z‖₊ ^ p : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (‖z‖ ^ p) := by
  have h1 : ((‖z‖₊ ^ p : ℝ≥0) : ℝ) = ‖z‖ ^ p := by
    rw [NNReal.coe_rpow, coe_nnnorm]
  rw [← h1, ENNReal.ofReal_coe_nnreal]

end Transfer

end GaloisForLFunctions.HTGeometry
