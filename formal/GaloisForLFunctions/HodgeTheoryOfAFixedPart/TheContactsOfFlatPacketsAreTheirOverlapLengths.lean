import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheCombOfUnitMassesFixesTheContacts
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheEnergyOfAWindowIsTheJumpFormOfItsFlatPacket

/-!
# Contacts of flat packets

A contact of ratio `k` between two scaled integer windows is an
intersection of two integer intervals. Its normalized cardinality
converges to their overlap length. This gives every prime entry of
the limiting form on a fixed finite family of flat packets.
-/

open Finset Filter Topology
noncomputable section
namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart
open AbsoluteGeometryOfSpecZ

/-- Points in the first window whose ratio-`k` partners lie in the second. -/
def flatContactPoints (a b c d k N : ℕ) : Finset ℕ :=
  (Ioc (a * N) (b * N)).filter (fun m => c * N < k * m ∧ k * m ≤ d * N)

/-- The exact contact interval, including both floor corrections. -/
theorem flatContactPoints_eq (a b c d N : ℕ) {k : ℕ} (hk : 0 < k) :
    flatContactPoints a b c d k N =
      Ioc (max (a * N) (c * N / k)) (min (b * N) (d * N / k)) := by
  ext m
  simp only [flatContactPoints, mem_filter, mem_Ioc, max_lt_iff, le_min_iff,
    Nat.div_lt_iff_lt_mul hk, Nat.le_div_iff_mul_le hk]
  rw [Nat.mul_comm m k]
  tauto

private theorem natCast_sub_eq_max (a b : ℕ) :
    ((a - b : ℕ) : ℝ) = max ((a : ℝ) - b) 0 := by
  by_cases h : b ≤ a
  · rw [Nat.cast_sub h, max_eq_left (sub_nonneg.mpr (by exact_mod_cast h))]
  · have h' : a ≤ b := (lt_of_not_ge h).le
    rw [Nat.sub_eq_zero_of_le h', Nat.cast_zero,
      max_eq_right (sub_nonpos.mpr (by exact_mod_cast h'))]

private theorem natCast_sub_div (a b N : ℕ) :
    ((a - b : ℕ) : ℝ) / N = max ((a : ℝ) / N - (b : ℝ) / N) 0 := by
  rw [natCast_sub_eq_max, ← max_div_div_right (Nat.cast_nonneg N), sub_div, zero_div]

private theorem tendsto_mul_natCast_div (a : ℕ) :
    Tendsto (fun N : ℕ => ((a * N : ℕ) : ℝ) / N) atTop (𝓝 (a : ℝ)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [Nat.cast_mul]
  field_simp

private theorem tendsto_scaled_natDiv_div (a : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => ((a * N / k : ℕ) : ℝ) / N) atTop (𝓝 ((a : ℝ) / k)) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [zero_mul, Nat.zero_div, Nat.cast_zero, zero_div]
    exact tendsto_const_nhds
  · have ht : Tendsto (fun N : ℕ => a * N) atTop atTop :=
      tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N ha) tendsto_id
    have h := ((tendsto_natDiv_div hk).comp ht).const_mul (a : ℝ)
    have hv : (a : ℝ) * (1 / k) = (a : ℝ) / k := by ring
    rw [hv] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have han : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    simp only [Function.comp_apply, Nat.cast_mul]
    field_simp

/-- Every directed contact entry converges to the corresponding overlap length. -/
theorem tendsto_flatContactPoints_card_div (a b c d : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => ((flatContactPoints a b c d k N).card : ℝ) / N) atTop
      (𝓝 (max (min (b : ℝ) ((d : ℝ) / k) - max (a : ℝ) ((c : ℝ) / k)) 0)) := by
  have h := (((tendsto_mul_natCast_div b).min (tendsto_scaled_natDiv_div d hk)).sub
    ((tendsto_mul_natCast_div a).max (tendsto_scaled_natDiv_div c hk))).max tendsto_const_nhds
  apply h.congr'
  exact Eventually.of_forall fun N => by
    rw [flatContactPoints_eq a b c d N (by omega), Nat.card_Ioc, natCast_sub_div,
      Nat.cast_min, Nat.cast_max, ← min_div_div_right (Nat.cast_nonneg N),
      ← max_div_div_right (Nat.cast_nonneg N)]

/-- For one window the overlap is the positive part of `b/k-a`. -/
theorem tendsto_flatContactPoints_self_card_div (a b : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => ((flatContactPoints a b a b k N).card : ℝ) / N) atTop
      (𝓝 (max ((b : ℝ) / k - a) 0)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hkR
  have hle (x : ℕ) : (x : ℝ) / k ≤ x := by
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [Nat.cast_nonneg (α := ℝ) x, hkR]
  simpa only [min_eq_right (hle b), max_eq_left (hle a)] using
    tendsto_flatContactPoints_card_div a b a b hk

/-- A finite prime horizon can be passed through the overlap limit. -/
theorem tendsto_weighted_flatContactPoints (a b c d : ℕ) (S : Finset ℕ)
    (hS : ∀ k ∈ S, 1 ≤ k) (w : ℕ → ℝ) :
    Tendsto (fun N : ℕ => ∑ k ∈ S,
        w k * (((flatContactPoints a b c d k N).card : ℝ) / N)) atTop
      (𝓝 (∑ k ∈ S, w k *
        max (min (b : ℝ) ((d : ℝ) / k) - max (a : ℝ) ((c : ℝ) / k)) 0)) :=
  tendsto_finsetSum S fun k hk =>
    (tendsto_flatContactPoints_card_div a b c d (hS k hk)).const_mul (w k)

#print axioms tendsto_flatContactPoints_card_div
#print axioms tendsto_weighted_flatContactPoints

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
