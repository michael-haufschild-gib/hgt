import GaloisForLFunctions.HTGeometry.WittFormationMechanics
import GaloisForLFunctions.InfiniteRankPurityTheory.AtPositiveWeightIntegralityDoesNotBoundTheRank
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.Order.Compact

/-!
# Uniform detection by the first power sums

The first `r` positive power sums of an `r`-mode packet vanish together
only at the zero packet. Compactness upgrades this algebraic reconstruction
fact to a uniform positive observation bound on the unit sphere, even
when complex cancellation makes individual power sums vanish.
Rescaling yields a global lower bound with exponent `r` near zero and
linear growth beyond the unit sphere.
-/

namespace GaloisForLFunctions.HilbertMetric.Observation

open GaloisForLFunctions.HTGeometry

/-- Total observation supplied by the first positive power sums. -/
noncomputable def finiteGhostMass {r : ℕ} (x : Fin r → ℂ) : ℝ :=
  ∑ k ∈ Finset.range r, ‖wittGhost x (k + 1)‖

/-- Cancellation cannot annihilate every one of the first `r` positive power sums. -/
theorem finiteGhostMass_eq_zero_iff {r : ℕ} (x : Fin r → ℂ) :
    finiteGhostMass x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hz : ∀ k ∈ Finset.range r, wittGhost x (k + 1) = 0 := by
      intro k hk
      have hle : ‖wittGhost x (k + 1)‖ ≤ finiteGhostMass x :=
        Finset.single_le_sum (f := fun i => ‖wittGhost x (i + 1)‖)
          (fun i _ => norm_nonneg _) hk
      rw [hx] at hle
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    have he := wittGhost_reconstructs_modes x 0 (by
      intro k hk
      cases k with
      | zero => simp [wittGhost]
      | succ k =>
        rw [hz k (Finset.mem_range.mpr (by omega))]
        simp [wittGhost])
    funext i
    have hi : x i ∈ Finset.univ.val.map x :=
      Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
    rw [he] at hi
    obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hi
    exact hj.symm
  · rintro rfl
    simp [finiteGhostMass, wittGhost]

/-- Every finite power-sum observation depends continuously on the packet. -/
theorem continuous_finiteGhostMass (r : ℕ) :
    Continuous (finiteGhostMass : (Fin r → ℂ) → ℝ) := by
  change Continuous (fun x : Fin r → ℂ =>
    ∑ k ∈ Finset.range r, ‖∑ i : Fin r, x i ^ (k + 1)‖)
  fun_prop

/-- Rescaling the packet rescales its `k`th observation by the `k`th power. -/
theorem finiteGhostMass_smul {r : ℕ} (c : ℂ) (x : Fin r → ℂ) :
    finiteGhostMass (c • x) =
      ∑ k ∈ Finset.range r, ‖c‖ ^ (k + 1) * ‖wittGhost x (k + 1)‖ := by
  unfold finiteGhostMass
  apply Finset.sum_congr rfl
  intro k _
  have he : wittGhost (c • x) (k + 1) = c ^ (k + 1) * wittGhost x (k + 1) := by
    change (∑ i : Fin r, (c * x i) ^ (k + 1)) =
      c ^ (k + 1) * ∑ i : Fin r, x i ^ (k + 1)
    simp only [mul_pow, Finset.mul_sum]
  rw [he, norm_mul, norm_pow]

/-- The smallest scaling factor among degrees one through `r` is bounded by the endpoints. -/
theorem finiteGhostMass_smul_lower {r : ℕ} (c : ℂ) (x : Fin r → ℂ) :
    min ‖c‖ (‖c‖ ^ r) * finiteGhostMass x ≤ finiteGhostMass (c • x) := by
  rw [finiteGhostMass_smul, finiteGhostMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rcases le_total ‖c‖ 1 with hc | hc
  · exact (min_le_right _ _).trans
      (pow_le_pow_of_le_one (norm_nonneg c) hc (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))
  · exact (min_le_left _ _).trans
      (by simpa using pow_le_pow_right₀ hc (Nat.succ_le_succ (Nat.zero_le k)))

/-- Every normalized packet has a uniformly detectable positive power sum. -/
theorem unitSphere_uniform_ghost_detection (r : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.sphere (0 : Fin r → ℂ) 1,
      ε ≤ finiteGhostMass x := by
  apply (isCompact_sphere (0 : Fin r → ℂ) 1).exists_forall_le'
    (continuous_finiteGhostMass r).continuousOn
  intro x hx
  have hx0 : x ≠ 0 := by
    intro he
    subst x
    simp at hx
  have hnonneg : 0 ≤ finiteGhostMass x := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  exact lt_of_le_of_ne hnonneg (Ne.symm ((finiteGhostMass_eq_zero_iff x).not.mpr hx0))

/-- A global quantitative reconstruction bound, including arbitrary complex cancellation. -/
theorem global_ghost_detection (r : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin r → ℂ,
      ε * min ‖x‖ (‖x‖ ^ r) ≤ finiteGhostMass x := by
  obtain ⟨ε, hε, h⟩ := unitSphere_uniform_ghost_detection r
  refine ⟨ε, hε, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    simp [finiteGhostMass, wittGhost]
  let y : Fin r → ℂ := (‖x‖ : ℂ)⁻¹ • x
  have hn : ‖(‖x‖ : ℂ)‖ = ‖x‖ := by simp
  have hy : y ∈ Metric.sphere (0 : Fin r → ℂ) 1 := by
    rw [Metric.mem_sphere, dist_zero_right]
    change ‖(‖x‖ : ℂ)⁻¹ • x‖ = 1
    rw [norm_smul, norm_inv, hn, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hc : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hx)
  have he : (‖x‖ : ℂ) • y = x := by
    dsimp only [y]
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  calc
    ε * min ‖x‖ (‖x‖ ^ r) ≤ finiteGhostMass y * min ‖x‖ (‖x‖ ^ r) :=
      mul_le_mul_of_nonneg_right (h y hy)
        (le_min (norm_nonneg x) (pow_nonneg (norm_nonneg x) r))
    _ ≤ finiteGhostMass x := by
      simpa only [hn, he, mul_comm] using finiteGhostMass_smul_lower (‖x‖ : ℂ) y

/-- A complete cyclic packet, with one mode at each root of unity. -/
noncomputable def cyclicGhostPacket (n : ℕ) : Fin (n + 1) → ℂ :=
  fun i => Complex.exp (2 * Real.pi * Complex.I / ((n + 1 : ℕ) : ℂ)) ^ (i : ℕ)

/-- A cyclic packet is normalized independently of its number of modes. -/
theorem norm_cyclicGhostPacket (n : ℕ) : ‖cyclicGhostPacket n‖ = 1 := by
  have hroot := (Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n)).norm'_eq_one
    (Nat.succ_ne_zero n)
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    simp only [cyclicGhostPacket, norm_pow, hroot, one_pow, le_refl]
  · simpa only [cyclicGhostPacket, Fin.val_zero, pow_zero, norm_one] using
      norm_le_pi_norm (cyclicGhostPacket n) (0 : Fin (n + 1))

/-- The full ghost sequence of a cyclic packet is the divisibility indicator. -/
theorem cyclicGhostPacket_ghost (n k : ℕ) :
    wittGhost (cyclicGhostPacket n) k = if n + 1 ∣ k then ((n + 1 : ℕ) : ℂ) else 0 := by
  change (∑ i : Fin (n + 1),
    (Complex.exp (2 * Real.pi * Complex.I / ((n + 1 : ℕ) : ℂ)) ^ (i : ℕ)) ^ k) = _
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    (Complex.exp (2 * Real.pi * Complex.I / ((n + 1 : ℕ) : ℂ)) ^ j) ^ k)]
  exact GaloisForLFunctions.InfiniteRankPurityTheory.sum_range_root_pow
    (Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n)) k

/-- The global degree exponent is attained by a whole explicit family of packets. -/
theorem cyclicGhostPacket_scaled_mass (n : ℕ) (c : ℂ) :
    finiteGhostMass (c • cyclicGhostPacket n) = ((n + 1 : ℕ) : ℝ) * ‖c‖ ^ (n + 1) := by
  rw [finiteGhostMass_smul, Finset.sum_eq_single n]
  · rw [cyclicGhostPacket_ghost]
    rw [if_pos (dvd_refl _), Complex.norm_natCast, mul_comm]
  · intro k hk hkn
    have hnd : ¬ n + 1 ∣ k + 1 := by
      intro hd
      have hle := Nat.le_of_dvd (Nat.succ_pos k) hd
      have hk' := Finset.mem_range.mp hk
      omega
    simp only [cyclicGhostPacket_ghost, if_neg hnd, norm_zero, mul_zero]
  · simp

/-- Exactly `r` positive power sums are needed to detect every `r`-mode packet. -/
theorem ghost_detection_cutoff (n m : ℕ) :
    (∀ x : Fin (n + 1) → ℂ,
      (∀ k < m, wittGhost x (k + 1) = 0) → x = 0) ↔ n + 1 ≤ m := by
  constructor
  · intro h
    by_contra hnm
    have hz := h (cyclicGhostPacket n) (by
      intro k hk
      rw [cyclicGhostPacket_ghost]
      apply if_neg
      intro hd
      have hle := Nat.le_of_dvd (Nat.succ_pos k) hd
      omega)
    have hn := norm_cyclicGhostPacket n
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  · intro hm x hx
    apply (finiteGhostMass_eq_zero_iff x).mp
    unfold finiteGhostMass
    apply Finset.sum_eq_zero
    intro k hk
    rw [hx k (lt_of_lt_of_le (Finset.mem_range.mp hk) hm), norm_zero]

end GaloisForLFunctions.HilbertMetric.Observation

#print axioms GaloisForLFunctions.HilbertMetric.Observation.finiteGhostMass_eq_zero_iff
#print axioms GaloisForLFunctions.HilbertMetric.Observation.unitSphere_uniform_ghost_detection
#print axioms GaloisForLFunctions.HilbertMetric.Observation.global_ghost_detection
#print axioms GaloisForLFunctions.HilbertMetric.Observation.cyclicGhostPacket_scaled_mass
#print axioms GaloisForLFunctions.HilbertMetric.Observation.ghost_detection_cutoff
