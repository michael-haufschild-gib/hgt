import GaloisForLFunctions.Bottcher.ConnectedRepellingRootDefect

open Polynomial Filter Topology Set Metric

namespace Bottcher

/-- Eventual bounded root defect plus eventual bounded non-strong count implies the strong-root pool
is frequently larger than every finite threshold.  This is the direct counting bridge into the
unbounded-strong-root hRigid input. -/
theorem frequently_strongFixedPointRoots_card_gt_of_eventually_rootDefect_nonStrong_card_le
    (c : ℂ) (D N : ℕ)
    (hrootDefect : ∀ᶠ p : ℕ in atTop,
      2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + D)
    (hN : ∀ᶠ p : ℕ in atTop, (nonStrongFixedPointRoots c p).card ≤ N) :
    ∀ A : ℕ, ∃ᶠ p : ℕ in atTop, A < (strongFixedPointRoots c p).card := by
  intro A
  have htwo : Tendsto (fun p : ℕ => 2 ^ p) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (show 1 < (2 : ℕ) by norm_num)
  have hbig : ∀ᶠ p : ℕ in atTop, A + N + D < 2 ^ p :=
    htwo.eventually_gt_atTop (A + N + D)
  have hev : ∀ᶠ p : ℕ in atTop, A < (strongFixedPointRoots c p).card := by
    filter_upwards [hrootDefect, hN, hbig] with p hdef hNcard hbigp
    have hsplit :=
      strongFixedPointRoots_card_add_nonStrongFixedPointRoots_card_eq_roots_card c p
    rw [← hsplit] at hdef
    omega
  exact hev.frequently

/-- Eventual duplicate-excess bounds plus eventual bounded non-strong count imply the unbounded
strong-root input. -/
theorem frequently_strongFixedPointRoots_card_gt_of_eventually_roots_count_excess_nonStrong_card_le
    (c : ℂ) (D N : ℕ)
    (hD : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
      (∑ z ∈ (fixedPointPoly c p).roots.toFinset,
        ((fixedPointPoly c p).roots.count z - 1)) ≤ D)
    (hN : ∀ᶠ p : ℕ in atTop, (nonStrongFixedPointRoots c p).card ≤ N) :
    ∀ A : ℕ, ∃ᶠ p : ℕ in atTop, A < (strongFixedPointRoots c p).card :=
  frequently_strongFixedPointRoots_card_gt_of_eventually_rootDefect_nonStrong_card_le
    c D N
    (eventually_fixedPointPoly_rootDefect_bound_of_eventually_roots_count_excess_le c D hD)
    hN

/-- Eventual finite multiplier-one support with local duplicate-excess bounds, together with eventual
bounded non-strong count, implies the unbounded strong-root input. -/
theorem frequently_strongFixedPointRoots_card_gt_of_eventually_multiplierOne_subset_nonStrong_card_le
    (c : ℂ) (F : Finset ℂ) (L N : ℕ)
    (hmultiplierOne : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
      multiplierOneFixedPointRoots c p ⊆ F ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ F →
        (fixedPointPoly c p).roots.count z - 1 ≤ L))
    (hN : ∀ᶠ p : ℕ in atTop, (nonStrongFixedPointRoots c p).card ≤ N) :
    ∀ A : ℕ, ∃ᶠ p : ℕ in atTop, A < (strongFixedPointRoots c p).card :=
  frequently_strongFixedPointRoots_card_gt_of_eventually_rootDefect_nonStrong_card_le
    c (F.card * L) N
    (eventually_fixedPointPoly_rootDefect_bound_of_eventually_multiplierOne_subset
      c F L hmultiplierOne)
    hN

end Bottcher
