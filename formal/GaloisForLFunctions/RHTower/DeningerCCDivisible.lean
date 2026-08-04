import GaloisForLFunctions.RHTower.DeningerCCTrajectory

/-!
# The colimit of the tower is divisible

A schedule which visits every enumeration index with every admissible exponent arbitrarily late
makes the colimit divisible: an element of the colimit comes from a stage, is enumerated there by an
index of an earlier block, and that index denotes its image at every later stage, so at a stage
where the schedule visits that index with the wanted exponent the image acquires the root, and the
structure maps carry the root back to the colimit.

* `deningerCCSched` : the fair schedule.
* `deningerCCColimit_divisible` : divisibility of the colimit.
-/

namespace RHTower

open CategoryTheory Monoid

universe u

namespace RootAdjunction

open scoped Classical

/-- An enumeration of the pairs of an index and an exponent. -/
noncomputable def deningerCCPairs : ℕ → ℕ × ℤ :=
  Classical.choose (exists_surjective_nat (ℕ × ℤ))

theorem deningerCCPairs_surjective : Function.Surjective deningerCCPairs :=
  Classical.choose_spec (exists_surjective_nat (ℕ × ℤ))

/-- **The fair schedule**: the pair enumerated by the second component of the index, with the
exponent corrected to an admissible one. -/
noncomputable def deningerCCSched (k : ℕ) : ℕ × ℤ :=
  ((deningerCCPairs (Nat.unpair k).2).1,
    if 2 ≤ (deningerCCPairs (Nat.unpair k).2).2.natAbs
      then (deningerCCPairs (Nat.unpair k).2).2 else 2)

/-- **The exponents of the fair schedule are admissible.** -/
theorem deningerCCSched_exp (k : ℕ) : 2 ≤ (deningerCCSched k).2.natAbs := by
  rw [deningerCCSched]
  split
  · assumption
  · omega

/-- **The fair schedule visits every index with every admissible exponent arbitrarily late.** -/
theorem deningerCCSched_fair (p : ℕ) (N : ℤ) (hN : 2 ≤ N.natAbs) (n : ℕ) :
    ∃ k : ℕ, n ≤ k ∧ deningerCCSched k = (p, N) := by
  obtain ⟨i, hi⟩ := deningerCCPairs_surjective (p, N)
  refine ⟨Nat.pair n i, Nat.left_le_pair n i, ?_⟩
  rw [deningerCCSched, Nat.unpair_pair, hi]
  simp [hN]

/-- **The colimit of the tower over the fair schedule is divisible.** -/
theorem deningerCCColimit_divisible (S₀ : DeningerCCStage.{u}) (hgood : DeningerCCGood S₀)
    (h₀ : ∀ w : S₀.carrier, ∃ p : ℕ, (Nat.unpair p).1 = 0 ∧ S₀.hist p = w)
    (x : deningerCCColimit S₀ deningerCCSched) (N : ℤ) (hN : N ≠ 0) :
    ∃ y : deningerCCColimit S₀ deningerCCSched, y ^ N = x := by
  rcases lt_or_ge N.natAbs 2 with hsmall | hbig
  · -- the exponent is a unit
    rcases Int.natAbs_eq N with h | h
    · refine ⟨x, ?_⟩
      rw [show N = 1 by omega, zpow_one]
    · refine ⟨x⁻¹, ?_⟩
      rw [show N = -1 by omega, zpow_neg, zpow_one, inv_inv]
  · obtain ⟨n, a, ha⟩ := deningerCCColimit_surjective S₀ deningerCCSched x
    obtain ⟨p, hp, hpa⟩ := deningerCCTower_hist_bound S₀ deningerCCSched deningerCCSched_exp
      hgood h₀ n a
    obtain ⟨k, hk, hsched⟩ := deningerCCSched_fair p N hbig n
    obtain ⟨y', hy'⟩ := deningerCCEmbed_root S₀ deningerCCSched deningerCCSched_exp hgood k
    refine ⟨deningerCCIota S₀ deningerCCSched (k + 1) y', ?_⟩
    have hp1 : (deningerCCSched k).1 = p := by rw [hsched]
    have hp2 : (deningerCCSched k).2 = N := by rw [hsched]
    rw [hp1, hp2] at hy'
    calc (deningerCCIota S₀ deningerCCSched (k + 1) y') ^ N
        = deningerCCIota S₀ deningerCCSched (k + 1) (y' ^ N) := (map_zpow _ _ _).symm
      _ = deningerCCIota S₀ deningerCCSched (k + 1)
            (deningerCCEmbed S₀ deningerCCSched k
              ((deningerCCTower S₀ deningerCCSched k).hist p)) := by rw [hy']
      _ = deningerCCIota S₀ deningerCCSched k
            ((deningerCCTower S₀ deningerCCSched k).hist p) :=
          deningerCCIota_step S₀ deningerCCSched k _
      _ = deningerCCIota S₀ deningerCCSched k (deningerCCMap S₀ deningerCCSched hk
            ((deningerCCTower S₀ deningerCCSched n).hist p)) := by
          rw [← deningerCCTower_hist_map S₀ deningerCCSched p n hp k hk]
      _ = deningerCCIota S₀ deningerCCSched n ((deningerCCTower S₀ deningerCCSched n).hist p) :=
          deningerCCIota_map S₀ deningerCCSched hk _
      _ = x := by rw [hpa, ha]

end RootAdjunction

end RHTower
