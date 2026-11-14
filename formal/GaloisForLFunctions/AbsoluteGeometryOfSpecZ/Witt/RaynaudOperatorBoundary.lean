import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheGhostRingOfTheArithmeticSquare

/-!
# The Raynaud relation on integral big-Witt ghosts

The arithmetic ghost ring satisfies `F_k V_k = k`, but its reverse composite
is multiplication by `k` followed by the mask of indices divisible by `k`.
Consequently `V_k F_k = k` holds precisely on ghosts supported on those indices,
and globally only for `k = 1`. Verschiebung has no power torsion, whereas every
nonidentity Frobenius has a nonzero kernel.

This identifies the exact applicability boundary for the two-sided operator
relations used in Yang's Hodge--Witt finite-torsion comparisons.
-/

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The reverse composite retains exactly the coordinates divisible by its degree. -/
theorem verschiebung_frobenius_apply (k n : ℕ+) (x : ghostRing) :
    (verschiebung k (frobenius k x)).1 n =
      if (k : ℕ) ∣ n then (k : ℤ) * x.1 n else 0 := by
  rw [verschiebung_apply]
  split_ifs with h
  · rw [frobenius_apply, PNat.mul_div_exact (PNat.dvd_iff.mpr h)]
  · rfl

/-- Exact locus of the second Raynaud relation inside the arithmetic ghost ring. -/
theorem verschiebung_frobenius_eq_smul_iff (k : ℕ+) (x : ghostRing) :
    verschiebung k (frobenius k x) = (k : ℤ) • x ↔
      ∀ n : ℕ+, ¬ (k : ℕ) ∣ n → x.1 n = 0 := by
  constructor
  · intro h n hn
    have he := congrArg (fun z : ghostRing => z.1 n) h
    rw [verschiebung_frobenius_apply, if_neg hn] at he
    change 0 = (k : ℤ) * x.1 n at he
    exact (mul_eq_zero.mp he.symm).resolve_left (Int.natCast_ne_zero.mpr k.ne_zero)
  · intro h
    apply ghostRing_ext
    intro n
    change (verschiebung k (frobenius k x)).1 n = (k : ℤ) * x.1 n
    rw [verschiebung_frobenius_apply]
    split_ifs with hn
    · rfl
    · rw [h n hn, mul_zero]

/-- The second Raynaud relation holds on the whole image of Verschiebung. -/
theorem verschiebung_frobenius_on_range (k : ℕ+) (x : ghostRing) :
    verschiebung k (frobenius k (verschiebung k x)) =
      (k : ℤ) • verschiebung k x := by
  rw [frobenius_verschiebung, map_zsmul]

/-- Integral big-Witt Verschiebung is injective in every positive degree. -/
theorem ghost_verschiebung_injective (k : ℕ+) : Function.Injective (verschiebung k) := by
  intro x y h
  have hf := congrArg (frobenius k) h
  rw [frobenius_verschiebung, frobenius_verschiebung] at hf
  apply ghostRing_ext
  intro n
  have hn := congrArg (fun z : ghostRing => z.1 n) hf
  change (k : ℤ) * x.1 n = (k : ℤ) * y.1 n at hn
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr k.ne_zero) hn

/-- No nonzero arithmetic ghost is killed by any Verschiebung iterate. -/
theorem ghost_verschiebung_iterate_eq_zero_iff (k : ℕ+) (n : ℕ) (x : ghostRing) :
    (verschiebung k)^[n] x = 0 ↔ x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      constructor
      · intro h
        apply ih.mp
        exact ghost_verschiebung_injective k (h.trans (map_zero (verschiebung k)).symm)
      · intro h
        rw [ih.mpr h, map_zero]

/-- An explicit ghost in the kernel of Frobenius. -/
def frobeniusKernelGhost (k : ℕ+) : ghostRing := orbit k - (k : ℤ) • 1

theorem frobenius_frobeniusKernelGhost (k : ℕ+) :
    frobenius k (frobeniusKernelGhost k) = 0 := by
  rw [frobeniusKernelGhost, map_sub, orbit, frobenius_verschiebung,
    map_zsmul, map_one, sub_self]

/-- The explicit Frobenius-kernel ghost vanishes exactly in degree one. -/
theorem frobeniusKernelGhost_eq_zero_iff (k : ℕ+) :
    frobeniusKernelGhost k = 0 ↔ k = 1 := by
  constructor
  · intro h
    by_contra hk
    have hkd : ¬ (k : ℕ) ∣ (1 : ℕ) := by
      intro hd
      apply hk
      exact PNat.coe_injective (Nat.dvd_one.mp hd)
    have he := congrArg (fun x : ghostRing => x.1 1) h
    change (orbit k).1 1 - (k : ℤ) * 1 = 0 at he
    rw [orbit_apply] at he
    change (if (k : ℕ) ∣ 1 then (k : ℤ) else 0) - (k : ℤ) * 1 = 0 at he
    rw [if_neg hkd, mul_one, zero_sub, neg_eq_zero] at he
    exact (Int.natCast_ne_zero.mpr k.ne_zero) he
  · rintro rfl
    apply ghostRing_ext
    intro n
    change (orbit 1).1 n - (1 : ℤ) * 1 = 0
    simp [orbit_apply]

/-- Frobenius is injective exactly for the identity degree. -/
theorem ghost_frobenius_injective_iff (k : ℕ+) :
    Function.Injective (frobenius k) ↔ k = 1 := by
  constructor
  · intro h
    apply (frobeniusKernelGhost_eq_zero_iff k).mp
    apply h
    rw [frobenius_frobeniusKernelGhost, map_zero]
  · rintro rfl
    intro x y h
    simpa only [frobenius_one] using h

/-- The two Frobenius--Verschiebung composites agree globally only in degree one. -/
theorem ghost_frobenius_verschiebung_commute_iff (k : ℕ+) :
    (∀ x : ghostRing, verschiebung k (frobenius k x) = frobenius k (verschiebung k x)) ↔
      k = 1 := by
  constructor
  · intro h
    apply (frobeniusKernelGhost_eq_zero_iff k).mp
    change orbit k - (k : ℤ) • 1 = 0
    apply sub_eq_zero.mpr
    simpa only [map_one, frobenius_verschiebung, orbit] using h 1
  · rintro rfl
    intro x
    rw [frobenius_one, frobenius_one]

#print axioms verschiebung_frobenius_eq_smul_iff
#print axioms verschiebung_frobenius_on_range
#print axioms ghost_verschiebung_iterate_eq_zero_iff
#print axioms ghost_frobenius_injective_iff
#print axioms ghost_frobenius_verschiebung_commute_iff

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
