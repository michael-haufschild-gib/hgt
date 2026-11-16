import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheTeichmullerPointsAndTheLatticeOfSections

/-!
# Opposite eigenvalues and primitive ghost coordinates

Pairing `a` and `-a` removes every odd trace and equals the Verschiebung
of the squared eigenvalue. Necklace coordinates are additive, and
Verschiebung shifts their indices exactly. Together these give an integral
parity identity for primitive coordinates, following the signed trace
mechanism in Zehavi, Proposition 4.16, arXiv:2611.18218.
-/

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open Finset

/-- Necklace coordinates turn addition of ghost sequences into addition of primitive counts. -/
theorem coord_add (x y : ghostRing) (n : ℕ+) :
    coord (x + y) n = coord x n + coord y n := by
  apply necklace_unique (b := coord (x + y)) (b' := fun d => coord x d + coord y d) _ n n.ne_zero
  intro m hm
  let M : ℕ+ := ⟨m, Nat.pos_of_ne_zero hm⟩
  have hxy := ghostComponent_eq_sum_coord (x + y) M
  have hx := ghostComponent_eq_sum_coord x M
  have hy := ghostComponent_eq_sum_coord y M
  simpa only [map_add, hx, hy, Finset.sum_add_distrib, mul_add] using hxy.symm

private theorem sum_divisors_multiple (k n : ℕ+) (b : ℕ → ℤ) :
    (∑ d ∈ ((k : ℕ) * n).divisors,
      if (k : ℕ) ∣ d then (d : ℤ) * b (d / k) else 0) =
        ((k : ℕ) : ℤ) * ∑ d ∈ (n : ℕ).divisors, (d : ℤ) * b d := by
  rw [← Finset.sum_filter, Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun d _ => (k : ℕ) * d)
  · intro d hd
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨Nat.mul_dvd_mul_left k (Nat.mem_divisors.mp hd).1, Nat.mul_ne_zero k.ne_zero n.ne_zero⟩,
      dvd_mul_right _ _⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left k.pos hab
  · intro d hd
    obtain ⟨hdn, hkd⟩ := Finset.mem_filter.mp hd
    obtain ⟨q, rfl⟩ := hkd
    refine ⟨q, Nat.mem_divisors.mpr ⟨?_, n.ne_zero⟩, rfl⟩
    exact Nat.dvd_of_mul_dvd_mul_left k.pos (Nat.mem_divisors.mp hdn).1
  · intro d _
    rw [Nat.mul_div_cancel_left _ k.pos, Nat.cast_mul]
    ring

/-- Verschiebung moves primitive coordinates to divisible indices without multiplying them. -/
theorem coord_verschiebung (k : ℕ+) (x : ghostRing) (n : ℕ+) :
    coord (verschiebung k x) n = if (k : ℕ) ∣ n then coord x ((n : ℕ) / k) else 0 := by
  apply necklace_unique (b := coord (verschiebung k x))
    (b' := fun d => if (k : ℕ) ∣ d then coord x (d / k) else 0) _ n n.ne_zero
  intro m hm
  let M : ℕ+ := ⟨m, Nat.pos_of_ne_zero hm⟩
  rw [← ghostComponent_eq_sum_coord (verschiebung k x) M]
  change (verschiebung k x).val M = _
  simp_rw [mul_ite, mul_zero]
  by_cases hkM : (k : ℕ) ∣ M
  · obtain ⟨N, hN⟩ := PNat.dvd_iff.mpr hkM
    change M = k * N at hN
    have hm' : m = (k : ℕ) * N := congrArg PNat.val hN
    change (verschiebungFun k x.val) M = _
    rw [hN, verschiebungFun_mul, hm', sum_divisors_multiple]
    rw [← ghostComponent_eq_sum_coord x N]
    rfl
  · rw [verschiebung_apply, if_neg hkM]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    apply if_neg
    intro hkd
    exact hkM (dvd_trans hkd (Nat.mem_divisors.mp hd).1)

/-- Opposite Teichmüller points form the double cover of the squared point. -/
theorem teichmuller_add_neg (a : ℤ) :
    teichmuller a + teichmuller (-a) = verschiebung 2 (teichmuller (a ^ 2)) := by
  apply ghostRing_ext
  intro n
  rw [map_add, ghostComponent_teichmuller, ghostComponent_teichmuller]
  change _ = (verschiebung 2 (teichmuller (a ^ 2))).val n
  by_cases hn : 2 ∣ (n : ℕ)
  · obtain ⟨m, hm⟩ := PNat.dvd_iff.mpr hn
    rw [hm]
    change a ^ (2 * (m : ℕ)) + (-a) ^ (2 * (m : ℕ)) =
      (verschiebungFun 2 (teichmuller (a ^ 2)).val) (2 * m)
    rw [verschiebungFun_mul, teichmuller_apply, pow_mul, pow_mul]
    ring
  · rw [verschiebung_apply, if_neg hn]
    have ho : Odd (n : ℕ) := Nat.odd_iff_not_even.mpr (by simpa only [even_iff_two_dvd] using hn)
    rw [ho.neg_pow]
    exact add_neg_cancel _

/-- The primitive contribution of opposite eigenvalues is exactly a shifted squared contribution. -/
theorem opposite_necklace_coordinates (a : ℤ) (n : ℕ+) :
    coord (teichmuller a) n + coord (teichmuller (-a)) n =
      if 2 ∣ (n : ℕ) then coord (teichmuller (a ^ 2)) ((n : ℕ) / 2) else 0 := by
  rw [← coord_add, teichmuller_add_neg, coord_verschiebung]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.coord_add
#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.coord_verschiebung
#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.opposite_necklace_coordinates
