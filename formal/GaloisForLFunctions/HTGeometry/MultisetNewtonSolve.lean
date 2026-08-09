import GaloisForLFunctions.HTGeometry.MultisetNewton
import GaloisForLFunctions.HTGeometry.MultisetSymmetricDetermination

/-!
# Newton's identity for an arbitrary multiset, solved for the elementary symmetric function

Newton's identity is available here for a family indexed by `Fin n`; every multiset is such a
family, through the enumeration by its underlying list, so the identity holds for an arbitrary
multiset.  In characteristic zero the leading coefficient `k` is invertible, so the identity
*solves* for the `k`-th elementary symmetric function in terms of the power sums of degree at most
`k` and the elementary symmetric functions of lower degree.

That solved form is what makes symmetric functions of a moving root multiset holomorphic: the power
sums are given by contour integrals, and the recursion propagates holomorphy upwards in `k`.

Power sums of every order therefore determine a multiset outright.

* `GaloisForLFunctions.multiset_newton_general`;
* `GaloisForLFunctions.multiset_esymm_eq_of_powerSum`;
* `GaloisForLFunctions.multiset_eq_of_powerSum_eq`.
-/

open Finset MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- Every multiset is the image of the universal `Finset` under the enumeration by its list. -/
theorem multiset_eq_map_univ_val {S : Type*} (M : Multiset S) :
    ∃ (n : ℕ) (f : Fin n → S), (Finset.univ.val.map f) = M := by
  classical
  refine ⟨M.toList.length, M.toList.get, ?_⟩
  have h1 : (Finset.univ : Finset (Fin M.toList.length)).val
      = (↑(List.finRange M.toList.length) : Multiset (Fin M.toList.length)) := rfl
  rw [h1]
  have h2 : ((↑(List.finRange M.toList.length) : Multiset (Fin M.toList.length)).map M.toList.get)
      = ↑((List.finRange M.toList.length).map M.toList.get) := rfl
  rw [h2, ← List.ofFn_eq_map, List.ofFn_get]
  exact M.coe_toList

/-- **Newton's identity for an arbitrary multiset.** -/
theorem multiset_newton_general {S : Type*} [CommRing S] (M : Multiset S) (k : ℕ) (hk : 0 < k) :
    (M.map (fun x => x ^ k)).sum
      = (-1) ^ (k + 1) * k * M.esymm k
        - ∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
            (-1) ^ a.1 * M.esymm a.1 * (M.map (fun x => x ^ a.2)).sum := by
  obtain ⟨n, f, hf⟩ := multiset_eq_map_univ_val M
  subst hf
  have h := multiset_newton f k hk
  have hmap : ∀ j : ℕ, (Finset.univ.val.map fun i => f i ^ j)
      = (Finset.univ.val.map f).map (fun x => x ^ j) := by
    intro j
    rw [Multiset.map_map]
    rfl
  rw [← hmap k]
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hmap a.2]

/-- **Newton's identity solved for the elementary symmetric function.**  In characteristic zero the
`k`-th elementary symmetric function of a multiset is an explicit expression in its power sums of
degree at most `k` and its elementary symmetric functions of lower degree. -/
theorem multiset_esymm_eq_of_powerSum {S : Type*} [Field S] [CharZero S] (M : Multiset S) (k : ℕ)
    (hk : 0 < k) :
    M.esymm k
      = (-1) ^ (k + 1) * (k : S)⁻¹ *
        ((M.map (fun x => x ^ k)).sum
          + ∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
              (-1) ^ a.1 * M.esymm a.1 * (M.map (fun x => x ^ a.2)).sum) := by
  have hkne : (k : S) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h := multiset_newton_general M k hk
  have hsign : ((-1 : S) ^ (k + 1)) * ((-1 : S) ^ (k + 1)) = 1 := by
    rw [← mul_pow]
    norm_num
  have hPQ : (M.map (fun x => x ^ k)).sum
      + ∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
          (-1) ^ a.1 * M.esymm a.1 * (M.map (fun x => x ^ a.2)).sum
        = (-1) ^ (k + 1) * (k : S) * M.esymm k := by
    rw [h]
    ring
  rw [hPQ]
  have hcollect : (-1 : S) ^ (k + 1) * (k : S)⁻¹ * ((-1) ^ (k + 1) * (k : S) * M.esymm k)
      = ((-1 : S) ^ (k + 1) * (-1) ^ (k + 1)) * ((k : S)⁻¹ * (k : S)) * M.esymm k := by
    ring
  rw [hcollect, hsign, inv_mul_cancel₀ hkne, one_mul, one_mul]

/-- The zeroth power sum is the cardinality. -/
theorem multiset_powerSum_zero {S : Type*} [CommRing S] (M : Multiset S) :
    (M.map (fun x => x ^ 0)).sum = (Multiset.card M : S) := by
  have hmap : M.map (fun x : S => x ^ 0) = Multiset.replicate (Multiset.card M) (1 : S) := by
    rw [← Multiset.map_const']
    exact Multiset.map_congr rfl fun x _ => pow_zero x
  rw [hmap, Multiset.sum_replicate, nsmul_eq_mul, mul_one]

/-- **Power sums of every order determine a multiset.**  The zeroth power sum is the cardinality,
Newton's identity propagates equality of the power sums to equality of the elementary symmetric
functions, and those determine the multiset as the roots of a monic polynomial. -/
theorem multiset_eq_of_powerSum_eq {S : Type*} [Field S] [CharZero S] {M N : Multiset S}
    (h : ∀ p : ℕ, (M.map (fun x => x ^ p)).sum = (N.map (fun x => x ^ p)).sum) : M = N := by
  have hcard : Multiset.card M = Multiset.card N := by
    have h0 := h 0
    rw [multiset_powerSum_zero, multiset_powerSum_zero] at h0
    exact_mod_cast h0
  have hesymm : ∀ k : ℕ, M.esymm k = N.esymm k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simp [Multiset.esymm]
      · rw [multiset_esymm_eq_of_powerSum M k hk, multiset_esymm_eq_of_powerSum N k hk, h k]
        congr 2
        refine Finset.sum_congr rfl fun a ha => ?_
        have ha1 : a.1 < k := ((Finset.mem_filter.1 ha).2).2
        rw [ih a.1 ha1, h a.2]
  exact multiset_eq_of_esymm_eq hcard fun k _ => hesymm k

end

end GaloisForLFunctions
