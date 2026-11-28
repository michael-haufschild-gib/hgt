import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! The full cycle partition includes the fixed points.
A permutation with prescribed partition has the reciprocal
of its centralizer order as its probability. -/

noncomputable section

open Finset Equiv

namespace WindowedLandauTheory.ConcN

/-- The probability of a given permutation partition under the uniform measure. -/
theorem partition_probability (N : ℕ) (m : Multiset ℕ)
    (hm : ∀ d ∈ m, 1 ≤ d) (hs : m.sum = N) :
    (((univ : Finset (Perm (Fin N))).filter (fun σ => σ.partition.parts = m)).card : ℝ) /
      N.factorial = ∏ d ∈ m.toFinset, ((d : ℝ) ^ m.count d * (m.count d).factorial)⁻¹ := by
  let u := m.filter (fun d => 2 ≤ d)
  let v := m.filter (fun d => ¬ 2 ≤ d)
  have huv : u + v = m := Multiset.filter_add_not _ _
  have hu (d : ℕ) (hd : d ∈ u) : 2 ≤ d := (Multiset.mem_filter.mp hd).2
  have hvm (d : ℕ) (hd : d ∈ v) : d = 1 := by
    obtain ⟨h, hd'⟩ := Multiset.mem_filter.mp hd
    have := hm d h
    omega
  have hv : v = Multiset.replicate (m.count 1) 1 := by
    have hv1 : v.count 1 = m.count 1 := Multiset.count_filter_of_pos (by omega)
    have he := Multiset.eq_replicate_card.mpr hvm
    rw [he, Multiset.count_replicate_self] at hv1
    rwa [← hv1]
  have hsum : u.sum + m.count 1 = N := by
    have h := congrArg Multiset.sum huv
    simpa only [Multiset.sum_add, hv, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, mul_one, hs] using h
  have hprod : m.prod = u.prod := by
    rw [← huv, Multiset.prod_add, hv, Multiset.prod_replicate, one_pow, mul_one]
  have hU : u.toFinset = m.toFinset.erase 1 := by
    ext d
    simp only [u, Multiset.mem_toFinset, Multiset.mem_filter, Finset.mem_erase]
    exact ⟨fun h => ⟨by omega, h.1⟩, fun h => ⟨h.2, by have := hm d h.2; omega⟩⟩
  have hmul :
      (∏ d ∈ m.toFinset, (m.count d).factorial) =
        (m.count 1).factorial * ∏ d ∈ u.toFinset, (u.count d).factorial := by
    have he : ∏ d ∈ u.toFinset, (u.count d).factorial =
        ∏ d ∈ m.toFinset.erase 1, (m.count d).factorial := by
      refine Finset.prod_congr hU fun d hd => ?_
      rw [show u.count d = m.count d from
        Multiset.count_filter_of_pos (hu d (Multiset.mem_toFinset.mp (hU.symm ▸ hd)))]
    rw [he]
    by_cases h1 : 1 ∈ m.toFinset
    · exact (Finset.mul_prod_erase _ _ h1).symm
    · rw [Finset.erase_eq_of_notMem h1]
      have hz : m.count 1 = 0 := Multiset.count_eq_zero.mpr (by simpa using h1)
      simp [hz]

  have hsets : ((univ : Finset (Perm (Fin N))).filter fun σ => σ.partition.parts = m) =
      univ.filter (fun σ : Perm (Fin N) => σ.cycleType = u) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      change σ.cycleType = m.filter (fun d => 2 ≤ d)
      rw [← h, Perm.filter_parts_partition_eq_cycleType]
    · intro h
      rw [Perm.parts_partition, ← Perm.sum_cycleType, Fintype.card_fin, h, ← huv, hv,
        show N - u.sum = m.count 1 by omega]

  have hcard := Perm.card_of_cycleType_mul_eq (Fin N) u
  rw [Fintype.card_fin, if_pos ⟨by omega, hu⟩, ← hsets,
    show N - u.sum = m.count 1 by omega] at hcard
  have hcentral : (m.count 1).factorial * u.prod *
      (∏ d ∈ u.toFinset, (u.count d).factorial) =
      ∏ d ∈ m.toFinset, (d ^ m.count d * (m.count d).factorial) := by
    rw [Finset.prod_mul_distrib, ← Finset.prod_multiset_count, hprod, hmul]
    ac_rfl
  rw [hcentral] at hcard
  have hc : (((univ : Finset (Perm (Fin N))).filter (fun σ => σ.partition.parts = m)).card : ℝ) *
      (∏ d ∈ m.toFinset, ((d : ℝ) ^ m.count d * (m.count d).factorial)) = N.factorial := by
    exact_mod_cast hcard
  have hp : 0 < ∏ d ∈ m.toFinset, ((d : ℝ) ^ m.count d * (m.count d).factorial) := by
    apply Finset.prod_pos
    intro d hd
    have : 0 < (d : ℝ) := by exact_mod_cast hm d (Multiset.mem_toFinset.mp hd)
    positivity
  have hn : 0 < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  rw [Finset.prod_inv_distrib, inv_eq_one_div, div_eq_div_iff hn.ne' hp.ne', one_mul]
  exact hc

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.partition_probability
