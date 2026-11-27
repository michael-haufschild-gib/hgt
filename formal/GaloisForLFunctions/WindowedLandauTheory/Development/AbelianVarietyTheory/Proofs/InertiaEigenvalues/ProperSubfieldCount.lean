import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenLabelRoots

/-! A finite field of degree d has few nonzero elements in proper
subfields: each such element has degree at most d/2. -/

noncomputable section
open Polynomial WindowedLandauTheory.CyclotomicNorms
open scoped Classical

namespace GlobalTheory.GreenExists

private theorem geometric_bound {g : ℕ} (hg : 5 ≤ g) (m : ℕ) :
    4 * (∑ e ∈ Finset.range m, (g ^ (e + 1) - 1)) + 4 * m + 5 ≤ 5 * g ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hp : 0 < g ^ (m + 1) := pow_pos (by omega) _
    have hq : 5 * g ^ m ≤ g ^ (m + 1) := by
      rw [pow_succ, mul_comm 5]
      exact Nat.mul_le_mul_left _ hg
    omega

private theorem linear_bound {g : ℕ} (hg : 5 ≤ g) (m : ℕ) :
    5 * (m + 1) ≤ g ^ (m + 1) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
    have h : g ^ (m + 1) * 5 ≤ g ^ (m + 1 + 1) := by
      rw [pow_succ g (m + 1)]
      exact Nat.mul_le_mul_left _ hg
    omega

private theorem geometric_bound_even {g : ℕ} (hg : 5 ≤ g) (m : ℕ) :
    4 * (m + 1) * (∑ e ∈ Finset.range (m + 1), (g ^ (e + 1) - 1)) + 1 <
      g ^ (2 * (m + 1)) := by
  set T := ∑ e ∈ Finset.range (m + 1), (g ^ (e + 1) - 1)
  set q := g ^ (m + 1)
  have h₁ : 4 * T + 4 * (m + 1) + 5 ≤ 5 * q := geometric_bound hg (m + 1)
  have h₂ : 5 * (m + 1) ≤ q := linear_bound hg m
  have h₃ := Nat.mul_le_mul_left (m + 1) h₁
  have h₄ := Nat.mul_le_mul_right q h₂
  have hmargin := Nat.mul_le_mul_left (m + 1) (show 2 ≤ 4 * (m + 1) + 5 by omega)
  rw [two_mul, pow_add]
  change 4 * (m + 1) * T + 1 < q * q
  nlinarith only [h₃, h₄, hmargin, Nat.zero_le m]

private theorem proper_subfield_sum_lt {g d : ℕ} (hg : 5 ≤ g) (hd : 0 < d) :
    2 * d * (∑ e ∈ Finset.range (d / 2), (g ^ (e + 1) - 1)) < g ^ d - 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' d
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
    rw [show 2 * (t + 1) / 2 = t + 1 by omega,
      show 2 * (2 * (t + 1)) = 4 * (t + 1) by omega]
    exact Nat.lt_sub_of_add_lt (geometric_bound_even hg t)
  · cases m with
    | zero => simp; omega
    | succ t =>
      rw [show (2 * (t + 1) + 1) / 2 = t + 1 by omega, pow_succ g (2 * (t + 1))]
      set T := ∑ e ∈ Finset.range (t + 1), (g ^ (e + 1) - 1)
      set q := g ^ (2 * (t + 1))
      have h : 4 * (t + 1) * T + 1 < q := geometric_bound_even hg t
      have h₁ := Nat.mul_le_mul_right T
        (show 2 * (2 * (t + 1) + 1) ≤ 2 * (4 * (t + 1)) by omega)
      have h₂ := Nat.mul_le_mul_left q (show 2 ≤ g by omega)
      apply Nat.lt_sub_of_add_lt
      calc
        _ ≤ (2 * (4 * (t + 1))) * T + 1 := Nat.add_le_add_right h₁ 1
        _ ≤ 2 * (4 * (t + 1) * T + 1) := by
          rw [mul_add, mul_assoc 2]
          omega
        _ < q * 2 := by
          rw [mul_comm q]
          exact Nat.mul_lt_mul_of_pos_left h (by omega)
        _ ≤ _ := h₂

/-- Nonzero elements of smaller degree in the field of size g^d occupy
fewer than one part in 2d of its multiplicative group when g is at least five. -/
theorem card_properSubfield_elements_lt (g d : ℕ) [Fact g.Prime] (hg : 5 ≤ g) (hd : 0 < d) :
    2 * d * Nat.card {z : Fbar g // z ≠ 0 ∧ z ^ g ^ d = z ∧ (minpoly (ZMod g) z).natDegree ≠ d} <
      g ^ d - 1 := by
  let S : Set (Fbar g) := {z | z ≠ 0 ∧ z ^ g ^ d = z ∧ (minpoly (ZMod g) z).natDegree ≠ d}
  let F := (Finset.range (d / 2)).biUnion fun e =>
    (nthRoots (g ^ (e + 1) - 1) (1 : Fbar g)).toFinset
  have hsub : S ⊆ (F : Set (Fbar g)) := by
    rintro z ⟨hz, hfix, hne⟩
    have hintegral : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
    let m := (minpoly (ZMod g) z).natDegree
    have hm : 0 < m := minpoly.natDegree_pos hintegral
    have hpow (r : ℕ) : m ∣ r ↔ z ^ g ^ r = z := by
      simpa only [Nat.card_zmod] using (CuspGL.minpoly_natDegree_dvd_iff_pow z r)
    have hfix' := (hpow m).mp dvd_rfl
    obtain ⟨j, hj⟩ := (hpow d).mpr hfix
    have hj' : 2 ≤ j := by
      rcases j with _ | _ | j
      · simp at hj
        omega
      · simp at hj
        exact (hne hj.symm).elim
      · omega
    have hm' : m * 2 ≤ d := by
      rw [hj]
      exact Nat.mul_le_mul_left m hj'
    let e := m - 1
    have he : e + 1 = m := Nat.sub_add_cancel hm
    have hgpow : 1 < g ^ (e + 1) := Nat.one_lt_pow (by omega) (by omega)
    apply Finset.mem_biUnion.mpr
    refine ⟨e, Finset.mem_range.mpr (by omega), Multiset.mem_toFinset.mpr ?_⟩
    rw [mem_nthRoots (by omega)]
    apply mul_right_cancel₀ hz
    rw [← pow_succ, one_mul, Nat.sub_add_cancel hgpow.le, he, hfix']
  have hcard : Nat.card S ≤ ∑ e ∈ Finset.range (d / 2), (g ^ (e + 1) - 1) := by
    calc
      Nat.card S = S.ncard := rfl
      _ ≤ (F : Set (Fbar g)).ncard := Set.ncard_le_ncard hsub F.finite_toSet
      _ = F.card := Set.ncard_coe_finset F
      _ ≤ _ := Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e _ =>
        (Multiset.toFinset_card_le _).trans (card_nthRoots _ _))
  exact (Nat.mul_le_mul_left (2 * d) hcard).trans_lt (proper_subfield_sum_lt hg hd)

end GlobalTheory.GreenExists
