import GaloisForLFunctions.HTGeometry.RootBlockMomentSelection

/-!
# Assembling the vanishing micro-spectrum

`RootBlockMomentSelection` shows that one root-of-unity block writes a prescribed value into one
chosen moment, disturbs no lower one, and costs an arbitrarily small amount of Schatten `p` energy
as long as its order is below `p`.  This module runs the blocks in increasing order of degree and
assembles the full construction `(M)`: for every prescribed target for the moments
`1, …, p−1` and every energy budget there is a finite spectrum realising all of them inside the
budget.

Running the degrees in increasing order is what makes the bookkeeping finite: a block of order `k`
contributes only in degrees divisible by `k`, hence nothing at all below `k`, so at stage `k` the
residual target is already determined by the blocks already placed.

The cost identity is exponent-free.  Distributing a target `R` over `N` copies of a `k`-block of
radius `t` fixes `‖t‖^k = ‖R‖/(kN)`, so the Schatten energy is

`kN‖t‖^p = kN · ‖t‖^k · ‖t‖^{p−k} = ‖R‖ · ‖t‖^{p−k}`,

and `p − k ≥ 1`, so shrinking `t` -- that is, taking more copies -- shrinks the energy.  At `k = p`
the exponent `p − k` is zero and the mechanism disappears, which is the quantitative reason the
cutoff sits at `p − 1`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `N` copies of a root-of-unity block of order `k` and radius `t`. -/
def rootBlockMultiset (k : ℕ) (t : ℂ) (N : ℕ) : Multiset ℂ :=
  N • ((Multiset.range k).map (rootBlock k t))

theorem sum_map_pow_rootBlockMultiset {k : ℕ} (hk : k ≠ 0) (t : ℂ) (N q : ℕ) :
    ((rootBlockMultiset k t N).map (fun z => z ^ q)).sum
      = if k ∣ q then (N : ℂ) * ((k : ℂ) * t ^ q) else 0 := by
  rw [rootBlockMultiset, Multiset.map_nsmul, Multiset.sum_nsmul]
  have hbase : ((Multiset.range k).map (rootBlock k t)).map (fun z => z ^ q) =
      (Multiset.range k).map (fun r => rootBlock k t r ^ q) := by
    rw [Multiset.map_map]
    rfl
  rw [hbase]
  have hfin : ((Multiset.range k).map (fun r => rootBlock k t r ^ q)).sum
      = ∑ r ∈ Finset.range k, rootBlock k t r ^ q := rfl
  rw [hfin, sum_rootBlock_pow hk t q]
  by_cases hdvd : k ∣ q
  · rw [if_pos hdvd, if_pos hdvd, nsmul_eq_mul]
  · rw [if_neg hdvd, if_neg hdvd, smul_zero]

theorem sum_map_normPow_rootBlockMultiset {k : ℕ} (hk : k ≠ 0) (t : ℂ) (N p : ℕ) :
    ((rootBlockMultiset k t N).map (fun z => ‖z‖ ^ p)).sum = (N * k : ℕ) * ‖t‖ ^ p := by
  rw [rootBlockMultiset, Multiset.map_nsmul, Multiset.sum_nsmul]
  have hbase : ((Multiset.range k).map (rootBlock k t)).map (fun z => ‖z‖ ^ p) =
      (Multiset.range k).map (fun r => ‖rootBlock k t r‖ ^ p) := by
    rw [Multiset.map_map]
    rfl
  rw [hbase]
  have hfin : ((Multiset.range k).map (fun r => ‖rootBlock k t r‖ ^ p)).sum
      = ∑ r ∈ Finset.range k, ‖rootBlock k t r‖ ^ p := rfl
  rw [hfin]
  have hconst : ∀ r ∈ Finset.range k, ‖rootBlock k t r‖ ^ p = ‖t‖ ^ p := fun r _ => by
    rw [norm_rootBlock hk t r]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    nsmul_eq_mul]
  push_cast
  ring

/-- **One block writes one moment inside any energy budget.**  For a degree strictly below the
Schatten order, a prescribed target can be written into that single moment at arbitrarily small
Schatten energy, with no effect on any lower moment. -/
theorem exists_block_realizing {p k : ℕ} (hk : 0 < k) (hkp : k < p) (R : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Multiset ℂ,
      (∀ q, 1 ≤ q → q < k → (S.map (fun z => z ^ q)).sum = 0) ∧
      (S.map (fun z => z ^ k)).sum = R ∧
      (S.map (fun z => ‖z‖ ^ p)).sum < ε := by
  classical
  have hkne : k ≠ 0 := hk.ne'
  by_cases hR : R = 0
  · refine ⟨0, fun q _ _ => by simp, by simp [hR], by simpa using hε⟩
  -- a positive radius bound whose `p − k` power is small enough
  have hRpos : 0 < ‖R‖ := norm_pos_iff.mpr hR
  obtain ⟨δ, hδpos, hδle, hδsmall⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ‖R‖ * δ < ε := by
    refine ⟨min 1 (ε / (2 * ‖R‖)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
    have hle : min 1 (ε / (2 * ‖R‖)) ≤ ε / (2 * ‖R‖) := min_le_right _ _
    have := mul_le_mul_of_nonneg_left hle (le_of_lt hRpos)
    calc ‖R‖ * min 1 (ε / (2 * ‖R‖)) ≤ ‖R‖ * (ε / (2 * ‖R‖)) := this
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  -- enough copies
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (‖R‖ / ((k : ℝ) * δ ^ k))
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = N₀ + 1 := ⟨_, rfl⟩
  have hNpos : 0 < N := by omega
  have hN : ‖R‖ / ((k : ℝ) * δ ^ k) < (N : ℝ) := by
    have hle : (N₀ : ℝ) ≤ (N : ℝ) := by
      have : N₀ ≤ N := by omega
      exact_mod_cast this
    linarith
  have hkNpos : (0 : ℝ) < (k : ℝ) * (N : ℝ) := by
    have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    positivity
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (R / ((k : ℂ) * (N : ℂ))) hk
  have hkNC : ((k : ℂ) * (N : ℂ)) ≠ 0 := by
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hkne
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
    exact mul_ne_zero hk' hN'
  have hnormt : ‖t‖ ^ k = ‖R‖ / ((k : ℝ) * (N : ℝ)) := by
    have := congrArg norm ht
    rw [norm_pow, norm_div] at this
    simpa using this
  have htδ : ‖t‖ < δ := by
    have hlt : ‖t‖ ^ k < δ ^ k := by
      rw [hnormt]
      rw [div_lt_iff₀ hkNpos]
      have hNgt : ‖R‖ / ((k : ℝ) * δ ^ k) < (N : ℝ) := hN
      have hden : (0 : ℝ) < (k : ℝ) * δ ^ k := by
        have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
        positivity
      rw [div_lt_iff₀ hden] at hNgt
      nlinarith [hNgt]
    exact lt_of_pow_lt_pow_left₀ k (le_of_lt hδpos) hlt
  refine ⟨rootBlockMultiset k t N, ?_, ?_, ?_⟩
  · intro q hq1 hqk
    rw [sum_map_pow_rootBlockMultiset hkne, if_neg (Nat.not_dvd_of_pos_of_lt hq1 hqk)]
  · rw [sum_map_pow_rootBlockMultiset hkne, if_pos dvd_rfl, ht]
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hkne
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
    field_simp
  · rw [sum_map_normPow_rootBlockMultiset hkne]
    have hsplit : ‖t‖ ^ p = ‖t‖ ^ k * ‖t‖ ^ (p - k) := by
      rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hkp)]
    rw [hsplit, hnormt]
    have hcast : ((N * k : ℕ) : ℝ) = (k : ℝ) * (N : ℝ) := by push_cast; ring
    rw [hcast, ← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hkNpos)]
    have hek : 1 ≤ p - k := by omega
    have hlt : ‖t‖ ^ (p - k) < δ ^ (p - k) :=
      pow_lt_pow_left₀ htδ (norm_nonneg t) (by omega)
    have hδpow : δ ^ (p - k) ≤ δ := by
      calc δ ^ (p - k) ≤ δ ^ (1 : ℕ) := pow_le_pow_of_le_one (le_of_lt hδpos) hδle hek
        _ = δ := pow_one δ
    calc ‖R‖ * ‖t‖ ^ (p - k) ≤ ‖R‖ * δ ^ (p - k) :=
          mul_le_mul_of_nonneg_left (le_of_lt hlt) (norm_nonneg R)
      _ ≤ ‖R‖ * δ := mul_le_mul_of_nonneg_left hδpow (norm_nonneg R)
      _ < ε := hδsmall

/-- **The vanishing micro-spectrum construction `(M)`.**  For every prescribed set of targets for
the moments `1, …, n` with `n < p`, and every Schatten `p` energy budget, there is a finite
spectrum realising all of those moments inside the budget. -/
theorem exists_multiset_moment_realization (p : ℕ) :
    ∀ n : ℕ, n < p → ∀ (T : ℕ → ℂ) (ε : ℝ), 0 < ε →
      ∃ S : Multiset ℂ,
        (∀ k, 1 ≤ k → k ≤ n → (S.map (fun z => z ^ k)).sum = T k) ∧
        (S.map (fun z => ‖z‖ ^ p)).sum < ε := by
  intro n
  induction n with
  | zero =>
      intro _ T ε hε
      exact ⟨0, fun k hk1 hk0 => by omega, by simpa using hε⟩
  | succ n ih =>
      intro hn T ε hε
      obtain ⟨S₀, hS₀mom, hS₀cost⟩ := ih (by omega) T (ε / 2) (by linarith)
      obtain ⟨B, hBlow, hBtop, hBcost⟩ :=
        exists_block_realizing (p := p) (k := n + 1) (Nat.succ_pos n) hn
          (T (n + 1) - (S₀.map (fun z => z ^ (n + 1))).sum) (ε := ε / 2) (by linarith)
      refine ⟨S₀ + B, ?_, ?_⟩
      · intro k hk1 hk
        rw [Multiset.map_add, Multiset.sum_add]
        rcases Nat.lt_or_ge k (n + 1) with hlt | hge
        · rw [hBlow k hk1 hlt, add_zero]
          exact hS₀mom k hk1 (by omega)
        · have hkeq : k = n + 1 := by omega
          subst hkeq
          rw [hBtop]
          ring
      · rw [Multiset.map_add, Multiset.sum_add]
        linarith

end

end GaloisForLFunctions.HTGeometry
