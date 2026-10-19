import GaloisForLFunctions.TransHorizonIncidenceMechanics.ValuationTraceDistanceAndPrimePowerPeriod

/-!
# Errors, erasures, and the exact valuation-trace recovery clock

The classical finite-word criterion is proved by partitioning disagreement
positions into erasures and two error sets. Inverting the exact prime-power
distance floor then gives the closed recovery-window formula, including its
parity dependence. These facts feed the literal horizon-state recovery theorem.
-/

set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section

/-- Number of received symbols unequal to the actual word outside the erased positions. -/
def observationErrorCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    (erased : Finset ι) (received actual : ι → ℕ) : ℕ :=
  (Finset.univ.filter (fun i => i ∉ erased ∧ received i ≠ actual i)).card

/-- Two words share a received word with e errors and s erasures exactly when their distance is at most 2e+s. -/
theorem shared_faulty_observation_iff_hammingDist_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] (f g : ι → ℕ) (e s : ℕ) :
    (∃ E : Finset ι, E.card ≤ s ∧ ∃ z : ι → ℕ,
      observationErrorCount E z f ≤ e ∧ observationErrorCount E z g ≤ e) ↔
      hammingDist f g ≤ 2 * e + s := by
  classical
  let D := Finset.univ.filter (fun i => f i ≠ g i)
  change (∃ E : Finset ι, E.card ≤ s ∧ ∃ z : ι → ℕ,
    observationErrorCount E z f ≤ e ∧ observationErrorCount E z g ≤ e) ↔
    D.card ≤ 2 * e + s
  constructor
  · rintro ⟨E, hE, z, hf, hg⟩
    let F := Finset.univ.filter (fun i => i ∉ E ∧ z i ≠ f i)
    let G := Finset.univ.filter (fun i => i ∉ E ∧ z i ≠ g i)
    change F.card ≤ e at hf
    change G.card ≤ e at hg
    have hsub : D ⊆ (E ∪ F) ∪ G := by
      intro i hi
      have hfg : f i ≠ g i := (Finset.mem_filter.mp hi).2
      by_cases hiE : i ∈ E
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hiE)))
      · by_cases hzf : z i = f i
        · apply Finset.mem_union.mpr
          right
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiE, fun hzg =>
            hfg (hzf.symm.trans hzg)⟩
        · apply Finset.mem_union.mpr
          left
          apply Finset.mem_union.mpr
          right
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiE, hzf⟩
    have hcard := Finset.card_le_card hsub
    have hEF := Finset.card_union_le E F
    have hEFG := Finset.card_union_le (E ∪ F) G
    omega
  · intro hdist
    obtain ⟨E, hED, hEcard⟩ := Finset.exists_subset_card_eq
      (s := D) (Nat.min_le_right s D.card)
    let R := D \ E
    have hRcard : R.card + E.card = D.card := Finset.card_sdiff_add_card_eq_card hED
    have hRbound : R.card ≤ 2 * e := by omega
    obtain ⟨A, hAR, hAcard⟩ := Finset.exists_subset_card_eq
      (s := R) (Nat.min_le_right e R.card)
    let z : ι → ℕ := fun i => if i ∈ A then f i else g i
    refine ⟨E, by omega, z, ?_, ?_⟩
    · have hsub : (Finset.univ.filter (fun i => i ∉ E ∧ z i ≠ f i)) ⊆ R \ A := by
        intro i hi
        obtain ⟨_, hiE, hzf⟩ := Finset.mem_filter.mp hi
        have hiA : i ∉ A := by
          intro h
          exact hzf (by simp [z, h])
        have hiD : i ∈ D := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ i, ?_⟩
          intro hfg
          exact hzf (by simp [z, hiA, hfg])
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hiD, hiE⟩, hiA⟩
      have hcard := Finset.card_le_card hsub
      have hsplit := Finset.card_sdiff_add_card_eq_card hAR
      change (Finset.univ.filter (fun i => i ∉ E ∧ z i ≠ f i)).card ≤ e
      omega
    · have hsub : (Finset.univ.filter (fun i => i ∉ E ∧ z i ≠ g i)) ⊆ A := by
        intro i hi
        obtain ⟨_, _, hzg⟩ := Finset.mem_filter.mp hi
        by_contra h
        exact hzg (by simp [z, h])
      have hcard := Finset.card_le_card hsub
      change (Finset.univ.filter (fun i => i ∉ E ∧ z i ≠ g i)).card ≤ e
      omega

/-- Sharp prime-power recovery window with e corrupted symbols and s erased positions. -/
def primePowerFaultRecoveryClock (q e s : ℕ) : ℕ :=
  (e + s / 2) * q + if Even s then q.totient else q

private theorem cutoff_distance_gt_iff {q c : ℕ} (hq : 0 < q)
    (hc : 0 < c) (hcq : c ≤ q) (W e s : ℕ) :
    2 * e + s < 2 * (W / q) + (if c ≤ W % q then 1 else 0) ↔
      (e + s / 2) * q + (if Even s then c else q) ≤ W := by
  let n := W / q
  let m := e + s / 2
  let r := W % q
  have hw : q * n + r = W := Nat.div_add_mod W q
  have hr : r < q := Nat.mod_lt W hq
  have hsrem : s % 2 < 2 := Nat.mod_lt s (by omega)
  have hsdiv := Nat.div_add_mod s 2
  change 2 * e + s < 2 * n + (if c ≤ r then 1 else 0) ↔
    m * q + (if Even s then c else q) ≤ W
  by_cases hs : Even s
  · have hs0 : s % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp (even_iff_two_dvd.mp hs)
    have hb : 2 * e + s = 2 * m := by dsimp [m]; omega
    rw [hb, if_pos hs]
    rcases lt_trichotomy n m with hnm | hnm | hmn
    · have hprod : (n + 1) * q ≤ m * q := Nat.mul_le_mul_right q hnm
      constructor
      · intro h
        split_ifs at h <;> omega
      · intro h
        exfalso
        nlinarith
    · rw [hnm] at hw ⊢
      by_cases hcr : c ≤ r
      · simp only [if_pos hcr]
        constructor
        · intro _
          nlinarith
        · intro _
          omega
      · simp only [if_neg hcr]
        constructor
        · omega
        · intro h
          exfalso
          nlinarith
    · have hprod : (m + 1) * q ≤ n * q := Nat.mul_le_mul_right q hmn
      constructor
      · intro _
        nlinarith
      · intro _
        split_ifs <;> omega
  · have hs1 : s % 2 = 1 := by
      have hne : s % 2 ≠ 0 := fun h => hs (even_iff_two_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr h))
      omega
    have hb : 2 * e + s = 2 * m + 1 := by dsimp [m]; omega
    rw [hb, if_neg hs]
    by_cases hmn : m < n
    · have hprod : (m + 1) * q ≤ n * q := Nat.mul_le_mul_right q hmn
      constructor
      · intro _
        nlinarith
      · intro _
        split_ifs <;> omega
    · have hnm : n ≤ m := by omega
      have hprod : n * q ≤ m * q := Nat.mul_le_mul_right q hnm
      constructor
      · intro h
        split_ifs at h <;> omega
      · intro h
        exfalso
        nlinarith

/-- Exact inversion of the prime-power distance floor at the mixed-fault budget. -/
theorem primePowerTraceDistanceFloor_gt_iff_clock_le {q : ℕ}
    (hq : 0 < q) (W e s : ℕ) :
    2 * e + s < primePowerTraceDistanceFloor q W ↔
      primePowerFaultRecoveryClock q e s ≤ W := by
  exact cutoff_distance_gt_iff hq (Nat.totient_pos.mpr hq) (Nat.totient_le q) W e s

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
