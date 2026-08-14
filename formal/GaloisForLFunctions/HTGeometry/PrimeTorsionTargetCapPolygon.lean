import GaloisForLFunctions.HTGeometry.FiniteGridCoherenceMoment
import GaloisForLFunctions.HTGeometry.PrimeTorsionOrbitAvoidance

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A complete nonidentity prime-torsion orbit simultaneously avoids every
translated target cap once the exact finite cap budget closes. -/
theorem exists_primeTorsion_complete_targetCap_avoidance
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p d : ℕ) [Fact p.Prime] (weight : Fin d → ℝ) (threshold : ℝ)
    (target : Y → Fin d → ZMod p)
    (hsmall : (p - 1) * Fintype.card Y *
        (finiteGridCoherenceCap p weight threshold).card < p ^ d) :
    ∃ q : Fin d → ZMod p,
      ∀ a : ZMod p, a ≠ 0 → ∀ y : Y,
        (fun i => a * q i) ∉
          finiteGridTranslatedCoherenceCap p weight threshold (target y) := by
  let bad := finiteGridTargetCaptureSet p weight threshold target
  have hbadCard : bad.card ≤ Fintype.card Y *
      (finiteGridCoherenceCap p weight threshold).card := by
    exact finiteGridTargetCaptureSet_card_le p weight threshold target
  have hbadSmall : (p - 1) * bad.card < p ^ d := by
    exact lt_of_le_of_lt (Nat.mul_le_mul_left (p - 1) hbadCard)
      (by simpa [mul_assoc] using hsmall)
  obtain ⟨q, hq⟩ := exists_primeTorsion_complete_avoidance p d bad hbadSmall
  refine ⟨q, ?_⟩
  intro a ha y hy
  apply hq a ha
  exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ y, hy⟩

/-- **Replica-budget prime-polygon law.** Replica order `n` may be much
smaller than prime torsion order `p`.  If `2n < p` and the factorial moment
budget, including every target and every nonidentity power, lies below the
coherence threshold, then one entire nonidentity order-`p` polygon avoids all
target caps. -/
theorem exists_primeTorsion_complete_targetCap_avoidance_of_replicaBudget
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p d : ℕ) [Fact p.Prime] {weight : Fin d → ℝ}
    (hweight : ∀ i, 0 ≤ weight i) (n : ℕ) (hreplica : 2 * n < p)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (target : Y → Fin d → ZMod p)
    (hbudget :
      (((p - 1) * Fintype.card Y : ℕ) : ℝ) * (n.factorial : ℝ) *
          (∑ i, weight i ^ 2) ^ n < threshold ^ (2 * n)) :
    ∃ q : Fin d → ZMod p,
      ∀ a : ZMod p, a ≠ 0 → ∀ y : Y,
        (fun i => a * q i) ∉
          finiteGridTranslatedCoherenceCap p weight threshold (target y) := by
  have hcap := finiteGridCoherenceCap_card_mul_pow_le_factorial
    p hweight n hreplica threshold hthreshold.le
  let A : ℝ := (((p - 1) * Fintype.card Y : ℕ) : ℝ)
  let B : ℝ := ((finiteGridCoherenceCap p weight threshold).card : ℝ)
  let P : ℝ := (p : ℝ) ^ d
  let F : ℝ := (n.factorial : ℝ) * (∑ i, weight i ^ 2) ^ n
  let T : ℝ := threshold ^ (2 * n)
  have hA : 0 ≤ A := by positivity
  have hP : 0 < P := by
    exact pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  have hT : 0 < T := pow_pos hthreshold _
  have hcap' : B * T ≤ P * F := by
    simpa [B, T, P, F, mul_assoc] using hcap
  have hbudget' : A * F < T := by
    simpa [A, F, T, mul_assoc] using hbudget
  have hAB : A * B < P := by
    have hABT : (A * B) * T < P * T := calc
      (A * B) * T = A * (B * T) := by ring
      _ ≤ A * (P * F) := mul_le_mul_of_nonneg_left hcap' hA
      _ = P * (A * F) := by ring
      _ < P * T := mul_lt_mul_of_pos_left hbudget' hP
    nlinarith
  have hsmall : (p - 1) * Fintype.card Y *
      (finiteGridCoherenceCap p weight threshold).card < p ^ d := by
    have hcast :
        (((p - 1) * Fintype.card Y *
          (finiteGridCoherenceCap p weight threshold).card : ℕ) : ℝ) <
        ((p ^ d : ℕ) : ℝ) := by
      push_cast
      simpa [A, B, P, mul_assoc] using hAB
    exact_mod_cast hcast
  exact exists_primeTorsion_complete_targetCap_avoidance
    p d weight threshold target hsmall

end GaloisForLFunctions.HTGeometry
