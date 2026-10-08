import GaloisForLFunctions.RHTower.WeilWorkPBAPJointPhase

/-!
# Logarithmic cost at the exact phase-mass boundary

Any two distinct positive integer nodes below a prime force correction
frequencies to escape compact intervals as their total weight approaches one.
Their cosine defect is positive pointwise and has weighted sum `2(M-1)`.
Compactness gives a minorant for `log (2+|t|)`, yielding cost divergence
uniformly over all finite corrections. No Weil-energy lower bound is assumed
or concluded. The pair may be chosen among the profile's actual active nodes.
-/

open Filter Topology
noncomputable section
namespace RHTower.WeilWorkPBAP

/-- The two-coordinate endpoint defect; its exact weighted total is `2(M-1)`. -/
def jointPairDefect (p : Nat.Primes) (n m : ℕ) (t : ℝ) : ℝ :=
  2 + Real.cos ((Real.log n - Real.log (p : ℕ)/2)*t) +
    Real.cos ((Real.log m - Real.log (p : ℕ)/2)*t)

theorem jointPairDefect_pos (p : Nat.Primes) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hnp : n < (p : ℕ)) (hmp : m < (p : ℕ)) (hnm : n ≠ m) (t : ℝ) :
    0 < jointPairDefect p n m t := by
  have h2 := Real.neg_one_le_cos ((Real.log n - Real.log (p : ℕ)/2)*t)
  have h3 := Real.neg_one_le_cos ((Real.log m - Real.log (p : ℕ)/2)*t)
  by_contra hneg
  have hn' := not_lt.mp hneg
  unfold jointPairDefect at hn'
  apply joint_nodes_no_common_antiphase p hn hm hnp hmp hnm (t/2)
  constructor
  · rw [show (2*Real.log n - Real.log (p : ℕ))*(t/2) =
      (Real.log n - Real.log (p : ℕ)/2)*t by ring]
    linarith
  · rw [show (2*Real.log m - Real.log (p : ℕ))*(t/2) =
      (Real.log m - Real.log (p : ℕ)/2)*t by ring]
    linarith

theorem jointPairDefect_compact_gap (p : Nat.Primes) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hnp : n < (p : ℕ)) (hmp : m < (p : ℕ)) (hnm : n ≠ m)
    (H : ℝ) (hH : 0 ≤ H) :
    ∃ d : ℝ, 0 < d ∧ ∀ t, |t| ≤ H → d ≤ jointPairDefect p n m t := by
  have hc : Continuous (jointPairDefect p n m) := by unfold jointPairDefect; fun_prop
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (-H) H).Nonempty from ⟨0, by constructor <;> linarith⟩) hc.continuousOn
  refine ⟨jointPairDefect p n m x, jointPairDefect_pos p hn hm hnp hmp hnm x, fun t ht => ?_⟩
  exact hmin (abs_le.mp ht)

theorem sum_jointPairDefect (p : Nat.Primes) {n m : ℕ}
    {ι : Type} [Fintype ι] (w t : ι → ℝ)
    (hc : (1 + (∑ i, w i * Real.cos ((Real.log n - Real.log (p : ℕ)/2)*t i)) = 0) ∧
      (1 + (∑ i, w i * Real.cos ((Real.log m - Real.log (p : ℕ)/2)*t i)) = 0)) :
    (∑ i, w i * jointPairDefect p n m (t i)) = 2*((∑ i, w i)-1) := by
  have h2 := hc.1
  have h3 := hc.2
  simp only [jointPairDefect, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  linarith

/-- An actual two-phase minorant for logarithmic frequency cost, at any prescribed level. -/
theorem joint_pair_logCost_minorant (p : Nat.Primes) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hnp : n < (p : ℕ)) (hmp : m < (p : ℕ)) (hnm : n ≠ m)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ,
      K*d ≤ d*Real.log (2+|t|) + K*jointPairDefect p n m t := by
  obtain ⟨d, hd, hgap⟩ := jointPairDefect_compact_gap p hn hm hnp hmp hnm (Real.exp K) (Real.exp_pos K).le
  refine ⟨d, hd, fun t => ?_⟩
  have hlog0 : 0 ≤ Real.log (2+|t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hdef0 := (jointPairDefect_pos p hn hm hnp hmp hnm t).le
  by_cases ht : |t| ≤ Real.exp K
  · have hgap' := hgap t ht
    nlinarith
  · have hlog : K ≤ Real.log (2+|t|) := by
      rw [← Real.log_exp K]
      exact Real.log_le_log (Real.exp_pos K) (by linarith [not_le.mp ht])
    nlinarith

/-- The exact phase constraints force logarithmic frequency cost to infinity as mass tends to one.
The conclusion is uniform over all finite supports and all real frequencies. -/
theorem joint_pair_logCost_diverges_at_mass_one (p : Nat.Primes) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hnp : n < (p : ℕ)) (hmp : m < (p : ℕ)) (hnm : n ≠ m) (A : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ι : Type) (_ : Fintype ι) (w t : ι → ℝ),
      (∀ i, 0 ≤ w i) →
      ((1 + (∑ i, w i * Real.cos ((Real.log n - Real.log (p : ℕ)/2)*t i)) = 0) ∧
        (1 + (∑ i, w i * Real.cos ((Real.log m - Real.log (p : ℕ)/2)*t i)) = 0)) →
      (∑ i, w i) < 1+δ → A < ∑ i, w i * Real.log (2+|t i|) := by
  let K := 2*(max A 0+1)
  have hK : 0 < K := by dsimp [K]; linarith [le_max_right A 0]
  obtain ⟨d, hd, hpoint⟩ := joint_pair_logCost_minorant p hn hm hnp hmp hnm K hK.le
  refine ⟨d/4, by positivity, ?_⟩
  intro ι hi w t hw hc hmass
  letI : Fintype ι := hi
  have hsum := sum_jointPairDefect p w t hc
  have hM : 1 ≤ ∑ i, w i := by
    have he : -(∑ i, w i) ≤ ∑ i, w i*Real.cos ((Real.log n - Real.log (p : ℕ)/2)*t i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro i _
      have hx := Real.neg_one_le_cos ((Real.log n - Real.log (p : ℕ)/2)*t i)
      nlinarith [hw i]
    linarith [hc.1]
  have hcert : K*d*(∑ i, w i) ≤
      d*(∑ i, w i*Real.log (2+|t i|)) + K*(∑ i, w i*jointPairDefect p n m (t i)) := by
    calc
      K*d*(∑ i, w i) = ∑ i, w i*(K*d) := by rw [← Finset.sum_mul]; ring
      _ ≤ ∑ i, w i*(d*Real.log (2+|t i|)+K*jointPairDefect p n m (t i)) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpoint (t i)) (hw i)
      _ = _ := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum] at hcert
  have hsmall : K*(2*((∑ i, w i)-1)) < K*(d/2) :=
    mul_lt_mul_of_pos_left (by linarith) hK
  have hlarge : K*d ≤ K*d*(∑ i, w i) := by
    exact le_mul_of_one_le_right (mul_nonneg hK.le hd.le) hM
  have hcost : K/2 < ∑ i, w i*Real.log (2+|t i|) := by
    nlinarith
  apply lt_trans _ hcost
  dsimp [K]
  linarith [le_max_left A 0]

/-- Full-system specialization; every finite exact correction has divergent logarithmic cost
as its total weight approaches one. -/
theorem joint_logCost_diverges_at_mass_one (p : Nat.Primes) (hp : 5 ≤ (p : ℕ)) (A : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ι : Type) (_ : Fintype ι) (w t : ι → ℝ),
      (∀ i, 0 ≤ w i) →
      (∀ n : ℕ, 2 ≤ n → n < (p : ℕ) →
        1 + (∑ i, w i * Real.cos ((Real.log n - Real.log (p : ℕ)/2)*t i)) = 0) →
      (∑ i, w i) < 1+δ → A < ∑ i, w i * Real.log (2+|t i|) := by
  obtain ⟨δ, hδ, h⟩ := joint_pair_logCost_diverges_at_mass_one p
    (by norm_num : 0<(2:ℕ)) (by norm_num : 0<(3:ℕ)) (by omega) (by omega) (by omega) A
  refine ⟨δ, hδ, fun ι hi w t hw hc hm => h ι hi w t hw ?_ hm⟩
  exact ⟨hc 2 le_rfl (by omega), hc 3 (by omega) (by omega)⟩

end RHTower.WeilWorkPBAP
