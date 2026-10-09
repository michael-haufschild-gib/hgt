import GaloisForLFunctions.RHTower.WeilLogShiftArbitraryPrecisionImpulse

/-!
# The actual feasible history set at arbitrary precision

Coordinatewise error constraints and exact finite observations define a
closed subset of the bounded-history space. A nonzero tolerance at one
sufficiently late coordinate makes nowhere-bounded histories dense in its
inherited supremum metric. No boundedness of the tolerance profile is needed.
-/

open Filter Topology Real
open scoped BoundedContinuousFunction

namespace RHTower

open WeilExcess

/-- Actual bounded histories meeting every tolerance and an exact prefix. -/
def WeilLogShiftPrecisionFeasibleSet (center : ℕ →ᵇ ℝ) (ε : ℕ → ℝ) (M : ℕ) :
    Set (ℕ →ᵇ ℝ) :=
  {h | (∀ j : ℕ, |h j - center j| ≤ ε j) ∧ ∀ j : ℕ, j < M → h j = center j}

/-- Feasible histories carrying the inherited supremum metric. -/
abbrev WeilLogShiftPrecisionHistory (center : ℕ →ᵇ ℝ) (ε : ℕ → ℝ) (M : ℕ) :=
  WeilLogShiftPrecisionFeasibleSet center ε M

/-- Arbitrary pointwise tolerances define a closed history set. -/
theorem isClosed_weilLogShiftPrecisionFeasibleSet (center : ℕ →ᵇ ℝ)
    (ε : ℕ → ℝ) (M : ℕ) : IsClosed (WeilLogShiftPrecisionFeasibleSet center ε M) := by
  have heval (j : ℕ) : Continuous (fun h : ℕ →ᵇ ℝ => h j) :=
    (continuous_apply j).comp BoundedContinuousFunction.continuous_coe
  have hset : WeilLogShiftPrecisionFeasibleSet center ε M =
      (⋂ j : ℕ, {h : ℕ →ᵇ ℝ | |h j - center j| ≤ ε j}) ∩
        (⋂ j : ℕ, ⋂ (_ : j < M), {h : ℕ →ᵇ ℝ | h j = center j}) := by
    ext h
    simp only [WeilLogShiftPrecisionFeasibleSet, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  exact (isClosed_iInter fun j =>
    isClosed_le ((heval j).sub continuous_const).abs continuous_const).inter
    (isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (heval j) continuous_const)

/-- Nonnegative tolerances always leave the center feasible. -/
theorem weilLogShiftPrecisionFeasibleSet_center (center : ℕ →ᵇ ℝ)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 ≤ ε j) (M : ℕ) :
    center ∈ WeilLogShiftPrecisionFeasibleSet center ε M := by
  constructor
  · intro j
    simpa only [sub_self, abs_zero] using hε j
  · intro j _
    rfl

/-- A permitted impulse beyond the exact prefix preserves all constraints. -/
theorem weilLogShiftRecoveryImpulseHistory_mem_precision (center : ℕ →ᵇ ℝ)
    (ε : ℕ → ℝ) (M : ℕ) (h : WeilLogShiftPrecisionHistory center ε M)
    (k : ℕ) (t : ℝ) (hk : M ≤ k)
    (ht : |(h : ℕ →ᵇ ℝ) k - center k + t| ≤ ε k) :
    weilLogShiftRecoveryImpulseHistory h k t ∈ WeilLogShiftPrecisionFeasibleSet center ε M := by
  constructor
  · intro j
    by_cases hj : j = k
    · subst j
      rw [weilLogShiftRecoveryImpulseHistory_apply, if_pos rfl,
        show (h : ℕ →ᵇ ℝ) k + t - center k = (h : ℕ →ᵇ ℝ) k - center k + t by ring]
      exact ht
    · rw [weilLogShiftRecoveryImpulseHistory_apply, if_neg hj, add_zero]
      exact h.property.1 j
  · intro j hj
    rw [weilLogShiftRecoveryImpulseHistory_apply, if_neg (by omega : j ≠ k), add_zero]
    exact h.property.2 j hj

/-- The supremum displacement of one physical impulse is at most its amplitude. -/
theorem dist_weilLogShiftRecoveryImpulseHistory_le (h : ℕ →ᵇ ℝ) (k : ℕ) (t : ℝ) :
    dist (weilLogShiftRecoveryImpulseHistory h k t) h ≤ |t| := by
  rw [dist_eq_norm, weilLogShiftRecoveryImpulseHistory, add_sub_cancel_left,
    norm_smul, Real.norm_eq_abs]
  calc
    |t| * ‖weilLogShiftRecoveryUnitHistory k‖ ≤ |t| * 1 :=
      mul_le_mul_of_nonneg_left (norm_weilLogShiftRecoveryUnitHistory_le k) (abs_nonneg t)
    _ = |t| := mul_one _

private theorem precision_coordinate_step (a b e δ : ℝ) (ha : |a| ≤ e) (hb : |b| ≤ e)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    |a + δ * (b - a)| ≤ e ∧ |δ * (b - a)| ≤ 2 * δ * e := by
  constructor
  · have hid : a + δ * (b - a) = (1 - δ) * a + δ * b := by ring
    rw [hid]
    calc
      |(1 - δ) * a + δ * b| ≤ |(1 - δ) * a| + |δ * b| := abs_add_le _ _
      _ = (1 - δ) * |a| + δ * |b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hδ1), abs_of_nonneg hδ0]
      _ ≤ (1 - δ) * e + δ * e :=
        add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hδ1))
          (mul_le_mul_of_nonneg_left hb hδ0)
      _ = e := by ring
  · have hab : |b - a| ≤ 2 * e := by
      calc
        |b - a| ≤ |b| + |-a| := abs_add_le _ _
        _ ≤ 2 * e := by rw [abs_neg]; linarith
    rw [abs_mul, abs_of_nonneg hδ0]
    calc
      δ * |b - a| ≤ δ * (2 * e) := mul_le_mul_of_nonneg_left hab hδ0
      _ = 2 * δ * e := by ring

/-- Arbitrarily near every feasible history, a change at one permitted
sufficiently late coordinate produces unbounded tails at all real shifts. -/
theorem exists_weilLogShiftPrecisionFeasible_near_nowhere_bounded :
    ∃ K : ℕ, ∀ (center : ℕ →ᵇ ℝ) (ε : ℕ → ℝ) (M k : ℕ),
      K ≤ k → M ≤ k → 0 < ε k → ∀ h : WeilLogShiftPrecisionHistory center ε M,
      ∀ η : ℝ, 0 < η → ∃ g : WeilLogShiftPrecisionHistory center ε M,
        dist g h < η ∧ (∀ j : ℕ, j ≠ k → (g : ℕ →ᵇ ℝ) j = (h : ℕ →ᵇ ℝ) j) ∧
          WeilLogShiftUniformNowhereBounded g := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftRecoveryImpulse_two_amplitude_alternative
  refine ⟨K, fun center ε M k hkK hkM hkε h η hη => ?_⟩
  let a : ℝ := (h : ℕ →ᵇ ℝ) k - center k
  let δ : ℝ := min (1 / 2) (η / (4 * ε k))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hnear : 2 * δ * ε k < η := by
    have hle : δ ≤ η / (4 * ε k) := min_le_right _ _
    have hmul := (le_div_iff₀ (by positivity : 0 < 4 * ε k)).mp hle
    nlinarith
  let tp : ℝ := δ * (ε k - a)
  let tm : ℝ := δ * (-ε k - a)
  have hp := precision_coordinate_step a (ε k) (ε k) δ (h.property.1 k)
    (by rw [abs_of_pos hkε]) hδ.le hδ1
  have hm := precision_coordinate_step a (-ε k) (ε k) δ (h.property.1 k)
    (by rw [abs_neg, abs_of_pos hkε]) hδ.le hδ1
  let gp : WeilLogShiftPrecisionHistory center ε M :=
    ⟨weilLogShiftRecoveryImpulseHistory h k tp,
      weilLogShiftRecoveryImpulseHistory_mem_precision center ε M h k tp hkM hp.1⟩
  let gm : WeilLogShiftPrecisionHistory center ε M :=
    ⟨weilLogShiftRecoveryImpulseHistory h k tm,
      weilLogShiftRecoveryImpulseHistory_mem_precision center ε M h k tm hkM hm.1⟩
  have hne : tp ≠ tm := by
    intro ht
    have hpos : 0 < δ * ε k := mul_pos hδ hkε
    dsimp only [tp, tm] at ht
    nlinarith
  rcases hK h k hkK tp tm hne with hpGood | hmGood
  · refine ⟨gp, ?_, ?_, hpGood⟩
    · change dist (weilLogShiftRecoveryImpulseHistory h k tp) (h : ℕ →ᵇ ℝ) < η
      exact (dist_weilLogShiftRecoveryImpulseHistory_le h k tp).trans_lt (hp.2.trans_lt hnear)
    · intro j hj
      change weilLogShiftRecoveryImpulseHistory h k tp j = (h : ℕ →ᵇ ℝ) j
      rw [weilLogShiftRecoveryImpulseHistory_apply, if_neg hj, add_zero]
  · refine ⟨gm, ?_, ?_, hmGood⟩
    · change dist (weilLogShiftRecoveryImpulseHistory h k tm) (h : ℕ →ᵇ ℝ) < η
      exact (dist_weilLogShiftRecoveryImpulseHistory_le h k tm).trans_lt (hm.2.trans_lt hnear)
    · intro j hj
      change weilLogShiftRecoveryImpulseHistory h k tm j = (h : ℕ →ᵇ ℝ) j
      rw [weilLogShiftRecoveryImpulseHistory_apply, if_neg hj, add_zero]

/-- Density holds directly in the feasible history set's supremum topology. -/
theorem exists_weilLogShiftPrecisionFeasible_dense_nowhere_bounded :
    ∃ K : ℕ, ∀ (center : ℕ →ᵇ ℝ) (ε : ℕ → ℝ) (M : ℕ),
      (∃ k : ℕ, K ≤ k ∧ M ≤ k ∧ 0 < ε k) →
        Dense {h : WeilLogShiftPrecisionHistory center ε M | WeilLogShiftUniformNowhereBounded h} := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftPrecisionFeasible_near_nowhere_bounded
  refine ⟨K, fun center ε M ⟨k, hkK, hkM, hkε⟩ => Metric.dense_iff.mpr ?_⟩
  intro h η hη
  obtain ⟨g, hgdist, _, hg⟩ := hK center ε M k hkK hkM hkε h η hη
  exact ⟨g, hgdist, hg⟩

end RHTower
