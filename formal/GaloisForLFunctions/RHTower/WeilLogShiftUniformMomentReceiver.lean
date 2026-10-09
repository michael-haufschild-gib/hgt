import GaloisForLFunctions.RHTower.WeilLogShiftBoundedCubeGenericity
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# A uniform operator receiver for bounded-history moments

The centered recovery inverse is linear. Its weighted coordinates give continuous
linear functionals on bounded histories with the supremum norm. Pointwise
summability throughout the unit cube is equivalent to uniform boundedness of
finite absolute moments, and to a uniform operator-norm bound for finite signed
centered panels together with the zero-history moment. These equivalences do not
assert that the receiver holds at any interior shift.
-/

open Filter Topology Zeta23 Real
open scoped BigOperators BoundedContinuousFunction

noncomputable section

namespace RHTower

open WeilExcess

/-- Recovery is affine; centering at the zero history removes its fixed offset. -/
theorem weilLogShiftRecoveryInverse_affine (c d : ℝ) (h g : ℕ → ℝ) :
    weilLogShiftRecoveryInverse (fun k => c * h k + d * g k) =
      fun n => c * weilLogShiftRecoveryInverse h n + d * weilLogShiftRecoveryInverse g n +
        (1 - c - d) * weilLogShiftRecoveryInverse (fun _ => 0) n := by
  let f := fun n => c * weilLogShiftRecoveryInverse h n + d * weilLogShiftRecoveryInverse g n +
    (1 - c - d) * weilLogShiftRecoveryInverse (fun _ => 0) n
  have hprobe (n : ℕ) : weilLogShiftRecoveryProbe f n =
      c * weilLogShiftRecoveryProbe (weilLogShiftRecoveryInverse h) n +
      d * weilLogShiftRecoveryProbe (weilLogShiftRecoveryInverse g) n +
      (1 - c - d) * weilLogShiftRecoveryProbe
        (weilLogShiftRecoveryInverse (fun _ => 0)) n := by
    rw [weilLogShiftRecoveryProbe_affine f,
      weilLogShiftRecoveryProbe_affine (weilLogShiftRecoveryInverse h),
      weilLogShiftRecoveryProbe_affine (weilLogShiftRecoveryInverse g),
      weilLogShiftRecoveryProbe_affine (weilLogShiftRecoveryInverse (fun _ => 0))]
    simp only [f, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  have hhistory : weilLogShiftRecoveryHistory f = fun k => c * h k + d * g k := by
    funext k
    change weilLogShiftRecoveryProbe f (k + 2) = _
    rw [hprobe]
    change c * weilLogShiftRecoveryHistory (weilLogShiftRecoveryInverse h) k +
      d * weilLogShiftRecoveryHistory (weilLogShiftRecoveryInverse g) k +
      (1 - c - d) * weilLogShiftRecoveryHistory
        (weilLogShiftRecoveryInverse (fun _ => 0)) k = _
    rw [weilLogShiftRecoveryHistory_inverse, weilLogShiftRecoveryHistory_inverse,
      weilLogShiftRecoveryHistory_inverse]
    ring
  have hf0 : f 0 = 0 := by
    simp only [f, (weilLogShiftRecoveryInverse_head h).1,
      (weilLogShiftRecoveryInverse_head g).1,
      (weilLogShiftRecoveryInverse_head (fun _ => 0)).1, mul_zero, add_zero]
  have hf1 : f 1 = 0 := by
    simp only [f, (weilLogShiftRecoveryInverse_head h).2,
      (weilLogShiftRecoveryInverse_head g).2,
      (weilLogShiftRecoveryInverse_head (fun _ => 0)).2, mul_zero, add_zero]
  have hinv := weilLogShiftRecoveryInverse_history f
  rw [hhistory] at hinv
  funext n
  rw [congrFun hinv n]
  change (if 2 ≤ n then f n else 0) = f n
  by_cases hn : 2 ≤ n
  · exact if_pos hn
  · rw [if_neg hn]
    have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl
    · exact hf0.symm
    · exact hf1.symm

/-- The signed weighted deviation at a real shift, read from recovery coordinates. -/
def weilLogShiftRecoveryMoment (y : ℝ) (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  weilDeviation (weilLogShiftRecoveryInverse h) n * pairedLogKernel y n

/-- A centered moment coordinate on the Banach space of bounded histories. -/
def weilLogShiftRecoveryMomentCLM (y : ℝ) (n : ℕ) : (ℕ →ᵇ ℝ) →L[ℝ] ℝ where
  toFun h := weilLogShiftRecoveryMoment y h n - weilLogShiftRecoveryMoment y (fun _ => 0) n
  map_add' h g := by
    have hi := congrFun (weilLogShiftRecoveryInverse_affine 1 1 h g) n
    norm_num only [one_mul, sub_self, zero_sub, neg_one_mul] at hi
    change weilLogShiftRecoveryMoment y (fun k => h k + g k) n - _ = _
    unfold weilLogShiftRecoveryMoment weilDeviation
    by_cases hn : 2 ≤ n
    · simp only [if_pos hn, hi]
      ring
    · simp only [if_neg hn, zero_mul, sub_self, add_zero]
  map_smul' c h := by
    have hi := congrFun (weilLogShiftRecoveryInverse_affine c 0 h (fun _ => 0)) n
    simp only [zero_mul, add_zero, sub_zero] at hi
    change weilLogShiftRecoveryMoment y (fun k => c * h k) n - _ =
      c * (weilLogShiftRecoveryMoment y h n - _)
    unfold weilLogShiftRecoveryMoment weilDeviation
    by_cases hn : 2 ≤ n
    · simp only [if_pos hn, hi]
      ring
    · simp only [if_neg hn, zero_mul, sub_self, mul_zero]
  cont := by
    have hcoe : Continuous (fun h : ℕ →ᵇ ℝ => (fun k => h k)) :=
      continuous_pi fun k => (BoundedContinuousFunction.evalCLM ℝ k).continuous
    exact (((continuous_weilDeviation_recoveryInverse n).comp hcoe).mul_const _).sub
      continuous_const

theorem weilLogShiftRecoveryMomentCLM_apply (y : ℝ) (n : ℕ) (h : ℕ →ᵇ ℝ) :
    weilLogShiftRecoveryMomentCLM y n h =
      weilLogShiftRecoveryMoment y h n - weilLogShiftRecoveryMoment y (fun _ => 0) n := rfl

/-- Finite signed sums of centered moment coordinates. -/
def weilLogShiftRecoveryMomentPanel (y : ℝ) (N : ℕ) (sign : ℕ → Bool) :
    (ℕ →ᵇ ℝ) →L[ℝ] ℝ :=
  ∑ n ∈ Finset.range N, (if sign n then (1 : ℝ) else -1) • weilLogShiftRecoveryMomentCLM y n

theorem weilLogShiftRecoveryMomentPanel_apply (y : ℝ) (N : ℕ) (sign : ℕ → Bool)
    (h : ℕ →ᵇ ℝ) :
    weilLogShiftRecoveryMomentPanel y N sign h =
      ∑ n ∈ Finset.range N, (if sign n then (1 : ℝ) else -1) *
        weilLogShiftRecoveryMomentCLM y n h := by
  simp only [weilLogShiftRecoveryMomentPanel, sum_apply, smul_apply, smul_eq_mul]

/-- Embed the product cube into the Banach space of bounded real sequences. -/
def weilLogShiftBoundedHistoryBCF (h : WeilLogShiftBoundedHistory) : ℕ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (weilLogShiftBoundedHistoryValues h)
    continuous_of_discreteTopology 1 (fun k => by
      exact abs_le.mpr (h k).property)

theorem norm_weilLogShiftBoundedHistoryBCF_le (h : WeilLogShiftBoundedHistory) :
    ‖weilLogShiftBoundedHistoryBCF h‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le zero_le_one).mpr fun k => abs_le.mpr (h k).property

/-- Universal signed moment summability on the fixed unit recovery cube. -/
def WeilLogShiftBoundedMomentSummable (y : ℝ) : Prop :=
  ∀ h : WeilLogShiftBoundedHistory,
    Summable (weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues h))

private theorem centered_summable_of_cube {y : ℝ}
    (hs : WeilLogShiftBoundedMomentSummable y) (h : ℕ →ᵇ ℝ) :
    Summable (fun n => weilLogShiftRecoveryMomentCLM y n h) := by
  let z : WeilLogShiftBoundedHistory := fun _ => ⟨0, by norm_num⟩
  have hz : Summable (weilLogShiftRecoveryMoment y (fun _ => 0)) := hs z
  let M := ‖h‖ + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  let b : WeilLogShiftBoundedHistory := fun k => ⟨h k / M, abs_le.mp (by
    rw [abs_div, abs_of_pos hM]
    exact (div_le_one hM).mpr ((h.norm_coe_le_norm k).trans (by dsimp only [M]; linarith)))⟩
  have hb : Summable (fun n => weilLogShiftRecoveryMomentCLM y n
      (weilLogShiftBoundedHistoryBCF b)) := (hs b).sub hz
  have heq : M • weilLogShiftBoundedHistoryBCF b = h := by
    apply BoundedContinuousFunction.ext
    intro k
    change M * (h k / M) = h k
    field_simp
  have hterms (n : ℕ) : weilLogShiftRecoveryMomentCLM y n h =
      M * weilLogShiftRecoveryMomentCLM y n (weilLogShiftBoundedHistoryBCF b) := by
    rw [← heq, map_smul, smul_eq_mul]
  exact (hb.mul_left M).congr fun n => (hterms n).symm

private theorem panel_le_sum_norm (y : ℝ) (N : ℕ) (sign : ℕ → Bool) (h : ℕ →ᵇ ℝ) :
    ‖weilLogShiftRecoveryMomentPanel y N sign h‖ ≤
      ∑ n ∈ Finset.range N, ‖weilLogShiftRecoveryMomentCLM y n h‖ := by
  rw [weilLogShiftRecoveryMomentPanel_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  cases sign n <;> simp

/-- Signed-panel operator bounds control every finite absolute centered moment. -/
theorem sum_norm_weilLogShiftRecoveryMomentCLM_le (y : ℝ) {C : ℝ}
    (hC : ∀ N sign, ‖weilLogShiftRecoveryMomentPanel y N sign‖ ≤ C)
    (h : ℕ →ᵇ ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖weilLogShiftRecoveryMomentCLM y n h‖ ≤ C * ‖h‖ := by
  let sign : ℕ → Bool := fun n => if 0 ≤ weilLogShiftRecoveryMomentCLM y n h then true else false
  have hsign (n : ℕ) : (if sign n then (1 : ℝ) else -1) *
      weilLogShiftRecoveryMomentCLM y n h = ‖weilLogShiftRecoveryMomentCLM y n h‖ := by
    by_cases hn : 0 ≤ weilLogShiftRecoveryMomentCLM y n h
    · simp [sign, hn, Real.norm_eq_abs, abs_of_nonneg hn]
    · simp [sign, hn, Real.norm_eq_abs, abs_of_neg (lt_of_not_ge hn)]
  have heq : weilLogShiftRecoveryMomentPanel y N sign h =
      ∑ n ∈ Finset.range N, ‖weilLogShiftRecoveryMomentCLM y n h‖ := by
    rw [weilLogShiftRecoveryMomentPanel_apply]
    exact Finset.sum_congr rfl fun n _ => hsign n
  rw [← heq]
  exact (le_abs_self _).trans (((weilLogShiftRecoveryMomentPanel y N sign).le_opNorm h).trans
    (mul_le_mul_of_nonneg_right (hC N sign) (norm_nonneg h)))

/-- Pointwise summability forces a uniform operator-norm bound for every finite
signed centered panel; no bound is assumed in the premise. -/
theorem weilLogShiftRecoveryMomentPanel_bounded {y : ℝ}
    (hs : WeilLogShiftBoundedMomentSummable y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N sign, ‖weilLogShiftRecoveryMomentPanel y N sign‖ ≤ C := by
  have hpoint : ∀ h : ℕ →ᵇ ℝ, ∃ C : ℝ,
      ∀ p : ℕ × (ℕ → Bool), ‖weilLogShiftRecoveryMomentPanel y p.1 p.2 h‖ ≤ C := by
    intro h
    have hh := (centered_summable_of_cube hs h).norm
    refine ⟨∑' n, ‖weilLogShiftRecoveryMomentCLM y n h‖, fun p => ?_⟩
    exact (panel_le_sum_norm y p.1 p.2 h).trans
      (hh.sum_le_tsum _ fun n _ => norm_nonneg _)
  obtain ⟨C, hC⟩ := banach_steinhaus hpoint
  exact ⟨max C 0, le_max_right _ _, fun N sign => (hC (N, sign)).trans (le_max_left _ _)⟩

/-- Exact operator receiver: universal cube summability is zero-history
summability plus uniform boundedness of finite signed centered panel norms. -/
theorem weilLogShiftBoundedMomentSummable_iff_operator_bound (y : ℝ) :
    WeilLogShiftBoundedMomentSummable y ↔
      Summable (weilLogShiftRecoveryMoment y (fun _ => 0)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N sign, ‖weilLogShiftRecoveryMomentPanel y N sign‖ ≤ C := by
  constructor
  · intro hs
    exact ⟨hs (fun _ => ⟨0, by norm_num⟩), weilLogShiftRecoveryMomentPanel_bounded hs⟩
  · rintro ⟨hz, C, _, hC⟩ h
    have hh : Summable (fun n => weilLogShiftRecoveryMomentCLM y n
        (weilLogShiftBoundedHistoryBCF h)) := summable_norm_iff.mp
      (summable_of_sum_range_le (fun n => norm_nonneg _)
        (sum_norm_weilLogShiftRecoveryMomentCLM_le y hC (weilLogShiftBoundedHistoryBCF h)))
    exact (hh.add hz).congr fun n => sub_add_cancel _ _

/-- Universal pointwise summability is already uniform in both the history and
the partial-sum cutoff. -/
theorem weilLogShiftBoundedMomentSummable_iff_uniform_bound (y : ℝ) :
    WeilLogShiftBoundedMomentSummable y ↔
      ∃ B : ℝ, ∀ (h : WeilLogShiftBoundedHistory) (N : ℕ),
        ∑ n ∈ Finset.range N,
          ‖weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues h) n‖ ≤ B := by
  constructor
  · intro hs
    obtain ⟨hz, C, hC0, hC⟩ := (weilLogShiftBoundedMomentSummable_iff_operator_bound y).mp hs
    refine ⟨C + ∑' n, ‖weilLogShiftRecoveryMoment y (fun _ => 0) n‖, fun h N => ?_⟩
    have hsplit (n : ℕ) : ‖weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues h) n‖ ≤
        ‖weilLogShiftRecoveryMomentCLM y n (weilLogShiftBoundedHistoryBCF h)‖ +
        ‖weilLogShiftRecoveryMoment y (fun _ => 0) n‖ := by
      have heq : weilLogShiftRecoveryMoment y (weilLogShiftBoundedHistoryValues h) n =
          weilLogShiftRecoveryMomentCLM y n (weilLogShiftBoundedHistoryBCF h) +
          weilLogShiftRecoveryMoment y (fun _ => 0) n := (sub_add_cancel _ _).symm
      rw [heq]
      exact norm_add_le _ _
    calc
      _ ≤ ∑ n ∈ Finset.range N,
          (‖weilLogShiftRecoveryMomentCLM y n (weilLogShiftBoundedHistoryBCF h)‖ +
          ‖weilLogShiftRecoveryMoment y (fun _ => 0) n‖) := Finset.sum_le_sum fun n _ => hsplit n
      _ = (∑ n ∈ Finset.range N, ‖weilLogShiftRecoveryMomentCLM y n
          (weilLogShiftBoundedHistoryBCF h)‖) +
          ∑ n ∈ Finset.range N, ‖weilLogShiftRecoveryMoment y (fun _ => 0) n‖ :=
        Finset.sum_add_distrib
      _ ≤ C * ‖weilLogShiftBoundedHistoryBCF h‖ +
          ∑' n, ‖weilLogShiftRecoveryMoment y (fun _ => 0) n‖ :=
        add_le_add (sum_norm_weilLogShiftRecoveryMomentCLM_le y hC _ N)
          (hz.norm.sum_le_tsum _ fun n _ => norm_nonneg _)
      _ ≤ C + ∑' n, ‖weilLogShiftRecoveryMoment y (fun _ => 0) n‖ := by
        gcongr
        exact (mul_le_mul_of_nonneg_left (norm_weilLogShiftBoundedHistoryBCF_le h) hC0).trans_eq
          (mul_one C)
  · rintro ⟨B, hB⟩ h
    exact summable_norm_iff.mp (summable_of_sum_range_le (fun n => norm_nonneg _) (hB h))

/-- Whenever every unit-bounded history has a finite moment, moment differences
are uniformly Lipschitz in the supremum norm, at every finite cutoff. -/
theorem weilLogShiftBoundedMomentSummable_lipschitz {y : ℝ}
    (hs : WeilLogShiftBoundedMomentSummable y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h g : ℕ →ᵇ ℝ) (N : ℕ),
      ∑ n ∈ Finset.range N,
        ‖weilLogShiftRecoveryMoment y h n - weilLogShiftRecoveryMoment y g n‖ ≤ C * ‖h - g‖ := by
  obtain ⟨C, hC0, hC⟩ := weilLogShiftRecoveryMomentPanel_bounded hs
  refine ⟨C, hC0, fun h g N => ?_⟩
  have heq (n : ℕ) : weilLogShiftRecoveryMomentCLM y n (h - g) =
      weilLogShiftRecoveryMoment y h n - weilLogShiftRecoveryMoment y g n := by
    rw [map_sub, weilLogShiftRecoveryMomentCLM_apply, weilLogShiftRecoveryMomentCLM_apply]
    ring
  simpa only [heq] using sum_norm_weilLogShiftRecoveryMomentCLM_le y hC (h - g) N

end RHTower
