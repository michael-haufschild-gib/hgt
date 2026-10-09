import GaloisForLFunctions.RHTower.WeilLogShiftRecoveryDomainDensity
import GaloisForLFunctions.HTGeometry.CountableResidualIntersection

/-!
# Generic recovery histories have no finite moments

Origin-weighted reconstructed deviations have arbitrarily large excursions of
both signs in every tail on a dense residual set of histories. These excursions
exclude signed, excess, and deficit summability at the origin. Inward transfer
then excludes every real shift simultaneously. Thus the existence of even one
finite moment of any of the three kinds is a meagre condition, although each
realizable moment profile is dense by the preceding domain-density theorem.
-/

open Filter Topology Zeta23 Real
open scoped BigOperators

noncomputable section

namespace RHTower

open WeilExcess

/-- Reconstructing a history preserves every normalized arithmetic deviation. -/
theorem weilDeviation_recoveryInverse_history (lam : ℕ → ℝ) (n : ℕ) :
    weilDeviation (weilLogShiftRecoveryInverse (weilLogShiftRecoveryHistory lam)) n =
      weilDeviation lam n := by
  rw [weilLogShiftRecoveryInverse_history]
  by_cases hn : 2 ≤ n <;> simp [weilDeviation, hn]

/-- The signed origin-weighted arithmetic term read from a complete recovery history. -/
def weilLogShiftRecoveryOriginTerm (height : ℕ → ℝ) (n : ℕ) : ℝ :=
  weilDeviation (weilLogShiftRecoveryInverse height) n * pairedLogKernel 0 n

/-- Every reconstructed normalized coefficient is continuous in history. -/
theorem continuous_weilDeviation_recoveryInverse (n : ℕ) :
    Continuous (fun height : ℕ → ℝ => weilDeviation (weilLogShiftRecoveryInverse height) n) := by
  unfold weilDeviation
  by_cases hn : 2 ≤ n
  · simp only [if_pos hn]
    exact (((continuous_apply n).comp continuous_weilLogShiftRecoveryInverse).sub
      continuous_const).div_const _
  · simp only [if_neg hn]
    exact continuous_const

theorem continuous_weilLogShiftRecoveryOriginTerm (n : ℕ) :
    Continuous (fun height : ℕ → ℝ => weilLogShiftRecoveryOriginTerm height n) :=
  (continuous_weilDeviation_recoveryInverse n).mul_const _

/-- A positive or negative weighted excursion past a given tail cutoff. -/
def weilLogShiftRecoveryTailExcursion (negative : Bool) (K N : ℕ) : Set (ℕ → ℝ) :=
  {height | ∃ n : ℕ, N + 2 ≤ n ∧
    (K : ℝ) < (if negative then -1 else 1) * weilLogShiftRecoveryOriginTerm height n}

theorem isOpen_weilLogShiftRecoveryTailExcursion (negative : Bool) (K N : ℕ) :
    IsOpen (weilLogShiftRecoveryTailExcursion negative K N) := by
  have hset : weilLogShiftRecoveryTailExcursion negative K N =
      ⋃ n : ℕ, ⋃ (_ : N + 2 ≤ n),
        {height : ℕ → ℝ | (K : ℝ) <
          (if negative then -1 else 1) * weilLogShiftRecoveryOriginTerm height n} := by
    ext height
    simp only [weilLogShiftRecoveryTailExcursion, Set.mem_setOf_eq, Set.mem_iUnion,
      exists_prop]
  rw [hset]
  exact isOpen_iUnion fun n => isOpen_iUnion fun _ => isOpen_lt continuous_const
    ((continuous_weilLogShiftRecoveryOriginTerm n).const_mul _)

/-- Either sign can exceed any threshold after any cutoff while approaching an
arbitrary prescribed history coordinatewise. -/
theorem dense_weilLogShiftRecoveryTailExcursion (negative : Bool) (K N : ℕ) :
    Dense (weilLogShiftRecoveryTailExcursion negative K N) := by
  let ε : ℝ := if negative then -1 else 1
  let v (n : ℕ) : ℝ := ε * ((K : ℝ) + 1) / pairedLogKernel 0 n
  let base := weilCoefficientLift v
  intro height
  apply mem_closure_of_tendsto (tendsto_weilLogShiftRecoverySplice_history base height)
  filter_upwards with M
  let n := M + N + 2
  have hn : 2 ≤ n := by dsimp only [n]; omega
  have htail : weilLogShiftRecoverySplice base height M n = base n :=
    weilLogShiftRecoverySplice_tail base height M n (by dsimp only [n]; omega)
  have hdev : weilDeviation (weilLogShiftRecoverySplice base height M) n = v n := by
    calc
      _ = weilDeviation base n := by simp only [weilDeviation, if_pos hn, htail]
      _ = v n := by simpa only [base, if_pos hn] using weilDeviation_coefficientLift v n
  refine ⟨n, by dsimp only [n]; omega, ?_⟩
  change (K : ℝ) < ε * weilLogShiftRecoveryOriginTerm
    (weilLogShiftRecoveryHistory (weilLogShiftRecoverySplice base height M)) n
  rw [weilLogShiftRecoveryOriginTerm, weilDeviation_recoveryInverse_history, hdev]
  have hterm : v n * pairedLogKernel 0 n = ε * ((K : ℝ) + 1) :=
    div_mul_cancel₀ _ (pairedLogKernel_pos 0 n).ne'
  rw [hterm]
  cases negative <;> norm_num [ε]

/-- Arbitrarily large excursions of both signs occur beyond every finite head. -/
def WeilLogShiftTwoSidedExcursions (height : ℕ → ℝ) : Prop :=
  ∀ negative : Bool, ∀ K N : ℕ, height ∈ weilLogShiftRecoveryTailExcursion negative K N

/-- The explicit two-sided tail-excursion family is dense and residual. -/
theorem dense_and_residual_weilLogShiftTwoSidedExcursions :
    Dense {height : ℕ → ℝ | WeilLogShiftTwoSidedExcursions height} ∧
      {height : ℕ → ℝ | WeilLogShiftTwoSidedExcursions height} ∈ residual (ℕ → ℝ) := by
  have h := GaloisForLFunctions.HTGeometry.dense_and_residual_setOf_forall
    (fun q : Bool × ℕ × ℕ => weilLogShiftRecoveryTailExcursion q.1 q.2.1 q.2.2)
    (fun q => isOpen_weilLogShiftRecoveryTailExcursion q.1 q.2.1 q.2.2)
    (fun q => dense_weilLogShiftRecoveryTailExcursion q.1 q.2.1 q.2.2)
  have hset : {height : ℕ → ℝ | ∀ q : Bool × ℕ × ℕ,
      height ∈ weilLogShiftRecoveryTailExcursion q.1 q.2.1 q.2.2} =
      {height | WeilLogShiftTwoSidedExcursions height} := by
    ext height
    constructor
    · intro hh negative K N
      exact hh (negative, K, N)
    · rintro hh ⟨negative, K, N⟩
      exact hh negative K N
  rw [hset] at h
  exact h

/-- All three local convergence domains of the reconstructed coefficients are empty. -/
def WeilLogShiftNowhereSummable (height : ℕ → ℝ) : Prop :=
  ∀ y : ℝ,
    (¬ Summable fun n => weilDeviation (weilLogShiftRecoveryInverse height) n *
      pairedLogKernel y n) ∧
    (¬ Summable fun n => deviationExcess (weilLogShiftRecoveryInverse height) n *
      pairedLogKernel y n) ∧
    (¬ Summable fun n => deviationDeficit (weilLogShiftRecoveryInverse height) n *
      pairedLogKernel y n)

/-- Excursions exclude one-sided moments at zero; inward transfer excludes all shifts. -/
theorem weilLogShiftNowhereSummable_of_twoSidedExcursions (height : ℕ → ℝ)
    (hexcursion : WeilLogShiftTwoSidedExcursions height) :
    WeilLogShiftNowhereSummable height := by
  let lam := weilLogShiftRecoveryInverse height
  have hexc : ¬ Summable fun n => deviationExcess lam n * pairedLogKernel 0 n := by
    intro hs
    obtain ⟨M, hM⟩ := eventually_atTop.mp
      ((tendsto_order.mp hs.tendsto_atTop_zero).2 1 (by norm_num))
    obtain ⟨n, hn, hlarge⟩ := hexcursion false 1 M
    have hlarge' : 1 < weilDeviation lam n * pairedLogKernel 0 n := by
      simpa only [Bool.false_eq_true, if_false, one_mul, Nat.cast_one,
        weilLogShiftRecoveryOriginTerm] using hlarge
    have hle := mul_le_mul_of_nonneg_right
      (le_max_left (weilDeviation lam n) 0) (pairedLogKernel_pos 0 n).le
    have hsmall := hM n (by omega)
    change weilDeviation lam n * pairedLogKernel 0 n ≤
      deviationExcess lam n * pairedLogKernel 0 n at hle
    linarith only [hlarge', hle, hsmall]
  have hdef : ¬ Summable fun n => deviationDeficit lam n * pairedLogKernel 0 n := by
    intro hs
    obtain ⟨M, hM⟩ := eventually_atTop.mp
      ((tendsto_order.mp hs.tendsto_atTop_zero).2 1 (by norm_num))
    obtain ⟨n, hn, hlarge⟩ := hexcursion true 1 M
    have hlarge' : 1 < (-weilDeviation lam n) * pairedLogKernel 0 n := by
      simpa only [if_true, neg_one_mul, Nat.cast_one, weilLogShiftRecoveryOriginTerm,
        neg_mul, one_mul] using hlarge
    have hle := mul_le_mul_of_nonneg_right
      (le_max_left (-weilDeviation lam n) 0) (pairedLogKernel_pos 0 n).le
    have hsmall := hM n (by omega)
    change (-weilDeviation lam n) * pairedLogKernel 0 n ≤
      deviationDeficit lam n * pairedLogKernel 0 n at hle
    linarith only [hlarge', hle, hsmall]
  have hsigned : ¬ Summable fun n => weilDeviation lam n * pairedLogKernel 0 n :=
    fun hs => hexc (summable_excess_potential_of_summable_potential hs)
  intro y
  have hin : |(0 : ℝ)| ≤ |y| := by simpa only [abs_zero] using abs_nonneg y
  exact ⟨fun hs => hsigned (summable_kernelPotential_of_abs_le hin hs),
    fun hs => hexc (summable_kernelPotential_of_abs_le hin hs),
    fun hs => hdef (summable_kernelPotential_of_abs_le hin hs)⟩

/-- Nowhere convergence of every moment kind is generic in the product topology. -/
theorem dense_and_residual_weilLogShiftNowhereSummable :
    Dense {height : ℕ → ℝ | WeilLogShiftNowhereSummable height} ∧
      {height : ℕ → ℝ | WeilLogShiftNowhereSummable height} ∈ residual (ℕ → ℝ) := by
  have hsub : {height : ℕ → ℝ | WeilLogShiftTwoSidedExcursions height} ⊆
      {height | WeilLogShiftNowhereSummable height} :=
    fun height h => weilLogShiftNowhereSummable_of_twoSidedExcursions height h
  have h := dense_and_residual_weilLogShiftTwoSidedExcursions
  exact ⟨h.1.mono hsub, mem_of_superset h.2 hsub⟩

/-- The existence of any finite signed, excess, or deficit moment is meagre,
even allowing the real shift to depend on the history. -/
theorem isMeagre_weilLogShift_some_summable_moment :
    IsMeagre {height : ℕ → ℝ | ∃ y : ℝ,
      (Summable fun n => weilDeviation (weilLogShiftRecoveryInverse height) n *
        pairedLogKernel y n) ∨
      (Summable fun n => deviationExcess (weilLogShiftRecoveryInverse height) n *
        pairedLogKernel y n) ∨
      (Summable fun n => deviationDeficit (weilLogShiftRecoveryInverse height) n *
        pairedLogKernel y n)} := by
  change _ᶜ ∈ residual (ℕ → ℝ)
  apply mem_of_superset dense_and_residual_weilLogShiftNowhereSummable.2
  rintro height hh ⟨y, hs | hs | hs⟩
  · exact (hh y).1 hs
  · exact (hh y).2.1 hs
  · exact (hh y).2.2 hs

end RHTower
