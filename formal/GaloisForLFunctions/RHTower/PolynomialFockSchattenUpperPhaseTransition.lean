import GaloisForLFunctions.RHTower.PolynomialFockFiniteTangentUpper
import GaloisForLFunctions.RHTower.SchattenTwoIdentity
import GaloisForLFunctions.HTGeometry.SchattenApproximationAdditivity
import GaloisForLFunctions.RHTower.PositiveOperatorTraceComparison
import GaloisForLFunctions.RHTower.PolynomialFockSchattenLowerObstruction

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace ComplexConjugate

namespace RHTower

noncomputable section

open ContinuousLinearMap

theorem summable_rpow_of_nonneg_of_summable_of_one_le
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {q : ℝ} (hq : 1 ≤ q) : Summable fun n => a n ^ q := by
  have hev : ∀ᶠ n in cofinite, a n ≤ 1 :=
    (hs.tendsto_cofinite_zero.eventually_lt_const one_pos).mono fun n hn => hn.le
  apply Summable.of_norm_bounded_eventually hs
  filter_upwards [hev] with n hn
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (ha n) _)]
  exact Real.rpow_le_self_of_le_one (ha n) hn hq

/-- Archimedean cutoff containing every prime whose logarithm is below the geometric tail. -/
def criticalPrimeFockLowLogCutoff : ℕ :=
  Classical.choose (exists_nat_gt (Real.exp 2))

theorem exp_two_lt_criticalPrimeFockLowLogCutoff :
    Real.exp 2 < criticalPrimeFockLowLogCutoff :=
  Classical.choose_spec (exists_nat_gt (Real.exp 2))

def criticalPrimeFockLowLogHead : Finset Nat.Primes :=
  GaloisForLFunctions.primesBelowSubtype criticalPrimeFockLowLogCutoff

theorem mem_criticalPrimeFockLowLogHead_of_log_lt_two
    (p : Nat.Primes) (hp : Real.log (p : ℝ) < 2) :
    p ∈ criticalPrimeFockLowLogHead := by
  rw [criticalPrimeFockLowLogHead, mem_primesBelowSubtype_iff]
  have hpRpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hpR : (p : ℝ) < criticalPrimeFockLowLogCutoff := by
    calc
      (p : ℝ) = Real.exp (Real.log (p : ℝ)) := (Real.exp_log hpRpos).symm
      _ < Real.exp 2 := Real.exp_lt_exp.mpr hp
      _ < criticalPrimeFockLowLogCutoff := exp_two_lt_criticalPrimeFockLowLogCutoff
  exact_mod_cast hpR

def polynomialCriticalPrimeLowLogHeadResponse
    (m : ℝ) (hm : 4 ≤ m) (j : ℕ) : ℝ :=
  ∑ p ∈ criticalPrimeFockLowLogHead, ‖criticalPrimeKernelRestriction
    (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p
    (svVec (energyOp (polynomialCriticalPrimeSamplingIncidence m hm)) j)‖ ^ 2

theorem polynomialCriticalPrimeLowLogHeadResponse_nonneg
    (m : ℝ) (hm : 4 ≤ m) (j : ℕ) :
    0 ≤ polynomialCriticalPrimeLowLogHeadResponse m hm j :=
  Finset.sum_nonneg fun _p _ => sq_nonneg _

theorem summable_polynomialCriticalPrimeLowLogHeadResponse
    {m : ℝ} (hm : 4 < m) :
    Summable (polynomialCriticalPrimeLowLogHeadResponse m hm.le) := by
  classical
  let Op : MomentFock →L[ℂ] MomentFock :=
    polynomialCriticalPrimeSamplingIncidence m hm.le
  have hcpt : IsCompactOperator Op :=
    polynomialCriticalPrimeSamplingIncidence_isCompactOperator hm
  have hcoord : ∀ p : Nat.Primes, Summable fun j =>
      ‖criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p
        (svVec (energyOp Op) j)‖ ^ 2 := by
    intro p
    let k : MomentFock := criticalPrimeMomentFockKernel
      (polynomialMomentFockData m (by linarith)) p
    have hs := summable_inner_svVec_sq hcpt k
    have hmul := Summable.mul_left (criticalPrimeSamplingWeight p) hs
    apply hmul.congr
    intro j
    rw [criticalPrimeKernelRestriction_apply, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (criticalPrimeSamplingWeight_pos p).le]
    simp only [k, norm_inner_symm]
  unfold polynomialCriticalPrimeLowLogHeadResponse
  induction criticalPrimeFockLowLogHead using Finset.induction_on with
  | empty => simp
  | @insert p H hp ih =>
      simpa [Finset.sum_insert hp] using (hcoord p).add ih

theorem summable_rpow_polynomialCriticalPrimeLowLogHeadResponse
    {m q : ℝ} (hm : 4 < m) (hq : 1 ≤ q) :
    Summable fun j => polynomialCriticalPrimeLowLogHeadResponse m hm.le j ^ q :=
  summable_rpow_of_nonneg_of_summable_of_one_le
    (polynomialCriticalPrimeLowLogHeadResponse_nonneg m hm.le)
    (summable_polynomialCriticalPrimeLowLogHeadResponse hm) hq

def polynomialCriticalPrimeFiniteResponse
    (m : ℝ) (hm : 4 ≤ m) (P : Finset Nat.Primes) (j : ℕ) : ℝ :=
  ∑ p ∈ P, ‖criticalPrimeKernelRestriction
    (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p
    (svVec (energyOp (polynomialCriticalPrimeSamplingIncidence m hm)) j)‖ ^ 2

theorem polynomialCriticalPrimeFiniteResponse_nonneg
    (m : ℝ) (hm : 4 ≤ m) (P : Finset Nat.Primes) (j : ℕ) :
    0 ≤ polynomialCriticalPrimeFiniteResponse m hm P j :=
  Finset.sum_nonneg fun _p _ => sq_nonneg _

theorem polynomialCriticalPrimeFiniteResponse_le_head_add_tail
    {m : ℝ} (hm : 4 ≤ m) (P : Finset Nat.Primes) (j : ℕ) :
    polynomialCriticalPrimeFiniteResponse m hm P j ≤
      polynomialCriticalPrimeLowLogHeadResponse m hm j +
        polynomialCriticalPrimeFiniteResponse m hm
          (P.filter fun p => 2 ≤ Real.log (p : ℝ)) j := by
  classical
  let f : Nat.Primes → ℝ := fun p => ‖criticalPrimeKernelRestriction
    (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p
    (svVec (energyOp (polynomialCriticalPrimeSamplingIncidence m hm)) j)‖ ^ 2
  let Q : Finset Nat.Primes := P.filter fun p => 2 ≤ Real.log (p : ℝ)
  let L : Finset Nat.Primes := P.filter fun p => ¬ 2 ≤ Real.log (p : ℝ)
  have hLsub : L ⊆ criticalPrimeFockLowLogHead := by
    intro p hp
    exact mem_criticalPrimeFockLowLogHead_of_log_lt_two p
      (lt_of_not_ge (Finset.mem_filter.mp hp).2)
  have hLle : (∑ p ∈ L, f p) ≤ ∑ p ∈ criticalPrimeFockLowLogHead, f p :=
    Finset.sum_le_sum_of_subset_of_nonneg hLsub (fun p _ _ => sq_nonneg _)
  calc
    polynomialCriticalPrimeFiniteResponse m hm P j =
        (∑ p ∈ Q, f p) + ∑ p ∈ L, f p := by
      rw [Finset.sum_filter_add_sum_filter_not P
        (fun p => 2 ≤ Real.log (p : ℝ)) f]
      rfl
    _ ≤ (∑ p ∈ Q, f p) + ∑ p ∈ criticalPrimeFockLowLogHead, f p :=
      add_le_add le_rfl hLle
    _ = polynomialCriticalPrimeLowLogHeadResponse m hm j +
        polynomialCriticalPrimeFiniteResponse m hm Q j := by
      rw [add_comm]
      rfl

theorem sum_rpow_polynomialCriticalPrimeFiniteResponse_le_uniform
    {m q : ℝ} (hm : 4 < m) (hq : criticalPrimeFockSchattenThreshold m < q)
    (P : Finset Nat.Primes) (S : Finset ℕ) :
    (∑ j ∈ S, polynomialCriticalPrimeFiniteResponse m hm.le P j ^ q) ≤
      2 ^ q * ((∑' j : ℕ, polynomialCriticalPrimeLowLogHeadResponse m hm.le j ^ q) +
        Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) ^ q *
          (Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
            3 ^ (m / 2 - 1)) *
          ∑' n : ℕ, criticalPrimeFockScaledAdaptedCellMass m
            (criticalPrimeFockOverlapCellScale m) n ^ q) := by
  classical
  let Q : Finset Nat.Primes := P.filter fun p => 2 ≤ Real.log (p : ℝ)
  have hq1 : 1 < q := lt_trans (criticalPrimeFockSchattenThreshold_gt_one hm) hq
  have hq0 : 0 ≤ q := by linarith
  have hheadsum := summable_rpow_polynomialCriticalPrimeLowLogHeadResponse hm hq1.le
  have hhead : (∑ j ∈ S, polynomialCriticalPrimeLowLogHeadResponse m hm.le j ^ q) ≤
      ∑' j : ℕ, polynomialCriticalPrimeLowLogHeadResponse m hm.le j ^ q :=
    hheadsum.sum_le_tsum S (fun j _ =>
      Real.rpow_nonneg (polynomialCriticalPrimeLowLogHeadResponse_nonneg m hm.le j) _)
  have htail :
      (∑ j ∈ S, polynomialCriticalPrimeFiniteResponse m hm.le Q j ^ q) ≤
        Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) ^ q *
          (Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
            3 ^ (m / 2 - 1)) *
          ∑' n : ℕ, criticalPrimeFockScaledAdaptedCellMass m
            (criticalPrimeFockOverlapCellScale m) n ^ q := by
    simpa only [polynomialCriticalPrimeFiniteResponse, Q] using
      sum_rpow_finiteTailCriticalPrimeResponse_svVec_le_cellMassTsum hm hq Q
        (fun p hp => (Finset.mem_filter.mp hp).2) S
  calc
    (∑ j ∈ S, polynomialCriticalPrimeFiniteResponse m hm.le P j ^ q) ≤
        ∑ j ∈ S, 2 ^ q *
          (polynomialCriticalPrimeLowLogHeadResponse m hm.le j ^ q +
            polynomialCriticalPrimeFiniteResponse m hm.le Q j ^ q) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        polynomialCriticalPrimeFiniteResponse m hm.le P j ^ q ≤
            (polynomialCriticalPrimeLowLogHeadResponse m hm.le j +
              polynomialCriticalPrimeFiniteResponse m hm.le Q j) ^ q :=
          Real.rpow_le_rpow
            (polynomialCriticalPrimeFiniteResponse_nonneg m hm.le P j)
            (polynomialCriticalPrimeFiniteResponse_le_head_add_tail hm.le P j) hq0
        _ ≤ _ := GaloisForLFunctions.HTGeometry.rpow_add_le_two_rpow_mul
          (polynomialCriticalPrimeLowLogHeadResponse_nonneg m hm.le j)
          (polynomialCriticalPrimeFiniteResponse_nonneg m hm.le Q j) hq0
    _ = 2 ^ q * ((∑ j ∈ S,
        polynomialCriticalPrimeLowLogHeadResponse m hm.le j ^ q) +
        ∑ j ∈ S, polynomialCriticalPrimeFiniteResponse m hm.le Q j ^ q) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := by gcongr

theorem tsum_normSq_criticalPrimeKernelRestriction_svVec_eq_singVal
    {m : ℝ} (hm : 4 < m) (j : ℕ) :
    (∑' p : Nat.Primes, ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p
      (svVec (energyOp (polynomialCriticalPrimeSamplingIncidence m hm.le)) j)‖ ^ 2) =
      singVal (polynomialCriticalPrimeSamplingIncidence m hm.le) j := by
  let Op : MomentFock →L[ℂ] MomentFock :=
    polynomialCriticalPrimeSamplingIncidence m hm.le
  let v : MomentFock := svVec (energyOp Op) j
  have hcpt : IsCompactOperator Op :=
    polynomialCriticalPrimeSamplingIncidence_isCompactOperator hm
  have hquad := re_inner_criticalPrimeSamplingIncidence_apply_eq_tsum_normSq
    (polynomialCriticalPrimeSamplingOperator m hm.le) v
  have heig := re_inner_svVec_apply_of_nonneg hcpt
    ((nonneg_iff_isPositive Op).2 (by
      simpa only [Op] using polynomialCriticalPrimeSamplingIncidence_isPositive m hm.le)) j
  calc
    (∑' p : Nat.Primes, ‖criticalPrimeKernelRestriction
      (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p v‖ ^ 2) =
        (inner ℂ (Op v) v).re := by
      simpa only [Op, v, polynomialCriticalPrimeSamplingIncidence,
        polynomialCriticalPrimeSamplingOperator_apply] using hquad.symm
    _ = (inner ℂ v (Op v)).re := by
      have h := congrArg Complex.re (inner_conj_symm (Op v) v)
      simpa only [Complex.conj_re] using h.symm
    _ = singVal Op j := heig

/-- Exact upper half of the polynomial critical-prime Schatten phase transition. -/
theorem polynomialCriticalPrimeSamplingIncidence_memSchattenClass_of_threshold_lt
    {m q : ℝ} (hm : 4 < m) (hq : criticalPrimeFockSchattenThreshold m < q) :
    MemSchattenClass q (polynomialCriticalPrimeSamplingIncidence m hm.le) := by
  classical
  let Op : MomentFock →L[ℂ] MomentFock :=
    polynomialCriticalPrimeSamplingIncidence m hm.le
  let C : ℝ :=
    2 ^ q * ((∑' j : ℕ, polynomialCriticalPrimeLowLogHeadResponse m hm.le j ^ q) +
      Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) ^ q *
        (Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
          3 ^ (m / 2 - 1)) *
        ∑' n : ℕ, criticalPrimeFockScaledAdaptedCellMass m
          (criticalPrimeFockOverlapCellScale m) n ^ q)
  have hq1 : 1 < q := lt_trans (criticalPrimeFockSchattenThreshold_gt_one hm) hq
  have hq0 : 0 ≤ q := by linarith
  have hcpt : IsCompactOperator Op :=
    polynomialCriticalPrimeSamplingIncidence_isCompactOperator hm
  have hfinite : ∀ S : Finset ℕ, (∑ j ∈ S, singVal Op j ^ q) ≤ C := by
    intro S
    have htend : Tendsto
        (fun P : Finset Nat.Primes =>
          ∑ j ∈ S, polynomialCriticalPrimeFiniteResponse m hm.le P j ^ q)
        atTop (nhds (∑ j ∈ S, singVal Op j ^ q)) := by
      apply tendsto_finsetSum S
      intro j hj
      have hsR := summable_normSq_criticalPrimeKernelRestriction_polynomial hm.le
        (svVec (energyOp Op) j)
      have hsNat : Summable fun p : Nat.Primes => ‖criticalPrimeKernelRestriction
          (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p
          (svVec (energyOp Op) j)‖ ^ 2 := by
        apply hsR.congr
        intro p
        exact Real.rpow_two _
      have hhas := hsNat.hasSum
      have hlimit := tsum_normSq_criticalPrimeKernelRestriction_svVec_eq_singVal hm j
      rw [hlimit] at hhas
      have hbase : Tendsto
          (fun P : Finset Nat.Primes => polynomialCriticalPrimeFiniteResponse m hm.le P j)
          atTop (nhds (singVal Op j)) := by
        change Tendsto (fun P : Finset Nat.Primes => ∑ p ∈ P,
          ‖criticalPrimeKernelRestriction
            (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p
            (svVec (energyOp Op) j)‖ ^ 2) atTop (nhds (singVal Op j))
        change Tendsto (fun P : Finset Nat.Primes => ∑ p ∈ P,
          ‖criticalPrimeKernelRestriction
            (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p
            (svVec (energyOp Op) j)‖ ^ 2) atTop (nhds (singVal Op j)) at hhas
        simpa only [polynomialCriticalPrimeFiniteResponse, Op] using hhas
      exact (Real.continuous_rpow_const hq0).tendsto (singVal Op j) |>.comp hbase
    exact le_of_tendsto htend (Filter.Eventually.of_forall fun P =>
      sum_rpow_polynomialCriticalPrimeFiniteResponse_le_uniform hm hq P S)
  have hsSing : Summable fun j => singVal Op j ^ q :=
    summable_of_sum_le (fun j => Real.rpow_nonneg (singVal_nonneg Op j) _) hfinite
  unfold MemSchattenClass
  apply hsSing.congr
  intro j
  rw [approxNumber_eq_singVal hcpt j]

theorem polynomialCriticalPrimeSamplingIncidence_memSchattenClass_iff
    {m q : ℝ} (hm : 4 < m) (hq : 0 < q) :
    MemSchattenClass q (polynomialCriticalPrimeSamplingIncidence m hm.le) ↔
      criticalPrimeFockSchattenThreshold m < q := by
  constructor
  · intro hmem
    exact lt_of_not_ge fun hle =>
      polynomialCriticalPrimeSamplingIncidence_not_memSchattenClass_of_pos_of_le_threshold
        hm hq hle hmem
  · exact polynomialCriticalPrimeSamplingIncidence_memSchattenClass_of_threshold_lt hm

/-- Exact rectangular Schatten threshold of the literal normalized critical-prime sampler. -/
theorem polynomialCriticalPrimeSamplingOperator_memRectSchattenClass_iff
    {m r : ℝ} (hm : 4 < m) (hr : 0 < r) :
    MemRectSchattenClass r (polynomialCriticalPrimeSamplingOperator m hm.le) ↔
      2 * criticalPrimeFockSchattenThreshold m < r := by
  let S : MomentFock →L[ℂ] CriticalPrimeEllTwo :=
    polynomialCriticalPrimeSamplingOperator m hm.le
  have hcompact : IsCompactOperator S :=
    polynomialCriticalPrimeSamplingOperator_isCompactOperator hm
  have hbridge :=
    memRectSchattenClass_two_mul_iff_memSchattenClass_criticalPrimeSamplingIncidence
      S hcompact (r / 2)
  have hincidence := polynomialCriticalPrimeSamplingIncidence_memSchattenClass_iff
    hm (by linarith : 0 < r / 2)
  constructor
  · intro hS
    have hS' : MemRectSchattenClass (2 * (r / 2)) S := by
      convert hS using 1 <;> ring
    have hT := hincidence.mp (hbridge.mp hS')
    linarith
  · intro hrThreshold
    have hT : MemSchattenClass (r / 2) (criticalPrimeSamplingIncidence S) :=
      hincidence.mpr (by linarith)
    have hS' := hbridge.mpr hT
    change MemRectSchattenClass r S
    convert hS' using 1 <;> ring

end

end RHTower
