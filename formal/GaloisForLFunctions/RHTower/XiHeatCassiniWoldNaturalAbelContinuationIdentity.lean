import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalLogMeshContinuation
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldPrimeZetaLaplaceSymbol
import GaloisForLFunctions.RHTower.DirichletAbel
import GaloisForLFunctions.RHTower.DirichletIncrementSummable
import GaloisForLFunctions.HTGeometry.BarnesOrderOnePartialFractions

/-!
# Natural Wold Abel continuation and safe identity

Assume one natural Wold residual square energy at radius `t > 1/2`.
The resulting critical weighted `l¹` bound makes the residual first-difference
Abel current holomorphic on `re s > -1/2`.

The module then proves the exact natural-cutoff summation-by-parts identity

`WoldCurrent(s) = residualAbel(s) + holonomy + integerLogMesh(s)`

on `re s > 0`. Prime reindexing is literal: the natural Wold weight vanishes
off primes and its prime-supported sum is the corpus ordered Wold current.
This is the safe germ needed for zeta-cleared analytic continuation in the
T2 square-energy no-go.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

local notation "R" => xiHeatCassiniWoldNatResidualLogDiscrepancy

theorem norm_woldNatResidualAbelAtom_le_of_re_ge_neg_half
    {s : ℂ} (hsre : -(1 / 2 : ℝ) ≤ s.re) (N : ℕ) :
    ‖woldNatResidualAbelAtom s N‖ ≤
      ‖s‖ * (|R (N + 1)| * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by
  by_cases hs0 : s = 0
  · subst s
    simp [woldNatResidualAbelAtom]
  have hm : 0 < (N : ℝ) + 1 := by positivity
  have ht : (N : ℝ) + 2 ∈ Set.Icc ((N : ℝ) + 1) (((N : ℝ) + 1) + 1) := by
    constructor <;> linarith
  have hwne : -s ≠ 0 := neg_ne_zero.mpr hs0
  have hwre : (-s).re ≤ 1 := by
    simp only [neg_re]
    linarith
  have hinc := GaloisForLFunctions.HTGeometry.norm_ofReal_cpow_sub_le
    hwne hwre hm ht
  have hexp : (-s).re - 1 ≤ -(1 / 2 : ℝ) := by
    simp only [neg_re]
    linarith
  have hbase : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have hN : (0 : ℝ) ≤ N := by positivity
    linarith
  have hpow : ((N : ℝ) + 1) ^ ((-s).re - 1) ≤
      ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  rw [norm_sub_rev] at hinc
  have hinc' :
      ‖(((((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) -
          ((((N : ℝ) + 2 : ℝ) : ℂ) ^ (-s)))‖ ≤
        ‖s‖ * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
    calc
      ‖(((((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) -
          ((((N : ℝ) + 2 : ℝ) : ℂ) ^ (-s)))‖ ≤
          ‖-s‖ * ((N : ℝ) + 1) ^ ((-s).re - 1) := hinc
      _ ≤ ‖-s‖ * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = ‖s‖ * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by rw [norm_neg]
  rw [woldNatResidualAbelAtom, norm_mul, norm_real, Real.norm_eq_abs]
  calc
    |R (N + 1)| *
        ‖(((((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) -
          ((((N : ℝ) + 2 : ℝ) : ℂ) ^ (-s)))‖ ≤
        |R (N + 1)| *
          (‖s‖ * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hinc' (abs_nonneg _)
    _ = ‖s‖ *
        (|R (N + 1)| * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ))) := by ring

theorem differentiableAt_woldNatResidualAbelCurrent_of_squareEnergy
    {t : ℝ} (ht : 1 / 2 < t) (hEnergy : WoldNatResidualSquareEnergy t)
    {s : ℂ} (hs : -(1 / 2 : ℝ) < s.re) :
    DifferentiableAt ℂ woldNatResidualAbelCurrent s := by
  let radius : ℝ := (s.re + 1 / 2) / 2
  have hradius : 0 < radius := by dsimp only [radius]; linarith
  let q : ℕ → ℝ := fun N =>
    |R (N + 1)| * ((N : ℝ) + 1) ^ (-(1 / 2 : ℝ))
  let bound : ℕ → ℝ := fun N => (‖s‖ + radius) * q N
  have hq : Summable q :=
    summable_abs_woldNatResidual_mul_succ_rpow_neg_half_of_squareEnergy ht hEnergy
  have hboundSum : Summable bound := hq.mul_left (‖s‖ + radius)
  have hdiff : ∀ N : ℕ,
      DifferentiableOn ℂ (woldNatResidualAbelAtom · N) (Metric.ball s radius) := by
    intro N z hz
    have hbase1 : ((((N : ℝ) + 1 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show (N : ℝ) + 1 ≠ 0 by positivity)
    have hbase2 : ((((N : ℝ) + 2 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show (N : ℝ) + 2 ≠ 0 by positivity)
    unfold woldNatResidualAbelAtom
    exact ((((differentiableAt_id.neg).const_cpow (Or.inl hbase1)).sub
      ((differentiableAt_id.neg).const_cpow (Or.inl hbase2))).const_mul
        (R (N + 1) : ℂ)).differentiableWithinAt
  have hbound : ∀ N : ℕ, ∀ z ∈ Metric.ball s radius,
      ‖woldNatResidualAbelAtom z N‖ ≤ bound N := by
    intro N z hz
    have hdist : ‖z - s‖ < radius := by
      rw [Metric.mem_ball, dist_eq] at hz
      exact hz
    have hreNorm : |(z - s).re| ≤ ‖z - s‖ := abs_re_le_norm (z - s)
    have hzre : -(1 / 2 : ℝ) ≤ z.re := by
      simp only [sub_re] at hreNorm
      have hleft : -‖z - s‖ ≤ z.re - s.re := by
        exact (abs_le.mp hreNorm).1
      dsimp only [radius] at hdist
      linarith
    have hnorm : ‖z‖ ≤ ‖s‖ + radius := by
      calc
        ‖z‖ = ‖(z - s) + s‖ := by ring_nf
        _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
        _ ≤ ‖s‖ + radius := by linarith
    have hqnonneg : 0 ≤ q N := by dsimp only [q]; positivity
    calc
      ‖woldNatResidualAbelAtom z N‖ ≤ ‖z‖ * q N := by
        simpa only [q] using
          norm_woldNatResidualAbelAtom_le_of_re_ge_neg_half hzre N
      _ ≤ (‖s‖ + radius) * q N :=
        mul_le_mul_of_nonneg_right hnorm hqnonneg
      _ = bound N := rfl
  change DifferentiableAt ℂ
    (fun z : ℂ => ∑' N : ℕ, woldNatResidualAbelAtom z N) s
  exact GaloisForLFunctions.HTGeometry.differentiableAt_tsum_of_cauchy_dominated
    hradius hdiff hbound hboundSum

theorem xiHeatCassiniWoldNatWeightSum_succ (N : ℕ) :
    xiHeatCassiniWoldNatWeightSum (N + 1) =
      xiHeatCassiniWoldNatWeightSum N + xiHeatCassiniWoldNatWeight (N + 1) := by
  rw [xiHeatCassiniWoldNatWeightSum, xiHeatCassiniWoldNatWeightSum,
    Sieve.Icc_zero_eq_range, Sieve.Icc_zero_eq_range]
  rw [Finset.sum_range_succ]

theorem xiHeatCassiniWoldNatResidualLogDiscrepancy_succ_sub
    (N : ℕ) :
    R (N + 1) - R N =
      xiHeatCassiniWoldNatWeight (N + 1) -
        (Real.log (N + 1) - Real.log N) := by
  rw [xiHeatCassiniWoldNatResidualLogDiscrepancy,
    xiHeatCassiniWoldNatResidualLogDiscrepancy,
    xiHeatCassiniWoldNatWeightSum_succ]
  push_cast
  ring

@[simp] theorem xiHeatCassiniWoldNatWeight_zero :
    xiHeatCassiniWoldNatWeight 0 = 0 := by
  unfold xiHeatCassiniWoldNatWeight
  split_ifs with h
  · exact False.elim (h.ne_zero rfl)
  · rfl

@[simp] theorem xiHeatCassiniWoldNatWeight_one :
    xiHeatCassiniWoldNatWeight 1 = 0 := by
  unfold xiHeatCassiniWoldNatWeight
  split_ifs with h
  · exact False.elim (h.ne_one rfl)
  · rfl

@[simp] theorem xiHeatCassiniWoldNatWeightSum_zero :
    xiHeatCassiniWoldNatWeightSum 0 = 0 := by
  rw [xiHeatCassiniWoldNatWeightSum, Sieve.Icc_zero_eq_range]
  simp

@[simp] theorem xiHeatCassiniWoldNatWeightSum_one :
    xiHeatCassiniWoldNatWeightSum 1 = 0 := by
  rw [xiHeatCassiniWoldNatWeightSum, Sieve.Icc_zero_eq_range]
  norm_num [Finset.sum_range_succ]

def woldNatDifferenceCoeff : ℕ → ℂ
  | 0 => (xiHeatCassiniWoldNatWeight 1 : ℂ)
  | N + 1 =>
      (xiHeatCassiniWoldNatWeight (N + 2) : ℂ) -
        (integerLogMeshIncrement N : ℂ)

theorem coeffPartial_woldNatDifferenceCoeff (k : ℕ) :
    coeffPartial woldNatDifferenceCoeff k =
      (R k + xiHeatCassiniWoldLogHolonomyConstant : ℂ) := by
  induction k with
  | zero =>
      simp [coeffPartial, xiHeatCassiniWoldNatResidualLogDiscrepancy]
  | succ k ih =>
      rcases k with _ | k
      · simp [coeffPartial, woldNatDifferenceCoeff,
          xiHeatCassiniWoldNatResidualLogDiscrepancy]
      · rw [coeffPartial, Finset.sum_range_succ]
        rw [← coeffPartial, ih, woldNatDifferenceCoeff]
        have hdiff :=
          xiHeatCassiniWoldNatResidualLogDiscrepancy_succ_sub (k + 1)
        have hR : R (k + 2) =
            R (k + 1) + xiHeatCassiniWoldNatWeight (k + 2) -
              (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) := by
          norm_num [Nat.cast_add, Nat.cast_one] at hdiff
          ring_nf at hdiff ⊢
          linarith
        rw [integerLogMeshIncrement]
        rw [hR]
        push_cast
        ring

theorem norm_coeffPartial_woldNatDifferenceCoeff_le (k : ℕ) :
    ‖coeffPartial woldNatDifferenceCoeff k‖ ≤
      mertensPrimeWindowBound + xiHeatCassiniWoldNatTraceCorrectionMass := by
  rw [coeffPartial_woldNatDifferenceCoeff]
  have hcast : (R k : ℂ) + (xiHeatCassiniWoldLogHolonomyConstant : ℂ) =
      ((R k + xiHeatCassiniWoldLogHolonomyConstant : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  rw [norm_real, Real.norm_eq_abs]
  rw [xiHeatCassiniWoldNatResidualLogDiscrepancy]
  ring_nf
  rcases k with _ | k
  · simp
    exact add_nonneg mertensPrimeWindowBound_nonneg
      (tsum_nonneg xiHeatCassiniWoldNatTraceCorrection_nonneg)
  · exact abs_xiHeatCassiniWoldNatWeightSum_sub_log_le (k + 1) (by omega)

def naturalCpowKernel (s : ℂ) (N : ℕ) : ℂ :=
  ((((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s))

def naturalCpowIncrement (s : ℂ) (N : ℕ) : ℂ :=
  naturalCpowKernel s N - naturalCpowKernel s (N + 1)

theorem summable_naturalCpowKernel_sub_succ {s : ℂ} (hs : 0 < s.re) :
    Summable (naturalCpowIncrement s) := by
  have h := Summable.of_norm
    (GaloisForLFunctions.RHTower.summable_norm_cpow_increment hs)
  exact h.congr fun N => by
    rw [naturalCpowIncrement, naturalCpowKernel, naturalCpowKernel]
    congr 2
    push_cast
    ring

theorem tendsto_naturalCpowKernel_atTop {s : ℂ} (hs : 0 < s.re) :
    Tendsto (naturalCpowKernel s) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hreal :=
    (GaloisForLFunctions.RHTower.tendsto_rpow_neg_nat_atTop hs).comp
      (Filter.tendsto_add_atTop_nat 1)
  change Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ)) ^ (-s.re)) atTop (𝓝 0) at hreal
  have hnorm : (fun N : ℕ => ‖naturalCpowKernel s N‖) =
      fun N : ℕ => ((N : ℝ) + 1) ^ (-s.re) := by
    funext N
    rw [naturalCpowKernel, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [neg_re]
  rw [hnorm]
  simpa only [Nat.cast_add, Nat.cast_one] using hreal

theorem tsum_naturalCpowKernel_sub_succ {s : ℂ} (hs : 0 < s.re) :
    (∑' N : ℕ, naturalCpowIncrement s N) = 1 := by
  have h := GaloisForLFunctions.HTGeometry.tsum_telescope
    (summable_naturalCpowKernel_sub_succ hs)
    (tendsto_naturalCpowKernel_atTop hs)
  change (∑' N : ℕ, naturalCpowIncrement s N) = naturalCpowKernel s 0 at h
  calc
    (∑' N : ℕ, naturalCpowIncrement s N) = naturalCpowKernel s 0 := h
    _ = 1 := by simp [naturalCpowKernel]

theorem abelDirichlet_woldNatDifferenceCoeff_eq
    {t : ℝ} (ht : 1 / 2 < t) (hEnergy : WoldNatResidualSquareEnergy t)
    {s : ℂ} (hs : 0 < s.re) :
    abelDirichlet woldNatDifferenceCoeff s =
      woldNatResidualAbelCurrent s +
        (xiHeatCassiniWoldLogHolonomyConstant : ℂ) := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hA := summable_woldNatResidualAbelAtom_of_squareEnergy
    ht hEnergy hs0 (by linarith : -(1 / 2 : ℝ) ≤ s.re)
  have hD := summable_naturalCpowKernel_sub_succ hs
  have hCD := hD.mul_left (xiHeatCassiniWoldLogHolonomyConstant : ℂ)
  rw [abelDirichlet, woldNatResidualAbelCurrent]
  calc
    (∑' k : ℕ, coeffPartial woldNatDifferenceCoeff (k + 1) *
        (((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) -
          ((((k : ℝ) + 2 : ℝ) : ℂ) ^ (-s)))) =
        ∑' k : ℕ, (woldNatResidualAbelAtom s k +
          (xiHeatCassiniWoldLogHolonomyConstant : ℂ) *
            naturalCpowIncrement s k) := by
      apply tsum_congr
      intro k
      rw [coeffPartial_woldNatDifferenceCoeff]
      rw [woldNatResidualAbelAtom, naturalCpowIncrement,
        naturalCpowKernel, naturalCpowKernel]
      push_cast
      ring
    _ = (∑' k : ℕ, woldNatResidualAbelAtom s k) +
          ∑' k : ℕ, (xiHeatCassiniWoldLogHolonomyConstant : ℂ) *
            naturalCpowIncrement s k :=
      hA.tsum_add hCD
    _ = (∑' k : ℕ, woldNatResidualAbelAtom s k) +
          (xiHeatCassiniWoldLogHolonomyConstant : ℂ) := by
      rw [tsum_mul_left, tsum_naturalCpowKernel_sub_succ hs, mul_one]

def woldNatLaplaceAtom (s : ℂ) (n : ℕ) : ℂ :=
  (xiHeatCassiniWoldNatWeight n : ℂ) * (((n : ℕ) : ℂ) ^ (-s))

def woldNatLaplaceCurrent (s : ℂ) : ℂ :=
  ∑' n : ℕ, woldNatLaplaceAtom s n

theorem summable_woldNatLaplaceAtom {s : ℂ} (hs : 0 < s.re) :
    Summable (woldNatLaplaceAtom s) := by
  classical
  let e : Nat.Primes → ℕ := fun p => (p : ℕ)
  have he : Function.Injective e := Nat.Primes.coe_nat_injective
  have hzero : ∀ n : ℕ, n ∉ Set.range e → woldNatLaplaceAtom s n = 0 := by
    intro n hn
    have hnp : ¬ n.Prime := by
      intro hp
      exact hn ⟨⟨n, hp⟩, rfl⟩
    simp [woldNatLaplaceAtom, xiHeatCassiniWoldNatWeight, hnp]
  rw [← he.summable_iff hzero]
  have hordered := summable_xiHeatCassiniWoldLaplaceAtom hs
  have hprime : Summable (fun p : Nat.Primes =>
      (woldCoeff 1 p : ℂ) * coronaPrimeEigenvalue s p) := by
    apply nthPrimeEquiv.summable_iff.mp
    exact hordered.congr fun N => by
      rw [xiHeatCassiniWoldLaplaceAtom,
        xiHeatCassiniOrderedPrimeLaplacePhase_eq_coronaPrimeEigenvalue]
      simp only [Function.comp_apply, nthPrimeEquiv_apply]
  exact hprime.congr fun p => by
    simp only [Function.comp_apply, e, woldNatLaplaceAtom,
      xiHeatCassiniWoldNatWeight, dif_pos p.2, coronaPrimeEigenvalue]
    congr 2

theorem woldNatLaplaceCurrent_eq_woldLaplaceCurrent (s : ℂ) :
    woldNatLaplaceCurrent s = xiHeatCassiniWoldLaplaceCurrent s := by
  classical
  let e : Nat.Primes → ℕ := fun p => (p : ℕ)
  have he : Function.Injective e := Nat.Primes.coe_nat_injective
  have hzero : ∀ n : ℕ, n ∉ Set.range e → woldNatLaplaceAtom s n = 0 := by
    intro n hn
    have hnp : ¬ n.Prime := by
      intro hp
      exact hn ⟨⟨n, hp⟩, rfl⟩
    simp [woldNatLaplaceAtom, xiHeatCassiniWoldNatWeight, hnp]
  have hsupp : Function.support (woldNatLaplaceAtom s) ⊆ Set.range e := by
    intro n hn
    by_contra hnr
    exact hn (hzero n hnr)
  rw [woldNatLaplaceCurrent, ← he.tsum_eq hsupp,
    xiHeatCassiniWoldLaplaceCurrent_eq_prime_tsum]
  apply tsum_congr
  intro p
  simp only [e, woldNatLaplaceAtom,
    xiHeatCassiniWoldNatWeight, dif_pos p.2, coronaPrimeEigenvalue]
  congr 2

def shiftedIntegerLogMeshAtom (s : ℂ) : ℕ → ℂ
  | 0 => 0
  | N + 1 => integerLogMeshAtom s N

def woldNatDifferenceDirichletAtom (s : ℂ) (N : ℕ) : ℂ :=
  naturalCpowKernel s N * woldNatDifferenceCoeff N

theorem woldNatDifferenceDirichletAtom_eq (s : ℂ) (N : ℕ) :
    woldNatDifferenceDirichletAtom s N =
      woldNatLaplaceAtom s (N + 1) - shiftedIntegerLogMeshAtom s N := by
  rcases N with _ | N
  · simp [woldNatDifferenceDirichletAtom, woldNatDifferenceCoeff,
      woldNatLaplaceAtom, shiftedIntegerLogMeshAtom]
  · rw [woldNatDifferenceDirichletAtom, woldNatDifferenceCoeff,
      woldNatLaplaceAtom, shiftedIntegerLogMeshAtom,
      naturalCpowKernel, integerLogMeshAtom]
    push_cast
    ring

theorem summable_shiftedIntegerLogMeshAtom {s : ℂ} (hs : 0 < s.re) :
    Summable (shiftedIntegerLogMeshAtom s) := by
  have htail : Summable (fun N : ℕ => shiftedIntegerLogMeshAtom s (N + 1)) := by
    simpa only [shiftedIntegerLogMeshAtom] using summable_integerLogMeshAtom (s := s) hs
  exact (summable_nat_add_iff 1).mp htail

theorem summable_woldNatDifferenceDirichletAtom {s : ℂ} (hs : 0 < s.re) :
    Summable (woldNatDifferenceDirichletAtom s) := by
  have hwShift : Summable (fun N : ℕ => woldNatLaplaceAtom s (N + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_woldNatLaplaceAtom hs)
  have hm := summable_shiftedIntegerLogMeshAtom hs
  exact (hwShift.sub hm).congr fun N =>
    (woldNatDifferenceDirichletAtom_eq s N).symm

theorem tsum_woldNatLaplaceAtom_succ {s : ℂ} (hs : 0 < s.re) :
    (∑' N : ℕ, woldNatLaplaceAtom s (N + 1)) = woldNatLaplaceCurrent s := by
  have h := (summable_woldNatLaplaceAtom hs).sum_add_tsum_nat_add 1
  have h0 : woldNatLaplaceAtom s 0 = 0 := by
    simp [woldNatLaplaceAtom]
  rw [Finset.sum_range_one, h0, zero_add] at h
  simpa only [woldNatLaplaceCurrent] using h

theorem tsum_shiftedIntegerLogMeshAtom {s : ℂ} (hs : 0 < s.re) :
    (∑' N : ℕ, shiftedIntegerLogMeshAtom s N) = integerLogMeshCurrent s := by
  have hm := summable_shiftedIntegerLogMeshAtom hs
  have h := hm.sum_add_tsum_nat_add 1
  simpa [shiftedIntegerLogMeshAtom, integerLogMeshCurrent] using h.symm

theorem tsum_woldNatDifferenceDirichletAtom {s : ℂ} (hs : 0 < s.re) :
    (∑' N : ℕ, woldNatDifferenceDirichletAtom s N) =
      xiHeatCassiniWoldLaplaceCurrent s - integerLogMeshCurrent s := by
  have hwShift : Summable (fun N : ℕ => woldNatLaplaceAtom s (N + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_woldNatLaplaceAtom hs)
  have hm := summable_shiftedIntegerLogMeshAtom hs
  calc
    (∑' N : ℕ, woldNatDifferenceDirichletAtom s N) =
        ∑' N : ℕ, (woldNatLaplaceAtom s (N + 1) -
          shiftedIntegerLogMeshAtom s N) := by
      apply tsum_congr
      exact woldNatDifferenceDirichletAtom_eq s
    _ = (∑' N : ℕ, woldNatLaplaceAtom s (N + 1)) -
          ∑' N : ℕ, shiftedIntegerLogMeshAtom s N := hwShift.tsum_sub hm
    _ = xiHeatCassiniWoldLaplaceCurrent s - integerLogMeshCurrent s := by
      rw [tsum_woldNatLaplaceAtom_succ hs,
        woldNatLaplaceCurrent_eq_woldLaplaceCurrent,
        tsum_shiftedIntegerLogMeshAtom hs]

theorem abelDirichlet_woldNatDifferenceCoeff_eq_wold_sub_mesh
    {s : ℂ} (hs : 0 < s.re) :
    abelDirichlet woldNatDifferenceCoeff s =
      xiHeatCassiniWoldLaplaceCurrent s - integerLogMeshCurrent s := by
  have hAbel := tendsto_abelDirichlet
    (c := woldNatDifferenceCoeff)
    (B := mertensPrimeWindowBound + xiHeatCassiniWoldNatTraceCorrectionMass)
    norm_coeffPartial_woldNatDifferenceCoeff_le hs
  have hSum := (summable_woldNatDifferenceDirichletAtom hs).hasSum
  have hSeries : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      woldNatDifferenceDirichletAtom s i) atTop
      (𝓝 (∑' N : ℕ, woldNatDifferenceDirichletAtom s N)) :=
    (Summable.hasSum_iff_tendsto_nat
      (summable_woldNatDifferenceDirichletAtom hs)
      (m := ∑' N : ℕ, woldNatDifferenceDirichletAtom s N)).mp hSum
  have hAbel' : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      woldNatDifferenceDirichletAtom s i) atTop
      (𝓝 (abelDirichlet woldNatDifferenceCoeff s)) := by
    apply hAbel.congr'
    filter_upwards with n
    apply Finset.sum_congr rfl
    intro i hi
    rw [woldNatDifferenceDirichletAtom, naturalCpowKernel]
  have heq : abelDirichlet woldNatDifferenceCoeff s =
      ∑' N : ℕ, woldNatDifferenceDirichletAtom s N :=
    tendsto_nhds_unique hAbel' hSeries
  rw [heq, tsum_woldNatDifferenceDirichletAtom hs]

theorem woldLaplaceCurrent_eq_naturalAbel_add_logMesh
    {t : ℝ} (ht : 1 / 2 < t) (hEnergy : WoldNatResidualSquareEnergy t)
    {s : ℂ} (hs : 0 < s.re) :
    xiHeatCassiniWoldLaplaceCurrent s =
      woldNatResidualAbelCurrent s +
        (xiHeatCassiniWoldLogHolonomyConstant : ℂ) +
          integerLogMeshCurrent s := by
  have h1 := abelDirichlet_woldNatDifferenceCoeff_eq ht hEnergy hs
  have h2 := abelDirichlet_woldNatDifferenceCoeff_eq_wold_sub_mesh hs
  linear_combination h1 - h2

end

end RHTower

