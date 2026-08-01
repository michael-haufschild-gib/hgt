import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointHilbertSchmidt
import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointCofinalHolonomy
import GaloisForLFunctions.RHTower.SchattenDoubleCommutatorRelocation
import GaloisForLFunctions.RHTower.XiPrimeMarkedCycleGauge
import GaloisForLFunctions.HTGeometry.FredholmDeterminantInfinite
import Mathlib.NumberTheory.PrimeCounting

/-!
# Source-defined marked-prime RVM relocation

Smooth Riemann--von Mangoldt quantiles give a positive injective reciprocal Hilbert--Schmidt
skeleton on marked primes.  The completed physical endpoint supplies a bounded self-adjoint
Hilbert--Schmidt source operator.  Their double commutator is an unconditional self-adjoint
Schatten-1 relocation with exact matrix entries and cofinal nonzero cycle holonomy.

No Xi divisor or target spectral ordering enters the construction.  This module does not assert
the centered-Xi determinant identity.
-/

open scoped BigOperators InnerProductSpace Nat.Prime

namespace RHTower

noncomputable section

def routeKRVMBase : ℝ := 2 * Real.pi * Real.exp 1

theorem routeKRVMBase_pos : 0 < routeKRVMBase := by
  rw [routeKRVMBase]
  positivity

theorem one_lt_routeKRVMBase : 1 < routeKRVMBase := by
  rw [routeKRVMBase]
  have hpi : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have hexp : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  nlinarith

def routeKSmoothRVMCount (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Real.log (T / routeKRVMBase) + 7 / 8

theorem routeKSmoothRVMCount_base :
    routeKSmoothRVMCount routeKRVMBase = 7 / 8 := by
  rw [routeKSmoothRVMCount]
  have hb0 : routeKRVMBase ≠ 0 := routeKRVMBase_pos.ne'
  rw [div_self hb0, Real.log_one, mul_zero, zero_add]

theorem routeKSmoothRVMCount_strictMonoOn :
    StrictMonoOn routeKSmoothRVMCount (Set.Ioi routeKRVMBase) := by
  intro a ha b hb hab
  have htwoPi : 0 < 2 * Real.pi := by positivity
  have ha0 : 0 < a := routeKRVMBase_pos.trans ha
  have hb0 : 0 < b := routeKRVMBase_pos.trans hb
  have hbase0 := routeKRVMBase_pos
  have haratio : 1 < a / routeKRVMBase :=
    (lt_div_iff₀ hbase0).2 (by simpa using ha)
  have hbratio : 1 < b / routeKRVMBase :=
    (lt_div_iff₀ hbase0).2 (by simpa using hb)
  have hlogA : 0 < Real.log (a / routeKRVMBase) :=
    Real.log_pos haratio
  have hlogB : 0 < Real.log (b / routeKRVMBase) :=
    Real.log_pos hbratio
  have hdiv : a / (2 * Real.pi) < b / (2 * Real.pi) :=
    div_lt_div_of_pos_right hab htwoPi
  have hratio :
      a / routeKRVMBase < b / routeKRVMBase :=
    div_lt_div_of_pos_right hab hbase0
  have hlog :
      Real.log (a / routeKRVMBase) <
        Real.log (b / routeKRVMBase) :=
    Real.strictMonoOn_log
      (zero_lt_one.trans haratio) (zero_lt_one.trans hbratio) hratio
  rw [routeKSmoothRVMCount, routeKSmoothRVMCount]
  gcongr

def routeKRVMUpperWitness (n : ℕ) : ℝ :=
  routeKRVMBase *
    Real.exp (2 * Real.pi * (n + 1 : ℝ))

theorem routeKRVMBase_lt_upperWitness (n : ℕ) :
    routeKRVMBase < routeKRVMUpperWitness n := by
  rw [routeKRVMUpperWitness]
  have hexp : 1 < Real.exp (2 * Real.pi * (n + 1 : ℝ)) := by
    rw [Real.one_lt_exp_iff]
    positivity
  nlinarith [routeKRVMBase_pos]

theorem routeKSmoothRVMCount_upperWitness (n : ℕ) :
    (n + 1 : ℝ) <
      routeKSmoothRVMCount (routeKRVMUpperWitness n) := by
  have hb0 : routeKRVMBase ≠ 0 := routeKRVMBase_pos.ne'
  have htwoPi0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hexpPos :
      0 < Real.exp (2 * Real.pi * (n + 1 : ℝ)) := Real.exp_pos _
  have hlog :
      Real.log
          (routeKRVMUpperWitness n / routeKRVMBase) =
        2 * Real.pi * (n + 1 : ℝ) := by
    rw [routeKRVMUpperWitness, mul_div_cancel_left₀ _ hb0,
      Real.log_exp]
  rw [routeKSmoothRVMCount, hlog, routeKRVMUpperWitness]
  have hb1 : 1 < routeKRVMBase := one_lt_routeKRVMBase
  calc
    (n + 1 : ℝ) <
        routeKRVMBase *
          Real.exp (2 * Real.pi * (n + 1 : ℝ)) *
            (n + 1 : ℝ) + 7 / 8 := by
      have hn : 0 < (n + 1 : ℝ) := by positivity
      have hfactor :
          1 < routeKRVMBase *
            Real.exp (2 * Real.pi * (n + 1 : ℝ)) := by
        have hexpOne :
            1 < Real.exp (2 * Real.pi * (n + 1 : ℝ)) := by
          rw [Real.one_lt_exp_iff]
          positivity
        calc
          1 < routeKRVMBase := hb1
          _ < routeKRVMBase *
              Real.exp (2 * Real.pi * (n + 1 : ℝ)) := by
            nlinarith [routeKRVMBase_pos]
      nlinarith
    _ = routeKRVMBase *
          Real.exp (2 * Real.pi * (n + 1 : ℝ)) /
            (2 * Real.pi) *
              (2 * Real.pi * (n + 1 : ℝ)) + 7 / 8 := by
      field_simp [htwoPi0]
    _ = _ := rfl

theorem continuousOn_routeKSmoothRVMCount_Icc
    {a b : ℝ} (ha : 0 < a) :
    ContinuousOn routeKSmoothRVMCount (Set.Icc a b) := by
  intro x hx
  have hx0 : x ≠ 0 := (ha.trans_le hx.1).ne'
  have hratio0 : x / routeKRVMBase ≠ 0 :=
    div_ne_zero hx0 routeKRVMBase_pos.ne'
  change ContinuousWithinAt
    (fun T : ℝ =>
      T / (2 * Real.pi) * Real.log (T / routeKRVMBase) + 7 / 8)
    (Set.Icc a b) x
  fun_prop

theorem exists_unique_routeKRVMQuantile (n : ℕ) :
    ∃! T : ℝ,
      routeKRVMBase < T ∧
        routeKSmoothRVMCount T = (n + 1 : ℝ) := by
  have hbaseLe : routeKRVMBase ≤ routeKRVMUpperWitness n :=
    (routeKRVMBase_lt_upperWitness n).le
  have htarget :
      (n + 1 : ℝ) ∈ Set.Icc
        (routeKSmoothRVMCount routeKRVMBase)
        (routeKSmoothRVMCount (routeKRVMUpperWitness n)) := by
    constructor
    · rw [routeKSmoothRVMCount_base]
      have hn : 0 ≤ (n : ℝ) := by positivity
      norm_num
      linarith
    · exact (routeKSmoothRVMCount_upperWitness n).le
  obtain ⟨T, hTmem, hTvalue⟩ :=
    intermediate_value_Icc hbaseLe
      (continuousOn_routeKSmoothRVMCount_Icc
        routeKRVMBase_pos) htarget
  have hTgt : routeKRVMBase < T := by
    have hle := hTmem.1
    exact lt_of_le_of_ne hle fun hEq => by
      subst T
      rw [routeKSmoothRVMCount_base] at hTvalue
      have hn : 0 ≤ (n : ℝ) := by positivity
      norm_num at hTvalue
      linarith
  refine ⟨T, ⟨hTgt, hTvalue⟩, ?_⟩
  intro U hU
  exact (routeKSmoothRVMCount_strictMonoOn.injOn
    hTgt hU.1 (hTvalue.trans hU.2.symm)).symm

def routeKRVMQuantile (n : ℕ) : ℝ :=
  Classical.choose (exists_unique_routeKRVMQuantile n)

theorem routeKRVMBase_lt_quantile (n : ℕ) :
    routeKRVMBase < routeKRVMQuantile n :=
  (Classical.choose_spec (exists_unique_routeKRVMQuantile n)).1.1

theorem routeKSmoothRVMCount_quantile (n : ℕ) :
    routeKSmoothRVMCount (routeKRVMQuantile n) =
      (n + 1 : ℝ) :=
  (Classical.choose_spec (exists_unique_routeKRVMQuantile n)).1.2

theorem routeKRVMQuantile_injective :
    Function.Injective routeKRVMQuantile := by
  intro m n h
  have hcount := congrArg routeKSmoothRVMCount h
  rw [routeKSmoothRVMCount_quantile,
    routeKSmoothRVMCount_quantile] at hcount
  have hnat : m + 1 = n + 1 := by exact_mod_cast hcount
  omega

theorem Real.log_le_two_mul_sqrt {x : ℝ} (hx : 1 < x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hsqrt0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hlog :=
    Real.log_le_sub_one_of_pos hsqrt0
  have hlogSqrt :
      Real.log (Real.sqrt x) = (1 / 2 : ℝ) * Real.log x := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hx0]
  rw [hlogSqrt] at hlog
  nlinarith [Real.sqrt_nonneg x]

theorem routeKRVMQuantile_growth_lower (n : ℕ) :
    (n + 1 : ℝ) ≤
      16 * routeKRVMQuantile n *
        Real.sqrt (routeKRVMQuantile n) := by
  let T := routeKRVMQuantile n
  have hTbase : routeKRVMBase < T :=
    routeKRVMBase_lt_quantile n
  have hT0 : 0 < T := routeKRVMBase_pos.trans hTbase
  have hratio : 1 < T / routeKRVMBase :=
    (lt_div_iff₀ routeKRVMBase_pos).2 (by simpa using hTbase)
  have hlog :=
    Real.log_le_two_mul_sqrt hratio
  have hcount := routeKSmoothRVMCount_quantile n
  have hmain :
      (n + 1 : ℝ) ≤
        8 * (T / (2 * Real.pi) *
          Real.log (T / routeKRVMBase)) := by
    rw [routeKSmoothRVMCount] at hcount
    have hn : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hratioLe : T / routeKRVMBase ≤ T := by
    rw [div_le_iff₀ routeKRVMBase_pos]
    nlinarith [one_lt_routeKRVMBase]
  have hsqrtLe :
      Real.sqrt (T / routeKRVMBase) ≤ Real.sqrt T :=
    Real.sqrt_le_sqrt hratioLe
  have htwoPi : 1 ≤ 2 * Real.pi := by
    linarith [Real.pi_gt_three]
  calc
    (n + 1 : ℝ) ≤
        8 * (T / (2 * Real.pi) *
          Real.log (T / routeKRVMBase)) := hmain
    _ ≤ 8 * (T / (2 * Real.pi) *
          (2 * Real.sqrt (T / routeKRVMBase))) := by
      gcongr
    _ ≤ 8 * (T *
          (2 * Real.sqrt (T / routeKRVMBase))) := by
      gcongr
      exact div_le_self hT0.le htwoPi
    _ ≤ 8 * (T * (2 * Real.sqrt T)) := by
      gcongr
    _ = 16 * T * Real.sqrt T := by ring

theorem routeKRVMQuantile_reciprocal_sq_le (n : ℕ) :
    (routeKRVMQuantile n)⁻¹ ^ 2 ≤
      16 ^ (4 / 3 : ℝ) * (n + 1 : ℝ) ^ (-4 / 3 : ℝ) := by
  let T := routeKRVMQuantile n
  let N : ℝ := n + 1
  have hTbase : routeKRVMBase < T :=
    routeKRVMBase_lt_quantile n
  have hT0 : 0 < T := routeKRVMBase_pos.trans hTbase
  have hN0 : 0 < N := by dsimp [N]; positivity
  have hgrowth : N ≤ 16 * T * Real.sqrt T := by
    simpa [T, N] using routeKRVMQuantile_growth_lower n
  have hpow :=
    Real.rpow_le_rpow hN0.le hgrowth (by norm_num : (0 : ℝ) ≤ 4 / 3)
  have hfactor0 : 0 ≤ (16 : ℝ) := by norm_num
  have hpowEq :
      (16 * T * Real.sqrt T) ^ (4 / 3 : ℝ) =
        16 ^ (4 / 3 : ℝ) * T ^ 2 := by
    rw [Real.sqrt_eq_rpow]
    rw [show 16 * T * T ^ (1 / 2 : ℝ) =
        16 * (T * T ^ (1 / 2 : ℝ)) by ring]
    rw [Real.mul_rpow hfactor0
      (mul_nonneg hT0.le (Real.rpow_nonneg hT0.le _))]
    rw [Real.mul_rpow hT0.le (Real.rpow_nonneg hT0.le _)]
    rw [← Real.rpow_mul hT0.le]
    rw [← Real.rpow_add hT0]
    norm_num
  rw [hpowEq] at hpow
  have hNneg : 0 ≤ N ^ (-4 / 3 : ℝ) :=
    Real.rpow_nonneg hN0.le _
  have hone :
      (1 : ℝ) = N ^ (4 / 3 : ℝ) * N ^ (-4 / 3 : ℝ) := by
    rw [← Real.rpow_add hN0]
    norm_num
  have hunit :
      1 ≤ 16 ^ (4 / 3 : ℝ) * T ^ 2 * N ^ (-4 / 3 : ℝ) := by
    rw [hone]
    gcongr
  change T⁻¹ ^ 2 ≤
    16 ^ (4 / 3 : ℝ) * N ^ (-4 / 3 : ℝ)
  rw [inv_pow]
  apply le_of_mul_le_mul_right _ (sq_pos_of_pos hT0)
  rw [inv_mul_cancel₀ (pow_ne_zero 2 hT0.ne')]
  calc
    1 ≤ 16 ^ (4 / 3 : ℝ) * T ^ 2 * N ^ (-4 / 3 : ℝ) := hunit
    _ = (16 ^ (4 / 3 : ℝ) * N ^ (-4 / 3 : ℝ)) * T ^ 2 := by ring

theorem summable_routeKRVMQuantile_reciprocal_sq :
    Summable (fun n : ℕ => (routeKRVMQuantile n)⁻¹ ^ 2) := by
  have hbase : Summable (fun n : ℕ =>
      (n + 1 : ℝ) ^ (-4 / 3 : ℝ)) := by
    have h := Real.summable_nat_rpow.mpr
      (by norm_num : (-4 / 3 : ℝ) < -1)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr h
  have hmajor := hbase.mul_left (16 ^ (4 / 3 : ℝ))
  exact Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    routeKRVMQuantile_reciprocal_sq_le
    hmajor

def routeKPrimeRVMIndex (p : Nat.Primes) : ℕ :=
  Nat.primeCounting' p

theorem routeKPrimeRVMIndex_injective :
    Function.Injective routeKPrimeRVMIndex := by
  intro p q h
  apply Subtype.ext
  have hnth := congrArg (Nat.nth Nat.Prime) h
  simpa [routeKPrimeRVMIndex, Nat.primeCounting',
    Nat.nth_count p.prop, Nat.nth_count q.prop] using hnth

def routeKPrimeRVMReciprocal (p : Nat.Primes) : ℝ :=
  (routeKRVMQuantile (routeKPrimeRVMIndex p))⁻¹

theorem routeKPrimeRVMReciprocal_pos (p : Nat.Primes) :
    0 < routeKPrimeRVMReciprocal p := by
  rw [routeKPrimeRVMReciprocal]
  exact inv_pos.mpr (routeKRVMBase_pos.trans
    (routeKRVMBase_lt_quantile _))

theorem routeKPrimeRVMReciprocal_injective :
    Function.Injective routeKPrimeRVMReciprocal := by
  intro p q h
  rw [routeKPrimeRVMReciprocal, routeKPrimeRVMReciprocal] at h
  have hquantile :
      routeKRVMQuantile (routeKPrimeRVMIndex p) =
        routeKRVMQuantile (routeKPrimeRVMIndex q) := by
    exact inv_injective h
  exact routeKPrimeRVMIndex_injective
    (routeKRVMQuantile_injective hquantile)

theorem summable_routeKPrimeRVMReciprocal_sq :
    Summable (fun p : Nat.Primes =>
      routeKPrimeRVMReciprocal p ^ 2) := by
  exact (summable_routeKRVMQuantile_reciprocal_sq.comp_injective
    routeKPrimeRVMIndex_injective).congr fun p => by
      simp [routeKPrimeRVMReciprocal]

def routeKRVMSkeletonKernel
    (pq : Nat.Primes × Nat.Primes) : ℂ :=
  HilbertSchmidt.diagMul
    (fun p : Nat.Primes => (routeKPrimeRVMReciprocal p : ℂ)) pq

theorem routeKRVMSkeletonKernel_isHS :
    HilbertSchmidt.IsHS routeKRVMSkeletonKernel := by
  apply HilbertSchmidt.isHS_diagMul_infinite
  exact summable_routeKPrimeRVMReciprocal_sq.congr fun p => by
    simp [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (routeKPrimeRVMReciprocal_pos p)]

def routeKRVMSkeletonOperator :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  HilbertSchmidt.toOperator routeKRVMSkeletonKernel_isHS

theorem routeKRVMSkeletonOperator_isHilbertSchmidt :
    routeKRVMSkeletonOperator.IsHilbertSchmidt :=
  HilbertSchmidt.isHilbertSchmidt_toOperator
    routeKRVMSkeletonKernel_isHS

theorem routeKRVMSkeletonOperator_basis (p : Nat.Primes) :
    routeKRVMSkeletonOperator (routeKPrimeBasis p) =
      (routeKPrimeRVMReciprocal p : ℂ) • routeKPrimeBasis p := by
  apply lp.ext
  funext q
  rw [routeKRVMSkeletonOperator, routeKPrimeBasis,
    HilbertSchmidt.toOperator_single routeKRVMSkeletonKernel_isHS]
  change routeKRVMSkeletonKernel (q, p) =
    ((routeKPrimeRVMReciprocal p : ℂ) •
      (lp.single 2 p 1 : RouteKPrimeHilbert)) q
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hqp : q = p
  · subst q
    simp [routeKRVMSkeletonKernel, HilbertSchmidt.diagMul]
  · simp [routeKRVMSkeletonKernel, HilbertSchmidt.diagMul, hqp]

theorem routeKRVMSkeletonKernel_hsAdjoint :
    HilbertSchmidt.hsAdjoint routeKRVMSkeletonKernel =
      routeKRVMSkeletonKernel := by
  funext pq
  rcases pq with ⟨p, q⟩
  by_cases hpq : p = q
  · subst q
    simp [HilbertSchmidt.hsAdjoint, routeKRVMSkeletonKernel,
      HilbertSchmidt.diagMul]
  · have hqp : q ≠ p := Ne.symm hpq
    simp [HilbertSchmidt.hsAdjoint, routeKRVMSkeletonKernel,
      HilbertSchmidt.diagMul, hpq, hqp]

theorem routeKRVMSkeletonOperator_isSelfAdjoint :
    IsSelfAdjoint routeKRVMSkeletonOperator := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff',
    routeKRVMSkeletonOperator,
    HilbertSchmidt.adjoint_toOperator]
  exact HilbertSchmidt.toOperator_congr _ _
    routeKRVMSkeletonKernel_hsAdjoint

/-- Source-defined trace-class relocation of the reciprocal RVM skeleton. -/
def routeKPhysicalEndpointRVMRelocation :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  schattenDoubleCommutator routeKRVMSkeletonOperator
    routeKPhysicalEndpointCompletedPairOperator

theorem routeKPhysicalEndpointRVMRelocation_memSchattenClass_one :
    MemSchattenClass 1 routeKPhysicalEndpointRVMRelocation :=
  schattenDoubleCommutator_memSchattenClass_one
    routeKRVMSkeletonOperator_isHilbertSchmidt

theorem routeKPhysicalEndpointRVMRelocation_isHilbertSchmidt :
    routeKPhysicalEndpointRVMRelocation.IsHilbertSchmidt :=
  schattenDoubleCommutator_isHilbertSchmidt
    routeKRVMSkeletonOperator_isHilbertSchmidt

theorem routeKPhysicalEndpointRVMRelocation_isSelfAdjoint :
    IsSelfAdjoint routeKPhysicalEndpointRVMRelocation :=
  schattenDoubleCommutator_isSelfAdjoint
    routeKRVMSkeletonOperator_isSelfAdjoint
    routeKPhysicalEndpointCompletedPairOperator_isSelfAdjoint

theorem routeKPhysicalEndpointRVMRelocation_matrix
    (p q : Nat.Primes) :
    inner ℂ (routeKPrimeBasis p)
      (routeKPhysicalEndpointRVMRelocation (routeKPrimeBasis q)) =
      (((routeKPrimeRVMReciprocal p -
          routeKPrimeRVMReciprocal q) ^ 2 : ℝ) : ℂ) *
        (xiPhysicalEndpointCompletedPairResponse p q : ℂ) := by
  rw [routeKPhysicalEndpointRVMRelocation,
    inner_schattenDoubleCommutator_eigenvector
      routeKRVMSkeletonOperator_isSelfAdjoint
      routeKPrimeBasis routeKPrimeRVMReciprocal
      routeKRVMSkeletonOperator_basis,
    routeKPhysicalEndpointCompletedPairOperator_matrix]

theorem routeKPhysicalEndpointRVMRelocation_diagonal_zero
    (p : Nat.Primes) :
    inner ℂ (routeKPrimeBasis p)
      (routeKPhysicalEndpointRVMRelocation (routeKPrimeBasis p)) = 0 := by
  rw [routeKPhysicalEndpointRVMRelocation_matrix]
  simp

/-- The reciprocal skeleton and source relocation are Hilbert--Schmidt orthogonal.  This is forced
by the exact zero diagonal of the double commutator, not by an assumed trace cancellation. -/
theorem hsInner_routeKRVMSkeletonOperator_physicalEndpointRVMRelocation_eq_zero :
    ContinuousLinearMap.hsInner routeKRVMSkeletonOperator
      routeKPhysicalEndpointRVMRelocation = 0 := by
  rw [ContinuousLinearMap.hsInner_eq_tsum_basis
    routeKRVMSkeletonOperator_isHilbertSchmidt
    routeKPhysicalEndpointRVMRelocation_isHilbertSchmidt
    (HilbertSchmidt.lpBasis Nat.Primes)]
  have hterm :
      (fun p : Nat.Primes =>
        inner ℂ
          (routeKRVMSkeletonOperator (HilbertSchmidt.lpBasis Nat.Primes p))
          (routeKPhysicalEndpointRVMRelocation
            (HilbertSchmidt.lpBasis Nat.Primes p))) = 0 := by
    funext p
    rw [HilbertSchmidt.lpBasis_apply]
    change inner ℂ
      (routeKRVMSkeletonOperator (routeKPrimeBasis p))
      (routeKPhysicalEndpointRVMRelocation (routeKPrimeBasis p)) = 0
    rw [routeKRVMSkeletonOperator_basis, inner_smul_left,
      routeKPhysicalEndpointRVMRelocation_diagonal_zero]
    simp
  rw [hterm]
  change (∑' _ : Nat.Primes, (0 : ℂ)) = 0
  exact tsum_zero

/-- **Exact quadratic budget law.** The actual source relocation can only increase the
Hilbert--Schmidt quadratic determinant budget, and its increase is exactly its own squared
Hilbert--Schmidt norm. -/
theorem hsNormSq_routeKRVMSkeleton_add_physicalEndpointRVMRelocation :
    ContinuousLinearMap.hsNormSq
        (routeKRVMSkeletonOperator + routeKPhysicalEndpointRVMRelocation) =
      ContinuousLinearMap.hsNormSq routeKRVMSkeletonOperator +
        ContinuousLinearMap.hsNormSq routeKPhysicalEndpointRVMRelocation :=
  ContinuousLinearMap.hsNormSq_add_eq_of_hsInner_eq_zero
    routeKRVMSkeletonOperator_isHilbertSchmidt
    routeKPhysicalEndpointRVMRelocation_isHilbertSchmidt
    hsInner_routeKRVMSkeletonOperator_physicalEndpointRVMRelocation_eq_zero

theorem routeKPhysicalEndpointRVMRelocation_triangleHolonomy
    (p q r : Nat.Primes) :
    inner ℂ (routeKPrimeBasis p)
        (routeKPhysicalEndpointRVMRelocation (routeKPrimeBasis q)) *
      inner ℂ (routeKPrimeBasis q)
        (routeKPhysicalEndpointRVMRelocation (routeKPrimeBasis r)) *
      inner ℂ (routeKPrimeBasis r)
        (routeKPhysicalEndpointRVMRelocation (routeKPrimeBasis p)) =
      (((routeKPrimeRVMReciprocal p -
            routeKPrimeRVMReciprocal q) ^ 2 *
          (routeKPrimeRVMReciprocal q -
            routeKPrimeRVMReciprocal r) ^ 2 *
          (routeKPrimeRVMReciprocal r -
            routeKPrimeRVMReciprocal p) ^ 2 : ℝ) : ℂ) *
        ((xiPhysicalEndpointCompletedPairResponse p q : ℂ) *
          (xiPhysicalEndpointCompletedPairResponse q r : ℂ) *
          (xiPhysicalEndpointCompletedPairResponse r p : ℂ)) := by
  rw [routeKPhysicalEndpointRVMRelocation,
    schattenDoubleCommutator_triangleHolonomy
      routeKRVMSkeletonOperator_isSelfAdjoint
      routeKPrimeBasis routeKPrimeRVMReciprocal
      routeKRVMSkeletonOperator_basis,
    routeKPhysicalEndpointCompletedPairOperator_matrix,
    routeKPhysicalEndpointCompletedPairOperator_matrix,
    routeKPhysicalEndpointCompletedPairOperator_matrix]

theorem routeKPhysicalEndpointRVMRelocation_triangleHolonomy_ne_zero
    {p q r : Nat.Primes} (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hpqB : xiPhysicalEndpointCompletedPairResponse p q ≠ 0)
    (hqrB : xiPhysicalEndpointCompletedPairResponse q r ≠ 0)
    (hrpB : xiPhysicalEndpointCompletedPairResponse r p ≠ 0) :
    inner ℂ (routeKPrimeBasis p)
        (routeKPhysicalEndpointRVMRelocation (routeKPrimeBasis q)) *
      inner ℂ (routeKPrimeBasis q)
        (routeKPhysicalEndpointRVMRelocation (routeKPrimeBasis r)) *
      inner ℂ (routeKPrimeBasis r)
        (routeKPhysicalEndpointRVMRelocation (routeKPrimeBasis p)) ≠ 0 := by
  apply schattenDoubleCommutator_triangleHolonomy_ne_zero
    routeKRVMSkeletonOperator_isSelfAdjoint
    routeKPrimeBasis routeKPrimeRVMReciprocal
    routeKRVMSkeletonOperator_basis
  · exact routeKPrimeRVMReciprocal_injective.ne hpq
  · exact routeKPrimeRVMReciprocal_injective.ne hqr
  · exact routeKPrimeRVMReciprocal_injective.ne hrp
  · simpa only [routeKPhysicalEndpointCompletedPairOperator_matrix] using
      (show (xiPhysicalEndpointCompletedPairResponse p q : ℂ) ≠ 0 by
        exact_mod_cast hpqB)
  · simpa only [routeKPhysicalEndpointCompletedPairOperator_matrix] using
      (show (xiPhysicalEndpointCompletedPairResponse q r : ℂ) ≠ 0 by
        exact_mod_cast hqrB)
  · simpa only [routeKPhysicalEndpointCompletedPairOperator_matrix] using
      (show (xiPhysicalEndpointCompletedPairResponse r p : ℂ) ≠ 0 by
        exact_mod_cast hrpB)

/-- Three-prime reciprocal RVM diagonal used by an actual source compression. -/
def routeKPhysicalEndpointRVMTriangleSkeleton
    (p q r : Nat.Primes) : Fin 3 → ℝ :=
  ![routeKPrimeRVMReciprocal p,
    routeKPrimeRVMReciprocal q,
    routeKPrimeRVMReciprocal r]

/-- Three cyclic edges of the double-commutator relocation.  These are exactly the real matrix
entries given by `routeKPhysicalEndpointRVMRelocation_matrix`. -/
def routeKPhysicalEndpointRVMTriangleEdge
    (p q r : Nat.Primes) : Fin 3 → ℝ :=
  ![(routeKPrimeRVMReciprocal p - routeKPrimeRVMReciprocal q) ^ 2 *
      xiPhysicalEndpointCompletedPairResponse p q,
    (routeKPrimeRVMReciprocal q - routeKPrimeRVMReciprocal r) ^ 2 *
      xiPhysicalEndpointCompletedPairResponse q r,
    (routeKPrimeRVMReciprocal r - routeKPrimeRVMReciprocal p) ^ 2 *
      xiPhysicalEndpointCompletedPairResponse r p]

theorem routeKPhysicalEndpointRVMTriangleSkeleton_pos
    (p q r : Nat.Primes) :
    ∀ i, 0 < routeKPhysicalEndpointRVMTriangleSkeleton p q r i := by
  intro i
  fin_cases i <;>
    simp [routeKPhysicalEndpointRVMTriangleSkeleton,
      routeKPrimeRVMReciprocal_pos]

theorem routeKPhysicalEndpointRVMTriangleEdge_ne_zero
    {p q r : Nat.Primes} (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hpqB : xiPhysicalEndpointCompletedPairResponse p q ≠ 0)
    (hqrB : xiPhysicalEndpointCompletedPairResponse q r ≠ 0)
    (hrpB : xiPhysicalEndpointCompletedPairResponse r p ≠ 0) :
    ∀ i, routeKPhysicalEndpointRVMTriangleEdge p q r i ≠ 0 := by
  intro i
  fin_cases i
  · simp only [routeKPhysicalEndpointRVMTriangleEdge]
    exact mul_ne_zero
      (pow_ne_zero 2 (sub_ne_zero.mpr
        (routeKPrimeRVMReciprocal_injective.ne hpq))) hpqB
  · simp only [routeKPhysicalEndpointRVMTriangleEdge]
    exact mul_ne_zero
      (pow_ne_zero 2 (sub_ne_zero.mpr
        (routeKPrimeRVMReciprocal_injective.ne hqr))) hqrB
  · simp only [routeKPhysicalEndpointRVMTriangleEdge]
    exact mul_ne_zero
      (pow_ne_zero 2 (sub_ne_zero.mpr
        (routeKPrimeRVMReciprocal_injective.ne hrp))) hrpB

/-- **First reflection-even source signal.** Arbitrarily far actual completed-endpoint RVM
compressions have a quartic paired trace cumulant that changes under one-edge orientation flip.
Thus the cofinal source holonomy survives both Schatten relocation and centered reflection at the
first determinant-visible order. -/
theorem exists_cofinal_physicalEndpointRVM_quarticPairedTrace_ne_edgeFlip
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      routeKThreePrimePairedTracePower
          (routeKPhysicalEndpointRVMTriangleSkeleton
            (nthPrimeSubtype n) (nthPrimeSubtype (n + 1))
              (nthPrimeSubtype (n + 2)))
          (routeKPhysicalEndpointRVMTriangleEdge
            (nthPrimeSubtype n) (nthPrimeSubtype (n + 1))
              (nthPrimeSubtype (n + 2))) 4 ≠
        routeKThreePrimePairedTracePower
          (routeKPhysicalEndpointRVMTriangleSkeleton
            (nthPrimeSubtype n) (nthPrimeSubtype (n + 1))
              (nthPrimeSubtype (n + 2)))
          (routeKThreePrimeEdgeFlip
            (routeKPhysicalEndpointRVMTriangleEdge
              (nthPrimeSubtype n) (nthPrimeSubtype (n + 1))
                (nthPrimeSubtype (n + 2)))) 4 := by
  obtain ⟨n, hn, hpq, hqr, hrp⟩ :=
    exists_cofinal_positive_physicalEndpoint_pair_triangle N
  refine ⟨n, hn, ?_⟩
  apply routeKThreePrimePairedTracePower_four_ne_edgeFlip
  · exact routeKPhysicalEndpointRVMTriangleSkeleton_pos _ _ _
  · apply routeKPhysicalEndpointRVMTriangleEdge_ne_zero
    · exact nthPrimeSubtype_injective.ne (by omega)
    · exact nthPrimeSubtype_injective.ne (by omega)
    · exact nthPrimeSubtype_injective.ne (by omega)
    · exact hpq.ne'
    · exact hqr.ne'
    · exact hrp.ne'

theorem exists_cofinal_nonzero_physicalEndpointRVMRelocation_triangleHolonomy
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      inner ℂ (routeKPrimeBasis (nthPrimeSubtype n))
          (routeKPhysicalEndpointRVMRelocation
            (routeKPrimeBasis (nthPrimeSubtype (n + 1)))) *
        inner ℂ (routeKPrimeBasis (nthPrimeSubtype (n + 1)))
          (routeKPhysicalEndpointRVMRelocation
            (routeKPrimeBasis (nthPrimeSubtype (n + 2)))) *
        inner ℂ (routeKPrimeBasis (nthPrimeSubtype (n + 2)))
          (routeKPhysicalEndpointRVMRelocation
            (routeKPrimeBasis (nthPrimeSubtype n))) ≠ 0 := by
  obtain ⟨n, hn, hpq, hqr, hrp⟩ :=
    exists_cofinal_positive_physicalEndpoint_pair_triangle N
  refine ⟨n, hn, ?_⟩
  apply routeKPhysicalEndpointRVMRelocation_triangleHolonomy_ne_zero
  · exact nthPrimeSubtype_injective.ne (by omega)
  · exact nthPrimeSubtype_injective.ne (by omega)
  · exact nthPrimeSubtype_injective.ne (by omega)
  · exact hpq.ne'
  · exact hqr.ne'
  · exact hrp.ne'

theorem routeKPhysicalEndpointRVMRelocation_ne_zero :
    routeKPhysicalEndpointRVMRelocation ≠ 0 := by
  obtain ⟨n, _, htriangle⟩ :=
    exists_cofinal_nonzero_physicalEndpointRVMRelocation_triangleHolonomy 0
  intro hzero
  rw [hzero] at htriangle
  simp at htriangle

theorem hsNormSq_routeKPhysicalEndpointRVMRelocation_pos :
    0 < ContinuousLinearMap.hsNormSq
      routeKPhysicalEndpointRVMRelocation := by
  have hnonneg :=
    ContinuousLinearMap.hsNormSq_nonneg
      routeKPhysicalEndpointRVMRelocation
  exact lt_of_le_of_ne hnonneg
    (fun hzero =>
      routeKPhysicalEndpointRVMRelocation_ne_zero
        ((ContinuousLinearMap.hsNormSq_eq_zero_iff
          routeKPhysicalEndpointRVMRelocation_isHilbertSchmidt).mp
            hzero.symm))

/-- The actual completed-endpoint relocation strictly raises the quadratic determinant budget
above that of the smooth reciprocal RVM skeleton. -/
theorem hsNormSq_routeKRVMSkeleton_lt_add_physicalEndpointRVMRelocation :
    ContinuousLinearMap.hsNormSq routeKRVMSkeletonOperator <
      ContinuousLinearMap.hsNormSq
        (routeKRVMSkeletonOperator + routeKPhysicalEndpointRVMRelocation) := by
  rw [hsNormSq_routeKRVMSkeleton_add_physicalEndpointRVMRelocation]
  exact lt_add_of_pos_right _
    hsNormSq_routeKPhysicalEndpointRVMRelocation_pos

end

end RHTower
