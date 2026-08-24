import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointRVMRelocation
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import GaloisForLFunctions.HTGeometry.HarmonicOrdinateDivergence
import GaloisForLFunctions.HTGeometry.IndexedDiagonalApproximation

/-!
# Prime-indexed RVM Schatten infrastructure

Exact smooth-counting, Schatten-boundary, and prime-clock results for the
prime-indexed Riemann--von Mangoldt diagonal model.
-/

open scoped BigOperators InnerProductSpace Nat.Prime
open Filter

namespace RHTower

noncomputable section

theorem routeKRVMQuantile_le_iff_lt_floor_count
    {n : ℕ} {T : ℝ} (hT : routeKRVMBase < T) :
    routeKRVMQuantile n ≤ T ↔ n < ⌊routeKSmoothRVMCount T⌋₊ := by
  have hq : routeKRVMQuantile n ∈ Set.Ioi routeKRVMBase :=
    routeKRVMBase_lt_quantile n
  have hTIoi : T ∈ Set.Ioi routeKRVMBase := hT
  have hcountPos : 0 < routeKSmoothRVMCount T := by
    have hT0 : 0 < T := routeKRVMBase_pos.trans hT
    have hratio : 1 < T / routeKRVMBase :=
      (lt_div_iff₀ routeKRVMBase_pos).2 (by simpa using hT)
    have hlog : 0 < Real.log (T / routeKRVMBase) := Real.log_pos hratio
    have hdiv : 0 < T / (2 * Real.pi) := by positivity
    rw [routeKSmoothRVMCount]
    nlinarith [mul_pos hdiv hlog]
  rw [← (routeKSmoothRVMCount_strictMonoOn.le_iff_le hq hTIoi),
    routeKSmoothRVMCount_quantile]
  constructor
  · intro h
    have hcast : ((n + 1 : ℕ) : ℝ) ≤ routeKSmoothRVMCount T := by
      norm_num
      exact h
    have hfloor : n + 1 ≤ ⌊routeKSmoothRVMCount T⌋₊ := Nat.le_floor hcast
    omega
  · intro h
    have hsucc : n + 1 ≤ ⌊routeKSmoothRVMCount T⌋₊ := by omega
    exact le_trans (by exact_mod_cast hsucc)
      (Nat.floor_le hcountPos.le)

def routeKRVMSmoothCountFinset (T : ℝ) : Finset ℕ :=
  Finset.range ⌊routeKSmoothRVMCount T⌋₊

theorem mem_routeKRVMSmoothCountFinset_iff
    {n : ℕ} {T : ℝ} (hT : routeKRVMBase < T) :
    n ∈ routeKRVMSmoothCountFinset T ↔ routeKRVMQuantile n ≤ T := by
  rw [routeKRVMSmoothCountFinset, Finset.mem_range,
    routeKRVMQuantile_le_iff_lt_floor_count hT]

theorem card_routeKRVMSmoothCountFinset (T : ℝ) :
    (routeKRVMSmoothCountFinset T).card = ⌊routeKSmoothRVMCount T⌋₊ := by
  simp [routeKRVMSmoothCountFinset]

theorem routeKRVMQuantile_monotone : Monotone routeKRVMQuantile := by
  intro i j hij
  have hi : routeKRVMQuantile i ∈ Set.Ioi routeKRVMBase :=
    routeKRVMBase_lt_quantile i
  have hj : routeKRVMQuantile j ∈ Set.Ioi routeKRVMBase :=
    routeKRVMBase_lt_quantile j
  apply (routeKSmoothRVMCount_strictMonoOn.le_iff_le hi hj).mp
  rw [routeKSmoothRVMCount_quantile, routeKSmoothRVMCount_quantile]
  exact_mod_cast Nat.succ_le_succ hij

theorem routeKRVMQuantile_reciprocal_antitone :
    Antitone (fun n : ℕ => (routeKRVMQuantile n)⁻¹) := by
  intro i j hij
  have hi : 0 < routeKRVMQuantile i :=
    routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile i)
  have hj : 0 < routeKRVMQuantile j :=
    routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile j)
  exact (inv_le_inv₀ hj hi).2 (routeKRVMQuantile_monotone hij)

theorem routeKRVMQuantile_le_linear (n : ℕ) :
    routeKRVMQuantile n ≤
      (2 * routeKRVMBase * Real.exp 1) * ((n : ℝ) + 1) := by
  let T : ℝ := routeKRVMBase * Real.exp 1 * ((n : ℝ) + 2)
  have hExpOne : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have hratioOne : 1 < Real.exp 1 * ((n : ℝ) + 2) := by nlinarith
  have hTgt : routeKRVMBase < T := by
    dsimp [T]
    nlinarith [routeKRVMBase_pos]
  have hratio : T / routeKRVMBase = Real.exp 1 * ((n : ℝ) + 2) := by
    dsimp [T]
    field_simp [routeKRVMBase_pos.ne']
  have hlog : 1 ≤ Real.log (T / routeKRVMBase) := by
    rw [hratio, Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    have : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
    linarith
  have hdiv : (n : ℝ) + 2 ≤ T / (2 * Real.pi) := by
    have heq : T / (2 * Real.pi) =
        Real.exp 1 * Real.exp 1 * ((n : ℝ) + 2) := by
      dsimp [T, routeKRVMBase]
      field_simp
    rw [heq]
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    nlinarith [Real.exp_pos 1, le_of_lt hExpOne]
  have hcount : (n + 1 : ℝ) ≤ routeKSmoothRVMCount T := by
    rw [routeKSmoothRVMCount]
    have hdiv0 : 0 ≤ T / (2 * Real.pi) :=
      (div_nonneg (routeKRVMBase_pos.trans hTgt).le (by positivity))
    have hprod : (n : ℝ) + 2 ≤
        T / (2 * Real.pi) * Real.log (T / routeKRVMBase) :=
      calc
        (n : ℝ) + 2 ≤ T / (2 * Real.pi) := hdiv
        _ ≤ T / (2 * Real.pi) * Real.log (T / routeKRVMBase) := by
          nlinarith
    norm_num
    linarith
  have hquantile : routeKRVMQuantile n ≤ T := by
    have hq : routeKRVMQuantile n ∈ Set.Ioi routeKRVMBase :=
      routeKRVMBase_lt_quantile n
    have hTIoi : T ∈ Set.Ioi routeKRVMBase := hTgt
    rw [← (routeKSmoothRVMCount_strictMonoOn.le_iff_le hq hTIoi),
      routeKSmoothRVMCount_quantile]
    exact hcount
  calc
    routeKRVMQuantile n ≤ T := hquantile
    _ ≤ (2 * routeKRVMBase * Real.exp 1) * ((n : ℝ) + 1) := by
      dsimp [T]
      nlinarith [routeKRVMBase_pos, Real.exp_pos 1]

theorem routeKRVMQuantile_subpower_growth {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ((n : ℝ) + 1) ≤
      ((2 * Real.pi * ε)⁻¹ + 1) *
        routeKRVMQuantile n ^ (1 + ε) := by
  let T : ℝ := routeKRVMQuantile n
  have hTbase : routeKRVMBase < T := routeKRVMBase_lt_quantile n
  have hT0 : 0 < T := routeKRVMBase_pos.trans hTbase
  have hbaseOne : (1 : ℝ) ≤ routeKRVMBase := by
    dsimp [routeKRVMBase]
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hexp : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    nlinarith
  have hTone : (1 : ℝ) ≤ T := hbaseOne.trans hTbase.le
  have hratio0 : 0 ≤ T / routeKRVMBase := by positivity
  have hratioT : T / routeKRVMBase ≤ T := by
    rw [div_le_iff₀ routeKRVMBase_pos]
    nlinarith
  have hlog : Real.log (T / routeKRVMBase) ≤ T ^ ε / ε := by
    calc
      Real.log (T / routeKRVMBase) ≤
          (T / routeKRVMBase) ^ ε / ε :=
        Real.log_le_rpow_div hratio0 hε
      _ ≤ T ^ ε / ε := by
        gcongr
  have hmain : T / (2 * Real.pi) * Real.log (T / routeKRVMBase) ≤
      (2 * Real.pi * ε)⁻¹ * T ^ (1 + ε) := by
    have hfac : 0 ≤ T / (2 * Real.pi) := by positivity
    calc
      T / (2 * Real.pi) * Real.log (T / routeKRVMBase) ≤
          T / (2 * Real.pi) * (T ^ ε / ε) :=
        mul_le_mul_of_nonneg_left hlog hfac
      _ = (2 * Real.pi * ε)⁻¹ * T ^ (1 + ε) := by
        rw [Real.rpow_add hT0, Real.rpow_one]
        field_simp
  have hconst : (7 / 8 : ℝ) ≤ T ^ (1 + ε) := by
    have hone : (1 : ℝ) ≤ T ^ (1 + ε) :=
      Real.one_le_rpow hTone (by linarith)
    linarith
  rw [← routeKSmoothRVMCount_quantile n, routeKSmoothRVMCount]
  exact (add_le_add hmain hconst).trans_eq (by ring)

theorem summable_routeKRVMQuantile_reciprocal_rpow {q : ℝ} (hq : 1 < q) :
    Summable (fun n : ℕ => (routeKRVMQuantile n)⁻¹ ^ q) := by
  let ε : ℝ := (q - 1) / 2
  let a : ℝ := 1 + ε
  let α : ℝ := q / a
  let C : ℝ := (2 * Real.pi * ε)⁻¹ + 1
  have hε : 0 < ε := by dsimp [ε]; linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have hα : 1 < α := by
    dsimp [α, a, ε]
    rw [one_lt_div (by linarith : 0 < 1 + (q - 1) / 2)]
    linarith
  have hC : 0 < C := by
    dsimp [C]
    have : 0 < 2 * Real.pi * ε := by positivity
    positivity
  have hbase : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-α)) := by
    have h := Real.summable_nat_rpow.mpr (by linarith : -α < -1)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr h
  have hmajor : Summable (fun n : ℕ => C ^ α * ((n : ℝ) + 1) ^ (-α)) :=
    hbase.mul_left _
  refine Summable.of_nonneg_of_le
    (fun n => Real.rpow_nonneg (inv_nonneg.mpr
      (routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n)).le) q)
    ?_ hmajor
  intro n
  let T : ℝ := routeKRVMQuantile n
  let N : ℝ := (n : ℝ) + 1
  have hT : 0 < T := routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n)
  have hN : 0 < N := by dsimp [N]; positivity
  have hgrowth : N ≤ C * T ^ a := by
    simpa [T, N, C, a] using routeKRVMQuantile_subpower_growth hε n
  have hdiv : N / C ≤ T ^ a := by
    rw [div_le_iff₀ hC]
    simpa [mul_comm] using hgrowth
  have hdivPos : 0 < N / C := div_pos hN hC
  have hTaPos : 0 < T ^ a := Real.rpow_pos_of_pos hT _
  have hrpow : (N / C) ^ α ≤ (T ^ a) ^ α :=
    Real.rpow_le_rpow hdivPos.le hdiv (by linarith)
  have haα : a * α = q := by
    dsimp [α]
    field_simp
  have hright : (T ^ a) ^ α = T ^ q := by
    rw [← Real.rpow_mul hT.le, haα]
  have hleftPos : 0 < (N / C) ^ α := Real.rpow_pos_of_pos hdivPos _
  have hrightPos : 0 < T ^ q := Real.rpow_pos_of_pos hT _
  have hinv : (T ^ q)⁻¹ ≤ ((N / C) ^ α)⁻¹ := by
    exact (inv_le_inv₀ hrightPos hleftPos).2 (hrpow.trans hright.le)
  calc
    T⁻¹ ^ q = (T ^ q)⁻¹ := Real.inv_rpow hT.le q
    _ ≤ ((N / C) ^ α)⁻¹ := hinv
    _ = C ^ α * N ^ (-α) := by
      rw [Real.div_rpow hN.le hC.le, inv_div, Real.rpow_neg hN.le]
      rfl

theorem not_summable_routeKRVMQuantile_reciprocal :
    ¬ Summable (fun n : ℕ => (routeKRVMQuantile n)⁻¹) := by
  apply GaloisForLFunctions.HTGeometry.not_summable_inv_of_le_linear
    (c := 2 * routeKRVMBase * Real.exp 1)
  · exact mul_pos (mul_pos two_pos routeKRVMBase_pos) (Real.exp_pos 1)
  · exact fun n => routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n)
  · filter_upwards [] with n
    simpa [Nat.cast_add, Nat.cast_one] using routeKRVMQuantile_le_linear n

theorem routeKPrimeRVMIndex_nthPrimeSubtype (n : ℕ) :
    routeKPrimeRVMIndex (nthPrimeSubtype n) = n := by
  rw [routeKPrimeRVMIndex, nthPrimeSubtype, Nat.primeCounting']
  exact Nat.count_nth fun hf => (Nat.infinite_setOf_prime hf).elim

theorem not_summable_routeKPrimeRVMReciprocal :
    ¬ Summable routeKPrimeRVMReciprocal := by
  intro hprime
  apply not_summable_routeKRVMQuantile_reciprocal
  have hcomp : Summable (routeKPrimeRVMReciprocal ∘ nthPrimeEquiv) :=
    nthPrimeEquiv.summable_iff.mpr hprime
  simpa [Function.comp_def, nthPrimeEquiv, routeKPrimeRVMReciprocal,
    routeKPrimeRVMIndex_nthPrimeSubtype] using hcomp

theorem summable_routeKPrimeRVMReciprocal_rpow {q : ℝ} (hq : 1 < q) :
    Summable (fun p : Nat.Primes => routeKPrimeRVMReciprocal p ^ q) := by
  have hnat := summable_routeKRVMQuantile_reciprocal_rpow hq
  exact (hnat.comp_injective routeKPrimeRVMIndex_injective).congr fun p => by
    simp [routeKPrimeRVMReciprocal]

theorem routeKPrimeRVMReciprocal_le_zero (p : Nat.Primes) :
    routeKPrimeRVMReciprocal p ≤ (routeKRVMQuantile 0)⁻¹ := by
  exact routeKRVMQuantile_reciprocal_antitone (Nat.zero_le _)

theorem norm_routeKPrimeRVMReciprocal_le_zero (p : Nat.Primes) :
    ‖(routeKPrimeRVMReciprocal p : ℂ)‖ ≤ (routeKRVMQuantile 0)⁻¹ := by
  simpa [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (routeKPrimeRVMReciprocal_pos p)] using
      routeKPrimeRVMReciprocal_le_zero p

def routeKPrimeRVMOperator : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  HTGeometry.ellTwoDiagonal
    (fun p : Nat.Primes => (routeKPrimeRVMReciprocal p : ℂ))
    norm_routeKPrimeRVMReciprocal_le_zero

theorem routeKPrimeRVMOperator_basis (p : Nat.Primes) :
    routeKPrimeRVMOperator (routeKPrimeBasis p) =
      (routeKPrimeRVMReciprocal p : ℂ) • routeKPrimeBasis p := by
  simpa [routeKPrimeRVMOperator, routeKPrimeBasis,
    HTGeometry.ellTwoCoordinateBasis_apply] using
      HTGeometry.ellTwoDiagonal_coordinateBasis
        (fun p : Nat.Primes => (routeKPrimeRVMReciprocal p : ℂ))
        norm_routeKPrimeRVMReciprocal_le_zero p

theorem routeKPrimeRVMOperator_approxNumber_le (n : ℕ) :
    approxNumber routeKPrimeRVMOperator n ≤ (routeKRVMQuantile n)⁻¹ := by
  simpa [routeKPrimeRVMOperator, routeKPrimeRVMReciprocal,
    routeKPrimeRVMIndex, nthPrimeEquiv] using
      HTGeometry.approxNumber_ellTwoDiagonal_reindex_le nthPrimeEquiv
        (fun n : ℕ => (routeKRVMQuantile n)⁻¹)
        (fun n => (inv_pos.mpr
          (routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n))).le)
        (fun {_ _} h => routeKRVMQuantile_reciprocal_antitone h) n

theorem routeKPrimeRVMOperator_memSchattenClass {q : ℝ} (hq : 1 < q) :
    MemSchattenClass q routeKPrimeRVMOperator := by
  have hsum := summable_routeKRVMQuantile_reciprocal_rpow hq
  exact Summable.of_nonneg_of_le
    (fun n => Real.rpow_nonneg (approxNumber_nonneg _ _) q)
    (fun n => Real.rpow_le_rpow (approxNumber_nonneg _ _)
      (routeKPrimeRVMOperator_approxNumber_le n) (by linarith)) hsum

theorem routeKPrimeRVMOperator_not_memSchattenClass_one :
    ¬ MemSchattenClass 1 routeKPrimeRVMOperator := by
  intro htrace
  have hdiag := htrace.one_summable_norm_inner_diag_basis
    (HilbertSchmidt.lpBasis Nat.Primes)
  apply not_summable_routeKPrimeRVMReciprocal
  have hterm : (fun p : Nat.Primes =>
      ‖inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
        (routeKPrimeRVMOperator (HilbertSchmidt.lpBasis Nat.Primes p))‖) =
      routeKPrimeRVMReciprocal := by
    funext p
    rw [HilbertSchmidt.lpBasis_apply]
    change ‖inner ℂ (routeKPrimeBasis p)
      (routeKPrimeRVMOperator (routeKPrimeBasis p))‖ =
        routeKPrimeRVMReciprocal p
    rw [routeKPrimeRVMOperator_basis, inner_smul_right]
    simp [routeKPrimeBasis]
    exact (routeKPrimeRVMReciprocal_pos p).le
  rw [← hterm]
  exact hdiag

def routeKPrimeClockPhase (t : ℝ) (p : Nat.Primes) : ℂ :=
  Complex.exp (-Complex.I * ((t * Real.log (p : ℝ) : ℝ) : ℂ))

theorem norm_routeKPrimeClockPhase (t : ℝ) (p : Nat.Primes) :
    ‖routeKPrimeClockPhase t p‖ = 1 := by
  let x : ℝ := t * Real.log (p : ℝ)
  rw [routeKPrimeClockPhase, Complex.norm_exp]
  change Real.exp (-Complex.I * (x : ℂ)).re = 1
  have hre : (-Complex.I * (x : ℂ)).re = 0 := by norm_num
  rw [hre, Real.exp_zero]

def routeKPrimeClock (t : ℝ) : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  HTGeometry.ellTwoDiagonal (routeKPrimeClockPhase t)
    (fun p => (norm_routeKPrimeClockPhase t p).le)

theorem routeKPrimeClock_basis (t : ℝ) (p : Nat.Primes) :
    routeKPrimeClock t (routeKPrimeBasis p) =
      routeKPrimeClockPhase t p • routeKPrimeBasis p := by
  simpa [routeKPrimeClock, routeKPrimeBasis,
    HTGeometry.ellTwoCoordinateBasis_apply] using
      HTGeometry.ellTwoDiagonal_coordinateBasis (routeKPrimeClockPhase t)
        (fun p => (norm_routeKPrimeClockPhase t p).le) p

theorem routeKPrimeClock_zero :
    routeKPrimeClock 0 = ContinuousLinearMap.id ℂ RouteKPrimeHilbert := by
  ext f p
  simp [routeKPrimeClock, routeKPrimeClockPhase,
    HTGeometry.ellTwoDiagonal_apply]

theorem routeKPrimeClock_add (s t : ℝ) :
    routeKPrimeClock s ∘L routeKPrimeClock t = routeKPrimeClock (s + t) := by
  ext f p
  change routeKPrimeClockPhase s p * (routeKPrimeClockPhase t p * f p) =
    routeKPrimeClockPhase (s + t) p * f p
  rw [← mul_assoc]
  congr 1
  unfold routeKPrimeClockPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem routeKPrimeClock_adjoint_comp_self (t : ℝ) :
    ContinuousLinearMap.adjoint (routeKPrimeClock t) ∘L routeKPrimeClock t =
      ContinuousLinearMap.id ℂ RouteKPrimeHilbert := by
  rw [routeKPrimeClock, HTGeometry.adjoint_comp_self_ellTwoDiagonal]
  ext f p
  rw [HTGeometry.ellTwoDiagonal_apply]
  simp [norm_routeKPrimeClockPhase]

theorem routeKPrimeClock_comp_adjoint (t : ℝ) :
    routeKPrimeClock t ∘L ContinuousLinearMap.adjoint (routeKPrimeClock t) =
      ContinuousLinearMap.id ℂ RouteKPrimeHilbert := by
  rw [routeKPrimeClock, HTGeometry.adjoint_ellTwoDiagonal]
  ext f p
  rw [ContinuousLinearMap.comp_apply, HTGeometry.ellTwoDiagonal_apply,
    HTGeometry.ellTwoDiagonal_apply]
  simp only [ContinuousLinearMap.id_apply]
  change routeKPrimeClockPhase t p *
      (starRingEnd ℂ (routeKPrimeClockPhase t p) * f p) = f p
  rw [← mul_assoc]
  have hnorm := norm_routeKPrimeClockPhase t p
  rw [Complex.mul_conj]
  rw [Complex.normSq_eq_norm_sq, hnorm]
  simp

theorem routeKPrimeClock_commutes_rvm (t : ℝ) :
    routeKPrimeClock t ∘L routeKPrimeRVMOperator =
      routeKPrimeRVMOperator ∘L routeKPrimeClock t := by
  ext f p
  change routeKPrimeClockPhase t p *
      ((routeKPrimeRVMReciprocal p : ℂ) * f p) =
    (routeKPrimeRVMReciprocal p : ℂ) *
      (routeKPrimeClockPhase t p * f p)
  ring

theorem routeKRVMSkeletonOperator_not_memSchattenClass_one :
    ¬ MemSchattenClass 1 routeKRVMSkeletonOperator := by
  intro htrace
  have hdiag := htrace.one_summable_norm_inner_diag_basis
    (HilbertSchmidt.lpBasis Nat.Primes)
  apply not_summable_routeKPrimeRVMReciprocal
  have hterm : (fun p : Nat.Primes =>
      ‖inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
        (routeKRVMSkeletonOperator (HilbertSchmidt.lpBasis Nat.Primes p))‖) =
      routeKPrimeRVMReciprocal := by
    funext p
    rw [HilbertSchmidt.lpBasis_apply]
    change ‖inner ℂ (routeKPrimeBasis p)
      (routeKRVMSkeletonOperator (routeKPrimeBasis p))‖ =
        routeKPrimeRVMReciprocal p
    rw [routeKRVMSkeletonOperator_basis, inner_smul_right]
    simp [routeKPrimeBasis]
    exact (routeKPrimeRVMReciprocal_pos p).le
  rw [← hterm]
  exact hdiag

theorem tendsto_log_routeKRVMQuantile_div_log_succ :
    Tendsto (fun n : ℕ =>
      Real.log (routeKRVMQuantile n) / Real.log ((n : ℝ) + 1))
      atTop (nhds 1) := by
  have hNtop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlogNtop : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hNtop
  rw [tendsto_order]
  constructor
  · intro a ha
    let η : ℝ := (1 - a) / 4
    let C : ℝ := (2 * Real.pi * η)⁻¹ + 1
    have hη : 0 < η := by dsimp [η]; linarith
    have hC : 0 < C := by
      dsimp [C]
      have : 0 < 2 * Real.pi * η := by positivity
      positivity
    have hmodel : Tendsto (fun n : ℕ =>
        (1 - Real.log C / Real.log ((n : ℝ) + 1)) / (1 + η))
        atTop (nhds (1 / (1 + η))) := by
      have hzero := hlogNtop.const_div_atTop (Real.log C)
      simpa [one_div] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hzero).div_const (1 + η)
    have hamodel : a < 1 / (1 + η) := by
      have hden : 0 < 1 + η := by linarith
      rw [lt_div_iff₀ hden]
      dsimp [η]
      by_cases ha0 : a ≤ 0
      · nlinarith
      · nlinarith
    have hevent := hmodel.eventually_const_lt hamodel
    filter_upwards [hevent, eventually_gt_atTop 0] with n han hn
    have hN : 0 < (n : ℝ) + 1 := by positivity
    have hlogN : 0 < Real.log ((n : ℝ) + 1) := by
      apply Real.log_pos
      exact_mod_cast Nat.succ_lt_succ hn
    have hT : 0 < routeKRVMQuantile n :=
      routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n)
    have hgrowth := routeKRVMQuantile_subpower_growth hη n
    change (n : ℝ) + 1 ≤ C * routeKRVMQuantile n ^ (1 + η) at hgrowth
    have hlogineq : Real.log ((n : ℝ) + 1) ≤
        Real.log C + (1 + η) * Real.log (routeKRVMQuantile n) := by
      calc
        Real.log ((n : ℝ) + 1) ≤
            Real.log (C * routeKRVMQuantile n ^ (1 + η)) :=
          Real.log_le_log hN hgrowth
        _ = Real.log C + (1 + η) * Real.log (routeKRVMQuantile n) := by
          rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hT _).ne',
            Real.log_rpow hT]
    have hlower :
        (1 - Real.log C / Real.log ((n : ℝ) + 1)) / (1 + η) ≤
          Real.log (routeKRVMQuantile n) / Real.log ((n : ℝ) + 1) := by
      have hηden : 0 < 1 + η := by linarith
      rw [div_le_div_iff₀ hηden hlogN]
      field_simp [hlogN.ne'] at hlogineq ⊢
      nlinarith
    exact han.trans_le hlower
  · intro b hb
    let C : ℝ := 2 * routeKRVMBase * Real.exp 1
    have hC : 0 < C := by
      dsimp [C]
      exact mul_pos (mul_pos two_pos routeKRVMBase_pos) (Real.exp_pos 1)
    have hmodel : Tendsto (fun n : ℕ =>
        1 + Real.log C / Real.log ((n : ℝ) + 1)) atTop (nhds 1) := by
      have hzero := hlogNtop.const_div_atTop (Real.log C)
      simpa using tendsto_const_nhds.add hzero
    have hevent := hmodel.eventually_lt_const hb
    filter_upwards [hevent, eventually_gt_atTop 0] with n hnb hn
    have hN : 0 < (n : ℝ) + 1 := by positivity
    have hlogN : 0 < Real.log ((n : ℝ) + 1) := by
      apply Real.log_pos
      exact_mod_cast Nat.succ_lt_succ hn
    have hT : 0 < routeKRVMQuantile n :=
      routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n)
    have hlinear := routeKRVMQuantile_le_linear n
    change routeKRVMQuantile n ≤ C * ((n : ℝ) + 1) at hlinear
    have hlogineq : Real.log (routeKRVMQuantile n) ≤
        Real.log C + Real.log ((n : ℝ) + 1) := by
      calc
        Real.log (routeKRVMQuantile n) ≤
            Real.log (C * ((n : ℝ) + 1)) :=
          Real.log_le_log hT hlinear
        _ = Real.log C + Real.log ((n : ℝ) + 1) := by
          rw [Real.log_mul hC.ne' hN.ne']
    have hupper :
        Real.log (routeKRVMQuantile n) / Real.log ((n : ℝ) + 1) ≤
          1 + Real.log C / Real.log ((n : ℝ) + 1) := by
      rw [div_le_iff₀ hlogN]
      field_simp [hlogN.ne']
      linarith
    exact hupper.trans_lt hnb

theorem tendsto_routeKRVMQuantile_div_rvmModel :
    Tendsto (fun n : ℕ =>
      routeKRVMQuantile n /
        (2 * Real.pi * ((n : ℝ) + 1) / Real.log ((n : ℝ) + 1)))
      atTop (nhds 1) := by
  have hNtop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlogNtop : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hNtop
  have hbaseRatio : Tendsto (fun n : ℕ =>
      Real.log (routeKRVMQuantile n / routeKRVMBase) /
        Real.log ((n : ℝ) + 1)) atTop (nhds 1) := by
    have hconst := hlogNtop.const_div_atTop (Real.log routeKRVMBase)
    have hsub := tendsto_log_routeKRVMQuantile_div_log_succ.sub hconst
    convert hsub using 1
    · funext n
      rw [Real.log_div
        (routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n)).ne'
        routeKRVMBase_pos.ne', sub_div]
    · norm_num
  have hinv : Tendsto (fun n : ℕ =>
      Real.log ((n : ℝ) + 1) /
        Real.log (routeKRVMQuantile n / routeKRVMBase)) atTop (nhds 1) := by
    have h := hbaseRatio.inv₀ one_ne_zero
    simpa [one_div, div_eq_mul_inv] using h
  have hsmall : Tendsto (fun n : ℕ =>
      (7 / 8 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    hNtop.const_div_atTop (7 / 8 : ℝ)
  have hfactor : Tendsto (fun n : ℕ =>
      1 - (7 / 8 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hsmall
  have hproduct := hfactor.mul hinv
  have heq : (fun n : ℕ =>
      (1 - (7 / 8 : ℝ) / ((n : ℝ) + 1)) *
        (Real.log ((n : ℝ) + 1) /
          Real.log (routeKRVMQuantile n / routeKRVMBase))) =ᶠ[atTop]
      (fun n : ℕ =>
        routeKRVMQuantile n /
          (2 * Real.pi * ((n : ℝ) + 1) / Real.log ((n : ℝ) + 1))) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hN : 0 < (n : ℝ) + 1 := by positivity
    have hlogN : 0 < Real.log ((n : ℝ) + 1) := by
      apply Real.log_pos
      exact_mod_cast Nat.succ_lt_succ hn
    have hT : 0 < routeKRVMQuantile n :=
      routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n)
    have hratio : 1 < routeKRVMQuantile n / routeKRVMBase :=
      (lt_div_iff₀ routeKRVMBase_pos).2 (by
        simpa using routeKRVMBase_lt_quantile n)
    have hlogT : 0 < Real.log (routeKRVMQuantile n / routeKRVMBase) :=
      Real.log_pos hratio
    have hcount := routeKSmoothRVMCount_quantile n
    rw [routeKSmoothRVMCount] at hcount
    field_simp [hN.ne', hlogN.ne', hlogT.ne', Real.pi_ne_zero] at hcount ⊢
    nlinarith [Real.pi_pos]
  simpa using hproduct.congr' heq

theorem tendsto_routeKRVMQuantile_reciprocal_div_rvmModel :
    Tendsto (fun n : ℕ =>
      (routeKRVMQuantile n)⁻¹ /
        (Real.log ((n : ℝ) + 1) /
          (2 * Real.pi * ((n : ℝ) + 1)))) atTop (nhds 1) := by
  have hinv := tendsto_routeKRVMQuantile_div_rvmModel.inv₀ one_ne_zero
  have hinv' : Tendsto (fun n : ℕ =>
      (routeKRVMQuantile n /
        (2 * Real.pi * ((n : ℝ) + 1) / Real.log ((n : ℝ) + 1)))⁻¹)
      atTop (nhds 1) := by
    simpa using hinv
  apply hinv'.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hlogN : 0 < Real.log ((n : ℝ) + 1) := by
    apply Real.log_pos
    exact_mod_cast Nat.succ_lt_succ hn
  have hT : 0 < routeKRVMQuantile n :=
    routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n)
  field_simp [hN.ne', hlogN.ne', hT.ne', Real.pi_ne_zero]

end

end RHTower
