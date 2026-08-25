import GaloisForLFunctions.RHTower.RoutePTwoStepWildSaddleTraceClassRelocation
import GaloisForLFunctions.HTGeometry.SchattenApproximationAdditivity
import GaloisForLFunctions.RHTower.SchattenTwoIdentity

/-!
# Sharp wild-saddle truncation depth for trace-class Xi relocation

The smooth Riemann--von Mangoldt inverse is the positive Lambert-W saddle
`u + log u = L`.  Its first two source-only logarithmic fixed-point truncations are
`u₁ = L - log L` and `u₂ = L - log u₁`.

This file proves the sharp trace-ideal boundary.  The one-step reciprocal defect has an eventual
prime-harmonic lower bound, so neither its signed RVM correction nor its correction to actual
reciprocal Xi is Schatten-1.  It is nevertheless Schatten-2.  The existing two-step source is
Schatten-1 close to both RVM and actual reciprocal Xi.  Thus two irregular stationary-phase
corrections are necessary and sufficient for determinant-grade relocation.

No RH assumption or target-fed datum enters either source operator.  This result does not identify
the remaining trace-class correction or assert determinant equality.
-/

open scoped BigOperators InnerProductSpace Nat.Prime
open Filter

namespace RHTower

noncomputable section

theorem oneStepLogFixedPoint_error_lower {L u : ℝ}
    (hL : 2 ≤ L) (hu : 0 < u)
    (hfix : u + Real.log u = L) :
    1 / (4 * L) ≤ u - (L - Real.log L) := by
  have hLpos : 0 < L := by linarith
  have huOne : 1 < u := by
    by_contra hnot
    have hule : u ≤ 1 := le_of_not_gt hnot
    have hlogu : Real.log u ≤ 0 := Real.log_nonpos hu.le hule
    linarith
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg huOne.le
  have huL : u ≤ L := by linarith
  have hu43 : (4 / 3 : ℝ) ≤ u := by
    by_contra hnot
    have hult : u < 4 / 3 := lt_of_not_ge hnot
    have hlogUpper : Real.log u ≤ u - 1 :=
      Real.log_le_sub_one_of_pos hu
    linarith
  have hinvLe : u⁻¹ ≤ (3 / 4 : ℝ) := by
    rw [inv_eq_one_div, div_le_iff₀ hu]
    nlinarith
  have hloguQuarter : (1 / 4 : ℝ) ≤ Real.log u := by
    have hlogInv := Real.log_le_sub_one_of_pos (inv_pos.mpr hu)
    rw [Real.log_inv] at hlogInv
    linarith
  have hratioPos : 0 < L / u := div_pos hLpos hu
  have hlogRatioLower : Real.log u / L ≤ Real.log (L / u) := by
    have hlogInv := Real.log_le_sub_one_of_pos (inv_pos.mpr hratioPos)
    rw [Real.log_inv] at hlogInv
    have hreflect : 1 - 1 / (L / u) ≤ Real.log (L / u) := by
      simp only [one_div]
      linarith
    have hgap : L - u = Real.log u := by linarith
    have hinvRatio : 1 / (L / u) = u / L := by
      field_simp [hLpos.ne', hu.ne']
    have hfrac : Real.log u / L = 1 - u / L := by
      field_simp [hLpos.ne']
      linarith
    rw [hinvRatio] at hreflect
    rw [hfrac]
    exact hreflect
  have hlogDiff : u - (L - Real.log L) = Real.log (L / u) := by
    rw [Real.log_div hLpos.ne' hu.ne']
    linarith
  rw [hlogDiff]
  apply le_trans ?_ hlogRatioLower
  have heq : 1 / (4 * L) = (1 / 4 : ℝ) * L⁻¹ := by
    field_simp [hLpos.ne']
  rw [heq, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hloguQuarter (inv_nonneg.mpr hLpos.le)

def routePOneStepWildSaddleReciprocal (n : ℕ) : ℝ :=
  routePTwoStepWildSaddleFirstPhase n /
    (2 * Real.pi * routePTwoStepWildSaddleMass n)

theorem routePOneStepWildSaddleReciprocal_nonneg (n : ℕ) :
    0 ≤ routePOneStepWildSaddleReciprocal n := by
  exact div_nonneg
    (le_trans (by linarith [routePTwoStepWildSaddleLogPhase_ge_two n])
      (routePTwoStepWildSaddleFirstPhase_bounds n).1)
    (mul_nonneg (by positivity) (routePTwoStepWildSaddleMass_pos n).le)

theorem routePOneStepWildSaddleReciprocal_le_one (n : ℕ) :
    routePOneStepWildSaddleReciprocal n ≤ 1 := by
  have hm := routePTwoStepWildSaddleMass_pos n
  have hfirst := (routePTwoStepWildSaddleFirstPhase_bounds n).2
  have hphase := routePTwoStepWildSaddleLogPhase_le_mass n
  rw [routePOneStepWildSaddleReciprocal, div_le_one (by positivity)]
  have htwoPi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  calc
    routePTwoStepWildSaddleFirstPhase n ≤
        routePTwoStepWildSaddleMass n := hfirst.trans hphase
    _ ≤ 2 * Real.pi * routePTwoStepWildSaddleMass n := by
      nlinarith

def routePOneStepWildSaddleRVMDefect (n : ℕ) : ℝ :=
  |routePOneStepWildSaddleReciprocal n - (routeKRVMQuantile n)⁻¹|

theorem eventually_routePOneStepWildSaddleRVMDefect_ge_primeReciprocal :
    ∀ᶠ n : ℕ in atTop,
      1 / (256 * ((Nat.nth Nat.Prime n : ℕ) : ℝ)) ≤
        routePOneStepWildSaddleRVMDefect n := by
  have hden : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * Real.log (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
    have hlogn0 : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    exact mul_ne_zero hn0 hlogn0
  have hratio : Tendsto (fun n : ℕ =>
      ((Nat.nth Nat.Prime n : ℕ) : ℝ) /
        ((n : ℝ) * Real.log (n : ℝ))) atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hden).mp nth_prime_asymp
  filter_upwards [eventually_routePTwoStepWildSaddleMass_eq,
      hratio.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1),
      eventually_gt_atTop 1] with n hmass hnratio hn
  let N : ℝ := (n : ℝ) + 1 / 8
  let L : ℝ := Real.log (N / Real.exp 1)
  let u : ℝ := Real.log (routeKRVMQuantile n / routeKRVMBase)
  let u₁ : ℝ := L - Real.log L
  let p : ℝ := ((Nat.nth Nat.Prime n : ℕ) : ℝ)
  let logn : ℝ := Real.log (n : ℝ)
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnTwo : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : 0 < logn := by
    dsimp [logn]
    exact Real.log_pos (by exact_mod_cast hn)
  have hN : 0 < N := by dsimp [N]; positivity
  have hL : 2 ≤ L := by
    simpa [routePTwoStepWildSaddleLogPhase, L, N, hmass] using
      routePTwoStepWildSaddleLogPhase_ge_two n
  have hLpos : 0 < L := by linarith
  have hu : 0 < u := by
    dsimp [u]
    exact routeKRVMQuantile_logPhase_pos n
  have hfix : u + Real.log u = L := by
    simpa [u, L, N] using routeKRVMQuantile_logPhase_fixedPoint n
  have herr : 1 / (4 * L) ≤ u - u₁ := by
    simpa [u₁] using oneStepLogFixedPoint_error_lower hL hu hfix
  have huOne : 1 < u := by
    by_contra hnot
    have hule : u ≤ 1 := le_of_not_gt hnot
    have hlogu : Real.log u ≤ 0 := Real.log_nonpos hu.le hule
    linarith
  have huL : u ≤ L := by
    linarith [Real.log_nonneg huOne.le]
  have hloguL : Real.log u ≤ Real.log L :=
    Real.strictMonoOn_log.monotoneOn hu hLpos huL
  have hu₁u : u₁ ≤ u := by
    dsimp [u₁]
    linarith
  have hsource : routePOneStepWildSaddleReciprocal n =
      u₁ / (2 * Real.pi * N) := by
    simp [routePOneStepWildSaddleReciprocal,
      routePTwoStepWildSaddleFirstPhase,
      routePTwoStepWildSaddleLogPhase, u₁, L, N, hmass]
  have hrvm : (routeKRVMQuantile n)⁻¹ =
      u / (2 * Real.pi * N) := by
    simpa [u, N] using routeKRVMQuantile_reciprocal_eq_logPhase_div n
  have hdenpos : 0 < 2 * Real.pi * N := by positivity
  have hdefect : routePOneStepWildSaddleRVMDefect n =
      (u - u₁) / (2 * Real.pi * N) := by
    rw [routePOneStepWildSaddleRVMDefect, hsource, hrvm]
    rw [abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (div_le_div_of_nonneg_right hu₁u hdenpos.le)
  have hp : 0 < p := by
    dsimp [p]
    exact_mod_cast (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n).pos
  have hpLower : ((n : ℝ) * logn) / 2 ≤ p := by
    have hratio' : (1 / 2 : ℝ) < p / ((n : ℝ) * logn) := by
      simpa [p, logn] using hnratio
    have hdenNat : 0 < (n : ℝ) * logn := mul_pos hnpos hlogn
    have := (lt_div_iff₀ hdenNat).mp hratio'
    linarith
  have hNle : N ≤ 2 * (n : ℝ) := by
    dsimp [N]
    linarith
  have hlogTwoLe : Real.log (2 : ℝ) ≤ logn := by
    dsimp [logn]
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hnpos hnTwo
  have hlogNle : Real.log N ≤ 2 * logn := by
    calc
      Real.log N ≤ Real.log (2 * (n : ℝ)) :=
        Real.strictMonoOn_log.monotoneOn hN (mul_pos (by norm_num) hnpos) hNle
      _ = Real.log 2 + logn := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne']
      _ ≤ 2 * logn := by linarith
  have hLformula : L = Real.log N - 1 := by
    dsimp [L]
    rw [Real.log_div hN.ne' (Real.exp_ne_zero 1), Real.log_exp]
  have hLle : L ≤ 2 * logn := by rw [hLformula]; linarith
  have hNLle : N * L ≤ 4 * ((n : ℝ) * logn) := by
    calc
      N * L ≤ (2 * (n : ℝ)) * (2 * logn) :=
        mul_le_mul hNle hLle hLpos.le (by positivity)
      _ = 4 * ((n : ℝ) * logn) := by ring
  have hNLp : N * L ≤ 8 * p := by linarith
  have hraw : 1 / (32 * (N * L)) ≤
      (u - u₁) / (2 * Real.pi * N) := by
    have herrMul : 1 ≤ 4 * L * (u - u₁) := by
      have h := (div_le_iff₀ (mul_pos (by norm_num) hLpos)).mp herr
      nlinarith
    field_simp [hN.ne', hLpos.ne', Real.pi_ne_zero]
    nlinarith [Real.pi_pos, Real.pi_lt_four, herrMul]
  have hprimeCompare : 1 / (256 * p) ≤ 1 / (32 * (N * L)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [hdefect]
  exact hprimeCompare.trans hraw

theorem not_summable_routePOneStepWildSaddleRVMDefect :
    ¬ Summable routePOneStepWildSaddleRVMDefect := by
  intro hsum
  have hsmall : Summable (fun n : ℕ =>
      1 / (256 * ((Nat.nth Nat.Prime n : ℕ) : ℝ))) := by
    apply hsum.of_norm_bounded_eventually
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_routePOneStepWildSaddleRVMDefect_ge_primeReciprocal]
      with n hn
    have hp : 0 < ((Nat.nth Nat.Prime n : ℕ) : ℝ) := by
      exact_mod_cast (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n).pos
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hn
  apply not_summable_nthPrime_reciprocal
  have hscaled := hsmall.mul_left 256
  have hnat : Summable (fun n : ℕ =>
      1 / (((Nat.nth Nat.Prime n : ℕ) : ℝ))) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  simpa [nthPrimeSubtype] using hnat

def routePOneStepWildSaddlePrimeReciprocal (p : Nat.Primes) : ℝ :=
  routePOneStepWildSaddleReciprocal (routeKPrimeRVMIndex p)

theorem routePOneStepWildSaddlePrimeReciprocal_nonneg (p : Nat.Primes) :
    0 ≤ routePOneStepWildSaddlePrimeReciprocal p :=
  routePOneStepWildSaddleReciprocal_nonneg _

theorem routePOneStepWildSaddlePrimeReciprocal_le_one (p : Nat.Primes) :
    routePOneStepWildSaddlePrimeReciprocal p ≤ 1 :=
  routePOneStepWildSaddleReciprocal_le_one _

theorem routePOneStepWildSaddlePrimeReciprocal_le_twoStep
    (p : Nat.Primes) :
    routePOneStepWildSaddlePrimeReciprocal p ≤
      routePTwoStepWildSaddlePrimeReciprocal p := by
  rw [routePOneStepWildSaddlePrimeReciprocal,
    routePTwoStepWildSaddlePrimeReciprocal,
    routePOneStepWildSaddleReciprocal,
    routePTwoStepWildSaddleReciprocal]
  exact div_le_div_of_nonneg_right
    (routePTwoStepWildSaddleSecondPhase_bounds _).1
    (mul_nonneg (by positivity) (routePTwoStepWildSaddleMass_pos _).le)

theorem not_summable_abs_routePOneStepWildSaddlePrimeReciprocal_sub_rvm :
    ¬ Summable (fun p : Nat.Primes =>
      |routePOneStepWildSaddlePrimeReciprocal p -
        routeKPrimeRVMReciprocal p|) := by
  intro hprime
  apply not_summable_routePOneStepWildSaddleRVMDefect
  have hnat := nthPrimeEquiv.summable_iff.mpr hprime
  change Summable (fun n : ℕ =>
    |routePOneStepWildSaddleReciprocal n - (routeKRVMQuantile n)⁻¹|)
  simpa [Function.comp_def, nthPrimeEquiv,
    routePOneStepWildSaddlePrimeReciprocal,
    routeKPrimeRVMReciprocal,
    routeKPrimeRVMIndex_nthPrimeSubtype] using hnat

def routePOneStepWildSaddleSignedMultiplier : RouteKSignedPrimeIndex → ℂ
  | Sum.inl p => (routePOneStepWildSaddlePrimeReciprocal p : ℂ)
  | Sum.inr p => -(routePOneStepWildSaddlePrimeReciprocal p : ℂ)

theorem norm_routePOneStepWildSaddleSignedMultiplier_le_one
    (i : RouteKSignedPrimeIndex) :
    ‖routePOneStepWildSaddleSignedMultiplier i‖ ≤ 1 := by
  cases i with
  | inl p =>
      simpa [routePOneStepWildSaddleSignedMultiplier, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg
          (routePOneStepWildSaddlePrimeReciprocal_nonneg p)] using
        routePOneStepWildSaddlePrimeReciprocal_le_one p
  | inr p =>
      simpa [routePOneStepWildSaddleSignedMultiplier, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
          (routePOneStepWildSaddlePrimeReciprocal_nonneg p)] using
        routePOneStepWildSaddlePrimeReciprocal_le_one p

def routePOneStepWildSaddleSignedOperator :
    RouteKSignedPrimeHilbert →L[ℂ] RouteKSignedPrimeHilbert :=
  HTGeometry.ellTwoDiagonal routePOneStepWildSaddleSignedMultiplier
    norm_routePOneStepWildSaddleSignedMultiplier_le_one

theorem routePOneStepWildSaddleSignedOperator_basis_inl (p : Nat.Primes) :
    routePOneStepWildSaddleSignedOperator
        (HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex (Sum.inl p)) =
      (routePOneStepWildSaddlePrimeReciprocal p : ℂ) •
        HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex (Sum.inl p) := by
  simpa [routePOneStepWildSaddleSignedOperator,
    routePOneStepWildSaddleSignedMultiplier] using
    HTGeometry.ellTwoDiagonal_coordinateBasis
      routePOneStepWildSaddleSignedMultiplier
      norm_routePOneStepWildSaddleSignedMultiplier_le_one (Sum.inl p)

theorem routePOneStepWildSaddleSignedOperator_basis_inr (p : Nat.Primes) :
    routePOneStepWildSaddleSignedOperator
        (HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex (Sum.inr p)) =
      -(routePOneStepWildSaddlePrimeReciprocal p : ℂ) •
        HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex (Sum.inr p) := by
  simpa [routePOneStepWildSaddleSignedOperator,
    routePOneStepWildSaddleSignedMultiplier] using
    HTGeometry.ellTwoDiagonal_coordinateBasis
      routePOneStepWildSaddleSignedMultiplier
      norm_routePOneStepWildSaddleSignedMultiplier_le_one (Sum.inr p)

theorem routePOneStepWildSaddleSignedOperator_selfAdjoint :
    ContinuousLinearMap.adjoint routePOneStepWildSaddleSignedOperator =
      routePOneStepWildSaddleSignedOperator := by
  rw [routePOneStepWildSaddleSignedOperator,
    HTGeometry.adjoint_ellTwoDiagonal]
  ext f i
  rw [HTGeometry.ellTwoDiagonal_apply, HTGeometry.ellTwoDiagonal_apply]
  cases i <;> simp [routePOneStepWildSaddleSignedMultiplier]

theorem routePOneStepWildSaddleSignedOperator_sub_rvm_not_memSchattenClass_one :
    ¬ MemSchattenClass 1
      (routePOneStepWildSaddleSignedOperator -
        routeKSignedPrimeRVMOperator) := by
  intro htrace
  have hdiag := htrace.one_summable_norm_inner_diag_basis
    (HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex)
  have hleft := hdiag.comp_injective
    (i := fun p : Nat.Primes => (Sum.inl p : RouteKSignedPrimeIndex))
    (fun _ _ h => Sum.inl.inj h)
  apply not_summable_abs_routePOneStepWildSaddlePrimeReciprocal_sub_rvm
  apply hleft.congr
  intro p
  simp only [Function.comp_apply]
  rw [sub_apply,
    routePOneStepWildSaddleSignedOperator_basis_inl,
    routeKSignedPrimeRVMOperator_basis_inl]
  rw [← sub_smul, inner_smul_right]
  have hnorm :=
    (HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex).orthonormal.1
      (Sum.inl p)
  rw [inner_self_eq_norm_sq_to_K, hnorm]
  norm_num
  have hcast :
      (routePOneStepWildSaddlePrimeReciprocal p : ℂ) -
          (routeKPrimeRVMReciprocal p : ℂ) =
        ((routePOneStepWildSaddlePrimeReciprocal p -
          routeKPrimeRVMReciprocal p : ℝ) : ℂ) := by
    norm_num
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]

theorem xiOrderedSignedPrimeOperator_sub_routePOneStepWildSaddleSignedOperator_not_memSchattenClass_one :
    ¬ MemSchattenClass 1
      (xiOrderedSignedPrimeOperator -
        routePOneStepWildSaddleSignedOperator) := by
  intro hxi
  have hXR :=
    xiOrderedSignedPrimeOperator_sub_routeKSignedPrimeRVMOperator_memSchattenClass_one
  have hdiff := hxi.one_sub hXR
  apply routePOneStepWildSaddleSignedOperator_sub_rvm_not_memSchattenClass_one
  have heq : routePOneStepWildSaddleSignedOperator -
      routeKSignedPrimeRVMOperator =
        -((xiOrderedSignedPrimeOperator -
            routePOneStepWildSaddleSignedOperator) -
          (xiOrderedSignedPrimeOperator - routeKSignedPrimeRVMOperator)) := by
    abel
  rw [heq]
  exact hdiff.one_neg

theorem routePTwoStepWildSaddleSignedOperator_memSchattenClass_two :
    MemSchattenClass 2 routePTwoStepWildSaddleSignedOperator := by
  have hcorrTwo : MemSchattenClass 2
      (routePTwoStepWildSaddleSignedOperator -
        routeKSignedPrimeRVMOperator) :=
    routePTwoStepWildSaddleSignedOperator_sub_routeKSignedPrimeRVMOperator_memSchattenClass_one.mono
      (by norm_num) (by norm_num)
  have hsum := GaloisForLFunctions.HTGeometry.memSchattenClass_add
    (by norm_num : (0 : ℝ) < 2) hcorrTwo
      routeKSignedPrimeRVMOperator_memSchattenClass_two
  have heq : routePTwoStepWildSaddleSignedOperator =
      (routePTwoStepWildSaddleSignedOperator - routeKSignedPrimeRVMOperator) +
        routeKSignedPrimeRVMOperator := by abel
  rw [heq]
  exact hsum

theorem routePOneStepWildSaddleSignedOperator_memSchattenClass_two :
    MemSchattenClass 2 routePOneStepWildSaddleSignedOperator := by
  have htwoHS : routePTwoStepWildSaddleSignedOperator.IsHilbertSchmidt :=
    (memSchattenClass_two_iff_isHilbertSchmidt _).mp
      routePTwoStepWildSaddleSignedOperator_memSchattenClass_two
  have hsumTwo : Summable (fun i : RouteKSignedPrimeIndex =>
      ‖routePTwoStepWildSaddleSignedMultiplier i‖ ^ 2) :=
    (HTGeometry.isHilbertSchmidt_ellTwoDiagonal_iff
      routePTwoStepWildSaddleSignedMultiplier
      norm_routePTwoStepWildSaddleSignedMultiplier_le_one).mp htwoHS
  have hnormLe : ∀ i : RouteKSignedPrimeIndex,
      ‖routePOneStepWildSaddleSignedMultiplier i‖ ≤
        ‖routePTwoStepWildSaddleSignedMultiplier i‖ := by
    intro i
    cases i with
    | inl p =>
        simpa [routePOneStepWildSaddleSignedMultiplier,
          routePTwoStepWildSaddleSignedMultiplier, Complex.norm_real,
          Real.norm_eq_abs,
          abs_of_nonneg (routePOneStepWildSaddlePrimeReciprocal_nonneg p),
          abs_of_nonneg (routePTwoStepWildSaddlePrimeReciprocal_nonneg p)] using
          routePOneStepWildSaddlePrimeReciprocal_le_twoStep p
    | inr p =>
        simpa [routePOneStepWildSaddleSignedMultiplier,
          routePTwoStepWildSaddleSignedMultiplier, Complex.norm_real,
          Real.norm_eq_abs,
          abs_of_nonneg (routePOneStepWildSaddlePrimeReciprocal_nonneg p),
          abs_of_nonneg (routePTwoStepWildSaddlePrimeReciprocal_nonneg p)] using
          routePOneStepWildSaddlePrimeReciprocal_le_twoStep p
  have hsumOne : Summable (fun i : RouteKSignedPrimeIndex =>
      ‖routePOneStepWildSaddleSignedMultiplier i‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) ?_ hsumTwo
    intro i
    have hle := hnormLe i
    nlinarith [norm_nonneg (routePOneStepWildSaddleSignedMultiplier i),
      norm_nonneg (routePTwoStepWildSaddleSignedMultiplier i)]
  apply (memSchattenClass_two_iff_isHilbertSchmidt _).mpr
  exact (HTGeometry.isHilbertSchmidt_ellTwoDiagonal_iff
    routePOneStepWildSaddleSignedMultiplier
    norm_routePOneStepWildSaddleSignedMultiplier_le_one).mpr hsumOne

/-- Depth two is the sharp wild-saddle truncation for trace-class relocation to reciprocal Xi. -/
theorem routeP_wildSaddle_minimalTraceClassDepth :
    MemSchattenClass 2 routePOneStepWildSaddleSignedOperator ∧
    ¬ MemSchattenClass 1
      (routePOneStepWildSaddleSignedOperator - routeKSignedPrimeRVMOperator) ∧
    ¬ MemSchattenClass 1
      (xiOrderedSignedPrimeOperator - routePOneStepWildSaddleSignedOperator) ∧
    MemSchattenClass 1
      (routePTwoStepWildSaddleSignedOperator - routeKSignedPrimeRVMOperator) ∧
    MemSchattenClass 1
      (xiOrderedSignedPrimeOperator - routePTwoStepWildSaddleSignedOperator) := by
  exact ⟨routePOneStepWildSaddleSignedOperator_memSchattenClass_two,
    routePOneStepWildSaddleSignedOperator_sub_rvm_not_memSchattenClass_one,
    xiOrderedSignedPrimeOperator_sub_routePOneStepWildSaddleSignedOperator_not_memSchattenClass_one,
    routePTwoStepWildSaddleSignedOperator_sub_routeKSignedPrimeRVMOperator_memSchattenClass_one,
    xiOrderedSignedPrimeOperator_sub_routePTwoStepWildSaddleSignedOperator_memSchattenClass_one⟩

end

end RHTower
