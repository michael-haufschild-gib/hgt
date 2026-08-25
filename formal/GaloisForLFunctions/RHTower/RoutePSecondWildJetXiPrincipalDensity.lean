import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaLogFullWeakTraceNoGo
import GaloisForLFunctions.RHTower.PrimeDiagonalSingularValues
import GaloisForLFunctions.RHTower.CriticalPrimeSourceSchattenIdeal
import GaloisForLFunctions.RHTower.XiOrderedPrimeApproximationAsymptotics

/-!
# Route-P second wild jet and Xi principal singular density

The intrinsic second wild/Mellin derivative of the prime-labelled Route-P exponential factors has
cofinal weight `(log p)^2 / (2πp)`. After signed multiplicity two, its approximation numbers have
exactly Xi's principal `log(n+1) / (π(n+1))` density. The resulting source operator belongs to
`S₂` and the logarithmically enhanced weak-trace class, has residue `1 / π`, and lies outside
ordinary weak `S₁`.

This identifies principal singular density only; it does not assert determinant equality or RH.
-/

open scoped BigOperators InnerProductSpace Nat.Prime
open Filter ContinuousLinearMap

namespace RHTower

noncomputable section

/-- Square of the first logarithmic wild half-density, with RVM normalization. -/
def routePSecondWildJetProfile (x : ℝ) : ℝ :=
  (Real.log x * x ^ (-(1 / 2 : ℝ))) ^ 2 / (2 * Real.pi)

theorem routePSecondWildJetProfile_nonneg (x : ℝ) :
    0 ≤ routePSecondWildJetProfile x := by
  exact div_nonneg (sq_nonneg _) (by positivity)

theorem routePSecondWildJetProfile_eq_log_sq_div
    {x : ℝ} (hx : 0 < x) :
    routePSecondWildJetProfile x =
      Real.log x ^ 2 / (2 * Real.pi * x) := by
  have hrpow : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hx.le]
    norm_num [Real.rpow_neg_one]
  rw [routePSecondWildJetProfile, mul_pow, hrpow]
  field_simp

theorem routePSecondWildJetProfile_antitoneOn :
    AntitoneOn routePSecondWildJetProfile (Set.Ici (Real.exp 2)) := by
  have hbase := antitoneOn_log_mul_rpow (σ := (1 / 2 : ℝ)) (by norm_num)
  have hbase' : AntitoneOn
      (fun t : ℝ => Real.log t * t ^ (-(1 / 2 : ℝ)))
      (Set.Ici (Real.exp 2)) := by
    simpa using hbase
  intro x hx y hy hxy
  have hxy' := hbase' hx hy hxy
  have hbasex : 0 ≤ Real.log x * x ^ (-(1 / 2 : ℝ)) := by
    have hxpos : 0 < x := (Real.exp_pos 2).trans_le hx
    exact mul_nonneg (Real.log_nonneg
        ((Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans hx))
      (Real.rpow_nonneg hxpos.le (-(1 / 2 : ℝ)))
  have hbasey : 0 ≤ Real.log y * y ^ (-(1 / 2 : ℝ)) := by
    have hypos : 0 < y := (Real.exp_pos 2).trans_le hy
    exact mul_nonneg (Real.log_nonneg
        ((Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans hy))
      (Real.rpow_nonneg hypos.le (-(1 / 2 : ℝ)))
  rw [routePSecondWildJetProfile, routePSecondWildJetProfile]
  gcongr

/-- Finite low-prime regularization; it is literal `(log p)^2/(2πp)` cofinally. -/
def routePSecondWildJetPrimeWeight (p : Nat.Primes) : ℝ :=
  routePSecondWildJetProfile (max (Real.exp 2) (p : ℝ))

theorem routePSecondWildJetPrimeWeight_nonneg (p : Nat.Primes) :
    0 ≤ routePSecondWildJetPrimeWeight p :=
  routePSecondWildJetProfile_nonneg _

theorem routePSecondWildJetPrimeWeight_ordered_antitone :
    Antitone (fun n : ℕ =>
      routePSecondWildJetPrimeWeight (nthPrimeSubtype n)) := by
  intro i j hij
  apply routePSecondWildJetProfile_antitoneOn
  · exact (show Real.exp 2 ≤
      max (Real.exp 2) ((nthPrimeSubtype i : Nat.Primes) : ℝ) from le_max_left _ _)
  · exact (show Real.exp 2 ≤
      max (Real.exp 2) ((nthPrimeSubtype j : Nat.Primes) : ℝ) from le_max_left _ _)
  · have hp : ((nthPrimeSubtype i : Nat.Primes) : ℕ) ≤
        ((nthPrimeSubtype j : Nat.Primes) : ℕ) :=
      nthPrimeSubtype_strictMono.monotone hij
    exact max_le_max (le_refl _) (by exact_mod_cast hp)

/-- Signed multiplicity-two second-wild-jet singular sequence. -/
def routePSecondWildJetSignedApproxNumber (n : ℕ) : ℝ :=
  routePSecondWildJetPrimeWeight (nthPrimeSubtype (n / 2))

theorem routePSecondWildJetSignedApproxNumber_nonneg (n : ℕ) :
    0 ≤ routePSecondWildJetSignedApproxNumber n :=
  routePSecondWildJetPrimeWeight_nonneg _

theorem routePSecondWildJetSignedApproxNumber_antitone :
    Antitone routePSecondWildJetSignedApproxNumber := by
  intro i j hij
  exact routePSecondWildJetPrimeWeight_ordered_antitone
    (Nat.div_le_div_right hij)

/-- Opposite orientations of intrinsic Route-P second wild jet. -/
def routePSecondWildJetSignedMultiplier : RouteKSignedPrimeIndex → ℂ
  | Sum.inl p => (routePSecondWildJetPrimeWeight p : ℂ)
  | Sum.inr p => -(routePSecondWildJetPrimeWeight p : ℂ)

theorem norm_routePSecondWildJetSignedMultiplier (i : RouteKSignedPrimeIndex) :
    ‖routePSecondWildJetSignedMultiplier i‖ =
      routePSecondWildJetSignedApproxNumber (routeKSignedPrimeEquiv.symm i) := by
  cases i with
  | inl p =>
      rw [routePSecondWildJetSignedMultiplier, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (routePSecondWildJetPrimeWeight_nonneg p)]
      rw [routePSecondWildJetSignedApproxNumber,
        routeKSignedPrimeEquiv_symm_apply, routeKSignedPrimeNatIndex]
      rw [show (2 * routeKPrimeRVMIndex p) / 2 =
          routeKPrimeRVMIndex p by omega,
        nthPrimeSubtype_routeKPrimeRVMIndex]
  | inr p =>
      rw [routePSecondWildJetSignedMultiplier, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (routePSecondWildJetPrimeWeight_nonneg p)]
      rw [routePSecondWildJetSignedApproxNumber,
        routeKSignedPrimeEquiv_symm_apply, routeKSignedPrimeNatIndex]
      rw [show (2 * routeKPrimeRVMIndex p + 1) / 2 =
          routeKPrimeRVMIndex p by omega,
        nthPrimeSubtype_routeKPrimeRVMIndex]

theorem norm_routePSecondWildJetSignedMultiplier_le_zero
    (i : RouteKSignedPrimeIndex) :
    ‖routePSecondWildJetSignedMultiplier i‖ ≤
      routePSecondWildJetSignedApproxNumber 0 := by
  rw [norm_routePSecondWildJetSignedMultiplier]
  exact routePSecondWildJetSignedApproxNumber_antitone (Nat.zero_le _)

/-- Source-pure signed second wild jet on prime-labelled Route-P carrier. -/
def routePSecondWildJetSignedOperator :
    RouteKSignedPrimeHilbert →L[ℂ] RouteKSignedPrimeHilbert :=
  HTGeometry.ellTwoDiagonal routePSecondWildJetSignedMultiplier
    norm_routePSecondWildJetSignedMultiplier_le_zero

theorem routePSecondWildJetSignedOperator_approxNumber (n : ℕ) :
    approxNumber routePSecondWildJetSignedOperator n =
      routePSecondWildJetSignedApproxNumber n := by
  simpa [routePSecondWildJetSignedOperator] using
    HTGeometry.approxNumber_ellTwoDiagonal_reindex_eq routeKSignedPrimeEquiv
      norm_routePSecondWildJetSignedMultiplier
      routePSecondWildJetSignedApproxNumber_nonneg
      (fun {_ _} h => routePSecondWildJetSignedApproxNumber_antitone h) n

theorem tendsto_log_natCast_succ_div_log_natCast :
    Tendsto (fun n : ℕ =>
      Real.log ((n : ℝ) + 1) / Real.log (n : ℝ))
      atTop (nhds 1) := by
  have hlogTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ =>
      Real.log 2 / Real.log (n : ℝ)) atTop (nhds 0) :=
    hlogTop.const_div_atTop (Real.log 2)
  have hupper : Tendsto (fun n : ℕ =>
      1 + Real.log 2 / Real.log (n : ℝ)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hlogn : 0 < Real.log (n : ℝ) := by
      exact Real.log_pos (by exact_mod_cast hn)
    have hle : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log hnpos (by linarith)
    exact (le_div_iff₀ hlogn).2 (by simpa using hle)
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hlogn : 0 < Real.log (n : ℝ) := by
      exact Real.log_pos (by exact_mod_cast hn)
    have hbound : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
      exact_mod_cast (by omega : n + 1 ≤ 2 * n)
    have hlog : Real.log ((n : ℝ) + 1) ≤
        Real.log 2 + Real.log (n : ℝ) := by
      calc
        Real.log ((n : ℝ) + 1) ≤ Real.log (2 * (n : ℝ)) :=
          Real.log_le_log (by positivity) hbound
        _ = _ := Real.log_mul (by norm_num) hnpos.ne'
    rw [div_le_iff₀ hlogn]
    field_simp [hlogn.ne'] at hlog ⊢
    linarith

theorem tendsto_natCast_succ_div_natCast :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ))
      atTop (nhds 1) := by
  have htop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) :=
    htop.const_div_atTop 1
  have hsum := (tendsto_const_nhds (x := (1 : ℝ))).add hzero
  have hsum' : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ))
      atTop (nhds 1) := by simpa using hsum
  apply hsum'.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0]

/-- Unsigned ordered second-wild-jet profile. -/
def routePSecondWildJetPrimeApproxNumber (n : ℕ) : ℝ :=
  routePSecondWildJetPrimeWeight (nthPrimeSubtype n)

theorem eventually_routePSecondWildJetPrimeApproxNumber_eq_logSq_div :
    ∀ᶠ n : ℕ in atTop,
      routePSecondWildJetPrimeApproxNumber n =
        Real.log (((nthPrimeSubtype n : Nat.Primes) : ℝ)) ^ 2 /
          (2 * Real.pi * ((nthPrimeSubtype n : Nat.Primes) : ℝ)) := by
  have hnth : Tendsto (fun n : ℕ => Nat.nth Nat.Prime n) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_id
    exact Nat.le_nth fun hf => absurd hf Nat.infinite_setOf_prime
  have hnthReal : Tendsto (fun n : ℕ =>
      ((Nat.nth Nat.Prime n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnth
  filter_upwards [hnthReal.eventually (eventually_ge_atTop (Real.exp 2))] with n hn
  have hp : (0 : ℝ) < ((nthPrimeSubtype n : Nat.Primes) : ℝ) := by
    exact_mod_cast (nthPrimeSubtype n).property.pos
  rw [routePSecondWildJetPrimeApproxNumber,
    routePSecondWildJetPrimeWeight, max_eq_right]
  · exact routePSecondWildJetProfile_eq_log_sq_div hp
  · simpa [nthPrimeSubtype] using hn

theorem tendsto_routePSecondWildJetPrimeApproxNumber_div_model :
    Tendsto (fun n : ℕ => routePSecondWildJetPrimeApproxNumber n /
      (Real.log ((n : ℝ) + 1) /
        (2 * Real.pi * ((n : ℝ) + 1))))
      atTop (nhds 1) := by
  have hpne : ∀ᶠ n : ℕ in atTop,
      ((Nat.nth Nat.Prime n : ℕ) : ℝ) ≠ 0 := by
    filter_upwards with n
    exact_mod_cast (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n).ne_zero
  have hpnt : Tendsto (fun n : ℕ =>
      ((n : ℝ) * Real.log (n : ℝ)) /
        ((Nat.nth Nat.Prime n : ℕ) : ℝ)) atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hpne).mp nth_prime_asymp.symm
  have hcore := hpnt.mul (tendsto_log_nthPrime_div.mul tendsto_log_nthPrime_div)
  have hcoreLimit : Tendsto (fun n : ℕ =>
      (((n : ℝ) * Real.log (n : ℝ)) /
          ((Nat.nth Nat.Prime n : ℕ) : ℝ)) *
        ((Real.log ((Nat.nth Nat.Prime n : ℕ) : ℝ) / Real.log (n : ℝ)) *
          (Real.log ((Nat.nth Nat.Prime n : ℕ) : ℝ) / Real.log (n : ℝ))))
      atTop (nhds 1) := by simpa using hcore
  have hcore' : Tendsto (fun n : ℕ =>
      routePSecondWildJetPrimeApproxNumber n /
        (Real.log (n : ℝ) / (2 * Real.pi * (n : ℝ))))
      atTop (nhds 1) := by
    apply hcoreLimit.congr'
    filter_upwards [eventually_routePSecondWildJetPrimeApproxNumber_eq_logSq_div,
        eventually_gt_atTop 1] with n hraw hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
    have hlogn : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    have hp0 : ((Nat.nth Nat.Prime n : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n).ne_zero
    rw [hraw]
    simp only [nthPrimeSubtype]
    field_simp [hn0, hlogn, hp0, Real.pi_ne_zero]
  have hlogInv := tendsto_log_natCast_succ_div_log_natCast.inv₀ one_ne_zero
  have hlogInv' : Tendsto (fun n : ℕ =>
      (Real.log ((n : ℝ) + 1) / Real.log (n : ℝ))⁻¹)
      atTop (nhds 1) := by simpa using hlogInv
  have hlogScale : Tendsto (fun n : ℕ =>
      Real.log (n : ℝ) / Real.log ((n : ℝ) + 1)) atTop (nhds 1) := by
    apply hlogInv'.congr'
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hlogn : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    have hlogs : Real.log ((n : ℝ) + 1) ≠ 0 :=
      (Real.log_pos (by linarith [show (1 : ℝ) < n by exact_mod_cast hn])).ne'
    field_simp [hlogn, hlogs]
  have hscale := hlogScale.mul tendsto_natCast_succ_div_natCast
  have hscale' : Tendsto (fun n : ℕ =>
      (Real.log (n : ℝ) / Real.log ((n : ℝ) + 1)) *
        (((n : ℝ) + 1) / (n : ℝ))) atTop (nhds 1) := by
    simpa using hscale
  have hproduct := hcore'.mul hscale'
  have hproduct' : Tendsto (fun n : ℕ =>
      (routePSecondWildJetPrimeApproxNumber n /
        (Real.log (n : ℝ) / (2 * Real.pi * (n : ℝ)))) *
      ((Real.log (n : ℝ) / Real.log ((n : ℝ) + 1)) *
        (((n : ℝ) + 1) / (n : ℝ)))) atTop (nhds 1) := by
    simpa using hproduct
  apply hproduct'.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
  have hns0 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hlogn : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hlogs : Real.log ((n : ℝ) + 1) ≠ 0 :=
    (Real.log_pos (by linarith [show (1 : ℝ) < n by exact_mod_cast hn])).ne'
  field_simp [hn0, hns0, hlogn, hlogs, Real.pi_ne_zero]

/-- Signed multiplicity-two second wild jet has Xi's RVM singular-value scale. -/
theorem tendsto_routePSecondWildJetSignedApproxNumber_div_model :
    Tendsto (fun n : ℕ => routePSecondWildJetSignedApproxNumber n /
      (Real.log ((n : ℝ) + 1) /
        (Real.pi * ((n : ℝ) + 1))))
      atTop (nhds 1) := by
  have hbase := tendsto_routePSecondWildJetPrimeApproxNumber_div_model.comp
    tendsto_nat_half_atTop
  have hscale := tendsto_log_natHalf_succ_div_log_succ.mul
    tendsto_succ_div_two_mul_natHalf_succ
  have hproduct := hbase.mul hscale
  have hproduct' : Tendsto
      (fun n : ℕ =>
        (routePSecondWildJetPrimeApproxNumber (n / 2) /
          (Real.log (((n / 2 : ℕ) : ℝ) + 1) /
            (2 * Real.pi * (((n / 2 : ℕ) : ℝ) + 1)))) *
        (Real.log (((n / 2 : ℕ) + 1 : ℕ) : ℝ) /
            Real.log ((n : ℝ) + 1) *
          (((n : ℝ) + 1) /
            (2 * (((n / 2 : ℕ) + 1 : ℕ) : ℝ)))))
      atTop (nhds 1) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using hproduct
  apply hproduct'.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hlogN : 0 < Real.log ((n : ℝ) + 1) := by
    apply Real.log_pos
    exact_mod_cast Nat.succ_lt_succ (Nat.zero_lt_of_lt hn)
  have hM : 0 < (((n / 2 : ℕ) + 1 : ℕ) : ℝ) := by positivity
  have hlogM : 0 < Real.log (((n / 2 : ℕ) + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < n / 2 + 1)
  have hlogM' : Real.log (((n / 2 : ℕ) : ℝ) + 1) ≠ 0 := by
    simpa [Nat.cast_add, Nat.cast_one] using hlogM.ne'
  rw [routePSecondWildJetSignedApproxNumber,
    routePSecondWildJetPrimeApproxNumber]
  push_cast
  field_simp [hN.ne', hM.ne', hlogN.ne', hlogM.ne', hlogM', Real.pi_ne_zero]

theorem tendsto_routePSecondWildJetSignedOperator_approxNumber_div_model :
    Tendsto (fun n : ℕ => approxNumber routePSecondWildJetSignedOperator n /
      (Real.log ((n : ℝ) + 1) /
        (Real.pi * ((n : ℝ) + 1))))
      atTop (nhds 1) := by
  simpa only [routePSecondWildJetSignedOperator_approxNumber] using
    tendsto_routePSecondWildJetSignedApproxNumber_div_model

/-- Source second wild jet and actual Xi have asymptotically identical singular values. -/
theorem tendsto_routePSecondWildJetSignedOperator_approxNumber_div_xi :
    Tendsto (fun n : ℕ =>
      approxNumber routePSecondWildJetSignedOperator n /
        approxNumber xiOrderedSignedPrimeOperator n)
      atTop (nhds 1) := by
  have hquot :=
    tendsto_routePSecondWildJetSignedOperator_approxNumber_div_model.div
      tendsto_xiOrderedSignedPrimeOperator_approxNumber_div_model one_ne_zero
  change Tendsto (fun n : ℕ =>
      (approxNumber routePSecondWildJetSignedOperator n /
          (Real.log ((n : ℝ) + 1) / (Real.pi * ((n : ℝ) + 1)))) /
        (approxNumber xiOrderedSignedPrimeOperator n /
          (Real.log ((n : ℝ) + 1) / (Real.pi * ((n : ℝ) + 1)))))
      atTop (nhds (1 / 1)) at hquot
  norm_num at hquot
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hlogN : Real.log ((n : ℝ) + 1) ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    exact_mod_cast Nat.succ_lt_succ hn
  have hxi : approxNumber xiOrderedSignedPrimeOperator n ≠ 0 := by
    rw [xiOrderedSignedPrimeOperator_approxNumber]
    exact (xiOrderedSignedApproxNumber_pos n).ne'
  field_simp [hN.ne', hlogN, hxi, Real.pi_ne_zero]

/-- Exact Xi residue is already present in source-pure second wild jet. -/
theorem hasLogEnhancedWeakTraceResidue_routePSecondWildJetSignedOperator :
    HasLogEnhancedWeakTraceResidue routePSecondWildJetSignedOperator Real.pi⁻¹ := by
  have hscaled :=
    tendsto_routePSecondWildJetSignedOperator_approxNumber_div_model.div_const Real.pi
  have hfinal : Tendsto
      (logEnhancedWeakTraceProfile routePSecondWildJetSignedOperator)
      atTop (nhds (1 / Real.pi)) := by
    apply hscaled.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hlog : Real.log ((n : ℝ) + 1) ≠ 0 := by
      apply (Real.log_pos ?_).ne'
      exact_mod_cast Nat.succ_lt_succ hn
    rw [logEnhancedWeakTraceProfile]
    field_simp [hlog, Real.pi_ne_zero]
  simpa [HasLogEnhancedWeakTraceResidue, one_div] using hfinal

theorem tendsto_succ_mul_routePSecondWildJetSignedOperator_approxNumber_atTop :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      approxNumber routePSecondWildJetSignedOperator n) atTop atTop := by
  have hres := hasLogEnhancedWeakTraceResidue_routePSecondWildJetSignedOperator
  change Tendsto (logEnhancedWeakTraceProfile routePSecondWildJetSignedOperator)
    atTop (nhds Real.pi⁻¹) at hres
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hproduct := Filter.Tendsto.pos_mul_atTop (by positivity) hres hlog
  apply hproduct.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hlog0 : Real.log ((n : ℝ) + 1) ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    exact_mod_cast Nat.succ_lt_succ hn
  rw [logEnhancedWeakTraceProfile]
  field_simp [hlog0]

theorem routePSecondWildJetSignedOperator_not_memWeakSchattenClass_one :
    ¬ MemWeakSchattenClass 1 routePSecondWildJetSignedOperator := by
  rintro ⟨C, _hC, hbound⟩
  have hev :=
    tendsto_succ_mul_routePSecondWildJetSignedOperator_approxNumber_atTop.eventually
      (eventually_gt_atTop C)
  obtain ⟨n, hn⟩ := hev.exists
  have hle := hbound n
  rw [Real.rpow_one, le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at hle
  exact (not_lt_of_ge hle) (by simpa [mul_comm] using hn)

/-- The second wild jet is globally dominated by a fixed multiple of Xi's singular sequence. -/
theorem exists_routePSecondWildJetSignedOperator_approxNumber_le_mul_xi :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      approxNumber routePSecondWildJetSignedOperator n ≤
        C * approxNumber xiOrderedSignedPrimeOperator n := by
  obtain ⟨C, hC⟩ :=
    tendsto_routePSecondWildJetSignedOperator_approxNumber_div_xi.bddAbove_range
  refine ⟨max C 0, le_max_right _ _, fun n => ?_⟩
  have hratio :
      approxNumber routePSecondWildJetSignedOperator n /
          approxNumber xiOrderedSignedPrimeOperator n ≤ max C 0 :=
    (hC (Set.mem_range_self n)).trans (le_max_left _ _)
  have hxi : 0 < approxNumber xiOrderedSignedPrimeOperator n := by
    rw [xiOrderedSignedPrimeOperator_approxNumber]
    exact xiOrderedSignedApproxNumber_pos n
  exact (div_le_iff₀ hxi).mp hratio

/-- The source-pure second wild jet has square-summable singular values. -/
theorem routePSecondWildJetSignedOperator_memSchattenClass_two :
    MemSchattenClass 2 routePSecondWildJetSignedOperator := by
  obtain ⟨C, hC, hdom⟩ :=
    exists_routePSecondWildJetSignedOperator_approxNumber_le_mul_xi
  have hmajor : Summable (fun n : ℕ =>
      C ^ (2 : ℝ) * approxNumber xiOrderedSignedPrimeOperator n ^ (2 : ℝ)) :=
    xiOrderedSignedPrimeOperator_memSchattenClass_two.mul_left (C ^ (2 : ℝ))
  apply hmajor.of_nonneg_of_le
  · intro n
    exact Real.rpow_nonneg (approxNumber_nonneg _ _) 2
  · intro n
    calc
      approxNumber routePSecondWildJetSignedOperator n ^ (2 : ℝ) ≤
          (C * approxNumber xiOrderedSignedPrimeOperator n) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (approxNumber_nonneg _ _) (hdom n) (by norm_num)
      _ = C ^ (2 : ℝ) *
          approxNumber xiOrderedSignedPrimeOperator n ^ (2 : ℝ) := by
        rw [Real.mul_rpow hC (approxNumber_nonneg _ _)]

/-- The exact logarithmically enhanced endpoint class of the source-pure second wild jet. -/
theorem routePSecondWildJetSignedOperator_memLogEnhancedWeakTraceClass :
    MemLogEnhancedWeakTraceClass routePSecondWildJetSignedOperator := by
  refine ⟨routePSecondWildJetSignedOperator_memSchattenClass_two.isCompactOperator
    (by norm_num), ?_⟩
  obtain ⟨C, hC⟩ :=
    hasLogEnhancedWeakTraceResidue_routePSecondWildJetSignedOperator.bddAbove_range
  refine ⟨max C 0, le_max_right _ _, fun n => ?_⟩
  exact (hC (Set.mem_range_self n)).trans (le_max_left _ _)

/-- Source-pure second wild jet has exactly Xi's principal singular density and endpoint ideal. -/
theorem routeP_secondWildJet_xiPrincipalDensity :
    Tendsto (fun n : ℕ =>
      approxNumber routePSecondWildJetSignedOperator n /
        approxNumber xiOrderedSignedPrimeOperator n)
      atTop (nhds 1) ∧
    MemSchattenClass 2 routePSecondWildJetSignedOperator ∧
    MemLogEnhancedWeakTraceClass routePSecondWildJetSignedOperator ∧
    HasLogEnhancedWeakTraceResidue
      routePSecondWildJetSignedOperator Real.pi⁻¹ ∧
    ¬ MemWeakSchattenClass 1 routePSecondWildJetSignedOperator := by
  exact ⟨tendsto_routePSecondWildJetSignedOperator_approxNumber_div_xi,
    routePSecondWildJetSignedOperator_memSchattenClass_two,
    routePSecondWildJetSignedOperator_memLogEnhancedWeakTraceClass,
    hasLogEnhancedWeakTraceResidue_routePSecondWildJetSignedOperator,
    routePSecondWildJetSignedOperator_not_memWeakSchattenClass_one⟩

end

end RHTower
