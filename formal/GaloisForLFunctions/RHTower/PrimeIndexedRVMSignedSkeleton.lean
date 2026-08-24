import GaloisForLFunctions.RHTower.PrimeIndexedRVMSchattenInfrastructure

/-!
# Prime-indexed signed RVM skeleton

The positive smooth RVM reciprocal diagonal is doubled with opposite sign on
two prime-marked sectors.  Its approximation numbers are computed exactly,
including multiplicity two, and its sharp Schatten boundary and singular-value
asymptotic are proved.
-/

open scoped BigOperators InnerProductSpace Nat.Prime
open Filter

namespace RHTower

noncomputable section

abbrev RouteKSignedPrimeIndex := Sum Nat.Primes Nat.Primes

def routeKSignedPrimeNatIndex : RouteKSignedPrimeIndex → ℕ
  | Sum.inl p => 2 * routeKPrimeRVMIndex p
  | Sum.inr p => 2 * routeKPrimeRVMIndex p + 1

theorem routeKSignedPrimeNatIndex_injective :
    Function.Injective routeKSignedPrimeNatIndex := by
  intro i j hij
  cases i with
  | inl p =>
      cases j with
      | inl q =>
          congr 1
          apply routeKPrimeRVMIndex_injective
          simp only [routeKSignedPrimeNatIndex] at hij
          omega
      | inr q =>
          simp only [routeKSignedPrimeNatIndex] at hij
          omega
  | inr p =>
      cases j with
      | inl q =>
          simp only [routeKSignedPrimeNatIndex] at hij
          omega
      | inr q =>
          congr 1
          apply routeKPrimeRVMIndex_injective
          simp only [routeKSignedPrimeNatIndex] at hij
          omega

theorem routeKSignedPrimeNatIndex_surjective :
    Function.Surjective routeKSignedPrimeNatIndex := by
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · refine ⟨Sum.inl (nthPrimeSubtype (n / 2)), ?_⟩
    rw [routeKSignedPrimeNatIndex, routeKPrimeRVMIndex_nthPrimeSubtype]
    exact Nat.two_mul_div_two_of_even (Nat.even_iff.mpr heven)
  · refine ⟨Sum.inr (nthPrimeSubtype (n / 2)), ?_⟩
    rw [routeKSignedPrimeNatIndex, routeKPrimeRVMIndex_nthPrimeSubtype]
    have hdecomp := Nat.mod_add_div n 2
    omega

def routeKSignedPrimeEquiv : ℕ ≃ RouteKSignedPrimeIndex :=
  (Equiv.ofBijective routeKSignedPrimeNatIndex
    ⟨routeKSignedPrimeNatIndex_injective,
      routeKSignedPrimeNatIndex_surjective⟩).symm

theorem routeKSignedPrimeEquiv_symm_apply (i : RouteKSignedPrimeIndex) :
    routeKSignedPrimeEquiv.symm i = routeKSignedPrimeNatIndex i := by
  rfl

def routeKRVMSignedApproxNumber (n : ℕ) : ℝ :=
  (routeKRVMQuantile (n / 2))⁻¹

theorem routeKRVMSignedApproxNumber_pos (n : ℕ) :
    0 < routeKRVMSignedApproxNumber n := by
  exact inv_pos.mpr
    (routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile (n / 2)))

theorem routeKRVMSignedApproxNumber_antitone :
    Antitone routeKRVMSignedApproxNumber := by
  intro i j hij
  exact routeKRVMQuantile_reciprocal_antitone
    (Nat.div_le_div_right hij)

def routeKSignedPrimeRVMMultiplier : RouteKSignedPrimeIndex → ℂ
  | Sum.inl p => (routeKPrimeRVMReciprocal p : ℂ)
  | Sum.inr p => -(routeKPrimeRVMReciprocal p : ℂ)

theorem norm_routeKSignedPrimeRVMMultiplier (i : RouteKSignedPrimeIndex) :
    ‖routeKSignedPrimeRVMMultiplier i‖ =
      routeKRVMSignedApproxNumber (routeKSignedPrimeEquiv.symm i) := by
  cases i with
  | inl p =>
      rw [routeKSignedPrimeRVMMultiplier, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (routeKPrimeRVMReciprocal_pos p)]
      simp [routeKRVMSignedApproxNumber,
        routeKSignedPrimeEquiv_symm_apply, routeKSignedPrimeNatIndex,
        routeKPrimeRVMReciprocal]
  | inr p =>
      rw [routeKSignedPrimeRVMMultiplier, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (routeKPrimeRVMReciprocal_pos p)]
      simp [routeKRVMSignedApproxNumber,
        routeKSignedPrimeEquiv_symm_apply, routeKSignedPrimeNatIndex,
        routeKPrimeRVMReciprocal]
      congr 1
      omega

theorem norm_routeKSignedPrimeRVMMultiplier_le_zero
    (i : RouteKSignedPrimeIndex) :
    ‖routeKSignedPrimeRVMMultiplier i‖ ≤ routeKRVMSignedApproxNumber 0 := by
  rw [norm_routeKSignedPrimeRVMMultiplier]
  exact routeKRVMSignedApproxNumber_antitone (Nat.zero_le _)

abbrev RouteKSignedPrimeHilbert := HTGeometry.IndexedEllTwo RouteKSignedPrimeIndex

def routeKSignedPrimeRVMOperator :
    RouteKSignedPrimeHilbert →L[ℂ] RouteKSignedPrimeHilbert :=
  HTGeometry.ellTwoDiagonal routeKSignedPrimeRVMMultiplier
    norm_routeKSignedPrimeRVMMultiplier_le_zero

theorem routeKSignedPrimeRVMOperator_basis_inl (p : Nat.Primes) :
    routeKSignedPrimeRVMOperator
        (HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex (Sum.inl p)) =
      (routeKPrimeRVMReciprocal p : ℂ) •
        HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex (Sum.inl p) := by
  simpa [routeKSignedPrimeRVMOperator, routeKSignedPrimeRVMMultiplier] using
    HTGeometry.ellTwoDiagonal_coordinateBasis routeKSignedPrimeRVMMultiplier
      norm_routeKSignedPrimeRVMMultiplier_le_zero (Sum.inl p)

theorem routeKSignedPrimeRVMOperator_basis_inr (p : Nat.Primes) :
    routeKSignedPrimeRVMOperator
        (HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex (Sum.inr p)) =
      -(routeKPrimeRVMReciprocal p : ℂ) •
        HTGeometry.ellTwoCoordinateBasis RouteKSignedPrimeIndex (Sum.inr p) := by
  simpa [routeKSignedPrimeRVMOperator, routeKSignedPrimeRVMMultiplier] using
    HTGeometry.ellTwoDiagonal_coordinateBasis routeKSignedPrimeRVMMultiplier
      norm_routeKSignedPrimeRVMMultiplier_le_zero (Sum.inr p)

theorem routeKSignedPrimeRVMOperator_approxNumber (n : ℕ) :
    approxNumber routeKSignedPrimeRVMOperator n =
      routeKRVMSignedApproxNumber n := by
  simpa [routeKSignedPrimeRVMOperator] using
    HTGeometry.approxNumber_ellTwoDiagonal_reindex_eq routeKSignedPrimeEquiv
      norm_routeKSignedPrimeRVMMultiplier
      (fun n => (routeKRVMSignedApproxNumber_pos n).le)
      (fun {_ _} h => routeKRVMSignedApproxNumber_antitone h) n

theorem routeKSignedPrimeRVMOperator_selfAdjoint :
    ContinuousLinearMap.adjoint routeKSignedPrimeRVMOperator =
      routeKSignedPrimeRVMOperator := by
  rw [routeKSignedPrimeRVMOperator, HTGeometry.adjoint_ellTwoDiagonal]
  ext f i
  rw [HTGeometry.ellTwoDiagonal_apply, HTGeometry.ellTwoDiagonal_apply]
  cases i <;> simp [routeKSignedPrimeRVMMultiplier]

theorem summable_routeKRVMSignedApproxNumber_rpow {q : ℝ} (hq : 1 < q) :
    Summable (fun n : ℕ => routeKRVMSignedApproxNumber n ^ q) := by
  have hprime := summable_routeKPrimeRVMReciprocal_rpow hq
  have hindex : Summable (fun i : RouteKSignedPrimeIndex =>
      ‖routeKSignedPrimeRVMMultiplier i‖ ^ q) := by
    apply Summable.sum
    · simpa [Function.comp_def, routeKSignedPrimeRVMMultiplier,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (routeKPrimeRVMReciprocal_pos _)] using hprime
    · simpa [Function.comp_def, routeKSignedPrimeRVMMultiplier,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (routeKPrimeRVMReciprocal_pos _)] using hprime
  have hnat := routeKSignedPrimeEquiv.summable_iff.mpr hindex
  exact hnat.congr fun n => by
    rw [Function.comp_apply, norm_routeKSignedPrimeRVMMultiplier,
      routeKSignedPrimeEquiv.symm_apply_apply]

theorem not_summable_routeKRVMSignedApproxNumber :
    ¬ Summable routeKRVMSignedApproxNumber := by
  intro hsum
  apply not_summable_routeKRVMQuantile_reciprocal
  have heven : Summable (fun n : ℕ => routeKRVMSignedApproxNumber (2 * n)) :=
    hsum.comp_injective (fun {_ _} h => by omega)
  simpa [routeKRVMSignedApproxNumber] using heven

theorem routeKSignedPrimeRVMOperator_memSchattenClass
    {q : ℝ} (hq : 1 < q) :
    MemSchattenClass q routeKSignedPrimeRVMOperator := by
  simpa only [MemSchattenClass,
    routeKSignedPrimeRVMOperator_approxNumber] using
    summable_routeKRVMSignedApproxNumber_rpow hq

theorem routeKSignedPrimeRVMOperator_not_memSchattenClass_one :
    ¬ MemSchattenClass 1 routeKSignedPrimeRVMOperator := by
  simpa only [MemSchattenClass, routeKSignedPrimeRVMOperator_approxNumber,
    Real.rpow_one] using not_summable_routeKRVMSignedApproxNumber

theorem routeKSignedPrimeRVMOperator_memSchattenClass_two :
    MemSchattenClass 2 routeKSignedPrimeRVMOperator :=
  routeKSignedPrimeRVMOperator_memSchattenClass (by norm_num)

theorem routeKSignedPrimeRVMOperator_approxNumber_even (n : ℕ) :
    approxNumber routeKSignedPrimeRVMOperator (2 * n) =
      (routeKRVMQuantile n)⁻¹ := by
  rw [routeKSignedPrimeRVMOperator_approxNumber]
  simp [routeKRVMSignedApproxNumber]

theorem routeKSignedPrimeRVMOperator_approxNumber_odd (n : ℕ) :
    approxNumber routeKSignedPrimeRVMOperator (2 * n + 1) =
      (routeKRVMQuantile n)⁻¹ := by
  rw [routeKSignedPrimeRVMOperator_approxNumber]
  simp [routeKRVMSignedApproxNumber]
  congr 1
  omega

theorem tendsto_nat_half_atTop :
    Tendsto (fun n : ℕ => n / 2) atTop atTop := by
  rw [tendsto_atTop]
  intro N
  filter_upwards [eventually_ge_atTop (2 * N)] with n hn
  omega

theorem tendsto_log_natHalf_succ_div_log_succ :
    Tendsto (fun n : ℕ =>
      Real.log ((n / 2 : ℕ) + 1 : ℕ) / Real.log ((n : ℝ) + 1))
      atTop (nhds 1) := by
  have hNtop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlogNtop : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hNtop
  have hzero := hlogNtop.const_div_atTop (Real.log 2)
  have hlower : Tendsto (fun n : ℕ =>
      1 - Real.log 2 / Real.log ((n : ℝ) + 1)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hN : 0 < (n : ℝ) + 1 := by positivity
    have hlogN : 0 < Real.log ((n : ℝ) + 1) := by
      apply Real.log_pos
      exact_mod_cast Nat.succ_lt_succ (Nat.zero_lt_of_lt hn)
    have hM : 0 < (((n / 2 : ℕ) + 1 : ℕ) : ℝ) := by positivity
    have hNM : (n : ℝ) + 1 ≤
        2 * (((n / 2 : ℕ) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n + 1 ≤ 2 * (n / 2 + 1))
    have hlog : Real.log ((n : ℝ) + 1) ≤
        Real.log 2 + Real.log (((n / 2 : ℕ) + 1 : ℕ) : ℝ) := by
      calc
        Real.log ((n : ℝ) + 1) ≤
            Real.log (2 * (((n / 2 : ℕ) + 1 : ℕ) : ℝ)) :=
          Real.log_le_log hN hNM
        _ = _ := Real.log_mul (by norm_num) hM.ne'
    rw [le_div_iff₀ hlogN]
    field_simp [hlogN.ne'] at hlog ⊢
    linarith
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hlogN : 0 < Real.log ((n : ℝ) + 1) := by
      apply Real.log_pos
      exact_mod_cast Nat.succ_lt_succ (Nat.zero_lt_of_lt hn)
    have hM : 0 < (((n / 2 : ℕ) + 1 : ℕ) : ℝ) := by positivity
    have hMN : (((n / 2 : ℕ) + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast (by omega : n / 2 + 1 ≤ n + 1)
    have hlog := Real.log_le_log hM hMN
    exact (div_le_one hlogN).2 hlog

theorem tendsto_succ_div_two_mul_natHalf_succ :
    Tendsto (fun n : ℕ =>
      ((n : ℝ) + 1) / (2 * (((n / 2 : ℕ) + 1 : ℕ) : ℝ)))
      atTop (nhds 1) := by
  have hNtop : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2))
      atTop (nhds 0) := hNtop.const_div_atTop 1
  have hlower : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hsmall
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower tendsto_const_nhds ?_ ?_
  · filter_upwards [] with n
    have hN2 : 0 < (n : ℝ) + 2 := by positivity
    have hM : 0 < (2 * (((n / 2 : ℕ) + 1 : ℕ) : ℝ)) := by positivity
    have hbounds : n + 1 ≤ 2 * (n / 2 + 1) ∧
        2 * (n / 2 + 1) ≤ n + 2 := by omega
    have hcast : (2 * (((n / 2 : ℕ) + 1 : ℕ) : ℝ)) ≤ (n : ℝ) + 2 := by
      exact_mod_cast hbounds.2
    have hfac : 0 ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2) := by positivity
    rw [le_div_iff₀ hM]
    calc
      (1 - 1 / ((n : ℝ) + 2)) *
          (2 * (((n / 2 : ℕ) + 1 : ℕ) : ℝ)) =
          (((n : ℝ) + 1) / ((n : ℝ) + 2)) *
            (2 * (((n / 2 : ℕ) + 1 : ℕ) : ℝ)) := by
        field_simp [hN2.ne']
        ring
      _ ≤ (((n : ℝ) + 1) / ((n : ℝ) + 2)) * ((n : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hcast hfac
      _ = (n : ℝ) + 1 := by field_simp [hN2.ne']
  · filter_upwards [] with n
    have hM : 0 < (2 * (((n / 2 : ℕ) + 1 : ℕ) : ℝ)) := by positivity
    rw [div_le_one hM]
    exact_mod_cast (by omega : n + 1 ≤ 2 * (n / 2 + 1))

theorem tendsto_routeKRVMSignedApproxNumber_div_model :
    Tendsto (fun n : ℕ => routeKRVMSignedApproxNumber n /
      (Real.log ((n : ℝ) + 1) / (Real.pi * ((n : ℝ) + 1))))
      atTop (nhds 1) := by
  have hbase := tendsto_routeKRVMQuantile_reciprocal_div_rvmModel.comp
    tendsto_nat_half_atTop
  have hscale := tendsto_log_natHalf_succ_div_log_succ.mul
    tendsto_succ_div_two_mul_natHalf_succ
  have hproduct := hbase.mul hscale
  have hproduct' : Tendsto
      (fun x =>
        ((fun m : ℕ => (routeKRVMQuantile m)⁻¹ /
          (Real.log ((m : ℝ) + 1) /
            (2 * Real.pi * ((m : ℝ) + 1)))) (x / 2)) *
          (Real.log (((x / 2 : ℕ) + 1 : ℕ) : ℝ) /
            Real.log ((x : ℝ) + 1) *
            (((x : ℝ) + 1) /
              (2 * (((x / 2 : ℕ) + 1 : ℕ) : ℝ))))) atTop (nhds 1) := by
    simpa [Function.comp_def] using hproduct
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
  have hlogM' : 0 < Real.log (1 + ((n / 2 : ℕ) : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one, add_comm] using hlogM
  have hlogM'' : Real.log (((n / 2 : ℕ) : ℝ) + 1) ≠ 0 := by
    simpa [Nat.cast_add, Nat.cast_one] using hlogM.ne'
  have hT : 0 < routeKRVMQuantile (n / 2) :=
    routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile (n / 2))
  rw [routeKRVMSignedApproxNumber]
  push_cast
  field_simp [hN.ne', hM.ne', hlogN.ne',
    hlogM.ne', hlogM'.ne', hlogM'', hT.ne', Real.pi_ne_zero]

theorem tendsto_routeKSignedPrimeRVMOperator_approxNumber_div_model :
    Tendsto (fun n : ℕ => approxNumber routeKSignedPrimeRVMOperator n /
      (Real.log ((n : ℝ) + 1) / (Real.pi * ((n : ℝ) + 1))))
      atTop (nhds 1) := by
  simpa only [routeKSignedPrimeRVMOperator_approxNumber] using
    tendsto_routeKRVMSignedApproxNumber_div_model

def routeKPrimeRVMOperatorPrimeCutoff (N : ℕ) :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  HTGeometry.ellTwoDiagonal
    (HTGeometry.equivTruncMultiplier nthPrimeEquiv
      (fun p : Nat.Primes => (routeKPrimeRVMReciprocal p : ℂ))
      (Nat.primeCounting' N))
    (HTGeometry.norm_equivTruncMultiplier_le nthPrimeEquiv
      norm_routeKPrimeRVMReciprocal_le_zero (Nat.primeCounting' N))

theorem finrank_range_routeKPrimeRVMOperatorPrimeCutoff (N : ℕ) :
    Module.finrank ℂ
      (LinearMap.range (routeKPrimeRVMOperatorPrimeCutoff N).toLinearMap) =
        Nat.primeCounting' N := by
  unfold routeKPrimeRVMOperatorPrimeCutoff
  convert HTGeometry.finrank_range_ellTwoDiagonal_equivTrunc nthPrimeEquiv
      (fun p : Nat.Primes => (routeKPrimeRVMReciprocal p : ℂ))
      norm_routeKPrimeRVMReciprocal_le_zero (Nat.primeCounting' N)
      (fun k => by
        exact_mod_cast (routeKPrimeRVMReciprocal_pos (nthPrimeEquiv k)).ne') using 1

def routeKSignedPrimeRVMOperatorPrimeCutoff (N : ℕ) :
    RouteKSignedPrimeHilbert →L[ℂ] RouteKSignedPrimeHilbert :=
  HTGeometry.ellTwoDiagonal
    (HTGeometry.equivTruncMultiplier routeKSignedPrimeEquiv
      routeKSignedPrimeRVMMultiplier (2 * Nat.primeCounting' N))
    (HTGeometry.norm_equivTruncMultiplier_le routeKSignedPrimeEquiv
      norm_routeKSignedPrimeRVMMultiplier_le_zero
      (2 * Nat.primeCounting' N))

theorem finrank_range_routeKSignedPrimeRVMOperatorPrimeCutoff (N : ℕ) :
    Module.finrank ℂ
      (LinearMap.range
        (routeKSignedPrimeRVMOperatorPrimeCutoff N).toLinearMap) =
      2 * Nat.primeCounting' N := by
  unfold routeKSignedPrimeRVMOperatorPrimeCutoff
  convert HTGeometry.finrank_range_ellTwoDiagonal_equivTrunc routeKSignedPrimeEquiv
      routeKSignedPrimeRVMMultiplier
      norm_routeKSignedPrimeRVMMultiplier_le_zero
      (2 * Nat.primeCounting' N)
      (fun k => by
        cases h : routeKSignedPrimeEquiv k with
        | inl p =>
            simp [routeKSignedPrimeRVMMultiplier,
              (routeKPrimeRVMReciprocal_pos p).ne']
        | inr p =>
            simp [routeKSignedPrimeRVMMultiplier,
              (routeKPrimeRVMReciprocal_pos p).ne']) using 1

end

end RHTower
