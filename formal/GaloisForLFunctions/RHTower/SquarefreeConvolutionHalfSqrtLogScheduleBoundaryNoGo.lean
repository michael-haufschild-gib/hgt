import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfSqrtLogSchedule

/-!
# Sharper boundary obstruction to the square-root logarithmic schedule

At `s = 6/11`, the positive-half exterior binomial terms eventually grow by at least `5/2`
per degree.  Combined with the factor-two lower growth already proved for the negative-half
factor, this gives

`5^(M-24) <= ‖poleFactorSqrtApprox M (6/11)‖`.

Pointwise boundedness of any cofinal scheduled product consequently imposes an eventual prime
ceiling with base five.  Bertrand primes in `(16^m, 2*16^m]` violate that ceiling for
`kappa(N) = log_4(sqrt N + 1) + 6`, since `5^11 > 2*16^6`.  Thus the schedule which survived
the earlier base-four estimate is still not locally bounded.  A viable raw schedule must grow
strictly more slowly.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

theorem boundaryHalfExteriorMagnitude_growth_five_halves {k : ℕ} (hk : 23 ≤ k) :
    (5 / 2 : ℝ) * boundaryHalfExteriorMagnitude k ≤
      boundaryHalfExteriorMagnitude (k + 1) := by
  have hrec := GaloisForLFunctions.choose_succ_field (1 / 2 : ℝ) k
  have hkreal : (23 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hchoose : Ring.choose (1 / 2 : ℝ) (k + 1) =
      Ring.choose (1 / 2 : ℝ) k * ((1 / 2 : ℝ) - k) / ((k : ℝ) + 1) := by
    rw [eq_div_iff (ne_of_gt hk1)]
    simpa [mul_comm] using hrec
  have hterm : boundaryHalfExteriorTerm (k + 1) =
      boundaryHalfExteriorTerm k *
        ((8 / 3 : ℝ) * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1)) := by
    unfold boundaryHalfExteriorTerm
    rw [hchoose, pow_succ]
    ring
  have hratio : (5 / 2 : ℝ) ≤
      (8 / 3 : ℝ) * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1) := by
    rw [le_div_iff₀ hk1]
    nlinarith
  rw [boundaryHalfExteriorMagnitude, boundaryHalfExteriorMagnitude, hterm]
  have htneg := boundaryHalfExteriorTerm_neg
    (le_trans (by norm_num : 1 ≤ 23) hk)
  have hmul := mul_le_mul_of_nonneg_left hratio (neg_nonneg.mpr htneg.le)
  calc
    (5 / 2 : ℝ) * -boundaryHalfExteriorTerm k ≤
        (8 / 3 * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1)) *
          -boundaryHalfExteriorTerm k := by simpa [mul_comm] using hmul
    _ = -(boundaryHalfExteriorTerm k *
        (8 / 3 * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1))) := by ring

theorem boundaryHalfExteriorMagnitude_ge_five_halves_pow
    {k : ℕ} (hk : 23 ≤ k) :
    (5 / 2 : ℝ) ^ (k - 23) ≤ boundaryHalfExteriorMagnitude k := by
  induction k, hk using Nat.le_induction with
  | base =>
      have htwo := boundaryHalfExteriorMagnitude_ge_two_pow (k := 23) (by norm_num)
      norm_num at htwo ⊢
      linarith
  | succ k hk ih =>
      have hexp : k + 1 - 23 = (k - 23) + 1 := by omega
      rw [hexp, pow_succ]
      calc
        (5 / 2 : ℝ) ^ (k - 23) * (5 / 2) ≤
            boundaryHalfExteriorMagnitude k * (5 / 2) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = (5 / 2) * boundaryHalfExteriorMagnitude k := by ring
        _ ≤ boundaryHalfExteriorMagnitude (k + 1) :=
          boundaryHalfExteriorMagnitude_growth_five_halves hk

theorem norm_boundaryHalfExteriorPartialSum_ge_five_halves_pow
    {N : ℕ} (hN : 24 ≤ N) :
    (5 / 2 : ℝ) ^ (N - 24) ≤
      ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-8 / 3 : ℂ)‖ := by
  rw [complex_boundaryHalfExteriorPartialSum_eq, Complex.norm_real, Real.norm_eq_abs]
  have hsumNonpos : boundaryHalfExteriorSum N ≤ 0 :=
    le_trans (boundaryHalfExteriorSum_le_neg_quarter (by omega)) (by norm_num)
  rw [abs_of_nonpos hsumNonpos]
  have hsplit : boundaryHalfExteriorSum N =
      boundaryHalfExteriorSum (N - 1) + boundaryHalfExteriorTerm (N - 1) := by
    conv_lhs => rw [show N = (N - 1) + 1 by omega,
      boundaryHalfExteriorSum, Finset.sum_range_succ, ← boundaryHalfExteriorSum]
  have hprefix : boundaryHalfExteriorSum (N - 1) ≤ 0 :=
    le_trans (boundaryHalfExteriorSum_le_neg_quarter (by omega)) (by norm_num)
  have hlast := boundaryHalfExteriorMagnitude_ge_five_halves_pow
    (show 23 ≤ N - 1 by omega)
  have hexp : N - 1 - 23 = N - 24 := by omega
  rw [hexp, boundaryHalfExteriorMagnitude] at hlast
  rw [hsplit]
  nlinarith

theorem two_pow_degree_le_norm_boundaryNegHalfExteriorPartialSum
    {N : ℕ} (hN : 24 ≤ N) :
    (2 : ℝ) ^ (N - 24) ≤
      ‖(binomialSeries ℂ (-1 / 2 : ℂ)).partialSum N (8 / 3 : ℂ)‖ := by
  have hneg := norm_boundaryNegHalfExteriorPartialSum_ge_two_pow (N := N) (by omega)
  have hscale : (2 : ℝ) ^ (N - 24) ≤ (2 : ℝ) ^ (N - 2) / 5 := by
    rw [show N - 2 = (N - 24) + 22 by omega, pow_add]
    have hnonneg : 0 ≤ (2 : ℝ) ^ (N - 24) := by positivity
    nlinarith [show (5 : ℝ) ≤ 2 ^ (22 : ℕ) by norm_num]
  exact hscale.trans hneg

theorem boundary_five_pow_eq_two_factor_pow {N : ℕ} :
    (5 : ℝ) ^ (N - 24) =
      (5 / 2 : ℝ) ^ (N - 24) * (2 : ℝ) ^ (N - 24) := by
  rw [← mul_pow]
  norm_num

theorem norm_poleFactorSqrtApprox_boundaryExteriorPoint_five_pow
    {N : ℕ} (hN : 24 ≤ N) :
    (5 : ℝ) ^ (N - 24) ≤ ‖poleFactorSqrtApprox N boundaryExteriorPoint‖ := by
  have hhalf := norm_boundaryHalfExteriorPartialSum_ge_five_halves_pow hN
  have hneg := two_pow_degree_le_norm_boundaryNegHalfExteriorPartialSum hN
  have hhalf' : (5 / 2 : ℝ) ^ (N - 24) ≤
      ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-(8 / 3) : ℂ)‖ := by
    simpa only [neg_div] using hhalf
  have hneg' : (2 : ℝ) ^ (N - 24) ≤
      ‖(binomialSeries ℂ (-(1 / 2) : ℂ)).partialSum N (8 / 3 : ℂ)‖ := by
    simpa only [neg_div] using hneg
  rw [poleFactorSqrtApprox, poleFactorCayley_boundaryExteriorPoint]
  norm_num only [neg_div, neg_neg]
  rw [norm_mul, boundary_five_pow_eq_two_factor_pow]
  exact mul_le_mul hhalf' hneg' (by positivity) (by positivity)

theorem boundaryFiveCayleySchedule_prime_scale_ceiling
    (kappa : ℕ → ℕ) (hkappa : Tendsto kappa atTop atTop)
    (hbound : ∃ C : ℝ, ∀ N,
      ‖poleClearedFirstTraceScheduledApprox kappa N boundaryExteriorPoint‖ ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, ∀ p : ℕ, N₀ ≤ p → p.Prime →
      (5 : ℝ) ^ min (kappa p - 24) (kappa (p + 1) - 24) ≤
        B * (p : ℝ) ^ (6 / 11 : ℝ) := by
  obtain ⟨C, hC⟩ := hbound
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hkappa.eventually (eventually_ge_atTop 24))
  let K : ℝ := C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpartial (N : ℕ) (hN : N₀ ≤ N) :
      (5 : ℝ) ^ (kappa N - 24) *
          ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤ K := by
    have hfactor := norm_poleFactorSqrtApprox_boundaryExteriorPoint_five_pow (hN₀ N hN)
    have hdetpos : 0 < ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ :=
      norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
    have hsource := hC N
    have hprod :
        ‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ *
            ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤
          C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ := by
      rw [poleClearedFirstTraceScheduledApprox, norm_div, norm_mul] at hsource
      exact (div_le_iff₀ hdetpos).mp hsource
    exact le_trans (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)) hprod
  refine ⟨4 * K, by positivity, N₀, ?_⟩
  intro p hpN hp
  let e : ℕ := min (kappa p - 24) (kappa (p + 1) - 24)
  have hpowleft : (5 : ℝ) ^ e ≤ (5 : ℝ) ^ (kappa p - 24) :=
    pow_le_pow_right₀ (by norm_num) (min_le_left _ _)
  have hpowright : (5 : ℝ) ^ e ≤ (5 : ℝ) ^ (kappa (p + 1) - 24) :=
    pow_le_pow_right₀ (by norm_num) (min_le_right _ _)
  have hpbound :
      (5 : ℝ) ^ e * ‖squarefreeHalfDirichletPartialSum p boundaryExteriorPoint‖ ≤ K :=
    le_trans (mul_le_mul_of_nonneg_right hpowleft (norm_nonneg _)) (hpartial p hpN)
  have hsuccbound :
      (5 : ℝ) ^ e *
          ‖squarefreeHalfDirichletPartialSum (p + 1) boundaryExteriorPoint‖ ≤ K :=
    le_trans (mul_le_mul_of_nonneg_right hpowright (norm_nonneg _))
      (hpartial (p + 1) (hpN.trans (Nat.le_succ p)))
  have hsucc := squarefreeHalfDirichletPartialSum_succ p boundaryExteriorPoint
  have htermEq :
      LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint p =
        squarefreeHalfDirichletPartialSum (p + 1) boundaryExteriorPoint -
          squarefreeHalfDirichletPartialSum p boundaryExteriorPoint := by
    rw [hsucc]
    ring
  have htri :
      ‖LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint p‖ ≤
        ‖squarefreeHalfDirichletPartialSum (p + 1) boundaryExteriorPoint‖ +
          ‖squarefreeHalfDirichletPartialSum p boundaryExteriorPoint‖ := by
    rw [htermEq]
    exact norm_sub_le _ _
  have htermUpper :
      (5 : ℝ) ^ e * ‖LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint p‖ ≤
        2 * K := by
    calc
      (5 : ℝ) ^ e * ‖LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint p‖ ≤
          (5 : ℝ) ^ e *
            (‖squarefreeHalfDirichletPartialSum (p + 1) boundaryExteriorPoint‖ +
              ‖squarefreeHalfDirichletPartialSum p boundaryExteriorPoint‖) :=
        mul_le_mul_of_nonneg_left htri (pow_nonneg (by norm_num) _)
      _ = (5 : ℝ) ^ e *
            ‖squarefreeHalfDirichletPartialSum (p + 1) boundaryExteriorPoint‖ +
          (5 : ℝ) ^ e * ‖squarefreeHalfDirichletPartialSum p boundaryExteriorPoint‖ := by ring
      _ ≤ K + K := add_le_add hsuccbound hpbound
      _ = 2 * K := by ring
  rw [norm_squarefreeConvolutionHalf_term_prime_boundaryExteriorPoint p hp] at htermUpper
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpowpos : 0 < (p : ℝ) ^ (6 / 11 : ℝ) := Real.rpow_pos_of_pos hp0 _
  have hdiv : ((5 : ℝ) ^ e / 2) / (p : ℝ) ^ (6 / 11 : ℝ) ≤ 2 * K := by
    calc
      ((5 : ℝ) ^ e / 2) / (p : ℝ) ^ (6 / 11 : ℝ) =
          (5 : ℝ) ^ e * ((1 / 2 : ℝ) / (p : ℝ) ^ (6 / 11 : ℝ)) := by ring
      _ ≤ 2 * K := htermUpper
  have hmul := (div_le_iff₀ hpowpos).mp hdiv
  change (5 : ℝ) ^ e ≤ (4 * K) * (p : ℝ) ^ (6 / 11 : ℝ)
  nlinarith

private theorem rpow_six_elevenths_pow_eleven {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (6 / 11 : ℝ)) ^ (11 : ℕ) = x ^ (6 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem not_sqrtLogarithmicCayleySchedule_boundaryFivePrimeCeiling :
    ¬ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, ∀ p : ℕ, N₀ ≤ p → p.Prime →
      (5 : ℝ) ^
          min (sqrtLogarithmicCayleySchedule p - 24)
            (sqrtLogarithmicCayleySchedule (p + 1) - 24) ≤
        B * (p : ℝ) ^ (6 / 11 : ℝ) := by
  rintro ⟨B, hB, N₀, hceiling⟩
  let C : ℝ := B ^ (11 : ℕ) * 64 * 5 ^ (18 * 11 : ℕ)
  obtain ⟨mPow, hmPow⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num)).eventually_gt_atTop C)
  obtain ⟨mScale, hmScale⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt (r := (16 : ℝ)) (by norm_num)).eventually_ge_atTop (N₀ : ℝ))
  let m := max 18 (max mPow mScale)
  have hm18 : 18 ≤ m := le_max_left _ _
  have hmPowLe : mPow ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
  have hmScaleLe : mScale ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
  have hClarge : C < (2 : ℝ) ^ m := hmPow m hmPowLe
  have hN₀real : (N₀ : ℝ) ≤ (16 : ℝ) ^ m := hmScale m hmScaleLe
  have hN₀nat : N₀ ≤ 16 ^ m := by exact_mod_cast hN₀real
  have hfourSq : (4 ^ m) ^ 2 = 16 ^ m := by
    calc
      (4 ^ m) ^ 2 = 4 ^ (m * 2) := (pow_mul 4 m 2).symm
      _ = 4 ^ (2 * m) := by rw [Nat.mul_comm]
      _ = (4 ^ 2) ^ m := pow_mul 4 2 m
      _ = 16 ^ m := by norm_num
  obtain ⟨p, hp, hnp, hpupper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (16 ^ m) (by positivity)
  have hpN₀ : N₀ ≤ p := hN₀nat.trans hnp.le
  have hsqrtp : 4 ^ m ≤ Nat.sqrt p := by
    apply Nat.le_sqrt.mpr
    have hsquare := hnp.le
    rw [← hfourSq] at hsquare
    simpa [pow_two] using hsquare
  have hsqrtpsucc : 4 ^ m ≤ Nat.sqrt (p + 1) := by
    apply Nat.le_sqrt.mpr
    have hp1 : 16 ^ m ≤ p + 1 := hnp.le.trans (Nat.le_succ p)
    rw [← hfourSq] at hp1
    simpa [pow_two] using hp1
  have hlogp : m ≤ Nat.log 4 (Nat.sqrt p + 1) :=
    Nat.le_log_of_pow_le (by norm_num) (hsqrtp.trans (Nat.le_add_right _ 1))
  have hlogpsucc : m ≤ Nat.log 4 (Nat.sqrt (p + 1) + 1) :=
    Nat.le_log_of_pow_le (by norm_num) (hsqrtpsucc.trans (Nat.le_add_right _ 1))
  let e : ℕ := min (sqrtLogarithmicCayleySchedule p - 24)
    (sqrtLogarithmicCayleySchedule (p + 1) - 24)
  have he : m - 18 ≤ e := by
    apply le_min
    · simp only [sqrtLogarithmicCayleySchedule]
      omega
    · simp only [sqrtLogarithmicCayleySchedule]
      omega
  have hleft : (5 : ℝ) ^ ((m - 18) * 11) ≤ (5 : ℝ) ^ (e * 11) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right 11 he)
  have hceil := hceiling p hpN₀ hp
  change (5 : ℝ) ^ e ≤ B * (p : ℝ) ^ (6 / 11 : ℝ) at hceil
  have hceil11 := pow_le_pow_left₀ (pow_nonneg (by norm_num) e) hceil 11
  have hpnonneg : (0 : ℝ) ≤ p := by positivity
  rw [← pow_mul, mul_pow, rpow_six_elevenths_pow_eleven hpnonneg] at hceil11
  have hpupperReal : (p : ℝ) ≤ 2 * (16 : ℝ) ^ m := by exact_mod_cast hpupper
  have hpupperSix : (p : ℝ) ^ (6 : ℕ) ≤
      (2 * (16 : ℝ) ^ m) ^ (6 : ℕ) :=
    pow_le_pow_left₀ hpnonneg hpupperReal 6
  have hbase : (2 : ℝ) * 16 ^ (6 : ℕ) ≤ 5 ^ (11 : ℕ) := by norm_num
  have hbasepow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * 16 ^ (6 : ℕ)) hbase m
  rw [mul_pow, ← pow_mul, ← pow_mul] at hbasepow
  have hscalePos : 0 < (16 : ℝ) ^ (6 * m) := by positivity
  have hgrow : C * (16 : ℝ) ^ (6 * m) < (5 : ℝ) ^ (11 * m) :=
    (mul_lt_mul_of_pos_right hClarge hscalePos).trans_le hbasepow
  have hfiveHeadPos : 0 < (5 : ℝ) ^ (18 * 11 : ℕ) := by positivity
  have hgrow' :
      (B ^ (11 : ℕ) * 64 * (16 : ℝ) ^ (6 * m)) *
          5 ^ (18 * 11 : ℕ) <
        (5 : ℝ) ^ ((m - 18) * 11) * 5 ^ (18 * 11 : ℕ) := by
    dsimp [C] at hgrow
    rw [show 11 * m = (m - 18) * 11 + 18 * 11 by omega, pow_add] at hgrow
    simpa [mul_assoc, mul_comm, mul_left_comm] using hgrow
  have hgrowCore : B ^ (11 : ℕ) * 64 * (16 : ℝ) ^ (6 * m) <
      (5 : ℝ) ^ ((m - 18) * 11) :=
    lt_of_mul_lt_mul_right hgrow' hfiveHeadPos.le
  have hpSixBound : B ^ (11 : ℕ) * (p : ℝ) ^ (6 : ℕ) <
      (5 : ℝ) ^ ((m - 18) * 11) := by
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpupperSix (pow_nonneg hB 11))
    calc
      B ^ (11 : ℕ) * (2 * (16 : ℝ) ^ m) ^ (6 : ℕ) =
          B ^ (11 : ℕ) * 64 * (16 : ℝ) ^ (6 * m) := by
        rw [mul_pow, ← pow_mul]
        norm_num
        ring
      _ < _ := hgrowCore
  exact (not_lt_of_ge (hleft.trans hceil11)) hpSixBound

theorem not_sqrtLogarithmicCayleySchedule_boundedAtBoundaryPoint :
    ¬ ∃ C : ℝ, ∀ N,
      ‖poleClearedFirstTraceScheduledApprox sqrtLogarithmicCayleySchedule N
        boundaryExteriorPoint‖ ≤ C := by
  intro hbound
  exact not_sqrtLogarithmicCayleySchedule_boundaryFivePrimeCeiling
    (boundaryFiveCayleySchedule_prime_scale_ceiling
      sqrtLogarithmicCayleySchedule
      tendsto_sqrtLogarithmicCayleySchedule_atTop hbound)

theorem not_sqrtLogarithmicCayleySchedule_locallyBounded :
    ¬ PoleClearedFirstTraceScheduledLocallyBounded sqrtLogarithmicCayleySchedule := by
  intro hloc
  obtain ⟨R, hR, hball, C, hC⟩ :=
    hloc boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
  have hcenter : boundaryExteriorPoint ∈ ball boundaryExteriorPoint R := mem_ball_self hR
  exact not_sqrtLogarithmicCayleySchedule_boundedAtBoundaryPoint
    ⟨C, fun N => hC N boundaryExteriorPoint hcenter⟩

end

end RHTower
