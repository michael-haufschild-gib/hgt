import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfLogScheduleBoundaryNoGo

/-!
# Two-factor boundary growth and scheduled prime ceiling

At `s = 6/11`, both Cayley binomial factors grow exponentially.  The positive-half factor grows
at least like `2^N` after a finite head, while the negative-half factor has the same lower rate.
Their product therefore satisfies `‖r_N‖ >= 4^(N-6)/5`.

For a scheduled product to be pointwise bounded, adjacent prime cutoffs must consequently satisfy
`4^min(kappa(p)-6,kappa(p+1)-6) <= B p^(6/11)`.  Any schedule violating this scale law is ruled
out.  This sharpens the earlier one-factor prime ceiling and quantifies the two-factor exterior
growth that a surviving resynchronization must absorb.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

def boundaryHalfExteriorMagnitude (k : ℕ) : ℝ := -boundaryHalfExteriorTerm k

theorem boundaryHalfExteriorMagnitude_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < boundaryHalfExteriorMagnitude k := by
  exact neg_pos.mpr (boundaryHalfExteriorTerm_neg hk)

theorem boundaryHalfExteriorMagnitude_growth_two {k : ℕ} (hk : 5 ≤ k) :
    2 * boundaryHalfExteriorMagnitude k ≤ boundaryHalfExteriorMagnitude (k + 1) := by
  have hrec := GaloisForLFunctions.choose_succ_field (1 / 2 : ℝ) k
  have hkreal : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
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
  have hratio : (2 : ℝ) ≤
      (8 / 3 : ℝ) * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1) := by
    rw [le_div_iff₀ hk1]
    nlinarith
  rw [boundaryHalfExteriorMagnitude, boundaryHalfExteriorMagnitude, hterm]
  have htneg := boundaryHalfExteriorTerm_neg
    (le_trans (by norm_num : 1 ≤ 5) hk)
  have hmul := mul_le_mul_of_nonneg_left hratio (neg_nonneg.mpr htneg.le)
  calc
    2 * -boundaryHalfExteriorTerm k ≤
        (8 / 3 * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1)) *
          -boundaryHalfExteriorTerm k := by simpa [mul_comm] using hmul
    _ = -(boundaryHalfExteriorTerm k *
        (8 / 3 * ((k : ℝ) - 1 / 2) / ((k : ℝ) + 1))) := by ring

theorem boundaryHalfExteriorMagnitude_five_ge_two :
    (2 : ℝ) ≤ boundaryHalfExteriorMagnitude 5 := by
  have hc1 : Ring.choose (1 / 2 : ℝ) 1 = 1 / 2 := by norm_num
  have hc2 : Ring.choose (1 / 2 : ℝ) 2 = -1 / 8 := by
    have h := GaloisForLFunctions.choose_succ_field (1 / 2 : ℝ) 1
    rw [hc1] at h
    norm_num at h ⊢
    linarith
  have hc3 : Ring.choose (1 / 2 : ℝ) 3 = 1 / 16 := by
    have h := GaloisForLFunctions.choose_succ_field (1 / 2 : ℝ) 2
    rw [hc2] at h
    norm_num at h ⊢
    linarith
  have hc4 : Ring.choose (1 / 2 : ℝ) 4 = -5 / 128 := by
    have h := GaloisForLFunctions.choose_succ_field (1 / 2 : ℝ) 3
    rw [hc3] at h
    norm_num at h ⊢
    linarith
  have hc5 : Ring.choose (1 / 2 : ℝ) 5 = 7 / 256 := by
    have h := GaloisForLFunctions.choose_succ_field (1 / 2 : ℝ) 4
    rw [hc4] at h
    norm_num at h ⊢
    linarith
  norm_num [boundaryHalfExteriorMagnitude, boundaryHalfExteriorTerm, hc5]

theorem boundaryHalfExteriorMagnitude_ge_two_pow {k : ℕ} (hk : 5 ≤ k) :
    (2 : ℝ) ^ (k - 4) ≤ boundaryHalfExteriorMagnitude k := by
  induction k, hk using Nat.le_induction with
  | base => simpa using boundaryHalfExteriorMagnitude_five_ge_two
  | succ k hk ih =>
      have hexp : k + 1 - 4 = (k - 4) + 1 := by omega
      rw [hexp, pow_succ]
      calc
        (2 : ℝ) ^ (k - 4) * 2 ≤ boundaryHalfExteriorMagnitude k * 2 :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = 2 * boundaryHalfExteriorMagnitude k := by ring
        _ ≤ boundaryHalfExteriorMagnitude (k + 1) :=
          boundaryHalfExteriorMagnitude_growth_two hk

theorem norm_boundaryHalfExteriorPartialSum_ge_two_pow
    {N : ℕ} (hN : 6 ≤ N) :
    (2 : ℝ) ^ (N - 5) ≤
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
  have hlast := boundaryHalfExteriorMagnitude_ge_two_pow (show 5 ≤ N - 1 by omega)
  have hexp : N - 1 - 4 = N - 5 := by omega
  rw [hexp] at hlast
  rw [boundaryHalfExteriorMagnitude] at hlast
  rw [hsplit]
  nlinarith

theorem norm_boundaryNegHalfExteriorPartialSum_ge_two_pow
    {N : ℕ} (hN : 3 ≤ N) :
    (2 : ℝ) ^ (N - 2) / 5 ≤
      ‖(binomialSeries ℂ (-1 / 2 : ℂ)).partialSum N (8 / 3 : ℂ)‖ := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · have hm2 : 2 ≤ m := by omega
    obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    subst m
    rw [show 2 * (k + 1) - 2 = 2 * k by omega,
      show 2 * (k + 1) = 2 * k + 2 by omega]
    exact norm_boundaryNegHalfExteriorPartialSum_even_ge k
  · have hm1 : 1 ≤ m := by omega
    have hexp : 2 * m + 1 - 2 = 2 * m - 1 := by omega
    rw [hexp]
    exact norm_boundaryNegHalfExteriorPartialSum_odd_ge m hm1

theorem boundary_four_pow_le_two_factor_pow {N : ℕ} (hN : 6 ≤ N) :
    (4 : ℝ) ^ (N - 6) ≤ (2 : ℝ) ^ (N - 5) * (2 : ℝ) ^ (N - 2) := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem norm_poleFactorSqrtApprox_boundaryExteriorPoint_four_pow
    {N : ℕ} (hN : 6 ≤ N) :
    (4 : ℝ) ^ (N - 6) / 5 ≤
      ‖poleFactorSqrtApprox N boundaryExteriorPoint‖ := by
  have hhalf := norm_boundaryHalfExteriorPartialSum_ge_two_pow hN
  have hneg := norm_boundaryNegHalfExteriorPartialSum_ge_two_pow (N := N) (by omega)
  have hhalf' : (2 : ℝ) ^ (N - 5) ≤
      ‖(binomialSeries ℂ (1 / 2 : ℂ)).partialSum N (-(8 / 3) : ℂ)‖ := by
    simpa only [neg_div] using hhalf
  have hneg' : (2 : ℝ) ^ (N - 2) / 5 ≤
      ‖(binomialSeries ℂ (-(1 / 2) : ℂ)).partialSum N (8 / 3 : ℂ)‖ := by
    simpa only [neg_div] using hneg
  rw [poleFactorSqrtApprox, poleFactorCayley_boundaryExteriorPoint]
  norm_num only [neg_div, neg_neg]
  rw [norm_mul]
  calc
    (4 : ℝ) ^ (N - 6) / 5 ≤
        ((2 : ℝ) ^ (N - 5) * (2 : ℝ) ^ (N - 2)) / 5 :=
      div_le_div_of_nonneg_right (boundary_four_pow_le_two_factor_pow hN) (by norm_num)
    _ = (2 : ℝ) ^ (N - 5) * ((2 : ℝ) ^ (N - 2) / 5) := by ring
    _ ≤ _ := mul_le_mul hhalf' hneg' (by positivity) (by positivity)

/-- Two-factor prime ceiling at the boundary test point `s = 6/11`. -/
theorem boundaryCayleySchedule_prime_scale_ceiling
    (kappa : ℕ → ℕ) (hkappa : ∀ N, 6 ≤ kappa N)
    (hbound : ∃ C : ℝ, ∀ N,
      ‖poleClearedFirstTraceScheduledApprox kappa N boundaryExteriorPoint‖ ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℕ, p.Prime →
      (4 : ℝ) ^ min (kappa p - 6) (kappa (p + 1) - 6) ≤
        B * (p : ℝ) ^ (6 / 11 : ℝ) := by
  obtain ⟨C, hC⟩ := hbound
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  let K : ℝ := 5 * C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpartial (N : ℕ) :
      (4 : ℝ) ^ (kappa N - 6) *
          ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤ K := by
    have hfactor := norm_poleFactorSqrtApprox_boundaryExteriorPoint_four_pow (hkappa N)
    have hdetpos : 0 < ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ :=
      norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
    have hsource := hC N
    have hprod :
        ‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ *
            ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤
          C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ := by
      rw [poleClearedFirstTraceScheduledApprox, norm_div, norm_mul] at hsource
      exact (div_le_iff₀ hdetpos).mp hsource
    have hscaled :
        ((4 : ℝ) ^ (kappa N - 6) / 5) *
            ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤
          C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ :=
      le_trans (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)) hprod
    dsimp [K]
    nlinarith
  refine ⟨4 * K, by positivity, ?_⟩
  intro p hp
  let e : ℕ := min (kappa p - 6) (kappa (p + 1) - 6)
  have hpowleft : (4 : ℝ) ^ e ≤ (4 : ℝ) ^ (kappa p - 6) :=
    pow_le_pow_right₀ (by norm_num) (min_le_left _ _)
  have hpowright : (4 : ℝ) ^ e ≤ (4 : ℝ) ^ (kappa (p + 1) - 6) :=
    pow_le_pow_right₀ (by norm_num) (min_le_right _ _)
  have hpbound :
      (4 : ℝ) ^ e * ‖squarefreeHalfDirichletPartialSum p boundaryExteriorPoint‖ ≤ K :=
    le_trans (mul_le_mul_of_nonneg_right hpowleft (norm_nonneg _)) (hpartial p)
  have hsuccbound :
      (4 : ℝ) ^ e *
          ‖squarefreeHalfDirichletPartialSum (p + 1) boundaryExteriorPoint‖ ≤ K :=
    le_trans (mul_le_mul_of_nonneg_right hpowright (norm_nonneg _)) (hpartial (p + 1))
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
      (4 : ℝ) ^ e * ‖LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint p‖ ≤
        2 * K := by
    calc
      (4 : ℝ) ^ e * ‖LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint p‖ ≤
          (4 : ℝ) ^ e *
            (‖squarefreeHalfDirichletPartialSum (p + 1) boundaryExteriorPoint‖ +
              ‖squarefreeHalfDirichletPartialSum p boundaryExteriorPoint‖) :=
        mul_le_mul_of_nonneg_left htri (pow_nonneg (by norm_num) _)
      _ = (4 : ℝ) ^ e *
            ‖squarefreeHalfDirichletPartialSum (p + 1) boundaryExteriorPoint‖ +
          (4 : ℝ) ^ e * ‖squarefreeHalfDirichletPartialSum p boundaryExteriorPoint‖ := by ring
      _ ≤ K + K := add_le_add hsuccbound hpbound
      _ = 2 * K := by ring
  rw [norm_squarefreeConvolutionHalf_term_prime_boundaryExteriorPoint p hp] at htermUpper
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpowpos : 0 < (p : ℝ) ^ (6 / 11 : ℝ) := Real.rpow_pos_of_pos hp0 _
  have hdiv : ((4 : ℝ) ^ e / 2) / (p : ℝ) ^ (6 / 11 : ℝ) ≤ 2 * K := by
    calc
      ((4 : ℝ) ^ e / 2) / (p : ℝ) ^ (6 / 11 : ℝ) =
          (4 : ℝ) ^ e * ((1 / 2 : ℝ) / (p : ℝ) ^ (6 / 11 : ℝ)) := by ring
      _ ≤ 2 * K := htermUpper
  have hmul := (div_le_iff₀ hpowpos).mp hdiv
  change (4 : ℝ) ^ e ≤ (4 * K) * (p : ℝ) ^ (6 / 11 : ℝ)
  nlinarith

def BoundaryCayleySchedulePrimeScaleDiverges (kappa : ℕ → ℕ) : Prop :=
  Tendsto (fun N : ℕ =>
    (4 : ℝ) ^ min (kappa N - 6) (kappa (N + 1) - 6) /
      (N : ℝ) ^ (6 / 11 : ℝ)) atTop atTop

theorem not_scheduledApprox_boundedAtBoundaryPoint_of_primeScaleDiverges
    (kappa : ℕ → ℕ) (hkappa : ∀ N, 6 ≤ kappa N)
    (hdiv : BoundaryCayleySchedulePrimeScaleDiverges kappa) :
    ¬ ∃ C : ℝ, ∀ N,
      ‖poleClearedFirstTraceScheduledApprox kappa N boundaryExteriorPoint‖ ≤ C := by
  intro hbound
  obtain ⟨B, hBnonneg, hceiling⟩ :=
    boundaryCayleySchedule_prime_scale_ceiling kappa hkappa hbound
  have heventually : ∀ᶠ N : ℕ in atTop,
      B < (4 : ℝ) ^ min (kappa N - 6) (kappa (N + 1) - 6) /
        (N : ℝ) ^ (6 / 11 : ℝ) := hdiv.eventually_gt_atTop B
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventually
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpowpos : 0 < (p : ℝ) ^ (6 / 11 : ℝ) := Real.rpow_pos_of_pos hp0 _
  have hlarge := hN p hpN
  have hsmall :
      (4 : ℝ) ^ min (kappa p - 6) (kappa (p + 1) - 6) /
          (p : ℝ) ^ (6 / 11 : ℝ) ≤ B := by
    exact (div_le_iff₀ hpowpos).2 (hceiling p hp)
  exact (not_lt_of_ge hsmall) hlarge

end

end RHTower
