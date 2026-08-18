import GaloisForLFunctions.RHTower.Sieve.HuxleyExplicitLargeValues

/-!
# Huxley's density bound for a dyadic Dirichlet block
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- **The Huxley threshold in the divisor-bounded normalisation.**  `V ≥ N^{3/4+o(1)}` becomes
`2400 D² ≤ N^{1/2−2σ}` when `V = N^{-σ}` and the coefficients are bounded by `D`. -/
theorem huxley_threshold_of_rpow {N : ℕ} (hN : 1 ≤ N) {D sigma : ℝ}
    (h : 2400 * D ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma)) :
    (D ^ 2 / (N : ℝ)) * (1 + 1536 * Real.sqrt (3 * (N : ℝ) / (4 * Real.pi)))
      ≤ ((N : ℝ) ^ (-sigma)) ^ 2 / 3 := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  -- the resonance endpoint
  have hconst : Real.sqrt (3 / (4 * Real.pi)) ≤ 0.5 := by
    have hle : (3 : ℝ) / (4 * Real.pi) ≤ 0.25 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hpi]
    have h1 : Real.sqrt (3 / (4 * Real.pi)) ≤ Real.sqrt 0.25 := Real.sqrt_le_sqrt hle
    have h2 : Real.sqrt 0.25 = 0.5 := by
      rw [show (0.25 : ℝ) = 0.5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h1, h2]
  have hsplit : Real.sqrt (3 * (N : ℝ) / (4 * Real.pi))
      = Real.sqrt (3 / (4 * Real.pi)) * Real.sqrt (N : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hsN : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hNR
  have henv : 1 + 1536 * Real.sqrt (3 * (N : ℝ) / (4 * Real.pi)) ≤ 800 * Real.sqrt (N : ℝ) := by
    rw [hsplit]
    nlinarith [hconst, hsN, Real.sqrt_nonneg ((N : ℝ))]
  -- reduce to the reciprocal square root
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN0.le
  have hs0 : (0 : ℝ) < Real.sqrt (N : ℝ) := by linarith
  have hstep : (D ^ 2 / (N : ℝ)) * (1 + 1536 * Real.sqrt (3 * (N : ℝ) / (4 * Real.pi)))
      ≤ 800 * D ^ 2 / Real.sqrt (N : ℝ) := by
    have hD2 : (0 : ℝ) ≤ D ^ 2 / (N : ℝ) := by positivity
    have h1 := mul_le_mul_of_nonneg_left henv hD2
    have hdiv : Real.sqrt (N : ℝ) / (N : ℝ) = 1 / Real.sqrt (N : ℝ) := by
      field_simp
      exact Real.sq_sqrt hN0.le
    have h2 : D ^ 2 / (N : ℝ) * (800 * Real.sqrt (N : ℝ)) = 800 * D ^ 2 / Real.sqrt (N : ℝ) := by
      rw [show D ^ 2 / (N : ℝ) * (800 * Real.sqrt (N : ℝ))
          = 800 * D ^ 2 * (Real.sqrt (N : ℝ) / (N : ℝ)) by ring, hdiv]
      ring
    linarith [h1, h2 ▸ h1]
  refine le_trans hstep ?_
  -- rpow bookkeeping
  have hsqrpow : Real.sqrt (N : ℝ) = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (N : ℝ)
  have hV2 : ((N : ℝ) ^ (-sigma)) ^ 2 = (N : ℝ) ^ (-(2 * sigma)) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (-sigma)) 2, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hsplit2 : (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma)
      = (N : ℝ) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ (-(2 * sigma)) := by
    rw [← Real.rpow_add hN0]
    congr 1
  rw [hV2, hsqrpow]
  set P : ℝ := (N : ℝ) ^ ((1 : ℝ) / 2) with hP
  have hP0 : (0 : ℝ) < P := Real.rpow_pos_of_pos hN0 _
  rw [hsplit2] at h
  rw [div_le_iff₀ hP0]
  nlinarith [h, hP0, Real.rpow_pos_of_pos hN0 (-(2 * sigma))]

/-- **Huxley's density bound for a dyadic Dirichlet block, both terms explicit.**
For `‖c n‖ ≤ D` on `[N,2N)`, a one-separated set `S` of ordinates inside a range of length `2T` on
which the block reaches `N^{-σ}` satisfies

`|S| ≤ (6594624·T·D⁶·N^{6σ−2} + 2·D²·N^{2σ})·(1 + 12π(1 + log(2T+1)))` ,

which is Huxley's `T G³ N V^{-6} + G N V^{-2}` at `G = D²/N`, `V = N^{-σ}`, with every constant
explicit and no asymptotic notation. -/
theorem huxley_block_two_term {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℂ)
    {T D sigma : ℝ} (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hc : ∀ n ∈ Finset.Ico N (2 * N), ‖c n‖ ≤ D)
    (hthr : 2400 * D ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma))
    (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T)
    (hbig : ∀ x ∈ S, (N : ℝ) ^ (-sigma) ≤ ‖blockPoly N c 1 x‖) :
    (S.card : ℝ)
      ≤ (6594624 * T * D ^ 6 * (N : ℝ) ^ (6 * sigma - 2)
          + 2 * D ^ 2 * (N : ℝ) ^ (2 * sigma))
        * (1 + 12 * Real.pi * (1 + Real.log (2 * T + 1))) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hthresh := huxley_threshold_of_rpow hN hthr
  have hV : (0 : ℝ) < (N : ℝ) ^ (-sigma) := Real.rpow_pos_of_pos hN0 _
  have hbase := huxley_block_large_values_explicit hN c (delta := 1) (Ttot := 2 * T)
    one_pos hV (by linarith) hD hc S hsep hspread hbig hthresh
  simp only [div_one] at hbase
  set V : ℝ := (N : ℝ) ^ (-sigma) with hVdef
  set A : ℝ := (N : ℝ) ^ (2 * sigma) with hAdef
  have hA0 : (0 : ℝ) < A := Real.rpow_pos_of_pos hN0 _
  have hpowV : ∀ k : ℕ, V ^ k = (N : ℝ) ^ (-(sigma * (k : ℝ))) := by
    intro k
    rw [hVdef, ← Real.rpow_natCast ((N : ℝ) ^ (-sigma)) k, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  have hone : V ^ 2 * A = 1 := by
    rw [hpowV 2, hAdef, ← Real.rpow_add hN0,
      show -(sigma * ((2 : ℕ) : ℝ)) + 2 * sigma = 0 by push_cast; ring, Real.rpow_zero]
  have hA2 : A ^ 2 = (N : ℝ) ^ (4 * sigma) := by
    rw [hAdef, ← Real.rpow_natCast ((N : ℝ) ^ (2 * sigma)) 2, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hone4 : V ^ 4 * A ^ 2 = 1 := by
    rw [hpowV 4, hA2, ← Real.rpow_add hN0,
      show -(sigma * ((4 : ℕ) : ℝ)) + 4 * sigma = 0 by push_cast; ring, Real.rpow_zero]
  have hV4inv : V ^ 4 = (A ^ 2)⁻¹ := by
    field_simp
    linarith [hone4]
  have hA3 : A ^ 3 = (N : ℝ) ^ (6 * sigma) := by
    rw [hAdef, ← Real.rpow_natCast ((N : ℝ) ^ (2 * sigma)) 3, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hNA : (N : ℝ) ^ (6 * sigma - 2) = A ^ 3 / (N : ℝ) ^ 2 := by
    rw [hA3, eq_div_iff (by positivity), ← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  set L : ℝ := 1 + 12 * Real.pi * (1 + Real.log (2 * T + 1)) with hLdef
  calc (S.card : ℝ)
      = ((S.card : ℝ) * V ^ 2) * A := by
        rw [mul_assoc, hone, mul_one]
    _ ≤ (1648656 * (2 * T) * D ^ 4 / ((N : ℝ) ^ 2 * V ^ 4) + 1) * (2 * D ^ 2 * L) * A :=
        mul_le_mul_of_nonneg_right hbase hA0.le
    _ = (6594624 * T * D ^ 6 * (N : ℝ) ^ (6 * sigma - 2) + 2 * D ^ 2 * A) * L := by
        rw [hV4inv, hNA]
        field_simp
        ring

end RHTower.Sieve
