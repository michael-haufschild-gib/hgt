import GaloisForLFunctions.RHTower.Sieve.PSeriesTailAboveCutoff
import GaloisForLFunctions.RHTower.GaussSpikeMass

/-!
# The offset bookkeeping of the near-diagonal tail

Each of the three exponential-sum regimes contributes a power of `T` after the offset `r` is summed
against `1/r`.  The two tail ranges start at `T^{1/4}` and give `T^{15/16}` and `T^{7/8}`; the two
head ranges reach `T^{2/3}` and `T^{3/4}` and give `T^{53/54}` and `T^{15/16}`.  The transition
exponent `5/6 + (2/3)(2/9) = 53/54` dominates.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- A reciprocal power at a cutoff at least `T^a` is at most `T^{-ab}`. -/
theorem rpow_neg_cutoff_le {T a b : ℝ} (hT : 1 ≤ T) (hb : 0 < b) {R : ℕ}
    (hR : T ^ a ≤ (R : ℝ)) (hR1 : 1 ≤ R) :
    ((R : ℝ)) ^ (-b) ≤ T ^ (-(a * b)) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR1
  have hTa : (0 : ℝ) < T ^ a := Real.rpow_pos_of_pos hT0 a
  have hstep : ((R : ℝ)) ^ (-b) ≤ (T ^ a) ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos hTa hR (by linarith)
  have hid : (T ^ a) ^ (-b) = T ^ (-(a * b)) := by
    rw [← Real.rpow_mul hT0.le]
    congr 1
    ring
  rw [hid] at hstep
  exact hstep

/-- **The tail contribution.**  An offset range starting at `T^a` costs `a(c−1)` in the exponent. -/
theorem tail_contribution_le {T a c θ : ℝ} (hT : 1 ≤ T) (hc : 1 < c) {R N : ℕ}
    (hR1 : 1 ≤ R) (hR : T ^ a ≤ (R : ℝ)) :
    T ^ θ * ∑ r ∈ Finset.Icc R N, ((r : ℝ)) ^ (-c)
      ≤ (c / (c - 1)) * T ^ (θ - a * (c - 1)) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hc1 : (0 : ℝ) < c - 1 := by linarith
  have hTθ : (0 : ℝ) < T ^ θ := Real.rpow_pos_of_pos hT0 θ
  have hsum := sum_rpow_neg_tail_le (c := c) hc (R := R) (N := N) hR1
  have hRpow : ((R : ℝ)) ^ (1 - c) ≤ T ^ (-(a * (c - 1))) := by
    have h := rpow_neg_cutoff_le (T := T) (a := a) (b := c - 1) hT hc1 hR hR1
    rw [show (1 - c : ℝ) = -(c - 1) by ring]
    exact h
  have hstep : T ^ θ * ∑ r ∈ Finset.Icc R N, ((r : ℝ)) ^ (-c)
      ≤ T ^ θ * ((c / (c - 1)) * ((R : ℝ)) ^ (1 - c)) :=
    mul_le_mul_of_nonneg_left hsum hTθ.le
  refine hstep.trans ?_
  have hcoef : (0 : ℝ) ≤ c / (c - 1) := by positivity
  have hstep2 : T ^ θ * ((c / (c - 1)) * ((R : ℝ)) ^ (1 - c))
      ≤ T ^ θ * ((c / (c - 1)) * T ^ (-(a * (c - 1)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRpow hcoef) hTθ.le
  refine hstep2.trans (le_of_eq ?_)
  rw [show T ^ θ * ((c / (c - 1)) * T ^ (-(a * (c - 1))))
      = (c / (c - 1)) * (T ^ θ * T ^ (-(a * (c - 1)))) by ring,
    ← Real.rpow_add hT0]
  congr 2

/-- **The head contribution.**  An offset range reaching `K·T^a` gains `a(1−c)` in the exponent. -/
theorem head_contribution_le {T a c θ K : ℝ} (hT : 1 ≤ T) (hc0 : 0 < c) (hc1 : c < 1)
    (ha : 0 ≤ a) (hK : 1 ≤ K) {M : ℕ} (hM : (M : ℝ) ≤ K * T ^ a) :
    T ^ θ * ∑ r ∈ Finset.Icc 1 M, ((r : ℝ)) ^ (-c)
      ≤ (1 + K ^ (1 - c) / (1 - c)) * T ^ (θ + a * (1 - c)) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hd : (0 : ℝ) < 1 - c := by linarith
  have hTθ : (0 : ℝ) < T ^ θ := Real.rpow_pos_of_pos hT0 θ
  have hTa : (0 : ℝ) < T ^ a := Real.rpow_pos_of_pos hT0 a
  have hsum := RHTower.sum_rpow_neg_head_le hc0 hc1 M
  have hMpow : ((M : ℝ)) ^ (1 - c) ≤ K ^ (1 - c) * T ^ (a * (1 - c)) := by
    have hstep : ((M : ℝ)) ^ (1 - c) ≤ (K * T ^ a) ^ (1 - c) :=
      Real.rpow_le_rpow (Nat.cast_nonneg M) hM hd.le
    have hid : (K * T ^ a) ^ (1 - c) = K ^ (1 - c) * T ^ (a * (1 - c)) := by
      rw [Real.mul_rpow (by linarith) hTa.le, ← Real.rpow_mul hT0.le]
    rw [hid] at hstep
    exact hstep
  have hone : (1 : ℝ) ≤ T ^ (a * (1 - c)) :=
    Real.one_le_rpow hT (by positivity)
  have hchain : ∑ r ∈ Finset.Icc 1 M, ((r : ℝ)) ^ (-c)
      ≤ (1 + K ^ (1 - c) / (1 - c)) * T ^ (a * (1 - c)) := by
    refine hsum.trans ?_
    have h1 : ((M : ℝ)) ^ (1 - c) / (1 - c)
        ≤ (K ^ (1 - c) / (1 - c)) * T ^ (a * (1 - c)) := by
      rw [div_mul_eq_mul_div]
      gcongr
    have hexp : (1 + K ^ (1 - c) / (1 - c)) * T ^ (a * (1 - c))
        = T ^ (a * (1 - c)) + (K ^ (1 - c) / (1 - c)) * T ^ (a * (1 - c)) := by ring
    rw [hexp]
    linarith [h1, hone]
  have hres : T ^ θ * ∑ r ∈ Finset.Icc 1 M, ((r : ℝ)) ^ (-c)
      ≤ T ^ θ * ((1 + K ^ (1 - c) / (1 - c)) * T ^ (a * (1 - c))) :=
    mul_le_mul_of_nonneg_left hchain hTθ.le
  refine hres.trans (le_of_eq ?_)
  rw [show T ^ θ * ((1 + K ^ (1 - c) / (1 - c)) * T ^ (a * (1 - c)))
      = (1 + K ^ (1 - c) / (1 - c)) * (T ^ θ * T ^ (a * (1 - c))) by ring,
    ← Real.rpow_add hT0]

/-- The transition exponent of the near-diagonal tail. -/
theorem kubalalika_transition_exponent : (5 : ℝ) / 6 + (2 / 3) * (1 - (7 : ℝ) / 9) = 53 / 54 := by
  norm_num

/-- The low-frequency exponent. -/
theorem kubalalika_low_exponent : (1 : ℝ) - (1 / 4) * ((5 : ℝ) / 4 - 1) = 15 / 16 := by
  norm_num

/-- The high-frequency exponent. -/
theorem kubalalika_high_exponent : (3 : ℝ) / 4 + (3 / 4) * (1 - (3 : ℝ) / 4) = 15 / 16 := by
  norm_num

/-- The second transition exponent. -/
theorem kubalalika_second_exponent : (1 : ℝ) - (1 / 4) * ((3 : ℝ) / 2 - 1) = 7 / 8 := by
  norm_num

/-- The transition regime dominates. -/
theorem kubalalika_exponent_dominates :
    max (max ((15 : ℝ) / 16) (53 / 54)) ((7 : ℝ) / 8) = 53 / 54 := by
  norm_num [max_def]

end

end RHTower.Sieve
