import GaloisForLFunctions.RHTower.Sieve.GSScheduleFacts
import GaloisForLFunctions.RHTower.Sieve.RouteTScheduleWorstCase
import GaloisForLFunctions.RHTower.Sieve.RouteTScheduleHats

/-!
# The Granville–Soundararajan tail, assembled at the schedule

Every hypothesis of `Sieve/RouteTTailBudget.exists_abs_sum_cos_div_primesRange_le_budget` is
discharged at `y = gsCutoff z`, `ρ₀ = gsRho z`, `B = 9(2 + log z)`, for every frequency with
`(log z)^{0.6} ≤ log|t| ≤ 2 log z`.  The resulting bound `9ρ₀(2 + log z)` is exactly `1`.

The six facts about `log z` that the assembly needs are hypotheses here; each of them is an
eventually-true statement proved in `Sieve/RouteTThresholdLimits`, `Sieve/PolylogRpowDomination`
and below.
-/

namespace RHTower.Sieve

open Finset Filter Topology

noncomputable section

/-- The cutoff outgrows every linear function of the logarithm. -/
theorem eventually_gsCutoff_growth :
    ∀ᶠ L : ℝ in atTop, 126 * Real.exp 9 * (2 + L) ≤ Real.exp (L ^ (0.99 : ℝ)) := by
  have hlim := eventually_const_mul_rpow_polylog_le_rpow
    (C := 1512 * Real.exp 9) (α := (1 : ℝ)) (β := (1.98 : ℝ)) 0 (by norm_num)
  filter_upwards [hlim, Filter.eventually_ge_atTop (1 : ℝ)] with L h1 hL1
  simp only [pow_zero, mul_one, Real.rpow_one] at h1
  have hL0 : (0 : ℝ) < L := by linarith
  have hu : (0 : ℝ) ≤ L ^ (0.99 : ℝ) := Real.rpow_nonneg hL0.le _
  have hhalf : (1 : ℝ) + L ^ (0.99 : ℝ) / 2 ≤ Real.exp (L ^ (0.99 : ℝ) / 2) := by
    have := Real.add_one_le_exp (L ^ (0.99 : ℝ) / 2)
    linarith
  have hsq : Real.exp (L ^ (0.99 : ℝ)) = (Real.exp (L ^ (0.99 : ℝ) / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hpos : (0 : ℝ) ≤ 1 + L ^ (0.99 : ℝ) / 2 := by linarith
  have hge : (L ^ (0.99 : ℝ)) ^ 2 / 4 ≤ Real.exp (L ^ (0.99 : ℝ)) := by
    rw [hsq]
    nlinarith [hhalf, hpos, hu]
  have hval : (L ^ (0.99 : ℝ)) ^ 2 = L ^ (1.98 : ℝ) := by
    rw [← Real.rpow_natCast (L ^ (0.99 : ℝ)) 2, ← Real.rpow_mul hL0.le]
    norm_num
  rw [hval] at hge
  have he : (0 : ℝ) < Real.exp 9 := Real.exp_pos 9
  have hlin : 126 * Real.exp 9 * (2 + L) ≤ 1512 * Real.exp 9 * L / 4 := by nlinarith [hL1, he]
  linarith [hlin, h1, hge]

/-- **The tail cosine sum at the schedule, from the six schedule facts.** -/
theorem exists_abs_sum_cos_div_gsRange_le :
    ∃ A delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (z : ℕ) (t : ℝ), 2 ≤ z → 1 ≤ Real.log (z : ℝ) →
        Real.log (9 * C * (1 + (4 + 2 * Real.log (z : ℝ)) * routeTBudgetHat A (Real.log (z : ℝ))
              + 2 * Real.log (z : ℝ)) * (9 * (2 + Real.log (z : ℝ))))
            * (6 * routeTBudgetHat A (Real.log (z : ℝ)))
          ≤ (Real.log (z : ℝ)) ^ (0.99 : ℝ) →
        routeTTruncHat (Real.log (z : ℝ)) * Real.log (z : ℝ)
            + Real.log (9 * C * (3 : ℝ) ^ routeTTruncHat (Real.log (z : ℝ))
                * (2 + (Real.log (z : ℝ)) ^ 2 + (4 + 2 * Real.log (z : ℝ))
                    * routeTBudgetHat A (Real.log (z : ℝ)))
                * (9 * (2 + Real.log (z : ℝ))))
          ≤ (Real.log (z : ℝ)) ^ (0.6 : ℝ) →
        Real.log (216 * (2 + Real.log (z : ℝ))) ≤ (Real.log (z : ℝ)) ^ (0.99 : ℝ) / 4 →
        1 / routeTBudgetHat A (Real.log (z : ℝ)) ≤ delta →
        126 * Real.exp 9 * (2 + Real.log (z : ℝ))
          ≤ Real.exp ((Real.log (z : ℝ)) ^ (0.99 : ℝ)) →
        Real.log (16 * Real.pi / 3) ≤ (Real.log (z : ℝ)) ^ (0.6 : ℝ) →
        (Real.log (z : ℝ)) ^ (0.6 : ℝ) ≤ Real.log |t| →
        Real.log |t| ≤ 2 * Real.log (z : ℝ) →
        |∑ p ∈ primesRange (gsCutoff z) z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)| ≤ 1 := by
  obtain ⟨A, delta, C, hdelta, hC, hbudget⟩ := exists_abs_sum_cos_div_primesRange_le_budget
  refine ⟨A, delta, C, hdelta, hC, ?_⟩
  intro z t hz2 hLz1 hcon htru hcheb hinv hgro hpi htlo hthi
  have hLz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  have hzpos : 0 < z := by omega
  have hGhat0 : (0 : ℝ) < routeTBudgetHat A (Real.log (z : ℝ)) := routeTBudgetHat_pos hLz1
  -- the frequency
  have hlt0 : (0 : ℝ) < Real.log |t| := by
    have h2 : (0 : ℝ) < Real.log (16 * Real.pi / 3) := by
      refine Real.log_pos ?_
      nlinarith [Real.pi_gt_three]
    linarith
  have habs1 : (1 : ℝ) < |t| := by
    rcases le_or_gt |t| 1 with h | h
    · exfalso
      have hnp : Real.log |t| ≤ 0 := Real.log_nonpos (abs_nonneg t) h
      linarith
    · exact h
  have habs1' : (1 : ℝ) ≤ |t| := le_of_lt habs1
  have hτ : 16 * Real.pi / 3 ≤ |t| := by
    have hpi0 : (0 : ℝ) < 16 * Real.pi / 3 := by positivity
    have hle : Real.log (16 * Real.pi / 3) ≤ Real.log |t| := le_trans hpi htlo
    have hexp : Real.exp (Real.log (16 * Real.pi / 3)) ≤ Real.exp (Real.log |t|) :=
      Real.exp_le_exp.2 hle
    rwa [Real.exp_log hpi0, Real.exp_log (by linarith)] at hexp
  have hGle : routeTReciprocalBudget A t ≤ routeTBudgetHat A (Real.log (z : ℝ)) :=
    routeTReciprocalBudget_le_hat habs1' hthi
  have hG0 : (0 : ℝ) < routeTReciprocalBudget A t := by
    rw [routeTReciprocalBudget]
    have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
    have hb := one_le_routeTHeightBudget habs1'
    have hpow : (0 : ℝ) < (routeTHeightBudget t) ^ ((9 : ℝ) / 10) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hlog : (0 : ℝ) ≤ Real.log (routeTHeightBudget t) := Real.log_nonneg hb
    positivity
  have hvle : routeTTruncExponent t ≤ routeTTruncHat (Real.log (z : ℝ)) :=
    routeTTruncExponent_le_hat hLz1 htlo
  have hv0 : (0 : ℝ) ≤ routeTTruncExponent t := by
    rw [routeTTruncExponent]
    have hK := routeTWidthUpperConst_pos
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hp : (0 : ℝ) ≤ (Real.log |t| / Real.log 2) ^ ((9 : ℝ) / 10) :=
      Real.rpow_nonneg (by positivity) _
    positivity
  -- the schedule constants
  have hB0 : (0 : ℝ) < 9 * (2 + Real.log (z : ℝ)) := by linarith
  have hρ : 1 / (9 * (2 + Real.log (z : ℝ))) ≤ gsRho z := by rw [gsRho]
  have hρ0 : (0 : ℝ) ≤ gsRho z := (gsRho_pos hLz0.le).le
  have hy2 : 2 ≤ gsCutoff z := two_le_gsCutoff hLz0
  have hyz : gsCutoff z ≤ z := gsCutoff_le hLz1 hzpos
  have he9 : 14 * Real.exp 9 ≤ gsRho z * ((gsCutoff z : ℕ) : ℝ) := by
    have hc := exp_le_gsCutoff z
    have hstep : 126 * Real.exp 9 * (2 + Real.log (z : ℝ)) ≤ ((gsCutoff z : ℕ) : ℝ) :=
      le_trans hgro hc
    rw [gsRho, one_div, inv_mul_eq_div, le_div_iff₀ hB0]
    nlinarith [hstep]
  -- the worst-case keys
  have hkeycon : Real.log (9 * C * (1 + (4 + 2 * Real.log (z : ℝ))
        * routeTBudgetHat A (Real.log (z : ℝ)) + 2 * Real.log (z : ℝ))
        * (9 * (2 + Real.log (z : ℝ))))
      ≤ min delta (1 / routeTBudgetHat A (Real.log (z : ℝ))) / 6
        * (Real.log (z : ℝ)) ^ (0.99 : ℝ) := by
    rw [min_eq_right hinv]
    have h6G : (0 : ℝ) < 6 * routeTBudgetHat A (Real.log (z : ℝ)) := by linarith
    have hval : 1 / routeTBudgetHat A (Real.log (z : ℝ)) / 6
          * (Real.log (z : ℝ)) ^ (0.99 : ℝ)
        = (Real.log (z : ℝ)) ^ (0.99 : ℝ) / (6 * routeTBudgetHat A (Real.log (z : ℝ))) := by
      field_simp
    rw [hval, le_div_iff₀ h6G]
    linarith [hcon]
  have hfin : |∑ p ∈ primesRange (gsCutoff z) z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)|
      ≤ 9 * gsRho z * (2 + Real.log (z : ℝ)) := by
   refine hbudget (gsCutoff z) z t (gsRho z) hy2 hyz hρ0 hτ he9 ?_ ?_ ?_
   · intro i hyi hiz
     have hi1 : (1 : ℝ) ≤ (i : ℝ) := by
       have : 1 ≤ i := le_trans (by omega) hyi
       exact_mod_cast this
     have hi0 : (0 : ℝ) < (i : ℝ) := by linarith
     have hLimin : (Real.log (z : ℝ)) ^ (0.99 : ℝ) ≤ Real.log (i : ℝ) :=
       log_ge_of_ge_gsCutoff hyi
     have hLi : Real.log (i : ℝ) ≤ Real.log (z : ℝ) := by
       refine Real.log_le_log hi0 ?_
       exact_mod_cast hiz
     have hkey := contour_threshold_worst (C := C) (Li := Real.log (i : ℝ))
       (Lz := Real.log (z : ℝ)) (Lt := Real.log |t|) (G := routeTReciprocalBudget A t)
       (Ghat := routeTBudgetHat A (Real.log (z : ℝ))) (delta := delta)
       hC hLz0.le hG0 hGle hdelta hlt0.le hthi hLi hLimin hkeycon
     refine contour_regime_at hi1 ?_ hB0 hρ hkey
     have hP : (0 : ℝ) < 1 + (4 + Real.log |t|) * routeTReciprocalBudget A t
         + 2 * Real.log (i : ℝ) := by
       have hlogi : (0 : ℝ) ≤ Real.log (i : ℝ) := Real.log_nonneg hi1
       positivity
     positivity
   · intro i hyi hiz
     have hi1 : (1 : ℝ) ≤ (i : ℝ) := by
       have : 1 ≤ i := le_trans (by omega) hyi
       exact_mod_cast this
     have hi0 : (0 : ℝ) < (i : ℝ) := by linarith
     have hlogi : (0 : ℝ) ≤ Real.log (i : ℝ) := Real.log_nonneg hi1
     have hLi : Real.log (i : ℝ) ≤ Real.log (z : ℝ) := by
       refine Real.log_le_log hi0 ?_
       exact_mod_cast hiz
     have hkey := trunc_threshold_worst (C := C) (Li := Real.log (i : ℝ))
       (Lz := Real.log (z : ℝ)) (Lt := Real.log |t|) (G := routeTReciprocalBudget A t)
       (Ghat := routeTBudgetHat A (Real.log (z : ℝ))) (v := routeTTruncExponent t)
       (vhat := routeTTruncHat (Real.log (z : ℝ)))
       hC hLz0.le hG0 hGle hv0 hvle hlt0.le hthi htlo hlogi hLi htru
     refine trunc_regime_at hi1 ?_ (by linarith) hB0 hρ hkey
     have hQ : (0 : ℝ) < 2 + (Real.log (i : ℝ)) ^ 2
         + (4 + Real.log |t|) * routeTReciprocalBudget A t := by positivity
     have h3v : (0 : ℝ) < (3 : ℝ) ^ routeTTruncExponent t :=
       Real.rpow_pos_of_pos (by norm_num) _
     positivity
   · intro i hyi hiz
     have hi1 : (1 : ℝ) ≤ (i : ℝ) := by
       have : 1 ≤ i := le_trans (by omega) hyi
       exact_mod_cast this
     have hLimin : (Real.log (z : ℝ)) ^ (0.99 : ℝ) ≤ Real.log (i : ℝ) :=
       log_ge_of_ge_gsCutoff hyi
     refine cheb_regime_at hi1 hB0 hρ ?_
     have hval : (24 : ℝ) * (9 * (2 + Real.log (z : ℝ))) = 216 * (2 + Real.log (z : ℝ)) := by ring
     rw [hval]
     linarith [hcheb, hLimin]

  rwa [nine_mul_gsRho_mul hLz0.le] at hfin

end

end RHTower.Sieve
