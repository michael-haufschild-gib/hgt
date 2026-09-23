import GaloisForLFunctions.RHTower.Sieve.ConstQuotientLimit
import GaloisForLFunctions.RHTower.Sieve.BudgetTermSplit
import GaloisForLFunctions.RHTower.Sieve.ShortIntervalLength

/-!
# The normalised spectral budget

The whole budget of the designated fibre, divided by the square of the harmonic mass, the square of
the window length and the square root of the outer scale, vanishes.  This is the short-interval mean
square for the Möbius function.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

set_option maxHeartbeats 400000 in
/-- **The normalised spectral budget vanishes.** -/
theorem tendsto_normalised_omegaBudget {β γ : ℝ} (hβ0 : 9 / 10 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ0 : 9 / 10 < γ * β) (hγβ1 : γ * β < 1) :
    Tendsto (fun x : ℝ =>
        omegaBudget x (cardLength β x) (siftStart (γ * β) x) (ladderTop β γ x)
          / ((mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ (2 : ℕ)
            * (cardLength β x) ^ (2 : ℕ) * Real.sqrt x)) atTop (𝓝 0) := by
  have hβ0' : (0 : ℝ) < β := by linarith
  obtain ⟨A, delta, Ctot, hdelta, hCtot, hbound⟩ :=
    exists_eventually_omegaBudget_le (β := β) (γ := γ) hβ0' hβ1 hγ0 hγ1 hγβ1
  have hslope := tendsto_slope_quotient (A := A) (delta := delta) (Ctot := Ctot)
    hβ0 hβ1 hγ0 hγ1 hγβ0 hγβ1 hCtot.le hdelta
  have henergy := tendsto_energy_quotient (β := β) (γ := γ) hβ0' hβ1 hγ0 hγ1 hγβ1
  have hconst := tendsto_const_quotient (A := A) (delta := delta) (Ctot := Ctot)
    hβ0 hβ1 hγ0 hγ1 hγβ0 hγβ1 hCtot.le hdelta
  have hns := tendsto_nonSpectralBudget (β := β) (γ := γ) hβ0' hβ1 hγ0 hγ1 hγβ1
  have hmaj := (((hslope.const_mul (136 : ℝ)).add (henergy.const_mul (140 : ℝ))).add
    (hconst.const_mul (131 : ℝ))).add hns
  rw [show (136 : ℝ) * 0 + 140 * 0 + 131 * 0 + 0 = 0 by ring] at hmaj
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [(tendsto_ladderMass hβ0' hγ0 hγ1 hγβ1).eventually_ge_atTop (1 : ℝ),
      Filter.eventually_gt_atTop (1 : ℝ)] with x hW hx1
    have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hnum : (0 : ℝ) ≤ omegaBudget x (cardLength β x) (siftStart (γ * β) x)
        (ladderTop β γ x) := by
      rw [omegaBudget]
      have hint : (0 : ℝ) ≤ ∫ w : ℝ,
          ‖logWindowKernel (fibreWidth x (cardLength β x)) w‖ ^ (2 : ℕ)
            * ‖omegaWeightedMoebiusPoly (primesRange (siftStart (γ * β) x) (ladderTop β γ x))
                (fibreIndex x (cardLength β x)) w‖ ^ (2 : ℕ) :=
        MeasureTheory.integral_nonneg fun w => by positivity
      have hm : (0 : ℝ) ≤ mertensS (ladderTop β γ x) := mertensS_nonneg' _
      have hsx0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
      have hpc : (0 : ℝ) ≤ ((Nat.primesLE (ladderTop β γ x)).card : ℝ) := Nat.cast_nonneg _
      have t1 : (0 : ℝ) ≤ 16 * Real.sqrt x * (∫ w : ℝ,
          ‖logWindowKernel (fibreWidth x (cardLength β x)) w‖ ^ (2 : ℕ)
            * ‖omegaWeightedMoebiusPoly (primesRange (siftStart (γ * β) x) (ladderTop β γ x))
                (fibreIndex x (cardLength β x)) w‖ ^ (2 : ℕ)) :=
        mul_nonneg (by linarith) hint
      have t2 : (0 : ℝ) ≤ 204
          * (((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ) + 1) ^ (2 : ℕ)
          * (Real.sqrt x + 1) :=
        mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith)
      have t3 : (0 : ℝ) ≤ 2 * (cardLength β x + 1) * (2 * cardLength β x + 1)
          * (4 * (Real.sqrt x / 2 + cardLength β x + 1) * mertensS (ladderTop β γ x)
            + 4 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ)
            + 8 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ) ^ (2 : ℕ)) := by
        refine mul_nonneg (mul_nonneg (by linarith) (by linarith)) ?_
        have a1 : (0 : ℝ) ≤ 4 * (Real.sqrt x / 2 + cardLength β x + 1)
            * mertensS (ladderTop β γ x) := mul_nonneg (by linarith) hm
        nlinarith [a1, hpc, sq_nonneg ((Nat.primesLE (ladderTop β γ x)).card : ℝ)]
      linarith [t1, t2, t3]
    have hden : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ (2 : ℕ)
        * (cardLength β x) ^ (2 : ℕ) * Real.sqrt x := by
      have : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ (2 : ℕ) := by
        nlinarith [hW]
      exact mul_pos (mul_pos this (pow_pos hh0 2)) hsx
    exact div_nonneg hnum hden.le
  · filter_upwards [hbound, Filter.eventually_gt_atTop (1 : ℝ),
      (tendsto_ladderMass hβ0' hγ0 hγ1 hγβ1).eventually_ge_atTop (1 : ℝ),
      (tendsto_cardLength hβ0').eventually_ge_atTop (1 : ℝ),
      eventually_budgetB_le hβ0' hβ1, eventually_le_siftStart (mul_pos hγ0 hβ0') 2,
      Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1)
        (tendsto_ladderEta (β := β) (γ := γ) hβ0' hγβ1)]
      with x hb hx1 hW hh1 hB2 hQ2 hη1
    have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
    have hQ2R : (2 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ2
    have hh0 : (0 : ℝ) < cardLength β x := by linarith
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hBsx : Real.sqrt x ≤ ((budgetB β x : ℕ) : ℝ) := sqrt_le_budgetB (β := β) x hh1
    have hB0 : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) := by linarith
    have hden : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ (2 : ℕ)
        * (cardLength β x) ^ (2 : ℕ) * Real.sqrt x := by
      have : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ (2 : ℕ) := by
        nlinarith [hW]
      exact mul_pos (mul_pos this (pow_pos hh0 2)) hsx
    refine (div_le_div_of_nonneg_right hb hden.le).trans ?_
    -- rearrange the denominator into the split form
    have hdenperm : (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ (2 : ℕ)
          * (cardLength β x) ^ (2 : ℕ) * Real.sqrt x
        = (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ (2 : ℕ)
          * (cardLength β x) ^ (2 : ℕ) * Real.sqrt x := rfl
    rw [hdenperm, budget_div_eq (sx := Real.sqrt x) (h := cardLength β x)
      (W := mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x))
      (G := gallagherCut β x) (T0 := budgetT β x) (δ := fibreWidth x (cardLength β x))
      (αL := ladderAffineSlope (ladderSteps β γ x) (budgetB β x)
        ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x) (budgetRho A delta Ctot β γ x))
      (βL := ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x) (ladderSteps β γ x)
        (budgetB β x) ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
        (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x))
      (Ec := ∑ n ∈ Finset.Icc 1 (budgetB β x),
        ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ (2 : ℕ))
      (B0 := ((budgetB β x : ℕ) : ℝ)) hsx (by nlinarith [hW]) hh0
      (by
        rw [show gallagherCut β x = ((budgetB β x : ℕ) : ℝ) / cardLength β x from rfl]
        exact div_pos hB0 hh0)]
    have hGdef : gallagherCut β x = ((budgetB β x : ℕ) : ℝ) / cardLength β x := rfl
    have hGh : gallagherCut β x * cardLength β x = ((budgetB β x : ℕ) : ℝ) := by
      rw [hGdef]
      field_simp
    have hG0 : (0 : ℝ) < gallagherCut β x := by
      rw [hGdef]
      exact div_pos hB0 hh0
    have hδ0 : (0 : ℝ) ≤ fibreWidth x (cardLength β x) := by
      rw [fibreWidth]
      refine Real.log_nonneg ?_
      have : (0 : ℝ) ≤ cardLength β x / Real.sqrt x := div_nonneg hh0.le hsx.le
      linarith
    have hδle : fibreWidth x (cardLength β x) ≤ cardLength β x / Real.sqrt x := by
      rw [fibreWidth]
      have hu : (0 : ℝ) ≤ cardLength β x / Real.sqrt x := div_nonneg hh0.le hsx.le
      have := Real.log_le_sub_one_of_pos (by linarith :
        (0:ℝ) < 1 + cardLength β x / Real.sqrt x)
      linarith
    have hspec := spectral_terms_le (sx := Real.sqrt x) (h := cardLength β x)
      (W := mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x))
      (G := gallagherCut β x) (T0 := budgetT β x) (δ := fibreWidth x (cardLength β x))
      (αL := ladderAffineSlope (ladderSteps β γ x) (budgetB β x)
        ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x) (budgetRho A delta Ctot β γ x))
      (βL := ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x) (ladderSteps β γ x)
        (budgetB β x) ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
        (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x))
      (Ec := ∑ n ∈ Finset.Icc 1 (budgetB β x),
        ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ (2 : ℕ))
      (B0 := ((budgetB β x : ℕ) : ℝ)) hsx hW hh1 hB0
      hδ0 hδle hGh hG0 rfl
      (by nlinarith [hB2, hB0, Real.sq_sqrt (by linarith : (0:ℝ) ≤ x)])
      (ladderAffineSlope_nonneg (by linarith) hη.le)
      (ladderAffineConst_nonneg (by linarith) hη.le)
      (Finset.sum_nonneg fun n _ => sq_nonneg _)
    have e1 : (136 : ℝ) * ladderAffineSlope (ladderSteps β γ x) (budgetB β x)
          ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x) (budgetRho A delta Ctot β γ x)
          / (((budgetB β x : ℕ) : ℝ) * cardLength β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ (2 : ℕ))
        = 136 * (ladderAffineSlope (ladderSteps β γ x) (budgetB β x)
            ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x) (budgetRho A delta Ctot β γ x)
          / (((budgetB β x : ℕ) : ℝ) * cardLength β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ (2 : ℕ))) := by
      ring
    have e2 : (140 : ℝ) * (∑ n ∈ Finset.Icc 1 (budgetB β x),
            ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ (2 : ℕ))
          / (((budgetB β x : ℕ) : ℝ) * cardLength β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ (2 : ℕ))
        = 140 * ((∑ n ∈ Finset.Icc 1 (budgetB β x),
            ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ (2 : ℕ))
          / (((budgetB β x : ℕ) : ℝ) * cardLength β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ (2 : ℕ))) := by
      ring
    have e3 : (131 : ℝ) * ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x)
          (ladderSteps β γ x) (budgetB β x) ((siftStart (γ * β) x : ℕ) : ℝ)
          (ladderEta β γ x) (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x)
          / (((budgetB β x : ℕ) : ℝ) ^ (2 : ℕ)
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ (2 : ℕ))
        = 131 * (ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x)
            (ladderSteps β γ x) (budgetB β x) ((siftStart (γ * β) x : ℕ) : ℝ)
            (ladderEta β γ x) (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x)
          / (((budgetB β x : ℕ) : ℝ) ^ (2 : ℕ)
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ (2 : ℕ))) := by
      ring
    linarith [hspec, e1, e2, e3]

end

end RHTower.Sieve
