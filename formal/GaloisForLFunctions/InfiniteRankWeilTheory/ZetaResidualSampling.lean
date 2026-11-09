import GaloisForLFunctions.InfiniteRankWeilTheory.ResidualSamplingCancellation
import GaloisForLFunctions.InfiniteRankWeilTheory.ZetaSamplingDimension
import GaloisForLFunctions.RHTower.WeilLagFunctionOmega

/-!+# Actual Weil lag has residual cancellation bases

Unconditional oscillation and continuity give arbitrarily large zeros of the actual Weil lag.
Consequently every countable family of positive sampling accuracies has a residual set of bases.
A single residual set gives recurrence at every real exponential rate; if AAL fails, its positive
part has Hausdorff dimension zero. Topological size alone therefore imposes no arithmetic bound.
-/

open Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

private theorem continuous_actualLag : Continuous RHTower.weilLagFunctionReal :=
  Complex.continuous_re.comp RHTower.continuous_weilLagFunction_unconditional

/-- The actual Weil lag has zeros beyond every real threshold, unconditionally. -/
theorem exists_actualLag_zero_ge (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ RHTower.weilLagFunctionReal t = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp T)
  obtain ⟨n, hn, hpos⟩ := frequently_atTop.mp
    (RHTower.frequently_integerLag_gt (RHTower.poleSharpConstant / 2)
      (half_pos RHTower.poleSharpConstant_pos)) N
  have hnexp : Real.exp T < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
  have hn0 : 0 < (n : ℝ) := (Real.exp_pos T).trans hnexp
  have hT : T ≤ Real.log n := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos T) hnexp.le
  obtain ⟨η, hη, hneg⟩ := RHTower.frequently_integerLag_le_neg
  obtain ⟨m, hm, hnegm⟩ := frequently_atTop.mp hneg n
  have hnm : Real.log n ≤ Real.log m := Real.log_le_log hn0 (by exact_mod_cast hm)
  have hpn : 0 ≤ RHTower.weilLagFunctionReal (Real.log n) := by
    change RHTower.poleSharpConstant - RHTower.poleSharpConstant / 2 <
      RHTower.weilLagFunctionReal (Real.log n) at hpos
    linarith only [hpos, RHTower.poleSharpConstant_pos]
  have hnmval : RHTower.weilLagFunctionReal (Real.log m) ≤ 0 :=
    hnegm.trans (neg_nonpos.mpr hη.le)
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc' hnm continuous_actualLag.continuousOn
    (show (0 : ℝ) ∈ Icc (RHTower.weilLagFunctionReal (Real.log m))
      (RHTower.weilLagFunctionReal (Real.log n)) from ⟨hnmval, hpn⟩)
  exact ⟨t, hT.trans ht.1, hzero⟩

/-- Every positive accuracy family is attained recurrently on a dense G-delta of actual lag
sampling bases, with no RH or abscissa-law assumption. -/
theorem actualLag_samplingCancellation_residual {ε : ℕ → ℕ → ℝ}
    (hε : ∀ m n, 0 < ε m n) :
    IsGδ (samplingCancellationBases RHTower.weilLagFunctionReal ε) ∧
      Dense (samplingCancellationBases RHTower.weilLagFunctionReal ε) ∧
      samplingCancellationBases RHTower.weilLagFunctionReal ε ∈ residual ℝ := by
  have hg := isGδ_samplingCancellationBases continuous_actualLag ε
  have hd := dense_samplingCancellationBases continuous_actualLag
    RHTower.weilLagFunctionReal_neg exists_actualLag_zero_ge hε
  exact ⟨hg, hd, residual_of_dense_Gδ hg hd⟩

/-- A common set of bases for cancellations at every integer exponential decay rate. -/
def lagRapidCancellationBases : Set ℝ :=
  samplingCancellationBases RHTower.weilLagFunctionReal
    (fun m n => Real.exp (-((m : ℝ) + 1) * (n : ℝ)))

theorem lagRapidCancellationBases_residual :
    IsGδ lagRapidCancellationBases ∧ Dense lagRapidCancellationBases ∧
      lagRapidCancellationBases ∈ residual ℝ :=
  actualLag_samplingCancellation_residual (fun _ _ => Real.exp_pos _)

/-- The actual rapid cancellation bases are uncountable in every nonempty open interval. -/
theorem not_countable_lagRapidCancellationBases_inter_Ioo {a b : ℝ} (hab : a < b) :
    ¬ (lagRapidCancellationBases ∩ Ioo a b).Countable :=
  not_countable_inter_Ioo_of_dense_isGδ lagRapidCancellationBases_residual.1
    lagRapidCancellationBases_residual.2.1 hab

/-- Every positive base in the same residual set has recurrence at every real rate, with
constant one. -/
theorem lagRapidCancellationBases_recurrence {ℓ : ℝ} (hℓ : ℓ ∈ lagRapidCancellationBases)
    (a : ℝ) : ∃ᶠ n : ℕ in atTop,
      ‖RHTower.weilLagFunction ((n : ℝ) * ℓ)‖ ≤ Real.exp (a * (n : ℝ) * ℓ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (-a * ℓ)
  have hsmall := mem_samplingCancellationBases_iff.mp hℓ m
  refine hsmall.mono fun n hn => ?_
  rw [RHTower.weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
  refine hn.le.trans (Real.exp_le_exp.mpr ?_)
  have hrate : -((m : ℝ) + 1) ≤ a * ℓ := by linarith only [hm]
  have h := mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith only [h]

/-- Actual zeta already has one residual family with recurrent readings at every real rate.
Thus this topological recurrence property supplies no additional arithmetic restriction. -/
theorem exists_residual_actualLag_recurrence_all_rates :
    ∃ S : Set ℝ, IsGδ S ∧ Dense S ∧ S ∈ residual ℝ ∧
      ∀ ℓ ∈ S, ∀ a : ℝ, ∃ᶠ n : ℕ in atTop,
        ‖RHTower.weilLagFunction ((n : ℝ) * ℓ)‖ ≤ Real.exp (a * (n : ℝ) * ℓ) :=
  ⟨lagRapidCancellationBases, lagRapidCancellationBases_residual.1,
    lagRapidCancellationBases_residual.2.1, lagRapidCancellationBases_residual.2.2,
    fun _ hℓ a => lagRapidCancellationBases_recurrence hℓ a⟩

/-- If AAL fails, actual rapid cancellation is residual but zero-dimensional on positive bases. -/
theorem dimH_positive_lagRapidCancellationBases_eq_zero_of_not_asymptoticAbscissaLaw
    (hnot : ¬ RHTower.AsymptoticAbscissaLaw) :
    dimH (lagRapidCancellationBases ∩ Ioi 0) = 0 := by
  have hsub : lagRapidCancellationBases ∩ Ioi 0 ⊆ lagRecurrenceBases (-1) := by
    rintro ℓ ⟨hℓ, hℓ0⟩
    exact ⟨hℓ0, 1, by simpa only [one_mul] using lagRapidCancellationBases_recurrence hℓ (-1)⟩
  have htop := (not_asymptoticAbscissaLaw_implies_metric_top_detection hnot).1
  have hd := dimH_lagRecurrenceBases_eq_zero_of_not_asymptoticAbscissaLaw hnot
    (a := -1) (by linarith only [htop])
  exact le_antisymm ((dimH_mono hsub).trans_eq hd) bot_le

#print axioms exists_actualLag_zero_ge
#print axioms actualLag_samplingCancellation_residual
#print axioms lagRapidCancellationBases_recurrence
#print axioms exists_residual_actualLag_recurrence_all_rates
#print axioms dimH_positive_lagRapidCancellationBases_eq_zero_of_not_asymptoticAbscissaLaw

end GaloisForLFunctions.InfiniteRankWeilTheory
