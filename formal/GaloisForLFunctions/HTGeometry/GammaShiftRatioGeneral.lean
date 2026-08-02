import GaloisForLFunctions.HTGeometry.GammaShiftRatioAsymptotic
import GaloisForLFunctions.HTGeometry.GammaShiftDatumAlgebra

/-!
# Equation (14) for shifts of either sign

The card's shifts are arbitrary reals; only the line has to stay in the right half plane.  The
positive case is the integrated digamma; the negative case follows from it by exchanging the two
abscissas, at the cost of comparing two real powers whose bases differ by a real constant — and
those agree asymptotically, because both logarithms are `log t + iπ/2 + o(1)`.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Two vertical lines give the same real power asymptotically. -/
theorem tendsto_cpow_vertical_ratio (σ σ' : ℝ) (lam : ℝ) :
    Tendsto (fun t : ℝ => ((σ' : ℂ) + (t : ℂ) * Complex.I) ^ (lam : ℂ)
      / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (lam : ℂ)) atTop (nhds 1) := by
  have hdiff : Tendsto (fun t : ℝ => (lam : ℂ)
      * (Complex.log ((σ' : ℂ) + (t : ℂ) * Complex.I)
        - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I))) atTop (nhds 0) := by
    have h1 := tendsto_log_vertical_sub_vertLog σ'
    have h2 := tendsto_log_vertical_sub_vertLog σ
    have hsub := h1.sub h2
    rw [sub_zero] at hsub
    have hmul := (tendsto_const_nhds (x := (lam : ℂ))).mul hsub
    rw [mul_zero] at hmul
    refine hmul.congr fun t => ?_
    ring
  have hexp := (Complex.continuous_exp.tendsto (0 : ℂ)).comp hdiff
  rw [Complex.exp_zero] at hexp
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := vertical_ne_zero_of_pos (σ := σ) ht
  have hs' : ((σ' : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := vertical_ne_zero_of_pos (σ := σ') ht
  show Complex.exp ((lam : ℂ) * (Complex.log ((σ' : ℂ) + (t : ℂ) * Complex.I)
      - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)))
    = ((σ' : ℂ) + (t : ℂ) * Complex.I) ^ (lam : ℂ)
      / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (lam : ℂ)
  rw [Complex.cpow_def_of_ne_zero hs, Complex.cpow_def_of_ne_zero hs', ← Complex.exp_sub]
  ring_nf

/-- **Equation (14) for a shift of either sign.**  As long as the shifted line stays in the right
half plane, the ratio of the two translates is the real power of the argument. -/
theorem tendsto_gammaShift_ratio_general {σ lam : ℝ} (hσ : 0 < σ) (hσlam : 0 < σ + lam) :
    Tendsto (fun t : ℝ => gammaLine (σ + lam) t
      / (gammaLine σ t * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (lam : ℂ))) atTop (nhds 1) := by
  rcases le_or_gt 0 lam with hpos | hneg
  · exact tendsto_gammaShift_ratio hσ hpos
  · -- exchange the two abscissas
    have hmu : 0 ≤ -lam := by linarith
    have hbase := tendsto_gammaShift_ratio (σ := σ + lam) hσlam hmu
    have hval : σ + lam + -lam = σ := by ring
    rw [hval] at hbase
    have hbase' : Tendsto (fun t : ℝ =>
        (gammaLine (σ + lam) t
          * ((((σ + lam : ℝ)) : ℂ) + (t : ℂ) * Complex.I) ^ ((-lam : ℝ) : ℂ))
          / gammaLine σ t) atTop (nhds 1) := by
      have hinv := hbase.inv₀ one_ne_zero
      rw [inv_one] at hinv
      refine hinv.congr fun t => ?_
      rw [inv_div]
    have hratio := hbase'.mul (tendsto_cpow_vertical_ratio σ (σ + lam) lam)
    rw [one_mul] at hratio
    refine hratio.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := vertical_ne_zero_of_pos (σ := σ) ht
    have hs' : ((((σ + lam : ℝ)) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
      vertical_ne_zero_of_pos (σ := σ + lam) ht
    have hΓ : gammaLine σ t ≠ 0 := gammaLine_ne_zero hσ t
    have hcancel : ((((σ + lam : ℝ)) : ℂ) + (t : ℂ) * Complex.I) ^ ((-lam : ℝ) : ℂ)
        * ((((σ + lam : ℝ)) : ℂ) + (t : ℂ) * Complex.I) ^ (lam : ℂ) = 1 := by
      rw [← Complex.cpow_add _ _ hs']
      norm_num
    have hpowne : ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (lam : ℂ) ≠ 0 :=
      cpow_real_vertical_ne_zero (σ := σ) ht
    field_simp
    calc gammaLine (σ + lam) t
          * ((((σ + lam : ℝ)) : ℂ) + (t : ℂ) * Complex.I) ^ ((-lam : ℝ) : ℂ)
          * ((((σ + lam : ℝ)) : ℂ) + (t : ℂ) * Complex.I) ^ (lam : ℂ)
        = gammaLine (σ + lam) t
          * (((((σ + lam : ℝ)) : ℂ) + (t : ℂ) * Complex.I) ^ ((-lam : ℝ) : ℂ)
            * ((((σ + lam : ℝ)) : ℂ) + (t : ℂ) * Complex.I) ^ (lam : ℂ)) := by ring
      _ = gammaLine (σ + lam) t := by rw [hcancel, mul_one]

/-- **The shifted Gamma has datum `(1, λ, 0)` for a shift of either sign.** -/
theorem hasShiftDatum_gammaShift_general {σ lam : ℝ} (hσ : 0 < σ) (hσlam : 0 < σ + lam) :
    HasShiftDatum 0 σ (fun t => gammaLine (σ + lam) t) 1 lam 0 1 := by
  refine ⟨one_ne_zero, ?_⟩
  refine (tendsto_gammaShift_ratio_general hσ hσlam).congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with t ht
  refine congrArg (fun w => gammaLine (σ + lam) t / w) ?_
  rw [gammaShiftShape, add_zero, zpow_one, zpow_zero, mul_one]

end

end GaloisForLFunctions.HTGeometry
