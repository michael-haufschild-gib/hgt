import GaloisForLFunctions.HTGeometry.CarrierPoincareCoefficients
import GaloisForLFunctions.HTGeometry.ShellCarrierUniformExpansion

/-!
# The cost of truncating the carrier approximant

The approximant assembled from the factors has degree above the order it is accurate to, so passing
to the genuine order-`m` partial sum discards a tail.  Because every discarded coefficient is a
polynomial in the squared shell variable of degree at most its own order, that tail carries the same
shell growth as the expansion error itself: the order-`m` power of the squared shell variable, times
a constant free of the shell.
-/

open Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Generic

/-- A polynomial of degree at most `j` is bounded by its coefficient mass times the `j`-th power of
the larger of one and the argument. -/
theorem norm_eval_le_of_natDegree_le {Q : Polynomial ℂ} {j : ℕ} (hQ : Q.natDegree ≤ j) (z : ℂ) :
    ‖Q.eval z‖ ≤ polyAbsSum Q * max 1 ‖z‖ ^ j := by
  classical
  have hmax1 : (1 : ℝ) ≤ max 1 ‖z‖ := le_max_left _ _
  have hmaxz : ‖z‖ ≤ max 1 ‖z‖ := le_max_right _ _
  have hmax0 : (0 : ℝ) ≤ max 1 ‖z‖ := by linarith
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  refine le_trans (norm_sum_le _ _) ?_
  rw [polyAbsSum, Finset.sum_mul]
  refine Finset.sum_le_sum fun d hd => ?_
  have hdj : d ≤ j := le_trans (Polynomial.le_natDegree_of_mem_supp d hd) hQ
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖z‖ ^ d ≤ max 1 ‖z‖ ^ d := pow_le_pow_left₀ (norm_nonneg z) hmaxz d
    _ ≤ max 1 ‖z‖ ^ j := pow_le_pow_right₀ hmax1 hdj

/-- Truncating a polynomial below degree `n` costs the order-`n` power of the argument times the
worst weighted tail coefficient, once per degree below the cut-off degree. -/
theorem norm_eval_sub_truncBelow_le_upTo (P : Polynomial ℂ) (n D : ℕ) {r B : ℝ}
    (hn : n < D) (hdeg : P.natDegree < D)
    (hB : ∀ j, n ≤ j → ‖P.coeff j‖ * r ^ (j - n) ≤ B) (hB0 : 0 ≤ B)
    {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖P.eval w - (truncBelow n P).eval w‖ ≤ (D : ℝ) * B * ‖w‖ ^ n := by
  classical
  have hsplit : P.eval w - (truncBelow n P).eval w
      = ∑ j ∈ Finset.Ico n D, P.coeff j * w ^ j := by
    rw [Polynomial.eval_eq_sum_range' hdeg, eval_truncBelow,
      ← Finset.sum_range_add_sum_Ico (fun j => P.coeff j * w ^ j) (le_of_lt hn)]
    ring
  rw [hsplit]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ j ∈ Finset.Ico n D, ‖P.coeff j * w ^ j‖ ≤ B * ‖w‖ ^ n := by
    intro j hj
    have hnj : n ≤ j := (Finset.mem_Ico.mp hj).1
    have hpow : ‖w‖ ^ j = ‖w‖ ^ n * ‖w‖ ^ (j - n) := by
      rw [← pow_add]
      congr 1
      omega
    have hle : ‖w‖ ^ (j - n) ≤ r ^ (j - n) := pow_le_pow_left₀ (norm_nonneg w) hw _
    have hkey := hB j hnj
    rw [norm_mul, norm_pow, hpow]
    have h0 : (0 : ℝ) ≤ ‖w‖ ^ n := pow_nonneg (norm_nonneg w) n
    calc ‖P.coeff j‖ * (‖w‖ ^ n * ‖w‖ ^ (j - n))
        = ‖P.coeff j‖ * ‖w‖ ^ (j - n) * ‖w‖ ^ n := by ring
      _ ≤ ‖P.coeff j‖ * r ^ (j - n) * ‖w‖ ^ n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (norm_nonneg _)) h0
      _ ≤ B * ‖w‖ ^ n := mul_le_mul_of_nonneg_right hkey h0
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hcard : ((D - n : ℕ) : ℝ) ≤ (D : ℝ) := by
    have : (D - n : ℕ) ≤ D := by omega
    exact_mod_cast this
  have h0 : (0 : ℝ) ≤ ‖w‖ ^ n := pow_nonneg (norm_nonneg w) n
  nlinarith [mul_nonneg hB0 h0, mul_le_mul_of_nonneg_right hcard (mul_nonneg hB0 h0)]

end Generic

section Carrier

/-- A degree bound for the carrier approximant, free of the shell variable. -/
def carrierDegBound (a : ℝ) (n m : ℕ) : ℕ := (carrierProductSeries a n m).natDegree + m + 2

/-- The coefficient mass of the Poincaré coefficient polynomials up to the degree bound. -/
def poincareMassSum (a : ℝ) (n m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (carrierDegBound a n m), polyAbsSum (poincareCoeffPoly a n m i)

theorem poincareMassSum_nonneg (a : ℝ) (n m : ℕ) : 0 ≤ poincareMassSum a n m :=
  Finset.sum_nonneg fun _ _ => polyAbsSum_nonneg _

theorem natDegree_carrierProductPoly_lt (a x : ℝ) (n m : ℕ) :
    (carrierProductPoly a x n m).natDegree < carrierDegBound a n m := by
  have h : (carrierProductPoly a x n m).natDegree ≤ (carrierProductSeries a n m).natDegree := by
    rw [← shellEval_carrierProductSeries a n m x, shellEval_apply]
    exact Polynomial.natDegree_map_le
  rw [carrierDegBound]
  omega

theorem norm_ofReal_pow_two (x : ℝ) : ‖((x : ℝ) : ℂ) ^ (2 : ℕ)‖ = x ^ (2 : ℕ) := by
  rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]

theorem shellMax_mul_le {x r c : ℝ} (hr1 : r ≤ 1) (hxc : x ^ (2 : ℕ) * r ≤ c) :
    max 1 (x ^ (2 : ℕ)) * r ≤ max 1 c := by
  rcases le_total (x ^ (2 : ℕ)) 1 with h | h
  · rw [max_eq_left h, one_mul]
    exact le_trans hr1 (le_max_left _ _)
  · rw [max_eq_right h]
    exact le_trans hxc (le_max_right _ _)

theorem norm_coeff_carrierProductPoly_le {a x r c : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hxc : x ^ (2 : ℕ) * r ≤ c) (n m : ℕ) {j : ℕ} (hj : m ≤ j) :
    ‖(carrierProductPoly a x n m).coeff j‖ * r ^ (j - m)
      ≤ poincareMassSum a n m * max 1 c ^ carrierDegBound a n m * max 1 (x ^ (2 : ℕ)) ^ m := by
  classical
  have hxr0 : (0 : ℝ) ≤ x ^ (2 : ℕ) * r := mul_nonneg (sq_nonneg x) hr0
  have hc0 : (0 : ℝ) ≤ c := le_trans hxr0 hxc
  have hmx1 : (1 : ℝ) ≤ max 1 (x ^ (2 : ℕ)) := le_max_left _ _
  have hmc1 : (1 : ℝ) ≤ max 1 c := le_max_left _ _
  have hmxm : (1 : ℝ) ≤ max 1 (x ^ (2 : ℕ)) ^ m := one_le_pow₀ hmx1
  have hmass := poincareMassSum_nonneg a n m
  have hmcD : (0 : ℝ) ≤ max 1 c ^ carrierDegBound a n m := pow_nonneg (by linarith) _
  have hRHS : (0 : ℝ) ≤ poincareMassSum a n m * max 1 c ^ carrierDegBound a n m
      * max 1 (x ^ (2 : ℕ)) ^ m := by positivity
  rcases le_or_gt (carrierDegBound a n m) j with hjD | hjD
  · have hzero : (carrierProductPoly a x n m).coeff j = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_lt_of_le (natDegree_carrierProductPoly_lt a x n m) hjD)
    rw [hzero, norm_zero, zero_mul]
    exact hRHS
  · have hcoeff := coeff_carrierProductPoly a x n m j
    have hdeg : (poincareCoeffPoly a n m j).natDegree ≤ j := natDegree_poincareCoeffPoly_le a n m j
    have hbase := norm_eval_le_of_natDegree_le hdeg (((x : ℝ) : ℂ) ^ (2 : ℕ))
    rw [norm_ofReal_pow_two] at hbase
    have hAj : polyAbsSum (poincareCoeffPoly a n m j) ≤ poincareMassSum a n m := by
      rw [poincareMassSum]
      exact Finset.single_le_sum (fun i _ => polyAbsSum_nonneg _) (Finset.mem_range.mpr hjD)
    have hsplit : max 1 (x ^ (2 : ℕ)) ^ j = max 1 (x ^ (2 : ℕ)) ^ m * max 1 (x ^ (2 : ℕ)) ^ (j - m) := by
      rw [← pow_add]
      congr 1
      omega
    have htail : max 1 (x ^ (2 : ℕ)) ^ (j - m) * r ^ (j - m) ≤ max 1 c ^ carrierDegBound a n m := by
      rw [← mul_pow]
      refine le_trans (pow_le_pow_left₀ (mul_nonneg (by linarith) hr0)
        (shellMax_mul_le hr1 hxc) (j - m)) ?_
      exact pow_le_pow_right₀ hmc1 (by omega)
    rw [hcoeff]
    calc ‖(poincareCoeffPoly a n m j).eval (((x : ℝ) : ℂ) ^ (2 : ℕ))‖ * r ^ (j - m)
        ≤ polyAbsSum (poincareCoeffPoly a n m j) * max 1 (x ^ (2 : ℕ)) ^ j * r ^ (j - m) :=
          mul_le_mul_of_nonneg_right hbase (pow_nonneg hr0 _)
      _ = polyAbsSum (poincareCoeffPoly a n m j) * max 1 (x ^ (2 : ℕ)) ^ m
            * (max 1 (x ^ (2 : ℕ)) ^ (j - m) * r ^ (j - m)) := by rw [hsplit]; ring
      _ ≤ polyAbsSum (poincareCoeffPoly a n m j) * max 1 (x ^ (2 : ℕ)) ^ m
            * max 1 c ^ carrierDegBound a n m := by
          refine mul_le_mul_of_nonneg_left htail ?_
          exact mul_nonneg (polyAbsSum_nonneg _) (by linarith)
      _ ≤ poincareMassSum a n m * max 1 (x ^ (2 : ℕ)) ^ m * max 1 c ^ carrierDegBound a n m := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAj (by linarith)) hmcD
      _ = poincareMassSum a n m * max 1 c ^ carrierDegBound a n m * max 1 (x ^ (2 : ℕ)) ^ m := by ring

/-- The shell-free constant of the truncated carrier expansion. -/
def carrierTruncConst (a c : ℝ) (n m : ℕ) : ℝ :=
  carrierShellConst a c n m * (1 + (a * cbinomAbsCoeff ((1 : ℝ) / 2) 1) ^ m)
    + (carrierDegBound a n m : ℝ)
      * (poincareMassSum a n m * max 1 c ^ carrierDegBound a n m)

theorem one_le_carrierShellConst {a c : ℝ} (hc : 0 ≤ c) (n m : ℕ) :
    1 ≤ carrierShellConst a c n m := by
  have key : ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → 1 ≤ u * v := fun u v hu hv => by nlinarith
  have hpc : 1 ≤ poincareFactorConst a c n m := by
    rw [poincareFactorConst]
    have : (0 : ℝ) ≤ ∑ k ∈ Finset.range n,
        3 * (max 1 ‖((besselK1Coeff k : ℝ) : ℂ) * ((a : ℂ)⁻¹) ^ k‖ * 1)
          * shellPowConst (-(k : ℝ) / 2) c m := by
      refine Finset.sum_nonneg fun k _ => ?_
      have h1 : (0 : ℝ) ≤ max 1 ‖((besselK1Coeff k : ℝ) : ℂ) * ((a : ℂ)⁻¹) ^ k‖ * 1 := by
        have := le_max_left (1 : ℝ) ‖((besselK1Coeff k : ℝ) : ℂ) * ((a : ℂ)⁻¹) ^ k‖
        linarith
      have h2 : (0 : ℝ) ≤ shellPowConst (-(k : ℝ) / 2) c m := by
        linarith [one_le_shellPowConst (α := (-(k : ℝ) / 2)) hc m]
      positivity
    linarith
  rw [carrierShellConst]
  refine key _ _ (key _ _ (key _ _ (key _ _ (by norm_num) ?_) ?_) hpc) ?_
  · exact key _ _ (le_max_left _ _) (one_le_shellPowConst hc m)
  · exact one_le_shellPowConst hc m
  · exact le_trans (by norm_num) (le_max_left (2 : ℝ) (defectExpConst a c m))

/-- **The carrier profile against its genuine order-`m` partial sum, uniformly over the shell.** -/
theorem norm_shellCarrierProfile_sub_trunc_le {a x r c : ℝ} (ha : 0 ≤ a) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hxr : x ^ (2 : ℕ) * r ^ (2 : ℕ) ≤ 1 / 2) (hxc : x ^ (2 : ℕ) * r ≤ c)
    (hdef : a * shellDefectRate x * r ≤ 1 / 2) (n m : ℕ) {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖shellCarrierProfile a x n w - (truncBelow m (carrierProductPoly a x n m)).eval w‖
      ≤ carrierTruncConst a c n m * max 1 (x ^ (2 : ℕ)) ^ m * ‖w‖ ^ m := by
  have hxr0 : (0 : ℝ) ≤ x ^ (2 : ℕ) * r := mul_nonneg (sq_nonneg x) hr0
  have hc0 : (0 : ℝ) ≤ c := le_trans hxr0 hxc
  have hcb1 : (0 : ℝ) ≤ cbinomAbsCoeff ((1 : ℝ) / 2) 1 := cbinomAbsCoeff_nonneg _ _
  have hmx1 : (1 : ℝ) ≤ max 1 (x ^ (2 : ℕ)) := le_max_left _ _
  have hmxm : (1 : ℝ) ≤ max 1 (x ^ (2 : ℕ)) ^ m := one_le_pow₀ hmx1
  have hw0 : (0 : ℝ) ≤ ‖w‖ ^ m := pow_nonneg (norm_nonneg w) m
  have hone := one_le_carrierShellConst (a := a) hc0 n m
  have hK : a * shellDefectRate x = a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 * x ^ (2 : ℕ) := by
    rw [shellDefectRate, sq_abs]
    ring
  have hKle : (a * shellDefectRate x) ^ m
      ≤ (a * cbinomAbsCoeff ((1 : ℝ) / 2) 1) ^ m * max 1 (x ^ (2 : ℕ)) ^ m := by
    rw [hK, mul_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sq_nonneg x) (le_max_right 1 (x ^ (2 : ℕ))) m)
      (pow_nonneg (mul_nonneg ha hcb1) m)
  have hstep1 : carrierShellConst a c n m * (1 + (a * shellDefectRate x) ^ m)
      ≤ carrierShellConst a c n m * (1 + (a * cbinomAbsCoeff ((1 : ℝ) / 2) 1) ^ m)
        * max 1 (x ^ (2 : ℕ)) ^ m := by
    have h1 : 1 + (a * shellDefectRate x) ^ m
        ≤ (1 + (a * cbinomAbsCoeff ((1 : ℝ) / 2) 1) ^ m) * max 1 (x ^ (2 : ℕ)) ^ m := by
      have hexp : (1 + (a * cbinomAbsCoeff ((1 : ℝ) / 2) 1) ^ m) * max 1 (x ^ (2 : ℕ)) ^ m
          = max 1 (x ^ (2 : ℕ)) ^ m
            + (a * cbinomAbsCoeff ((1 : ℝ) / 2) 1) ^ m * max 1 (x ^ (2 : ℕ)) ^ m := by ring
      rw [hexp]
      linarith
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ carrierShellConst a c n m)
    calc carrierShellConst a c n m * (1 + (a * shellDefectRate x) ^ m)
        ≤ carrierShellConst a c n m
            * ((1 + (a * cbinomAbsCoeff ((1 : ℝ) / 2) 1) ^ m) * max 1 (x ^ (2 : ℕ)) ^ m) := this
      _ = carrierShellConst a c n m * (1 + (a * cbinomAbsCoeff ((1 : ℝ) / 2) 1) ^ m)
            * max 1 (x ^ (2 : ℕ)) ^ m := by ring
  have hmain : ‖shellCarrierProfile a x n w - (carrierProductPoly a x n m).eval w‖
      ≤ carrierShellConst a c n m * (1 + (a * shellDefectRate x) ^ m) * ‖w‖ ^ m :=
    (bddExpS_shellCarrierProfile ha hr0 hr1 hxr hxc hdef n m).2.2 w hw
  have hB0 : (0 : ℝ) ≤ poincareMassSum a n m * max 1 c ^ carrierDegBound a n m
      * max 1 (x ^ (2 : ℕ)) ^ m :=
    mul_nonneg (mul_nonneg (poincareMassSum_nonneg a n m)
      (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)) (by linarith)
  have htail := norm_eval_sub_truncBelow_le_upTo (carrierProductPoly a x n m) m
    (carrierDegBound a n m) (by rw [carrierDegBound]; omega)
    (natDegree_carrierProductPoly_lt a x n m)
    (fun j hj => norm_coeff_carrierProductPoly_le hr0 hr1 hxc n m hj) hB0 hw
  calc ‖shellCarrierProfile a x n w - (truncBelow m (carrierProductPoly a x n m)).eval w‖
      ≤ ‖shellCarrierProfile a x n w - (carrierProductPoly a x n m).eval w‖
        + ‖(carrierProductPoly a x n m).eval w
            - (truncBelow m (carrierProductPoly a x n m)).eval w‖ := by
        have h := norm_add_le (shellCarrierProfile a x n w - (carrierProductPoly a x n m).eval w)
          ((carrierProductPoly a x n m).eval w
            - (truncBelow m (carrierProductPoly a x n m)).eval w)
        simpa using h
    _ ≤ carrierShellConst a c n m * (1 + (a * cbinomAbsCoeff ((1 : ℝ) / 2) 1) ^ m)
          * max 1 (x ^ (2 : ℕ)) ^ m * ‖w‖ ^ m
        + (carrierDegBound a n m : ℝ)
          * (poincareMassSum a n m * max 1 c ^ carrierDegBound a n m * max 1 (x ^ (2 : ℕ)) ^ m)
          * ‖w‖ ^ m :=
        add_le_add (le_trans hmain (mul_le_mul_of_nonneg_right hstep1 hw0)) htail
    _ = carrierTruncConst a c n m * max 1 (x ^ (2 : ℕ)) ^ m * ‖w‖ ^ m := by
        rw [carrierTruncConst]
        ring

end Carrier

end

end GaloisForLFunctions.HTGeometry
