import GaloisForLFunctions.RHTower.ZetaLogDerivSharpLandau

/-!
# The companion bound: keeping the zero's own resolvent term

`neg_re_logDeriv_riemannZeta_le` drops the completed logarithmic derivative entirely.  Keeping one
zero's resolvent term costs nothing, because the reflection-paired partial fraction is a series of
nonnegative terms and the pair `{q, reflect q}` contributes `2·(s.re − β)/|s − ρ|²` whether or not
the two copies coincide.  The result is the sharp form needed by the three-four-one step:

```text
−Re (ζ'/ζ)(σ + it) ≤ 1/5 + log t + C − (σ − β)/|s − ρ|² .
```

At `t = γ` and `ρ = β + iγ` the subtracted term is exactly `1/(σ − β)`, with coefficient one: a
factor `2` there would make the de la Vallée Poussin bracket `2/(c₀+c) − 3/c₀` negative for every
`c₀`, so the pairing must be handled without loss.
-/

open Complex GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Every paired resolvent term is nonnegative right of the strip. -/
theorem xiPairedResolventTerm_nonneg {s : ℂ} (h1 : 1 ≤ s.re) (q : XiZeroCopy) :
    0 ≤ xiPairedResolventTerm s q := by
  have hu0 := xiZeroCopy_re_pos q
  have hu1 := xiZeroCopy_re_lt_one q
  unfold xiPairedResolventTerm
  have hA : 0 ≤ (s.re - (q.1 : ℂ).re) / Complex.normSq (s - (q.1 : ℂ)) :=
    div_nonneg (by linarith) (Complex.normSq_nonneg _)
  have hB : 0 ≤ (s.re - (1 - (q.1 : ℂ).re)) / Complex.normSq (s - (1 - (q.1 : ℂ))) :=
    div_nonneg (by linarith) (Complex.normSq_nonneg _)
  linarith

/-- The zero of a reflected copy is the reflected zero. -/
theorem coe_xiZeroCopyReflect (q : XiZeroCopy) :
    (((xiZeroCopyReflectEquiv q).1 : XiDivisorSupport) : ℂ)
      = 1 - ((q.1 : XiDivisorSupport) : ℂ) := rfl

/-- Reflection permutes the two halves of a paired resolvent term. -/
theorem xiPairedResolventTerm_reflect (s : ℂ) (q : XiZeroCopy) :
    xiPairedResolventTerm s (xiZeroCopyReflectEquiv q) = xiPairedResolventTerm s q := by
  unfold xiPairedResolventTerm
  rw [coe_xiZeroCopyReflect]
  have h1 : ((1 : ℂ) - (q.1 : ℂ)).re = 1 - (q.1 : ℂ).re := by simp
  have h2 : (1 : ℂ) - (1 - (q.1 : ℂ)) = (q.1 : ℂ) := by ring
  rw [h1, h2]
  have h3 : (1 : ℝ) - (1 - (q.1 : ℂ).re) = (q.1 : ℂ).re := by ring
  rw [h3]
  ring

/-- **One zero's resolvent term is dominated by `Re (ξ'/ξ)`,** with no loss from the pairing. -/
theorem resolventTerm_le_re_logDeriv_xi {s : ℂ} (hs : xi s ≠ 0) (h1 : 1 ≤ s.re)
    (q₀ : XiZeroCopy) :
    (s.re - (q₀.1 : ℂ).re) / Complex.normSq (s - (q₀.1 : ℂ)) ≤ (logDeriv xi s).re := by
  classical
  have hsum := summable_xiPairedResolventTerm hs
  have hnn : ∀ q : XiZeroCopy, 0 ≤ xiPairedResolventTerm s q :=
    fun q => xiPairedResolventTerm_nonneg h1 q
  have hS : ∑ q ∈ ({q₀, xiZeroCopyReflectEquiv q₀} : Finset XiZeroCopy),
        xiPairedResolventTerm s q
      ≤ ∑' q : XiZeroCopy, xiPairedResolventTerm s q :=
    hsum.sum_le_tsum _ (fun q _ => hnn q)
  rw [← two_mul_re_logDeriv_xi_eq_tsum_paired hs] at hS
  have hu0 := xiZeroCopy_re_pos q₀
  have hu1 := xiZeroCopy_re_lt_one q₀
  have hB : 0 ≤ (s.re - (1 - (q₀.1 : ℂ).re)) / Complex.normSq (s - (1 - (q₀.1 : ℂ))) :=
    div_nonneg (by linarith) (Complex.normSq_nonneg _)
  have hkey : 2 * ((s.re - (q₀.1 : ℂ).re) / Complex.normSq (s - (q₀.1 : ℂ)))
      ≤ ∑ q ∈ ({q₀, xiZeroCopyReflectEquiv q₀} : Finset XiZeroCopy),
          xiPairedResolventTerm s q := by
    by_cases hne : q₀ = xiZeroCopyReflectEquiv q₀
    · have hcoe : ((q₀.1 : XiDivisorSupport) : ℂ) = 1 - ((q₀.1 : XiDivisorSupport) : ℂ) := by
        have hc := congrArg (fun q : XiZeroCopy => ((q.1 : XiDivisorSupport) : ℂ)) hne
        simpa [coe_xiZeroCopyReflect] using hc
      have hset : ({q₀, xiZeroCopyReflectEquiv q₀} : Finset XiZeroCopy) = {q₀} := by
        rw [← hne]; simp
      have hre : (1 : ℝ) - ((q₀.1 : XiDivisorSupport) : ℂ).re
          = ((q₀.1 : XiDivisorSupport) : ℂ).re := by
        have hc := congrArg Complex.re hcoe
        simp only [Complex.sub_re, Complex.one_re] at hc
        linarith
      rw [hset, Finset.sum_singleton]
      unfold xiPairedResolventTerm
      rw [← hcoe, hre]
      linarith
    · rw [Finset.sum_pair hne, xiPairedResolventTerm_reflect]
      unfold xiPairedResolventTerm
      linarith [hB]
  linarith [hS, hkey]

/-- **The sharp Landau-type bound with the zero retained.** -/
theorem neg_re_logDeriv_riemannZeta_le_sub_resolvent {σ t : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (ht : 4 ≤ t) (q₀ : XiZeroCopy) :
    -(logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      ≤ 1 / 5 + Real.log t + digammaVerticalLogConstant
        - (σ - (q₀.1 : ℂ).re)
            / Complex.normSq (((σ : ℂ) + (t : ℂ) * Complex.I) - (q₀.1 : ℂ)) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by rw [hsdef]; simp
  have hsim : s.im = t := by rw [hsdef]; simp
  have h1 : 1 < s.re := by rw [hsre]; exact hσ1
  have hxine : xi s ≠ 0 := xi_ne_zero_of_one_le_re h1.le
  have hres := resolventTerm_le_re_logDeriv_xi hxine h1.le q₀
  rw [hsre] at hres
  have hfour := logDeriv_xi_fourFactor h1
  have hG : logDeriv Complex.Gammaℝ s
      = Complex.digamma (s / 2) / 2 - ((Real.log Real.pi : ℝ) : ℂ) / 2 :=
    logDeriv_Gammaℝ_digamma (by rw [hsre]; linarith)
  have hzeta : logDeriv riemannZeta s
      = logDeriv xi s - 1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s := by
    rw [hG, hfour]; ring
  rw [hzeta]
  have hre : (logDeriv xi s - 1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s).re
      = (logDeriv xi s).re - (1 / s).re - (1 / (s - 1)).re
        - (logDeriv Complex.Gammaℝ s).re := by
    simp only [Complex.sub_re]
  rw [hre]
  have hnormSq : Complex.normSq s = σ ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    rw [Complex.normSq_apply, hsre, hsim]; ring
  have hnormSq1 : Complex.normSq (s - 1) = (σ - 1) ^ (2 : ℕ) + t ^ (2 : ℕ) := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hsre, hsim]
    simp only [Complex.one_re, Complex.one_im, sub_zero]
    ring
  have hA : (1 / s).re ≤ 2 / 17 := by
    rw [one_div, Complex.inv_re, hsre, hnormSq]
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith [ht, hσ1, hσ2]
  have hB : (1 / (s - 1)).re ≤ 1 / 16 := by
    rw [one_div, Complex.inv_re, Complex.sub_re, hsre, hnormSq1]
    simp only [Complex.one_re]
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith [ht, hσ1, hσ2]
  have hC : (logDeriv Complex.Gammaℝ s).re ≤ Real.log t + digammaVerticalLogConstant := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [hsdef]
    exact norm_logDeriv_Gammaℝ_le (by linarith) (by linarith) ht
  linarith [hres, hA, hB, hC]

end

end RHTower
