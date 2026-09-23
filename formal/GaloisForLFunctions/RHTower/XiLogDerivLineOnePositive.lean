import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.RHTower.XiAntipodalShiftPhaseSplittingUniversalityLaw

/-!
# Positivity of the logarithmic derivative of the completed zeta on `Re s ≥ 1`

The completed zeta `ξ` has the absolutely convergent, multiplicity-exact partial fraction
`ξ'/ξ(s) = Σ_ρ (1/(ρ − 1/2) + 1/(s − ρ))` over its divisor.  Taking real parts and pairing every
divisor copy `ρ` with its functional-equation reflection `1 − ρ`, the contributions
`Re 1/(ρ − 1/2)` cancel in pairs, while `Re 1/(s − ρ) = (Re s − Re ρ)/|s − ρ|²` is strictly
positive whenever `Re s ≥ 1`, because every zero lies in the open strip `0 < Re ρ < 1`.
Hardy's theorem supplies at least one zero, so

`Re (ξ'/ξ)(s) > 0` for every `s` with `Re s ≥ 1`.

On the line `Re s = 1` this is the fundamental-harmonic (constant-mode) weight of the two-rate
horizon clock at a critical-line point `ρ = 1/2 + it`.  With the scattering coefficient
`φ(s) = ξ(2s−1)/ξ(2s)` that weight is `c₀(ρ) = −ξ(2ρ)·ξ(2ρ−1)·(φ'/φ)(ρ)`, and the functional
equation `ξ(1−s) = ξ(s)` together with the Schwarz reflection `ξ(s̄) = conj ξ(s)` give

`c₀(1/2 + it) = 4·|ξ(1+2it)|²·Re (ξ'/ξ)(1+2it) > 0`.

Thus the constant-mode weight is real and strictly positive at every height, with no input beyond
the location of the zeros in the strip.
-/

open Complex

namespace RHTower

noncomputable section

/-- Reflection of a divisor copy acts on the underlying point as `ρ ↦ 1 − ρ`. -/
private theorem reflect_coe (q : XiZeroCopy) :
    ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := rfl

/-- One term of the partial fraction of `ξ'/ξ`: `1/(ρ − 1/2) + 1/(s − ρ)`. -/
def xiPartialFractionTerm (s : ℂ) (q : XiZeroCopy) : ℂ :=
  ((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹

/-- The partial-fraction terms are summable wherever `ξ s ≠ 0`; they are `−i` times the
relative resolvent terms in the centred coordinate `z = (s − 1/2)(−i)`. -/
theorem summable_xiPartialFractionTerm_lineOne {s : ℂ} (hs : xi s ≠ 0) :
    Summable (xiPartialFractionTerm s) := by
  have hz : XiC ((s - 1 / 2) * (-I)) ≠ 0 := by
    rw [← xi_eq_XiC_comp]
    exact hs
  refine ((summable_xiRelativeResolventTerm hz).mul_left (-I)).congr ?_
  intro q
  simp only [xiRelativeResolventTerm, xiSpectralPoint, xiPartialFractionTerm]
  have h1 : ((q.1 : ℂ) - 1 / 2) * -I - (s - 1 / 2) * -I = (s - (q.1 : ℂ)) * I := by ring
  rw [h1, mul_inv, mul_inv, Complex.inv_I, inv_neg, Complex.inv_I]
  linear_combination (-(((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹)) * Complex.I_mul_I

/-- Real part of one partial-fraction term. -/
private theorem re_xiPartialFractionTerm (s : ℂ) (q : XiZeroCopy) :
    (xiPartialFractionTerm s q).re =
      ((q.1 : ℂ).re - 1 / 2) / normSq ((q.1 : ℂ) - 1 / 2) +
        (s.re - (q.1 : ℂ).re) / normSq (s - (q.1 : ℂ)) := by
  simp only [xiPartialFractionTerm, Complex.add_re, Complex.inv_re, Complex.sub_re]
  norm_num

/-- The real part of `ξ'/ξ` is the real series of the real parts of the partial-fraction terms. -/
theorem re_logDeriv_xi_eq_tsum {s : ℂ} (hs : xi s ≠ 0) :
    (logDeriv xi s).re = ∑' q : XiZeroCopy, (xiPartialFractionTerm s q).re := by
  rw [logDeriv_xi_eq_partialFraction hs]
  exact Complex.re_tsum (summable_xiPartialFractionTerm_lineOne hs)

/-- The reflection-paired resolvent term of `ξ'/ξ` at `s` for the divisor copy `q`:
`(Re s − β)/|s − ρ|² + (Re s − (1 − β))/|s − (1 − ρ)|²`. -/
def xiPairedResolventTerm (s : ℂ) (q : XiZeroCopy) : ℝ :=
  (s.re - (q.1 : ℂ).re) / normSq (s - (q.1 : ℂ)) +
    (s.re - (1 - (q.1 : ℂ).re)) / normSq (s - (1 - (q.1 : ℂ)))

/-- Pairing a copy with its reflection cancels the odd parts `Re 1/(ρ − 1/2)` and leaves the two
resolvent contributions of `ρ` and `1 − ρ`. -/
theorem re_term_add_reflect (s : ℂ) (q : XiZeroCopy) :
    (xiPartialFractionTerm s q).re +
        (xiPartialFractionTerm s (xiZeroCopyReflectEquiv q)).re =
      xiPairedResolventTerm s q := by
  unfold xiPairedResolventTerm
  rw [re_xiPartialFractionTerm, re_xiPartialFractionTerm, reflect_coe]
  have h1 : normSq ((1 - (q.1 : ℂ)) - 1 / 2) = normSq ((q.1 : ℂ) - 1 / 2) := by
    rw [← Complex.normSq_neg]
    congr 1
    ring
  rw [h1]
  simp only [Complex.sub_re, Complex.one_re]
  ring

/-- Every zero has real part in `(0, 1)`, so for `Re s ≥ 1` both resolvent contributions of a
reflected pair are strictly positive. -/
theorem xiPairedResolventTerm_pos {s : ℂ} (h1 : 1 ≤ s.re) (q : XiZeroCopy) :
    0 < xiPairedResolventTerm s q := by
  unfold xiPairedResolventTerm
  obtain ⟨hβ0, hβ1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have hne1 : s - (q.1 : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re] at this
    linarith
  have hne2 : s - (1 - (q.1 : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have hp1 : 0 < (s.re - (q.1 : ℂ).re) / normSq (s - (q.1 : ℂ)) :=
    div_pos (by linarith) (Complex.normSq_pos.mpr hne1)
  have hp2 : 0 < (s.re - (1 - (q.1 : ℂ).re)) / normSq (s - (1 - (q.1 : ℂ))) :=
    div_pos (by linarith) (Complex.normSq_pos.mpr hne2)
  linarith

/-- Hardy's theorem produces a divisor copy: the divisor of `ξ` is nonempty. -/
theorem nonempty_xiZeroCopy_xiLogDerivLineOnePositive : Nonempty XiZeroCopy := by
  obtain ⟨t, -, ht⟩ := exists_Xi_zero_gt 0
  have hXiC : XiC (t : ℂ) = 0 := by
    rw [XiC_ofReal, ht, Complex.ofReal_zero]
  obtain ⟨q, -⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (t : ℂ)).mp hXiC
  exact ⟨q⟩

/-- The paired resolvent terms are summable wherever `ξ s ≠ 0`. -/
theorem summable_xiPairedResolventTerm {s : ℂ} (hs : xi s ≠ 0) :
    Summable (xiPairedResolventTerm s) := by
  have hsum : Summable (fun q : XiZeroCopy => (xiPartialFractionTerm s q).re) :=
    (summable_xiPartialFractionTerm_lineOne hs).mapL Complex.reCLM
  have hsumR : Summable
      (fun q : XiZeroCopy => (xiPartialFractionTerm s (xiZeroCopyReflectEquiv q)).re) :=
    (xiZeroCopyReflectEquiv.summable_iff).mpr hsum
  refine (hsum.add hsumR).congr ?_
  intro q
  exact re_term_add_reflect s q

/-- **Twice the real part of `ξ'/ξ` is the series of paired resolvent terms.** -/
theorem two_mul_re_logDeriv_xi_eq_tsum_paired {s : ℂ} (hs : xi s ≠ 0) :
    2 * (logDeriv xi s).re = ∑' q : XiZeroCopy, xiPairedResolventTerm s q := by
  have hsum : Summable (fun q : XiZeroCopy => (xiPartialFractionTerm s q).re) :=
    (summable_xiPartialFractionTerm_lineOne hs).mapL Complex.reCLM
  have hsumR : Summable
      (fun q : XiZeroCopy => (xiPartialFractionTerm s (xiZeroCopyReflectEquiv q)).re) :=
    (xiZeroCopyReflectEquiv.summable_iff).mpr hsum
  have hcongr : ∑' q : XiZeroCopy, xiPairedResolventTerm s q = ∑' q : XiZeroCopy,
      ((xiPartialFractionTerm s q).re +
        (xiPartialFractionTerm s (xiZeroCopyReflectEquiv q)).re) := by
    congr 1
    funext q
    exact (re_term_add_reflect s q).symm
  rw [hcongr, hsum.tsum_add hsumR, re_logDeriv_xi_eq_tsum hs,
    xiZeroCopyReflectEquiv.tsum_eq (fun q => (xiPartialFractionTerm s q).re)]
  ring

/-- **Positivity of `Re (ξ'/ξ)` on `Re s ≥ 1`.**  The reflection-paired real partial fraction is a
series of strictly positive terms. -/
theorem re_logDeriv_xi_pos_of_one_le_re {s : ℂ} (h1 : 1 ≤ s.re) :
    0 < (logDeriv xi s).re := by
  have hs := xi_ne_zero_of_one_le_re h1
  have hpos : 0 < ∑' q : XiZeroCopy, xiPairedResolventTerm s q := by
    obtain ⟨q₀⟩ := nonempty_xiZeroCopy_xiLogDerivLineOnePositive
    exact (summable_xiPairedResolventTerm hs).tsum_pos
      (fun q => (xiPairedResolventTerm_pos h1 q).le) q₀ (xiPairedResolventTerm_pos h1 q₀)
  have htwice := two_mul_re_logDeriv_xi_eq_tsum_paired hs
  linarith

/-- On the line `Re s = 1`, at the doubled height `2t`. -/
theorem re_logDeriv_xi_lineOne_pos (t : ℝ) :
    0 < (logDeriv xi (1 + 2 * t * I)).re :=
  re_logDeriv_xi_pos_of_one_le_re (by simp)

/-- The derivative of `ξ` is odd about `1/2`: `ξ'(s) = −ξ'(1 − s)`. -/
private theorem deriv_xi_eq_neg (s : ℂ) : deriv xi s = -deriv xi (1 - s) := by
  have hfun : xi = fun w => xi (1 - w) := funext (fun w => (xi_one_sub w).symm)
  conv_lhs => rw [hfun]
  exact deriv_comp_const_sub xi 1 s

/-- The logarithmic derivative of `ξ` is odd about `1/2`. -/
theorem logDeriv_xi_one_sub_xiLogDerivLineOnePositive (s : ℂ) : logDeriv xi (1 - s) = -logDeriv xi s := by
  simp only [logDeriv, Pi.div_apply]
  rw [deriv_xi_eq_neg s, xi_one_sub s]
  ring

/-- Fundamental-harmonic (constant-mode) weight of the two-rate horizon clock at the critical-line
point `ρ = 1/2 + it`: `c₀(ρ) = −ξ(2ρ)·ξ(2ρ−1)·(φ'/φ)(ρ)`, where `φ(s) = ξ(2s−1)/ξ(2s)` is the
scattering coefficient, so `(φ'/φ)(ρ) = 2·(ξ'/ξ)(2ρ−1) − 2·(ξ'/ξ)(2ρ)`. -/
def hbConstantModeWeight (t : ℝ) : ℂ :=
  -(xi (1 + 2 * t * I) * xi (2 * t * I) *
    (2 * logDeriv xi (2 * t * I) - 2 * logDeriv xi (1 + 2 * t * I)))

/-- Functional equation and Schwarz reflection collapse the weight to `4|ξ(1+2it)|²·Re(ξ'/ξ)(1+2it)`. -/
theorem hbConstantModeWeight_eq (t : ℝ) :
    hbConstantModeWeight t =
      ((4 * normSq (xi (1 + 2 * t * I)) * (logDeriv xi (1 + 2 * t * I)).re : ℝ) : ℂ) := by
  have hconj : (starRingEnd ℂ) (1 + 2 * t * I) = 1 - 2 * t * I := by
    apply Complex.ext <;> simp
  have h1 : xi (2 * t * I) = (starRingEnd ℂ) (xi (1 + 2 * t * I)) := by
    rw [← xi_one_sub (2 * t * I), ← xi_conj, hconj]
  have h2 : logDeriv xi (2 * t * I) = -(starRingEnd ℂ) (logDeriv xi (1 + 2 * t * I)) := by
    rw [← logDeriv_xi_conj_global, hconj, logDeriv_xi_one_sub_xiLogDerivLineOnePositive (2 * t * I), neg_neg]
  unfold hbConstantModeWeight
  rw [h1, h2, Complex.mul_conj]
  have hL := Complex.add_conj (logDeriv xi (1 + 2 * t * I))
  push_cast at hL ⊢
  linear_combination (2 * (normSq (xi (1 + 2 * t * I)) : ℂ)) * hL

/-- The constant-mode weight is real. -/
theorem hbConstantModeWeight_im (t : ℝ) : (hbConstantModeWeight t).im = 0 := by
  rw [hbConstantModeWeight_eq, Complex.ofReal_im]

/-- **The constant-mode weight is strictly positive at every height.** -/
theorem hbConstantModeWeight_re_pos (t : ℝ) : 0 < (hbConstantModeWeight t).re := by
  rw [hbConstantModeWeight_eq, Complex.ofReal_re]
  have hL := re_logDeriv_xi_lineOne_pos t
  have hn : 0 < normSq (xi (1 + 2 * t * I)) :=
    Complex.normSq_pos.mpr (xi_ne_zero_of_one_le_re (by simp))
  have h4 : (0 : ℝ) < 4 * normSq (xi (1 + 2 * t * I)) := by linarith
  exact mul_pos h4 hL

end

end RHTower
