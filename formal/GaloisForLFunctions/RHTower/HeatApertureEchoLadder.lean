/-
# Heat-aperture echo coefficients and the shifted-zeta ladder

The additive heat-aperture expansion has complex echo coefficient

`Cₖ(s) * conj (ζ(s-k)) * x^((s+k-1)/2)`.

This module formalizes two exact value laws used by that expansion:

* the archimedean coefficients `Cₖ(s)` are nonzero in the critical strip and satisfy a two-step
  recurrence;
* every backward integer shift `ζ(s-k)`, `k ≥ 1`, is nonzero in the open critical strip.
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace GaloisForLFunctions

open Complex

noncomputable section

/-- The part of the `k`-th heat-aperture echo coefficient that varies with `k`. -/
def heatApertureEchoCore (s : ℂ) (k : ℕ) : ℂ :=
  sin ((Real.pi : ℂ) * (s + k) / 2) *
    (4 * (Real.pi : ℂ)) ^ ((s + k - 1) / 2) * Gamma ((s + k) / 2) /
    (Nat.factorial k : ℂ)

/-- The archimedean coefficient of the `k`-th complex heat-aperture echo. -/
def heatApertureEchoCoeff (s : ℂ) (k : ℕ) : ℂ :=
  Gamma (1 - s) * heatApertureEchoCore s k / (Real.sqrt Real.pi : ℂ)

/-- The exact two-step recurrence for the varying part of the echo coefficient. -/
theorem heatApertureEchoCore_add_two {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    heatApertureEchoCore s (k + 2) =
      -(2 * (Real.pi : ℂ) * (s + k) / ((k + 1) * (k + 2))) *
        heatApertureEchoCore s k := by
  have hsk : s + (k : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hhalf : (s + (k : ℂ)) / 2 ≠ 0 := div_ne_zero hsk two_ne_zero
  have hbase : (4 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hsin : sin ((Real.pi : ℂ) * (s + (k + 2 : ℕ)) / 2) =
      -sin ((Real.pi : ℂ) * (s + k) / 2) := by
    rw [show (Real.pi : ℂ) * (s + (k + 2 : ℕ)) / 2 =
        (Real.pi : ℂ) * (s + k) / 2 + (Real.pi : ℂ) by
      push_cast
      ring]
    exact sin_add_pi _
  have hgamma : Gamma ((s + (k + 2 : ℕ)) / 2) =
      ((s + k) / 2) * Gamma ((s + k) / 2) := by
    rw [show (s + (k + 2 : ℕ)) / 2 = (s + k) / 2 + 1 by
      push_cast
      ring]
    exact Gamma_add_one _ hhalf
  have hpow : (4 * (Real.pi : ℂ)) ^ ((s + (k + 2 : ℕ) - 1) / 2) =
      (4 * (Real.pi : ℂ)) ^ ((s + k - 1) / 2) * (4 * (Real.pi : ℂ)) := by
    rw [show (s + (k + 2 : ℕ) - 1) / 2 = (s + k - 1) / 2 + 1 by
      push_cast
      ring]
    rw [cpow_add _ _ hbase, cpow_one]
  rw [heatApertureEchoCore, heatApertureEchoCore, hsin, hgamma, hpow]
  norm_num [Nat.factorial_succ]
  field_simp
  ring

/-- Every archimedean echo coefficient is nonzero in the open critical strip. -/
theorem heatApertureEchoCore_ne_zero {s : ℂ}
    (hslo : (1 / 2 : ℝ) < s.re) (hshi : s.re < 1) (k : ℕ) :
    heatApertureEchoCore s k ≠ 0 := by
  have hskre : 0 < (s + (k : ℂ)).re := by
    norm_num
    positivity
  have hsin : sin ((Real.pi : ℂ) * (s + k) / 2) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp h0
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have harg : (s + k) / 2 = (m : ℂ) := by
      apply mul_left_cancel₀ hpi
      calc
        (Real.pi : ℂ) * ((s + k) / 2) =
            (Real.pi : ℂ) * (s + k) / 2 := by ring
        _ = (m : ℂ) * (Real.pi : ℂ) := hm
        _ = (Real.pi : ℂ) * (m : ℂ) := by ring
    have hre := congrArg Complex.re harg
    norm_num at hre
    have hs_integer : s.re = 2 * (m : ℝ) - (k : ℝ) := by linarith
    have hlt_or : (2 * m : ℤ) - (k : ℤ) ≤ 0 ∨ 1 ≤ (2 * m : ℤ) - (k : ℤ) := by omega
    rcases hlt_or with hnonpos | hpos
    · have hnonposR : (2 * (m : ℝ)) - (k : ℝ) ≤ 0 := by exact_mod_cast hnonpos
      linarith
    · have hposR : (1 : ℝ) ≤ 2 * (m : ℝ) - (k : ℝ) := by exact_mod_cast hpos
      linarith
  have hpow : (4 * (Real.pi : ℂ)) ^ ((s + k - 1) / 2) ≠ 0 := by
    exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have hgamma : Gamma ((s + k) / 2) ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos
    rw [div_ofNat_re]
    exact div_pos hskre two_pos
  have hfac : (Nat.factorial k : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hsin hpow) hgamma) hfac

/-- **Heat-aperture echo recurrence.** Every parity subsequence of archimedean echo coefficients is
generated from its first value by a rational two-step multiplier. -/
theorem heatApertureEchoCoeff_add_two {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    heatApertureEchoCoeff s (k + 2) =
      -(2 * (Real.pi : ℂ) * (s + k) / ((k + 1) * (k + 2))) *
        heatApertureEchoCoeff s k := by
  rw [heatApertureEchoCoeff, heatApertureEchoCoeff,
    heatApertureEchoCore_add_two hs]
  ring

/-- Every full archimedean echo coefficient is nonzero in the open critical strip. -/
theorem heatApertureEchoCoeff_ne_zero {s : ℂ}
    (hslo : (1 / 2 : ℝ) < s.re) (hshi : s.re < 1) (k : ℕ) :
    heatApertureEchoCoeff s k ≠ 0 := by
  apply div_ne_zero
  · apply mul_ne_zero
    · apply Gamma_ne_zero_of_re_pos
      norm_num
      linarith
    · exact heatApertureEchoCore_ne_zero hslo hshi k
  · exact_mod_cast Real.sqrt_ne_zero'.mpr Real.pi_pos

/-- **Backward shifted-zeta nonvanishing.** In the open critical strip, every strict backward
integer shift of the zeta value is nonzero. Thus the heat-aperture echo ladder can lose its
`k=0` rung at a nontrivial zero, but no rung with `k≥1`. -/
theorem riemannZeta_sub_nat_ne_zero_of_criticalStrip
    {s : ℂ} (hslo : (1 / 2 : ℝ) < s.re) (hshi : s.re < 1)
    {k : ℕ} (hk : 1 ≤ k) :
    riemannZeta (s - k) ≠ 0 := by
  let w : ℂ := s - k
  let u : ℂ := 1 - w
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hwre : w.re < 0 := by
    change s.re - (k : ℝ) < 0
    linarith
  have hure : 1 < u.re := by
    change 1 < 1 - (s.re - (k : ℝ))
    linarith
  have hw0 : w ≠ 0 := by
    intro h
    have : w.re = 0 := congrArg Complex.re h
    simp at this
    linarith
  have hu0 : u ≠ 0 := by
    intro h
    have : u.re = 0 := congrArg Complex.re h
    simp at this
    linarith
  have hGammaU : Gammaℝ u ≠ 0 := Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hure)
  have hGammaW : Gammaℝ w ≠ 0 := by
    intro h0
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp h0
    have hre := congrArg Complex.re hn
    norm_num [w] at hre
    by_cases hnk : 2 * n < k
    · have hgapR : (2 * (n : ℝ)) + 1 ≤ (k : ℝ) := by exact_mod_cast hnk
      linarith
    · have hnk' : k ≤ 2 * n := by omega
      have hnkR : (k : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hnk'
      linarith
  have hzu : riemannZeta u ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hure
  have hLambdaU : completedRiemannZeta u ≠ 0 := by
    intro h0
    apply hzu
    rw [riemannZeta_def_of_ne_zero hu0, h0, zero_div]
  have hLambdaW : completedRiemannZeta w ≠ 0 := by
    rw [← completedRiemannZeta_one_sub w]
    simpa [u]
  rw [riemannZeta_def_of_ne_zero hw0]
  exact div_ne_zero hLambdaW hGammaW

end

end GaloisForLFunctions
