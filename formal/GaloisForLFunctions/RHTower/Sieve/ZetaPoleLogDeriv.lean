import GaloisForLFunctions.RHTower.Sieve.ZetaPoleBoxLowerBound

/-!
# The pole term of the logarithmic derivative

Writing `ζ(s) = zetaEntire s / (s - 1)` with `zetaEntire` entire and nonvanishing on `Re s ≥ 1`,

```text
-ζ'/ζ (s) = 1/(s - 1) - (zetaEntire)'/(zetaEntire) (s),
```

so on the real segment `1 < σ ≤ 2` the logarithmic derivative exceeds `1/(σ - 1)` by a bounded
amount.  The coefficient of `1/(σ - 1)` is exactly `1`, which is what a three-four-one argument
needs: the Chebyshev bound `ψ(x) ≤ x log 4` would give the coefficient `log 4 > 4/3` and the
argument would fail.
-/

namespace RHTower.Sieve

open Complex

/-- The logarithmic derivative of `ζ` splits off the pole. -/
theorem logDeriv_riemannZeta_eq {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s = logDeriv RHTower.zetaEntire s - 1 / (s - 1) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hzE : RHTower.zetaEntire s ≠ 0 := by
    rw [RHTower.zetaEntire_eq hs]
    exact mul_ne_zero hs1 hz
  have hEq : riemannZeta =ᶠ[nhds s] fun w => RHTower.zetaEntire w / (w - 1) := by
    have hopen : IsOpen {w : ℂ | w ≠ 1} := isOpen_ne
    filter_upwards [hopen.mem_nhds hs] with w hw
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw
    rw [RHTower.zetaEntire_eq hw]
    field_simp
  have hsub : logDeriv (fun w : ℂ => w - 1) s = 1 / (s - 1) := by
    have hd : HasDerivAt (fun w : ℂ => w - 1) 1 s := (hasDerivAt_id s).sub_const 1
    rw [logDeriv_apply, hd.deriv]
  have hdiv := logDeriv_div (f := RHTower.zetaEntire) (g := fun w : ℂ => w - 1) s hzE hs1
    (RHTower.differentiable_zetaEntire s) (by fun_prop)
  rw [logDeriv_apply, hEq.deriv_eq, hEq.eq_of_nhds, ← logDeriv_apply, hdiv, hsub]

/-- **The pole bound.**  On `1 < σ ≤ 2` the real logarithmic derivative is `1/(σ - 1)` up to an
absolute constant. -/
theorem exists_pole_bound :
    ∃ A : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + A := by
  set F : ℝ → ℝ := fun σ => -(logDeriv RHTower.zetaEntire (σ : ℂ)).re with hFdef
  have hcont : ContinuousOn F (Set.Icc (1 : ℝ) 2) := by
    have hne : ∀ σ ∈ Set.Icc (1 : ℝ) 2, RHTower.zetaEntire (σ : ℂ) ≠ 0 := by
      intro σ hσ
      refine zetaEntire_ne_zero_of_one_le_re ?_
      simpa using hσ.1
    have hd : Continuous fun σ : ℝ => deriv RHTower.zetaEntire (σ : ℂ) :=
      (RHTower.differentiable_zetaEntire.deriv.continuous).comp Complex.continuous_ofReal
    have hf : Continuous fun σ : ℝ => RHTower.zetaEntire (σ : ℂ) :=
      (RHTower.differentiable_zetaEntire.continuous).comp Complex.continuous_ofReal
    refine ContinuousOn.neg (Complex.continuous_re.comp_continuousOn ?_)
    refine ContinuousOn.div hd.continuousOn hf.continuousOn hne
  obtain ⟨σ₀, hσ₀, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨1, by norm_num⟩ hcont
  refine ⟨F σ₀, fun σ hσ1 hσ2 => ?_⟩
  have hσne : (σ : ℂ) ≠ 1 := by
    intro hcon
    have : (σ : ℝ) = 1 := by exact_mod_cast hcon
    linarith
  have hzne : riemannZeta (σ : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simpa using hσ1.le)
  have hsplit := logDeriv_riemannZeta_eq hσne hzne
  have hre : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      = 1 / (σ - 1) + F σ := by
    have hlog : logDeriv riemannZeta (σ : ℂ) = deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) :=
      logDeriv_apply _ _
    have hneg : -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)
        = -(logDeriv riemannZeta (σ : ℂ)) := by
      rw [hlog, neg_div]
    have hpole : ((1 : ℂ) / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
      have hcast : ((σ : ℂ) - 1) = (((σ - 1 : ℝ)) : ℂ) := by push_cast; ring
      rw [hcast, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [hneg, hsplit]
    simp only [neg_sub, Complex.sub_re, hFdef]
    rw [hpole]
    ring
  rw [hre]
  have : F σ ≤ F σ₀ := hmax ⟨hσ1.le, hσ2⟩
  linarith

end RHTower.Sieve
