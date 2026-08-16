import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The residue factor of the zeta function and its derivative at one

The function `F(s) = (s-1)ζ(s)`, extended by `F(1) = 1`, has derivative `γ` at `1`: its difference
quotient at `1` is exactly `ζ(s) - 1/(s-1)`.  Since `-ζ'/ζ - 1/(s-1) = -F'/F` away from the pole,
this is the analytic source of the constant `-γ` in Mertens' second theorem.
-/

open Filter Topology Complex

namespace RHTower

noncomputable section

/-- The residue factor `(s-1)ζ(s)`, extended by `1` at the pole. -/
def zetaResidueFactor : ℂ → ℂ :=
  Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1

theorem zetaResidueFactor_of_ne {s : ℂ} (hs : s ≠ 1) :
    zetaResidueFactor s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs _ _

@[simp] theorem zetaResidueFactor_one : zetaResidueFactor 1 = 1 :=
  Function.update_self _ _ _

/-- **The residue factor tends to one at the pole.** -/
theorem tendsto_zetaResidueFactor :
    Tendsto zetaResidueFactor (𝓝[≠] 1) (𝓝 1) := by
  refine riemannZeta_residue_one.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (zetaResidueFactor_of_ne hs).symm

/-- **The difference quotient of the residue factor at the pole is `ζ(s) - 1/(s-1)`.** -/
theorem slope_zetaResidueFactor {s : ℂ} (hs : s ≠ 1) :
    slope zetaResidueFactor 1 s = riemannZeta s - 1 / (s - 1) := by
  have hne : s - 1 ≠ 0 := sub_ne_zero.2 hs
  rw [slope_def_field, zetaResidueFactor_of_ne hs, zetaResidueFactor_one]
  field_simp

/-- **The residue factor has derivative `γ` at the pole.** -/
theorem hasDerivAt_zetaResidueFactor :
    HasDerivAt zetaResidueFactor (Real.eulerMascheroniConstant : ℂ) 1 := by
  rw [hasDerivAt_iff_tendsto_slope]
  refine tendsto_riemannZeta_sub_one_div.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (slope_zetaResidueFactor hs).symm

/-- **The logarithmic derivative of zeta with the pole removed is the logarithmic derivative of the
residue factor.** -/
theorem logDeriv_riemannZeta_sub_pole {s zd : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    -(zd / riemannZeta s) - 1 / (s - 1)
      = -((riemannZeta s + (s - 1) * zd) / ((s - 1) * riemannZeta s)) := by
  have hne : s - 1 ≠ 0 := sub_ne_zero.2 hs
  field_simp
  ring

/-- **The derivative of the residue factor away from the pole.** -/
theorem hasDerivAt_zetaResidueFactor_of_ne {s zd : ℂ} (hs : s ≠ 1)
    (hd : HasDerivAt riemannZeta zd s) :
    HasDerivAt zetaResidueFactor (riemannZeta s + (s - 1) * zd) s := by
  have hsub : HasDerivAt (fun z : ℂ => z - 1) 1 s := by
    simpa using (hasDerivAt_id s).sub_const 1
  have hprod : HasDerivAt (fun z : ℂ => (z - 1) * riemannZeta z)
      (1 * riemannZeta s + (s - 1) * zd) s := hsub.mul hd
  refine hprod.congr_deriv (by ring) |>.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
  exact zetaResidueFactor_of_ne hz

/-! ## The logarithmic derivative near the pole -/

/-- **The residue factor is entire.** -/
theorem differentiable_zetaResidueFactor : Differentiable ℂ zetaResidueFactor := by
  intro s
  rcases eq_or_ne s 1 with hs | hs
  · subst hs
    exact hasDerivAt_zetaResidueFactor.differentiableAt
  · exact (hasDerivAt_zetaResidueFactor_of_ne hs
      (differentiableAt_riemannZeta hs).hasDerivAt).differentiableAt

@[simp] theorem deriv_zetaResidueFactor_one :
    deriv zetaResidueFactor 1 = (Real.eulerMascheroniConstant : ℂ) :=
  hasDerivAt_zetaResidueFactor.deriv

theorem deriv_zetaResidueFactor_of_ne {s : ℂ} (hs : s ≠ 1) :
    deriv zetaResidueFactor s = riemannZeta s + (s - 1) * deriv riemannZeta s :=
  (hasDerivAt_zetaResidueFactor_of_ne hs (differentiableAt_riemannZeta hs).hasDerivAt).deriv

/-- **Zeta does not vanish near its pole.** -/
theorem eventually_riemannZeta_ne_zero :
    ∀ᶠ s : ℂ in 𝓝[≠] 1, riemannZeta s ≠ 0 := by
  have hF : ∀ᶠ s : ℂ in 𝓝[≠] 1, zetaResidueFactor s ≠ 0 := by
    have hone : (1 : ℂ) ≠ 0 := one_ne_zero
    exact tendsto_zetaResidueFactor.eventually_ne hone
  filter_upwards [hF, self_mem_nhdsWithin] with s hs hne hzero
  rw [zetaResidueFactor_of_ne hne, hzero, mul_zero] at hs
  exact hs rfl

/-- **The constant of Mertens' second theorem is `−γ`.**  Away from the pole the logarithmic
derivative of zeta with the pole subtracted is the logarithmic derivative of the entire residue
factor, whose value at the pole is `γ`. -/
theorem tendsto_logDeriv_riemannZeta_sub_pole :
    Filter.Tendsto (fun s : ℂ => -(deriv riemannZeta s / riemannZeta s) - 1 / (s - 1))
      (𝓝[≠] 1) (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
  have hFc : Continuous zetaResidueFactor := differentiable_zetaResidueFactor.continuous
  have hFdc : Continuous (deriv zetaResidueFactor) :=
    differentiable_zetaResidueFactor.deriv.continuous
  have hne : zetaResidueFactor 1 ≠ 0 := by
    rw [zetaResidueFactor_one]
    exact one_ne_zero
  have hlim : Filter.Tendsto (fun s : ℂ => -(deriv zetaResidueFactor s / zetaResidueFactor s))
      (𝓝 1) (𝓝 (-(deriv zetaResidueFactor 1 / zetaResidueFactor 1))) := by
    refine Filter.Tendsto.neg ?_
    exact (hFdc.tendsto 1).div (hFc.tendsto 1) hne
  rw [deriv_zetaResidueFactor_one, zetaResidueFactor_one, div_one] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_riemannZeta_ne_zero, self_mem_nhdsWithin] with s hz hs
  rw [deriv_zetaResidueFactor_of_ne hs, zetaResidueFactor_of_ne hs]
  exact (logDeriv_riemannZeta_sub_pole (zd := deriv riemannZeta s) hs hz).symm

/-! ## The real approach to the pole -/

/-- The real numbers greater than one approach the complex pole from within its punctured
neighbourhood. -/
theorem tendsto_ofReal_nhdsWithin_ne_one :
    Filter.Tendsto (fun s : ℝ => ((s : ℝ) : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hc : Filter.Tendsto (fun s : ℝ => ((s : ℝ) : ℂ)) (𝓝 1) (𝓝 ((1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.tendsto 1
    simpa using hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : s ≠ 1 := ne_of_gt hs
    simpa using hs1

/-- **Zeta minus its pole tends to `γ` along the reals.** -/
theorem tendsto_riemannZeta_sub_pole_real :
    Filter.Tendsto (fun s : ℝ => riemannZeta (s : ℂ) - 1 / ((s : ℂ) - 1)) (𝓝[>] 1)
      (𝓝 ((Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
  tendsto_riemannZeta_sub_one_div.comp tendsto_ofReal_nhdsWithin_ne_one

/-! ## The von Mangoldt Dirichlet series at the pole -/

/-- **The von Mangoldt Dirichlet series minus the pole tends to `−γ`.**  On `re s > 1` the series
is the negative logarithmic derivative of zeta, so the limit is the one computed above. -/
theorem tendsto_LSeries_vonMangoldt_sub_pole :
    Filter.Tendsto
      (fun s : ℝ => LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ)
        - 1 / ((s : ℂ) - 1))
      (𝓝[>] 1) (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
  have hcomp := tendsto_logDeriv_riemannZeta_sub_pole.comp tendsto_ofReal_nhdsWithin_ne_one
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hre : 1 < ((s : ℝ) : ℂ).re := by simpa using hs
  simp only [Function.comp_apply]
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre, neg_div]

end

end RHTower
