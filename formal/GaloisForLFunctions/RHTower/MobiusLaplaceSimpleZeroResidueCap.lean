import GaloisForLFunctions.RHTower.MobiusLaplacePolylogSharpCoefficientLaw
import GaloisForLFunctions.RHTower.MobiusLaplaceBoundaryMultiplicity

/-!
# The exact-half-decay residue cap

At `q = 0` the sharp maximal-order coefficient law reads off the derivative itself: exact
half-power decay of the discrete Möbius--Laplace transform with constant `C` makes every
critical-line zeta zero simple and caps the archimedean residue,

```text
‖Γ(ρ)/ζ′(ρ)‖ ≤ C .
```

The local factor `p` of the sharp law has `p(ρ) = ζ′(ρ)` because the zero is simple.
-/

open Filter Topology

namespace RHTower

noncomputable section

theorem mobiusLaplaceHalfPolylogKernel_zero (x : ℝ) :
    mobiusLaplaceHalfPolylogKernel 0 x = x ^ (-(1 / 2) : ℝ) := by
  rw [mobiusLaplaceHalfPolylogKernel]
  norm_num

/-- If `ζ` factors as `(z-ρ)·p` near `ρ` with `p` analytic, then `ζ′(ρ) = p(ρ)`. -/
theorem deriv_riemannZeta_eq_of_simple_factor {rho : ℂ} {p : ℂ → ℂ}
    (hp : AnalyticAt ℂ p rho)
    (heq : riemannZeta =ᶠ[nhds rho] fun z => (z - rho) ^ (0 + 1) * p z) :
    deriv riemannZeta rho = p rho := by
  have hlin : HasDerivAt (fun z : ℂ => (z - rho) ^ (0 + 1)) 1 rho := by
    have h : HasDerivAt (fun z : ℂ => z - rho) 1 rho := by
      simpa using (hasDerivAt_id rho).sub_const rho
    simpa using h
  have hpd : HasDerivAt p (deriv p rho) rho := hp.differentiableAt.hasDerivAt
  have hval : (1 : ℂ) * p rho + (rho - rho) ^ (0 + 1) * deriv p rho = p rho := by
    simp
  have hmul : HasDerivAt (fun z : ℂ => (z - rho) ^ (0 + 1) * p z) (p rho) rho := by
    have h := hlin.mul hpd
    rw [hval] at h
    exact h
  rw [heq.deriv_eq, hmul.deriv]

/-- **The residue cap `(3)`.**  Exact half-power decay with constant `C` caps the archimedean
residue of every critical-line zeta zero. -/
theorem norm_Gamma_div_deriv_riemannZeta_le_of_halfDecay {C delta : ℝ} (hC : 0 ≤ C)
    (hdelta : 0 < delta)
    (hsrc : ∀ x : ℝ, 0 < x → x < delta →
      ‖mobiusDiscreteLaplaceTransform x‖ ≤ C * x ^ (-(1 / 2) : ℝ))
    {rho : ℂ} (hre : rho.re = 1 / 2) (hzero : riemannZeta rho = 0) :
    ‖Complex.Gamma rho / deriv riemannZeta rho‖ ≤ C := by
  have hdecay : MobiusDiscreteLaplaceHalfDecay := ⟨C, delta, hC, hdelta, hsrc⟩
  have horder : analyticOrderAt riemannZeta rho = 1 :=
    analyticOrderAt_riemannZeta_eq_one_of_mobiusDiscreteLaplaceHalfDecay hdecay hre hzero
  have hsrc' : ∀ x : ℝ, 0 < x → x < delta →
      ‖mobiusDiscreteLaplaceTransform x‖ ≤ C * mobiusLaplaceHalfPolylogKernel 0 x := by
    intro x hx hxd
    rw [mobiusLaplaceHalfPolylogKernel_zero]
    exact hsrc x hx hxd
  have horder' : analyticOrderAt riemannZeta rho = ((0 + 1 : ℕ) : ℕ∞) := by
    rw [horder]
    norm_num
  obtain ⟨p, hp, hpne, heq, hbound⟩ :=
    exists_localFactor_with_Gamma_cap_of_halfPolylog_maximalOrder (q := 0) hC hdelta hsrc' hre
      horder'
  have hderiv : deriv riemannZeta rho = p rho := deriv_riemannZeta_eq_of_simple_factor hp heq
  rw [hderiv]
  have hfac : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num
  rw [hfac, mul_one] at hbound
  exact hbound

/-- **The `q = 0` package.**  Exact half-power decay implies the Riemann hypothesis, simplicity of
every critical-line zero, and the residue cap. -/
theorem mobiusDiscreteLaplaceHalfDecay_implies_rh_simplicity_and_residueCap
    {C delta : ℝ} (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hsrc : ∀ x : ℝ, 0 < x → x < delta →
      ‖mobiusDiscreteLaplaceTransform x‖ ≤ C * x ^ (-(1 / 2) : ℝ)) :
    RiemannHypothesis ∧
      (∀ rho : ℂ, rho.re = 1 / 2 → riemannZeta rho = 0 →
        analyticOrderAt riemannZeta rho = 1) ∧
      (∀ rho : ℂ, rho.re = 1 / 2 → riemannZeta rho = 0 →
        ‖Complex.Gamma rho / deriv riemannZeta rho‖ ≤ C) := by
  have hdecay : MobiusDiscreteLaplaceHalfDecay := ⟨C, delta, hC, hdelta, hsrc⟩
  obtain ⟨hrh, hsimple⟩ :=
    mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis_and_boundarySimplicity hdecay
  exact ⟨hrh, hsimple, fun rho hre hz =>
    norm_Gamma_div_deriv_riemannZeta_le_of_halfDecay hC hdelta hsrc hre hz⟩

end

end RHTower
