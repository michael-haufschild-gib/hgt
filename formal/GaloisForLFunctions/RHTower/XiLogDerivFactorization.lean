import GaloisForLFunctions.RHTower.XiRectangleZeroCount
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# The logarithmic derivative of `ξ` splits into its four factors

On the half-plane of absolute convergence

`ξ(s) = (s(s−1)/2) · π^{−s/2} · Γ(s/2) · ζ(s)`,

and the logarithmic derivative of a product is the sum of the logarithmic derivatives, so

`ξ'/ξ (s) = 1/s + 1/(s−1) − ½ log π + ½ ψ(s/2) + ζ'/ζ (s)`.

Each summand is elementary except the digamma term, whose vertical integral is the Gamma phase.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-! ## The three Archimedean logarithmic derivatives -/

theorem logDeriv_quadratic {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv (fun z : ℂ => z * (z - 1) / 2) s = 1 / s + 1 / (s - 1) := by
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hd : HasDerivAt (fun z : ℂ => z * (z - 1) / 2) ((2 * s - 1) / 2) s := by
    have h1 : HasDerivAt (fun z : ℂ => z * (z - 1)) (1 * (s - 1) + s * 1) s :=
      (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
    have h2 := h1.div_const 2
    have heq : (1 * (s - 1) + s * 1) / 2 = (2 * s - 1) / 2 := by ring
    rw [← heq]
    exact h2
  have hne : s * (s - 1) / 2 ≠ 0 := div_ne_zero (mul_ne_zero hs0 hs1') two_ne_zero
  rw [logDeriv_apply, hd.deriv]
  field_simp
  ring

theorem logDeriv_piPow (s : ℂ) :
    logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s = -(Real.log Real.pi : ℂ) / 2 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hlog : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
    rw [← Complex.ofReal_log Real.pi_pos.le]
  have hrw : (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      = fun z : ℂ => Complex.exp ((-z / 2) * (Real.log Real.pi : ℂ)) := by
    funext z
    rw [Complex.cpow_def_of_ne_zero hπ, hlog, mul_comm]
  have hinner : HasDerivAt (fun z : ℂ => (-z / 2) * (Real.log Real.pi : ℂ))
      ((-1 / 2 : ℂ) * (Real.log Real.pi : ℂ)) s := by
    have h1 : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2 : ℂ) s := by
      have := ((hasDerivAt_id s).neg).div_const 2
      simpa using this
    exact h1.mul_const _
  rw [hrw, logDeriv_apply, (hinner.cexp).deriv]
  have hexp : Complex.exp ((-s / 2) * (Real.log Real.pi : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  field_simp

theorem logDeriv_gammaHalf {s : ℂ} (hs : ∀ m : ℕ, s / 2 ≠ -m) :
    logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s = Complex.digamma (s / 2) / 2 := by
  have hne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hs
  have h1 : HasDerivAt (fun z : ℂ => z / 2) (1 / 2 : ℂ) s := by
    simpa using (hasDerivAt_id s).div_const 2
  have hΓ : HasDerivAt Complex.Gamma (deriv Complex.Gamma (s / 2)) (s / 2) :=
    (Complex.differentiableAt_Gamma (s / 2) hs).hasDerivAt
  have hd : HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2))
      (deriv Complex.Gamma (s / 2) * (1 / 2)) s := by
    simpa [Function.comp_def] using hΓ.comp s h1
  rw [logDeriv_apply, hd.deriv, Complex.digamma, logDeriv_apply]
  field_simp

/-! ## The factorization -/

theorem xi_eq_four_factors {z : ℂ} (hz : 1 < z.re) :
    xi z = (z * (z - 1) / 2)
      * ((Real.pi : ℂ) ^ (-z / 2) * (Complex.Gamma (z / 2) * riemannZeta z)) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
    linarith
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hz
    simp at hz
  have hΓr : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΛ : completedRiemannZeta z = Complex.Gammaℝ z * riemannZeta z := by
    rw [riemannZeta_def_of_ne_zero hz0]
    field_simp
  rw [xi_eq_half_mul hz0 hz1, hΛ, Complex.Gammaℝ_def]
  ring

/-- **The logarithmic derivative of `ξ` splits into four terms.** -/
theorem logDeriv_xi_fourFactor {s : ℂ} (hs : 1 < s.re) :
    logDeriv xi s = 1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2
      + Complex.digamma (s / 2) / 2 + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hhalf : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m h
    have hre : (s / 2).re = -(m : ℝ) := by rw [h]; simp
    have : (s / 2).re = s.re / 2 := by simp
    rw [this] at hre
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hΓne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hhalf
  have hζne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hπne : ((Real.pi : ℂ) ^ (-s / 2)) ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.mpr ?_
    simp [Real.pi_ne_zero]
  have hqne : s * (s - 1) / 2 ≠ 0 := div_ne_zero (mul_ne_zero hs0 hs1') two_ne_zero
  have hgerm : xi =ᶠ[nhds s] (fun z : ℂ => (z * (z - 1) / 2)
      * ((Real.pi : ℂ) ^ (-z / 2) * (Complex.Gamma (z / 2) * riemannZeta z))) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact xi_eq_four_factors hz
  have hlog : logDeriv xi s = logDeriv (fun z : ℂ => (z * (z - 1) / 2)
      * ((Real.pi : ℂ) ^ (-z / 2) * (Complex.Gamma (z / 2) * riemannZeta z))) s := by
    rw [logDeriv_apply, logDeriv_apply, hgerm.deriv_eq, hgerm.eq_of_nhds]
  have hdq : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1) / 2) s := by fun_prop
  have hdπ : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    refine DifferentiableAt.const_cpow (by fun_prop) ?_
    left
    simp [Real.pi_ne_zero]
  have hdΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (Complex.differentiableAt_Gamma (s / 2) hhalf).comp s (by fun_prop)
  have hdζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  rw [hlog,
    logDeriv_mul (f := fun z : ℂ => z * (z - 1) / 2)
      (g := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * (Complex.Gamma (z / 2) * riemannZeta z))
      s hqne (mul_ne_zero hπne (mul_ne_zero hΓne hζne)) hdq (hdπ.mul (hdΓ.mul hdζ)),
    logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      (g := fun z : ℂ => Complex.Gamma (z / 2) * riemannZeta z)
      s hπne (mul_ne_zero hΓne hζne) hdπ (hdΓ.mul hdζ),
    logDeriv_mul (f := fun z : ℂ => Complex.Gamma (z / 2)) (g := riemannZeta)
      s hΓne hζne hdΓ hdζ,
    logDeriv_quadratic hs0 hs1, logDeriv_piPow s, logDeriv_gammaHalf hhalf]
  ring

/-! ## The splitting off the real axis -/

theorem xi_eq_four_factors_offReal {z : ℂ} (hz : z.im ≠ 0) :
    xi z = (z * (z - 1) / 2)
      * ((Real.pi : ℂ) ^ (-z / 2) * (Complex.Gamma (z / 2) * riemannZeta z)) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hz
    simp at hz
  have hΓr : Complex.Gammaℝ z ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
    rw [hn] at hz
    simp at hz
  have hΛ : completedRiemannZeta z = Complex.Gammaℝ z * riemannZeta z := by
    rw [riemannZeta_def_of_ne_zero hz0]
    field_simp
  rw [xi_eq_half_mul hz0 hz1, hΛ, Complex.Gammaℝ_def]
  ring

theorem logDeriv_xi_fourFactor_offReal {s : ℂ} (hs : s.im ≠ 0) (hζ : riemannZeta s ≠ 0) :
    logDeriv xi s = 1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2
      + Complex.digamma (s / 2) / 2 + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hhalf : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m h
    have him : (s / 2).im = 0 := by rw [h]; simp
    have : (s / 2).im = s.im / 2 := by simp
    rw [this] at him
    exact hs (by linarith)
  have hΓne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hhalf
  have hπne : ((Real.pi : ℂ) ^ (-s / 2)) ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.mpr ?_
    simp [Real.pi_ne_zero]
  have hqne : s * (s - 1) / 2 ≠ 0 := div_ne_zero (mul_ne_zero hs0 hs1') two_ne_zero
  have hopen : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne.preimage Complex.continuous_im
  have hgerm : xi =ᶠ[nhds s] (fun z : ℂ => (z * (z - 1) / 2)
      * ((Real.pi : ℂ) ^ (-z / 2) * (Complex.Gamma (z / 2) * riemannZeta z))) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact xi_eq_four_factors_offReal hz
  have hlog : logDeriv xi s = logDeriv (fun z : ℂ => (z * (z - 1) / 2)
      * ((Real.pi : ℂ) ^ (-z / 2) * (Complex.Gamma (z / 2) * riemannZeta z))) s := by
    rw [logDeriv_apply, logDeriv_apply, hgerm.deriv_eq, hgerm.eq_of_nhds]
  have hdq : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1) / 2) s := by fun_prop
  have hdπ : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    refine DifferentiableAt.const_cpow (by fun_prop) ?_
    left
    simp [Real.pi_ne_zero]
  have hdΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (Complex.differentiableAt_Gamma (s / 2) hhalf).comp s (by fun_prop)
  have hdζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  rw [hlog,
    logDeriv_mul (f := fun z : ℂ => z * (z - 1) / 2)
      (g := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * (Complex.Gamma (z / 2) * riemannZeta z))
      s hqne (mul_ne_zero hπne (mul_ne_zero hΓne hζ)) hdq (hdπ.mul (hdΓ.mul hdζ)),
    logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      (g := fun z : ℂ => Complex.Gamma (z / 2) * riemannZeta z)
      s hπne (mul_ne_zero hΓne hζ) hdπ (hdΓ.mul hdζ),
    logDeriv_mul (f := fun z : ℂ => Complex.Gamma (z / 2)) (g := riemannZeta)
      s hΓne hζ hdΓ hdζ,
    logDeriv_quadratic hs0 hs1, logDeriv_piPow s, logDeriv_gammaHalf hhalf]
  ring

end RHTower
