import GaloisForLFunctions.RHTower.MobiusDecayExponent
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# A zeta zero obstructs source decay

Source decay at exponent `b` makes the Mellin transform of the Möbius--Laplace source analytic on
`Re s > b`.  On `Re s > 1` that transform is `Γ(s)/ζ(s)`, so the product with the regularized
residue unit `(s-1)ζ(s)` equals `Γ(s)(s-1)` there.  Both sides are analytic on the convex — hence
connected — half-plane `Re s > b ≥ 0`, so the identity theorem propagates the equality to the whole
half-plane.

At a zeta zero `ρ ≠ 1` in that half-plane the left side vanishes while `Γ(ρ)(ρ-1)` does not, because
the Gamma function has no zeros.  So no such decay exponent can reach past a zero, and a subpower
coefficient bound producing it is impossible.
-/

open Complex Filter
open scoped Topology

namespace RHTower

/-- Off the nonpositive integers the Gamma function is analytic; on a half-plane strictly right of
the origin this is automatic. -/
theorem analyticOnNhd_Gamma_halfPlane {b : ℝ} (hb : 0 ≤ b) :
    AnalyticOnNhd ℂ Complex.Gamma {s : ℂ | b < s.re} := by
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) (isOpen_decayHalfPlane b)
  have hre : 0 < s.re := lt_of_le_of_lt hb hs
  refine (Complex.differentiableAt_Gamma s fun m => ?_).differentiableWithinAt
  intro hsm
  have : s.re = -(m : ℝ) := by rw [hsm]; simp
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith [this ▸ hre]

/-- **A zeta zero obstructs decay.**  If `ζ` vanishes at some `ρ ≠ 1` with `Re ρ > b ≥ 0`, then the
Möbius--Laplace source cannot decay at exponent `b`. -/
theorem not_mobiusDiscreteLaplaceDecay_of_riemannZeta_eq_zero
    {b : ℝ} (hb : 0 ≤ b) {ρ : ℂ} (hρre : b < ρ.re) (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) :
    ¬ MobiusDiscreteLaplaceDecay b := by
  intro hdecay
  have hopen : IsOpen {s : ℂ | b < s.re} := isOpen_decayHalfPlane b
  have hconn : IsPreconnected {s : ℂ | b < s.re} :=
    (convex_halfSpace_re_gt b).isPreconnected
  have hmel := analyticOnNhd_mellin_of_mobiusDiscreteLaplaceDecay hdecay
  have hG : AnalyticOnNhd ℂ
      (fun s => mellin mobiusDiscreteLaplaceTransform s * zetaResidueUnit s)
      {s : ℂ | b < s.re} :=
    fun s hs => (hmel s hs).mul (analyticAt_zetaResidueUnit s)
  have hH : AnalyticOnNhd ℂ (fun s => Complex.Gamma s * (s - 1)) {s : ℂ | b < s.re} :=
    fun s hs => (analyticOnNhd_Gamma_halfPlane hb s hs).mul
      ((analyticAt_id).sub (analyticAt_const))
  -- The two agree near `s = 2`, hence on the whole half-plane.
  set s₀ : ℂ := ((b + 2 : ℝ) : ℂ) with hs₀
  have hs₀re : s₀.re = b + 2 := by rw [hs₀, Complex.ofReal_re]
  have htwo : s₀ ∈ {s : ℂ | b < s.re} := by
    simp only [Set.mem_setOf_eq, hs₀re]
    linarith
  have hnear : (fun s => mellin mobiusDiscreteLaplaceTransform s * zetaResidueUnit s) =ᶠ[𝓝 s₀]
      fun s => Complex.Gamma s * (s - 1) := by
    have hopen1 : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem1 : s₀ ∈ {s : ℂ | 1 < s.re} := by
      simp only [Set.mem_setOf_eq, hs₀re]
      linarith
    have hnbhd : ∀ᶠ s : ℂ in 𝓝 s₀, 1 < s.re := hopen1.mem_nhds hmem1
    filter_upwards [hnbhd] with s hs
    have hs1 : s ≠ 1 := by
      intro h
      rw [h] at hs
      simp at hs
    have hzne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    have hres : zetaResidueUnit s = (s - 1) * riemannZeta s := by
      simp [zetaResidueUnit, Function.update_of_ne hs1]
    rw [mellin_mobiusDiscreteLaplaceTransform_eq_gamma_div_zeta hs, hres]
    field_simp
  have heq := hG.eqOn_of_preconnected_of_eventuallyEq hH hconn htwo hnear
  have hρmem : ρ ∈ {s : ℂ | b < s.re} := hρre
  have hval := heq hρmem
  have hleft : mellin mobiusDiscreteLaplaceTransform ρ * zetaResidueUnit ρ = 0 := by
    have hres : zetaResidueUnit ρ = (ρ - 1) * riemannZeta ρ := by
      simp [zetaResidueUnit, Function.update_of_ne hρ1]
    rw [hres, hzero, mul_zero, mul_zero]
  have hright : Complex.Gamma ρ * (ρ - 1) ≠ 0 := by
    refine mul_ne_zero (Complex.Gamma_ne_zero fun m => ?_) (sub_ne_zero.mpr hρ1)
    intro hsm
    have hre : 0 < ρ.re := lt_of_le_of_lt hb hρre
    have : ρ.re = -(m : ℝ) := by rw [hsm]; simp
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith [this ▸ hre]
  dsimp only at hval
  rw [hleft] at hval
  exact hright hval.symm

/-- **The order law in no-go form.**  A zeta zero beyond the abscissa `(α+1)/(2k)` forbids the
subpower coefficient bound with exponent `α`.  This is the `Θ`-sensitive lower bound `(R3)`: the
coefficient order cannot drop below what the zero permits. -/
theorem not_mixedSubpower_of_riemannZeta_eq_zero
    {k : ℕ} (hk : 0 < k) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C)
    {ρ : ℂ} (hρ1 : ρ ≠ 1) (hzero : riemannZeta ρ = 0)
    (hρre : (α + 1) / (2 * (k : ℝ)) < ρ.re) :
    ¬ (∀ N : ℕ,
      (mixedAdditiveConvolutionPower mobiusCoeff k N).re ≤ C * ((N : ℝ) + 1) ^ α) := by
  intro hupper
  have hkR : (0 : ℝ) < 2 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    linarith
  have hb : 0 ≤ (α + 1) / (2 * (k : ℝ)) := by positivity
  exact not_mobiusDiscreteLaplaceDecay_of_riemannZeta_eq_zero hb hρre hρ1 hzero
    (mobiusDiscreteLaplaceDecay_of_subpower hk hα hC hupper)

end RHTower
