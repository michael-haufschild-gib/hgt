import GaloisForLFunctions.RHTower.TwistedMobiusMellin

/-!
# A twisted L-zero obstructs source decay

For a nontrivial Dirichlet character the L-function is entire, so the obstruction argument is
shorter than at conductor one: no regularizing factor `(s-1)` is needed.

Source decay at exponent `b` makes the twisted Mellin transform analytic on `Re s > b`, and on
`Re s > 1` the product `mellin A_χ · L(·,χ)` equals `Γ`.  Both sides are analytic on the convex,
hence connected, half-plane `Re s > b ≥ 0`, so the identity theorem propagates the identity.  At a
zero of `L(·,χ)` in that half-plane the left side vanishes while `Γ` does not.
-/

open Complex Filter
open scoped Topology ArithmeticFunction.Moebius LSeries.notation

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- **A twisted L-zero obstructs decay.**  If `L(·,χ)` vanishes at some point with real part
exceeding `b ≥ 0`, the twisted source cannot decay at exponent `b`. -/
theorem not_twistedMobiusLaplaceDecay_of_LFunction_eq_zero
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {b : ℝ} (hb : 0 ≤ b)
    {ρ : ℂ} (hρre : b < ρ.re) (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    ¬ TwistedMobiusLaplaceDecay χ b := by
  intro hdecay
  have hconn : IsPreconnected {s : ℂ | b < s.re} :=
    (convex_halfSpace_re_gt b).isPreconnected
  have hmel := analyticOnNhd_mellin_of_twistedMobiusLaplaceDecay hdecay
  have hLan : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {s : ℂ | b < s.re} := fun s _ =>
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have hG : AnalyticOnNhd ℂ
      (fun s => mellin (twistedMobiusLaplaceTransform χ) s * DirichletCharacter.LFunction χ s)
      {s : ℂ | b < s.re} :=
    fun s hs => (hmel s hs).mul (hLan s hs)
  have hH : AnalyticOnNhd ℂ Complex.Gamma {s : ℂ | b < s.re} :=
    analyticOnNhd_Gamma_halfPlane hb
  set s₀ : ℂ := ((b + 2 : ℝ) : ℂ) with hs₀
  have hs₀re : s₀.re = b + 2 := by rw [hs₀, Complex.ofReal_re]
  have hmem : s₀ ∈ {s : ℂ | b < s.re} := by
    simp only [Set.mem_setOf_eq, hs₀re]
    linarith
  have hnear : (fun s => mellin (twistedMobiusLaplaceTransform χ) s *
      DirichletCharacter.LFunction χ s) =ᶠ[𝓝 s₀] Complex.Gamma := by
    have hopen1 : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem1 : s₀ ∈ {s : ℂ | 1 < s.re} := by
      simp only [Set.mem_setOf_eq, hs₀re]
      linarith
    filter_upwards [hopen1.mem_nhds hmem1] with s hs
    have hLs : DirichletCharacter.LFunction χ s = L ↗χ s :=
      DirichletCharacter.LFunction_eq_LSeries χ hs
    have hne : L ↗χ s ≠ 0 := DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs
    rw [mellin_twistedMobiusLaplaceTransform_eq_gamma_div_LSeries χ hs, hLs]
    field_simp
  have heq := hG.eqOn_of_preconnected_of_eventuallyEq hH hconn hmem hnear
  have hval := heq (show ρ ∈ {s : ℂ | b < s.re} from hρre)
  have hleft : mellin (twistedMobiusLaplaceTransform χ) ρ *
      DirichletCharacter.LFunction χ ρ = 0 := by
    rw [hzero, mul_zero]
  have hright : Complex.Gamma ρ ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m => ?_
    intro hsm
    have hre : 0 < ρ.re := lt_of_le_of_lt hb hρre
    have hval2 : ρ.re = -(m : ℝ) := by rw [hsm]; simp
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith [hval2 ▸ hre]
  dsimp only at hval
  rw [hleft] at hval
  exact hright hval.symm

/-- **The twisted order law in no-go form.**  A zero of `L(·,χ)` beyond the abscissa `(α+1)/(2k)`
forbids the subpower bound with exponent `α` on the twisted Hermitian convolution coefficients. -/
theorem not_twistedMixedSubpower_of_LFunction_eq_zero
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {k : ℕ} (hk : 0 < k) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C)
    {ρ : ℂ} (hzero : DirichletCharacter.LFunction χ ρ = 0)
    (hρre : (α + 1) / (2 * (k : ℝ)) < ρ.re) :
    ¬ (∀ M : ℕ,
      (mixedAdditiveConvolutionPower (↗χ * ↗μ) k M).re ≤ C * ((M : ℝ) + 1) ^ α) := by
  intro hupper
  have hkR : (0 : ℝ) < 2 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    linarith
  have hb : 0 ≤ (α + 1) / (2 * (k : ℝ)) := by positivity
  exact not_twistedMobiusLaplaceDecay_of_LFunction_eq_zero hχ hb hρre hzero
    (twistedMobiusLaplaceDecay_of_subpower χ hk hα hC hupper)

end RHTower
