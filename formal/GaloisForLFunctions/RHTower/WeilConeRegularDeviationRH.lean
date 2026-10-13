import GaloisForLFunctions.RHTower.WeilFullConeDeviationResidue

/-!
# A Weil-positive system with regular deviation forces RH

Let `lam` be full-cone Weil-positive with Herglotz continuation `Φ_lam`.  On `Re s > 1` its
deviation series is `D(s) = Σ_{n≥2} (lam(n) − Λ(n)) n^{−s} = ξ'/ξ(s) − Φ_lam(s)`, and on
`Re s > 1/2` the function `ξ'/ξ − Φ_lam` has residue `ord_{s₀} ξ` at every point
(`tendsto_sub_mul_logDeriv_xi_sub_weilContinuation`).

**Theorem** (`riemannHypothesis_of_regular_deviation`).  If the deviation series of a
Weil-positive system continues holomorphically to `Re s > 1/2`, the Riemann hypothesis holds.

So, if prime-blind positivity holds and RH fails, every point of the Weil cone has a deviation
series whose continuation is singular at every zero right of the critical line, with residue
exactly its multiplicity.  A detection proof (PBAP ⟹ RH) must exclude precisely such
integer-supported deviations.

**Proof.**  Let `G` be the continuation and `H = ξ' − ξ(Φ_lam + G)`, holomorphic on the half-plane.
On `Re s > 1` we have `H = 0`, so `H ≡ 0` by the identity theorem.  Near a zero `s₀`, `ξ'/ξ − Φ_lam`
then equals `G` off `s₀`, so `(s − s₀)(ξ'/ξ − Φ_lam) → 0`.  The residue law says that limit is
`ord_{s₀} ξ`, so the order vanishes and `ξ(s₀) ≠ 0`.
-/

open Complex Filter Topology Set

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-- **RH from a Weil-positive system whose deviation series is regular right of the line.** -/
theorem riemannHypothesis_of_regular_deviation {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re →
      G s = LSeries (lamC lam) s - LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) :
    RiemannHypothesis := by
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hΦ := differentiableOn_weilContinuation hW
  -- the holomorphic function `ξ' − ξ (Φ + G)` vanishes on the half-plane
  set H : ℂ → ℂ := fun s => deriv xi s - xi s * (weilContinuation hW s + G s) with hH
  have hdxi : DifferentiableOn ℂ (deriv xi) U :=
    (xi_differentiable.differentiableOn.deriv isOpen_univ).mono (subset_univ _)
  have hHa : AnalyticOnNhd ℂ H U :=
    (hdxi.sub (xi_differentiable.differentiableOn.mul (hΦ.add hG))).analyticOnNhd hUo
  have hU2 : (2 : ℂ) ∈ U := by simp only [hU, Set.mem_setOf_eq, Complex.re_ofNat]; norm_num
  have hHev : H =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hV : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hV] with s hs
    have hs' : 1 < s.re := hs
    have hne1 : s ≠ 1 := by
      intro h; rw [h, Complex.one_re] at hs'; exact lt_irrefl 1 hs'
    have hxi0 : xi s ≠ 0 := fun h =>
      riemannZeta_ne_zero_of_one_lt_re hs' ((xi_eq_zero_iff (by linarith) hne1).mp h)
    have hdev := logDeriv_xi_sub_weilContinuation_eq hW hs'
    rw [← hGeq s hs', logDeriv_apply] at hdev
    simp only [hH, Pi.zero_apply]
    have : deriv xi s = xi s * (weilContinuation hW s + G s) := by
      field_simp at hdev
      linear_combination hdev
    rw [this, sub_self]
  have hH0 : EqOn H 0 U :=
    hHa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_halfSpace_re_gt _).isPreconnected
      hU2 hHev
  -- no zero of `ξ` right of the critical line
  refine rh_iff_xi_ne_zero_right.mpr fun s₀ hs₀ => ?_
  have hs₀' : 1 / 2 < s₀.re := hs₀
  have hres := tendsto_sub_mul_logDeriv_xi_sub_weilContinuation hW hs₀'
  have hUs₀ : U ∈ 𝓝 s₀ := hUo.mem_nhds hs₀'
  have hGc : ContinuousAt G s₀ := (hG.differentiableAt hUs₀).continuousAt
  have hlin : Tendsto (fun s : ℂ => (s - s₀) * G s) (𝓝[≠] s₀) (𝓝 0) := by
    have h1 : ContinuousAt (fun s : ℂ => s - s₀) s₀ := by fun_prop
    have h : Tendsto (fun s : ℂ => (s - s₀) * G s) (𝓝 s₀) (𝓝 ((s₀ - s₀) * G s₀)) :=
      (h1.mul hGc).tendsto
    rw [sub_self, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hord : analyticOrderAt xi s₀ ≠ ⊤ := xi_orderAt_ne_top s₀
  have hnz : ∀ᶠ s in 𝓝[≠] s₀, xi s ≠ 0 := by
    rcases (xi_differentiable.analyticAt s₀).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (analyticOrderAt_eq_top.mpr h) hord
    · exact h
  have hU' : ∀ᶠ s in 𝓝[≠] s₀, s ∈ U := mem_nhdsWithin_of_mem_nhds hUs₀
  have heq : (fun s => (s - s₀) * (logDeriv xi s - weilContinuation hW s)) =ᶠ[𝓝[≠] s₀]
      fun s => (s - s₀) * G s := by
    filter_upwards [hnz, hU'] with s hs hsU
    have hHs : H s = 0 := hH0 hsU
    simp only [hH] at hHs
    rw [logDeriv_apply]
    congr 1
    field_simp
    linear_combination hHs
  have h0 := tendsto_nhds_unique (hres.congr' heq) hlin
  have hnat : analyticOrderNatAt xi s₀ = 0 := by exact_mod_cast h0
  have hzero : analyticOrderAt xi s₀ = 0 := by
    unfold analyticOrderNatAt at hnat
    rcases (ENat.toNat_eq_zero.mp hnat) with h | h
    · exact h
    · exact absurd h hord
  exact ((analyticOrderAt_eq_zero.mp hzero).resolve_left
    (not_not.mpr (xi_differentiable.analyticAt s₀)))

end RHTower.WeilSpectral
