import GaloisForLFunctions.RHTower.Sieve.LogNormSegment

/-!
# Transport of `log‖g‖` on convex zero-free sets

A nowhere-zero analytic function on a convex open set has an analytic logarithm
(`exists_analyticOnNhd_exp_eq_convex`). If `‖g'/g − c‖ ≤ E` on the segment `[z₂, z₁]`, then

`log‖g z₁‖ − log‖g z₂‖ ≤ Re((z₁ − z₂) c) + E ‖z₁ − z₂‖`

(`log_norm_sub_le_of_logDeriv_sub_const`): the logarithm `L` of `g` has `(L − c·)' = g'/g − c`, the
mean value inequality bounds `L z₁ − L z₂ − c(z₁ − z₂)`, and `log‖g‖ = Re L`.
-/

noncomputable section

open Complex Set

namespace RHTower

/-- A nowhere-zero analytic function on a convex open set has an analytic logarithm. -/
theorem exists_analyticOnNhd_exp_eq_convex {U : Set ℂ} (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hUne : U.Nonempty) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hg0 : ∀ z ∈ U, g z ≠ 0) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ ∀ z ∈ U, Complex.exp (f z) = g z := by
  have hUsc : IsSimplyConnected U := by
    haveI : ContractibleSpace U := hUc.contractibleSpace hUne
    exact SimplyConnectedSpace.ofContractible _
  have hU0 : (0 : ℂ) ∉ g '' U := by
    rintro ⟨z, hz, hgz⟩
    exact hg0 z hz hgz
  obtain ⟨f, hfc, hfeq⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUsc hUo hg.continuousOn hU0
  exact ⟨f, U0KummerBranch.analyticOnNhd_of_continuousOn_exp_eq hUo hfc hg
    (fun z hz => hfeq hz), fun z hz => hfeq hz⟩

/-- The derivative of an analytic logarithm on an open set is the logarithmic derivative. -/
theorem deriv_analyticLog_eq_of_isOpen {g L : ℂ → ℂ} {U : Set ℂ} (hUo : IsOpen U)
    (hg0 : ∀ w ∈ U, g w ≠ 0) (hL : AnalyticOnNhd ℂ L U)
    (hLexp : ∀ w ∈ U, Complex.exp (L w) = g w) {z : ℂ} (hz : z ∈ U) :
    deriv L z = logDeriv g z := by
  have hLd : HasDerivAt L (deriv L z) z := (hL z hz).differentiableAt.hasDerivAt
  have hexpd : HasDerivAt (fun w => Complex.exp (L w)) (Complex.exp (L z) * deriv L z) z :=
    hLd.cexp
  have hEq : (fun w => Complex.exp (L w)) =ᶠ[nhds z] g := by
    filter_upwards [hUo.mem_nhds hz] with w hw
    exact hLexp w hw
  have hgd : HasDerivAt g (Complex.exp (L z) * deriv L z) z :=
    hexpd.congr_of_eventuallyEq hEq.symm
  have hgz : Complex.exp (L z) = g z := hLexp z hz
  rw [logDeriv_apply, hgd.deriv, hgz, mul_comm, mul_div_assoc, div_self (hg0 z hz), mul_one]

/-- **Transport of `log‖g‖` with a constant main term.** -/
theorem log_norm_sub_le_of_logDeriv_sub_const {g : ℂ → ℂ} {U : Set ℂ} (hUo : IsOpen U)
    (hUc : Convex ℝ U) (hg : AnalyticOnNhd ℂ g U) (hg0 : ∀ z ∈ U, g z ≠ 0) {z₁ z₂ c : ℂ} {E : ℝ}
    (hz₁ : z₁ ∈ U) (hz₂ : z₂ ∈ U)
    (hE : ∀ u ∈ Icc (0 : ℝ) 1, ‖logDeriv g (z₂ + (u : ℂ) * (z₁ - z₂)) - c‖ ≤ E) :
    Real.log ‖g z₁‖ - Real.log ‖g z₂‖ ≤ ((z₁ - z₂) * c).re + E * ‖z₁ - z₂‖ := by
  obtain ⟨f, hf, hfexp⟩ := exists_analyticOnNhd_exp_eq_convex hUo hUc ⟨z₁, hz₁⟩ hg hg0
  have hseg : ∀ u ∈ Icc (0 : ℝ) 1, z₂ + (u : ℂ) * (z₁ - z₂) ∈ U := by
    intro u hu
    have h := hUc hz₂ hz₁ (show 0 ≤ 1 - u by linarith [hu.2]) hu.1 (by ring)
    have e : (1 - u) • z₂ + u • z₁ = z₂ + (u : ℂ) * (z₁ - z₂) := by
      rw [Complex.real_smul, Complex.real_smul]; push_cast; ring
    rwa [e] at h
  set L : ℂ → ℂ := fun z => f z - c * z with hLdef
  have hdiff : ∀ u ∈ Icc (0 : ℝ) 1, DifferentiableAt ℂ L (z₂ + (u : ℂ) * (z₁ - z₂)) := by
    intro u hu
    exact ((hf _ (hseg u hu)).differentiableAt).sub (differentiableAt_id.const_mul c)
  have hderiv : ∀ u ∈ Icc (0 : ℝ) 1, ‖deriv L (z₂ + (u : ℂ) * (z₁ - z₂))‖ ≤ E := by
    intro u hu
    have hz := hseg u hu
    have h1 : deriv L (z₂ + (u : ℂ) * (z₁ - z₂)) =
        deriv f (z₂ + (u : ℂ) * (z₁ - z₂)) - c := by
      have hfd : HasDerivAt f (deriv f (z₂ + (u : ℂ) * (z₁ - z₂))) (z₂ + (u : ℂ) * (z₁ - z₂)) :=
        (hf _ hz).differentiableAt.hasDerivAt
      have hcd : HasDerivAt (fun z : ℂ => c * z) c (z₂ + (u : ℂ) * (z₁ - z₂)) := by
        simpa using (hasDerivAt_id (z₂ + (u : ℂ) * (z₁ - z₂))).const_mul c
      exact (hfd.sub hcd).deriv
    rw [h1, deriv_analyticLog_eq_of_isOpen hUo hg0 hf hfexp hz]
    exact hE u hu
  have hmv := Sieve.norm_sub_le_segment hdiff hderiv
  have hlog : ∀ z ∈ U, Real.log ‖g z‖ = (f z).re := by
    intro z hz
    rw [← hfexp z hz, Complex.norm_exp, Real.log_exp]
  rw [hlog z₁ hz₁, hlog z₂ hz₂]
  have e : (f z₁).re - (f z₂).re = (L z₁ - L z₂).re + ((z₁ - z₂) * c).re := by
    simp only [hLdef, Complex.sub_re, Complex.mul_re, Complex.sub_im]
    ring
  rw [e]
  have := (Complex.re_le_norm (L z₁ - L z₂)).trans hmv
  linarith

end RHTower
