import GaloisForLFunctions.HTGeometry.SampledSmallInterpolation
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Complex-valued sampled-smallness estimate

Transfer of the interpolation smallness estimate to an entire function
restricted to a real unit window: real and imaginary parts are interpolated
separately (no complex Rolle theorem is used), with the real iterated
derivatives along the line identified with the complex ones.

`‖H x‖ ≤ 2·((N+1)·2^N/(η^N·N!)·ε₀ + M/(N+1)!)`

for `H` entire, small (`≤ ε₀`) at `N+1` `η`-separated real samples, with
`‖H^{(N+1)}‖ ≤ M` along the window.
-/

noncomputable section

namespace HTGeometry

open Complex Set

/-- The derivative of an entire function is entire. -/
theorem differentiable_deriv_of_entire {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) : Differentiable ℂ (deriv H) := by
  have h := (hH.differentiableOn.analyticOnNhd isOpen_univ).deriv
  rw [← differentiableOn_univ]
  exact h.differentiableOn

/-- Real iterated derivatives along the real axis agree with the complex
iterated derivatives of an entire function. -/
theorem iteratedDeriv_comp_ofReal :
    ∀ (n : ℕ) {H : ℂ → ℂ}, Differentiable ℂ H →
      iteratedDeriv n (fun x : ℝ => H (x : ℂ))
        = fun x : ℝ => iteratedDeriv n H (x : ℂ) := by
  intro n
  induction n with
  | zero =>
    intro H _
    simp
  | succ n ihn =>
    intro H hH
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have hd : deriv (fun x : ℝ => H (x : ℂ))
        = fun x : ℝ => deriv H (x : ℂ) := by
      funext x
      exact ((hH _).hasDerivAt.comp_ofReal).deriv
    rw [hd]
    exact ihn (differentiable_deriv_of_entire hH)

/-- Iterated derivatives commute with a real-linear projection. -/
theorem iteratedDeriv_clm_comp (L : ℂ →L[ℝ] ℝ) :
    ∀ (n : ℕ) {g : ℝ → ℂ}, ContDiff ℝ (⊤ : ℕ∞) g →
      iteratedDeriv n (fun x => L (g x))
        = fun x => L (iteratedDeriv n g x) := by
  intro n
  induction n with
  | zero =>
    intro g _
    simp
  | succ n ihn =>
    intro g hg
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ihn hg]
    funext x
    have hdiff : DifferentiableAt ℝ (iteratedDeriv n g) x := by
      have h := hg.differentiable_iteratedDeriv n (compareOfLessAndEq_eq_lt.mp rfl)
      exact h.differentiableAt
    exact ((L.hasFDerivAt).comp_hasDerivAt x hdiff.hasDerivAt).deriv

/-- The real restriction of an entire function is smooth. -/
theorem contDiff_comp_ofReal {H : ℂ → ℂ} (hH : Differentiable ℂ H) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => H (x : ℂ) :=
  (hH.contDiff.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff

/-- **Complex sampled-smallness estimate**: an entire function small at
`N + 1` separated real samples of a unit window, with `(N+1)`-st derivative
bounded there, is small on the whole window. -/
theorem norm_le_of_sampled_small_complex
    {N : ℕ} {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {s : Finset ℝ} (hcard : s.card = N + 1)
    {a : ℝ} (hsub : ↑s ⊆ Set.Icc a (a + 1))
    {η : ℝ} (hη : 0 < η)
    (hsep : ∀ t ∈ s, ∀ u ∈ s, t ≠ u → η ≤ |t - u|)
    {M : ℝ}
    (hM : ∀ t ∈ Set.Icc a (a + 1), ‖iteratedDeriv (N + 1) H (t : ℂ)‖ ≤ M)
    {ε₀ : ℝ} (hε₀ : ∀ t ∈ s, ‖H (t : ℂ)‖ ≤ ε₀)
    {x : ℝ} (hx : x ∈ Set.Icc a (a + 1)) :
    ‖H (x : ℂ)‖ ≤ 2 * ((N + 1) * (2 ^ N / (η ^ N * N.factorial)) * ε₀
      + M / (N + 1).factorial) := by
  set g : ℝ → ℂ := fun x : ℝ => H (x : ℂ) with hg
  have hgc : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_comp_ofReal hH
  have hgder : iteratedDeriv (N + 1) g = fun t : ℝ =>
      iteratedDeriv (N + 1) H (t : ℂ) := iteratedDeriv_comp_ofReal (N + 1) hH
  -- the two projections
  have hkey : ∀ L : ℂ →L[ℝ] ℝ, (∀ z : ℂ, |L z| ≤ ‖z‖) →
      |L (H (x : ℂ))| ≤ (N + 1) * (2 ^ N / (η ^ N * N.factorial)) * ε₀
        + M / (N + 1).factorial := by
    intro L hLnorm
    have hfL : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => L (g t) :=
      L.contDiff.comp hgc
    have hMder : ∀ t ∈ Set.Icc a (a + 1),
        |iteratedDeriv (N + 1) (fun t : ℝ => L (g t)) t| ≤ M := by
      intro t ht
      rw [iteratedDeriv_clm_comp L (N + 1) hgc]
      calc |L (iteratedDeriv (N + 1) g t)|
          ≤ ‖iteratedDeriv (N + 1) g t‖ := hLnorm _
        _ ≤ M := by
            rw [hgder]
            exact hM t ht
    have hsmall : ∀ t ∈ s, |L (g t)| ≤ ε₀ := by
      intro t ht
      calc |L (g t)| ≤ ‖g t‖ := hLnorm _
        _ ≤ ε₀ := hε₀ t ht
    exact abs_le_of_sampled_small hfL hcard hsub hη hsep hMder hsmall hx
  have hre := hkey Complex.reCLM fun z => by
    simpa using Complex.abs_re_le_norm z
  have him := hkey Complex.imCLM fun z => by
    simpa using Complex.abs_im_le_norm z
  calc ‖H (x : ℂ)‖ ≤ |(H (x : ℂ)).re| + |(H (x : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Complex.reCLM (H (x : ℂ))| + |Complex.imCLM (H (x : ℂ))| := by simp
    _ ≤ ((N + 1) * (2 ^ N / (η ^ N * N.factorial)) * ε₀
          + M / (N + 1).factorial)
        + ((N + 1) * (2 ^ N / (η ^ N * N.factorial)) * ε₀
          + M / (N + 1).factorial) := add_le_add hre him
    _ = 2 * ((N + 1) * (2 ^ N / (η ^ N * N.factorial)) * ε₀
          + M / (N + 1).factorial) := by ring

end HTGeometry
