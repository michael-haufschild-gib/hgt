import GaloisForLFunctions.HTGeometry.SampledSmallComplex

/-!
# Sampled smallness for smooth curves and half-plane analytic restrictions

Two generalizations that free the sampled-window machinery from global
entirety:

* the window estimate for an arbitrary globally smooth curve
  `g : ℝ → ℂ` with real iterated-derivative bounds — the projection
  argument of the complex estimate never used analyticity;
* for `H` analytic on a right half-plane, the real restriction is smooth
  there and its real iterated derivatives agree with the complex ones —
  the local form of the entire-function identification, proved by the
  same induction with eventual equality of derivatives on `Ioi T`.
-/

noncomputable section

namespace HTGeometry

open Complex Set

/-- **Sampled-smallness for smooth curves**: a globally smooth
`g : ℝ → ℂ` small at `N + 1` separated samples with bounded `(N+1)`-st
derivative is small on the whole window. -/
theorem norm_le_of_sampled_small_smooth
    {N : ℕ} {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {s : Finset ℝ} (hcard : s.card = N + 1)
    {a : ℝ} (hsub : ↑s ⊆ Set.Icc a (a + 1))
    {η : ℝ} (hη : 0 < η)
    (hsep : ∀ t ∈ s, ∀ u ∈ s, t ≠ u → η ≤ |t - u|)
    {M : ℝ}
    (hM : ∀ t ∈ Set.Icc a (a + 1), ‖iteratedDeriv (N + 1) g t‖ ≤ M)
    {ε₀ : ℝ} (_hε₀0 : 0 ≤ ε₀) (hε₀ : ∀ t ∈ s, ‖g t‖ ≤ ε₀)
    {x : ℝ} (hx : x ∈ Set.Icc a (a + 1)) :
    ‖g x‖ ≤ 2 * ((N + 1) * (2 ^ N / (η ^ N * N.factorial)) * ε₀
      + M / (N + 1).factorial) := by
  have hkey : ∀ L : ℂ →L[ℝ] ℝ, (∀ z : ℂ, |L z| ≤ ‖z‖) →
      |L (g x)| ≤ (N + 1) * (2 ^ N / (η ^ N * N.factorial)) * ε₀
        + M / (N + 1).factorial := by
    intro L hLnorm
    have hfL : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => L (g t) :=
      L.contDiff.comp hg
    have hMder : ∀ t ∈ Set.Icc a (a + 1),
        |iteratedDeriv (N + 1) (fun t : ℝ => L (g t)) t| ≤ M := by
      intro t ht
      rw [iteratedDeriv_clm_comp L (N + 1) hg]
      calc |L (iteratedDeriv (N + 1) g t)|
          ≤ ‖iteratedDeriv (N + 1) g t‖ := hLnorm _
        _ ≤ M := hM t ht
    have hsmall : ∀ t ∈ s, |L (g t)| ≤ ε₀ := by
      intro t ht
      calc |L (g t)| ≤ ‖g t‖ := hLnorm _
        _ ≤ ε₀ := hε₀ t ht
    exact abs_le_of_sampled_small hfL hcard hsub hη hsep hMder hsmall hx
  have hre := hkey Complex.reCLM fun z => by
    simpa using Complex.abs_re_le_norm z
  have him := hkey Complex.imCLM fun z => by
    simpa using Complex.abs_im_le_norm z
  calc ‖g x‖ ≤ |(g x).re| + |(g x).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Complex.reCLM (g x)| + |Complex.imCLM (g x)| := by simp
    _ ≤ ((N + 1) * (2 ^ N / (η ^ N * N.factorial)) * ε₀
          + M / (N + 1).factorial)
        + ((N + 1) * (2 ^ N / (η ^ N * N.factorial)) * ε₀
          + M / (N + 1).factorial) := add_le_add hre him
    _ = 2 * ((N + 1) * (2 ^ N / (η ^ N * N.factorial)) * ε₀
          + M / (N + 1).factorial) := by ring

/-- The real restriction of a half-plane-analytic function is smooth on
the half-line. -/
theorem contDiffOn_comp_ofReal_of_analyticAt {T : ℝ} {H : ℂ → ℂ}
    (hH : ∀ t : ℝ, T < t → AnalyticAt ℂ H (t : ℂ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => H (t : ℂ)) (Set.Ioi T) := by
  intro t ht
  apply ContDiffAt.contDiffWithinAt
  have h1 : ContDiffAt ℂ (⊤ : ℕ∞) H (t : ℂ) :=
    (hH t ht).contDiffAt
  exact (h1.restrict_scalars ℝ).comp t
    Complex.ofRealCLM.contDiff.contDiffAt

/-- **Local derivative identification**: on the half-line over which `H`
is analytic, the real iterated derivatives of the restriction agree with
the complex iterated derivatives. -/
theorem iteratedDeriv_comp_ofReal_of_analyticAt {T : ℝ} :
    ∀ (n : ℕ) {H : ℂ → ℂ}, (∀ t : ℝ, T < t → AnalyticAt ℂ H (t : ℂ)) →
      ∀ t : ℝ, T < t →
      iteratedDeriv n (fun x : ℝ => H (x : ℂ)) t
        = iteratedDeriv n H (t : ℂ) := by
  intro n
  induction n with
  | zero =>
    intro H _ t _
    simp
  | succ n ihn =>
    intro H hH t ht
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have hev : deriv (fun x : ℝ => H (x : ℂ))
        =ᶠ[nhds t] fun x : ℝ => deriv H (x : ℂ) := by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      exact ((hH u hu).differentiableAt.hasDerivAt.comp_ofReal).deriv
    rw [Filter.EventuallyEq.iteratedDeriv_eq n hev]
    exact ihn (fun u hu => (hH u hu).deriv) t ht

end HTGeometry
