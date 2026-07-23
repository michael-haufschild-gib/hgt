import GaloisForLFunctions.HTGeometry.SeparatedNodeInterpolantBound

/-!
# Smallness propagation through interpolation on a unit window

A smooth function that is small at `N + 1` separated sample points of a unit
interval and has a controlled `(N+1)`-st derivative there is small on the
whole interval:

`|f x| ≤ (N+1)·2^N/(η^N·N!)·ε₀ + M/(N+1)!`.

The first term is the interpolant of the sampled values (crude separated-node
Lagrange bound), the second the interpolation remainder (iterated Rolle).
With `N ≈ cR` samples at separation `η ≈ 1/(2N)`, sampled values
`ε₀ = e^{-σR}` and derivative bound `M = e^{-δR/2}`, this reads
`|f| ≤ e^{O(cR)}e^{-σR} + e^{-cR log R(1+o(1))}` — the oversampling estimate
whose `R → ∞`, then `c → 0` limit recovers the full sampled decay rate.
-/

noncomputable section

namespace HTGeometry

open Set

/-- **Sampled-smallness estimate**: a smooth function small on `N + 1`
`η`-separated samples of a unit interval is small everywhere on it, up to the
factorially small interpolation remainder. -/
theorem abs_le_of_sampled_small
    {N : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {s : Finset ℝ} (hcard : s.card = N + 1)
    {a : ℝ} (hsub : ↑s ⊆ Set.Icc a (a + 1))
    {η : ℝ} (hη : 0 < η)
    (hsep : ∀ t ∈ s, ∀ u ∈ s, t ≠ u → η ≤ |t - u|)
    {M : ℝ} (hM : ∀ t ∈ Set.Icc a (a + 1), |iteratedDeriv (N + 1) f t| ≤ M)
    {ε₀ : ℝ} (hε₀ : ∀ t ∈ s, |f t| ≤ ε₀)
    {x : ℝ} (hx : x ∈ Set.Icc a (a + 1)) :
    |f x| ≤ (N + 1) * (2 ^ N / (η ^ N * N.factorial)) * ε₀
      + M / (N + 1).factorial := by
  have hclose : ∀ u ∈ s, |x - u| ≤ 1 := by
    intro u hu
    have h1 := hsub hu
    rw [Set.mem_Icc] at h1
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hrem := abs_sub_eval_interpolate_le hf hcard hsub hM hx
  have hsup := abs_eval_interpolate_le_of_separated hcard hη hsep hclose hε₀
  have hprod : (∏ t ∈ s, |x - t|) ≤ 1 :=
    Finset.prod_le_one (fun t _ => abs_nonneg _) fun t ht => hclose t ht
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM x hx)
  have hfact0 : (0:ℝ) ≤ M / (N + 1).factorial := by positivity
  calc |f x|
      = |(f x - (Lagrange.interpolate s id f).eval x)
          + (Lagrange.interpolate s id f).eval x| := by ring_nf
    _ ≤ |f x - (Lagrange.interpolate s id f).eval x|
        + |(Lagrange.interpolate s id f).eval x| := abs_add_le _ _
    _ ≤ M / (N + 1).factorial * ∏ t ∈ s, |x - t|
        + (N + 1) * (2 ^ N / (η ^ N * N.factorial)) * ε₀ :=
        add_le_add hrem hsup
    _ ≤ M / (N + 1).factorial * 1
        + (N + 1) * (2 ^ N / (η ^ N * N.factorial)) * ε₀ := by
        exact add_le_add (mul_le_mul_of_nonneg_left hprod hfact0) le_rfl
    _ = (N + 1) * (2 ^ N / (η ^ N * N.factorial)) * ε₀
        + M / (N + 1).factorial := by ring

end HTGeometry
