import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# The normalization defect of a reducible curve

The appendix of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), shows that the Gauss curvature of the induced fibre metric cannot
stay bounded below.  Assuming it did, two evaluations of the total curvature of the central fibre
would have to agree:

```text
(1/2π) ∫_{X₀ ∖ Sing X₀} K₀ dv₀ = χ(X_s)                                        (10.1)
(1/2π) ∫_{X₀ ∖ Sing X₀} K₀ dv₀ = χ(X_s) + Σ_p ( 2δ_p + Σ_{q ↦ p} (N_q − 1) )   (10.2)+(10.3)
```

They cannot, because every singular point contributes `δ_p ≥ 1` and every branch contributes
`N_q − 1 ≥ 0`, so the second evaluation is strictly larger.  That strict positivity of the
normalization defect is the entire arithmetic of the appendix, and it is what is proved here; the
two evaluations themselves are the cited Gauss–Bonnet and normalization formulas.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- **The normalization defect is strictly positive.**

Over a nonempty set of singular points, with `δ_p ≥ 1` (the delta invariant of a curve singularity)
and `N_q ≥ 1` (the branch multiplicities), the total defect `Σ_p (2δ_p + Σ_q (N_q − 1))` is
positive. -/
theorem normalizationDefect_pos {ι : Type*} {P : Finset ι} (hP : P.Nonempty)
    {δ D : ι → ℤ} (hδ : ∀ p ∈ P, 1 ≤ δ p) (hD : ∀ p ∈ P, 0 ≤ D p) :
    0 < ∑ p ∈ P, (2 * δ p + D p) := by
  obtain ⟨p₀, hp₀⟩ := hP
  have hnonneg : ∀ p ∈ P, 0 ≤ 2 * δ p + D p := by
    intro p hp
    have := hδ p hp
    have := hD p hp
    linarith
  have hpos : 0 < 2 * δ p₀ + D p₀ := by
    have := hδ p₀ hp₀
    have := hD p₀ hp₀
    linarith
  exact Finset.sum_pos' hnonneg ⟨p₀, hp₀, hpos⟩

/-- **Appendix Lemma 10.1, arithmetic core.**

The two evaluations of the total curvature of a reducible reduced central fibre are incompatible:
the Gauss–Bonnet value `χ(X_s)` and the normalization value `χ(X_s) + defect` cannot agree, because
the defect is positive.  Hence the standing assumption that the curvature stays bounded below is
untenable. -/
theorem gaussBonnet_normalization_incompatible {ι : Type*} {P : Finset ι} (hP : P.Nonempty)
    {δ D : ι → ℤ} (hδ : ∀ p ∈ P, 1 ≤ δ p) (hD : ∀ p ∈ P, 0 ≤ D p)
    {I χ : ℤ} (h1 : I = χ) (h2 : I = χ + ∑ p ∈ P, (2 * δ p + D p)) : False := by
  have hpos := normalizationDefect_pos hP hδ hD
  omega

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
