import GaloisForLFunctions.HTGeometry.ImageSeparatingPolynomial
import GaloisForLFunctions.HTGeometry.RealAnalyticZeroFiniteness

/-!
# A real-analytic curve meets a low-dimensional image finitely often

If a real-analytic curve passes through a point whose coordinates are algebraically independent
over `ℚ`, then it meets the image of any polynomial parametrisation with fewer parameters only
finitely often on any compact set.

No semialgebraic geometry and no o-minimality: the separating polynomial of
`ImageSeparatingPolynomial` vanishes identically on the image and not at the independent point, so
composing it with the curve gives a nonzero real-analytic function whose finitely many zeros already
contain every intersection.  Finiteness of those zeros is
`RealAnalyticZeroFiniteness.finite_zeros_of_analyticOnNhd`.

This is the mechanism that makes exceptional-time sets locally finite for orbits with high
transcendence degree: the intersections with the states reachable by a bounded number of gates are
confined to the zeros of one analytic function.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- A polynomial in real-analytic functions is real-analytic. -/
theorem analyticOnNhd_aeval {r : ℕ} {U : Set ℝ} (g : Fin r → ℝ → ℝ)
    (hg : ∀ i, AnalyticOnNhd ℝ (g i) U) (h : MvPolynomial (Fin r) ℚ) :
    AnalyticOnNhd ℝ (fun t => MvPolynomial.aeval (fun i => g i t) h) U := by
  induction h using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.aeval_C]
      exact analyticOnNhd_const
  | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X]
      exact hp.mul (hg i)

/-- **A real-analytic curve through an algebraically independent point meets a
lower-dimensional polynomial image only finitely often.** -/
theorem finite_meets_image {r m : ℕ} (hr : m < r) (Φ : Fin r → MvPolynomial (Fin m) ℚ)
    (γ : Fin r → ℝ → ℝ) (hγ : ∀ i, AnalyticOnNhd ℝ (γ i) Set.univ)
    {t₀ : ℝ} (hP : AlgebraicIndependent ℚ (fun i => γ i t₀))
    {S : Set ℝ} (hS : IsCompact S) :
    {t ∈ S | ∃ u : Fin m → ℝ, ∀ i, γ i t = MvPolynomial.aeval u (Φ i)}.Finite := by
  obtain ⟨h, -, hker, hP0⟩ := exists_separating_polynomial (K := ℚ) (L := ℝ) hr Φ hP
  have hfan : AnalyticOnNhd ℝ (fun t => MvPolynomial.aeval (fun i => γ i t) h) Set.univ :=
    analyticOnNhd_aeval γ hγ h
  have hfin := finite_zeros_of_analyticOnNhd (U := Set.univ) isPreconnected_univ hfan
    (Set.mem_univ t₀) hP0 hS (Set.subset_univ S)
  refine Set.Finite.subset hfin ?_
  rintro t ⟨htS, u, hu⟩
  refine ⟨htS, ?_⟩
  have harg : (fun i => γ i t) = (fun i => MvPolynomial.aeval u (Φ i)) := funext hu
  rw [Set.mem_preimage, Set.mem_singleton_iff, harg]
  exact aeval_eq_zero_of_aeval_eq_zero hker u

end GaloisForLFunctions.HTGeometry
