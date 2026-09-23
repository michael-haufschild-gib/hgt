import GaloisForLFunctions.HTGeometry.AnalyticImageFiniteness
import Mathlib.Analysis.Complex.Basic

/-!
# A complex-valued analytic curve meets a low-dimensional image finitely often

The real statement of `AnalyticImageFiniteness` charges one parameter per *real* degree of freedom.
For a complex orbit and complex gate entries that doubles the parameter count and loses a factor
two in the exceptional-time theorem.  The whole mechanism goes through verbatim over `ℂ`: the
separating polynomial is base-field generic, a polynomial in complex-valued real-analytic functions
is real-analytic, and the zeros of a complex-valued real-analytic function are the zeros of the
real-analytic function `(Re f)² + (Im f)²`.

## Main results

* `analyticOnNhd_aeval_complex` — a polynomial in complex-valued real-analytic functions.
* `finite_zeros_of_analyticOnNhd_complex` — finiteness of the zero set.
* `finite_meets_image_subfamily_complex` — **the complex-parameter finiteness theorem.**
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Set

/-- A polynomial in complex-valued real-analytic functions is real-analytic. -/
theorem analyticOnNhd_aeval_complex {r : ℕ} {U : Set ℝ} (g : Fin r → ℝ → ℂ)
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

/-- **Finiteness of the zero set of a complex-valued real-analytic function.** -/
theorem finite_zeros_of_analyticOnNhd_complex {f : ℝ → ℂ} {U : Set ℝ}
    (hUconn : IsPreconnected U) (hf : AnalyticOnNhd ℝ f U) {x₀ : ℝ} (hx₀ : x₀ ∈ U)
    (hfx₀ : f x₀ ≠ 0) {K : Set ℝ} (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ f ⁻¹' {0}).Finite := by
  classical
  set g : ℝ → ℝ := fun t => (f t).re ^ (2 : ℕ) + (f t).im ^ (2 : ℕ) with hg
  have hre : AnalyticOnNhd ℝ (fun t => (f t).re) U :=
    Complex.reCLM.comp_analyticOnNhd hf
  have him : AnalyticOnNhd ℝ (fun t => (f t).im) U :=
    Complex.imCLM.comp_analyticOnNhd hf
  have hgan : AnalyticOnNhd ℝ g U := (hre.pow 2).add (him.pow 2)
  have hzero : ∀ t, g t = 0 ↔ f t = 0 := by
    intro t
    constructor
    · intro h0
      have h0' : (f t).re ^ (2 : ℕ) + (f t).im ^ (2 : ℕ) = 0 := h0
      have hre0 : (f t).re = 0 := by nlinarith [sq_nonneg (f t).re, sq_nonneg (f t).im]
      have him0 : (f t).im = 0 := by nlinarith [sq_nonneg (f t).re, sq_nonneg (f t).im]
      exact Complex.ext hre0 him0
    · intro h0
      show (f t).re ^ (2 : ℕ) + (f t).im ^ (2 : ℕ) = 0
      rw [h0]
      simp
  have hgx₀ : g x₀ ≠ 0 := fun h0 => hfx₀ ((hzero x₀).mp h0)
  have hfin := finite_zeros_of_analyticOnNhd hUconn hgan hx₀ hgx₀ hK hKU
  refine Set.Finite.subset hfin ?_
  rintro t ⟨htK, htf⟩
  refine ⟨htK, ?_⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff]
  exact (hzero t).mpr htf

/-- **A complex-valued analytic curve through an algebraically independent point meets a
lower-dimensional complex-parameter polynomial image only finitely often.** -/
theorem finite_meets_image_subfamily_complex {r m k : ℕ} (hr : m < k) (σ : Fin k → Fin r)
    (Φ : Fin r → MvPolynomial (Fin m) ℚ) (γ : Fin r → ℝ → ℂ)
    (hγ : ∀ i, AnalyticOnNhd ℝ (γ i) Set.univ)
    {t₀ : ℝ} (hP : AlgebraicIndependent ℚ (fun i => γ (σ i) t₀))
    {S : Set ℝ} (hS : IsCompact S) :
    {t ∈ S | ∃ u : Fin m → ℂ, ∀ i, γ i t = MvPolynomial.aeval u (Φ i)}.Finite := by
  obtain ⟨h, hker, hP0⟩ :=
    exists_separating_polynomial_subfamily (K := ℚ) (L := ℂ) hr σ Φ (P := fun i => γ i t₀) hP
  have hfan : AnalyticOnNhd ℝ (fun t => MvPolynomial.aeval (fun i => γ i t) h) Set.univ :=
    analyticOnNhd_aeval_complex γ hγ h
  have hfin := finite_zeros_of_analyticOnNhd_complex (U := Set.univ) isPreconnected_univ hfan
    (Set.mem_univ t₀) hP0 hS (Set.subset_univ S)
  refine Set.Finite.subset hfin ?_
  rintro t ⟨htS, u, hu⟩
  refine ⟨htS, ?_⟩
  have harg : (fun i => γ i t) = (fun i => MvPolynomial.aeval u (Φ i)) := funext hu
  rw [Set.mem_preimage, Set.mem_singleton_iff, harg]
  exact aeval_eq_zero_of_aeval_eq_zero hker u

end GaloisForLFunctions.HTGeometry
