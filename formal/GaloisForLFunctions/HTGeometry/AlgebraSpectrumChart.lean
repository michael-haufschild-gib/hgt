import GaloisForLFunctions.HTGeometry.AlgebraSpectrumFibre

/-!
# The inverse chart is continuous

Where a chosen element generates the algebra, every element takes at a complex point the value
`q(s, t) / g(s)`, a rational expression in the chart coordinates.  Hence any set-theoretic inverse
of the chart map is continuous — which is what upgrades the fibrewise bijection of
`AlgebraSpectrumFibre` to a homeomorphism, and so to the even-covering property.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B] [IsScalarTower ℂ ℂ[X] B]

/-- Where `θ` generates, the value of any element at a `ℂ`-point is a rational expression in the
chart coordinates. -/
theorem eval_eq_of_gen {θ : B} {U : Set ℂ}
    {b : B} {q : ℂ[X][X]} {g : ℂ[X]} (hg : ∀ s ∈ U, g.eval s ≠ 0)
    (hb : (algebraMap ℂ[X] B g) * b = Polynomial.aeval θ q)
    {χ : AlgSpec B} (hχ : AlgSpec.proj B χ ∈ U) :
    χ b = biEval q (AlgSpec.toPlane θ χ) / g.eval (AlgSpec.proj B χ) := by
  have h : g.eval (AlgSpec.proj B χ) * χ b = biEval q (AlgSpec.toPlane θ χ) := by
    have := congrArg (fun x => χ x) hb
    simpa [AlgSpec.apply_algebraMap B χ g, AlgSpec.apply_aeval θ q χ, AlgSpec.toPlane] using this
  rw [eq_div_iff (hg _ hχ), mul_comm]
  exact h

/-- **Continuity of the inverse chart.**  Any set-theoretic inverse of the chart map is continuous,
because every element of the algebra is a rational expression in the chart coordinates. -/
theorem continuousOn_of_toPlane_eq {θ : B} {U : Set ℂ}
    (hgen : ∀ b : B, ∃ (q : ℂ[X][X]) (g : ℂ[X]), (∀ s ∈ U, g.eval s ≠ 0) ∧
      (algebraMap ℂ[X] B g) * b = Polynomial.aeval θ q)
    {V : Set (ℂ × ℂ)} (Ψ : ℂ × ℂ → AlgSpec B)
    (hΨ : ∀ z ∈ V, AlgSpec.toPlane θ (Ψ z) = z)
    (hproj : ∀ z ∈ V, AlgSpec.proj B (Ψ z) ∈ U) :
    ContinuousOn Ψ V := by
  rw [AlgSpec.isInducing_coe.continuousOn_iff]
  refine continuousOn_pi.mpr fun b => ?_
  obtain ⟨q, g, hg, hb⟩ := hgen b
  have hEq : ∀ z ∈ V, (Ψ z) b = biEval q z / g.eval z.1 := by
    intro z hz
    have hfst : AlgSpec.proj B (Ψ z) = z.1 := by
      have h := hΨ z hz
      rw [AlgSpec.toPlane] at h
      exact congrArg Prod.fst h
    rw [eval_eq_of_gen hg hb (hproj z hz), hΨ z hz, hfst]
  refine ContinuousOn.congr ?_ hEq
  refine ContinuousOn.div ((continuous_biEval q).continuousOn) ?_ ?_
  · exact ((Polynomial.continuous_aeval g).comp continuous_fst).continuousOn
  · intro z hz
    have h1 : AlgSpec.proj B (Ψ z) ∈ U := hproj z hz
    have h2 : AlgSpec.proj B (Ψ z) = z.1 := by
      have := hΨ z hz
      rw [AlgSpec.toPlane] at this
      exact congrArg Prod.fst this
    rw [← h2]
    exact hg _ h1

end

end GaloisForLFunctions.HTGeometry
