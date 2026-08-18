import GaloisForLFunctions.HTGeometry.AlgebraSpectrumCovering
import GaloisForLFunctions.HTGeometry.SplitFibresPackage
import GaloisForLFunctions.HTGeometry.AlgebraCharpoly
import GaloisForLFunctions.HTGeometry.PowerMatrixCramer
import GaloisForLFunctions.HTGeometry.PowerDeterminantNonvanishing
import GaloisForLFunctions.HTGeometry.SplitAlgebraSeparation
import GaloisForLFunctions.HTGeometry.SplitParameterSeparability

/-!
# The chart data of a finite free algebra with split fibres

Assembling `AlgebraCharpoly`, `PowerMatrixCramer`, `SplitAlgebraSeparation`,
`PowerDeterminantNonvanishing`, `SplitParameterSeparability` and `SplitFibresPackage` produces the
chart hypothesis of `AlgebraSpectrumCovering`, so the complex-point space of a finite free
`ℂ[X]`-algebra all of whose fibres are split is a covering space of the parameter line.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B] [IsScalarTower ℂ ℂ[X] B]

/-- **The chart data of a finite free algebra with split fibres.** -/
theorem exists_chart_of_splitFibres [Module.Free ℂ[X] B] [Module.Finite ℂ[X] B]
    {n : ℕ} (hn : 1 ≤ n) (e : Module.Basis (Fin n) ℂ[X] B) (h : SplitFibres B n)
    (χ₀ : AlgSpec B) :
    ∃ (θ : B) (p : ℂ[X][X]) (U : Set ℂ), Polynomial.aeval θ p = 0 ∧ p.Monic ∧ IsOpen U ∧
      AlgSpec.proj B χ₀ ∈ U ∧
      (∀ b : B, ∃ (q : ℂ[X][X]) (g : ℂ[X]), (∀ s ∈ U, g.eval s ≠ 0) ∧
        (algebraMap ℂ[X] B g) * b = Polynomial.aeval θ q) ∧
      (∀ s ∈ U, (biFibre p s).Separable) ∧
      (∀ s ∈ U, {χ : AlgSpec B | AlgSpec.proj B χ = s}.ncard = p.natDegree) := by
  classical
  set s₀ := AlgSpec.proj B χ₀ with hs₀
  obtain ⟨χ, hproj, hsurj, hrange⟩ := h s₀
  obtain ⟨θ, hθ⟩ := exists_separating_of_surjective (fun i => (χ i : B →ₐ[ℂ] ℂ)) hsurj
  refine ⟨θ, algCharpoly ℂ[X] θ,
    {s : ℂ | ((powerMatrix e θ).det).eval s ≠ 0},
    aeval_algCharpoly ℂ[X] θ, algCharpoly_monic ℂ[X] θ, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_ne_fun ((powerMatrix e θ).det).continuous_aeval continuous_const
  · show ((powerMatrix e θ).det).eval s₀ ≠ 0
    have hcomm : ∀ i : Fin n, ∀ a : ℂ[X],
        (χ i : B →+* ℂ) (algebraMap ℂ[X] B a) = (Polynomial.evalRingHom s₀) a := by
      intro i a
      have := AlgSpec.apply_algebraMap B (χ i) a
      rw [hproj i] at this
      exact this
    exact det_powerMatrix_map_ne_zero e θ (Polynomial.evalRingHom s₀)
      (fun i => (χ i : B →+* ℂ)) hcomm hθ
  · intro b
    obtain ⟨q, hq⟩ := exists_aeval_of_det_smul e θ b
    exact ⟨q, (powerMatrix e θ).det, fun s hs => hs, by rwa [Algebra.smul_def] at hq⟩
  · intro s hs
    obtain ⟨ψ, hψproj, hψsurj, hψrange⟩ := h s
    have hgen : ∀ b : B, ∃ (q : ℂ[X][X]) (g : ℂ[X]),
        (∀ t ∈ ({s} : Set ℂ), g.eval t ≠ 0) ∧
          (algebraMap ℂ[X] B g) * b = Polynomial.aeval θ q := by
      intro b
      obtain ⟨q, hq⟩ := exists_aeval_of_det_smul e θ b
      refine ⟨q, (powerMatrix e θ).det, ?_, by rwa [Algebra.smul_def] at hq⟩
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact hs
    have hψθ : Function.Injective fun i => ψ i θ := by
      intro i j hij
      apply injective_of_surjective_family ψ hψsurj
      apply AlgSpec.toPlane_injOn hgen
      · show AlgSpec.proj B (ψ i) ∈ ({s} : Set ℂ)
        rw [hψproj i]; rfl
      · show AlgSpec.proj B (ψ j) ∈ ({s} : Set ℂ)
        rw [hψproj j]; rfl
      · exact Prod.ext ((hψproj i).trans (hψproj j).symm) hij
    exact separable_biFibre_of_separating hn (aeval_algCharpoly ℂ[X] θ)
      (algCharpoly_monic ℂ[X] θ) (algCharpoly_natDegree ℂ[X] e θ) ψ hψproj hψθ
  · intro s _
    rw [ncard_fibre_of_splitFibres h s, algCharpoly_natDegree ℂ[X] e θ]

/-- **The complex-point space of a finite free algebra with split fibres is a covering space of the
parameter line.** -/
theorem isCoveringMap_proj_of_splitFibres [Module.Free ℂ[X] B] [Module.Finite ℂ[X] B]
    {n : ℕ} (hn : 1 ≤ n) (e : Module.Basis (Fin n) ℂ[X] B) (h : SplitFibres B n) :
    IsCoveringMap (AlgSpec.proj B) := by
  refine AlgSpec.isCoveringMap_proj ?_
  intro χ₀
  obtain ⟨θ, p, U, hp, hmonic, hU, hmem, hgen, hsep, hcard⟩ :=
    exists_chart_of_splitFibres hn e h χ₀
  exact ⟨θ, p, U, hp, hmonic, hU, hmem, hgen, hsep, hcard⟩

end

end GaloisForLFunctions.HTGeometry
