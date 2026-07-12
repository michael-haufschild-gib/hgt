import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Graph saturation from annihilator rigidity

This module formalizes the Hilbert-space core of the singular Toeplitz graph argument. The graph
of two linear realizations of a common algebraic domain is dense in the full Hilbert product
exactly when its joint inner-product annihilator is trivial. The later Toeplitz module must prove
that rigidity using the relevant half-Fourier theorem; it is not assumed here as graph closure.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {D H₁ H₂ : Type*}
  [AddCommMonoid D] [Module ℂ D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

/-- Graph submodule of two linear realizations `i` and `A` of the same algebraic domain, equipped
with the genuine Hilbert `L²` product norm. -/
def linearGraphSubmodule (i : D →ₗ[ℂ] H₁) (A : D →ₗ[ℂ] H₂) :
    Submodule ℂ (WithLp 2 (H₁ × H₂)) :=
  LinearMap.range ((WithLp.linearEquiv 2 ℂ (H₁ × H₂)).symm.toLinearMap.comp (i.prod A))

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- Exact description of the orthogonal complement of a linear graph. -/
theorem mem_linearGraphSubmodule_orthogonal_iff
    (i : D →ₗ[ℂ] H₁) (A : D →ₗ[ℂ] H₂) (z : WithLp 2 (H₁ × H₂)) :
    z ∈ (linearGraphSubmodule i A)ᗮ ↔
      ∀ d : D, inner ℂ (i d) z.ofLp.1 + inner ℂ (A d) z.ofLp.2 = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h d
    have hd := h (WithLp.toLp 2 (i d, A d)) ⟨d, rfl⟩
    simpa [WithLp.prod_inner_apply] using hd
  · intro h u hu
    obtain ⟨d, rfl⟩ := hu
    simpa [WithLp.prod_inner_apply] using h d

/-- **Graph-saturation principle.** If the only joint annihilator of the two realizations is zero,
then the graph closure is the entire Hilbert product. -/
theorem linearGraphSubmodule_closure_eq_top_of_annihilator
    (i : D →ₗ[ℂ] H₁) (A : D →ₗ[ℂ] H₂)
    (hann : ∀ x : H₁, ∀ y : H₂,
      (∀ d : D, inner ℂ (i d) x + inner ℂ (A d) y = 0) → x = 0 ∧ y = 0) :
    (linearGraphSubmodule i A).topologicalClosure = ⊤ := by
  have horth : (linearGraphSubmodule i A)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hrel := (mem_linearGraphSubmodule_orthogonal_iff i A z).mp hz
    rcases hann z.ofLp.1 z.ofLp.2 hrel with ⟨hx, hy⟩
    apply WithLp.ofLp_injective 2
    exact Prod.ext hx hy
  calc
    (linearGraphSubmodule i A).topologicalClosure =
        (linearGraphSubmodule i A)ᗮᗮ :=
      (Submodule.orthogonal_orthogonal_eq_closure _).symm
    _ = (⊥ : Submodule ℂ (WithLp 2 (H₁ × H₂)))ᗮ := by rw [horth]
    _ = ⊤ := Submodule.bot_orthogonal_eq_top

/-- **Exact graph-saturation criterion.** A linear graph is dense in the full Hilbert product if
and only if its joint inner-product annihilator is trivial. -/
theorem linearGraphSubmodule_closure_eq_top_iff_annihilator
    (i : D →ₗ[ℂ] H₁) (A : D →ₗ[ℂ] H₂) :
    (linearGraphSubmodule i A).topologicalClosure = ⊤ ↔
      ∀ x : H₁, ∀ y : H₂,
        (∀ d : D, inner ℂ (i d) x + inner ℂ (A d) y = 0) → x = 0 ∧ y = 0 := by
  constructor
  · intro hclosure x y hrel
    let z : WithLp 2 (H₁ × H₂) := WithLp.toLp 2 (x, y)
    have hz : z ∈ (linearGraphSubmodule i A)ᗮ :=
      (mem_linearGraphSubmodule_orthogonal_iff i A z).mpr hrel
    have horth : (linearGraphSubmodule i A)ᗮ = ⊥ := by
      rw [← Submodule.orthogonal_closure, hclosure, Submodule.top_orthogonal_eq_bot]
    rw [horth] at hz
    have hz0 : z = 0 := hz
    have hprod : (x, y) = 0 := WithLp.toLp_injective 2 hz0
    exact ⟨congrArg Prod.fst hprod, congrArg Prod.snd hprod⟩
  · intro hann
    exact linearGraphSubmodule_closure_eq_top_of_annihilator i A hann

end

end GaloisForLFunctions.HTGeometry
