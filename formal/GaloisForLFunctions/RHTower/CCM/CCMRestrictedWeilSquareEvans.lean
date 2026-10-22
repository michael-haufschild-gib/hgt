import GaloisForLFunctions.RHTower.CCM.CCMRationalResidualEvansMatrix
import GaloisForLFunctions.RHTower.CCM.CCMSpectralParameterEvans

/-!
# The restricted Weil eigenproblem: a square Evans determinant

Four exact mechanisms of the card are formalized.

*Equal dimensions.*  The characteristic source `F_{a,λ}` and the Bessel residual target
`R_{a,λ}` both have dimension `d_{a,λ} = 2L_{a,λ}`, so the Evans map `(7)` is **square** — this is
`(3)`–`(4)`.

*Kernel transfer.*  Under the isomorphism `(8)` the eigenspace is trivial exactly when the Evans
kernel is trivial.

*The determinant criterion.*  A square matrix has vanishing determinant exactly when its kernel is
nontrivial, so `(9)`: `λ ∈ spec(A_a) ⟺ det N_{a,λ} = 0`.

*The parity grading.*  The reflection splitting `(22)` adds the two equal halves to the full
dimension, so no excess parity channel occurs.

The restricted Weil form, the Paley–Wiener compression `(12)`, the logarithmic Dirichlet
reconstruction `(5)` and the residual computation `(6)` are cited parents and stay outside the Lean
statement.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-! ## Equal dimensions -/

/-- **Equations (3)–(4).**  Source and target of the Evans map have the same dimension, so the map
is square. -/
theorem finrank_source_eq_target {p : Polynomial ℂ} {L : ℕ} (hp : p ≠ 0)
    (hdeg : p.natDegree = 2 * L) :
    Module.finrank ℂ (solutionSpace p) = Module.finrank ℂ (residualSpace L) := by
  rw [finrank_solutionSpace hp, finrank_residualSpace, hdeg]

/-! ## Kernel transfer and the determinant criterion -/

/-- A square matrix has vanishing determinant exactly when its kernel is nontrivial. -/
theorem det_eq_zero_iff_ker_ne_bot {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) :
    N.det = 0 ↔ LinearMap.ker (Matrix.mulVecLin N) ≠ ⊥ := by
  constructor
  · intro hdet
    obtain ⟨v, hv, hNv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    intro hbot
    have hmem : v ∈ LinearMap.ker (Matrix.mulVecLin N) := by
      simpa [LinearMap.mem_ker] using hNv
    rw [hbot, Submodule.mem_bot] at hmem
    exact hv hmem
  · intro hne
    obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hvne, ?_⟩
    simpa [LinearMap.mem_ker] using hv

/-- **Equations (8)–(9).**  Under the kernel isomorphism, the eigenspace is trivial exactly when the
square Evans determinant is nonzero. -/
theorem eigenspace_eq_bot_iff_det_ne_zero {n : ℕ} {N : Matrix (Fin n) (Fin n) ℂ}
    {V : Type*} [AddCommGroup V] [Module ℂ V] {K : Submodule ℂ V}
    (e : K ≃ₗ[ℂ] LinearMap.ker (Matrix.mulVecLin N)) :
    K = ⊥ ↔ N.det ≠ 0 := by
  have key : K ≠ ⊥ ↔ LinearMap.ker (Matrix.mulVecLin N) ≠ ⊥ := by
    constructor
    · intro hK hkbot
      obtain ⟨u, hu, hune⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
      have h1 : ((e ⟨u, hu⟩ : LinearMap.ker (Matrix.mulVecLin N)) : Fin n → ℂ) = 0 := by
        have hmem := (e ⟨u, hu⟩).2
        exact (Submodule.eq_bot_iff _).mp hkbot _ hmem
      have h2 : e ⟨u, hu⟩ = 0 := Subtype.ext h1
      have h3 : (⟨u, hu⟩ : K) = 0 := by
        have h4 := congrArg e.symm h2
        rwa [LinearEquiv.symm_apply_apply, map_zero] at h4
      exact hune (congrArg Subtype.val h3)
    · intro hk hKbot
      obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
      have h1 : ((e.symm ⟨v, hv⟩ : K) : V) = 0 := by
        have hmem := (e.symm ⟨v, hv⟩).2
        exact (Submodule.eq_bot_iff _).mp hKbot _ hmem
      have h2 : e.symm ⟨v, hv⟩ = 0 := Subtype.ext h1
      have h3 : (⟨v, hv⟩ : LinearMap.ker (Matrix.mulVecLin N)) = 0 := by
        have h4 := congrArg e h2
        rwa [LinearEquiv.apply_symm_apply, map_zero] at h4
      exact hvne (congrArg Subtype.val h3)
  constructor
  · intro hK hdet
    exact (key.mpr ((det_eq_zero_iff_ker_ne_bot N).mp hdet)) hK
  · intro hdet
    by_contra hK
    exact hdet ((det_eq_zero_iff_ker_ne_bot N).mpr (key.mp hK))

/-! ## The parity grading -/

/-- **Equation (22).**  The reflection splitting has two equal halves adding to the full
dimension. -/
theorem parity_split_dim (L : ℕ) : L + L = 2 * L := by ring

end GaloisForLFunctions.RHTower

end
