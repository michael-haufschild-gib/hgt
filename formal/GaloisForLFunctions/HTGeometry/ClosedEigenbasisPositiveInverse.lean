import GaloisForLFunctions.HTGeometry.ClosedEigenbasisDomain
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator

/-!
# Positive inverses in a complete eigenbasis

Reciprocal spectral multiplication gives an actual inverse on the closed
operator domain. Proper positive energies make this bounded inverse compact.
-/

noncomputable section

open Filter Topology
open scoped InnerProductSpace LinearPMap

namespace GaloisForLFunctions.HTGeometry

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_inv_real_le_one_of_one_le {r : ℝ} (hr : 1 ≤ r) :
    ‖(r : ℂ)⁻¹‖ ≤ 1 := by
  have hpos : 0 < r := zero_lt_one.trans_le hr
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hr

/-- Reciprocal multiplication in the complete basis, for energies at least one. -/
def positiveBasisInverse (b : HilbertBasis ι ℂ E) (r : ι → ℝ)
    (hr : ∀ i, 1 ≤ r i) : E →L[ℂ] E :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    lpDiagonalCLM (fun i => (r i : ℂ)⁻¹) zero_le_one
      (fun i => norm_inv_real_le_one_of_one_le (hr i)) ∘L
        b.repr.toContinuousLinearEquiv.toContinuousLinearMap

theorem positiveBasisInverse_repr (b : HilbertBasis ι ℂ E) (r : ι → ℝ)
    (hr : ∀ i, 1 ≤ r i) (x : E) (i : ι) :
    b.repr (positiveBasisInverse b r hr x) i = (r i : ℂ)⁻¹ * b.repr x i := by
  change b.repr (b.repr.symm (lpDiagonalCLM (fun j => (r j : ℂ)⁻¹)
    zero_le_one (fun j => norm_inv_real_le_one_of_one_le (hr j)) (b.repr x))) i = _
  rw [b.repr.apply_symm_apply, lpDiagonalCLM_apply]

theorem positiveBasisInverse_basis (b : HilbertBasis ι ℂ E) (r : ι → ℝ)
    (hr : ∀ i, 1 ≤ r i) (i : ι) :
    positiveBasisInverse b r hr (b i) = (r i : ℂ)⁻¹ • b i := by
  classical
  change b.repr.symm (lpDiagonalCLM (fun j => (r j : ℂ)⁻¹)
    zero_le_one (fun j => norm_inv_real_le_one_of_one_le (hr j)) (b.repr (b i))) = _
  rw [b.repr_self, lpDiagonalCLM_single]
  have hsingle : (lp.single 2 i (r i : ℂ)⁻¹ : lp (fun _ : ι => ℂ) 2) =
      (r i : ℂ)⁻¹ • lp.single 2 i (1 : ℂ) := by
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  rw [hsingle, map_smul, b.repr_symm_single]

/-- The inverse image belongs to the actual closed graph, with its prescribed image. -/
theorem positiveBasisInverse_mem_graph (A : E →ₗ.[ℂ] E)
    (b : HilbertBasis ι ℂ E) (r : ι → ℝ) (hr : ∀ i, 1 ≤ r i)
    (hclosed : A.IsClosed) (hb : ∀ i, b i ∈ A.domain)
    (heigen : ∀ i, A ⟨b i, hb i⟩ = (r i : ℂ) • b i) (x : E) :
    (positiveBasisInverse b r hr x, x) ∈ A.graph := by
  apply mem_graph_of_complete_eigenbasis A b r hclosed hb heigen
  intro i
  rw [positiveBasisInverse_repr, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le (hr i)).ne'), one_mul]

theorem positiveBasisInverse_mem_domain (A : E →ₗ.[ℂ] E)
    (b : HilbertBasis ι ℂ E) (r : ι → ℝ) (hr : ∀ i, 1 ≤ r i)
    (hclosed : A.IsClosed) (hb : ∀ i, b i ∈ A.domain)
    (heigen : ∀ i, A ⟨b i, hb i⟩ = (r i : ℂ) • b i) (x : E) :
    positiveBasisInverse b r hr x ∈ A.domain := by
  obtain ⟨u, hu, _⟩ := A.mem_graph_iff.mp
    (positiveBasisInverse_mem_graph A b r hr hclosed hb heigen x)
  change (u : E) = positiveBasisInverse b r hr x at hu
  rw [← hu]
  exact u.property

theorem apply_positiveBasisInverse (A : E →ₗ.[ℂ] E)
    (b : HilbertBasis ι ℂ E) (r : ι → ℝ) (hr : ∀ i, 1 ≤ r i)
    (hclosed : A.IsClosed) (hb : ∀ i, b i ∈ A.domain)
    (heigen : ∀ i, A ⟨b i, hb i⟩ = (r i : ℂ) • b i) (x : E) :
    A ⟨positiveBasisInverse b r hr x,
      positiveBasisInverse_mem_domain A b r hr hclosed hb heigen x⟩ = x := by
  obtain ⟨u, hu, hau⟩ := A.mem_graph_iff.mp
    (positiveBasisInverse_mem_graph A b r hr hclosed hb heigen x)
  have heq : u = ⟨positiveBasisInverse b r hr x,
      positiveBasisInverse_mem_domain A b r hr hclosed hb heigen x⟩ := Subtype.ext hu
  rw [← heq]
  exact hau

theorem positiveBasisInverse_apply (A : E →ₗ.[ℂ] E)
    (b : HilbertBasis ι ℂ E) (r : ι → ℝ) (hr : ∀ i, 1 ≤ r i)
    (hsymm : A.IsFormalAdjoint A) (hb : ∀ i, b i ∈ A.domain)
    (heigen : ∀ i, A ⟨b i, hb i⟩ = (r i : ℂ) • b i) (x : A.domain) :
    positiveBasisInverse b r hr (A x) = (x : E) := by
  apply b.repr.injective
  apply lp.ext
  funext i
  rw [positiveBasisInverse_repr, eigenbasis_graph_coordinates A b r hsymm hb heigen,
    ← mul_assoc, inv_mul_cancel₀
      (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le (hr i)).ne'), one_mul]

/-- Proper positive energies give a compact actual inverse. -/
theorem positiveBasisInverse_isCompact [CompleteSpace E]
    (b : HilbertBasis ι ℂ E) (r : ι → ℝ)
    (hr : ∀ i, 1 ≤ r i) (hproper : Tendsto r cofinite atTop) :
    IsCompactOperator (positiveBasisInverse b r hr) := by
  apply isCompactOperator_of_diag_tendsto_cofinite b (positiveBasisInverse_basis b r hr)
  refine (tendsto_inv_atTop_zero.comp hproper).congr fun i => ?_
  change (r i)⁻¹ = ‖(r i : ℂ)⁻¹‖
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (zero_lt_one.trans_le (hr i))]

end GaloisForLFunctions.HTGeometry
