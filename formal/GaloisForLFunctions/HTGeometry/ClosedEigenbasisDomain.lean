import GaloisForLFunctions.HTGeometry.MaximalRealDiagonalSelfAdjoint

/-!
# Closed operators with a complete real eigenbasis

Finite eigenvector sums approximate both coordinates of the graph. Closedness
therefore identifies the entire operator domain from its spectral weights.
-/

noncomputable section

open scoped InnerProductSpace LinearPMap
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A closed graph contains every convergent eigenvector expansion with a
convergent weighted expansion. -/
theorem mem_graph_of_complete_eigenbasis
    (A : E →ₗ.[ℂ] E) (b : HilbertBasis ι ℂ E) (energy : ι → ℝ)
    (hclosed : A.IsClosed) (hb : ∀ i, b i ∈ A.domain)
    (heigen : ∀ i, A ⟨b i, hb i⟩ = (energy i : ℂ) • b i)
    {x y : E} (hcoord : ∀ i, b.repr y i = (energy i : ℂ) * b.repr x i) :
    (x, y) ∈ A.graph := by
  have hsum := (b.hasSum_repr x).prodMk (b.hasSum_repr y)
  apply hclosed.mem_of_tendsto hsum
  exact Eventually.of_forall fun s => A.graph.sum_mem fun i _ => by
    have hi := A.graph.smul_mem (b.repr x i) (A.mem_graph ⟨b i, hb i⟩)
    rw [heigen i] at hi
    simpa only [Prod.smul_mk, hcoord i, smul_smul, mul_comm] using hi

/-- Symmetry recovers the weighted coordinates of every graph element. -/
theorem eigenbasis_graph_coordinates
    (A : E →ₗ.[ℂ] E) (b : HilbertBasis ι ℂ E) (energy : ι → ℝ)
    (hsymm : A.IsFormalAdjoint A) (hb : ∀ i, b i ∈ A.domain)
    (heigen : ∀ i, A ⟨b i, hb i⟩ = (energy i : ℂ) • b i)
    (x : A.domain) (i : ι) :
    b.repr (A x) i = (energy i : ℂ) * b.repr (x : E) i := by
  rw [b.repr_apply_apply, b.repr_apply_apply]
  have h := hsymm ⟨b i, hb i⟩ x
  change inner ℂ (A ⟨b i, hb i⟩) (x : E) = inner ℂ (b i) (A x) at h
  rw [heigen i, inner_smul_left, Complex.conj_ofReal] at h
  exact h.symm

/-- The full maximal domain is exactly square-summability of the eigenvalue
weighted basis coefficients. -/
theorem closed_eigenbasis_domain_iff
    (A : E →ₗ.[ℂ] E) (b : HilbertBasis ι ℂ E) (energy : ι → ℝ)
    (hclosed : A.IsClosed) (hsymm : A.IsFormalAdjoint A)
    (hb : ∀ i, b i ∈ A.domain)
    (heigen : ∀ i, A ⟨b i, hb i⟩ = (energy i : ℂ) • b i) (x : E) :
    x ∈ A.domain ↔ Memℓp (fun i => (energy i : ℂ) * b.repr x i) 2 := by
  constructor
  · intro hx
    have hc := eigenbasis_graph_coordinates A b energy hsymm hb heigen ⟨x, hx⟩
    have hfun : (fun i => (energy i : ℂ) * b.repr x i) =
        fun i => b.repr (A ⟨x, hx⟩) i := by
      funext i
      exact (hc i).symm
    rw [hfun]
    exact lp.memℓp _
  · intro hx
    let z : lp (fun _ : ι => ℂ) 2 := ⟨_, hx⟩
    have hg := mem_graph_of_complete_eigenbasis A b energy hclosed hb heigen
      (x := x) (y := b.repr.symm z) (fun i => by
        rw [b.repr.apply_symm_apply])
    obtain ⟨u, hu, _⟩ := (A.mem_graph_iff).mp hg
    change (u : E) = x at hu
    rw [← hu]
    exact u.property

/-- A domain containing a complete Hilbert basis is dense. -/
theorem dense_domain_of_complete_basis
    (A : E →ₗ.[ℂ] E) (b : HilbertBasis ι ℂ E)
    (hb : ∀ i, b i ∈ A.domain) : Dense (A.domain : Set E) := by
  have hd : Dense (Submodule.span ℂ (Set.range b) : Set E) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  apply hd.mono
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact hb i

/-- A closed symmetric operator with a complete real eigenbasis is
self-adjoint on its actual domain. -/
theorem closed_eigenbasis_isSelfAdjoint
    [CompleteSpace E]
    (A : E →ₗ.[ℂ] E) (b : HilbertBasis ι ℂ E) (energy : ι → ℝ)
    (hclosed : A.IsClosed) (hsymm : A.IsFormalAdjoint A)
    (hb : ∀ i, b i ∈ A.domain)
    (heigen : ∀ i, A ⟨b i, hb i⟩ = (energy i : ℂ) • b i) :
    IsSelfAdjoint A := by
  have hd := dense_domain_of_complete_basis A b hb
  have hc (y : A†.domain) (i : ι) :
      b.repr (A† y) i = (energy i : ℂ) * b.repr (y : E) i := by
    rw [b.repr_apply_apply, b.repr_apply_apply]
    have h := (LinearPMap.adjoint_isFormalAdjoint hd).symm ⟨b i, hb i⟩ y
    change inner ℂ (A ⟨b i, hb i⟩) (y : E) = inner ℂ (b i) (A† y) at h
    rw [heigen i, inner_smul_left, Complex.conj_ofReal] at h
    exact h.symm
  have hg (y : A†.domain) : ((y : E), A† y) ∈ A.graph :=
    mem_graph_of_complete_eigenbasis A b energy hclosed hb heigen (hc y)
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨u, hu, _⟩ := A.mem_graph_iff.mp (hg ⟨x, hx⟩)
      change (u : E) = x at hu
      rw [← hu]
      exact u.property
    · intro x y hxy
      obtain ⟨u, hu, hau⟩ := A.mem_graph_iff.mp (hg x)
      have huy : u = y := Subtype.ext (hu.trans hxy)
      exact hau.symm.trans (congrArg A huy)
  · exact hsymm.le_adjoint hd

end GaloisForLFunctions.HTGeometry
