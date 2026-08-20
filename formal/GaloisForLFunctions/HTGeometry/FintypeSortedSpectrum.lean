/-
# The sorted spectrum over an arbitrary finite index

Sorting needs a linearly ordered index, so the canonical spectral labelling is stated for `Fin D`.
Reindexing a Hermitian matrix along any bijection to `Fin D` changes neither its power traces nor,
therefore, its sorted spectrum, so every consequence of the canonical labelling -- simplicity, and
the closedness of the degenerate locus -- transfers to an arbitrary finite index.

Main results:
* `trace_reindex_eq`, `trace_pow_reindex` — reindexing preserves every power trace.
* `sum_pow_eigenvalues_eq_trace_pow_re'` — the power sums of the spectrum, any finite index.
* `sortedTuple_eigenvalues_reindex` — **the sorted spectrum is the reindexed one**.
* `injective_eigenvalues_reindex_iff` — simplicity is preserved by reindexing.
* `isClosed_repeatedSpectrum` — **the degenerate locus of a continuous Hermitian family is
  closed**, over an arbitrary finite index.
-/
import GaloisForLFunctions.HTGeometry.SimpleSpectrumOpen

open Matrix Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem trace_reindex_eq {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (A : Matrix ι ι ℂ) : (Matrix.reindex e e A).trace = A.trace := by
  rw [Matrix.trace, Matrix.trace]
  change (∑ i : κ, A (e.symm i) (e.symm i)) = ∑ i : ι, A i i
  exact Equiv.sum_comp e.symm (fun i : ι => A i i)

theorem trace_pow_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (A : Matrix ι ι ℂ) (p : ℕ) :
    ((Matrix.reindex e e A) ^ p).trace = (A ^ p).trace := by
  have hpow : Matrix.reindex e e (A ^ p) = (Matrix.reindex e e A) ^ p := by
    have h := map_pow (Matrix.reindexAlgEquiv ℂ ℂ e) A p
    simpa only [Matrix.coe_reindexAlgEquiv] using h
  rw [← hpow, trace_reindex_eq]

theorem sum_pow_eigenvalues_eq_trace_pow_re' {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (p : ℕ) :
    ∑ i, (hA.eigenvalues i) ^ p = ((A ^ p).trace).re := by
  rw [trace_pow_eq_sum_eigenvalues_pow hA p, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- **The sorted spectrum of a reindexed Hermitian matrix is the sorted reindexed spectrum.** -/
theorem sortedTuple_eigenvalues_reindex (e : ι ≃ Fin (Fintype.card ι)) {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) :
    sortedTuple ((hA.reindex e).eigenvalues) = sortedTuple (hA.eigenvalues ∘ e.symm) := by
  refine eq_of_monotone_of_sum_pow_eq (monotone_sortedTuple _) (monotone_sortedTuple _) ?_
  intro p
  rw [sum_pow_sortedTuple, sum_pow_sortedTuple,
    sum_pow_eigenvalues_eq_trace_pow_re' (hA.reindex e) p, trace_pow_reindex,
    ← sum_pow_eigenvalues_eq_trace_pow_re' hA p]
  exact (Equiv.sum_comp e.symm fun j : ι => (hA.eigenvalues j) ^ p).symm

/-- **Simplicity of the spectrum is preserved by reindexing.** -/
theorem injective_eigenvalues_reindex_iff (e : ι ≃ Fin (Fintype.card ι)) {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) :
    Function.Injective ((hA.reindex e).eigenvalues) ↔ Function.Injective hA.eigenvalues := by
  rw [injective_iff_injective_sortedTuple, sortedTuple_eigenvalues_reindex e hA,
    ← injective_iff_injective_sortedTuple]
  constructor
  · intro h
    have := h.comp e.injective
    simpa [Function.comp_def] using this
  · intro h
    exact h.comp e.symm.injective

/-- **The degenerate locus of a continuous Hermitian family is closed.** -/
theorem isClosed_repeatedSpectrum {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {F : X → Matrix ι ι ℂ} (hF : Continuous F) (hHerm : ∀ x, (F x).IsHermitian) :
    IsClosed {x : X | ¬ Function.Injective (hHerm x).eigenvalues} := by
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set G : X → Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ :=
    fun x => Matrix.reindex e e (F x) with hG
  have hGcont : Continuous G := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (e.symm j)).comp ((continuous_apply (e.symm i)).comp hF)
  have hGherm : ∀ x, (G x).IsHermitian := fun x => (hHerm x).reindex e
  have hs : Continuous (fun x => sortedTuple ((hGherm x).eigenvalues)) :=
    continuous_sortedTuple_eigenvalues hGcont hGherm
  have hset : {x : X | ¬ Function.Injective (hHerm x).eigenvalues}
      = ⋃ i : Fin (Fintype.card ι), ⋃ j : Fin (Fintype.card ι),
          {x : X | i ≠ j ∧ sortedTuple ((hGherm x).eigenvalues) i
            = sortedTuple ((hGherm x).eigenvalues) j} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hx
      have hx' : ¬ Function.Injective (sortedTuple ((hGherm x).eigenvalues)) := by
        rw [← injective_iff_injective_sortedTuple, injective_eigenvalues_reindex_iff e (hHerm x)]
        exact hx
      obtain ⟨i, j, heq, hne⟩ : ∃ i j, sortedTuple ((hGherm x).eigenvalues) i
          = sortedTuple ((hGherm x).eigenvalues) j ∧ i ≠ j := by
        by_contra hcon
        refine hx' fun a b hab => ?_
        by_contra hne
        exact hcon ⟨a, b, hab, hne⟩
      exact ⟨i, j, hne, heq⟩
    · rintro ⟨i, j, hne, heq⟩
      intro hinj
      have hinj' : Function.Injective (sortedTuple ((hGherm x).eigenvalues)) := by
        rw [← injective_iff_injective_sortedTuple, injective_eigenvalues_reindex_iff e (hHerm x)]
        exact hinj
      exact hne (hinj' heq)
  rw [hset]
  refine isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j => ?_
  by_cases hij : i ≠ j
  · have hrw : {x : X | i ≠ j ∧ sortedTuple ((hGherm x).eigenvalues) i
        = sortedTuple ((hGherm x).eigenvalues) j}
      = {x : X | sortedTuple ((hGherm x).eigenvalues) i
        = sortedTuple ((hGherm x).eigenvalues) j} := by
      ext x
      simp [hij]
    rw [hrw]
    exact isClosed_eq ((continuous_apply i).comp hs) ((continuous_apply j).comp hs)
  · have hrw : {x : X | i ≠ j ∧ sortedTuple ((hGherm x).eigenvalues) i
        = sortedTuple ((hGherm x).eigenvalues) j} = (∅ : Set X) := by
      ext x
      simp [hij]
    rw [hrw]
    exact isClosed_empty

end

end GaloisForLFunctions.HTGeometry
