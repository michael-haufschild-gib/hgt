import GaloisForLFunctions.HTGeometry.SubmoduleSpectrumRelationEscape
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

/-!
# Real diagonal matrices escape every constant real relation

Where the whole Hermitian matrix space is available — a two-site architecture, whose local
Hamiltonian class is unrestricted — the escape witness needs no interaction geometry: a real
diagonal matrix whose entries avoid one nonzero polynomial suffices.  The polynomial is the affine
labelling orbit of the relation times the pairwise-difference product enforcing simplicity.

## Main results

* `exists_injective_escaping_energy` — the escaping real spectrum.
* `diagonalSet_spectrumEscapesAffineRelations` — hence the real diagonal matrices escape.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **An escaping simple real spectrum exists for every nonzero relation and every value.** -/
theorem exists_injective_escaping_energy {I : Type*} [Fintype I] [DecidableEq I]
    {c : I → ℝ} (hc : c ≠ 0) (target : ℝ) :
    ∃ E : I → ℝ, Function.Injective E ∧ ∀ σ : Equiv.Perm I, ∑ i, c i * E (σ i) ≠ target := by
  classical
  set separation : MvPolynomial I ℝ :=
    ∏ p : {p : I × I // p.1 ≠ p.2}, (MvPolynomial.X p.1.1 - MvPolynomial.X p.1.2)
    with hseparation
  have hsepne : separation ≠ 0 := by
    rw [hseparation]
    refine Finset.prod_ne_zero_iff.mpr fun p _ => ?_
    intro h0
    have hev :=
      congrArg (MvPolynomial.eval (fun i => if i = p.1.1 then (1 : ℝ) else 0)) h0
    simp [Ne.symm p.2] at hev
  have hQ : affineRelationOrbit c target * separation ≠ 0 :=
    mul_ne_zero (affineRelationOrbit_ne_zero hc target) hsepne
  have hexists : ∃ E : I → ℝ,
      MvPolynomial.eval E (affineRelationOrbit c target * separation) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hQ (MvPolynomial.funext fun E => by rw [hcon E, map_zero])
  obtain ⟨E, hE⟩ := hexists
  rw [map_mul] at hE
  refine ⟨E, ?_, ?_⟩
  · intro a b hab
    by_contra hne
    refine (mul_ne_zero_iff.mp hE).2 ?_
    rw [hseparation, map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨(a, b), hne⟩) ?_
    simp [hab]
  · refine (affineRelationOrbitValue_ne_zero_iff c target E).mp ?_
    rw [← eval_affineRelationOrbit]
    exact (mul_ne_zero_iff.mp hE).1

/-- **The real diagonal matrices escape every constant real relation.** -/
theorem diagonalSet_spectrumEscapesAffineRelations {I : Type*} [Fintype I] [DecidableEq I] :
    SpectrumEscapesAffineRelations
      {M : Matrix I I ℂ | ∃ E : I → ℝ, M = Matrix.diagonal (fun i => (E i : ℂ))} := by
  intro c hbalanced hc target
  obtain ⟨E, hEinj, hEesc⟩ := exists_injective_escaping_energy hc target
  exact ⟨Matrix.diagonal (fun i => (E i : ℂ)), ⟨E, rfl⟩, E, hEinj,
    fun i => matrixCharpolyRelation_diagonal_root (fun i => (E i : ℂ)) i, hEesc⟩

end

end GaloisForLFunctions.HTGeometry
