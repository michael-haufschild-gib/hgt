import GaloisForLFunctions.HTGeometry.UniformDistinctKeyResidue

/-!
# A `ψ`-degree group over an arbitrary finite index

The groups of a jet polynomial are subsets of its monomial index, not intervals, so the group datum
has to accept an arbitrary finite index.  Transporting along the canonical equivalence with an
interval does that: sums and exponent families move across the equivalence, and injectivity is
preserved.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The datum of a `ψ`-degree group over an arbitrary finite index.** -/
theorem exists_tubeLimit_jetPolyGroup_datum_fintype {M : ℝ} (hM : 0 < M) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (K d : ℕ) (e : ℕ) (a : ι → Polynomial ℂ) (E : ι → Fin (K + 1) → ℕ)
    (hdeg : ∀ x, (a x).natDegree ≤ d) (hEinj : Function.Injective E)
    (he : ∀ x, E x 0 = e) {x₀ : ι} (hx₀ : a x₀ ≠ 0) :
    ∃ (p : ℕ) (c : ℂ), c ≠ 0 ∧ TubeLimit M (fun σ t =>
      (∑ x : ι, ((a x).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
        * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E x i)
      / gammaShapeZ σ 0 (-(p : ℤ)) (e : ℤ) t) c := by
  classical
  set φ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with hφ
  set a' : Fin (Fintype.card ι) → Polynomial ℂ := fun n => a (φ.symm n) with ha'
  set E' : Fin (Fintype.card ι) → Fin (K + 1) → ℕ := fun n => E (φ.symm n) with hE'
  have hdeg' : ∀ n, (a' n).natDegree ≤ d := fun n => hdeg _
  have hEinj' : Function.Injective E' := by
    intro m n hmn
    exact φ.symm.injective (hEinj hmn)
  have he' : ∀ n, E' n 0 = e := fun n => he _
  have hx₀' : a' (φ x₀) ≠ 0 := by
    rw [ha']
    simpa using hx₀
  obtain ⟨p, c, hc, hlim⟩ :=
    exists_tubeLimit_jetPolyGroup_datum hM K d (Fintype.card ι) e a' E' hdeg' hEinj' he' hx₀'
  refine ⟨p, c, hc, ?_⟩
  refine hlim.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  refine congrArg (fun w => w / gammaShapeZ σ 0 (-(p : ℤ)) (e : ℤ) t) ?_
  refine Fintype.sum_equiv φ.symm _ _ fun n => ?_
  rw [ha', hE']

end

end GaloisForLFunctions.HTGeometry
