import GaloisForLFunctions.HTGeometry.UniformDominantFintype

/-!
# The residue of a Gamma-field presentation in its own index shape

The clearing of a Gamma-field element produces the data in a nested shape: finitely many `Γ`-powers,
each with its own coefficient — a jet polynomial with its own number of monomials and its own jet
range.  Indexing the terms by the corresponding sigma type, and padding the jet ranges to a common
length, the tube residue theorem applies directly.

This is eq. (3) in tube form, stated on the data the clearing theorem produces.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The residue of a nested Gamma-field presentation, uniformly on a tube.** -/
theorem exists_tubeLimit_gammaPresentation_residue {M : ℝ} (hM : 0 < M) {N : ℕ}
    (Mm : Fin N → ℕ) (Kf : Fin N → ℕ) (K d : ℕ) (hK : ∀ j, Kf j ≤ K) (u : Fin N → ℕ)
    (a : ∀ j : Fin N, Fin (Mm j) → Polynomial ℂ)
    (E : ∀ j : Fin N, Fin (Mm j) → Fin (Kf j + 1) → ℕ)
    (hdeg : ∀ j α, (a j α).natDegree ≤ d) (ha : ∀ j α, a j α ≠ 0)
    (hne : Nonempty (Σ j : Fin N, Fin (Mm j))) :
    ∃ (p : (Σ j : Fin N, Fin (Mm j)) → ℕ) (c : (Σ j : Fin N, Fin (Mm j)) → ℂ)
      (β : Σ j : Fin N, Fin (Mm j)), (∀ x, c x ≠ 0) ∧
      TubeLimit M (fun σ t => (∑ j : Fin N, gammaLine σ t ^ u j
          * (∑ α : Fin (Mm j), ((a j α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
              / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
            * ∏ i : Fin (Kf j + 1), iteratedDeriv (i : ℕ) Complex.digamma
                ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E j α i))
        / gammaShapeZ σ (u β.1 : ℤ) (-(p β : ℤ)) ((E β.1 β.2 0 : ℤ)) t)
        (∑ x ∈ Finset.univ.filter (fun x : Σ j : Fin N, Fin (Mm j) =>
            (u x.1 : ℤ) = (u β.1 : ℤ) ∧ (-(p x : ℤ)) = (-(p β : ℤ))
              ∧ ((E x.1 x.2 0 : ℤ)) = ((E β.1 β.2 0 : ℤ))), c x) := by
  classical
  haveI := hne
  -- the datum of each monomial, padded to the common jet range
  choose p c hc hlim using fun x : Σ j : Fin N, Fin (Mm j) =>
    exists_tubeLimit_jetMonomial_datum hM K d (a x.1 x.2)
      (fun i : Fin (K + 1) => padExp (Kf x.1) (E x.1 x.2) (i : ℕ))
      (hdeg x.1 x.2) (ha x.1 x.2)
  have hpad : ∀ x : Σ j : Fin N, Fin (Mm j),
      padExp (Kf x.1) (E x.1 x.2) ((0 : Fin (K + 1)) : ℕ) = E x.1 x.2 0 := by
    intro x
    have h0 : ((0 : Fin (K + 1)) : ℕ) = 0 := rfl
    rw [h0, padExp_zero]
  -- each term, with its Gamma power
  have hterm : ∀ x : Σ j : Fin N, Fin (Mm j), TubeLimit M
      (fun σ t => (gammaLine σ t ^ u x.1
          * (((a x.1 x.2).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
              / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
            * ∏ i : Fin (Kf x.1 + 1), iteratedDeriv (i : ℕ) Complex.digamma
                ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E x.1 x.2 i))
        / gammaShapeZ σ (u x.1 : ℤ) (-(p x : ℤ)) ((E x.1 x.2 0 : ℤ)) t) (c x) := by
    intro x
    have hx := (hlim x).mul_gammaPow (u x.1)
    rw [hpad x] at hx
    refine hx.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
    rw [prod_jets_pad (hK x.1) (E x.1 x.2)]
  obtain ⟨β, hβ⟩ := exists_tubeLimit_dominant_class_fintype hM
    (fun x σ t => gammaLine σ t ^ u x.1
      * (((a x.1 x.2).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
        * ∏ i : Fin (Kf x.1 + 1), iteratedDeriv (i : ℕ) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E x.1 x.2 i))
    (fun x => (u x.1 : ℤ)) (fun x => -(p x : ℤ)) (fun x => (E x.1 x.2 0 : ℤ)) c hterm
  refine ⟨p, c, β, hc, ?_⟩
  refine hβ.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  refine congrArg (fun w => w / gammaShapeZ σ (u β.1 : ℤ) (-(p β : ℤ)) ((E β.1 β.2 0 : ℤ)) t) ?_
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]

end

end GaloisForLFunctions.HTGeometry
