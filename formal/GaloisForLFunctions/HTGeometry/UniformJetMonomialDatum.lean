import GaloisForLFunctions.HTGeometry.UniformDominantRatio

/-!
# A full jet monomial against its shape, uniformly on a vertical tube

A monomial of a Gamma-field presentation involves *all* jets, `ψ` included, while the uniform datum
machinery is stated for the positive-order jets.  Splitting the `ψ`-slot off the product turns one
into the other: the positive part has a uniform datum against a power of the argument, and the `ψ`
factor contributes its power of the vertical logarithm.

So a single monomial with a nonzero polynomial coefficient has a residue against
`s^{-p}·(log s)^{E 0}`, uniformly on every tube.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Splitting the `ψ`-slot off a jet monomial. -/
theorem prod_jets_split (K : ℕ) (E : Fin (K + 1) → ℕ) (z : ℂ) :
    ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ E i
      = Complex.digamma z ^ E 0
        * ∏ i : Fin K, iteratedDeriv ((i : ℕ) + 1) Complex.digamma z ^ E i.succ := by
  rw [Fin.prod_univ_succ]
  simp [Fin.val_succ]

/-- **The uniform datum of a single jet monomial with a nonzero polynomial coefficient.** -/
theorem exists_tubeLimit_jetMonomial_datum {M : ℝ} (hM : 0 < M) (K d : ℕ) (a : Polynomial ℂ)
    (E : Fin (K + 1) → ℕ) (hdeg : a.natDegree ≤ d) (ha : a ≠ 0) :
    ∃ (p : ℕ) (c : ℂ), c ≠ 0 ∧ TubeLimit M (fun σ t =>
      ((a.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
        * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E i)
      / gammaShapeZ σ 0 (-(p : ℤ)) (E 0 : ℤ) t) c := by
  classical
  -- the positive-order part, as a one-term jet polynomial
  set W : ℕ := ∑ i : Fin K, ((i : ℕ) + 1) * E i.succ with hW
  have hdeg' : ∀ α : Fin 1, ((fun _ : Fin 1 => a) α).natDegree ≤ d := fun _ => hdeg
  have hWle : ∀ α : Fin 1, W ≤ ∑ i : Fin K, ((i : ℕ) + 1) * (fun _ : Fin 1 => fun i : Fin K =>
      E i.succ) α i := fun _ => le_refl _
  have hinj : Function.Injective (fun _ : Fin 1 => fun i : Fin K => E i.succ) := by
    intro x y _
    exact Subsingleton.elim x y
  have hne : jetPolyMvCoeff K 1 d (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => fun i : Fin K => E i.succ) ≠ 0 :=
    jetPolyMvCoeff_ne_zero (fun _ => a) _ hinj (β := (0 : Fin 1)) ha
  obtain ⟨p, c, hc, hlim⟩ := exists_uniform_jetPolyCoeff_datum_of_ne_zero hM K 1 W d
    (fun _ : Fin 1 => fun i : Fin K => E i.succ) (fun _ : Fin 1 => a) hdeg' hWle hne
  -- multiply by the `ψ`-power
  have hterm := tubeLimit_gammaJet_term hM hlim 0 (E 0)
  refine ⟨p, c, hc, ?_⟩
  refine hterm.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  rw [prod_jets_split K E]
  simp only [Finset.univ_unique, Finset.sum_singleton, pow_zero, one_mul, Nat.cast_zero]
  ring

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The residue of a full jet polynomial, uniformly on a vertical tube.**  Every monomial — all
jets, `ψ` included, with a nonzero polynomial coefficient — has its own datum, and the sum has the
residue of the dominant class.  This is eq. (19) in tube form for an element of `ℂ(s)⟨ψ⟩` written in
normal form. -/
theorem exists_tubeLimit_jetPoly_full_residue {M : ℝ} (hM : 0 < M) {Mm : ℕ} (hMm : 0 < Mm)
    (K d : ℕ) (a : Fin Mm → Polynomial ℂ) (E : Fin Mm → Fin (K + 1) → ℕ)
    (hdeg : ∀ α, (a α).natDegree ≤ d) (ha : ∀ α, a α ≠ 0) :
    ∃ (p : Fin Mm → ℕ) (c : Fin Mm → ℂ) (β : Fin Mm), (∀ α, c α ≠ 0) ∧
      TubeLimit M (fun σ t => (∑ α : Fin Mm,
          ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
          * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma
              ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α i)
        / gammaShapeZ σ 0 (-(p β : ℤ)) ((E β 0 : ℤ)) t)
        (∑ α ∈ Finset.univ.filter (fun α : Fin Mm =>
            (0 : ℤ) = (0 : ℤ) ∧ (-(p α : ℤ)) = (-(p β : ℤ))
              ∧ ((E α 0 : ℤ)) = ((E β 0 : ℤ))), c α) := by
  classical
  choose p c hc hlim using fun α : Fin Mm =>
    exists_tubeLimit_jetMonomial_datum hM K d (a α) (E α) (hdeg α) (ha α)
  obtain ⟨β, hβ⟩ := exists_tubeLimit_dominant_class hM hMm
    (fun α σ t => ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
      * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma
          ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α i)
    (fun _ => (0 : ℤ)) (fun α => -(p α : ℤ)) (fun α => (E α 0 : ℤ)) c hlim
  exact ⟨p, c, β, hc, hβ⟩

end

end GaloisForLFunctions.HTGeometry
