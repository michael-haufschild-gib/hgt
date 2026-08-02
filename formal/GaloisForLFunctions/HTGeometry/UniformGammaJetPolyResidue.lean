import GaloisForLFunctions.HTGeometry.UniformJetMonomialDatum

/-!
# The residue of a Gamma-field presentation, uniformly on a vertical tube

A Gamma-field element in normal form is a finite sum `∑ Γ^{u_α}·a_α(s)/s^d·∏_i (ψ^{(i)})^{E_{α i}}`.
Each term's residue is the monomial's residue — multiplying by a power of `Γ` multiplies the shape by
the same power and leaves the quotient untouched — and the sum has the residue of the dominant class.

That is eq. (3) in tube form for a presentation, with the dominant datum produced rather than assumed.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Multiplying a residue by a power of `Γ` multiplies its shape by the same power. -/
theorem TubeLimit.mul_gammaPow {M : ℝ} {F : ℝ → ℝ → ℂ} {A B : ℤ} {c : ℂ}
    (h : TubeLimit M (fun σ t => F σ t / gammaShapeZ σ 0 A B t) c) (u : ℕ) :
    TubeLimit M (fun σ t => (gammaLine σ t ^ u * F σ t) / gammaShapeZ σ (u : ℤ) A B t) c := by
  refine h.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  have hΓ : gammaLine σ t ≠ 0 := gammaLine_ne_zero hσ t
  have hshape : gammaShapeZ σ (u : ℤ) A B t = gammaLine σ t ^ u * gammaShapeZ σ 0 A B t := by
    rw [gammaShapeZ, gammaShapeZ, zpow_zero, one_mul, zpow_natCast]
  rw [hshape, mul_div_mul_left _ _ (pow_ne_zero u hΓ)]

/-- **The residue of a Gamma-field presentation, uniformly on a tube.** -/
theorem exists_tubeLimit_gammaJetPoly_residue {M : ℝ} (hM : 0 < M) {Ntot : ℕ} (hN : 0 < Ntot)
    (K d : ℕ) (u : Fin Ntot → ℕ) (a : Fin Ntot → Polynomial ℂ)
    (E : Fin Ntot → Fin (K + 1) → ℕ) (hdeg : ∀ α, (a α).natDegree ≤ d) (ha : ∀ α, a α ≠ 0) :
    ∃ (p : Fin Ntot → ℕ) (c : Fin Ntot → ℂ) (β : Fin Ntot), (∀ α, c α ≠ 0) ∧
      TubeLimit M (fun σ t => (∑ α : Fin Ntot, gammaLine σ t ^ u α
          * (((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
              / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
            * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma
                ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α i))
        / gammaShapeZ σ (u β : ℤ) (-(p β : ℤ)) ((E β 0 : ℤ)) t)
        (∑ α ∈ Finset.univ.filter (fun α : Fin Ntot =>
            (u α : ℤ) = (u β : ℤ) ∧ (-(p α : ℤ)) = (-(p β : ℤ))
              ∧ ((E α 0 : ℤ)) = ((E β 0 : ℤ))), c α) := by
  classical
  choose p c hc hlim using fun α : Fin Ntot =>
    exists_tubeLimit_jetMonomial_datum hM K d (a α) (E α) (hdeg α) (ha α)
  obtain ⟨β, hβ⟩ := exists_tubeLimit_dominant_class hM hN
    (fun α σ t => gammaLine σ t ^ u α
      * (((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
        * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α i))
    (fun α => (u α : ℤ)) (fun α => -(p α : ℤ)) (fun α => (E α 0 : ℤ)) c
    (fun α => (hlim α).mul_gammaPow (u α))
  exact ⟨p, c, β, hc, hβ⟩

end

end GaloisForLFunctions.HTGeometry
