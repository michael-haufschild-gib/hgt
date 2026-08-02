import GaloisForLFunctions.HTGeometry.UniformGammaPresentation

/-!
# The residue of a presentation with unnormalized coefficients

The clearing theorem hands over a presentation whose coefficients are plain polynomials, not
polynomials divided by a common power of the argument.  Multiplying a residue by `s^d` shifts its
argument exponent by `d` and leaves the quotient untouched, so the normalization can be undone once,
at the level of the whole presentation.

This states eq. (3) in tube form directly on the clearing data.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Multiplying a residue by a power of the argument shifts its argument exponent. -/
theorem TubeLimit.mul_pow_arg {M : ℝ} {F : ℝ → ℝ → ℂ} {k A B : ℤ} {c : ℂ}
    (h : TubeLimit M (fun σ t => F σ t / gammaShapeZ σ k A B t) c) (d : ℕ) :
    TubeLimit M (fun σ t => (((σ : ℂ) + (t : ℂ) * Complex.I) ^ d * F σ t)
      / gammaShapeZ σ k (A + (d : ℤ)) B t) c := by
  refine h.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [h0] at him
    simp only [Complex.zero_im] at him
    linarith
  have hshape : gammaShapeZ σ k (A + (d : ℤ)) B t
      = ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d * gammaShapeZ σ k A B t := by
    rw [gammaShapeZ, gammaShapeZ, zpow_add₀ hs, zpow_natCast]
    ring
  rw [hshape, mul_div_mul_left _ _ (pow_ne_zero d hs)]

/-- **The residue of a presentation with plain polynomial coefficients, uniformly on a tube.**  This
is the shape the clearing theorem produces: `Γ`-powers times jet polynomials whose coefficients are
polynomials, with per-power monomial counts and jet ranges. -/
theorem exists_tubeLimit_gammaPresentation_residue_raw {M : ℝ} (hM : 0 < M) {N : ℕ}
    (Mm : Fin N → ℕ) (Kf : Fin N → ℕ) (K d : ℕ) (hK : ∀ j, Kf j ≤ K) (u : Fin N → ℕ)
    (a : ∀ j : Fin N, Fin (Mm j) → Polynomial ℂ)
    (E : ∀ j : Fin N, Fin (Mm j) → Fin (Kf j + 1) → ℕ)
    (hdeg : ∀ j α, (a j α).natDegree ≤ d) (ha : ∀ j α, a j α ≠ 0)
    (hne : Nonempty (Σ j : Fin N, Fin (Mm j))) :
    ∃ (p : (Σ j : Fin N, Fin (Mm j)) → ℕ) (c : (Σ j : Fin N, Fin (Mm j)) → ℂ)
      (β : Σ j : Fin N, Fin (Mm j)), (∀ x, c x ≠ 0) ∧
      TubeLimit M (fun σ t => (∑ j : Fin N, gammaLine σ t ^ u j
          * (∑ α : Fin (Mm j), (a j α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            * ∏ i : Fin (Kf j + 1), iteratedDeriv (i : ℕ) Complex.digamma
                ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E j α i))
        / gammaShapeZ σ (u β.1 : ℤ) (-(p β : ℤ) + (d : ℤ)) ((E β.1 β.2 0 : ℤ)) t)
        (∑ x ∈ Finset.univ.filter (fun x : Σ j : Fin N, Fin (Mm j) =>
            (u x.1 : ℤ) = (u β.1 : ℤ) ∧ (-(p x : ℤ) + (d : ℤ)) = (-(p β : ℤ) + (d : ℤ))
              ∧ ((E x.1 x.2 0 : ℤ)) = ((E β.1 β.2 0 : ℤ))), c x) := by
  classical
  haveI := hne
  choose p c hc hlim using fun x : Σ j : Fin N, Fin (Mm j) =>
    exists_tubeLimit_jetMonomial_datum hM K d (a x.1 x.2)
      (fun i : Fin (K + 1) => padExp (Kf x.1) (E x.1 x.2) (i : ℕ))
      (hdeg x.1 x.2) (ha x.1 x.2)
  have hpad : ∀ x : Σ j : Fin N, Fin (Mm j),
      padExp (Kf x.1) (E x.1 x.2) ((0 : Fin (K + 1)) : ℕ) = E x.1 x.2 0 := by
    intro x
    have h0 : ((0 : Fin (K + 1)) : ℕ) = 0 := rfl
    rw [h0, padExp_zero]
  -- each term: monomial datum, times the Gamma power, times the cleared argument power
  have hterm : ∀ x : Σ j : Fin N, Fin (Mm j), TubeLimit M
      (fun σ t => (gammaLine σ t ^ u x.1
          * ((a x.1 x.2).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            * ∏ i : Fin (Kf x.1 + 1), iteratedDeriv (i : ℕ) Complex.digamma
                ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E x.1 x.2 i))
        / gammaShapeZ σ (u x.1 : ℤ) (-(p x : ℤ) + (d : ℤ)) ((E x.1 x.2 0 : ℤ)) t) (c x) := by
    intro x
    have hx := ((hlim x).mul_gammaPow (u x.1)).mul_pow_arg d
    rw [hpad x] at hx
    refine hx.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
    have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      rw [h0] at him
      simp only [Complex.zero_im] at him
      linarith
    rw [prod_jets_pad (hK x.1) (E x.1 x.2)]
    refine congrArg (fun w => w / gammaShapeZ σ (u x.1 : ℤ) (-(p x : ℤ) + (d : ℤ))
      ((E x.1 x.2 0 : ℤ)) t) ?_
    field_simp
  obtain ⟨β, hβ⟩ := exists_tubeLimit_dominant_class_fintype hM
    (fun x σ t => gammaLine σ t ^ u x.1
      * ((a x.1 x.2).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        * ∏ i : Fin (Kf x.1 + 1), iteratedDeriv (i : ℕ) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E x.1 x.2 i))
    (fun x => (u x.1 : ℤ)) (fun x => -(p x : ℤ) + (d : ℤ)) (fun x => (E x.1 x.2 0 : ℤ)) c hterm
  refine ⟨p, c, β, hc, ?_⟩
  refine hβ.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  refine congrArg (fun w => w / gammaShapeZ σ (u β.1 : ℤ) (-(p β : ℤ) + (d : ℤ))
    ((E β.1 β.2 0 : ℤ)) t) ?_
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]

end

end GaloisForLFunctions.HTGeometry
