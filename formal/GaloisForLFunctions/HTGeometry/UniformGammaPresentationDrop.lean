import GaloisForLFunctions.HTGeometry.UniformGammaPresentationRaw

/-!
# Presentations with vanishing coefficients

A presentation produced by clearing denominators need not have all its coefficients nonzero, and the
residue machinery asks for nonzero ones — a monomial with zero coefficient has no datum.  The terms
with vanishing coefficient are the zero function, so dropping them changes nothing, and the residue is
that of the surviving subfamily.

Only one hypothesis is left: *some* coefficient is nonzero, which for a presentation of a nonzero
element is automatic.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The residue of a presentation, dropping the vanishing coefficients.** -/
theorem exists_tubeLimit_gammaPresentation_residue_drop {M : ℝ} (hM : 0 < M) {N : ℕ}
    (Mm : Fin N → ℕ) (Kf : Fin N → ℕ) (K d : ℕ) (hK : ∀ j, Kf j ≤ K) (u : Fin N → ℕ)
    (a : ∀ j : Fin N, Fin (Mm j) → Polynomial ℂ)
    (E : ∀ j : Fin N, Fin (Mm j) → Fin (Kf j + 1) → ℕ)
    (hdeg : ∀ j α, (a j α).natDegree ≤ d)
    (hane : ∃ x : Σ j : Fin N, Fin (Mm j), a x.1 x.2 ≠ 0) :
    ∃ (p : {x : Σ j : Fin N, Fin (Mm j) // a x.1 x.2 ≠ 0} → ℕ)
      (c : {x : Σ j : Fin N, Fin (Mm j) // a x.1 x.2 ≠ 0} → ℂ)
      (β : {x : Σ j : Fin N, Fin (Mm j) // a x.1 x.2 ≠ 0}), (∀ x, c x ≠ 0) ∧
      TubeLimit M (fun σ t => (∑ j : Fin N, gammaLine σ t ^ u j
          * (∑ α : Fin (Mm j), (a j α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            * ∏ i : Fin (Kf j + 1), iteratedDeriv (i : ℕ) Complex.digamma
                ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E j α i))
        / gammaShapeZ σ (u β.val.1 : ℤ) (-(p β : ℤ) + (d : ℤ))
          ((E β.val.1 β.val.2 0 : ℤ)) t)
        (∑ x ∈ Finset.univ.filter
          (fun x : {x : Σ j : Fin N, Fin (Mm j) // a x.1 x.2 ≠ 0} =>
            (u x.val.1 : ℤ)
                = (u β.val.1 : ℤ)
              ∧ (-(p x : ℤ) + (d : ℤ)) = (-(p β : ℤ) + (d : ℤ))
              ∧ ((E x.val.1 x.val.2 0 : ℤ))
                = ((E β.val.1
                    β.val.2 0 : ℤ))), c x) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hane
  haveI : Nonempty {x : Σ j : Fin N, Fin (Mm j) // a x.1 x.2 ≠ 0} := ⟨⟨x₀, hx₀⟩⟩
  -- the surviving terms, with their data
  choose p c hc hlim using fun x : {x : Σ j : Fin N, Fin (Mm j) // a x.1 x.2 ≠ 0} =>
    exists_tubeLimit_jetMonomial_datum hM K d (a x.val.1
        x.val.2)
      (fun i : Fin (K + 1) => padExp (Kf x.val.1)
        (E x.val.1 x.val.2) (i : ℕ))
      (hdeg _ _) x.2
  have hpad : ∀ x : {x : Σ j : Fin N, Fin (Mm j) // a x.1 x.2 ≠ 0},
      padExp (Kf x.val.1)
        (E x.val.1 x.val.2)
        ((0 : Fin (K + 1)) : ℕ)
      = E x.val.1 x.val.2 0 := by
    intro x
    have h0 : ((0 : Fin (K + 1)) : ℕ) = 0 := rfl
    rw [h0, padExp_zero]
  have hterm : ∀ x : {x : Σ j : Fin N, Fin (Mm j) // a x.1 x.2 ≠ 0}, TubeLimit M
      (fun σ t => (gammaLine σ t ^ u x.val.1
          * ((a x.val.1 x.val.2).eval
              ((σ : ℂ) + (t : ℂ) * Complex.I)
            * ∏ i : Fin (Kf x.val.1 + 1),
                iteratedDeriv (i : ℕ) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
                  ^ E x.val.1 x.val.2 i))
        / gammaShapeZ σ (u x.val.1 : ℤ) (-(p x : ℤ) + (d : ℤ))
          ((E x.val.1
              x.val.2 0 : ℤ)) t) (c x) := by
    intro x
    have hx := ((hlim x).mul_gammaPow (u x.val.1)).mul_pow_arg d
    rw [hpad x] at hx
    refine hx.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
    have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      rw [h0] at him
      simp only [Complex.zero_im] at him
      linarith
    rw [prod_jets_pad (hK _) (E _ _)]
    refine congrArg (fun w => w / gammaShapeZ σ (u x.val.1 : ℤ)
      (-(p x : ℤ) + (d : ℤ))
      ((E x.val.1 x.val.2 0 : ℤ)) t) ?_
    field_simp
  obtain ⟨β, hβ⟩ := exists_tubeLimit_dominant_class_fintype hM
    (fun x σ t => gammaLine σ t ^ u x.val.1
      * ((a x.val.1 x.val.2).eval
          ((σ : ℂ) + (t : ℂ) * Complex.I)
        * ∏ i : Fin (Kf x.val.1 + 1),
            iteratedDeriv (i : ℕ) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
              ^ E x.val.1 x.val.2 i))
    (fun x => (u x.val.1 : ℤ)) (fun x => -(p x : ℤ) + (d : ℤ))
    (fun x => (E x.val.1 x.val.2 0 : ℤ)) c hterm
  refine ⟨p, c, β, hc, ?_⟩
  refine hβ.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  refine congrArg (fun w => w / gammaShapeZ σ (u β.val.1 : ℤ)
    (-(p β : ℤ) + (d : ℤ))
    ((E β.val.1 β.val.2 0 : ℤ)) t) ?_
  -- the dropped terms vanish
  have hzero : ∀ x : Σ j : Fin N, Fin (Mm j), a x.1 x.2 = 0 →
      gammaLine σ t ^ u x.1 * ((a x.1 x.2).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        * ∏ i : Fin (Kf x.1 + 1), iteratedDeriv (i : ℕ) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E x.1 x.2 i) = 0 := by
    intro x hx
    rw [hx]
    simp
  set Fterm : (Σ j : Fin N, Fin (Mm j)) → ℂ := fun x => gammaLine σ t ^ u x.1
    * ((a x.1 x.2).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
      * ∏ i : Fin (Kf x.1 + 1), iteratedDeriv (i : ℕ) Complex.digamma
          ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E x.1 x.2 i) with hFterm
  have hsub : ∑ x ∈ (Finset.univ.filter
      fun x : Σ j : Fin N, Fin (Mm j) => a x.1 x.2 ≠ 0), Fterm x
      = ∑ x : {x : Σ j : Fin N, Fin (Mm j) // a x.1 x.2 ≠ 0}, Fterm x.val :=
    Finset.sum_subtype _ (fun x => by simp [Finset.mem_filter]) Fterm
  have hfull : ∑ x ∈ (Finset.univ.filter
      fun x : Σ j : Fin N, Fin (Mm j) => a x.1 x.2 ≠ 0), Fterm x
      = ∑ x : Σ j : Fin N, Fin (Mm j), Fterm x := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun x _ hx => ?_
    have hzx : a x.1 x.2 = 0 := by
      by_contra hne
      exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hne⟩)
    exact hzero x hzx
  rw [← hsub, hfull, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hFterm]
  dsimp only
  rw [← Finset.mul_sum]

end

end GaloisForLFunctions.HTGeometry
