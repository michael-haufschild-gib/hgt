import GaloisForLFunctions.HTGeometry.FamilyPolynomialGauge
import GaloisForLFunctions.HTGeometry.FamilyInversionGauge
import GaloisForLFunctions.HTGeometry.ExponentialFullIndependence
import GaloisForLFunctions.HTGeometry.SpectralMobiusGauge

/-!
# Differential independence of the parabolic orbit of the exponential Cayley carrier

`hardy-cyclicity-maximal-ht-field-blindness`, statement `2`.

The carrier of the card is `O = exp ∘ c ∘ m ∘ φ` with `c(x) = (x−i)/(x+i)` the Cayley map of the
upper half plane into the disk and `φ(w) = i(1+w)/(1−w)` its inverse.  Because
`φ(τ_t(w)) = φ(w) + t`, the parabolic orbit `{O ∘ τ_t}` is, in the half-plane coordinate, the
family `z ↦ exp(c(m(z + t)))`.  Relation-freeness therefore transports along three corpus gauges:

* the Cayley post-composition `c` (affine + inversion gauges);
* the exponential (`not_familyDifferentiallyAlgebraicOn_exp`);
* the Möbius change of variable `φ` (`not_familyDifferentiallyAlgebraicOn_comp_mobius`).
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Relation-freeness only depends on the family near the domain -/

theorem familyDifferentiallyAlgebraicOn_congr {m : ℕ} {U : Set ℂ} (hU : IsOpen U)
    {g h : Fin m → ℂ → ℂ} (hgh : ∀ i, ∀ w ∈ U, g i w = h i w)
    (hrel : FamilyDifferentiallyAlgebraicOn g U) : FamilyDifferentiallyAlgebraicOn h U := by
  obtain ⟨n, P, hPne, hP⟩ := hrel
  refine ⟨n, P, hPne, fun z hz => ?_⟩
  have hjet : familyJetVec (n := n) h z = familyJetVec (n := n) g z := by
    funext s
    cases s with
    | inl x => rfl
    | inr p =>
        obtain ⟨i, j⟩ := p
        show iteratedDeriv (j : ℕ) (h i) z = iteratedDeriv (j : ℕ) (g i) z
        have heq : h i =ᶠ[nhds z] g i := by
          filter_upwards [hU.mem_nhds hz] with w hw
          exact (hgh i w hw).symm
        rw [heq.iteratedDeriv_eq]
  rw [hjet]
  exact hP z hz

/-! ## The Cayley post-composition gauge -/

theorem not_familyDifferentiallyAlgebraicOn_cayley {m : ℕ} {U : Set ℂ} (hU : IsOpen U)
    {g : Fin m → ℂ → ℂ}
    (hg : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) w)
    (hne : ∀ i, ∀ w ∈ U, g i w + Complex.I ≠ 0)
    (hfree : ¬ FamilyDifferentiallyAlgebraicOn g U) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i w => (g i w - Complex.I) / (g i w + Complex.I)) U := by
  intro hrel
  apply hfree
  set gI : Fin m → ℂ → ℂ := fun i w => g i w + Complex.I with hgI
  have hgIsmooth : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (gI i) w := by
    intro i w hw
    exact (hg i w hw).add contDiffAt_const
  have hgsmooth' : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z := fun z hz i => hg i z hz
  have hinvsmooth : ∀ z ∈ U, ∀ i, ContDiffAt ℂ (⊤ : ℕ∞) (fun w => (gI i w)⁻¹) z := by
    intro z hz i
    exact (hgIsmooth i z hz).inv (hne i z hz)
  -- the Cayley family agrees on `U` with an affine gauge of the reciprocals
  have hshape : ∀ i, ∀ w ∈ U,
      (g i w - Complex.I) / (g i w + Complex.I)
        = Polynomial.eval w (Polynomial.C (1 : ℂ))
          + Polynomial.eval w (Polynomial.C (-2 * Complex.I)) * (gI i w)⁻¹ := by
    intro i w hw
    have hden : g i w + Complex.I ≠ 0 := hne i w hw
    rw [hgI]
    simp only [Polynomial.eval_C]
    field_simp
    ring
  have hrel' : FamilyDifferentiallyAlgebraicOn
      (fun i w => Polynomial.eval w (Polynomial.C (1 : ℂ))
        + Polynomial.eval w (Polynomial.C (-2 * Complex.I)) * (gI i w)⁻¹) U :=
    familyDifferentiallyAlgebraicOn_congr hU (fun i w hw => hshape i w hw) hrel
  have hcne : (Polynomial.C (-2 * Complex.I) : Polynomial ℂ) ≠ 0 := by
    simp only [ne_eq, Polynomial.C_eq_zero]
    intro h
    have h2 : Complex.I = 0 := by
      have := h
      field_simp at this
      exact this
    exact Complex.I_ne_zero h2
  have hinvfree : FamilyDifferentiallyAlgebraicOn (fun i w => (gI i w)⁻¹) U :=
    familyDifferentiallyAlgebraicOn_of_affine (fun i w => (gI i w)⁻¹)
      (fun _ => Polynomial.C (-2 * Complex.I)) (fun _ => Polynomial.C (1 : ℂ))
      (fun _ => hcne) hinvsmooth hrel'
  have hgIfree : FamilyDifferentiallyAlgebraicOn gI U :=
    familyDifferentiallyAlgebraicOn_of_inv hU hgIsmooth (fun i w hw => hne i w hw) hinvfree
  refine familyDifferentiallyAlgebraicOn_of_add_polynomial g
    (fun _ => Polynomial.C Complex.I) hgsmooth' ?_
  simpa [hgI] using hgIfree

end

end GaloisForLFunctions.HTGeometry
