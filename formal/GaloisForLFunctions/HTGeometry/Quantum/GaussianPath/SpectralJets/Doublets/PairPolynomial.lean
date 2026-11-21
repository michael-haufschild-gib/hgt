import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.RescaledCharacteristic
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # The normalized characteristic polynomial in the longitudinal fields -/
open Matrix Finset
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section
variable {R S I κ : Type*} [CommRing R] [CommRing S] [Fintype I] [DecidableEq I] [Fintype κ]

/-- Each field is an independent polynomial variable. The energy variable is indexed by none. -/
def fieldPoly (u : κ → R) : MvPolynomial (Option κ) R :=
  ∑ i, MvPolynomial.C (u i)*MvPolynomial.X (some i)

theorem map_fieldPoly (φ : R →+* S) (u : κ → R) :
    MvPolynomial.map φ (fieldPoly u) = fieldPoly (φ ∘ u) := by
  simp only [fieldPoly,map_sum,map_mul,MvPolynomial.map_C,MvPolynomial.map_X,Function.comp_apply]

theorem eval_fieldPoly (u : κ → R) (x : Option κ → R) :
    MvPolynomial.eval x (fieldPoly u) = ∑ i, u i*x (some i) := by
  simp only [fieldPoly,map_sum,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]

theorem fieldPoly_neg (u : κ → R) :
    fieldPoly (-u) = -fieldPoly u := by
  simp [fieldPoly,Finset.sum_neg_distrib]

/-- The sign of the field term is negative in the characteristic matrix zI−H. -/
def pairPolynomial (A : Matrix I I R) (E : I → R) (u : I → κ → R) (s t : I) (b r : R) :
    MvPolynomial (Option κ) R :=
  rescaledDet (A.map MvPolynomial.C) (MvPolynomial.C ∘ E) (fun j => -fieldPoly (u j)) s t
    (MvPolynomial.C b) (MvPolynomial.C r) (MvPolynomial.X none)

theorem map_pairPolynomial (φ : R →+* S) (A : Matrix I I R) (E : I → R) (u : I → κ → R)
    (s t : I) (b r : R) :
    MvPolynomial.map φ (pairPolynomial A E u s t b r) =
      pairPolynomial (A.map φ) (φ ∘ E) (fun j => φ ∘ u j) s t (φ b) (φ r) := by
  simp only [pairPolynomial,map_rescaledDet,Matrix.map_map,Function.comp_def,MvPolynomial.map_C,
    map_neg,map_fieldPoly,MvPolynomial.map_X]

/-- The spectator gaps survive only as an overall constant at a diagonal collision. -/
theorem pairPolynomial_diagonal (E : I → R) (u : I → κ → R) (s t : I) (hst : s≠t)
    (hE : E s=E t) (hu : u t= -u s) :
    pairPolynomial (diagonal E) E u s t (E s) 0 =
      MvPolynomial.C (2*(∏ j ∈ (univ.erase s).erase t, (E s-E j))) *
        ((MvPolynomial.X none)^2-1-(fieldPoly (u s))^2) := by
  have hD : (diagonal E).map (MvPolynomial.C : R →+* MvPolynomial (Option κ) R) =
      diagonal (MvPolynomial.C ∘ E) := by
    ext i j
    by_cases he : i=j
    · subst j; simp [Matrix.map_apply]
    · simp [Matrix.map_apply,Matrix.diagonal_apply_ne _ he]
  unfold pairPolynomial
  have he := congrArg (MvPolynomial.C : R →+* MvPolynomial (Option κ) R) hE
  have hg : -fieldPoly (u t) = -(-fieldPoly (u s)) := by rw [hu,fieldPoly_neg]
  rw [map_zero,hD]
  simpa only [Function.comp_apply,map_mul,map_ofNat,map_prod,map_sub,neg_sq] using
    rescaled_diagonal (MvPolynomial.C ∘ E) (fun j => -fieldPoly (u j)) s t hst he hg (MvPolynomial.X none)

end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
