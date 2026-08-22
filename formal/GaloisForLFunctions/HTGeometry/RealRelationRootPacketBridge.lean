import GaloisForLFunctions.HTGeometry.LinearRelationObstructionPullback
import GaloisForLFunctions.HTGeometry.PolynomialHermitianMatrixProjectiveGenericity

/-!
# From an escaping root packet to the absence of an identical real relation

The two halves are now in place: a Hermitian local extension supplies a real root packet escaping
every relabeling of a real relation, and the labeling-orbit obstruction of such a relation is a
polynomial in the characteristic coefficients, hence in the parameters.  This file joins them for a
**polynomial matrix family**, whose signed characteristic coefficients are the elementary symmetric
functions of any simple root packet (`matrixCharacteristicElementaryCoefficient_eq_rootPacket`).

## Main results

* `eval₂_esymm_eq` — evaluating an elementary symmetric polynomial is the sum over subsets.
* `esymm_eval₂_cast` — the rational and real elementary symmetric polynomials agree after casting.
* `not_relation_on_open_of_rootPacket_escape` — **(L2) for a polynomial matrix family.**
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem eval₂_esymm_eq {R S : Type*} [CommSemiring R] [CommSemiring S] {I : Type*} [Fintype I]
    (f : R →+* S) (g : I → S) (n : ℕ) :
    MvPolynomial.eval₂ f g (MvPolynomial.esymm I R n)
      = ∑ t ∈ Finset.univ.powersetCard n, ∏ i ∈ t, g i := by
  classical
  rw [MvPolynomial.esymm]
  rw [show (MvPolynomial.eval₂ f g) = (MvPolynomial.eval₂Hom f g : MvPolynomial I R →+* S) from rfl]
  rw [map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_prod]
  simp

/-- The rational and real elementary symmetric polynomials agree after casting to `ℂ`. -/
theorem esymm_eval₂_cast {I : Type*} [Fintype I] (energy : I → ℝ) (n : ℕ) :
    MvPolynomial.eval₂ (Rat.castHom ℂ) (fun i => ((energy i : ℝ) : ℂ))
        (MvPolynomial.esymm I ℚ n)
      = ((MvPolynomial.eval energy (MvPolynomial.esymm I ℝ n) : ℝ) : ℂ) := by
  classical
  rw [eval₂_esymm_eq]
  rw [show (MvPolynomial.eval energy) (MvPolynomial.esymm I ℝ n)
      = MvPolynomial.eval₂ (RingHom.id ℝ) energy (MvPolynomial.esymm I ℝ n) from rfl]
  rw [eval₂_esymm_eq]
  push_cast
  rfl

/-- **(L2) for a polynomial matrix family.**  If one real parameter carries a simple root packet
escaping every relabeling of the real relation `c`, then `c` cannot annihilate the spectrum
throughout any nonempty open set of parameters. -/
theorem not_relation_on_open_of_rootPacket_escape
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ)) {c : I → ℝ}
    (p₀ : Fin m → ℝ) (energy₀ : I → ℝ)
    (hinj₀ : Function.Injective energy₀)
    (hroot₀ : ∀ i,
      matrixCharpolyRelation
        (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p₀ t : ℂ))),
          ((energy₀ i : ℝ) : ℂ)) = 0)
    (hesc : ∀ σ : Equiv.Perm I, ∑ i, c i * energy₀ (σ i) ≠ 0)
    {U : Set (Fin m → ℝ)} (hU : IsOpen U) (hUne : U.Nonempty)
    (spec : (Fin m → ℝ) → I → ℝ)
    (hinj : ∀ q ∈ U, Function.Injective (spec q))
    (hrootq : ∀ q ∈ U, ∀ i,
      matrixCharpolyRelation
        (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (q t : ℂ))),
          ((spec q i : ℝ) : ℂ)) = 0)
    (hrel : ∀ q ∈ U, ∑ i, c i * spec q i = 0) : False := by
  classical
  have hbridge : ∀ (q : Fin m → ℝ) (e : I → ℝ),
      Function.Injective e →
      (∀ i, matrixCharpolyRelation
        (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (q t : ℂ))),
          ((e i : ℝ) : ℂ)) = 0) →
      ∀ j : Fin (Fintype.card I),
        MvPolynomial.eval₂ (RingHom.id ℂ) (fun i => (q i : ℂ))
            (matrixCharacteristicElementaryPolynomial M j)
          = ((MvPolynomial.eval e (MvPolynomial.esymm I ℝ (j.1 + 1)) : ℝ) : ℂ) := by
    intro q e he hr j
    rw [eval_matrixCharacteristicElementaryPolynomial]
    rw [matrixCharacteristicElementaryCoefficient_eq_rootPacket _ (fun i => ((e i : ℝ) : ℂ))
      (fun a b h => he (Complex.ofReal_injective h)) hr j]
    exact esymm_eval₂_cast e (j.1 + 1)
  exact not_relation_on_open_of_escape (matrixCharacteristicElementaryPolynomial M) p₀ energy₀
    (hbridge p₀ energy₀ hinj₀ hroot₀) hesc hU hUne spec
    (fun q hq => hbridge q (spec q) (hinj q hq) (hrootq q hq)) hrel

end

end GaloisForLFunctions.HTGeometry
