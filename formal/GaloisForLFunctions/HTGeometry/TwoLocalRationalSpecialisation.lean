import GaloisForLFunctions.HTGeometry.TwoLocalSymmetricGalois
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.GaloisSpecialization

/-!
# Rational specializations of the transverse family keep the symmetric Galois group

The universal transverse characteristic polynomial is separable — its roots in the power series
ring are labelled by their distinct values at zero coupling — and its Galois group over the field of
rational functions in the couplings is the full symmetric group on the hypercube.  Hilbert
irreducibility therefore produces rational couplings, avoiding any prescribed nonzero polynomial
condition, at which the specialized characteristic polynomial still has symmetric Galois group.

## Main results

* `natDegree_universalCharpoly` — the degree is the size of the hypercube.
* `separable_universalCharpoly_map` — separability over the rational function field.
* `exists_rational_specialisation` — **a rational transverse Hamiltonian with symmetric Galois
  group, avoiding any prescribed nonzero polynomial condition.**
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type} [Field A] {m : ℕ}

theorem natDegree_universalCharpoly (d : (Fin (m + 1) → Bool) → A) :
    (universalCharpoly A (m + 1) d).natDegree = 2 ^ (m + 1) := by
  rw [universalCharpoly, Matrix.charpoly_natDegree_eq_dim]
  simp

/-- **The universal transverse characteristic polynomial is separable.**  Its roots in the power
series ring have pairwise distinct values at zero coupling. -/
theorem separable_universalCharpoly_map {d : (Fin (m + 1) → Bool) → A}
    (hd : Function.Injective d) :
    ((universalCharpoly A (m + 1) d).map
      (algebraMap (MvPolynomial (Fin (m + 1)) A)
        (FractionRing (MvPolynomial (Fin (m + 1)) A)))).Separable := by
  classical
  haveI : IsDomain (MvPowerSeries (Fin (m + 1)) A) := isDomain_mvPowerSeries A _
  have hcoeinj : Function.Injective
      (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (m + 1)) (R := A)) :=
    MvPolynomial.coe_injective (σ := Fin (m + 1)) (R := A)
  obtain ⟨Θ, hΘ, hconst⟩ := exists_canonicalRootFamily d hd
  have hΘinj : Function.Injective Θ := by
    intro x y hxy
    have := congrArg (MvPowerSeries.constantCoeff (σ := Fin (m + 1)) (R := A)) hxy
    rw [hconst, hconst] at this
    exact hd this
  refine (Polynomial.separable_map (fracLift hcoeinj)).mp ?_
  have hmapeq : ((universalCharpoly A (m + 1) d).map
        (algebraMap (MvPolynomial (Fin (m + 1)) A)
          (FractionRing (MvPolynomial (Fin (m + 1)) A)))).map (fracLift hcoeinj)
      = ∏ x, (X - C (algebraMap (MvPowerSeries (Fin (m + 1)) A)
          (FractionRing (MvPowerSeries (Fin (m + 1)) A)) (Θ x))) := by
    rw [Polynomial.map_map,
      show ((fracLift hcoeinj).comp
          (algebraMap (MvPolynomial (Fin (m + 1)) A)
            (FractionRing (MvPolynomial (Fin (m + 1)) A))))
        = (algebraMap (MvPowerSeries (Fin (m + 1)) A)
            (FractionRing (MvPowerSeries (Fin (m + 1)) A))).comp
          (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (m + 1)) (R := A)) from
        RingHom.ext fun p => fracLift_algebraMap hcoeinj p, ← Polynomial.map_map,
      show (universalCharpoly A (m + 1) d).map
          (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (m + 1)) (R := A))
        = universalCharpolySeries d from rfl, hΘ, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun x _ => by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [hmapeq]
  refine Polynomial.separable_prod_X_sub_C_iff.mpr ?_
  exact Function.Injective.comp
    (IsFractionRing.injective (MvPowerSeries (Fin (m + 1)) A)
      (FractionRing (MvPowerSeries (Fin (m + 1)) A))) hΘinj

/-- **A rational transverse Hamiltonian with symmetric Galois group.**  For diagonal energies whose
edge detunings are, in every direction, pairwise distinct and never opposite, Hilbert irreducibility
gives rational couplings — avoiding any prescribed nonzero polynomial condition — at which the
characteristic polynomial has Galois group of order `(2ⁿ)!`. -/
theorem exists_rational_specialisation {d : (Fin (m + 1) → Bool) → ℚ}
    (hd : Function.Injective d)
    (hδinj : ∀ i, Function.Injective (detuning d i))
    (hδne : ∀ i z z', detuning d i z ≠ -detuning d i z')
    {g : MvPolynomial (Fin (m + 1)) ℚ} (hg : g ≠ 0) :
    ∃ y : Fin (m + 1) → ℚ, MvPolynomial.eval y g ≠ 0 ∧
      Nat.card ((universalCharpoly ℚ (m + 1) d).map (MvPolynomial.eval y)).Gal
        = (2 ^ (m + 1)).factorial :=
  HilbertIrreducibility.gal_card_of_specialisation
    (universalCharpoly_monic ℚ (m + 1) d) (natDegree_universalCharpoly d)
    (separable_universalCharpoly_map hd)
    (card_gal_universalCharpoly (by norm_num) hd hδinj hδne) hg


theorem map_universalTransverseHam_eval (d : (Fin (m + 1) → Bool) → A) (y : Fin (m + 1) → A) :
    (universalTransverseHam A (m + 1) d).map (MvPolynomial.eval y)
      = transverseFamilyHam d y := by
  rw [universalTransverseHam, map_transverseFamilyHam]
  have h1 : (fun x => (MvPolynomial.eval y) (MvPolynomial.C (d x))) = d := by
    funext x
    simp
  have h2 : (fun j => (MvPolynomial.eval y) (MvPolynomial.X j)) = y := by
    funext j
    simp
  rw [h1, h2]

/-- **Specializing the couplings gives the characteristic polynomial of the transverse family.** -/
theorem map_universalCharpoly_eval (d : (Fin (m + 1) → Bool) → A) (y : Fin (m + 1) → A) :
    (universalCharpoly A (m + 1) d).map (MvPolynomial.eval y)
      = (transverseFamilyHam d y).charpoly := by
  rw [universalCharpoly, ← Matrix.charpoly_map, map_universalTransverseHam_eval]

theorem trace_transverseFamilyHam (d : (Fin (m + 1) → Bool) → A) (y : Fin (m + 1) → A) :
    (transverseFamilyHam d y).trace = ∑ x, d x := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun x _ => ?_
  show (if x = x then d x else _) = d x
  rw [if_pos rfl]

end

end GaloisForLFunctions.HTGeometry
