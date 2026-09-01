import GaloisForLFunctions.HTGeometry.RittLogTowerRing
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The affine tower as a substitution on a multivariate polynomial ring

The shift of the affine tower moves each jet to a base-affine combination of the jets below it, so it
is the pullback along an affine substitution of the polynomial ring in the jets.  Writing

`towerSub j = ∑_{i ≤ j} logCoeff j i · X i + logConst b j`,

the ring endomorphism `towerShift` that applies the base map to the coefficients and substitutes
`towerSub` for the variables intertwines with the shift of the ambient field along evaluation at the
jets.  This is the form in which the collapse of the tower becomes a single polynomial identity.
-/

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

open MvPolynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The affine image of the `j`-th variable under the tower shift. -/
noncomputable def towerSub (Fr : RittFrame K L) (b : K) (n : ℕ) (j : Fin n) :
    MvPolynomial (Fin n) K :=
  (∑ i : Fin n, C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i) + C (Fr.logConst b (j : ℕ))

/-- The tower shift as an endomorphism of the polynomial ring in the jets. -/
noncomputable def towerShift (Fr : RittFrame K L) (b : K) (n : ℕ) :
    MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K :=
  eval₂Hom ((C : K →+* MvPolynomial (Fin n) K).comp Fr.ψ) (Fr.towerSub b n)

theorem towerShift_C (Fr : RittFrame K L) (b : K) (n : ℕ) (a : K) :
    Fr.towerShift b n (C a) = C (Fr.ψ a) := by
  simp [towerShift]

theorem towerShift_X (Fr : RittFrame K L) (b : K) (n : ℕ) (j : Fin n) :
    Fr.towerShift b n (X j) = Fr.towerSub b n j := by
  simp [towerShift]

/-- **Evaluation at the jets intertwines the polynomial shift with the shift of the field.** -/
theorem aeval_towerShift (Fr : RittFrame K L) {u : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b) (n : ℕ)
    (F : MvPolynomial (Fin n) K) :
    aeval (fun j : Fin n => Fr.d^[(j : ℕ)] u) (Fr.towerShift b n F)
      = Fr.σ (aeval (fun j : Fin n => Fr.d^[(j : ℕ)] u) F) := by
  induction F using MvPolynomial.induction_on with
  | C a => rw [towerShift_C, aeval_C, aeval_C, Fr.comp]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p j hp =>
      rw [map_mul, map_mul, map_mul, map_mul, hp, towerShift_X]
      congr 1
      rw [towerSub, map_add, map_sum, aeval_C, aeval_X, Fr.sigma_affineJet hu (j : ℕ)]
      have hcoeff : ∀ i : Fin n, aeval (fun j : Fin n => Fr.d^[(j : ℕ)] u)
          (C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i)
          = algebraMap K L (Fr.logCoeff (j : ℕ) (i : ℕ)) * Fr.d^[(i : ℕ)] u := by
        intro i
        rw [map_mul, aeval_C, aeval_X]
      have hsum : (∑ i : Fin n, aeval (fun j : Fin n => Fr.d^[(j : ℕ)] u)
            (C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i))
          = ∑ i ∈ Finset.range ((j : ℕ) + 1),
            algebraMap K L (Fr.logCoeff (j : ℕ) i) * Fr.d^[i] u := by
        rw [Finset.sum_congr rfl (fun i _ => hcoeff i),
          Fin.sum_univ_eq_sum_range
            (fun i => algebraMap K L (Fr.logCoeff (j : ℕ) i) * Fr.d^[i] u) n]
        have hsub : Finset.range ((j : ℕ) + 1) ⊆ Finset.range n := by
          have hj : (j : ℕ) < n := j.isLt
          intro x hx
          simp only [Finset.mem_range] at hx ⊢
          omega
        refine (Finset.sum_subset hsub ?_).symm
        intro i _ hi
        simp only [Finset.mem_range, not_lt] at hi
        rw [Fr.logCoeff_eq_zero_of_lt (j : ℕ) i (by omega), map_zero, zero_mul]
      rw [hsum]

end RittFrame

end GaloisForLFunctions.HTGeometry
