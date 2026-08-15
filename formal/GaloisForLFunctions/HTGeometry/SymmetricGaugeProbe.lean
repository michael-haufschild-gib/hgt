import GaloisForLFunctions.HTGeometry.SymmetricPolynomialJets
import GaloisForLFunctions.HTGeometry.GaugeProbeJetFamily

/-!
# The symmetric passport probe

A perturbation of an exponent that must keep the functional equation, Schwarz reality, and a
prescribed finite jet passport is a symmetric polynomial divisible by the passport multiplier.
Averaging a coefficient window over the symmetry group produces exactly such polynomials, and the
average still realizes arbitrary jets at a node with a free symmetry orbit: the four averaged terms
contribute equally once the interpolation data at the orbit is extended equivariantly.

Multiplying by the passport multiplier is triangular and invertible on jets off its divisor, so the
constrained probe is onto the jets exactly like the unconstrained window.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-! ### The symmetry orbit of a node family -/

/-- The four points of the symmetry orbit of each node. -/
def orbitNode {X : Type*} (ν : X → ℂ) : X × Fin 4 → ℂ := fun p =>
  if p.2 = 0 then ν p.1
  else if p.2 = 1 then 1 - ν p.1
  else if p.2 = 2 then (starRingEnd ℂ) (ν p.1)
  else 1 - (starRingEnd ℂ) (ν p.1)

@[simp] theorem orbitNode_zero {X : Type*} (ν : X → ℂ) (x : X) :
    orbitNode ν (x, 0) = ν x := by simp [orbitNode]

@[simp] theorem orbitNode_one {X : Type*} (ν : X → ℂ) (x : X) :
    orbitNode ν (x, 1) = 1 - ν x := by simp [orbitNode]

@[simp] theorem orbitNode_two {X : Type*} (ν : X → ℂ) (x : X) :
    orbitNode ν (x, 2) = (starRingEnd ℂ) (ν x) := by simp [orbitNode]

@[simp] theorem orbitNode_three {X : Type*} (ν : X → ℂ) (x : X) :
    orbitNode ν (x, 3) = 1 - (starRingEnd ℂ) (ν x) := by
  simp only [orbitNode]
  norm_num

/-! ### The symmetric probe -/

variable {X : Type*} [Fintype X]

/-- The constrained probe: a symmetric average of a coefficient window, multiplied by the passport
polynomial. -/
def symProbe (X : Type*) [Fintype X] (Hp : Polynomial ℂ) (m N D : ℕ) : GaugeProbe X m D :=
  realCombProbe X m D
    (fun i => Hp * avgPoly (Polynomial.monomial (N + (i : ℕ)) (1 : ℂ)))
    (fun i => Hp * avgPoly (Polynomial.monomial (N + (i : ℕ)) Complex.I))

theorem symProbe_poly (Hp : Polynomial ℂ) (m N D : ℕ) (c : Fin D → ℂ) :
    (symProbe X Hp m N D).poly c = Hp * avgPoly (windowLin N D c) := by
  show realCombPoly D _ _ c = _
  rw [realCombPoly, windowLin_apply]
  rw [show avgPoly (∑ i : Fin D, Polynomial.monomial (N + (i : ℕ)) (c i))
      = ∑ i : Fin D, avgPoly (Polynomial.monomial (N + (i : ℕ)) (c i)) from by
    classical
    induction (Finset.univ : Finset (Fin D)) using Finset.induction_on with
    | empty => simp [avgPoly, reflectPoly, conjPoly]
    | insert a s ha ih => rw [Finset.sum_insert ha, avgPoly_add, ih, Finset.sum_insert ha]]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsplit : (Polynomial.monomial (N + (i : ℕ)) (c i) : Polynomial ℂ)
      = Polynomial.C (((c i).re : ℂ)) * Polynomial.monomial (N + (i : ℕ)) (1 : ℂ)
        + Polynomial.C (((c i).im : ℂ)) * Polynomial.monomial (N + (i : ℕ)) Complex.I := by
    rw [Polynomial.C_mul_monomial, Polynomial.C_mul_monomial, ← map_add, mul_one]
    congr 1
    exact (Complex.re_add_im (c i)).symm
  rw [hsplit, avgPoly_add, avgPoly_real_C_mul, avgPoly_real_C_mul, mul_add]
  ring

theorem reflectPoly_symProbe_poly (Hp : Polynomial ℂ) (hH : reflectPoly Hp = Hp)
    (m N D : ℕ) (c : Fin D → ℂ) :
    reflectPoly ((symProbe X Hp m N D).poly c) = (symProbe X Hp m N D).poly c := by
  rw [symProbe_poly, reflectPoly, Polynomial.mul_comp, ← reflectPoly, ← reflectPoly, hH,
    reflectPoly_avgPoly, symProbe_poly]

theorem conjPoly_symProbe_poly (Hp : Polynomial ℂ) (hH : conjPoly Hp = Hp)
    (m N D : ℕ) (c : Fin D → ℂ) :
    conjPoly ((symProbe X Hp m N D).poly c) = (symProbe X Hp m N D).poly c := by
  rw [symProbe_poly, conjPoly, Polynomial.map_mul, ← conjPoly, ← conjPoly, hH,
    conjPoly_avgPoly, symProbe_poly]

end

end GaloisForLFunctions.HTGeometry
