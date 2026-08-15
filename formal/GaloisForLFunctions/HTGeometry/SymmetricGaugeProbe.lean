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
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]

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
    reflectPoly_avgPoly]

theorem conjPoly_symProbe_poly (Hp : Polynomial ℂ) (hH : conjPoly Hp = Hp)
    (m N D : ℕ) (c : Fin D → ℂ) :
    conjPoly ((symProbe X Hp m N D).poly c) = (symProbe X Hp m N D).poly c := by
  rw [symProbe_poly, conjPoly, Polynomial.map_mul, ← conjPoly, ← conjPoly, hH,
    conjPoly_avgPoly]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {X : Type*} [Fintype X]

theorem symProbe_jet_apply (Hp : Polynomial ℂ) (m N D : ℕ) (ν : X → ℂ) (c : Fin D → ℂ)
    (x : X) (k : Fin m) :
    (symProbe X Hp m N D).jet ν c x k
      = (Polynomial.derivative^[(k : ℕ)] (Hp * avgPoly (windowLin N D c))).eval (ν x) := by
  rw [congrFun ((symProbe X Hp m N D).jet_eq ν c x) k, gaugeJetVec,
    iteratedDeriv_polynomial_eval, symProbe_poly]

theorem windowProbe_jet_apply' (m N D : ℕ) {Y : Type*} [Fintype Y] (μ : Y → ℂ)
    (c : Fin D → ℂ) (y : Y) (k : Fin m) :
    (windowProbe Y m N D).jet μ c y k
      = (Polynomial.derivative^[(k : ℕ)] (windowLin N D c)).eval (μ y) := by
  rw [congrFun ((windowProbe Y m N D).jet_eq μ c y) k, gaugeJetVec,
    iteratedDeriv_polynomial_eval, windowProbe_poly]

/-- **The constrained symmetric probe is onto the jets at a free orbit.** -/
theorem surjective_symProbe_jet [DecidableEq X] (Hp : Polynomial ℂ) (m N : ℕ) {ν : X → ℂ}
    (hinj : Function.Injective (orbitNode ν)) (hne : ∀ p, orbitNode ν p ≠ 0)
    (hHp : ∀ x, Hp.eval (ν x) ≠ 0) :
    Function.Surjective
      ((symProbe X Hp m N (Fintype.card (X × Fin 4) * m)).jet ν) := by
  classical
  set D := Fintype.card (X × Fin 4) * m with hD
  intro target
  obtain ⟨β, hβ⟩ := surjective_leibnizBlockLin m
    (fun x r => iteratedDeriv r (fun w => Polynomial.eval w Hp) (ν x))
    (fun x => by
      rw [iteratedDeriv_zero]
      exact hHp x) target
  set B : (X × Fin 4) → Fin m → ℂ := fun p k =>
    if p.2 = 0 then β p.1 k
    else if p.2 = 1 then (-1 : ℂ) ^ (k : ℕ) * β p.1 k
    else if p.2 = 2 then (starRingEnd ℂ) (β p.1 k)
    else (-1 : ℂ) ^ (k : ℕ) * (starRingEnd ℂ) (β p.1 k) with hB
  obtain ⟨c, hc⟩ := surjective_windowProbe_jet (X := X × Fin 4) m N hinj hne B
  refine ⟨c, ?_⟩
  set Q : Polynomial ℂ := windowLin N D c with hQdef
  have hjetQ : ∀ (p : X × Fin 4) (k : Fin m),
      (Polynomial.derivative^[(k : ℕ)] Q).eval (orbitNode ν p) = B p k := by
    intro p k
    have := congrFun (congrFun hc p) k
    rw [windowProbe_jet_apply'] at this
    exact this
  have hconjPow : ∀ k : ℕ, (starRingEnd ℂ) ((-1 : ℂ) ^ k) = (-1 : ℂ) ^ k := by
    intro k
    rw [map_pow]
    norm_num
  have havg : ∀ (x : X) (k : Fin m),
      (Polynomial.derivative^[(k : ℕ)] (avgPoly Q)).eval (ν x) = β x k := by
    intro x k
    rw [iterate_derivative_avgPoly_eval]
    have e0 : (Polynomial.derivative^[(k : ℕ)] Q).eval (ν x) = β x k := by
      have := hjetQ (x, 0) k
      rw [orbitNode_zero] at this
      rw [this, hB]
      simp
    have e1 : (Polynomial.derivative^[(k : ℕ)] Q).eval (1 - ν x)
        = (-1 : ℂ) ^ (k : ℕ) * β x k := by
      have := hjetQ (x, 1) k
      rw [orbitNode_one] at this
      rw [this, hB]
      simp
    have e2 : (Polynomial.derivative^[(k : ℕ)] Q).eval ((starRingEnd ℂ) (ν x))
        = (starRingEnd ℂ) (β x k) := by
      have := hjetQ (x, 2) k
      rw [orbitNode_two] at this
      rw [this, hB]
      simp only
      rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    have e3 : (Polynomial.derivative^[(k : ℕ)] Q).eval (1 - (starRingEnd ℂ) (ν x))
        = (-1 : ℂ) ^ (k : ℕ) * (starRingEnd ℂ) (β x k) := by
      have := hjetQ (x, 3) k
      rw [orbitNode_three] at this
      rw [this, hB]
      simp only
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    rw [e0, e1, e2, e3, map_mul, hconjPow, Complex.conj_conj]
    have hsq : (-1 : ℂ) ^ (k : ℕ) * ((-1 : ℂ) ^ (k : ℕ) * β x k) = β x k := by
      rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [hsq]
    ring
  funext x
  have hleib : ∀ k : Fin m, (symProbe X Hp m N D).jet ν c x k
      = ∑ j : Fin m,
        leibnizJetMatrix m (fun r => iteratedDeriv r (fun w => Polynomial.eval w Hp) (ν x)) k j
          * β x j := by
    intro k
    rw [symProbe_jet_apply]
    have hfun : (fun w => Polynomial.eval w (Hp * avgPoly Q))
        = fun w => Polynomial.eval w Hp * Polynomial.eval w (avgPoly Q) := by
      funext w
      rw [Polynomial.eval_mul]
    have hd : (Polynomial.derivative^[(k : ℕ)] (Hp * avgPoly Q)).eval (ν x)
        = iteratedDeriv (k : ℕ) (fun w => Polynomial.eval w Hp * Polynomial.eval w (avgPoly Q))
          (ν x) := by
      rw [← hfun, iteratedDeriv_polynomial_eval]
    rw [hd, iteratedDeriv_mul_eq_leibnizJetMatrix m
      (contDiffAt_of_entire (Polynomial.differentiable Hp) m (ν x))
      (contDiffAt_of_entire (Polynomial.differentiable (avgPoly Q)) m (ν x)) k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedDeriv_polynomial_eval, havg x j]
  funext k
  rw [hleib k]
  have hval := congrFun (congrFun hβ x) k
  rw [leibnizBlockLin_apply, Matrix.mulVec, dotProduct] at hval
  exact hval

end

end GaloisForLFunctions.HTGeometry
