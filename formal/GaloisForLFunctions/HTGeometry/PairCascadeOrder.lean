import GaloisForLFunctions.HTGeometry.PairPolynomialBridge
import GaloisForLFunctions.HTGeometry.CascadeExactOrderFromSeparation
import GaloisForLFunctions.HTGeometry.ExpPolyCascade

/-!
# The unit-cost law for linear first-order cascades

A cascade of transcendental entire maps each solving `h' = a(z)·h + b(z)` with polynomial
coefficients and `a ≠ 0` has differential order exactly its length.

The upper bound is the card's general one.  The lower bound is the observability step, now
discharged by the two-coordinate peel: the cascade's states obey the product law
`δ X_k = ∏_(j<k) (a_j(X_j)·X_(j+1) + b_j(X_j))`, whose output-jet Jacobian is nonsingular at every
height.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The two-coordinate law of a linear first-order cascade. -/
noncomputable def linearPair (a b : ℕ → Polynomial ℂ) : ℕ → MvPolynomial (Fin 2) ℂ :=
  fun j => affinePair (a j) (b j)

theorem linearPair_eq (a b : ℕ → Polynomial ℂ) (j : ℕ) :
    linearPair a b j = affinePair (a j) (b j) := rfl

/-! ## The first-order equation of one map -/

variable {h : ℕ → ℂ → ℂ} {a b : ℕ → Polynomial ℂ}

/-- **The first-order equation of a linear map.** -/
theorem differentiallyAlgebraicOfOrder_one_linear
    (hode : ∀ k z, deriv (h k) z = (a k).eval z * h k z + (b k).eval z) (k : ℕ) :
    DifferentiallyAlgebraicOfOrder (h k) 1 := by
  classical
  refine ⟨MvPolynomial.X 2
      - (Polynomial.aeval (MvPolynomial.X (0 : Fin 3)) (a k)) * MvPolynomial.X 1
      - (Polynomial.aeval (MvPolynomial.X (0 : Fin 3)) (b k)), ?_, ?_⟩
  · intro h0
    have h1 := congrArg
      (MvPolynomial.eval (![0, 0, (b k).eval 0 + 1] : Fin 3 → ℂ)) h0
    have e1 : (![0, 0, (b k).eval 0 + 1] : Fin 3 → ℂ) 1 = 0 := rfl
    have e2 : (![0, 0, (b k).eval 0 + 1] : Fin 3 → ℂ) 2 = (b k).eval 0 + 1 := rfl
    simp only [map_sub, map_mul, MvPolynomial.eval_X, eval_aeval_X_zero, map_zero,
      e1, e2, mul_zero, sub_zero] at h1
    simp at h1
  · intro z
    have h0 : iteratedDeriv 0 (h k) z = h k z := by simp [iteratedDeriv_zero]
    have h1 : iteratedDeriv 1 (h k) z = (a k).eval z * h k z + (b k).eval z := by
      rw [iteratedDeriv_one, hode]
    have hv0 : (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) (h k) z) : Fin 3 → ℂ) 0
        = z := rfl
    have hv1 : (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) (h k) z) : Fin 3 → ℂ) 1
        = iteratedDeriv 0 (h k) z := rfl
    have hv2 : (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) (h k) z) : Fin 3 → ℂ) 2
        = iteratedDeriv 1 (h k) z := rfl
    have hea : MvPolynomial.eval
        (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) (h k) z) : Fin 3 → ℂ)
        (Polynomial.aeval (MvPolynomial.X (0 : Fin 3)) (a k)) = (a k).eval z := by
      rw [eval_aeval_X_zero]
      rw [hv0]
    have heb : MvPolynomial.eval
        (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) (h k) z) : Fin 3 → ℂ)
        (Polynomial.aeval (MvPolynomial.X (0 : Fin 3)) (b k)) = (b k).eval z := by
      rw [eval_aeval_X_zero]
      rw [hv0]
    simp only [map_sub, map_mul, MvPolynomial.eval_X, hea, heb, hv1, hv2, h0, h1]
    ring

/-! ## The cascade's product law -/

theorem differentiable_linearCascade (hd : ∀ k, Differentiable ℂ (h k)) (k : ℕ) :
    Differentiable ℂ (entireCascade h k) := by
  induction k with
  | zero =>
      have hid : entireCascade h 0 = id := rfl
      rw [hid]
      exact differentiable_id
  | succ k ih =>
      have hstate : entireCascade h (k + 1) = fun z => h k (entireCascade h k z) := rfl
      rw [hstate]
      exact fun z => (hd k _).comp z (ih z)

theorem deriv_linearCascade (hd : ∀ k, Differentiable ℂ (h k))
    (hode : ∀ k z, deriv (h k) z = (a k).eval z * h k z + (b k).eval z) (k : ℕ) (z : ℂ) :
    deriv (entireCascade h k) z
      = ∏ j ∈ Finset.range k,
        ((a j).eval (entireCascade h j z) * entireCascade h (j + 1) z
          + (b j).eval (entireCascade h j z)) := by
  induction k with
  | zero =>
      have hid : entireCascade h 0 = id := rfl
      rw [hid]
      simp
  | succ k ih =>
      have hstate : entireCascade h (k + 1) = fun z => h k (entireCascade h k z) := rfl
      have hinner : HasDerivAt (entireCascade h k) (deriv (entireCascade h k) z) z :=
        (differentiable_linearCascade hd k z).hasDerivAt
      have houter : HasDerivAt (h k) (deriv (h k) (entireCascade h k z))
          (entireCascade h k z) := (hd k _).hasDerivAt
      have hcomp := houter.comp z hinner
      have hcomp' : deriv (fun w => h k (entireCascade h k w)) z
          = deriv (h k) (entireCascade h k z) * deriv (entireCascade h k) z := hcomp.deriv
      rw [hstate, hcomp', ih, hode k (entireCascade h k z), Finset.prod_range_succ]
      have hnext : h k (entireCascade h k z) = entireCascade h (k + 1) z := rfl
      rw [hnext]
      ring

/-- **The cascade obeys the two-coordinate law.** -/
theorem law_linearCascade (hd : ∀ k, Differentiable ℂ (h k))
    (hode : ∀ k z, deriv (h k) z = (a k).eval z * h k z + (b k).eval z) (k : ℕ) (z : ℂ) :
    deriv (entireCascade h k) z
      = evalAt (entireCascade h) z (polyPairDerivation (linearPair a b) (MvPolynomial.X k)) := by
  rw [deriv_linearCascade hd hode, polyPairDerivation_X, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [linearPair_eq, pairPoly_affinePair, map_add, map_mul, evalAt_univFactor, evalAt_univFactor,
    evalAt_X]

/-! ## The capstone -/

/-- **The unit-cost law for a linear first-order cascade.**  A cascade of `m+1` transcendental
entire maps, each solving `h' = a(z)·h + b(z)` with polynomial coefficients and `a ≠ 0`, has
differential order exactly `m+1`. -/
theorem exactDifferentialOrder_linearCascade
    (hent : ∀ k, TranscendentalEntire (h k))
    (hode : ∀ k z, deriv (h k) z = (a k).eval z * h k z + (b k).eval z)
    (ha : ∀ k, a k ≠ 0) (m : ℕ) :
    ExactDifferentialOrder (entireCascade h (m + 1)) (m + 1) := by
  have hd : ∀ k, Differentiable ℂ (h k) := fun k => (hent k).1
  refine ⟨differentiallyAlgebraicOfOrder_entireCascade_of_transcendental' hent
    (fun k _ => differentiallyAlgebraicOfOrder_one_linear hode k), ?_⟩
  intro n hn hDA
  have htop : ¬ DifferentiallyAlgebraicOfOrder (entireCascade h (m + 1)) m := by
    refine not_differentiallyAlgebraicOfOrder_of_model
      (δ := polyPairDerivation (linearPair a b))
      (Y := entireCascade h) (N := m + 1) (m := m)
      (fun k => differentiable_linearCascade hd k)
      (fun k z => law_linearCascade hd hode k z)
      (fun Q hQ => exists_evalAt_ne_zero_of_transcendental hent hQ) ?_ rfl
    refine algebraicIndependent_cons_of_jetDet ?_
    exact pairJetDet_ne_zero_general (linearPair a b) (fun j => rfl) ha m
  exact htop (hDA.mono (by omega))

end GaloisForLFunctions.HTGeometry
