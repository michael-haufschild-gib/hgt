import GaloisForLFunctions.HTGeometry.ProductLawTwoMapIndependence
import GaloisForLFunctions.HTGeometry.ExpShiftCascade

/-!
# Cascades of first-order linear entire maps with polynomial coefficients

A transcendental entire solution of `f' = a(w)·(f − d)` with polynomial `a` is `d + c·exp(A(w))` with
`A' = a`.  This file is the analytic side of that family: the maps, their differentiability, and the
derivative law in the form the polynomial model consumes.

Its cascade law is `δX_(k+1) = A_k'(X_k)·(X_(k+1) − d_k)·δX_k`, which is the product law with
`Q_j = A_j'·(X − d_(j−1))` and `v_k = X − d_(k−1)` — the shape whose determinant the algebraic layers
compute.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The first-order linear entire map with polynomial coefficient. -/
noncomputable def expPoly (A : ℕ → Polynomial ℂ) (c d : ℕ → ℂ) (k : ℕ) : ℂ → ℂ :=
  fun w => d k + c k * Complex.exp ((A k).eval w)

theorem differentiable_expPoly (A : ℕ → Polynomial ℂ) (c d : ℕ → ℂ) (k : ℕ) :
    Differentiable ℂ (expPoly A c d k) := by
  intro z
  have hp : DifferentiableAt ℂ (fun w : ℂ => (A k).eval w) z :=
    ((A k).hasDerivAt z).differentiableAt
  exact ((hp.cexp).const_mul (c k)).const_add (d k)

/-- **The defining equation.** -/
theorem deriv_expPoly (A : ℕ → Polynomial ℂ) (c d : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    deriv (expPoly A c d k) z
      = (A k).derivative.eval z * (expPoly A c d k z - d k) := by
  have hp : HasDerivAt (fun w : ℂ => (A k).eval w) ((A k).derivative.eval z) z :=
    (A k).hasDerivAt z
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp ((A k).eval w))
      (Complex.exp ((A k).eval z) * (A k).derivative.eval z) z := hp.cexp
  have hmul : HasDerivAt (fun w : ℂ => c k * Complex.exp ((A k).eval w))
      (c k * (Complex.exp ((A k).eval z) * (A k).derivative.eval z)) z := hexp.const_mul (c k)
  have hall : HasDerivAt (expPoly A c d k)
      (c k * (Complex.exp ((A k).eval z) * (A k).derivative.eval z)) z := hmul.const_add (d k)
  rw [hall.deriv, expPoly]
  ring

/-- The map is transcendental entire when its exponent is nonconstant. -/
theorem transcendentalEntire_expPoly {A : ℕ → Polynomial ℂ} {c d : ℕ → ℂ} {k : ℕ}
    (hc : c k ≠ 0) (hA : 1 ≤ (A k).natDegree) :
    TranscendentalEntire (expPoly A c d k) := by
  refine ⟨differentiable_expPoly A c d k, ?_⟩
  rintro ⟨p, hp⟩
  set q : Polynomial ℂ := Polynomial.C (c k)⁻¹ * (p - Polynomial.C (d k)) with hq
  have hval : ∀ z : ℂ, Complex.exp ((A k).eval z) = q.eval z := by
    intro z
    have h := hp z
    rw [expPoly] at h
    rw [hq]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]
    field_simp
    linear_combination h
  have hqroot : ∀ z : ℂ, q.eval z ≠ 0 := by
    intro z hz
    exact Complex.exp_ne_zero ((A k).eval z) (by rw [hval z, hz])
  have hqdeg : q.natDegree = 0 := by
    by_contra hne
    obtain ⟨z, hz⟩ := Complex.exists_root (f := q) (by
      rw [Polynomial.degree_eq_natDegree (fun h0 => hne (by rw [h0]; simp))]
      exact_mod_cast Nat.pos_of_ne_zero hne)
    exact hqroot z (by simpa [Polynomial.IsRoot] using hz)
  have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hqdeg
  have hconst : ∀ z : ℂ, Complex.exp ((A k).eval z) = q.coeff 0 := by
    intro z
    rw [hval z, hqC]
    simp
  have hderiv : ∀ z : ℂ, (A k).derivative.eval z * q.coeff 0 = 0 := by
    intro z
    have h1 : HasDerivAt (fun w : ℂ => Complex.exp ((A k).eval w))
        (Complex.exp ((A k).eval z) * (A k).derivative.eval z) z := ((A k).hasDerivAt z).cexp
    have h2 : HasDerivAt (fun w : ℂ => Complex.exp ((A k).eval w)) 0 z := by
      have hfun : (fun w : ℂ => Complex.exp ((A k).eval w)) = fun _ => q.coeff 0 := by
        funext w
        exact hconst w
      rw [hfun]
      exact hasDerivAt_const z (q.coeff 0)
    have := h1.unique h2
    rw [hconst z] at this
    rw [mul_comm]
    exact this
  have hq0 : q.coeff 0 ≠ 0 := by
    intro h0
    exact hqroot 0 (by rw [hqC]; simp [h0])
  have hAzero : (A k).derivative = 0 := by
    refine Polynomial.funext fun z => ?_
    have := hderiv z
    rcases mul_eq_zero.mp this with h | h
    · simpa using h
    · exact absurd h hq0
  rw [Polynomial.derivative_eq_zero] at hAzero
  omega

/-! ## The cascade law -/

/-- The terminal factor of the law: the shift by the previous constant. -/
noncomputable def polyV (d : ℕ → ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | (k + 1) => Polynomial.X - Polynomial.C (d k)

/-- The per-coordinate factor of the law. -/
noncomputable def polyQ (A : ℕ → Polynomial ℂ) (d : ℕ → ℂ) (j : ℕ) : Polynomial ℂ :=
  (A j).derivative * polyV d j

@[simp] theorem polyV_zero (d : ℕ → ℂ) : polyV d 0 = 1 := rfl

theorem polyV_succ (d : ℕ → ℂ) (k : ℕ) :
    polyV d (k + 1) = Polynomial.X - Polynomial.C (d k) := rfl

theorem differentiable_expPolyCascade (A : ℕ → Polynomial ℂ) (c d : ℕ → ℂ) (k : ℕ) :
    Differentiable ℂ (entireCascade (expPoly A c d) k) := by
  induction k with
  | zero =>
      have h : entireCascade (expPoly A c d) 0 = id := rfl
      rw [h]
      exact differentiable_id
  | succ k ih =>
      have h : entireCascade (expPoly A c d) (k + 1)
          = fun z => expPoly A c d k (entireCascade (expPoly A c d) k z) := rfl
      rw [h]
      exact (differentiable_expPoly A c d k).comp ih

/-- **The cascade law.**  Each state's derivative is the product of one factor per earlier coordinate
times the terminal shift. -/
theorem deriv_expPolyCascade (A : ℕ → Polynomial ℂ) (c d : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    deriv (entireCascade (expPoly A c d) k) z
      = (∏ j ∈ Finset.range k,
          (polyQ A d j).eval (entireCascade (expPoly A c d) j z))
        * (polyV d k).eval (entireCascade (expPoly A c d) k z) := by
  induction k with
  | zero =>
      have h : entireCascade (expPoly A c d) 0 = id := rfl
      rw [h]
      simp
  | succ k ih =>
      have hstate : entireCascade (expPoly A c d) (k + 1)
          = fun z => expPoly A c d k (entireCascade (expPoly A c d) k z) := rfl
      have hinner : HasDerivAt (entireCascade (expPoly A c d) k)
          (deriv (entireCascade (expPoly A c d) k) z) z :=
        (differentiable_expPolyCascade A c d k z).hasDerivAt
      have houter : HasDerivAt (expPoly A c d k)
          (deriv (expPoly A c d k) (entireCascade (expPoly A c d) k z))
          (entireCascade (expPoly A c d) k z) :=
        (differentiable_expPoly A c d k _).hasDerivAt
      have hcomp := (houter.comp z hinner)
      have hcomp' : HasDerivAt (entireCascade (expPoly A c d) (k + 1))
          (deriv (expPoly A c d k) (entireCascade (expPoly A c d) k z)
            * deriv (entireCascade (expPoly A c d) k) z) z := by
        rw [hstate]
        exact hcomp
      have hstate' : entireCascade (expPoly A c d) (k + 1) z
          = expPoly A c d k (entireCascade (expPoly A c d) k z) := rfl
      rw [hcomp'.deriv, deriv_expPoly, ih, Finset.prod_range_succ, polyQ, polyV_succ, hstate']
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      ring

/-! ## The law in model form -/

/-- Evaluating a one-coordinate polynomial at the states. -/
theorem evalAt_univFactor (Y : ℕ → ℂ → ℂ) (z : ℂ) (p : Polynomial ℂ) (j : ℕ) :
    evalAt Y z (univFactor p j) = p.eval (Y j z) := by
  induction p using Polynomial.induction_on with
  | C a => simp [univFactor, evalAt]
  | add p q hp hq =>
      have hsum : univFactor (p + q) j = univFactor p j + univFactor q j := by
        simp [univFactor]
      rw [hsum, map_add, hp, hq, Polynomial.eval_add]
  | monomial n a _ =>
      have hmul : univFactor (Polynomial.C a * Polynomial.X ^ (n + 1)) j
          = MvPolynomial.C a * MvPolynomial.X j ^ (n + 1) := by
        simp [univFactor]
      rw [hmul, map_mul, map_pow]
      simp [evalAt]

/-- **The cascade law, in the form the polynomial model consumes.** -/
theorem law_expPolyCascade (A : ℕ → Polynomial ℂ) (c d : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    deriv (entireCascade (expPoly A c d) k) z
      = evalAt (entireCascade (expPoly A c d)) z
          (polyProdDerivation (polyQ A d) (polyV d) (MvPolynomial.X k)) := by
  rw [deriv_expPolyCascade, polyProdDerivation_X, map_mul, map_prod, evalAt_univFactor]
  refine congrArg (fun t => t * (polyV d k).eval (entireCascade (expPoly A c d) k z)) ?_
  refine Finset.prod_congr rfl fun j _ => ?_
  exact (evalAt_univFactor _ z (polyQ A d j) j).symm

end GaloisForLFunctions.HTGeometry
