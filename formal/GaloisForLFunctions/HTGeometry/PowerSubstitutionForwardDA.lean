import GaloisForLFunctions.HTGeometry.PowerSubstitutionForwardJet
import GaloisForLFunctions.HTGeometry.Hypertranscendence

/-!
# Differential algebraicity is preserved by `z ↦ z^q`

The inverted chain rule expresses `s(z)^{2j} f^{(j)}(z^q)` as a polynomial-coefficient combination
of the jets of `g(z) = f(z^q)`, where `s = q X^{q-1}`.  Substituting into an algebraic differential
equation for `f` and homogenising in the jet variables by the common denominator `s^{2n}` clears
every division, and the resulting differential polynomial is nonzero because the substitution is
triangular with invertible diagonal at every `z ≠ 0`.

Together with `differentiallyAlgebraic_of_comp_pow` this makes differential algebraicity invariant
under every monomial change of variable `z ↦ c z^q`.
-/

namespace HTGeometry

open Polynomial MvPolynomial GaloisForLFunctions

variable {n q : ℕ}

/-! ## The substituted differential polynomial -/

/-- A univariate polynomial in the point slot of a jet polynomial ring. -/
noncomputable def pointPoly (n : ℕ) (P : Polynomial ℂ) : MvPolynomial (Fin (n + 2)) ℂ :=
  Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (0 : Fin (n + 2))) P

theorem eval_pointPoly (n : ℕ) (P : Polynomial ℂ) (v : Fin (n + 2) → ℂ) :
    MvPolynomial.eval v (pointPoly n P) = P.eval (v 0) := by
  have h := Polynomial.hom_eval₂ P (MvPolynomial.C : ℂ →+* MvPolynomial (Fin (n + 2)) ℂ)
    (MvPolynomial.eval v) (MvPolynomial.X (0 : Fin (n + 2)))
  have hid : ((MvPolynomial.eval v).comp
      (MvPolynomial.C : ℂ →+* MvPolynomial (Fin (n + 2)) ℂ) : ℂ →+* ℂ) = RingHom.id ℂ := by
    refine RingHom.ext fun c => ?_
    simp
  rw [pointPoly, h, hid, MvPolynomial.eval_X, Polynomial.eval₂_id]

/-- The numerator polynomials of the inverted chain rule, with the common denominator `s^{2n}`
already distributed. -/
noncomputable def powInvNumer (q n j : ℕ) : MvPolynomial (Fin (n + 2)) ℂ :=
  (∑ i : Fin (n + 1), pointPoly n (powInvCoeff q j (i : ℕ)) * MvPolynomial.X i.succ)
    * (pointPoly n (powScale q)) ^ (2 * n - 2 * j)

/-- Evaluating the numerator polynomial on the jets of the pullback. -/
theorem eval_powInvNumer {f : ℂ → ℂ}
    (hf : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m f))
    (hg : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m (fun w : ℂ => f (w ^ q))))
    (n j : ℕ) (hj : j ≤ n) (z : ℂ) :
    MvPolynomial.eval
        (Fin.cons z (fun i : Fin (n + 1) =>
          iteratedDeriv (i : ℕ) (fun w : ℂ => f (w ^ q)) z)) (powInvNumer q n j)
      = ((powScale q).eval z) ^ (2 * n) * iteratedDeriv j f (z ^ q) := by
  have hjets : ∀ i : Fin (n + 1),
      (Fin.cons z (fun i : Fin (n + 1) =>
        iteratedDeriv (i : ℕ) (fun w : ℂ => f (w ^ q)) z) : Fin (n + 2) → ℂ) i.succ
        = iteratedDeriv (i : ℕ) (fun w : ℂ => f (w ^ q)) z := fun i => by
    rw [Fin.cons_succ]
  have hpoint : (Fin.cons z (fun i : Fin (n + 1) =>
      iteratedDeriv (i : ℕ) (fun w : ℂ => f (w ^ q)) z) : Fin (n + 2) → ℂ) 0 = z := rfl
  rw [powInvNumer, map_mul, map_pow, map_sum]
  have hsum : ∑ i : Fin (n + 1),
      MvPolynomial.eval
        (Fin.cons z (fun i : Fin (n + 1) =>
          iteratedDeriv (i : ℕ) (fun w : ℂ => f (w ^ q)) z))
        (pointPoly n (powInvCoeff q j (i : ℕ)) * MvPolynomial.X i.succ)
      = ∑ i ∈ Finset.range (j + 1),
        (powInvCoeff q j i).eval z * iteratedDeriv i (fun w : ℂ => f (w ^ q)) z := by
    have hterm : ∀ i : Fin (n + 1),
        MvPolynomial.eval
          (Fin.cons z (fun i : Fin (n + 1) =>
            iteratedDeriv (i : ℕ) (fun w : ℂ => f (w ^ q)) z))
          (pointPoly n (powInvCoeff q j (i : ℕ)) * MvPolynomial.X i.succ)
          = (powInvCoeff q j (i : ℕ)).eval z
              * iteratedDeriv (i : ℕ) (fun w : ℂ => f (w ^ q)) z := by
      intro i
      rw [map_mul, eval_pointPoly, MvPolynomial.eval_X, hjets i, hpoint]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => (powInvCoeff q j i).eval z * iteratedDeriv i (fun w : ℂ => f (w ^ q)) z) (n + 1)]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro i hi
      have h1 : i < j + 1 := Finset.mem_range.mp hi
      exact Finset.mem_range.mpr (by omega)
    · intro i _ hi
      rw [powInvCoeff_eq_zero_of_lt q (by simpa using hi)]
      simp
  rw [hsum, ← pow_mul_iteratedDeriv_comp_pow hf hg j z, eval_pointPoly, hpoint]
  have hpow : ((powScale q).eval z) ^ (2 * j) * ((powScale q).eval z) ^ (2 * n - 2 * j)
      = ((powScale q).eval z) ^ (2 * n) := by
    rw [← pow_add]
    congr 1
    omega
  linear_combination (iteratedDeriv j f (z ^ q)) * hpow

/-! ## The homogenised substitution -/

/-- The differential polynomial obtained from `Q` by substituting the inverted chain rule and
homogenising in the jet variables by the common denominator `s^{2n}`. -/
noncomputable def powForwardPoly (q n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    MvPolynomial (Fin (n + 2)) ℂ :=
  ∑ a ∈ Q.support,
    MvPolynomial.C (MvPolynomial.coeff a Q)
      * (MvPolynomial.X (0 : Fin (n + 2)) ^ q) ^ a 0
      * (∏ j : Fin (n + 1), (powInvNumer q n (j : ℕ)) ^ a j.succ)
      * (pointPoly n (powScale q)) ^ (2 * n * (Q.totalDegree - ∑ j : Fin (n + 1), a j.succ))

/-- **Master evaluation.**  If the numerator polynomials evaluate to `s^{2n}` times a jet vector
`b`, the homogenised substitution evaluates to `(s^{2n})^{deg Q}` times `Q` at `(z^q, b)`. -/
theorem eval_powForwardPoly (q n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) (z : ℂ)
    (Y b : Fin (n + 1) → ℂ)
    (hb : ∀ j : Fin (n + 1),
      MvPolynomial.eval (Fin.cons z Y) (powInvNumer q n (j : ℕ))
        = ((powScale q).eval z) ^ (2 * n) * b j) :
    MvPolynomial.eval (Fin.cons z Y) (powForwardPoly q n Q)
      = (((powScale q).eval z) ^ (2 * n)) ^ Q.totalDegree
        * MvPolynomial.eval (Fin.cons (z ^ q) b) Q := by
  classical
  set S : ℂ := ((powScale q).eval z) ^ (2 * n) with hS
  have hterm : ∀ a ∈ Q.support,
      MvPolynomial.eval (Fin.cons z Y)
          (MvPolynomial.C (MvPolynomial.coeff a Q)
            * (MvPolynomial.X (0 : Fin (n + 2)) ^ q) ^ a 0
            * (∏ j : Fin (n + 1), (powInvNumer q n (j : ℕ)) ^ a j.succ)
            * (pointPoly n (powScale q)) ^ (2 * n * (Q.totalDegree - ∑ j : Fin (n + 1), a j.succ)))
        = S ^ Q.totalDegree
          * (MvPolynomial.coeff a Q * (z ^ q) ^ a 0
              * ∏ j : Fin (n + 1), b j ^ a j.succ) := by
    intro a ha
    have hle : ∑ j : Fin (n + 1), a j.succ ≤ Q.totalDegree := by
      have h1 : a.sum (fun _ e => e) ≤ Q.totalDegree := MvPolynomial.le_totalDegree ha
      have h2 : a.sum (fun _ e => e) = ∑ v : Fin (n + 2), a v :=
        (Finsupp.sum_fintype a (fun _ e => e) (fun _ => rfl))
      have h3 : ∑ v : Fin (n + 2), a v = a 0 + ∑ j : Fin (n + 1), a j.succ :=
        Fin.sum_univ_succ (fun v => a v)
      omega
    have hprod : MvPolynomial.eval (Fin.cons z Y)
        (∏ j : Fin (n + 1), (powInvNumer q n (j : ℕ)) ^ a j.succ)
        = S ^ (∑ j : Fin (n + 1), a j.succ) * ∏ j : Fin (n + 1), b j ^ a j.succ := by
      rw [map_prod]
      have h1 : ∀ j : Fin (n + 1),
          MvPolynomial.eval (Fin.cons z Y) ((powInvNumer q n (j : ℕ)) ^ a j.succ)
            = S ^ a j.succ * b j ^ a j.succ := by
        intro j
        rw [map_pow, hb j, mul_pow]
      rw [Finset.prod_congr rfl fun j _ => h1 j, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum]
    have hcons : (Fin.cons z Y : Fin (n + 2) → ℂ) 0 = z := rfl
    have hscale : MvPolynomial.eval (Fin.cons z Y)
        ((pointPoly n (powScale q)) ^ (2 * n * (Q.totalDegree - ∑ j : Fin (n + 1), a j.succ)))
        = S ^ (Q.totalDegree - ∑ j : Fin (n + 1), a j.succ) := by
      rw [map_pow, eval_pointPoly, hcons, hS, ← pow_mul]
    have hsplit : S ^ (∑ j : Fin (n + 1), a j.succ)
        * S ^ (Q.totalDegree - ∑ j : Fin (n + 1), a j.succ) = S ^ Q.totalDegree := by
      rw [← pow_add]
      congr 1
      omega
    rw [map_mul, map_mul, map_mul, hprod, hscale, MvPolynomial.eval_C, map_pow, map_pow,
      MvPolynomial.eval_X, hcons]
    linear_combination
      (MvPolynomial.coeff a Q * (z ^ q) ^ a 0 * ∏ j : Fin (n + 1), b j ^ a j.succ) * hsplit
  rw [powForwardPoly, map_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun a _ => ?_
  have hRHS : ∏ v : Fin (n + 2), (Fin.cons (z ^ q) b : Fin (n + 2) → ℂ) v ^ a v
      = (z ^ q) ^ a 0 * ∏ j : Fin (n + 1), b j ^ a j.succ := by
    have h := Fin.prod_univ_succ (f := fun v : Fin (n + 2) =>
      (Fin.cons (z ^ q) b : Fin (n + 2) → ℂ) v ^ a v)
    rw [h]
    have hs : ∀ j : Fin (n + 1),
        (Fin.cons (z ^ q) b : Fin (n + 2) → ℂ) j.succ ^ a j.succ = b j ^ a j.succ :=
      fun j => by rw [Fin.cons_succ]
    rw [Finset.prod_congr rfl fun j _ => hs j,
      show (Fin.cons (z ^ q) b : Fin (n + 2) → ℂ) 0 = z ^ q from rfl]
  rw [hRHS]
  ring

/-! ## Nonvanishing and the forward transfer -/

theorem eval_powInvNumer_apply (q n j : ℕ) (z : ℂ) (Y : Fin (n + 1) → ℂ) :
    MvPolynomial.eval (Fin.cons z Y) (powInvNumer q n j)
      = (∑ i : Fin (n + 1), (powInvCoeff q j (i : ℕ)).eval z * Y i)
        * ((powScale q).eval z) ^ (2 * n - 2 * j) := by
  have hcons : (Fin.cons z Y : Fin (n + 2) → ℂ) 0 = z := rfl
  rw [powInvNumer, map_mul, map_pow, map_sum, eval_pointPoly, hcons]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, eval_pointPoly, MvPolynomial.eval_X, hcons, Fin.cons_succ]

/-- The inverted triangular system is solvable at every nonzero point. -/
theorem exists_powInvCoeff_solution (hq : 0 < q) {z : ℂ} (hz : z ≠ 0) (n : ℕ)
    (c : Fin (n + 1) → ℂ) :
    ∃ Y : Fin (n + 1) → ℂ,
      ∀ j : Fin (n + 1),
        ∑ i : Fin (n + 1), (powInvCoeff q (j : ℕ) (i : ℕ)).eval z * Y i = c j := by
  classical
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.of fun j i => (powInvCoeff q (j : ℕ) (i : ℕ)).eval z with hM
  have hsne : ((powScale q).eval z) ≠ 0 := by
    rw [eval_powScale]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hq.ne') (pow_ne_zero _ hz)
  have hlow : M.BlockTriangular ⇑OrderDual.toDual := by
    intro i j hij
    have hlt : (i : ℕ) < (j : ℕ) := OrderDual.toDual_lt_toDual.mp hij
    simp [hM, powInvCoeff_eq_zero_of_lt q hlt]
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular M hlow]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    have hdiag : M i i = ((powScale q).eval z) ^ (i : ℕ) := by
      simp [hM, powInvCoeff_self]
    rw [hdiag]
    exact pow_ne_zero _ hsne
  refine ⟨M⁻¹.mulVec c, fun j => ?_⟩
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hsolve : M.mulVec (M⁻¹.mulVec c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hu, Matrix.one_mulVec]
  have hj := congrFun hsolve j
  simpa [Matrix.mulVec, dotProduct, hM] using hj

/-- **The homogenised substitution is nonzero.** -/
theorem powForwardPoly_ne_zero (hq : 0 < q) {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    (hQ : Q ≠ 0) : powForwardPoly q n Q ≠ 0 := by
  intro hzero
  apply hQ
  have hall : ∀ z : ℂ, z ≠ 0 → ∀ b : Fin (n + 1) → ℂ,
      MvPolynomial.eval (Fin.cons (z ^ q) b) Q = 0 := by
    intro z hz b
    have hsne : ((powScale q).eval z) ≠ 0 := by
      rw [eval_powScale]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr hq.ne') (pow_ne_zero _ hz)
    obtain ⟨Y, hY⟩ := exists_powInvCoeff_solution hq hz n
      (fun j => ((powScale q).eval z) ^ (2 * (j : ℕ)) * b j)
    have hb : ∀ j : Fin (n + 1),
        MvPolynomial.eval (Fin.cons z Y) (powInvNumer q n (j : ℕ))
          = ((powScale q).eval z) ^ (2 * n) * b j := by
      intro j
      have hjn : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.isLt
      rw [eval_powInvNumer_apply, hY j]
      have hpow : ((powScale q).eval z) ^ (2 * (j : ℕ))
          * ((powScale q).eval z) ^ (2 * n - 2 * (j : ℕ))
          = ((powScale q).eval z) ^ (2 * n) := by
        rw [← pow_add]
        congr 1
        omega
      calc ((powScale q).eval z) ^ (2 * (j : ℕ)) * b j
              * ((powScale q).eval z) ^ (2 * n - 2 * (j : ℕ))
          = (((powScale q).eval z) ^ (2 * (j : ℕ))
              * ((powScale q).eval z) ^ (2 * n - 2 * (j : ℕ))) * b j := by ring
        _ = ((powScale q).eval z) ^ (2 * n) * b j := by rw [hpow]
    have heval := eval_powForwardPoly q n Q z Y b hb
    rw [hzero, map_zero] at heval
    rcases mul_eq_zero.mp heval.symm with h | h
    · exact absurd h (pow_ne_zero _ (pow_ne_zero _ hsne))
    · exact h
  have hXQ : (MvPolynomial.X (0 : Fin (n + 2)) : MvPolynomial (Fin (n + 2)) ℂ) * Q = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, map_zero, MvPolynomial.eval_X]
    by_cases hx : x 0 = 0
    · rw [hx, zero_mul]
    · obtain ⟨z, hz⟩ : ∃ z : ℂ, z ^ q = x 0 := IsAlgClosed.exists_pow_nat_eq (x 0) hq
      have hzne : z ≠ 0 := by
        intro h
        rw [h, zero_pow hq.ne'] at hz
        exact hx hz.symm
      have hcons : Fin.cons (x 0) (fun j : Fin (n + 1) => x j.succ) = x := by
        funext v
        refine Fin.cases ?_ ?_ v <;> simp
      rw [← hcons, ← hz, hall z hzne _, mul_zero]
  exact (mul_eq_zero.mp hXQ).resolve_left (MvPolynomial.X_ne_zero 0)

/-- **Differential algebraicity is preserved by `z ↦ z^q`.** -/
theorem differentiallyAlgebraic_comp_pow {f : ℂ → ℂ} (hq : 0 < q)
    (hf : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m f))
    (hg : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m (fun w : ℂ => f (w ^ q))))
    (h : DifferentiallyAlgebraic f) :
    DifferentiallyAlgebraic (fun z : ℂ => f (z ^ q)) := by
  obtain ⟨n, Q, hQ0, hQ⟩ := h
  refine ⟨n, powForwardPoly q n Q, powForwardPoly_ne_zero hq hQ0, ?_⟩
  intro z
  have hb : ∀ j : Fin (n + 1),
      MvPolynomial.eval
          (Fin.cons z (fun i : Fin (n + 1) =>
            iteratedDeriv (i : ℕ) (fun w : ℂ => f (w ^ q)) z)) (powInvNumer q n (j : ℕ))
        = ((powScale q).eval z) ^ (2 * n) * iteratedDeriv (j : ℕ) f (z ^ q) :=
    fun j => eval_powInvNumer hf hg n (j : ℕ) (Nat.lt_succ_iff.mp j.isLt) z
  rw [eval_powForwardPoly q n Q z _ _ hb, hQ (z ^ q), mul_zero]

end HTGeometry
