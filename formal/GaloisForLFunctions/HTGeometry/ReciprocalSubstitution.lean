import GaloisForLFunctions.HTGeometry.ReciprocalJetPolynomials
import GaloisForLFunctions.HTGeometry.Hypertranscendence

/-!
# Substituting the reciprocal jets into a differential polynomial

If `f·g = 1` on an open set, the jets of `f` are the reciprocal numerators of the jets of `g`
divided by a power of `g`:  `f⁽ʲ⁾ = Aⱼ(g, g′, …)/g^{j+1}`.  Substituting this into a differential
polynomial `P(s, y₀, …, yₙ)` for `f` and clearing the single denominator `g^{(n+1)·deg P}` produces
a differential polynomial `recipSub n P` in the jets of `g`, and

`recipSub n P (s, g, g′, …) = P (s, f, f′, …) · g^{(n+1)·deg P}`

holds pointwise on the set.  In particular a relation for `f` transports verbatim to one for `g`;
what remains for a full reciprocal-closure theorem is that `recipSub` does not kill `P`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-! ## The weight of a jet monomial and the clearing exponent -/

/-- The `g`-degree of the denominator produced by the monomial `α`: substituting
`yⱼ ↦ Aⱼ/g^{j+1}` costs `∑ⱼ (j+1)·αⱼ` powers of `g`. -/
def recipWeight (n : ℕ) (α : Fin (n + 2) →₀ ℕ) : ℕ :=
  ∑ j : Fin (n + 1), ((j : ℕ) + 1) * α j.succ

/-- The uniform clearing exponent `(n+1)·deg P`. -/
def recipBound (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) : ℕ := (n + 1) * P.totalDegree

theorem recipWeight_le_recipBound (n : ℕ) {P : MvPolynomial (Fin (n + 2)) ℂ}
    {α : Fin (n + 2) →₀ ℕ} (hα : α ∈ P.support) :
    recipWeight n α ≤ recipBound n P := by
  have hstep : recipWeight n α ≤ ∑ j : Fin (n + 1), (n + 1) * α j.succ := by
    refine Finset.sum_le_sum fun j _ => ?_
    exact Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.lt_succ_iff.mp j.isLt))
  have hsum : ∑ j : Fin (n + 1), (n + 1) * α j.succ = (n + 1) * ∑ j : Fin (n + 1), α j.succ := by
    rw [Finset.mul_sum]
  have hle : ∑ j : Fin (n + 1), α j.succ ≤ ∑ i : Fin (n + 2), α i := by
    conv_rhs => rw [Fin.sum_univ_succ]
    exact Nat.le_add_left _ _
  have htot : ∑ i : Fin (n + 2), α i ≤ P.totalDegree := by
    have hfs : (α.sum fun _ e => e) = ∑ i : Fin (n + 2), α i := by
      rw [Finsupp.sum_fintype]
      intro _
      rfl
    rw [← hfs]
    exact le_totalDegree hα
  rw [recipBound]
  calc recipWeight n α ≤ ∑ j : Fin (n + 1), (n + 1) * α j.succ := hstep
    _ = (n + 1) * ∑ j : Fin (n + 1), α j.succ := hsum
    _ ≤ (n + 1) * P.totalDegree := Nat.mul_le_mul_left _ (le_trans hle htot)

/-! ## The substituted polynomial -/

/-- The reciprocal substitution of a differential polynomial: jet variable `yⱼ` is replaced by the
reciprocal numerator `Aⱼ` and the whole monomial is balanced with powers of `g` so that a single
factor `g^{(n+1)·deg P}` clears every denominator.  Slot `0` is the point variable, slot `i+1` is
`g⁽ⁱ⁾`. -/
def recipSub (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) : MvPolynomial (Fin (n + 3)) ℂ :=
  ∑ α ∈ P.support, C (P.coeff α) * X 0 ^ α 0 *
    (∏ j : Fin (n + 1), (rename Fin.succ (recipNum n (j : ℕ))) ^ α j.succ) *
    X (Fin.succ (0 : Fin (n + 2))) ^ (recipBound n P - recipWeight n α)

/-! ## The evaluation law -/

/-- **The reciprocal substitution computes the reciprocal relation.**  Wherever `f·g = 1`, the
substituted polynomial evaluated on the jets of `g` is the original polynomial evaluated on the
jets of `f`, times the clearing power of `g`. -/
theorem eval_recipSub (n : ℕ) {g f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hgd : ∀ k : ℕ, ∀ z ∈ U, HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k + 1) g z) z)
    (hfd : ∀ k : ℕ, ∀ z ∈ U, HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f z) z)
    (hinv : ∀ z ∈ U, f z * g z = 1)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {z : ℂ} (hz : z ∈ U) :
    eval (Fin.cons z (fun i : Fin (n + 2) => iteratedDeriv (i : ℕ) g z)) (recipSub n P)
      = eval (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)) P
          * g z ^ recipBound n P := by
  classical
  have hcomp : (Fin.cons z (fun i : Fin (n + 2) => iteratedDeriv (i : ℕ) g z) : Fin (n + 3) → ℂ)
      ∘ Fin.succ = fun i : Fin (n + 2) => iteratedDeriv (i : ℕ) g z := by
    funext i
    simp
  have hA : ∀ j : Fin (n + 1),
      eval (Fin.cons z (fun i : Fin (n + 2) => iteratedDeriv (i : ℕ) g z))
          (rename Fin.succ (recipNum n (j : ℕ)))
        = iteratedDeriv (j : ℕ) f z * g z ^ ((j : ℕ) + 1) := by
    intro j
    rw [eval_rename, hcomp]
    exact (recipNum_eval n hU hgd hfd hinv (j : ℕ) (Nat.lt_succ_iff.mp j.isLt) z hz).symm
  have hzero : (Fin.cons z (fun i : Fin (n + 2) => iteratedDeriv (i : ℕ) g z) : Fin (n + 3) → ℂ)
      0 = z := Fin.cons_zero _ _
  have hone : (Fin.cons z (fun i : Fin (n + 2) => iteratedDeriv (i : ℕ) g z) : Fin (n + 3) → ℂ)
      (Fin.succ (0 : Fin (n + 2))) = g z := by
    rw [Fin.cons_succ]
    simp
  rw [recipSub, map_sum, eval_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hw : recipWeight n α ≤ recipBound n P := recipWeight_le_recipBound n hα
  have hprodA : (∏ j : Fin (n + 1),
        eval (Fin.cons z (fun i : Fin (n + 2) => iteratedDeriv (i : ℕ) g z))
          (rename Fin.succ (recipNum n (j : ℕ))) ^ α j.succ)
      = (∏ j : Fin (n + 1), iteratedDeriv (j : ℕ) f z ^ α j.succ) * g z ^ recipWeight n α := by
    rw [recipWeight, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hA j, mul_pow, ← pow_mul]
  have hvfprod : (∏ i : Fin (n + 2),
        (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) : Fin (n + 2) → ℂ) i ^ α i)
      = z ^ α 0 * ∏ j : Fin (n + 1), iteratedDeriv (j : ℕ) f z ^ α j.succ := by
    rw [Fin.prod_univ_succ]
    simp
  simp only [map_mul, map_pow, map_prod, eval_C, eval_X, hzero, hone]
  rw [hprodA, hvfprod]
  have hpow : g z ^ recipWeight n α * g z ^ (recipBound n P - recipWeight n α)
      = g z ^ recipBound n P := by
    rw [← pow_add]
    congr 1
    omega
  calc coeff α P * z ^ α 0
        * ((∏ j : Fin (n + 1), iteratedDeriv (j : ℕ) f z ^ α j.succ) * g z ^ recipWeight n α)
        * g z ^ (recipBound n P - recipWeight n α)
      = coeff α P * (z ^ α 0 * ∏ j : Fin (n + 1), iteratedDeriv (j : ℕ) f z ^ α j.succ)
        * (g z ^ recipWeight n α * g z ^ (recipBound n P - recipWeight n α)) := by ring
    _ = coeff α P * (z ^ α 0 * ∏ j : Fin (n + 1), iteratedDeriv (j : ℕ) f z ^ α j.succ)
        * g z ^ recipBound n P := by rw [hpow]

end

end GaloisForLFunctions.HTGeometry
