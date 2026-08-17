import GaloisForLFunctions.HTGeometry.ComplexExpUnfolding

/-!
# Sums of Hermitian squares force the unfolding to be nonnegative

A sum of Hermitian squares `∑_l G_l G_l^*` is nonnegative on the real line for a trivial reason: on
`ℝ` it is `∑_l |G_l|²`.  The point of this file is that the reason is stronger than it looks.  A
Hermitian square is built from characters, and characters unfold: replacing `e^{μ t}` by
`e^{(Re μ) t} e^{i (Im μ) u}` turns `∑_l |G_l|²` into a nonnegative function of **two** independent
real variables.  Since the unfolding of an exponential polynomial depends only on the function, the
conclusion is intrinsic:

> if `f` is a sum of Hermitian squares of exponential polynomials, its unfolding is nonnegative on
> all of `ℝ × ℝ`, not merely on the diagonal.

Growth and phase are decoupled by any sum-of-squares certificate.  That is exactly the obstruction
that a Fejér–Riesz theorem for mixed exponents would have to overcome.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- `f`, presented by exponents `lam` with coefficients `w`, is a sum of Hermitian squares of the
exponential polynomials with exponents `μ` and coefficient rows `v`. -/
def IsHermitianSOS {n L m : ℕ} (w lam : Fin n → ℂ) (v : Fin L → Fin m → ℂ) (μ : Fin m → ℂ) :
    Prop :=
  ∀ t : ℝ, ∑ i, w i * Complex.exp (lam i * t)
    = ∑ l, ((Complex.normSq (∑ j, v l j * Complex.exp (μ j * t)) : ℝ) : ℂ)

/-- The unfolding of an exponential polynomial. -/
noncomputable def unfoldSum {n : ℕ} (w lam : Fin n → ℂ) (t u : ℝ) : ℂ :=
  ∑ i, w i * unfoldChar (lam i) t u

theorem unfoldSum_diag {n : ℕ} (w lam : Fin n → ℂ) (t : ℝ) :
    unfoldSum w lam t t = ∑ i, w i * Complex.exp (lam i * t) := by
  rw [unfoldSum]
  exact Finset.sum_congr rfl (fun i _ => by rw [unfoldChar_diag])

/-- Transfer of an identity between exponential polynomials to their unfoldings. -/
theorem unfold_eq_of_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {c : ι → ℂ} {ν : ι → ℂ}
    {d : κ → ℂ} {ρ : κ → ℂ}
    (h : ∀ t : ℝ, ∑ i, c i * Complex.exp (ν i * t) = ∑ j, d j * Complex.exp (ρ j * t)) :
    ∀ t u : ℝ, ∑ i, c i * unfoldChar (ν i) t u = ∑ j, d j * unfoldChar (ρ j) t u := by
  classical
  set C : ι ⊕ κ → ℂ := fun x => Sum.elim c (fun j => -(d j)) x with hC
  set N : ι ⊕ κ → ℂ := fun x => Sum.elim ν ρ x with hN
  have hzero : ∀ t : ℝ, ∑ x : ι ⊕ κ, C x * Complex.exp (N x * t) = 0 := by
    intro t
    rw [Fintype.sum_sum_type]
    simp only [hC, hN, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, h t]
    ring
  have hunf := unfold_eq_zero_of_eq_zero (S := (Finset.univ : Finset (ι ⊕ κ))) hzero
  intro t u
  have := hunf t u
  rw [Fintype.sum_sum_type] at this
  simp only [hC, hN, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at this
  linear_combination this

/-- The Gram expansion of a sum of Hermitian squares, for any character map. -/
theorem gram_expand {m L : ℕ} (v : Fin L → Fin m → ℂ) (μ : Fin m → ℂ) (χ : ℂ → ℂ)
    (hmul : ∀ a b, χ (a + b) = χ a * χ b)
    (hconj : ∀ a, (starRingEnd ℂ) (χ a) = χ ((starRingEnd ℂ) a)) :
    ∑ l, ((Complex.normSq (∑ j, v l j * χ (μ j)) : ℝ) : ℂ)
      = ∑ p : Fin m × Fin m, (∑ l, v l p.1 * (starRingEnd ℂ) (v l p.2))
          * χ (μ p.1 + (starRingEnd ℂ) (μ p.2)) := by
  have hone : ∀ l : Fin L, ((Complex.normSq (∑ j, v l j * χ (μ j)) : ℝ) : ℂ)
      = ∑ p : Fin m × Fin m, v l p.1 * (starRingEnd ℂ) (v l p.2)
          * χ (μ p.1 + (starRingEnd ℂ) (μ p.2)) := by
    intro l
    rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [map_mul, hconj, hmul]
    ring
  calc ∑ l, ((Complex.normSq (∑ j, v l j * χ (μ j)) : ℝ) : ℂ)
      = ∑ l, ∑ p : Fin m × Fin m, v l p.1 * (starRingEnd ℂ) (v l p.2)
          * χ (μ p.1 + (starRingEnd ℂ) (μ p.2)) := Finset.sum_congr rfl (fun l _ => hone l)
    _ = ∑ p : Fin m × Fin m, ∑ l, v l p.1 * (starRingEnd ℂ) (v l p.2)
          * χ (μ p.1 + (starRingEnd ℂ) (μ p.2)) := Finset.sum_comm
    _ = ∑ p : Fin m × Fin m, (∑ l, v l p.1 * (starRingEnd ℂ) (v l p.2))
          * χ (μ p.1 + (starRingEnd ℂ) (μ p.2)) :=
        Finset.sum_congr rfl (fun p _ => by rw [← Finset.sum_mul])

/-- **The unfolding obstruction.**  If an exponential polynomial is a sum of Hermitian squares, its
unfolding is nonnegative on the whole plane. -/
theorem unfoldSum_nonneg_of_isHermitianSOS {n L m : ℕ} (w lam : Fin n → ℂ)
    (v : Fin L → Fin m → ℂ) (μ : Fin m → ℂ) (h : IsHermitianSOS w lam v μ) (t u : ℝ) :
    0 ≤ (unfoldSum w lam t u).re := by
  -- rewrite the hypothesis as an identity between two exponential polynomials
  have hexp : ∀ s : ℝ, ∑ i, w i * Complex.exp (lam i * s)
      = ∑ p : Fin m × Fin m, (∑ l, v l p.1 * (starRingEnd ℂ) (v l p.2))
          * Complex.exp ((μ p.1 + (starRingEnd ℂ) (μ p.2)) * s) := by
    intro s
    rw [h s]
    refine gram_expand v μ (fun a => Complex.exp (a * s)) (fun a b => ?_) (fun a => ?_)
    · rw [← Complex.exp_add]; congr 1; ring
    · rw [← Complex.exp_conj]; congr 1; simp
  have hunf := unfold_eq_of_eq hexp t u
  rw [unfoldSum, hunf]
  have hgram := gram_expand v μ (fun a => unfoldChar a t u)
    (fun a b => unfoldChar_add a b t u) (fun a => unfoldChar_conj a t u)
  rw [← hgram, Complex.re_sum]
  refine Finset.sum_nonneg (fun l _ => ?_)
  rw [Complex.ofReal_re]
  exact Complex.normSq_nonneg _

end GaloisForLFunctions.HTGeometry
