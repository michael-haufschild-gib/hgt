import Mathlib

/-!
# The moment functional and Hankel positivity

Foundations of the Hamburger moment problem, absent from mathlib.  Given a real moment sequence
`s : ℕ → ℝ`, the **moment functional** `momentFunctional s` sends a polynomial `p = ∑ₖ aₖ Xᵏ` to
`∑ₖ aₖ sₖ`.  It is `ℝ`-linear, and — this is the load-bearing fact of the moment-fiber and
Nevanlinna-parametrization cards (`indeterminate-moment-fiber-maximal-translation-ht`,
`nevanlinna-boundary-bauer-retract-maximal-ht`) — it is **positive on squares** whenever `s` has a
representing measure:

`sₖ = ∫ xᵏ dμ  ⟹  momentFunctional s (p²) = ∫ (eval x p)² dμ ≥ 0`.

Positivity on squares is exactly positive-semidefiniteness of the Hankel form `(sᵢ₊ⱼ)`, the
necessary condition in Hamburger's solvability theorem and the constraint that carves out the
moment-fiber of an indeterminate sequence.  This file builds the functional, its linearity, the
bridge to a representing measure, the moment bilinear form `L(p·q) = ∫ (eval p)(eval q) dμ`, and the
Hankel positive-semidefiniteness corollary.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

/-- The **moment functional** of a real sequence `s`: `p = ∑ₖ aₖ Xᵏ ↦ ∑ₖ aₖ sₖ`. -/
noncomputable def momentFunctional (s : ℕ → ℝ) (p : Polynomial ℝ) : ℝ :=
  p.sum (fun k a => a * s k)

@[simp] theorem momentFunctional_zero (s : ℕ → ℝ) : momentFunctional s 0 = 0 := by
  simp [momentFunctional]

/-- Additivity of the moment functional. -/
theorem momentFunctional_add (s : ℕ → ℝ) (p q : Polynomial ℝ) :
    momentFunctional s (p + q) = momentFunctional s p + momentFunctional s q := by
  refine Polynomial.sum_add_index p q _ (fun i => by ring) (fun a b₁ b₂ => by ring)

/-- Homogeneity of the moment functional under scalar multiplication. -/
theorem momentFunctional_smul (s : ℕ → ℝ) (c : ℝ) (p : Polynomial ℝ) :
    momentFunctional s (c • p) = c * momentFunctional s p := by
  rw [momentFunctional, Polynomial.sum_smul_index _ _ _ (fun i => by ring)]
  rw [momentFunctional, Polynomial.sum_def, Polynomial.sum_def, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- Expansion of the moment functional as a support sum. -/
theorem momentFunctional_eq_support_sum (s : ℕ → ℝ) (p : Polynomial ℝ) :
    momentFunctional s p = ∑ k ∈ p.support, p.coeff k * s k := by
  rw [momentFunctional, Polynomial.sum_def]

/-- **Representing-measure bridge.**  If `s` is the moment sequence of a measure `μ` whose monomials
are all integrable, the moment functional is integration of the evaluated polynomial. -/
theorem momentFunctional_eq_integral {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ) (p : Polynomial ℝ) :
    momentFunctional s p = ∫ x, Polynomial.eval x p ∂μ := by
  have hev : ∫ x, Polynomial.eval x p ∂μ
      = ∫ x, ∑ k ∈ p.support, p.coeff k * x ^ k ∂μ := by
    refine integral_congr_ae (ae_of_all μ (fun x => ?_))
    show Polynomial.eval x p = ∑ k ∈ p.support, p.coeff k * x ^ k
    rw [eval_eq_sum, Polynomial.sum_def]
  rw [hev, integral_finsetSum p.support (fun k _ => (hint k).const_mul (p.coeff k)),
    momentFunctional_eq_support_sum]
  exact Finset.sum_congr rfl (fun k _ => by rw [integral_const_mul, hs k])

/-- **Moment bilinear form.**  Under a representing measure, `L(p·q)` is the `L²(μ)` inner product of
the evaluated polynomials — the Gram form of the moment sequence. -/
theorem momentFunctional_mul_eq_integral {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ) (p q : Polynomial ℝ) :
    momentFunctional s (p * q) = ∫ x, Polynomial.eval x p * Polynomial.eval x q ∂μ := by
  rw [momentFunctional_eq_integral s hs hint (p * q)]
  refine integral_congr_ae (ae_of_all μ (fun x => ?_))
  show Polynomial.eval x (p * q) = Polynomial.eval x p * Polynomial.eval x q
  rw [eval_mul]

/-- **Hankel positive-semidefiniteness.**  A moment sequence with a representing measure is positive
on squares: `momentFunctional s (p²) ≥ 0`.  This is positive-semidefiniteness of the Hankel matrix
`(sᵢ₊ⱼ)` and the necessary condition of Hamburger's theorem. -/
theorem momentFunctional_pow_two_nonneg {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ) (p : Polynomial ℝ) :
    0 ≤ momentFunctional s (p ^ 2) := by
  rw [momentFunctional_eq_integral s hs hint (p ^ 2)]
  have hcongr : ∫ x, Polynomial.eval x (p ^ 2) ∂μ = ∫ x, (Polynomial.eval x p) ^ 2 ∂μ := by
    refine integral_congr_ae (ae_of_all μ (fun x => ?_))
    show Polynomial.eval x (p ^ 2) = (Polynomial.eval x p) ^ 2
    rw [eval_pow]
  rw [hcongr]
  exact integral_nonneg (fun x => sq_nonneg _)

/-- Every evaluated polynomial is integrable against a measure whose monomials are integrable. -/
theorem integrable_eval {μ : Measure ℝ} (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ)
    (q : Polynomial ℝ) : Integrable (fun x : ℝ => Polynomial.eval x q) μ := by
  have hrw : (fun x : ℝ => Polynomial.eval x q)
      = fun x => ∑ k ∈ q.support, q.coeff k * x ^ k := by
    funext x; rw [eval_eq_sum, Polynomial.sum_def]
  rw [hrw]
  exact integrable_finsetSum q.support (fun k _ => (hint k).const_mul _)

/-- The value of the Hankel form on `p²` as an `L²(μ)` norm-square. -/
theorem momentFunctional_pow_two_eq_integral_sq {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ) (p : Polynomial ℝ) :
    momentFunctional s (p ^ 2) = ∫ x, (Polynomial.eval x p) ^ 2 ∂μ := by
  rw [momentFunctional_eq_integral s hs hint (p ^ 2)]
  refine integral_congr_ae (ae_of_all μ (fun x => ?_))
  show Polynomial.eval x (p ^ 2) = (Polynomial.eval x p) ^ 2
  rw [eval_pow]

/-- **Strict Hankel definiteness (nondegeneracy).**  When the representing measure charges every
cofinite set — i.e. is not supported on any finite set, the case of an indeterminate/infinitely
supported moment problem — the Hankel form is strictly positive-definite: `momentFunctional s (p²) = 0`
forces `p = 0`.  A vanishing norm-square makes `eval · p` zero almost everywhere, so it vanishes on a
cofinite set, but a nonzero polynomial has only finitely many roots. -/
theorem momentFunctional_pow_two_eq_zero {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ)
    (hμinf : ∀ F : Finset ℝ, 0 < μ {x : ℝ | x ∉ F})
    (p : Polynomial ℝ) (hp : momentFunctional s (p ^ 2) = 0) : p = 0 := by
  by_contra hpne
  rw [momentFunctional_pow_two_eq_integral_sq s hs hint] at hp
  have hnonneg : 0 ≤ᵐ[μ] fun x : ℝ => (Polynomial.eval x p) ^ 2 :=
    ae_of_all μ (fun x => sq_nonneg _)
  have hintp2 : Integrable (fun x : ℝ => (Polynomial.eval x p) ^ 2) μ := by
    refine (integrable_eval hint (p ^ 2)).congr (ae_of_all μ (fun x => ?_))
    show Polynomial.eval x (p ^ 2) = (Polynomial.eval x p) ^ 2
    rw [eval_pow]
  have hae : (fun x : ℝ => (Polynomial.eval x p) ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hintp2).mp hp
  have hae' : μ {x : ℝ | ¬ (Polynomial.eval x p) ^ 2 = 0} = 0 := by
    have h2 : ∀ᵐ x ∂μ, (Polynomial.eval x p) ^ 2 = 0 := by
      filter_upwards [hae] with x hx; simpa using hx
    rwa [ae_iff] at h2
  set R : Finset ℝ := p.roots.toFinset with hR
  have hsub : {x : ℝ | x ∉ R} ⊆ {x : ℝ | ¬ (Polynomial.eval x p) ^ 2 = 0} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have hev : Polynomial.eval x p ≠ 0 := fun he =>
      hx (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hpne).mpr he))
    exact pow_ne_zero 2 hev
  have hle : μ {x : ℝ | x ∉ R} ≤ 0 := by rw [← hae']; exact measure_mono hsub
  exact absurd (le_antisymm hle zero_le') (ne_of_gt (hμinf R))

/-- **Cauchy–Schwarz for the moment functional.**  The Hankel form is a positive-semidefinite inner
product on polynomials: `L_s(p·q)² ≤ L_s(p²)·L_s(q²)` whenever `s` has a representing measure.  Proved
purely from square-positivity (`momentFunctional_pow_two_nonneg`) via the nonnegative quadratic
`t ↦ L_s((p + t·q)²)` and its discriminant. -/
theorem momentFunctional_cauchy_schwarz {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ) (p q : Polynomial ℝ) :
    (momentFunctional s (p * q)) ^ 2
      ≤ momentFunctional s (p ^ 2) * momentFunctional s (q ^ 2) := by
  have hquad : ∀ x : ℝ, 0 ≤ (momentFunctional s (q ^ 2)) * (x * x)
      + (2 * momentFunctional s (p * q)) * x + momentFunctional s (p ^ 2) := by
    intro x
    have hpoly : (p + x • q) ^ 2 = p ^ 2 + (2 * x) • (p * q) + (x ^ 2) • q ^ 2 := by
      simp only [Polynomial.smul_eq_C_mul, map_mul, map_pow, map_ofNat]; ring
    have hexp : momentFunctional s ((p + x • q) ^ 2)
        = (momentFunctional s (q ^ 2)) * (x * x)
          + (2 * momentFunctional s (p * q)) * x + momentFunctional s (p ^ 2) := by
      rw [hpoly, momentFunctional_add, momentFunctional_add, momentFunctional_smul,
        momentFunctional_smul]
      ring
    rw [← hexp]
    exact momentFunctional_pow_two_nonneg s hs hint (p + x • q)
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith [hd]

/-- Finite-sum linearity of the moment functional. -/
theorem momentFunctional_sum (s : ℕ → ℝ) {ι : Type*} (t : Finset ι) (g : ι → Polynomial ℝ) :
    momentFunctional s (∑ i ∈ t, g i) = ∑ i ∈ t, momentFunctional s (g i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, momentFunctional_add, ih, Finset.sum_insert ha]

/-- The moment functional sends the monomial `Xᵏ` to the moment `sₖ`. -/
theorem momentFunctional_X_pow (s : ℕ → ℝ) (k : ℕ) :
    momentFunctional s ((X : Polynomial ℝ) ^ k) = s k := by
  rw [momentFunctional_eq_support_sum, Polynomial.support_X_pow one_ne_zero, Finset.sum_singleton,
    Polynomial.coeff_X_pow, if_pos rfl, one_mul]

/-- **Hankel matrix positive-semidefiniteness (matrix form).**  A moment sequence with a representing
measure has positive-semidefinite Hankel matrix `(sᵢ₊ⱼ)`: for every real vector `v`,
`∑ᵢⱼ vᵢ vⱼ s_{i+j} ≥ 0`.  This is the quadratic form `L_s(p²)` for `p = ∑ᵢ vᵢ Xⁱ`, so nonnegativity
is exactly square-positivity of the moment functional. -/
theorem hankelForm_nonneg {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ) {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, v i * v j * s ((i : ℕ) + (j : ℕ)) := by
  set p : Polynomial ℝ := ∑ i : Fin n, v i • X ^ (i : ℕ) with hp
  have hpsq : momentFunctional s (p ^ 2)
      = ∑ i : Fin n, ∑ j : Fin n, v i * v j * s ((i : ℕ) + (j : ℕ)) := by
    rw [sq, hp, Finset.sum_mul_sum, momentFunctional_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [momentFunctional_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show (v i • X ^ (i : ℕ)) * (v j • X ^ (j : ℕ))
        = (v i * v j) • X ^ ((i : ℕ) + (j : ℕ)) from by rw [smul_mul_smul_comm, ← pow_add],
      momentFunctional_smul, momentFunctional_X_pow]
  rw [← hpsq]
  exact momentFunctional_pow_two_nonneg s hs hint p

end HTGeometry
