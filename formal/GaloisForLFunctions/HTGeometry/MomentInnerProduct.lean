import GaloisForLFunctions.HTGeometry.MomentHankelStrict

/-!
# The moment inner product on real polynomials

`MomentFunctionalPositivity` supplies the moment functional `L_s` and its square positivity.  This
module turns that functional into the bilinear form

`⟪p, q⟫_s = L_s (p * q)`

and isolates the property that drives the whole orthogonal-polynomial theory of a Hamburger moment
sequence: *positive definiteness*, `p ≠ 0 → 0 < ⟪p, p⟫_s`.

`PositiveMomentForm s` bundles that property, and `positiveMomentForm_of_infiniteSupport`
constructs it from any representing measure charging the complement of every finite set — the
hypothesis already used for strict Hankel positivity.  Positive definiteness is exactly the input
required to run Gram--Schmidt on the monomial basis, so this module is the algebraic base for
orthonormal polynomials and their three-term recurrence.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

/-- The **moment inner product** attached to a real sequence `s`. -/
noncomputable def momentInner (s : ℕ → ℝ) (p q : Polynomial ℝ) : ℝ :=
  momentFunctional s (p * q)

theorem momentInner_def (s : ℕ → ℝ) (p q : Polynomial ℝ) :
    momentInner s p q = momentFunctional s (p * q) := rfl

/-- The moment form is symmetric. -/
theorem momentInner_comm (s : ℕ → ℝ) (p q : Polynomial ℝ) :
    momentInner s p q = momentInner s q p := by
  simp [momentInner, mul_comm]

/-- On the diagonal the moment form is the square functional. -/
theorem momentInner_self (s : ℕ → ℝ) (p : Polynomial ℝ) :
    momentInner s p p = momentFunctional s (p ^ (2 : ℕ)) := by
  simp [momentInner, pow_two]

@[simp] theorem momentInner_zero_left (s : ℕ → ℝ) (q : Polynomial ℝ) :
    momentInner s 0 q = 0 := by
  simp [momentInner]

@[simp] theorem momentInner_zero_right (s : ℕ → ℝ) (p : Polynomial ℝ) :
    momentInner s p 0 = 0 := by
  simp [momentInner]

theorem momentInner_add_left (s : ℕ → ℝ) (p q r : Polynomial ℝ) :
    momentInner s (p + q) r = momentInner s p r + momentInner s q r := by
  simp [momentInner, add_mul, momentFunctional_add]

theorem momentInner_add_right (s : ℕ → ℝ) (p q r : Polynomial ℝ) :
    momentInner s p (q + r) = momentInner s p q + momentInner s p r := by
  simp [momentInner, mul_add, momentFunctional_add]

theorem momentInner_smul_left (s : ℕ → ℝ) (c : ℝ) (p q : Polynomial ℝ) :
    momentInner s (c • p) q = c * momentInner s p q := by
  simp [momentInner, momentFunctional_smul]

theorem momentInner_smul_right (s : ℕ → ℝ) (c : ℝ) (p q : Polynomial ℝ) :
    momentInner s p (c • q) = c * momentInner s p q := by
  rw [momentInner_comm, momentInner_smul_left, momentInner_comm]

theorem momentInner_sum_left (s : ℕ → ℝ) {ι : Type*} (t : Finset ι) (g : ι → Polynomial ℝ)
    (q : Polynomial ℝ) :
    momentInner s (∑ i ∈ t, g i) q = ∑ i ∈ t, momentInner s (g i) q := by
  simp only [momentInner, Finset.sum_mul]
  exact momentFunctional_sum s t (fun i => g i * q)

theorem momentInner_sum_right (s : ℕ → ℝ) {ι : Type*} (t : Finset ι) (g : ι → Polynomial ℝ)
    (p : Polynomial ℝ) :
    momentInner s p (∑ i ∈ t, g i) = ∑ i ∈ t, momentInner s p (g i) := by
  rw [momentInner_comm, momentInner_sum_left]
  exact Finset.sum_congr rfl fun i _ => momentInner_comm s (g i) p

/-- Multiplication by `X` is symmetric for the moment form: the Jacobi/Hankel symmetry that makes
the three-term recurrence possible. -/
theorem momentInner_X_mul (s : ℕ → ℝ) (p q : Polynomial ℝ) :
    momentInner s (Polynomial.X * p) q = momentInner s p (Polynomial.X * q) := by
  simp only [momentInner]
  ring_nf

/-! ## Positive definiteness -/

/-- A moment sequence whose form is positive definite on nonzero polynomials.  This is exactly the
input Gram--Schmidt needs, and it holds for every indeterminate Hamburger sequence. -/
structure PositiveMomentForm (s : ℕ → ℝ) : Prop where
  pos_of_ne_zero : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < momentInner s p p

namespace PositiveMomentForm

variable {s : ℕ → ℝ} (h : PositiveMomentForm s)
include h

theorem nonneg (p : Polynomial ℝ) : 0 ≤ momentInner s p p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · exact (h.pos_of_ne_zero p hp).le

theorem eq_zero_of_self_eq_zero {p : Polynomial ℝ} (hp : momentInner s p p = 0) : p = 0 := by
  by_contra hne
  exact absurd hp (ne_of_gt (h.pos_of_ne_zero p hne))

theorem self_eq_zero_iff (p : Polynomial ℝ) : momentInner s p p = 0 ↔ p = 0 :=
  ⟨h.eq_zero_of_self_eq_zero, fun hp => by simp [hp]⟩

theorem self_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) : momentInner s p p ≠ 0 :=
  ne_of_gt (h.pos_of_ne_zero p hp)

end PositiveMomentForm

/-- A moment form is positive definite on every nonzero polynomial exactly when every finite
Hankel matrix of its coefficient sequence is positive definite.  This is the basis-free/finite-
coordinate bridge used by Hamburger representation arguments. -/
theorem positiveMomentForm_iff_momentHankelMatrix_posDef {s : ℕ → ℝ} :
    PositiveMomentForm s ↔ ∀ n : ℕ, (momentHankelMatrix s n).PosDef := by
  constructor
  · intro h n
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨momentHankelMatrix_isHermitian s n, ?_⟩
    intro a ha
    rw [star_trivial, dotProduct_mulVec_momentHankelMatrix, ← momentInner_self]
    apply h.pos_of_ne_zero
    intro hp
    apply ha
    apply Polynomial.injective_ofFn n
    rw [hp, Polynomial.ofFn_zero]
  · intro h
    refine ⟨fun p hp => ?_⟩
    let n := p.natDegree + 1
    let a : Fin n → ℝ := Polynomial.toFn n p
    have hpof : Polynomial.ofFn n a = p := by
      exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
    have ha : a ≠ 0 := by
      intro ha
      apply hp
      rw [← hpof, ha, Polynomial.ofFn_zero]
    have hquad := (h n).dotProduct_mulVec_pos ha
    rw [star_trivial, dotProduct_mulVec_momentHankelMatrix, hpof,
      ← momentInner_self] at hquad
    exact hquad

/-- **Positive definiteness from an infinitely supported representing measure.**  This is the
hypothesis already used for strict Hankel positivity, so every moment sequence carried by a
measure with infinite support generates a genuine inner product on real polynomials. -/
theorem positiveMomentForm_of_infiniteSupport {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ)
    (hμinf : ∀ F : Finset ℝ, 0 < μ {x : ℝ | x ∉ F}) :
    PositiveMomentForm s := by
  refine ⟨fun p hp => ?_⟩
  rw [momentInner_self]
  have hnonneg := momentFunctional_pow_two_nonneg s hs hint p
  refine lt_of_le_of_ne hnonneg (Ne.symm ?_)
  intro hzero
  exact hp (momentFunctional_pow_two_eq_zero s hs hint hμinf p hzero)

/-- Cauchy--Schwarz for the moment form. -/
theorem momentInner_sq_le {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ) (p q : Polynomial ℝ) :
    (momentInner s p q) ^ (2 : ℕ) ≤ momentInner s p p * momentInner s q q := by
  rw [momentInner_self, momentInner_self, momentInner_def]
  exact momentFunctional_cauchy_schwarz s hs hint p q

/-! ## Orthogonality -/

/-- Orthogonality of two polynomials for the moment form. -/
def MomentOrthogonal (s : ℕ → ℝ) (p q : Polynomial ℝ) : Prop :=
  momentInner s p q = 0

/-- A family orthogonal for a positive definite moment form is linearly independent: the Gram
matrix argument that makes Gram--Schmidt terminate with nonzero output at every degree. -/
theorem eq_zero_of_forall_momentOrthogonal {s : ℕ → ℝ} (h : PositiveMomentForm s)
    {ι : Type*} (t : Finset ι) (g : ι → Polynomial ℝ) (c : ι → ℝ)
    (hortho : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → momentInner s (g i) (g j) = 0)
    (hne : ∀ i ∈ t, g i ≠ 0)
    (hzero : ∑ i ∈ t, c i • g i = 0) :
    ∀ i ∈ t, c i = 0 := by
  intro i hi
  have hexp : momentInner s (∑ j ∈ t, c j • g j) (g i) = c i * momentInner s (g i) (g i) := by
    rw [momentInner_sum_left]
    rw [Finset.sum_eq_single i]
    · rw [momentInner_smul_left]
    · intro j hj hji
      rw [momentInner_smul_left, hortho j hj i hi hji, mul_zero]
    · intro hni
      exact absurd hi hni
  rw [hzero, momentInner_zero_left] at hexp
  have hgi : momentInner s (g i) (g i) ≠ 0 := h.self_ne_zero (hne i hi)
  exact (mul_eq_zero.mp hexp.symm).resolve_right hgi

end HTGeometry
