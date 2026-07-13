import GaloisForLFunctions.HTGeometry.GramDeterminantDistance
import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import GaloisForLFunctions.HTGeometry.ThermalKrylovMoments

/-!
# Exact thermal Krylov determinant values

The even thermal moment matrix is not merely positive: it is exactly the Gram matrix of the
squared-gap Krylov vectors

`vₙ(a,b) = sqrt(intensity a b) * ((energy a - energy b)²)ⁿ`.

Consequently its determinant is the product of the squared Gram--Schmidt residual norms.  This is
the determinant-value identity underlying Lanczos reconstruction and the statement that the
finite Krylov chain has not terminated.
-/

open scoped BigOperators InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-- For a finite complex Hilbert family, nontermination of every Gram--Schmidt residual is
equivalent to linear independence.  This converts the algebraic hypothesis used by strict Gram
consumers into the residual-value interface used by Krylov/Lanczos physics. -/
theorem linearIndependent_iff_gramSchmidt_ne_zero
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {n : ℕ} (v : Fin n → F) :
    LinearIndependent ℂ v ↔
      ∀ k : Fin n, InnerProductSpace.gramSchmidt ℂ v k ≠ 0 := by
  constructor
  · intro h k
    exact InnerProductSpace.gramSchmidt_ne_zero k h
  · intro h
    have hgs : LinearIndependent ℂ (InnerProductSpace.gramSchmidt ℂ v) :=
      linearIndependent_of_ne_zero_of_inner_eq_zero h fun i j hij =>
        InnerProductSpace.gramSchmidt_orthogonal ℂ v hij
    rw [linearIndependent_iff_card_eq_finrank_span]
    rw [Set.finrank, ← InnerProductSpace.span_gramSchmidt]
    exact linearIndependent_iff_card_eq_finrank_span.mp hgs

end GaloisForLFunctions.HTGeometry

namespace HTGeometry

noncomputable section

/-- Iterating the normalized Lanczos recurrence expresses the `k`-th squared residual as the
initial norm times the product of the first `k` squared off-diagonal coefficients. -/
theorem krylovResidualNormSq_eq_initial_mul_lanczosProduct
    (μ0 : ℝ) (b residualSq : ℕ → ℝ)
    (hzero : residualSq 0 = μ0)
    (hrec : ∀ k, residualSq (k + 1) = residualSq k * b (k + 1) ^ 2)
    (k : ℕ) :
    residualSq k = μ0 * ∏ j ∈ Finset.Ico 1 (k + 1), b j ^ 2 := by
  induction k with
  | zero => simp [hzero]
  | succ k ih =>
      rw [hrec k, ih]
      conv_rhs => rw [Finset.prod_Ico_succ_top (show 1 ≤ k + 1 by omega)]
      ring

/-- **Correct normalized Lanczos determinant scaling.**  If squared residual norms satisfy
`r₀ = μ₀` and `rₖ₊₁ = rₖ bₖ₊₁²`, then their determinant product is

`μ₀ᴺ ∏_{1 ≤ j < N} bⱼ^(2(N-j))`.

Thus earlier Lanczos coefficients occur with larger multiplicity; the formula in which every
coefficient occurs only once has the wrong scaling. -/
theorem lanczosDeterminantScaling
    (μ0 : ℝ) (b residualSq : ℕ → ℝ)
    (hzero : residualSq 0 = μ0)
    (hrec : ∀ k, residualSq (k + 1) = residualSq k * b (k + 1) ^ 2)
    (N : ℕ) :
    (∏ k ∈ Finset.range N, residualSq k) =
      μ0 ^ N * ∏ j ∈ Finset.Ico 1 N, b j ^ (2 * (N - j)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_range_succ, ih,
        krylovResidualNormSq_eq_initial_mul_lanczosProduct μ0 b residualSq hzero hrec N]
      by_cases hN : N = 0
      · subst N
        simp
      · have h1N : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
        rw [Finset.prod_Ico_succ_top h1N]
        rw [Finset.prod_Ico_succ_top h1N]
        have hprod :
            (∏ j ∈ Finset.Ico 1 N, b j ^ (2 * (N - j))) *
                (∏ j ∈ Finset.Ico 1 N, b j ^ 2) =
              ∏ j ∈ Finset.Ico 1 N, b j ^ (2 * (N + 1 - j)) := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro j hj
          rw [← pow_add]
          congr 1
          have hjN : j < N := (Finset.mem_Ico.mp hj).2
          omega
        rw [← hprod]
        have hlast : 2 * (N + 1 - N) = 2 := by omega
        rw [hlast]
        rw [pow_succ]
        ring

/-- Any complex reflected Gram realization gives an exact real Hankel determinant value as the
product of the squared Gram--Schmidt residual norms.  This is the generic value-level upgrade of
the existing strict-positivity consumer. -/
theorem det_momentHankelMatrix_eq_prod_complexKrylovResidualNormSq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (m : ℕ → ℝ) (v : ℕ → F)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = (m (i + j) : ℂ))
    (n : ℕ) (hli : LinearIndependent ℂ (fun i : Fin n => v (i : ℕ))) :
    (momentHankelMatrix m n).det =
      ∏ k : Fin n, ‖InnerProductSpace.gramSchmidt ℂ
        (fun i : Fin n => v (i : ℕ)) k‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_prod]
  change (algebraMap ℝ ℂ) (momentHankelMatrix m n).det = _
  rw [RingHom.map_det]
  have hmatrix : (algebraMap ℝ ℂ).mapMatrix (momentHankelMatrix m n) =
      Matrix.gram ℂ (fun i : Fin n => v (i : ℕ)) := by
    ext i j
    change (m ((i : ℕ) + (j : ℕ)) : ℂ) = inner ℂ (v (i : ℕ)) (v (j : ℕ))
    exact (hgram _ _).symm
  rw [hmatrix, GaloisForLFunctions.HTGeometry.det_gram_eq_prod _ hli]
  apply Finset.prod_congr rfl
  intro k _
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The finite complex Krylov vector whose Gram values are the even thermal gap moments. -/
def thermalKrylovVector {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ) (n : ℕ) :
    EuclideanSpace ℂ (α × α) :=
  WithLp.toLp 2 fun ab =>
    (Real.sqrt (intensity ab.1 ab.2) : ℂ) *
      (((energy ab.1 - energy ab.2) ^ 2 : ℝ) : ℂ) ^ n

/-- Exact Wightman/Krylov value relation: the inner product of squared-gap Krylov vectors is the
corresponding even Liouvillian moment. -/
theorem inner_thermalKrylovVector {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b) (i j : ℕ) :
    inner ℂ (thermalKrylovVector intensity energy i)
      (thermalKrylovVector intensity energy j) =
      (thermalEvenGapMoment intensity energy (i + j) : ℂ) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, thermalEvenGapMoment_eq,
    Complex.ofReal_sum]
  simp_rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [thermalKrylovVector, WithLp.ofLp_toLp, RCLike.inner_apply,
    map_mul, Complex.conj_ofReal, map_pow]
  push_cast
  have hsqrt : (Real.sqrt (intensity a b) : ℂ) ^ 2 = (intensity a b : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (hintensity a b)
  rw [← hsqrt, pow_add]
  ring

/-- The complexification of the thermal moment Hankel matrix is exactly the finite Krylov Gram
matrix. -/
theorem momentHankelMatrix_map_eq_thermalKrylovGram {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b) (n : ℕ) :
    (algebraMap ℝ ℂ).mapMatrix
      (momentHankelMatrix (thermalEvenGapMoment intensity energy) n) =
      Matrix.gram ℂ
        (fun i : Fin n => thermalKrylovVector intensity energy (i : ℕ)) := by
  ext i j
  change (thermalEvenGapMoment intensity energy ((i : ℕ) + (j : ℕ)) : ℂ) =
    inner ℂ (thermalKrylovVector intensity energy (i : ℕ))
      (thermalKrylovVector intensity energy (j : ℕ))
  exact (inner_thermalKrylovVector intensity energy hintensity _ _).symm

/-- Complex-cast form of the exact finite Krylov residual determinant product. -/
theorem det_thermalEvenGapMoment_eq_prod_krylovResidualNormSq_complex
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b) (n : ℕ)
    (hli : LinearIndependent ℂ
      (fun i : Fin n => thermalKrylovVector intensity energy (i : ℕ))) :
    ((momentHankelMatrix (thermalEvenGapMoment intensity energy) n).det : ℂ) =
      ∏ k : Fin n, (‖InnerProductSpace.gramSchmidt ℂ
        (fun i : Fin n => thermalKrylovVector intensity energy (i : ℕ)) k‖ ^ 2 : ℂ) := by
  change (algebraMap ℝ ℂ)
    (momentHankelMatrix (thermalEvenGapMoment intensity energy) n).det = _
  rw [RingHom.map_det, momentHankelMatrix_map_eq_thermalKrylovGram
    intensity energy hintensity]
  rw [GaloisForLFunctions.HTGeometry.det_gram_eq_prod _ hli]
  apply Finset.prod_congr rfl
  intro k _
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **Exact Lanczos/Krylov residual determinant value.** -/
theorem det_thermalEvenGapMoment_eq_prod_krylovResidualNormSq
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b) (n : ℕ)
    (hli : LinearIndependent ℂ
      (fun i : Fin n => thermalKrylovVector intensity energy (i : ℕ))) :
    (momentHankelMatrix (thermalEvenGapMoment intensity energy) n).det =
      ∏ k : Fin n, ‖InnerProductSpace.gramSchmidt ℂ
        (fun i : Fin n => thermalKrylovVector intensity energy (i : ℕ)) k‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_prod]
  simpa only [Complex.ofReal_pow] using
    det_thermalEvenGapMoment_eq_prod_krylovResidualNormSq_complex
      intensity energy hintensity n hli

/-- A directly physical nontermination premise makes the finite thermal determinant strictly
positive, without asking the caller to formulate linear independence. -/
theorem det_thermalEvenGapMoment_pos_of_krylovResidual_ne_zero
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b) (n : ℕ)
    (hresidual : ∀ k : Fin n, InnerProductSpace.gramSchmidt ℂ
      (fun i : Fin n => thermalKrylovVector intensity energy (i : ℕ)) k ≠ 0) :
    0 < (momentHankelMatrix (thermalEvenGapMoment intensity energy) n).det := by
  have hli : LinearIndependent ℂ
      (fun i : Fin n => thermalKrylovVector intensity energy (i : ℕ)) :=
    (GaloisForLFunctions.HTGeometry.linearIndependent_iff_gramSchmidt_ne_zero _).mpr
      hresidual
  rw [det_thermalEvenGapMoment_eq_prod_krylovResidualNormSq
    intensity energy hintensity n hli]
  apply Finset.prod_pos
  intro k _
  exact sq_pos_of_pos (norm_pos_iff.mpr (hresidual k))

end

end HTGeometry
