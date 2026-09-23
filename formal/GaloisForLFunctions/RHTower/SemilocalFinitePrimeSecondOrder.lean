import GaloisForLFunctions.RHTower.SemilocalQuadraticPathSecondOrder
import GaloisForLFunctions.RHTower.SemilocalOnePrimeSecondOrderResponse

/-!
# The finite-`S` second-order assembly

Rapidities `δ_a` and amplitudes `v_a` (`a : Fin k`), ray `ε = t v`.  The degree-two part of the
product weight `∏_a (1 + 2tv_a cos(δ_a s) + t²v_a²(1 + 2cos(2δ_a s)))` is

`1 + t A(s) + t² B(s)`,  `A = Σ_a 2v_a cos(δ_a s)`,  `B = ½ A² + Σ_a v_a² cos(2δ_a s)`,

so the Gram matrix is `1 + t M₁ + t² M₂` with `M₁ = Σ_a v_a T(δ_a)`,
`M₂ = ½ Σ_{a,b} v_a v_b (T(δ_a+δ_b) + T(δ_a−δ_b)) + ½ Σ_a v_a² T(2δ_a)`, and the second derivative of
`log D_n` along the ray is the **quadratic form**

`Q(v) = Σ_{a,b} v_a v_b B_{ab}(n) + Σ_a v_a² J_{2δ_a}(n)`

in the bilinear jets `B_{ab} = J_{δ_a+δ_b} + J_{δ_a−δ_b} − tr(T(δ_a)T(δ_b))`.  At the squared-radius
level (`raySecondOrderJet_eq`) it assembles exactly from the owned one-prime and two-prime jets:

`(a_n²)''(0) = Σ_a v_a² · [one-prime second-order jet]_a + Σ_{a≠b} v_a v_b · [bilinear squared-radius jet]_{ab}`.
-/

open Matrix Real MeasureTheory Filter Topology Finset
open scoped BigOperators

namespace RHTower
namespace CosineModeResponse

open GaloisForLFunctions.HilbertMetric FirstEulerCriticalJet

section finite

variable {k : ℕ} (δ v : Fin k → ℝ)

/-- `A(s) = Σ_a 2 v_a cos(δ_a s)`. -/
noncomputable def rayFirst (s : ℝ) : ℝ := ∑ a, 2 * v a * Real.cos (δ a * s)

/-- `B(s) = ½ A(s)² + Σ_a v_a² cos(2δ_a s)`. -/
noncomputable def raySecond (s : ℝ) : ℝ :=
  (1 / 2) * rayFirst δ v s ^ (2 : ℕ) + ∑ a, v a ^ (2 : ℕ) * Real.cos (2 * δ a * s)

/-- Gram matrix of the degree-two ray weight. -/
noncomputable def rayGram (t : ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => ∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial i).eval s *
    (semilocalArchimedeanJacobiPolynomial j).eval s *
    (1 + t * rayFirst δ v s + t ^ (2 : ℕ) * raySecond δ v s) ∂semilocalArchimedeanGammaMeasure

/-- `M₁ = Σ_a v_a T(δ_a)`. -/
noncomputable def rayM₁ (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  ∑ a, v a • cosineModeTangent (δ a) n

/-- `M₂ = ½ Σ_{a,b} v_a v_b (T(δ_a+δ_b) + T(δ_a−δ_b)) + ½ Σ_a v_a² T(2δ_a)`. -/
noncomputable def rayM₂ (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (1 / 2 : ℝ) • (∑ a, ∑ b, (v a * v b) •
      (cosineModeTangent (δ a + δ b) n + cosineModeTangent (δ a - δ b) n)) +
    (1 / 2 : ℝ) • ∑ a, (v a ^ (2 : ℕ)) • cosineModeTangent (2 * δ a) n

/-- **The ray Gram matrix is the quadratic path `1 + t M₁ + t² M₂`.** -/
theorem rayGram_eq (t : ℝ) (n : ℕ) : rayGram δ v t n = quadPath (rayM₁ δ v) (rayM₂ δ v) n t := by
  ext i j
  unfold rayGram
  set P : ℝ → ℝ := fun s => (semilocalArchimedeanJacobiPolynomial i).eval s *
    (semilocalArchimedeanJacobiPolynomial j).eval s with hP
  have h0 : Integrable P semilocalArchimedeanGammaMeasure :=
    integrable_eval_mul_eval_semilocalArchimedeanGammaMeasure
      (semilocalArchimedeanJacobiPolynomial i) (semilocalArchimedeanJacobiPolynomial j)
  have hcos : ∀ c : ℝ, Integrable (fun s => P s * Real.cos (c * s)) semilocalArchimedeanGammaMeasure :=
    fun c => integrable_eval_mul_eval_mul_cos i j c
  -- pointwise expansion
  have hsplit : (fun s : ℝ => (semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s *
      (1 + t * rayFirst δ v s + t ^ (2 : ℕ) * raySecond δ v s)) =
      fun s => P s + t * (∑ a, (2 * v a) * (P s * Real.cos (δ a * s))) +
        t ^ (2 : ℕ) * ((∑ a, ∑ b, (v a * v b) * (P s * Real.cos ((δ a + δ b) * s) +
          P s * Real.cos ((δ a - δ b) * s))) + ∑ a, v a ^ (2 : ℕ) * (P s * Real.cos (2 * δ a * s))) := by
    funext s
    have h1 : P s * rayFirst δ v s = ∑ a, (2 * v a) * (P s * Real.cos (δ a * s)) := by
      unfold rayFirst
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    have h2 : P s * ((1 / 2) * rayFirst δ v s ^ (2 : ℕ)) = ∑ a, ∑ b, (v a * v b) *
        (P s * Real.cos ((δ a + δ b) * s) + P s * Real.cos ((δ a - δ b) * s)) := by
      unfold rayFirst
      rw [sq, Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have := cos_add_add_cos_sub (δ a) (δ b) s
      linear_combination (-(v a * v b * P s)) * this
    have h3 : P s * (∑ a, v a ^ (2 : ℕ) * Real.cos (2 * δ a * s)) =
        ∑ a, v a ^ (2 : ℕ) * (P s * Real.cos (2 * δ a * s)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    have hexp : P s * (1 + t * rayFirst δ v s + t ^ (2 : ℕ) * raySecond δ v s) =
        P s + t * (P s * rayFirst δ v s) +
          t ^ (2 : ℕ) * (P s * ((1 / 2) * rayFirst δ v s ^ (2 : ℕ)) +
            P s * (∑ a, v a ^ (2 : ℕ) * Real.cos (2 * δ a * s))) := by
      unfold raySecond
      ring
    show P s * (1 + t * rayFirst δ v s + t ^ (2 : ℕ) * raySecond δ v s) = _
    rw [hexp, h1, h2, h3]
  -- integrability of the pieces
  have hI1 : ∀ a ∈ (Finset.univ : Finset (Fin k)), Integrable (fun s => (2 * v a) * (P s * Real.cos (δ a * s)))
      semilocalArchimedeanGammaMeasure := fun a _ => (hcos _).const_mul _
  have hI2 : ∀ a ∈ (Finset.univ : Finset (Fin k)), ∀ b ∈ (Finset.univ : Finset (Fin k)),
      Integrable (fun s => (v a * v b) * (P s * Real.cos ((δ a + δ b) * s) +
        P s * Real.cos ((δ a - δ b) * s))) semilocalArchimedeanGammaMeasure :=
    fun a _ b _ => ((hcos _).add (hcos _)).const_mul _
  have hI2' : ∀ a ∈ (Finset.univ : Finset (Fin k)), Integrable (fun s => ∑ b, (v a * v b) *
      (P s * Real.cos ((δ a + δ b) * s) + P s * Real.cos ((δ a - δ b) * s)))
      semilocalArchimedeanGammaMeasure :=
    fun a ha => integrable_finset_sum _ (hI2 a ha)
  have hI3 : ∀ a ∈ (Finset.univ : Finset (Fin k)), Integrable (fun s => v a ^ (2 : ℕ) * (P s * Real.cos (2 * δ a * s)))
      semilocalArchimedeanGammaMeasure := fun a _ => (hcos _).const_mul _
  have hS1 : Integrable (fun s => ∑ a, (2 * v a) * (P s * Real.cos (δ a * s)))
      semilocalArchimedeanGammaMeasure := integrable_finset_sum _ hI1
  have hS2 : Integrable (fun s => ∑ a, ∑ b, (v a * v b) * (P s * Real.cos ((δ a + δ b) * s) +
      P s * Real.cos ((δ a - δ b) * s))) semilocalArchimedeanGammaMeasure := integrable_finset_sum _ hI2'
  have hS3 : Integrable (fun s => ∑ a, v a ^ (2 : ℕ) * (P s * Real.cos (2 * δ a * s)))
      semilocalArchimedeanGammaMeasure := integrable_finset_sum _ hI3
  have hS1' : Integrable (fun s => t * (∑ a, (2 * v a) * (P s * Real.cos (δ a * s))))
      semilocalArchimedeanGammaMeasure := hS1.const_mul t
  have hA : Integrable (fun s => P s + t * (∑ a, (2 * v a) * (P s * Real.cos (δ a * s))))
      semilocalArchimedeanGammaMeasure := h0.add hS1'
  have hS23 : Integrable (fun s => (∑ a, ∑ b, (v a * v b) * (P s * Real.cos ((δ a + δ b) * s) +
      P s * Real.cos ((δ a - δ b) * s))) + ∑ a, v a ^ (2 : ℕ) * (P s * Real.cos (2 * δ a * s)))
      semilocalArchimedeanGammaMeasure := hS2.add hS3
  have hB : Integrable (fun s => t ^ (2 : ℕ) * ((∑ a, ∑ b, (v a * v b) * (P s * Real.cos ((δ a + δ b) * s) +
      P s * Real.cos ((δ a - δ b) * s))) + ∑ a, v a ^ (2 : ℕ) * (P s * Real.cos (2 * δ a * s))))
      semilocalArchimedeanGammaMeasure := hS23.const_mul _
  have hgram0 : ∫ s : ℝ, P s ∂semilocalArchimedeanGammaMeasure = if (i : ℕ) = (j : ℕ) then 1 else 0 :=
    semilocalArchimedeanJacobiGram_eq_ite i j
  have hgram : ∫ s : ℝ, P s ∂semilocalArchimedeanGammaMeasure = if i = j then 1 else 0 := by
    rw [hgram0]
    simp only [Fin.val_inj]
  rw [hsplit, integral_add hA hB, integral_add h0 hS1', integral_const_mul, integral_const_mul,
    integral_add hS2 hS3, integral_finset_sum _ hI1, integral_finset_sum _ hI2', integral_finset_sum _ hI3,
    hgram]
  have f1 : ∀ a : Fin k, (∫ s, (2 * v a) * (P s * Real.cos (δ a * s)) ∂semilocalArchimedeanGammaMeasure) =
      v a * (2 * ∫ s, P s * Real.cos (δ a * s) ∂semilocalArchimedeanGammaMeasure) := fun a => by
    rw [integral_const_mul]; ring
  have f2 : ∀ a : Fin k, (∫ s, ∑ b, (v a * v b) * (P s * Real.cos ((δ a + δ b) * s) +
      P s * Real.cos ((δ a - δ b) * s)) ∂semilocalArchimedeanGammaMeasure) =
      (1 / 2) * ∑ b, (v a * v b) * (2 * (∫ s, P s * Real.cos ((δ a + δ b) * s) ∂semilocalArchimedeanGammaMeasure) +
        2 * ∫ s, P s * Real.cos ((δ a - δ b) * s) ∂semilocalArchimedeanGammaMeasure) := fun a => by
    rw [integral_finset_sum _ (hI2 a (Finset.mem_univ a)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, integral_add (hcos _) (hcos _)]
    ring
  have f3 : ∀ a : Fin k, (∫ s, v a ^ (2 : ℕ) * (P s * Real.cos (2 * δ a * s)) ∂semilocalArchimedeanGammaMeasure) =
      (1 / 2) * (v a ^ (2 : ℕ) * (2 * ∫ s, P s * Real.cos (2 * δ a * s) ∂semilocalArchimedeanGammaMeasure)) := fun a => by
    rw [integral_const_mul]; ring
  simp only [f1, f2, f3]
  simp only [quadPath, rayM₁, rayM₂, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.one_apply,
    smul_eq_mul, cosineModeTangent, hP]
  simp only [Finset.mul_sum]

/-! ## Traces -/

theorem cosineDiagonalMoment_zero (j : ℕ) : cosineDiagonalMoment 0 j = 1 := by
  unfold cosineDiagonalMoment
  have h : (fun s : ℝ => (semilocalArchimedeanJacobiPolynomial j).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s * Real.cos (0 * s)) =
      fun s => (semilocalArchimedeanJacobiPolynomial j).eval s *
        (semilocalArchimedeanJacobiPolynomial j).eval s := by
    funext s; simp
  rw [h]
  have h2 := semilocalArchimedeanJacobiGram_eq_ite j j
  rw [if_pos rfl] at h2
  exact h2

theorem cosineModeDeterminantJet_zero (m : ℕ) : cosineModeDeterminantJet 0 m = 2 * ((m : ℝ) + 1) := by
  unfold cosineModeDeterminantJet
  simp [cosineDiagonalMoment_zero]

theorem cosineModeDeterminantJet_eq_trace (c : ℝ) (m : ℕ) :
    cosineModeDeterminantJet c m = Matrix.trace (cosineModeTangent c m) := by
  rw [trace_cosineModeTangent]; rfl

theorem trace_rayM₁ (n : ℕ) :
    Matrix.trace (rayM₁ δ v n) = ∑ a, v a * cosineModeDeterminantJet (δ a) n := by
  unfold rayM₁
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.trace_smul, smul_eq_mul, cosineModeDeterminantJet_eq_trace]

theorem trace_rayM₂ (n : ℕ) :
    Matrix.trace (rayM₂ δ v n) =
      (1 / 2) * ∑ a, ∑ b, (v a * v b) * (cosineModeDeterminantJet (δ a + δ b) n +
        cosineModeDeterminantJet (δ a - δ b) n) +
      (1 / 2) * ∑ a, v a ^ (2 : ℕ) * cosineModeDeterminantJet (2 * δ a) n := by
  unfold rayM₂
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_sum, Matrix.trace_sum, smul_eq_mul,
    smul_eq_mul]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.trace_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.trace_smul, Matrix.trace_add, smul_eq_mul, cosineModeDeterminantJet_eq_trace,
      cosineModeDeterminantJet_eq_trace]
  · congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.trace_smul, smul_eq_mul, cosineModeDeterminantJet_eq_trace]

theorem trace_rayM₁_mul_rayM₁ (n : ℕ) :
    Matrix.trace (rayM₁ δ v n * rayM₁ δ v n) =
      ∑ a, ∑ b, (v a * v b) * truncationDefect (δ a) (δ b) n := by
  unfold rayM₁ truncationDefect
  rw [Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **The quadratic form:** `(log D_n)''(0) = Σ_{a,b} v_a v_b B_{ab} + Σ_a v_a² J_{2δ_a}`. -/
theorem rayLogJet_eq (n : ℕ) :
    quadLogJet (rayM₁ δ v) (rayM₂ δ v) n =
      ∑ a, ∑ b, (v a * v b) * bilinearDeterminantJet (δ a) (δ b) n +
        ∑ a, v a ^ (2 : ℕ) * cosineModeDeterminantJet (2 * δ a) n := by
  unfold quadLogJet
  rw [trace_rayM₂, trace_rayM₁_mul_rayM₁]
  simp only [bilinearDeterminantJet, truncationDefect, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  ring

/-- `(log D_n)''(0)` along the ray, as an iterated derivative of the ray Gram determinant. -/
theorem deriv_deriv_log_rayDet (n : ℕ) :
    deriv (deriv (fun t => Real.log (rayGram δ v t n).det)) 0 =
      ∑ a, ∑ b, (v a * v b) * bilinearDeterminantJet (δ a) (δ b) n +
        ∑ a, v a ^ (2 : ℕ) * cosineModeDeterminantJet (2 * δ a) n := by
  have hfun : (fun t => Real.log (rayGram δ v t n).det) =
      fun t => Real.log (quadDet (rayM₁ δ v) (rayM₂ δ v) n t) := by
    funext t
    rw [rayGram_eq]
    rfl
  rw [hfun, deriv_deriv_log_quadDet, rayLogJet_eq]

/-- The ray squared radius `r_n² Δ_{n−1}Δ_{n+1}/Δ_n²` of the ray Gram determinants. -/
noncomputable def raySquaredRadius (n : ℕ) (t : ℝ) : ℝ := quadSquaredRadius (rayM₁ δ v) (rayM₂ δ v) n t

/-- **The finite-`S` second-order assembly at the squared-radius level:**
`(a_n²)''(0) = Σ_{a,b} v_a v_b · [bilinear squared-radius jet]_{ab} + Σ_a v_a² · [harmonic jet]_a`. -/
theorem deriv_deriv_raySquaredRadius (n : ℕ) :
    deriv (deriv (fun t => raySquaredRadius δ v n t)) 0 =
      ∑ a, ∑ b, (v a * v b) * bilinearSquaredRadiusJet (δ a) (δ b) n +
        ∑ a, v a ^ (2 : ℕ) * squaredRadiusJetOf (cosineModeDeterminantJet (2 * δ a)) n := by
  unfold raySquaredRadius
  rw [deriv_deriv_quadSquaredRadius]
  unfold quadSecondOrderJet
  have hr := archimedeanSquaredRadius_pos n
  -- expand the prevJets of the sums
  have hL : ∀ m, quadLogJet (rayM₁ δ v) (rayM₂ δ v) m =
      ∑ a, ∑ b, (v a * v b) * bilinearDeterminantJet (δ a) (δ b) m +
        ∑ a, v a ^ (2 : ℕ) * cosineModeDeterminantJet (2 * δ a) m := rayLogJet_eq δ v
  have hT : ∀ m, Matrix.trace (rayM₁ δ v m) = ∑ a, v a * cosineModeDeterminantJet (δ a) m :=
    trace_rayM₁ δ v
  have hprevL : prevJet (quadLogJet (rayM₁ δ v) (rayM₂ δ v)) n =
      ∑ a, ∑ b, (v a * v b) * prevJet (bilinearDeterminantJet (δ a) (δ b)) n +
        ∑ a, v a ^ (2 : ℕ) * prevJet (cosineModeDeterminantJet (2 * δ a)) n := by
    cases n with
    | zero => simp [prevJet]
    | succ m => simp only [prevJet]; exact hL m
  have hprevT : prevJet (fun m => Matrix.trace (rayM₁ δ v m)) n =
      ∑ a, v a * prevJet (cosineModeDeterminantJet (δ a)) n := by
    cases n with
    | zero => simp [prevJet]
    | succ m => simp only [prevJet]; exact hT m
  rw [hprevL, hL, hL, hprevT, hT, hT]
  unfold bilinearSquaredRadiusJet squaredRadiusJetOf
  have hlin : (∑ a, v a * prevJet (cosineModeDeterminantJet (δ a)) n +
      ∑ a, v a * cosineModeDeterminantJet (δ a) (n + 1) - 2 * ∑ a, v a * cosineModeDeterminantJet (δ a) n) =
      ∑ a, v a * (prevJet (cosineModeDeterminantJet (δ a)) n + cosineModeDeterminantJet (δ a) (n + 1) -
        2 * cosineModeDeterminantJet (δ a) n) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hsq : (∑ a, v a * prevJet (cosineModeDeterminantJet (δ a)) n +
      ∑ a, v a * cosineModeDeterminantJet (δ a) (n + 1) - 2 * ∑ a, v a * cosineModeDeterminantJet (δ a) n) ^ (2 : ℕ) =
      ∑ a, ∑ b, (v a * v b) * ((prevJet (cosineModeDeterminantJet (δ a)) n + cosineModeDeterminantJet (δ a) (n + 1) -
        2 * cosineModeDeterminantJet (δ a) n) * (prevJet (cosineModeDeterminantJet (δ b)) n +
        cosineModeDeterminantJet (δ b) (n + 1) - 2 * cosineModeDeterminantJet (δ b) n)) := by
    rw [hlin, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hsq]
  have hrne := hr.ne'
  set r2 := archimedeanSquaredRadius n with hr2
  -- clear the division in the bilinear summands
  have hdiv : ∀ a b : Fin k, (v a * v b) *
      (r2 * (prevJet (bilinearDeterminantJet (δ a) (δ b)) n + bilinearDeterminantJet (δ a) (δ b) (n + 1) -
          2 * bilinearDeterminantJet (δ a) (δ b) n) +
        r2 * (prevJet (cosineModeDeterminantJet (δ a)) n + cosineModeDeterminantJet (δ a) (n + 1) -
          2 * cosineModeDeterminantJet (δ a) n) *
        (r2 * (prevJet (cosineModeDeterminantJet (δ b)) n + cosineModeDeterminantJet (δ b) (n + 1) -
          2 * cosineModeDeterminantJet (δ b) n)) / r2) =
      r2 * ((v a * v b) * ((prevJet (bilinearDeterminantJet (δ a) (δ b)) n +
          bilinearDeterminantJet (δ a) (δ b) (n + 1) - 2 * bilinearDeterminantJet (δ a) (δ b) n) +
        (prevJet (cosineModeDeterminantJet (δ a)) n + cosineModeDeterminantJet (δ a) (n + 1) -
          2 * cosineModeDeterminantJet (δ a) n) *
        (prevJet (cosineModeDeterminantJet (δ b)) n + cosineModeDeterminantJet (δ b) (n + 1) -
          2 * cosineModeDeterminantJet (δ b) n))) := by
    intro a b
    field_simp
  have hsingle : ∀ a : Fin k, v a ^ (2 : ℕ) * (r2 * (prevJet (cosineModeDeterminantJet (2 * δ a)) n +
      cosineModeDeterminantJet (2 * δ a) (n + 1) - 2 * cosineModeDeterminantJet (2 * δ a) n)) =
      r2 * (v a ^ (2 : ℕ) * (prevJet (cosineModeDeterminantJet (2 * δ a)) n +
      cosineModeDeterminantJet (2 * δ a) (n + 1) - 2 * cosineModeDeterminantJet (2 * δ a) n)) := by
    intro a; ring
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hdiv a b)),
    Finset.sum_congr rfl (fun a _ => hsingle a)]
  simp only [← Finset.mul_sum]
  rw [← mul_add]
  congr 1
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  ring_nf

/-- **The diagonal identity:** the bilinear squared-radius jet at `δ₁ = δ₂ = δ` plus the harmonic jet
at `2δ` is the one-prime second-order jet. -/
theorem bilinearSquaredRadiusJet_diag_add_harmonic (δ : ℝ) (n : ℕ) :
    bilinearSquaredRadiusJet δ δ n + squaredRadiusJetOf (cosineModeDeterminantJet (2 * δ)) n =
      onePrimeSecondOrderJet δ n := by
  unfold bilinearSquaredRadiusJet onePrimeSecondOrderJet squaredRadiusJetOf eulerQuadraticLogJet
  have hB : ∀ m, bilinearDeterminantJet δ δ m =
      cosineModeDeterminantJet (2 * δ) m + 2 * ((m : ℝ) + 1) - truncationDefect δ δ m := by
    intro m
    unfold bilinearDeterminantJet truncationDefect
    rw [show δ + δ = 2 * δ by ring, sub_self, cosineModeDeterminantJet_zero]
  have hprevB : prevJet (bilinearDeterminantJet δ δ) n =
      prevJet (cosineModeDeterminantJet (2 * δ)) n + prevJet (fun m => 2 * ((m : ℝ) + 1)) n -
        prevJet (truncationDefect δ δ) n := by
    cases n with
    | zero => simp [prevJet]
    | succ m => simp only [prevJet]; exact hB m
  have hprevE : prevJet (fun m => 2 * ((m : ℝ) + 1 + cosineModeDeterminantJet (2 * δ) m) -
      truncationDefect δ δ m) n = 2 * (prevJet (fun m => (m : ℝ) + 1) n +
        prevJet (cosineModeDeterminantJet (2 * δ)) n) - prevJet (truncationDefect δ δ) n := by
    cases n with
    | zero => simp [prevJet]
    | succ m => simp only [prevJet]
  have hprev2 : prevJet (fun m => 2 * ((m : ℝ) + 1)) n = 2 * prevJet (fun m => (m : ℝ) + 1) n := by
    cases n with
    | zero => simp [prevJet]
    | succ m => simp only [prevJet]
  rw [hprevB, hB, hB, hprevE, hprev2]
  have hr := (archimedeanSquaredRadius_pos n).ne'
  field_simp
  push_cast
  ring

/-- **Assembly (guarded form):** `(a_n²)''(0) = Σ_a v_a² · [one-prime jet]_a + Σ_{a≠b} v_a v_b · [bilinear jet]_{ab}`. -/
theorem deriv_deriv_raySquaredRadius_assembly (n : ℕ) :
    deriv (deriv (fun t => raySquaredRadius δ v n t)) 0 =
      ∑ a, v a ^ (2 : ℕ) * onePrimeSecondOrderJet (δ a) n +
        ∑ a, ∑ b, (if a = b then 0 else (v a * v b) * bilinearSquaredRadiusJet (δ a) (δ b) n) := by
  rw [deriv_deriv_raySquaredRadius]
  have hsplit : ∀ a : Fin k, (∑ b, (v a * v b) * bilinearSquaredRadiusJet (δ a) (δ b) n) =
      v a ^ (2 : ℕ) * bilinearSquaredRadiusJet (δ a) (δ a) n +
        ∑ b, (if a = b then 0 else (v a * v b) * bilinearSquaredRadiusJet (δ a) (δ b) n) := by
    intro a
    have h1 : (∑ b, (v a * v b) * bilinearSquaredRadiusJet (δ a) (δ b) n) =
        ∑ b, ((if a = b then (v a * v b) * bilinearSquaredRadiusJet (δ a) (δ b) n else 0) +
          (if a = b then 0 else (v a * v b) * bilinearSquaredRadiusJet (δ a) (δ b) n)) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hsplit a), Finset.sum_add_distrib]
  have hdiag : ∀ a : Fin k, v a ^ (2 : ℕ) * bilinearSquaredRadiusJet (δ a) (δ a) n +
      v a ^ (2 : ℕ) * squaredRadiusJetOf (cosineModeDeterminantJet (2 * δ a)) n =
      v a ^ (2 : ℕ) * onePrimeSecondOrderJet (δ a) n := by
    intro a
    rw [← mul_add, bilinearSquaredRadiusJet_diag_add_harmonic]
  have hone : (∑ a, v a ^ (2 : ℕ) * onePrimeSecondOrderJet (δ a) n) =
      ∑ a, v a ^ (2 : ℕ) * bilinearSquaredRadiusJet (δ a) (δ a) n +
        ∑ a, v a ^ (2 : ℕ) * squaredRadiusJetOf (cosineModeDeterminantJet (2 * δ a)) n := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => (hdiag a).symm
  rw [hone]
  ring

/-! ## The finite product against its degree-two truncation -/

theorem abs_prod_sub_quadratic_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (x y : ι → ℝ) {t : ℝ}
    (ht : |t| ≤ 1) :
    |∏ a ∈ s, (1 + t * x a + t ^ (2 : ℕ) * y a) -
        (1 + t * ∑ a ∈ s, x a + t ^ (2 : ℕ) * (∑ a ∈ s, y a + (1 / 2) * ((∑ a ∈ s, x a) ^ (2 : ℕ) - ∑ a ∈ s, x a ^ (2 : ℕ))))| ≤
      |t| ^ (3 : ℕ) * (∏ a ∈ s, (1 + (|x a| + |y a|))) * (1 + ∑ a ∈ s, (|x a| + |y a|)) ^ (3 : ℕ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih =>
    set X := ∑ a ∈ s, x a with hX
    set Y := ∑ a ∈ s, y a + (1 / 2) * (X ^ (2 : ℕ) - ∑ a ∈ s, x a ^ (2 : ℕ)) with hY
    set W := ∑ a ∈ s, (|x a| + |y a|) with hW
    set P := ∏ a ∈ s, (1 + t * x a + t ^ (2 : ℕ) * y a) with hPdef
    set K := ∏ a ∈ s, (1 + (|x a| + |y a|)) with hK
    clear_value X Y W P K
    have hXW : |X| ≤ W := by
      rw [hX, hW]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      linarith [abs_nonneg (y a)]
    have hsq : ∑ a ∈ s, x a ^ (2 : ℕ) ≤ W ^ (2 : ℕ) := by
      rw [hW]
      have h1 : ∑ a ∈ s, x a ^ (2 : ℕ) ≤ ∑ a ∈ s, (|x a| + |y a|) ^ (2 : ℕ) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [← sq_abs (x a)]
        exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (y a)]) 2
      have h2 : ∑ a ∈ s, (|x a| + |y a|) ^ (2 : ℕ) ≤ (∑ a ∈ s, (|x a| + |y a|)) ^ (2 : ℕ) := by
        rw [sq, Finset.sum_mul_sum]
        have : ∀ a ∈ s, (|x a| + |y a|) ^ (2 : ℕ) = ∑ b ∈ s, (if a = b then (|x a| + |y a|) * (|x b| + |y b|) else 0) := by
          intro a ha
          rw [Finset.sum_ite_eq]
          simp [ha, sq]
        rw [Finset.sum_congr rfl this]
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        split_ifs
        · exact le_rfl
        · positivity
      linarith
    have hYW : |Y| ≤ W + W ^ (2 : ℕ) := by
      rw [hY]
      have hy : |∑ a ∈ s, y a| ≤ W := by
        rw [hW]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        linarith [abs_nonneg (x a)]
      have hx2 : 0 ≤ ∑ a ∈ s, x a ^ (2 : ℕ) := Finset.sum_nonneg fun a _ => sq_nonneg _
      have hX2 : X ^ (2 : ℕ) ≤ W ^ (2 : ℕ) := by
        rw [← sq_abs X]
        exact pow_le_pow_left₀ (abs_nonneg _) hXW 2
      calc |∑ a ∈ s, y a + 1 / 2 * (X ^ (2 : ℕ) - ∑ a ∈ s, x a ^ (2 : ℕ))|
          ≤ |∑ a ∈ s, y a| + |1 / 2 * (X ^ (2 : ℕ) - ∑ a ∈ s, x a ^ (2 : ℕ))| := abs_add_le _ _
        _ ≤ W + W ^ (2 : ℕ) := by
            have : |1 / 2 * (X ^ (2 : ℕ) - ∑ a ∈ s, x a ^ (2 : ℕ))| ≤ W ^ (2 : ℕ) := by
              rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
              have hb : |X ^ (2 : ℕ) - ∑ a ∈ s, x a ^ (2 : ℕ)| ≤ W ^ (2 : ℕ) := by
                rw [abs_le]
                constructor <;> nlinarith [sq_nonneg X]
              nlinarith [abs_nonneg (X ^ (2 : ℕ) - ∑ a ∈ s, x a ^ (2 : ℕ))]
            linarith
    have hWnn : 0 ≤ W := by
      rw [hW]
      exact Finset.sum_nonneg fun a _ => by positivity
    have hKpos : 1 ≤ K := by
      rw [hK]
      calc (1 : ℝ) = ∏ a ∈ s, (1 : ℝ) := by simp
        _ ≤ ∏ a ∈ s, (1 + (|x a| + |y a|)) :=
          Finset.prod_le_prod (fun _ _ => by norm_num)
            (fun a _ => by linarith [abs_nonneg (x a), abs_nonneg (y a)])
    rw [Finset.prod_insert hc, Finset.sum_insert hc, Finset.sum_insert hc, Finset.sum_insert hc,
      Finset.prod_insert hc, Finset.sum_insert hc]
    rw [← hX, ← hPdef, ← hK, ← hW]
    set w := |x c| + |y c| with hw
    clear_value w
    have hwnn : 0 ≤ w := by rw [hw]; positivity
    -- the new truncation is 1 + t(x_c + X) + t²(Y + y_c + x_c X)
    have hQ' : (1 + t * (x c + X) + t ^ (2 : ℕ) * (y c + ∑ a ∈ s, y a +
        (1 / 2) * ((x c + X) ^ (2 : ℕ) - (x c ^ (2 : ℕ) + ∑ a ∈ s, x a ^ (2 : ℕ))))) =
        1 + t * (x c + X) + t ^ (2 : ℕ) * (Y + y c + x c * X) := by
      rw [hY]; ring
    rw [hQ']
    have hfac : (1 + t * x c + t ^ (2 : ℕ) * y c) * P - (1 + t * (x c + X) + t ^ (2 : ℕ) * (Y + y c + x c * X)) =
        (1 + t * x c + t ^ (2 : ℕ) * y c) * (P - (1 + t * X + t ^ (2 : ℕ) * Y)) +
          (t ^ (3 : ℕ) * (x c * Y + y c * X) + t ^ (4 : ℕ) * (y c * Y)) := by ring
    rw [hfac]
    have hfabs : |1 + t * x c + t ^ (2 : ℕ) * y c| ≤ 1 + w := by
      rw [hw]
      have h1 : |t * x c| ≤ |x c| := by rw [abs_mul]; nlinarith [abs_nonneg (x c), abs_nonneg t]
      have h2 : |t ^ (2 : ℕ) * y c| ≤ |y c| := by
        rw [abs_mul, abs_pow]
        have : |t| ^ (2 : ℕ) ≤ 1 := pow_le_one₀ (abs_nonneg _) ht
        nlinarith [abs_nonneg (y c), sq_nonneg |t|]
      have ha1 := abs_add_le (1 + t * x c) (t ^ (2 : ℕ) * y c)
      have ha2 := abs_add_le (1 : ℝ) (t * x c)
      rw [abs_one] at ha2
      linarith
    have ht3 : 0 ≤ |t| ^ (3 : ℕ) := by positivity
    have hrem : |t ^ (3 : ℕ) * (x c * Y + y c * X) + t ^ (4 : ℕ) * (y c * Y)| ≤ |t| ^ (3 : ℕ) * (w * (W + 2 * (W + W ^ (2 : ℕ)))) := by
      have ha : |t ^ (3 : ℕ) * (x c * Y + y c * X)| ≤ |t| ^ (3 : ℕ) * (|x c| * (W + W ^ (2 : ℕ)) + |y c| * W) := by
        rw [abs_mul, abs_pow]
        apply mul_le_mul_of_nonneg_left _ ht3
        calc |x c * Y + y c * X| ≤ |x c * Y| + |y c * X| := abs_add_le _ _
          _ = |x c| * |Y| + |y c| * |X| := by rw [abs_mul, abs_mul]
          _ ≤ |x c| * (W + W ^ (2 : ℕ)) + |y c| * W := by gcongr
      have hb : |t ^ (4 : ℕ) * (y c * Y)| ≤ |t| ^ (3 : ℕ) * (|y c| * (W + W ^ (2 : ℕ))) := by
        rw [abs_mul, abs_pow, abs_mul]
        have h4 : |t| ^ (4 : ℕ) ≤ |t| ^ (3 : ℕ) := pow_le_pow_of_le_one (abs_nonneg _) ht (by norm_num)
        calc |t| ^ (4 : ℕ) * (|y c| * |Y|) ≤ |t| ^ (3 : ℕ) * (|y c| * |Y|) :=
              mul_le_mul_of_nonneg_right h4 (by positivity)
          _ ≤ |t| ^ (3 : ℕ) * (|y c| * (W + W ^ (2 : ℕ))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hYW (abs_nonneg _)) ht3
      calc |t ^ (3 : ℕ) * (x c * Y + y c * X) + t ^ (4 : ℕ) * (y c * Y)|
          ≤ |t ^ (3 : ℕ) * (x c * Y + y c * X)| + |t ^ (4 : ℕ) * (y c * Y)| := abs_add_le _ _
        _ ≤ |t| ^ (3 : ℕ) * (|x c| * (W + W ^ (2 : ℕ)) + |y c| * W) + |t| ^ (3 : ℕ) * (|y c| * (W + W ^ (2 : ℕ))) := add_le_add ha hb
        _ = |t| ^ (3 : ℕ) * (|x c| * (W + W ^ (2 : ℕ)) + |y c| * W + |y c| * (W + W ^ (2 : ℕ))) := by ring
        _ ≤ |t| ^ (3 : ℕ) * (w * (W + 2 * (W + W ^ (2 : ℕ)))) := by
            apply mul_le_mul_of_nonneg_left _ ht3
            rw [hw]
            have p1 := mul_nonneg (abs_nonneg (x c)) hWnn
            have p2 := mul_nonneg (abs_nonneg (x c)) (sq_nonneg W)
            have p3 := mul_nonneg (abs_nonneg (y c)) hWnn
            have p4 := mul_nonneg (abs_nonneg (y c)) (sq_nonneg W)
            nlinarith [p1, p2, p3, p4]
    have hKw : 1 ≤ (1 + w) * K := one_le_mul_of_one_le_of_one_le (by linarith) hKpos
    have hbin : (1 + W) ^ (3 : ℕ) + 3 * w * (1 + W) ^ (2 : ℕ) ≤ (1 + (w + W)) ^ (3 : ℕ) := by
      have h0 : (1 + (w + W)) ^ (3 : ℕ) = (1 + W) ^ (3 : ℕ) + 3 * w * (1 + W) ^ (2 : ℕ) + (3 * w ^ (2 : ℕ) * (1 + W) + w ^ (3 : ℕ)) := by ring
      have h1 : 0 ≤ 3 * w ^ (2 : ℕ) * (1 + W) + w ^ (3 : ℕ) := by positivity
      rw [h0]
      linarith
    have h3 : w * (W + 2 * (W + W ^ (2 : ℕ))) ≤ 3 * w * (1 + W) ^ (2 : ℕ) := by
      have h0 : 3 * w * (1 + W) ^ (2 : ℕ) - w * (W + 2 * (W + W ^ (2 : ℕ))) = 3 * w + 3 * w * W + w * W ^ (2 : ℕ) := by ring
      have h1 : 0 ≤ 3 * w + 3 * w * W + w * W ^ (2 : ℕ) := by positivity
      linarith
    have h4 : 3 * w * (1 + W) ^ (2 : ℕ) ≤ (1 + w) * K * (3 * w * (1 + W) ^ (2 : ℕ)) :=
      le_mul_of_one_le_left (by positivity) hKw
    have h5 : (1 + w) * K * (1 + W) ^ (3 : ℕ) + (1 + w) * K * (3 * w * (1 + W) ^ (2 : ℕ)) ≤
        (1 + w) * K * (1 + (w + W)) ^ (3 : ℕ) := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left hbin (by positivity)
    have hmain : (1 + w) * K * (1 + W) ^ (3 : ℕ) + w * (W + 2 * (W + W ^ (2 : ℕ))) ≤
        (1 + w) * K * (1 + (w + W)) ^ (3 : ℕ) := by linarith
    calc |(1 + t * x c + t ^ (2 : ℕ) * y c) * (P - (1 + t * X + t ^ (2 : ℕ) * Y)) +
          (t ^ (3 : ℕ) * (x c * Y + y c * X) + t ^ (4 : ℕ) * (y c * Y))|
        ≤ |(1 + t * x c + t ^ (2 : ℕ) * y c)| * |P - (1 + t * X + t ^ (2 : ℕ) * Y)| +
          |t ^ (3 : ℕ) * (x c * Y + y c * X) + t ^ (4 : ℕ) * (y c * Y)| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ (1 + w) * (|t| ^ (3 : ℕ) * K * (1 + W) ^ (3 : ℕ)) + |t| ^ (3 : ℕ) * (w * (W + 2 * (W + W ^ (2 : ℕ)))) := by
          gcongr
      _ = |t| ^ (3 : ℕ) * ((1 + w) * K * (1 + W) ^ (3 : ℕ) + w * (W + 2 * (W + W ^ (2 : ℕ)))) := by ring
      _ ≤ |t| ^ (3 : ℕ) * ((1 + w) * K * (1 + (w + W)) ^ (3 : ℕ)) := mul_le_mul_of_nonneg_left hmain ht3
      _ = _ := by ring

end finite

end CosineModeResponse
end RHTower
