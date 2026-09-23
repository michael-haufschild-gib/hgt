import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Skew-conjugated Riccati flows and their boundary Gramian

A matrix curve whose derivative is a commutator with a skew generator, minus its own square, minus
a rank-one boundary source, has a centered inverse whose derivative is the same commutator *plus*
a rank-one source of the opposite sign.  Conjugating by the orthogonal flow of the skew generator
removes the commutator entirely, so the conjugated centered inverse moves only by rank-one positive
semidefinite increments.

Differentiation is entrywise throughout, so no normed structure on the matrix space is used and no
instance diamond can appear.
-/

open Matrix MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-! ## Entrywise differentiation of matrix curves -/

/-- A matrix curve is differentiable with a given derivative matrix when every entry is. -/
def MatrixHasDerivAt (F : ℝ → Matrix (Fin n) (Fin n) ℝ) (F' : Matrix (Fin n) (Fin n) ℝ)
    (y : ℝ) : Prop := ∀ i j, HasDerivAt (fun v => F v i j) (F' i j) y

theorem MatrixHasDerivAt.add {F G : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {F' G' : Matrix (Fin n) (Fin n) ℝ} {y : ℝ}
    (hF : MatrixHasDerivAt F F' y) (hG : MatrixHasDerivAt G G' y) :
    MatrixHasDerivAt (fun v => F v + G v) (F' + G') y := fun i j => (hF i j).add (hG i j)

theorem MatrixHasDerivAt.sub {F G : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {F' G' : Matrix (Fin n) (Fin n) ℝ} {y : ℝ}
    (hF : MatrixHasDerivAt F F' y) (hG : MatrixHasDerivAt G G' y) :
    MatrixHasDerivAt (fun v => F v - G v) (F' - G') y := fun i j => (hF i j).sub (hG i j)

theorem MatrixHasDerivAt.transpose {F : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {F' : Matrix (Fin n) (Fin n) ℝ} {y : ℝ} (hF : MatrixHasDerivAt F F' y) :
    MatrixHasDerivAt (fun v => (F v)ᵀ) (F'ᵀ) y := fun i j => hF j i

theorem MatrixHasDerivAt.mul {F G : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {F' G' : Matrix (Fin n) (Fin n) ℝ} {y : ℝ}
    (hF : MatrixHasDerivAt F F' y) (hG : MatrixHasDerivAt G G' y) :
    MatrixHasDerivAt (fun v => F v * G v) (F' * G y + F y * G') y := by
  intro i j
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      HasDerivAt (fun v => F v i k * G v k j) (F' i k * G y k j + F y i k * G' k j) y :=
    fun k _ => (hF i k).mul (hG k j)
  have h := HasDerivAt.sum hterm
  have hfun : (∑ k ∈ (Finset.univ : Finset (Fin n)), fun v : ℝ => F v i k * G v k j)
      = fun v : ℝ => ∑ k ∈ (Finset.univ : Finset (Fin n)), F v i k * G v k j := by
    funext v
    rw [Finset.sum_apply]
  rw [hfun] at h
  simpa [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using h

theorem matrixHasDerivAt_smul_one (y : ℝ) :
    MatrixHasDerivAt (fun v : ℝ => v • (1 : Matrix (Fin n) (Fin n) ℝ))
      (1 : Matrix (Fin n) (Fin n) ℝ) y := by
  intro i j
  have h : HasDerivAt (fun v : ℝ => v * (1 : Matrix (Fin n) (Fin n) ℝ) i j)
      ((1 : Matrix (Fin n) (Fin n) ℝ) i j) y := by
    simpa using (hasDerivAt_id y).mul_const ((1 : Matrix (Fin n) (Fin n) ℝ) i j)
  simpa [Matrix.smul_apply, smul_eq_mul] using h

/-- A matrix curve with vanishing entrywise derivative is constant. -/
theorem matrix_eq_of_matrixHasDerivAt_zero {F : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ y, MatrixHasDerivAt F 0 y) (a b : ℝ) : F a = F b := by
  ext i j
  have hd : ∀ y : ℝ, HasDerivAt (fun v => F v i j) 0 y := by
    intro y
    simpa using h y i j
  exact is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt) (fun y => (hd y).deriv) a b

/-! ## The orthogonal flow of a skew generator -/

/-- **The flow of a skew generator is orthogonal.** -/
theorem transpose_mul_self_eq_one_of_skew_flow (A O : ℝ → Matrix (Fin n) (Fin n) ℝ) (y₀ : ℝ)
    (hO : ∀ y, MatrixHasDerivAt O (-(A y * O y)) y)
    (hskew : ∀ y, (A y)ᵀ = -A y) (hinit : O y₀ = 1) :
    ∀ y, (O y)ᵀ * O y = 1 := by
  have hderiv : ∀ y, MatrixHasDerivAt (fun v => (O v)ᵀ * O v) 0 y := by
    intro y
    have h2 := (hO y).transpose.mul (hO y)
    have hval : (-(A y * O y))ᵀ * O y + (O y)ᵀ * -(A y * O y) = 0 := by
      rw [Matrix.transpose_neg, Matrix.transpose_mul, hskew y]
      simp only [Matrix.mul_neg, neg_neg]
      rw [Matrix.mul_assoc]
      abel
    rw [hval] at h2
    exact h2
  intro y
  rw [matrix_eq_of_matrixHasDerivAt_zero hderiv y y₀, hinit]
  simp

/-! ## The centered inverse of a Riccati flow -/

/-- **The centered inverse law.**  If `J` solves a Riccati flow with skew commutator, its own
square, and a rank-one source, then the centered inverse `J⁻¹ − y` solves the same commutator with
the rank-one source transported through the inverse and with the opposite sign. -/
theorem matrixHasDerivAt_centeredInverse {J W A : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {J' : Matrix (Fin n) (Fin n) ℝ} {e : Fin n → ℝ} {c : ℝ} {y : ℝ}
    (hW : MatrixHasDerivAt W (-(W y * J' * W y)) y)
    (hWJ : W y * J y = 1) (hJW : J y * W y = 1) (hWsym : (W y)ᵀ = W y)
    (hric : J' = J y * A y - A y * J y - J y * J y - c • Matrix.vecMulVec e e) :
    MatrixHasDerivAt (fun v => W v - v • (1 : Matrix (Fin n) (Fin n) ℝ))
      ((W y - y • (1 : Matrix (Fin n) (Fin n) ℝ)) * A y
        - A y * (W y - y • (1 : Matrix (Fin n) (Fin n) ℝ))
        + c • Matrix.vecMulVec (W y *ᵥ e) (W y *ᵥ e)) y := by
  have hsub := hW.sub (matrixHasDerivAt_smul_one (n := n) y)
  have hsym : ∀ l j : Fin n, W y l j = W y j l := by
    intro l j
    have h := congrFun (congrFun hWsym j) l
    simpa [Matrix.transpose_apply] using h
  have hvec : W y * Matrix.vecMulVec e e * W y
      = Matrix.vecMulVec (W y *ᵥ e) (W y *ᵥ e) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct]
    calc (∑ l, (∑ k, W y i k * (e k * e l)) * W y l j)
        = ∑ l, ∑ k, (W y i k * e k) * (e l * W y l j) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = (∑ k, W y i k * e k) * (∑ l, e l * W y l j) := by
          rw [Finset.sum_mul_sum]
          exact Finset.sum_comm
      _ = (∑ k, W y i k * e k) * (∑ l, W y j l * e l) := by
          refine congrArg _ (Finset.sum_congr rfl fun l _ => ?_)
          rw [hsym l j]
          ring
  have h1 : W y * (J y * A y) * W y = A y * W y := by
    rw [← Matrix.mul_assoc (W y) (J y) (A y), hWJ, Matrix.one_mul]
  have h2 : W y * (A y * J y) * W y = W y * A y := by
    rw [Matrix.mul_assoc (W y) (A y * J y) (W y), Matrix.mul_assoc (A y) (J y) (W y), hJW,
      Matrix.mul_one]
  have h3 : W y * (J y * J y) * W y = 1 := by
    rw [← Matrix.mul_assoc (W y) (J y) (J y), hWJ, Matrix.one_mul, hJW]
  have hexpand : W y * J' * W y
      = A y * W y - W y * A y - 1 - c • Matrix.vecMulVec (W y *ᵥ e) (W y *ᵥ e) := by
    rw [hric]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [h1, h2, h3, hvec]
  have hval : -(W y * J' * W y) - 1
      = (W y - y • (1 : Matrix (Fin n) (Fin n) ℝ)) * A y
        - A y * (W y - y • (1 : Matrix (Fin n) (Fin n) ℝ))
        + c • Matrix.vecMulVec (W y *ᵥ e) (W y *ᵥ e) := by
    rw [hexpand]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    abel
  rw [← hval]
  exact hsub

/-! ## The conjugated increment -/

/-- **Skew conjugation removes the commutator.**  Conjugating a curve whose derivative is a
commutator with the skew generator plus a source leaves exactly the transported source. -/
theorem matrixHasDerivAt_conjugated {U A O : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {U' S : Matrix (Fin n) (Fin n) ℝ} {y : ℝ}
    (hU : MatrixHasDerivAt U U' y) (hO : MatrixHasDerivAt O (-(A y * O y)) y)
    (hskew : (A y)ᵀ = -A y)
    (hric : U' = U y * A y - A y * U y + S) :
    MatrixHasDerivAt (fun v => (O v)ᵀ * U v * O v) ((O y)ᵀ * S * O y) y := by
  have hstep := (hO.transpose.mul hU).mul hO
  have hval : ((-(A y * O y))ᵀ * U y + (O y)ᵀ * U') * O y
      + (O y)ᵀ * U y * -(A y * O y) = (O y)ᵀ * S * O y := by
    rw [hric, Matrix.transpose_neg, Matrix.transpose_mul, hskew]
    simp only [Matrix.mul_neg, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, neg_neg]
    abel
  rw [hval] at hstep
  exact hstep

/-! ## The boundary Gramian -/

/-- **The conjugated increment is the exact integral of the transported source.** -/
theorem conjugated_increment_eq_integral {U O : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {S : ℝ → Matrix (Fin n) (Fin n) ℝ} {y₀ Y : ℝ}
    (hstep : ∀ y ∈ Set.uIcc y₀ Y,
        MatrixHasDerivAt (fun v => (O v)ᵀ * U v * O v) (S y) y)
    (hint : ∀ i j, IntervalIntegrable (fun v => S v i j) volume y₀ Y) :
    (O Y)ᵀ * U Y * O Y - (O y₀)ᵀ * U y₀ * O y₀
      = Matrix.of fun i j => ∫ v in y₀..Y, S v i j := by
  ext i j
  have hderiv : ∀ v ∈ Set.uIcc y₀ Y,
      HasDerivAt (fun w => ((O w)ᵀ * U w * O w) i j) (S v i j) v := fun v hv => hstep v hv i j
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint i j)
  simp only [Matrix.sub_apply, Matrix.of_apply]
  rw [h]

theorem intervalIntegrable_sum_fun {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun v => ∑ i ∈ s, f i v) volume a b := by
  have hsum := IntervalIntegrable.sum s h
  have hfun : (∑ i ∈ s, f i) = fun v => ∑ i ∈ s, f i v := by
    funext v
    rw [Finset.sum_apply]
  rwa [hfun] at hsum

/-- A pointwise positive semidefinite integrand integrates to a positive semidefinite matrix. -/
theorem dotProduct_integral_nonneg {F : ℝ → Matrix (Fin n) (Fin n) ℝ} {y₀ Y : ℝ} (hle : y₀ ≤ Y)
    (hint : ∀ i j, IntervalIntegrable (fun v => F v i j) volume y₀ Y)
    (x : Fin n → ℝ) (hpos : ∀ v, 0 ≤ x ⬝ᵥ (F v *ᵥ x)) :
    0 ≤ x ⬝ᵥ ((Matrix.of fun i j => ∫ v in y₀..Y, F v i j) *ᵥ x) := by
  have hgint : ∀ i j, IntervalIntegrable (fun v => x i * (F v i j * x j)) volume y₀ Y :=
    fun i j => ((hint i j).mul_const (x j)).const_mul (x i)
  have hrowint : ∀ i, IntervalIntegrable (fun v => ∑ j, x i * (F v i j * x j)) volume y₀ Y :=
    fun i => intervalIntegrable_sum_fun _ fun j _ => hgint i j
  have hentry : ∀ i j, x i * ((∫ v in y₀..Y, F v i j) * x j)
      = ∫ v in y₀..Y, x i * (F v i j * x j) := by
    intro i j
    rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_const_mul]
  have hval : x ⬝ᵥ ((Matrix.of fun i j => ∫ v in y₀..Y, F v i j) *ᵥ x)
      = ∫ v in y₀..Y, x ⬝ᵥ (F v *ᵥ x) := by
    have hlhs : x ⬝ᵥ ((Matrix.of fun i j => ∫ v in y₀..Y, F v i j) *ᵥ x)
        = ∑ i, ∑ j, x i * ((∫ v in y₀..Y, F v i j) * x j) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    have hrhs : (∫ v in y₀..Y, x ⬝ᵥ (F v *ᵥ x))
        = ∑ i, ∫ v in y₀..Y, ∑ j, x i * (F v i j * x j) := by
      rw [← intervalIntegral.integral_finsetSum (fun i _ => hrowint i)]
      refine intervalIntegral.integral_congr fun v _ => ?_
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [hlhs, hrhs]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum (fun j _ => hgint i j)]
    exact Finset.sum_congr rfl fun j _ => hentry i j
  rw [hval]
  exact intervalIntegral.integral_nonneg hle fun v _ => hpos v

/-- Conjugation moves the test vector. -/
theorem dotProduct_conj_eq (O M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((Oᵀ * M * O) *ᵥ x) = (O *ᵥ x) ⬝ᵥ (M *ᵥ (O *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, Matrix.mulVec_mulVec]

/-- A nonnegative multiple of a rank-one square is positive semidefinite. -/
theorem dotProduct_smul_vecMulVec_nonneg {c : ℝ} (hc : 0 ≤ c) (w x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ ((c • Matrix.vecMulVec w w) *ᵥ x) := by
  have h : x ⬝ᵥ ((c • Matrix.vecMulVec w w) *ᵥ x) = c * (x ⬝ᵥ w) ^ (2 : ℕ) := by
    simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum,
      mul_comm, mul_left_comm, sq]
  rw [h]
  positivity

end GaloisForLFunctions.HTGeometry
