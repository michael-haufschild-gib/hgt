import GaloisForLFunctions.HilbertMetric.Spectral.ClippedFunctionalCalculus

/-!
# Diagonal congruences for mixed Gram energy

Positive diagonal weights transport a clipped dual certificate from an
unweighted correlation matrix to its weighted Gram matrix. Inverse square-root
congruence contracts the square energy when every weight is at least one.
-/

open Matrix
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.HilbertMetric.Clipped
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realDiagonal (s : ι → ℝ) : Matrix ι ι ℂ := diagonal fun i => (s i : ℂ)

def congruence (s : ι → ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  realDiagonal s * A * realDiagonal s

omit [Fintype ι] in
theorem realDiagonal_hermitian (s : ι → ℝ) : (realDiagonal s).IsHermitian := by
  simp [realDiagonal, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]

theorem congruence_hermitian (s : ι → ℝ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (congruence s A).IsHermitian := by
  have h := Matrix.isHermitian_conjTranspose_mul_mul (realDiagonal s) hA
  rwa [(realDiagonal_hermitian s).eq] at h

theorem congruence_posSemidef (s : ι → ℝ) {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    (congruence s A).PosSemidef := by
  have h := hA.conjTranspose_mul_mul_same (realDiagonal s)
  rwa [(realDiagonal_hermitian s).eq] at h

theorem congruence_apply (s : ι → ℝ) (A : Matrix ι ι ℂ) (i j : ι) :
    congruence s A i j = (s i : ℂ) * A i j * (s j : ℂ) := by
  simp only [congruence, realDiagonal, diagonal_mul, mul_diagonal]

/-- Reciprocal diagonal congruences cancel in the trace pairing. -/
theorem congruence_trace_pair (s t : ι → ℝ) (hst : ∀ i, s i * t i = 1)
    (A B : Matrix ι ι ℂ) :
    trace (congruence s A * congruence t B) = trace (A * B) := by
  simp only [trace, diag, mul_apply, congruence_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ((s i : ℂ) * t i) * ((s j : ℂ) * t j) * (A i j * B j i) := by ring
    _ = _ := by simp only [← Complex.ofReal_mul, hst, Complex.ofReal_one, one_mul]

/-- Diagonal contractions decrease the full Hermitian square energy. -/
theorem congruence_square_le (s : ι → ℝ) (hs : ∀ i, |s i| ≤ 1)
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (trace (congruence s A * congruence s A)).re ≤ (trace (A * A)).re := by
  rw [trace_square (congruence_hermitian s hA), trace_square hA]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [congruence_apply]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal]
  have hi : 0 ≤ s i * s i := mul_self_nonneg _
  have hj : 0 ≤ s j * s j := mul_self_nonneg _
  have hi' : s i * s i ≤ 1 := by nlinarith only [sq_le_sq₀ (abs_nonneg (s i)) zero_le_one |>.mpr (hs i), sq_abs (s i)]
  have hj' : s j * s j ≤ 1 := by nlinarith only [sq_le_sq₀ (abs_nonneg (s j)) zero_le_one |>.mpr (hs j), sq_abs (s j)]
  calc
    _ ≤ 1 * Complex.normSq (A i j) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hi' (Complex.normSq_nonneg _)) hj' hj
        (by simpa using Complex.normSq_nonneg (A i j))
    _ = _ := by ring

/-- The largest value of `d + τ/d` on `[1,2]` occurs at an endpoint. -/
theorem weight_admissible {d τ c : ℝ} (hd : 1 ≤ d) (hd' : d ≤ 2)
    (hτ : 0 ≤ τ) (h₁ : 1 + τ ≤ c) (h₂ : 2 + τ / 2 ≤ c) :
    d + τ / d ≤ c := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have ha := mul_nonneg (sub_nonneg.mpr h₁)
    (mul_nonneg (sub_nonneg.mpr hd') hd0.le)
  have hb := mul_nonneg (sub_nonneg.mpr h₂)
    (mul_nonneg (sub_nonneg.mpr hd) hd0.le)
  have ht := mul_nonneg hτ (mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hd'))
  have hdiv : τ / d ≤ c - d := (div_le_iff₀ hd0).mpr (by nlinarith only [ha, hb, ht])
  linarith only [hdiv]

/-- The Gram matrix with positive diagonal weights. -/
def weightedGram (d : ι → ℝ) (U : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  congruence (fun i => Real.sqrt (d i)) U

theorem weightedGram_hermitian (d : ι → ℝ) {U : Matrix ι ι ℂ} (hU : U.IsHermitian) :
    (weightedGram d U).IsHermitian := congruence_hermitian _ hU

theorem inverseSqrt_square_le (d : ι → ℝ) (hd : ∀ i, 1 ≤ d i)
    {C : Matrix ι ι ℂ} (hC : C.IsHermitian) :
    (trace (congruence (fun i => (Real.sqrt (d i))⁻¹) C *
      congruence (fun i => (Real.sqrt (d i))⁻¹) C)).re ≤ (trace (C * C)).re := by
  apply congruence_square_le _ _ hC
  intro i
  rw [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (hd i))

omit [Fintype ι] [DecidableEq ι] in
/-- The inverse square-root congruence cancels a positive diagonal weight. -/
theorem inverseSqrt_diagonal_cancel (d : ι → ℝ) (hd : ∀ i, 0 < d i) (i : ι) :
    d i * (Real.sqrt (d i))⁻¹ * (Real.sqrt (d i))⁻¹ = 1 := by
  rw [mul_assoc, ← mul_inv, Real.mul_self_sqrt (hd i).le, mul_inv_cancel₀ (hd i).ne']

/-- The weighted test matrix keeps the correlation pairing after diagonal rescaling. -/
theorem mixed_trace_identity (d : ι → ℝ) (hd : ∀ i, 0 < d i)
    (U C : Matrix ι ι ℂ) (hUd : ∀ i, U i i = 1) :
    let M := congruence (fun i => (Real.sqrt (d i))⁻¹) C
    let X := realDiagonal d + M
    2 * (trace (X * weightedGram d U)).re - (trace (X * X)).re - ∑ i, d i ^ 2 =
      2 * (trace (C * (U - 1))).re - (trace (M * M)).re := by
  intro M X
  have hDG : trace (realDiagonal d * weightedGram d U) = ∑ i, ((d i ^ 2 : ℝ) : ℂ) := by
    simp only [trace, diag, realDiagonal, diagonal_mul, weightedGram, congruence_apply, hUd]
    apply Finset.sum_congr rfl
    intro i _
    have hs : (Real.sqrt (d i) : ℂ) * Real.sqrt (d i) = (d i : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hd i).le]
    push_cast
    calc
      _ = (d i : ℂ) * ((Real.sqrt (d i) : ℂ) * Real.sqrt (d i)) := by ring
      _ = _ := by rw [hs]; ring
  have hMG : trace (M * weightedGram d U) = trace (C * U) := by
    apply congruence_trace_pair
    intro i
    exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (hd i)).ne'
  have hDD : trace (realDiagonal d * realDiagonal d) = ∑ i, ((d i ^ 2 : ℝ) : ℂ) := by
    simp [realDiagonal, diagonal_mul_diagonal, pow_two]
  have hDM : trace (realDiagonal d * M) = trace C := by
    simp only [trace, diag, realDiagonal, diagonal_mul, M, congruence_apply]
    apply Finset.sum_congr rfl
    intro i _
    have hc : (d i : ℂ) * (Real.sqrt (d i) : ℂ)⁻¹ * (Real.sqrt (d i) : ℂ)⁻¹ = 1 := by
      exact_mod_cast inverseSqrt_diagonal_cancel d hd i
    calc
      _ = ((d i : ℂ) * (Real.sqrt (d i) : ℂ)⁻¹ * (Real.sqrt (d i) : ℂ)⁻¹) * C i i := by
        push_cast; ring
      _ = _ := by rw [hc, one_mul]
  have hMD : trace (M * realDiagonal d) = trace C := by rw [trace_mul_comm, hDM]
  simp only [X, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one,
    trace_add, trace_sub, hDG, hMG, hDD, hDM, hMD, Complex.add_re, Complex.sub_re,
    Complex.re_sum, Complex.ofReal_re]
  ring

/-- The weighted dual certificate respects the same clipping constraint. -/
theorem mixed_certificate_cap (d : ι → ℝ) (hd₁ : ∀ i, 1 ≤ d i)
    (hd₂ : ∀ i, d i ≤ 2) {τ c : ℝ} (hτ : 0 ≤ τ)
    (hc₁ : 1 + τ ≤ c) (hc₂ : 2 + τ / 2 ≤ c)
    {C : Matrix ι ι ℂ} (hC : ((τ : ℂ) • (1 : Matrix ι ι ℂ) - C).PosSemidef) :
    ((c : ℂ) • (1 : Matrix ι ι ℂ) -
      (realDiagonal d + congruence (fun i => (Real.sqrt (d i))⁻¹) C)).PosSemidef := by
  let s : ι → ℝ := fun i => (Real.sqrt (d i))⁻¹
  have hd (i : ι) : 0 < d i := lt_of_lt_of_le zero_lt_one (hd₁ i)
  have hs (i : ι) : s i * s i = (d i)⁻¹ := by
    dsimp only [s]
    rw [← mul_inv, Real.mul_self_sqrt (hd i).le]
  have hR : (realDiagonal (fun i => c - d i - τ / d i)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    apply Complex.zero_le_real.mpr
    have h := weight_admissible (hd₁ i) (hd₂ i) hτ hc₁ hc₂
    linarith only [h]
  have hS := congruence_posSemidef s hC
  have heq : (c : ℂ) • (1 : Matrix ι ι ℂ) - (realDiagonal d + congruence s C) =
      realDiagonal (fun i => c - d i - τ / d i) +
        congruence s ((τ : ℂ) • (1 : Matrix ι ι ℂ) - C) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one, realDiagonal, Matrix.diagonal_apply_eq, congruence_apply]
      have hs' : (s i : ℂ) * s i = (d i : ℂ)⁻¹ := by exact_mod_cast hs i
      push_cast
      linear_combination -(τ : ℂ) * hs'
    · simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        realDiagonal, congruence_apply, hij]
  rw [heq]
  exact hR.add hS

/-- Mixed weights between one and two preserve the complete clipped correlation defect. -/
theorem mixed_bound {U : Matrix ι ι ℂ} (hU : U.IsHermitian) (hUd : ∀ i, U i i = 1)
    (d : ι → ℝ) (hd₁ : ∀ i, 1 ≤ d i) (hd₂ : ∀ i, d i ≤ 2)
    {τ c : ℝ} (hτ : 0 ≤ τ) (hc₁ : 1 + τ ≤ c) (hc₂ : 2 + τ / 2 ≤ c) :
    defectEnergy τ U + ∑ i, d i ^ 2 ≤ energy c (weightedGram d U) := by
  let C := RiemannGaussian.HermitianRankTrace.specMap hU (fun x => min (x - 1) τ)
  let M := congruence (fun i => (Real.sqrt (d i))⁻¹) C
  let X := realDiagonal d + M
  obtain ⟨hC, hcap, hatt⟩ := centered_certificate hU τ
  have hX : X.IsHermitian := (realDiagonal_hermitian d).add (congruence_hermitian _ hC)
  have hadm := mixed_certificate_cap d hd₁ hd₂ hτ hc₁ hc₂ hcap
  have hdual := dual_bound (weightedGram_hermitian d hU) hX c hadm
  have hid := mixed_trace_identity d (fun i => lt_of_lt_of_le zero_lt_one (hd₁ i)) U C hUd
  have hcontract := inverseSqrt_square_le d hd₁ hC
  change 2 * (trace (X * weightedGram d U)).re - (trace (X * X)).re - ∑ i, d i ^ 2 =
    2 * (trace (C * (U - 1))).re - (trace (M * M)).re at hid
  change 2 * (trace (C * (U - 1))).re - (trace (C * C)).re = defectEnergy τ U at hatt
  change (trace (M * M)).re ≤ (trace (C * C)).re at hcontract
  linarith only [hdual, hid, hatt, hcontract]

/-- Select single and double weights independently on a finite family. -/
def binaryWeight (doubled : ι → Bool) (i : ι) : ℝ := if doubled i then 2 else 1

/-- The smallest cutoff justified by the two endpoint constraints. -/
def mixedCutoff (τ : ℝ) : ℝ := max (1 + τ) (2 + τ / 2)

/-- Every selection of doubled columns preserves the same spectral defect. -/
theorem binary_mixed_bound {U : Matrix ι ι ℂ} (hU : U.IsHermitian)
    (hUd : ∀ i, U i i = 1) (doubled : ι → Bool) (τ : ℝ≥0) :
    defectEnergy τ U + ∑ i, binaryWeight doubled i ^ 2 ≤
      energy (mixedCutoff τ) (weightedGram (binaryWeight doubled) U) := by
  apply mixed_bound hU hUd (binaryWeight doubled)
  · intro i; simp only [binaryWeight]; split <;> norm_num
  · intro i; simp only [binaryWeight]; split <;> norm_num
  · exact τ.coe_nonneg
  · exact le_max_left _ _
  · exact le_max_right _ _

end
end GaloisForLFunctions.HilbertMetric.Clipped
