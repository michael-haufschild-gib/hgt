import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralDualExpansion
import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError

/-!
# Finite truncation of the general reflected Gaussian AFE edge

On `0 < Re s < 1`, the fixed left contour gives coefficient decay
`(n+1)^{-(2-Re s)}`.  The reflected series therefore has an explicit
`p`-series tail.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter

/-- The exact `n`-th coefficient of the reflected Gaussian AFE edge. -/
def smoothAFEZetaDualCoefficientGeneral (s : ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  (zetaChi s * (n + 1 : ℂ) ^ (s - 1)) *
    smoothAFEZetaDualCutoffGeneral s (1 / ((n + 1 : ℝ) * x))

/-- Pointwise `p`-series majorant for the general reflected coefficient. -/
theorem exists_norm_smoothAFEZetaDualCoefficientGeneral_le
    {x : ℝ} (hx : 0 < x) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖smoothAFEZetaDualCoefficientGeneral s x n‖ ≤
        K * (1 / (n + 1 : ℝ) ^ (2 - s.re)) := by
  obtain ⟨C, hC0, hC⟩ := norm_zetaChi_add_left_one_le h0 h1
  let G : ℝ := ∫ v : ℝ,
    (1 + |s.im| + |v|) ^ 2 * Real.exp (-(v ^ 2))
  let K : ℝ := (1 / (2 * Real.pi)) * x⁻¹ * Real.exp 1 * C * G
  have hgauss : Integrable (fun v : ℝ =>
      (1 + |s.im| + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by
    simpa only [add_assoc] using integrable_shifted_pow_mul_exp_neg_sq (1 + |s.im|) 2
  have hG0 : 0 ≤ G := integral_nonneg fun _ => by positivity
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK0, fun n => ?_⟩
  let D : ℝ :=
    (1 / (n + 1 : ℝ) ^ (2 - s.re)) * x⁻¹ * Real.exp 1 * C
  have hdom : Integrable (fun v : ℝ =>
      D * ((1 + |s.im| + |v|) ^ 2 * Real.exp (-(v ^ 2)))) :=
    hgauss.const_mul D
  have hint :
      ‖∫ v : ℝ, smoothAFEZetaReflectedTerm s x n
          ((-1 : ℂ) + (v : ℂ) * I)‖ ≤ D * G := by
    have hint0 := norm_integral_le_of_norm_le hdom
      (Filter.Eventually.of_forall fun v => by
        simpa only [D] using
          norm_smoothAFEZetaReflectedTerm_general_left_one_le hx hC n v)
    calc
      ‖∫ v : ℝ, smoothAFEZetaReflectedTerm s x n
          ((-1 : ℂ) + (v : ℂ) * I)‖
        ≤ ∫ v : ℝ, D *
            ((1 + |s.im| + |v|) ^ 2 * Real.exp (-(v ^ 2))) := hint0
      _ = D * G := by
        rw [integral_const_mul]
  have heq : smoothAFEZetaDualCoefficientGeneral s x n =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ v : ℝ, smoothAFEZetaReflectedTerm s x n
          ((-1 : ℂ) + (v : ℂ) * I) := by
    unfold smoothAFEZetaDualCoefficientGeneral smoothAFEZetaDualCutoffGeneral
    rw [Complex.real_smul]
    calc
      (zetaChi s * (n + 1 : ℂ) ^ (s - 1)) *
          ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ∫ v : ℝ, smoothAFEDualRatioIntegrand s
              (1 / ((n + 1 : ℝ) * x)) (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ((zetaChi s * (n + 1 : ℂ) ^ (s - 1)) *
            ∫ v : ℝ, smoothAFEDualRatioIntegrand s
              (1 / ((n + 1 : ℝ) * x)) (((-1 : ℝ) : ℂ) + (v : ℂ) * I)) := by ring
      _ = (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ∫ v : ℝ, smoothAFEZetaReflectedTerm s x n
            ((-1 : ℂ) + (v : ℂ) * I) := by
        rw [integral_smoothAFEZetaReflectedTerm_general_left_one_eq hx h0 h1]
        norm_num
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ v : ℝ, smoothAFEZetaReflectedTerm s x n
          ((-1 : ℂ) + (v : ℂ) * I)‖
      ≤ (1 / (2 * Real.pi)) * (D * G) := by
        gcongr
    _ = K * (1 / (n + 1 : ℝ) ^ (2 - s.re)) := by
      dsimp only [D, K]
      ring

/-- Explicit tail bound for the reflected Gaussian AFE series. -/
theorem exists_smoothAFE_dual_tail_le
    {x : ℝ} (hx : 0 < x) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℕ, 1 ≤ L →
      ∑' j : ℕ,
          ‖smoothAFEZetaDualCoefficientGeneral s x (j + L)‖ ≤
        K * (((L : ℝ)) ^ (s.re - 1) / (1 - s.re)) := by
  obtain ⟨K, hK0, hK⟩ :=
    exists_norm_smoothAFEZetaDualCoefficientGeneral_le hx h0 h1
  refine ⟨K, hK0, fun L hL => ?_⟩
  have hp : 1 < 2 - s.re := by linarith
  have hbase : Summable (fun j : ℕ =>
      (((j + L + 1 : ℕ) : ℝ)) ^ (-(2 - s.re))) := by
    have hseries : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(2 - s.re))) := by
      rw [Real.summable_nat_rpow]
      linarith
    have hshift := (summable_nat_add_iff (L + 1)).mpr hseries
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift
  have hmajor : Summable (fun j : ℕ =>
      K * (((j + L + 1 : ℕ) : ℝ)) ^ (-(2 - s.re))) :=
    hbase.mul_left K
  have hle : ∀ j : ℕ,
      ‖smoothAFEZetaDualCoefficientGeneral s x (j + L)‖ ≤
        K * (((j + L + 1 : ℕ) : ℝ)) ^ (-(2 - s.re)) := by
    intro j
    calc
      ‖smoothAFEZetaDualCoefficientGeneral s x (j + L)‖
          ≤ K * (1 / (j + L + 1 : ℝ) ^ (2 - s.re)) := by
            simpa only [Nat.cast_add, Nat.cast_one] using hK (j + L)
      _ = K * (((j + L + 1 : ℕ) : ℝ)) ^ (-(2 - s.re)) := by
        push_cast
        rw [one_div, Real.rpow_neg (by positivity : (0 : ℝ) ≤ j + L + 1)]
  have hsummable := Summable.of_nonneg_of_le (fun j => norm_nonneg _) hle hmajor
  calc
    ∑' j : ℕ, ‖smoothAFEZetaDualCoefficientGeneral s x (j + L)‖
        ≤ ∑' j : ℕ, K * (((j + L + 1 : ℕ) : ℝ)) ^ (-(2 - s.re)) :=
          hsummable.tsum_le_tsum hle hmajor
    _ = K * ∑' j : ℕ, (((j + L + 1 : ℕ) : ℝ)) ^ (-(2 - s.re)) :=
      tsum_mul_left
    _ ≤ K * (((L : ℝ)) ^ (1 - (2 - s.re)) / ((2 - s.re) - 1)) := by
      exact mul_le_mul_of_nonneg_left (Sieve.tsum_tail_rpow_neg_le hp hL) hK0
    _ = K * (((L : ℝ)) ^ (s.re - 1) / (1 - s.re)) := by ring_nf

/-- The reflected Gaussian AFE edge is a finite Dirichlet polynomial with an
explicit pointwise remainder. -/
theorem exists_smoothAFEZetaDualMellinGeneral_sub_head_le
    {x : ℝ} (hx : 0 < x) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℕ, 1 ≤ L →
      ‖smoothAFEZetaDualMellinGeneral s x -
          ∑ n ∈ Finset.range L, smoothAFEZetaDualCoefficientGeneral s x n‖ ≤
        K * (((L : ℝ)) ^ (s.re - 1) / (1 - s.re)) := by
  obtain ⟨K, hK0, hK⟩ := exists_smoothAFE_dual_tail_le hx h0 h1
  refine ⟨K, hK0, fun L hL => ?_⟩
  have hsum : Summable (smoothAFEZetaDualCoefficientGeneral s x) := by
    obtain ⟨C, hC0, hC⟩ :=
      exists_norm_smoothAFEZetaDualCoefficientGeneral_le hx h0 h1
    have hbase := summable_smoothAFEZetaMajorant
      (p := 2 - s.re) (by linarith)
    exact Summable.of_norm_bounded (hbase.mul_left C) hC
  have hsplit := hsum.sum_add_tsum_nat_add L
  have hdiff : smoothAFEZetaDualMellinGeneral s x -
      ∑ n ∈ Finset.range L, smoothAFEZetaDualCoefficientGeneral s x n =
        ∑' j : ℕ, smoothAFEZetaDualCoefficientGeneral s x (j + L) := by
    rw [smoothAFEZetaDualMellinGeneral_eq_tsum hx h0 h1]
    change ((∑' n : ℕ, smoothAFEZetaDualCoefficientGeneral s x n) -
      ∑ n ∈ Finset.range L, smoothAFEZetaDualCoefficientGeneral s x n) = _
    rw [← hsplit]
    abel
  rw [hdiff]
  have htail : Summable (fun j : ℕ =>
      smoothAFEZetaDualCoefficientGeneral s x (j + L)) := by
    have h := hsum.comp_injective (add_left_injective L)
    simpa [Function.comp_def, Nat.add_comm] using h
  exact le_trans (norm_tsum_le_tsum_norm htail.norm) (hK L hL)

end RHTower
