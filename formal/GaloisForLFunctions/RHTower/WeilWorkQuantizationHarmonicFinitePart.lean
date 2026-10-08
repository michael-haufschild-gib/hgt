import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticForwardMean
import GaloisForLFunctions.RHTower.DirichletUniformAbel

/-!
# The finite part of the literal source harmonic sum

Ordinary convergence of the centered source series at `5 / 8` gives a
quantitative tail at `1`. Adding the Euler constant correction identifies
one fixed real finite part, with error bounded by a constant times `N ^ (-3 / 8)`.
-/

open Complex Filter Topology
open GaloisForLFunctions.RHTower

noncomputable section
namespace RHTower.WeilSpectral
open WeilWorkSettledPhase
variable {lam : ℕ → ℝ}

/-- The literal source harmonic sum, including its coefficient at one. -/
def quantizationHarmonicSum (lam : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (sourceCoeff lam n).re / n

/-- The centered ordinary Dirichlet value plus the Euler constant correction. -/
def quantizationHarmonicFinitePart (hW : WeilPositiveFull lam) : ℝ :=
  (dirichletSum (fun n => sourceCoeff lam (n + 1) - sourceCompletion hW 1) 1).re +
    (sourceCompletion hW 1).re * Real.eulerMascheroniConstant

private theorem sum_Icc_one_eq_range {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ n ∈ Finset.range N, f (n + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

theorem quantizationHarmonicSum_centered (hW : WeilPositiveFull lam) (N : ℕ) :
    (dirichletPartialSum
      (fun n => sourceCoeff lam (n + 1) - sourceCompletion hW 1) N 1).re =
        quantizationHarmonicSum lam N - (sourceCompletion hW 1).re * (harmonic N : ℝ) := by
  rw [quantizationHarmonicSum, sum_Icc_one_eq_range]
  have hh : (harmonic N : ℝ) = ∑ n ∈ Finset.range N, (1 : ℝ) / (n + 1) := by
    simp [harmonic, one_div]
  rw [hh, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [dirichletPartialSum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Complex.cpow_neg_one, ← div_eq_mul_inv, Complex.div_ofReal_re,
    Complex.sub_re, Nat.cast_add, Nat.cast_one, sub_div, mul_one_div]

private theorem harmonic_euler_error (N : ℕ) (hN : 1 ≤ N) :
    |(harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant| ≤ 1 / (N : ℝ) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
  have hhi := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N
  simp only [Real.eulerMascheroniSeq', if_neg (by omega : N ≠ 0)] at hlo
  simp only [Real.eulerMascheroniSeq] at hhi
  rw [abs_of_nonneg (by linarith)]
  have hlog : Real.log ((N : ℝ) + 1) - Real.log N ≤ 1 / (N : ℝ) := by
    rw [← Real.log_div (by positivity) hpos.ne']
    calc
      _ ≤ ((N : ℝ) + 1) / N - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / (N : ℝ) := by field_simp; ring
  linarith

/-- The centered harmonic tail is controlled by ordinary source convergence. -/
theorem quantization_centered_harmonic_tail (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ‖dirichletSum (fun n => sourceCoeff lam (n + 1) - sourceCompletion hW 1) 1 -
        dirichletPartialSum
          (fun n => sourceCoeff lam (n + 1) - sourceCompletion hW 1) N 1‖ ≤
            C * (N : ℝ) ^ (-(3 / 8 : ℝ)) := by
  let a : ℕ → ℂ := fun n => sourceCoeff lam (n + 1) - sourceCompletion hW 1
  have hconv := centered_forward_dirichletConvergesAt hW (s := (5 / 8 : ℂ)) (by norm_num)
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hconv.choose_spec.cauchySeq.isBounded_range
  have hbound : ∀ N, ‖dirichletPartialSum a N (5 / 8)‖ ≤ C :=
    fun N => hC _ (Set.mem_range_self N)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hbound 0)
  refine ⟨4 * C, by positivity, fun N hN => ?_⟩
  have ht := norm_dirichletSum_sub_partialSum_le hbound
    (s := 1) (by norm_num) (centered_forward_dirichletConvergesAt hW (by norm_num)) N
  have he : (1 : ℂ) - 5 / 8 = ((3 / 8 : ℝ) : ℂ) := by norm_num
  rw [he] at ht
  norm_num [Complex.norm_real, Real.norm_eq_abs] at ht
  have ht' : ‖dirichletSum a 1 - dirichletPartialSum a N 1‖ ≤
      4 * C * ((N : ℝ) + 1) ^ (-(3 / 8 : ℝ)) := by
    convert ht using 1; ring
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  exact ht'.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (y := (N : ℝ) + 1)
      (z := -(3 / 8 : ℝ)) hp (by linarith) (by norm_num)) (by positivity))

/-- The finite part and its power-saving error for every full-positive source. -/
theorem quantizationHarmonicFinitePart_error (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |quantizationHarmonicSum lam N - (sourceCompletion hW 1).re * Real.log N -
        quantizationHarmonicFinitePart hW| ≤ C * (N : ℝ) ^ (-(3 / 8 : ℝ)) := by
  obtain ⟨C, hC, htail⟩ := quantization_centered_harmonic_tail hW
  refine ⟨C + |(sourceCompletion hW 1).re|, by positivity, fun N hN => ?_⟩
  let L := dirichletSum (fun n => sourceCoeff lam (n + 1) - sourceCompletion hW 1) 1
  let b := (sourceCompletion hW 1).re
  have heq : quantizationHarmonicSum lam N - b * Real.log N -
      quantizationHarmonicFinitePart hW =
      ((dirichletPartialSum
        (fun n => sourceCoeff lam (n + 1) - sourceCompletion hW 1) N 1).re - L.re) +
      b * ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant) := by
    rw [quantizationHarmonicSum_centered]
    simp only [quantizationHarmonicFinitePart, L, b]
    ring
  have hp : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hinv : 1 / (N : ℝ) ≤ (N : ℝ) ^ (-(3 / 8 : ℝ)) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hp (by norm_num)
  have ht : |(dirichletPartialSum
      (fun n => sourceCoeff lam (n + 1) - sourceCompletion hW 1) N 1).re - L.re| ≤
      C * (N : ℝ) ^ (-(3 / 8 : ℝ)) := by
    calc
      _ ≤ ‖dirichletPartialSum
        (fun n => sourceCoeff lam (n + 1) - sourceCompletion hW 1) N 1 - L‖ :=
          Complex.abs_re_le_norm _
      _ ≤ _ := by rw [norm_sub_rev]; exact htail N hN
  rw [heq]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ C * (N : ℝ) ^ (-(3 / 8 : ℝ)) + |b| * (N : ℝ) ^ (-(3 / 8 : ℝ)) := by
      rw [abs_mul]
      exact add_le_add ht (mul_le_mul_of_nonneg_left
        ((harmonic_euler_error N hN).trans hinv) (abs_nonneg _))
    _ = _ := by ring

/-- The same fixed finite part is the ordinary limit of the renormalized sums. -/
theorem quantizationHarmonicFinitePart_tendsto (hW : WeilPositiveFull lam) :
    Tendsto (fun N : ℕ => quantizationHarmonicSum lam N -
      (sourceCompletion hW 1).re * Real.log N) atTop
        (𝓝 (quantizationHarmonicFinitePart hW)) := by
  obtain ⟨C, hC, hbound⟩ := quantizationHarmonicFinitePart_error hW
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero_norm'
    (eventually_atTop.2 ⟨1, fun N hN => ?_⟩)
    (by simpa only [mul_zero] using
      (tendsto_rpow_neg_nat_atTop (show (0 : ℝ) < 3 / 8 by norm_num)).const_mul C)
  simpa only [Real.norm_eq_abs, abs_abs] using hbound N hN

/-- The same finite part and rate hold at every real cutoff at least one. -/
theorem quantizationHarmonicFinitePart_real_error (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |quantizationHarmonicSum lam ⌊x⌋₊ - (sourceCompletion hW 1).re * Real.log x -
        quantizationHarmonicFinitePart hW| ≤ C * x ^ (-(3 / 8 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := quantizationHarmonicFinitePart_error hW
  let b := (sourceCompletion hW 1).re
  refine ⟨C / (2 : ℝ) ^ (-(3 / 8 : ℝ)) + 2 * |b|, by positivity, fun x hx => ?_⟩
  let N := ⌊x⌋₊
  have hN : 1 ≤ N := (Nat.le_floor_iff (by linarith : 0 ≤ x)).2 (by simpa)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hhalf : x / 2 ≤ (N : ℝ) := by linarith
  have hpow : (N : ℝ) ^ (-(3 / 8 : ℝ)) ≤
      x ^ (-(3 / 8 : ℝ)) / (2 : ℝ) ^ (-(3 / 8 : ℝ)) := by
    rw [← Real.div_rpow (by linarith : 0 ≤ x) (by norm_num)]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hhalf (by norm_num)
  have hlog0 : 0 ≤ Real.log x - Real.log N := by
    exact sub_nonneg.mpr (Real.log_le_log hNp hNx)
  have hlog : |Real.log x - Real.log N| ≤ 2 * x ^ (-(3 / 8 : ℝ)) := by
    rw [abs_of_nonneg hlog0, ← Real.log_div (by linarith : x ≠ 0) hNp.ne']
    calc
      _ ≤ x / N - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ ≤ 1 / (N : ℝ) := by rw [div_sub_one hNp.ne']; gcongr; linarith
      _ ≤ 2 / x := by apply (div_le_div_iff₀ hNp (by linarith)).2; nlinarith
      _ ≤ 2 * x ^ (-(3 / 8 : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hx (by norm_num)) (by norm_num)
  have heq : quantizationHarmonicSum lam N - b * Real.log x -
      quantizationHarmonicFinitePart hW =
      (quantizationHarmonicSum lam N - b * Real.log N - quantizationHarmonicFinitePart hW) -
        b * (Real.log x - Real.log N) := by ring
  change |quantizationHarmonicSum lam N - b * Real.log x -
    quantizationHarmonicFinitePart hW| ≤ _
  rw [heq]
  calc
    _ ≤ _ := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        (quantizationHarmonicSum lam N - b * Real.log N - quantizationHarmonicFinitePart hW)
        (b * (Real.log x - Real.log N))
    _ ≤ C * (x ^ (-(3 / 8 : ℝ)) / (2 : ℝ) ^ (-(3 / 8 : ℝ))) +
        |b| * (2 * x ^ (-(3 / 8 : ℝ))) := by
      rw [abs_mul]
      exact add_le_add ((hbound N hN).trans (mul_le_mul_of_nonneg_left hpow hC))
        (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
    _ = _ := by ring

end RHTower.WeilSpectral
