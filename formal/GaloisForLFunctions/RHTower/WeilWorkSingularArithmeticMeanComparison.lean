import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticReciprocalTail
import GaloisForLFunctions.RHTower.Sieve.DirichletMeanValueSharp

/-!
# Finite mean comparison for the literal reciprocal

Uniform tail control and subpower growth compare the actual reciprocal mean
with a finite Dirichlet polynomial. The estimate below is the finite analytic
step toward the actual mean law; it asserts no quotient boundedness.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower
open RHTower.Sieve

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem mean_square_comparison {F P : ℝ → ℂ} (hF : Continuous F)
    (hP : Continuous P) {T B E : ℝ} (hT : 0 < T) (hE : 0 ≤ E)
    (hFn : ∀ t ∈ Icc (0 : ℝ) T, ‖F t‖ ≤ B)
    (hPn : ∀ t ∈ Icc (0 : ℝ) T, ‖P t‖ ≤ 2 * B)
    (hFP : ∀ t ∈ Icc (0 : ℝ) T, ‖F t - P t‖ ≤ E) :
    |(∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) / T -
      (∫ t in (0 : ℝ)..T, ‖P t‖ ^ 2) / T| ≤ 3 * B * E := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := T) (f := fun t => ‖F t‖ ^ 2 - ‖P t‖ ^ 2)
    (C := 3 * B * E) (fun t ht => by
      have ht' : t ∈ Icc (0 : ℝ) T := by
        simpa only [Set.uIcc_of_le hT.le] using Set.uIoc_subset_uIcc ht
      rw [Real.norm_eq_abs, sq_sub_sq, abs_mul,
        abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), mul_comm]
      calc
        _ ≤ E * (3 * B) := mul_le_mul
          ((abs_norm_sub_norm_le _ _).trans (hFP t ht'))
          (by linarith [hFn t ht', hPn t ht'])
          (add_nonneg (norm_nonneg _) (norm_nonneg _)) hE
        _ = _ := by ring)
  have hFi : IntervalIntegrable (fun t => ‖F t‖ ^ 2) volume 0 T :=
    (hF.norm.pow 2).intervalIntegrable _ _
  have hPi : IntervalIntegrable (fun t => ‖P t‖ ^ 2) volume 0 T :=
    (hP.norm.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hFi hPi, Real.norm_eq_abs, sub_zero, abs_of_pos hT] at hi
  rw [← sub_div, abs_div, abs_of_pos hT, div_le_iff₀ hT]
  exact hi

/-- The same literal reciprocal admits a quantitative comparison of its
actual vertical mean with every finite ordinary-series approximant. -/
theorem exists_reciprocal_finite_mean_comparison {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        G s = cexp (-LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s)) ∧
      ∀ (α ε : ℝ), 1 / 2 < α → 0 < ε →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ (σ : ℝ), α < σ → ∀ (N : ℕ) (T : ℝ), 0 < T →
          |(∫ t in (0 : ℝ)..T, ‖G ((σ : ℂ) + t * I)‖ ^ 2) / T -
            (∫ t in (0 : ℝ)..T, ‖∑ n ∈ Finset.Icc 1 N,
              LSeries.term (producerMobius (fun n => if 2 ≤ n then lam n else 0))
                ((σ : ℂ) + t * I) n‖ ^ 2) / T| ≤
            K * (2 + T) ^ (2 * ε) * ((N : ℝ) + 1) ^ (α - σ) := by
  obtain ⟨G, hGd, hGL, htail⟩ := exists_reciprocal_uniform_tail hW
  refine ⟨G, hGd, hGL, fun α ε hα hε => ?_⟩
  obtain ⟨C, hC, htail⟩ := htail α ε hα hε
  refine ⟨3 * C ^ 2, by positivity, fun σ hσ N T hT => ?_⟩
  let F : ℝ → ℂ := fun t => G ((σ : ℂ) + t * I)
  let P : ℝ → ℂ := fun t => ∑ n ∈ Finset.Icc 1 N,
    LSeries.term (producerMobius (fun n => if 2 ≤ n then lam n else 0))
      ((σ : ℂ) + t * I) n
  let B : ℝ := C * (2 + T) ^ ε
  let E : ℝ := B * ((N : ℝ) + 1) ^ (α - σ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hE_le : E ≤ B := by
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos
        (by have := Nat.cast_nonneg (α := ℝ) N; linarith : 1 ≤ (N : ℝ) + 1)
        (by linarith)) hB).trans_eq (mul_one B)
  have hh : ∀ t ∈ Icc (0 : ℝ) T, (2 + |t|) ^ ε ≤ (2 + T) ^ ε := by
    intro t ht
    rw [abs_of_nonneg ht.1]
    exact Real.rpow_le_rpow (by linarith [ht.1]) (by linarith [ht.2]) hε.le
  have hFc : Continuous F := by
    exact hGd.continuousOn.comp_continuous
      (f := fun t : ℝ => (σ : ℂ) + t * I) (by fun_prop)
      (fun t => by simpa using hα.trans hσ)
  have hPc : Continuous P := by
    apply continuous_finsetSum
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    have hn0' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    simp_rw [LSeries.term_of_ne_zero hn0, div_eq_mul_inv, ← Complex.cpow_neg]
    exact continuous_const.mul
      ((by fun_prop : Continuous (fun t : ℝ => -((σ : ℂ) + t * I))).const_cpow
        (Or.inl hn0'))
  have hFn : ∀ t ∈ Icc (0 : ℝ) T, ‖F t‖ ≤ B := by
    intro t ht
    have h := htail σ hσ 0 t
    simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.sum_empty,
      sub_zero, Nat.cast_zero, zero_add, Real.one_rpow, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hh t ht) hC)
  have hFP : ∀ t ∈ Icc (0 : ℝ) T, ‖F t - P t‖ ≤ E := by
    intro t ht
    exact (htail σ hσ N t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hh t ht) hC) (by positivity))
  have hPn : ∀ t ∈ Icc (0 : ℝ) T, ‖P t‖ ≤ 2 * B := by
    intro t ht
    have h := norm_sub_le (F t) (F t - P t)
    rw [sub_sub_cancel] at h
    linarith [hFn t ht, hFP t ht, hE_le]
  have hmean := mean_square_comparison hFc hPc hT hE hFn hPn hFP
  change |(∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) / T -
    (∫ t in (0 : ℝ)..T, ‖P t‖ ^ 2) / T| ≤ _
  convert hmean using 1
  dsimp [E, B]
  rw [show 2 * ε = ε + ε by ring, Real.rpow_add (by linarith : 0 < 2 + T)]
  ring

private theorem tendsto_floor_tail_bound {K a b : ℝ} (hK : 0 ≤ K)
    (ha : a < 0) (hb : 0 ≤ b) (hab : b + a / 2 < 0) :
    Tendsto (fun T : ℝ => K * (2 + T) ^ b *
      ((⌊T ^ (1 / 2 : ℝ)⌋₊ : ℝ) + 1) ^ a) atTop (𝓝 0) := by
  have hp : Tendsto (fun T : ℝ => T ^ (b + a / 2)) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hab)
  have hlim := hp.const_mul (K * 3 ^ b)
  simp only [mul_zero] at hlim
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 1] with T hT
    positivity
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have hT0 : 0 < T := by linarith
    have hbase : (2 + T) ^ b ≤ (3 * T) ^ b :=
      Real.rpow_le_rpow (by linarith) (by linarith) hb
    have hfloor : ((⌊T ^ (1 / 2 : ℝ)⌋₊ : ℝ) + 1) ^ a ≤ (T ^ (1 / 2 : ℝ)) ^ a :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (Nat.lt_floor_add_one _).le ha.le
    calc
      _ ≤ K * (3 * T) ^ b * (T ^ (1 / 2 : ℝ)) ^ a :=
        mul_le_mul (mul_le_mul_of_nonneg_left hbase hK) hfloor
          (by positivity) (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) hT0.le, ← Real.rpow_mul hT0.le,
          show (1 / 2 : ℝ) * a = a / 2 by ring, Real.rpow_add hT0]
        ring

/-- A growing polynomial of length `floor(sqrt(T))` approximates the
actual reciprocal mean square with an error tending to zero. -/
theorem exists_reciprocal_mean_approximation {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        G s = cexp (-LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s)) ∧
      ∀ σ : ℝ, 1 / 2 < σ →
        Tendsto (fun T : ℝ =>
          (∫ t in (0 : ℝ)..T, ‖G ((σ : ℂ) + t * I)‖ ^ 2) / T -
          (∫ t in (0 : ℝ)..T, ‖∑ n ∈ Finset.Icc 1 ⌊T ^ (1 / 2 : ℝ)⌋₊,
            LSeries.term (producerMobius (fun n => if 2 ≤ n then lam n else 0))
              ((σ : ℂ) + t * I) n‖ ^ 2) / T) atTop (𝓝 0) := by
  obtain ⟨G, hGd, hGL, hmean⟩ := exists_reciprocal_finite_mean_comparison hW
  refine ⟨G, hGd, hGL, fun σ hσ => ?_⟩
  let α : ℝ := (σ + 1 / 2) / 2
  let ε : ℝ := (σ - α) / 8
  have hα : 1 / 2 < α := by dsimp [α]; linarith
  have hασ : α < σ := by dsimp [α]; linarith
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨K, hK, hbound⟩ := hmean α ε hα hε
  refine squeeze_zero_norm' ?_ (tendsto_floor_tail_bound hK
    (by linarith : α - σ < 0) (by positivity : 0 ≤ 2 * ε)
    (by dsimp [ε]; linarith : 2 * ε + (α - σ) / 2 < 0))
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [Real.norm_eq_abs]
  exact hbound σ hασ _ T hT

end RHTower.WeilSingularArithmetic
