import GaloisForLFunctions.RHTower.SmoothAFEZetaChiUniformMovingLeftLine
import GaloisForLFunctions.RHTower.GaussSpikeMass
import GaloisForLFunctions.RHTower.AbelTailLSeries

/-!
# Uniform approximation of the displaced reflected AFE head

The reflected Gaussian coefficient differs from its classical Dirichlet
coefficient by a conductor-small term.  Uniform moving-line control of
`zetaChi` cancels the displacement power, leaving the summable head exponent
`-1/2 + eta`.
-/

noncomputable section

namespace RHTower

open Complex

theorem norm_displaced_reflected_main_eq
    (d τ : ℝ) (n : ℕ) :
    ‖zetaChi (displacedLinePt d τ) *
        (n + 1 : ℂ) ^ (displacedLinePt d τ - 1)‖ =
      ‖zetaChi (displacedLinePt d τ)‖ *
        (n + 1 : ℝ) ^ (-(1 / 2 + d)) := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  rw [norm_mul]
  have hpow := Complex.norm_cpow_eq_rpow_re_of_pos hn
    (displacedLinePt d τ - 1)
  rw [show (n + 1 : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) by norm_num]
  rw [hpow]
  have hre : (displacedLinePt d τ - 1).re = -(1 / 2 + d) := by
    simp [displacedLinePt]
    ring
  rw [hre]
  norm_num

theorem exists_norm_smoothAFEZetaDualCoefficientGeneral_displaced_add_main_le_rpow
    {d₀ η : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ (τ : ℝ) {x : ℝ}, 0 < x → ∀ n : ℕ,
        ‖smoothAFEZetaDualCoefficientGeneral (displacedLinePt d τ) x n +
            (zetaChi (displacedLinePt d τ) *
              (n + 1 : ℂ) ^ (displacedLinePt d τ - 1))‖ ≤
          C * x ^ (d + η) / (max 1 |τ|) ^ η *
            (n + 1 : ℝ) ^ (-(1 / 2 - η)) := by
  obtain ⟨Cw, hCw, hweight⟩ :=
    exists_norm_smoothAFEZetaDualCoefficientGeneral_displaced_add_main_le
      hd₀0 hd₀half hη hηhalf
  obtain ⟨Kχ, hKχ, hchi⟩ :=
    exists_norm_zetaChi_moving_left_line_le_rpow hd₀0 hd₀half
  refine ⟨Cw * Kχ, mul_nonneg hCw hKχ, fun d hd hdd₀ τ {x} hx n => ?_⟩
  let q : ℝ := max 1 |τ|
  let r : ℝ := n + 1
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hr : 0 < r := by dsimp only [r]; exact_mod_cast Nat.succ_pos n
  have hbase := hweight d hd hdd₀ τ hx n
  have hchi' : ‖zetaChi (displacedLinePt d τ)‖ ≤ Kχ * q ^ d := by
    simpa only [displacedLinePt, q] using hchi d hd.le hdd₀ τ
  rw [norm_displaced_reflected_main_eq] at hbase
  have hmain :
      ‖zetaChi (displacedLinePt d τ)‖ * r ^ (-(1 / 2 + d)) ≤
        (Kχ * q ^ d) * r ^ (-(1 / 2 + d)) :=
    mul_le_mul_of_nonneg_right hchi' (Real.rpow_nonneg hr.le _)
  have hcorr : 0 ≤ Cw * ((r * x) ^ (d + η)) / q ^ (d + η) := by
    positivity
  calc
    ‖smoothAFEZetaDualCoefficientGeneral (displacedLinePt d τ) x n +
        zetaChi (displacedLinePt d τ) *
          (n + 1 : ℂ) ^ (displacedLinePt d τ - 1)‖
        ≤ (‖zetaChi (displacedLinePt d τ)‖ * r ^ (-(1 / 2 + d))) *
            (Cw * ((r * x) ^ (d + η)) / q ^ (d + η)) := by
          simpa only [r, q, Nat.cast_add, Nat.cast_one] using hbase
    _ ≤ ((Kχ * q ^ d) * r ^ (-(1 / 2 + d))) *
            (Cw * ((r * x) ^ (d + η)) / q ^ (d + η)) :=
          mul_le_mul_of_nonneg_right hmain hcorr
    _ = (Cw * Kχ) * x ^ (d + η) / q ^ η *
            r ^ (-(1 / 2 - η)) := by
          rw [Real.mul_rpow hr.le hx.le]
          rw [Real.rpow_add hq]
          have hqd : q ^ d ≠ 0 := (Real.rpow_pos_of_pos hq d).ne'
          have hqη : q ^ η ≠ 0 := (Real.rpow_pos_of_pos hq η).ne'
          field_simp [hqd, hqη]
          change Kχ * r ^ (-((1 + 2 * d) / 2)) * Cw * r ^ (d + η) =
            Kχ * Cw * r ^ (-((1 - 2 * η) / 2))
          calc
            Kχ * r ^ (-((1 + 2 * d) / 2)) * Cw * r ^ (d + η) =
                Kχ * Cw *
                  (r ^ (-((1 + 2 * d) / 2)) * r ^ (d + η)) := by ring
            _ = Kχ * Cw * r ^ (-((1 - 2 * η) / 2)) := by
              rw [← Real.rpow_add hr]
              congr 2
              ring
    _ = (Cw * Kχ) * x ^ (d + η) / (max 1 |τ|) ^ η *
            (n + 1 : ℝ) ^ (-(1 / 2 - η)) := by
          rfl

theorem exists_norm_sum_smoothAFEZetaDualCoefficientGeneral_displaced_add_main_le
    {d₀ η : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ (τ : ℝ) {x : ℝ}, 0 < x → ∀ L : ℕ,
        ‖∑ n ∈ Finset.range L,
            (smoothAFEZetaDualCoefficientGeneral (displacedLinePt d τ) x n +
              zetaChi (displacedLinePt d τ) *
                (n + 1 : ℂ) ^ (displacedLinePt d τ - 1))‖ ≤
          C * x ^ (d + η) / (max 1 |τ|) ^ η *
            (1 + (L : ℝ) ^ (1 / 2 + η) / (1 / 2 + η)) := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_norm_smoothAFEZetaDualCoefficientGeneral_displaced_add_main_le_rpow
      hd₀0 hd₀half hη hηhalf
  refine ⟨C, hC, fun d hd hdd₀ τ {x} hx L => ?_⟩
  let P : ℝ := C * x ^ (d + η) / (max 1 |τ|) ^ η
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hsum :
      ∑ r ∈ Finset.Icc 1 L, (r : ℝ) ^ (-(1 / 2 - η)) ≤
        1 + (L : ℝ) ^ (1 / 2 + η) / (1 / 2 + η) := by
    have h := sum_rpow_neg_head_le
      (c := 1 / 2 - η) (by linarith) (by linarith) L
    convert h using 1
    all_goals ring_nf
  calc
    ‖∑ n ∈ Finset.range L,
        (smoothAFEZetaDualCoefficientGeneral (displacedLinePt d τ) x n +
          zetaChi (displacedLinePt d τ) *
            (n + 1 : ℂ) ^ (displacedLinePt d τ - 1))‖
        ≤ ∑ n ∈ Finset.range L,
            P * (n + 1 : ℝ) ^ (-(1 / 2 - η)) := by
          apply norm_sum_le_of_le
          intro n hn
          simpa only [P] using hpoint d hd hdd₀ τ hx n
    _ = P * ∑ n ∈ Finset.range L,
            (n + 1 : ℝ) ^ (-(1 / 2 - η)) := by
          rw [Finset.mul_sum]
    _ = P * ∑ r ∈ Finset.Icc 1 L,
            (r : ℝ) ^ (-(1 / 2 - η)) := by
          congr 1
          simpa only [Nat.cast_add, Nat.cast_one] using
            sum_range_succ_eq_sum_Icc
              (fun r : ℕ => (r : ℝ) ^ (-(1 / 2 - η))) L
    _ ≤ P * (1 + (L : ℝ) ^ (1 / 2 + η) / (1 / 2 + η)) :=
          mul_le_mul_of_nonneg_left hsum hP
    _ = C * x ^ (d + η) / (max 1 |τ|) ^ η *
          (1 + (L : ℝ) ^ (1 / 2 + η) / (1 / 2 + η)) := by
          rfl

end RHTower
