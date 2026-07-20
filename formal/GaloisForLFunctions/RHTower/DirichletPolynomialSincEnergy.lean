import GaloisForLFunctions.RHTower.BohrMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Finite-time sinc energy of a Dirichlet polynomial

The symmetric time average of a finite Dirichlet polynomial has an exact diagonal plus sinc-kernel
decomposition.  Its failure to have independent-phase second moment is therefore bounded by one
explicit weighted near-collision energy.  Applied to the coefficient vector of a high power, this
is the deterministic arithmetic quantity behind critical prime-log large deviations.
-/

open Complex MeasureTheory intervalIntegral

namespace RHTower

noncomputable section

/-- The normalized symmetric cosine kernel is the unnormalized real sinc function. -/
theorem cosInt_symmetric_div_eq_sinc (T L : ℝ) (hT : 0 < T) :
    cosInt L (-T) (2 * T) / (2 * T) = Real.sinc (L * T) := by
  by_cases hL : L = 0
  · subst L
    simp [cosInt_zero, hT.ne']
  · rw [cosInt, if_neg hL, Real.sinc_of_ne_zero (mul_ne_zero hL hT.ne')]
    rw [show -T + 2 * T = T by ring, mul_neg, Real.sin_neg]
    field_simp [hL, hT.ne']
    ring

/-- Sinc has both the trivial unit bound and the inverse-frequency bound. -/
theorem abs_sinc_mul_le_min (T L : ℝ) (hT : 0 < T) (hL : L ≠ 0) :
    |Real.sinc (L * T)| ≤ min 1 (1 / (T * |L|)) := by
  rw [le_min_iff]
  constructor
  · exact Real.abs_sinc_le_one _
  · rw [Real.sinc_of_ne_zero (mul_ne_zero hL hT.ne'), abs_div, abs_mul,
      abs_of_pos hT, mul_comm]
    simpa [mul_comm] using
      (div_le_div_of_nonneg_right (Real.abs_sin_le_one (L * T))
        (mul_pos hT (abs_pos.mpr hL)).le)

/-- On an arbitrary positive-length window, the unnormalized cosine kernel is bounded by the
window length.  This is the finite-window counterpart of the unit bound for sinc. -/
theorem abs_cosInt_le_window (L A U : ℝ) (hU : 0 ≤ U) :
    |cosInt L A U| ≤ U := by
  by_cases hL : L = 0
  · subst L
    simpa [cosInt_zero, abs_of_nonneg hU]
  · rw [cosInt, if_neg hL, abs_div]
    have hnum := Real.abs_sin_sub_sin_le (L * (A + U)) (L * A)
    have hdiff : |L * (A + U) - L * A| = |L| * U := by
      rw [show L * (A + U) - L * A = L * U by ring, abs_mul, abs_of_nonneg hU]
    have hLpos : 0 < |L| := abs_pos.mpr hL
    rw [hdiff] at hnum
    calc
      |Real.sin (L * (A + U)) - Real.sin (L * A)| / |L| ≤
          (|L| * U) / |L| :=
        div_le_div_of_nonneg_right hnum hLpos.le
      _ = U := by field_simp

/-- The normalized arbitrary-window cosine kernel has the exact two universal bounds: one from
the window mass, and one from cancellation of a nonzero frequency. -/
theorem abs_cosInt_div_le_min (L A U : ℝ) (hU : 0 < U) (hL : L ≠ 0) :
    |cosInt L A U / U| ≤ min 1 (2 / (U * |L|)) := by
  rw [le_min_iff, abs_div, abs_of_pos hU]
  constructor
  · calc
      |cosInt L A U| / U ≤ U / U :=
        div_le_div_of_nonneg_right (abs_cosInt_le_window L A U hU.le) hU.le
      _ = 1 := div_self hU.ne'
  · have hfreq := abs_cosInt_le L A U hL
    calc
      |cosInt L A U| / U ≤ (2 / |L|) / U :=
        div_le_div_of_nonneg_right hfreq hU.le
      _ = 2 / (U * |L|) := by ring

/-- The weighted logarithmic near-collision energy of a finite coefficient vector at time `T`. -/
def dpolySincOffDiagonalEnergy (a : ℕ → ℝ) (s : Finset ℕ) (T : ℝ) : ℝ :=
  ∑ m ∈ s, ∑ n ∈ s.erase m,
    |a m * a n| * min 1 (1 / (T * |Real.log n - Real.log m|))

/-- The weighted logarithmic near-collision energy on a positive window of length `U`.  Its
frequency cutoff is `1/U`; the window location affects the exact phases but not this envelope. -/
def dpolyWindowOffDiagonalEnergy (a : ℕ → ℝ) (s : Finset ℕ) (U : ℝ) : ℝ :=
  ∑ m ∈ s, ∑ n ∈ s.erase m,
    |a m * a n| * min 1 (2 / (U * |Real.log n - Real.log m|))

/-- Exact normalized moment decomposition on an arbitrary positive window. -/
theorem secondMoment_window_kernel
    (a : ℕ → ℝ) (s : Finset ℕ) (A U : ℝ) (hU : 0 < U) :
    (∫ t in A..(A + U), ‖dpoly a s t‖ ^ 2) / U =
      (∑ m ∈ s, (a m) ^ 2) +
        ∑ m ∈ s, ∑ n ∈ s.erase m,
          a m * a n * (cosInt (Real.log n - Real.log m) A U / U) := by
  rw [secondMoment_meanValue, add_div, mul_div_cancel_left₀ _ hU.ne']
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- On every shifted window, the deterministic second-moment error is bounded by the same local
multiplicative near-collision energy; only the window length enters the envelope. -/
theorem secondMoment_window_independence_error_le
    (a : ℕ → ℝ) (s : Finset ℕ) (A U : ℝ) (hU : 0 < U)
    (hs : ∀ n ∈ s, 1 ≤ n) :
    |(∫ t in A..(A + U), ‖dpoly a s t‖ ^ 2) / U -
        ∑ m ∈ s, (a m) ^ 2| ≤
      dpolyWindowOffDiagonalEnergy a s U := by
  rw [secondMoment_window_kernel a s A U hU, add_sub_cancel_left]
  unfold dpolyWindowOffDiagonalEnergy
  calc
    |∑ m ∈ s, ∑ n ∈ s.erase m,
        a m * a n * (cosInt (Real.log n - Real.log m) A U / U)| ≤
        ∑ m ∈ s, |∑ n ∈ s.erase m,
          a m * a n * (cosInt (Real.log n - Real.log m) A U / U)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ s, ∑ n ∈ s.erase m,
        |a m * a n * (cosInt (Real.log n - Real.log m) A U / U)| := by
      apply Finset.sum_le_sum
      intro m hm
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ s, ∑ n ∈ s.erase m,
        |a m * a n| * min 1 (2 / (U * |Real.log n - Real.log m|)) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      rw [Finset.mem_erase] at hn
      have hlog : Real.log n - Real.log m ≠ 0 :=
        log_diff_ne_zero m n (hs m hm) (hs n hn.2) hn.1
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_cosInt_div_le_min (Real.log n - Real.log m) A U hU hlog) (abs_nonneg _)

/-- Exact symmetric finite-time moment decomposition: diagonal independent-phase mass plus the
sinc-weighted multiplicative collision spectrum. -/
theorem secondMoment_symmetric_sinc (a : ℕ → ℝ) (s : Finset ℕ) (T : ℝ) (hT : 0 < T) :
    (∫ t in (-T)..T, ‖dpoly a s t‖ ^ 2) / (2 * T) =
      (∑ m ∈ s, (a m) ^ 2) +
        ∑ m ∈ s, ∑ n ∈ s.erase m,
          a m * a n * Real.sinc ((Real.log n - Real.log m) * T) := by
  have hmean := secondMoment_meanValue a s (-T) (2 * T)
  rw [show -T + 2 * T = T by ring] at hmean
  rw [hmean]
  have hden : 2 * T ≠ 0 := by positivity
  rw [add_div, mul_div_cancel_left₀ _ hden]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    (a m * a n * cosInt (Real.log n - Real.log m) (-T) (2 * T)) / (2 * T) =
        a m * a n *
          (cosInt (Real.log n - Real.log m) (-T) (2 * T) / (2 * T)) := by ring
    _ = a m * a n * Real.sinc ((Real.log n - Real.log m) * T) := by
      rw [cosInt_symmetric_div_eq_sinc _ _ hT]

/-- The exact finite-time independence error is bounded by the explicit near-collision energy. -/
theorem secondMoment_symmetric_sinc_error_le
    (a : ℕ → ℝ) (s : Finset ℕ) (T : ℝ) (hT : 0 < T)
    (hs : ∀ n ∈ s, 1 ≤ n) :
    |(∫ t in (-T)..T, ‖dpoly a s t‖ ^ 2) / (2 * T) -
        ∑ m ∈ s, (a m) ^ 2| ≤
      dpolySincOffDiagonalEnergy a s T := by
  rw [secondMoment_symmetric_sinc a s T hT, add_sub_cancel_left]
  unfold dpolySincOffDiagonalEnergy
  calc
    |∑ m ∈ s, ∑ n ∈ s.erase m,
        a m * a n * Real.sinc ((Real.log n - Real.log m) * T)| ≤
        ∑ m ∈ s, |∑ n ∈ s.erase m,
          a m * a n * Real.sinc ((Real.log n - Real.log m) * T)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ s, ∑ n ∈ s.erase m,
        |a m * a n * Real.sinc ((Real.log n - Real.log m) * T)| := by
      apply Finset.sum_le_sum
      intro m hm
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ s, ∑ n ∈ s.erase m,
        |a m * a n| * min 1 (1 / (T * |Real.log n - Real.log m|)) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      rw [Finset.mem_erase] at hn
      have hlog : Real.log n - Real.log m ≠ 0 :=
        log_diff_ne_zero m n (hs m hm) (hs n hn.2) hn.1
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_sinc_mul_le_min T (Real.log n - Real.log m) hT hlog) (abs_nonneg _)

/-- Every symmetric finite-time even moment is exactly the independent Steinhaus diagonal plus
the sinc spectrum of multiplicative near-collisions between the `k`-fold convolution
coefficients. -/
theorem evenMoment_symmetric_sinc
    (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (k : ℕ)
    (T : ℝ) (hT : 0 < T) :
    (∫ t in (-T)..T, ‖dpoly a s t‖ ^ (2 * k)) / (2 * T) =
      (∑ m ∈ powSupport s k, (powConv a s k m) ^ 2) +
        ∑ m ∈ powSupport s k, ∑ n ∈ (powSupport s k).erase m,
          powConv a s k m * powConv a s k n *
            Real.sinc ((Real.log n - Real.log m) * T) := by
  have hrw : ∀ t : ℝ,
      ‖dpoly a s t‖ ^ (2 * k) =
        ‖dpoly (powConv a s k) (powSupport s k) t‖ ^ 2 := by
    intro t
    rw [show 2 * k = k * 2 by ring, pow_mul, ← norm_pow, dpoly_pow a s hs t k]
  rw [intervalIntegral.integral_congr (fun t _ => hrw t)]
  exact secondMoment_symmetric_sinc (powConv a s k) (powSupport s k) T hT

/-- **High-moment arithmetic reduction.**  The complete failure of deterministic finite-time
`2k`-th moments to match the independent-phase model is bounded by one explicit weighted local
multiplicative energy of the `k`-fold Dirichlet convolution. -/
theorem evenMoment_symmetric_independence_error_le
    (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (k : ℕ)
    (T : ℝ) (hT : 0 < T) :
    |(∫ t in (-T)..T, ‖dpoly a s t‖ ^ (2 * k)) / (2 * T) -
        ∫ ω, ‖∑ n ∈ s,
          (a n : ℂ) * SteinhausModel.X n ω‖ ^ (2 * k)
            ∂SteinhausModel.steinhausMeasure| ≤
      dpolySincOffDiagonalEnergy (powConv a s k) (powSupport s k) T := by
  rw [integral_normPow_dpoly a s hs k]
  have hrw : ∀ t : ℝ,
      ‖dpoly a s t‖ ^ (2 * k) =
        ‖dpoly (powConv a s k) (powSupport s k) t‖ ^ 2 := by
    intro t
    rw [show 2 * k = k * 2 by ring, pow_mul, ← norm_pow, dpoly_pow a s hs t k]
  rw [intervalIntegral.integral_congr (fun t _ => hrw t)]
  exact secondMoment_symmetric_sinc_error_le
    (powConv a s k) (powSupport s k) T hT (one_le_of_mem_powSupport hs k)

/-- Every shifted-window even moment is exactly the independent diagonal plus the finite-window
Fourier transform of the `k`-fold multiplicative collision spectrum. -/
theorem evenMoment_window_kernel
    (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (k : ℕ)
    (A U : ℝ) (hU : 0 < U) :
    (∫ t in A..(A + U), ‖dpoly a s t‖ ^ (2 * k)) / U =
      (∑ m ∈ powSupport s k, (powConv a s k m) ^ 2) +
        ∑ m ∈ powSupport s k, ∑ n ∈ (powSupport s k).erase m,
          powConv a s k m * powConv a s k n *
            (cosInt (Real.log n - Real.log m) A U / U) := by
  have hrw : ∀ t : ℝ,
      ‖dpoly a s t‖ ^ (2 * k) =
        ‖dpoly (powConv a s k) (powSupport s k) t‖ ^ 2 := by
    intro t
    rw [show 2 * k = k * 2 by ring, pow_mul, ← norm_pow, dpoly_pow a s hs t k]
  rw [intervalIntegral.integral_congr (fun t _ => hrw t)]
  exact secondMoment_window_kernel (powConv a s k) (powSupport s k) A U hU

/-- **Shifted high-moment arithmetic reduction.**  On any observation window, the complete
failure of deterministic `2k`-th moments to match the independent Steinhaus model is bounded by
the local multiplicative energy at resolution `1/U`.  This is the exact form needed on dyadic
windows `[T,2T]`, where the trivial coherent time `t=0` is absent. -/
theorem evenMoment_window_independence_error_le
    (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (k : ℕ)
    (A U : ℝ) (hU : 0 < U) :
    |(∫ t in A..(A + U), ‖dpoly a s t‖ ^ (2 * k)) / U -
        ∫ ω, ‖∑ n ∈ s,
          (a n : ℂ) * SteinhausModel.X n ω‖ ^ (2 * k)
            ∂SteinhausModel.steinhausMeasure| ≤
      dpolyWindowOffDiagonalEnergy (powConv a s k) (powSupport s k) U := by
  rw [integral_normPow_dpoly a s hs k]
  have hrw : ∀ t : ℝ,
      ‖dpoly a s t‖ ^ (2 * k) =
        ‖dpoly (powConv a s k) (powSupport s k) t‖ ^ 2 := by
    intro t
    rw [show 2 * k = k * 2 by ring, pow_mul, ← norm_pow, dpoly_pow a s hs t k]
  rw [intervalIntegral.integral_congr (fun t _ => hrw t)]
  exact secondMoment_window_independence_error_le
    (powConv a s k) (powSupport s k) A U hU (one_le_of_mem_powSupport hs k)

end

end RHTower
