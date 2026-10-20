import GaloisForLFunctions.BezoutValuationIncidence.PhaseUniformWindowSandwichAndQuadraticObservabilityHorizon
import GaloisForLFunctions.BezoutValuationIncidence.IteratedSuccessorPredictionAndReservePhaseLossSplit
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ShortWindowCorrelationDefectAndIsoStateClassification

/-!
# Window Poincaré inequality and long-window dissipation at every phase

The Bézout successor geometry is a period statement: on a complete common-return period the
Dirichlet energy of a response is `2L` times the successor reserve, and the reserve dominates
half the variance because `2μ(q) ≤ φ(q)` for `q ≥ 2`. Using the inverse `ℓ¹` inequality
`‖c‖₁² ≤ S_N Q_Sel(c)` of the window sandwich, the same laws hold on every window of length
`K` at every phase, with additive errors that are multiples of `S_N V`:

* `|D_W - 2K R| ≤ 6 S_N V` for the window Dirichlet energy `D_W` and successor reserve `R`;
* window Poincaré inequality `Σ_W (s - H)² ≤ D_W + 7 S_N V`, so the torus constant `1`
  survives on windows of length `≫ S_N ≈ N² log N` instead of `lcm(1..N)`;
* long-window dissipation `2 R_W ≤ 4H² - (K - 11 S_N) V` for the renormalized window defect.

On short windows the sign of the renormalized defect is decided by the endpoint states; beyond
the polynomial horizon `11 S_N` every non-flat row in `ker P` dissipates, whatever the endpoint
states. These bounds say nothing below that horizon.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. The successor reserve is blind to the unit shift -/

theorem selbergMultiplesCoord_sieveRowShift_of_two_le (N : ℕ) (c : ℕ → ℝ) (κ : ℝ) {e : ℕ}
    (he : 2 ≤ e) : selbergMultiplesCoord N (sieveRowShift c κ) e = selbergMultiplesCoord N c e := by
  unfold selbergMultiplesCoord sieveRowShift
  refine sum_congr rfl fun d hd => ?_
  have hd1 : d ≠ 1 := by
    rintro rfl
    have := Nat.le_of_dvd one_pos (mem_filter.mp hd).2
    omega
  simp [hd1]

/-- The successor reserve as a sum over the non-harmonic modes. -/
theorem sieveSuccessorReserve_eq_sum_Icc_two {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    sieveSuccessorReserve N c = ∑ e ∈ Icc 2 N,
      ((Nat.totient e : ℝ) - moebiusReal e) * selbergMultiplesCoord N c e ^ (2 : ℕ) :=
  selbergSubBezoutQuadraticForm_eq_Icc_two hN c

theorem sieveSuccessorReserve_sieveRowShift {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (κ : ℝ) :
    sieveSuccessorReserve N (sieveRowShift c κ) = sieveSuccessorReserve N c := by
  rw [sieveSuccessorReserve_eq_sum_Icc_two hN, sieveSuccessorReserve_eq_sum_Icc_two hN]
  exact sum_congr rfl fun e he => by
    rw [selbergMultiplesCoord_sieveRowShift_of_two_le N c κ (mem_Icc.mp he).1]

/-- Half-decorrelation: the reserve carries at least half the variance and at most twice it. -/
theorem half_sieveVariance_le_sieveSuccessorReserve {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    sieveVariance N c / 2 ≤ sieveSuccessorReserve N c ∧
      sieveSuccessorReserve N c ≤ 2 * sieveVariance N c := by
  rw [sieveSuccessorReserve_eq_sum_Icc_two hN]
  unfold sieveVariance
  rw [sum_div, mul_sum]
  constructor
  · refine sum_le_sum fun e he => ?_
    have h := (two_mul_moebiusReal_le_totient (mem_Icc.mp he).1).1
    have hsq := sq_nonneg (selbergMultiplesCoord N c e)
    nlinarith
  · refine sum_le_sum fun e he => ?_
    have h1 : (1 : ℝ) ≤ Nat.totient e := by
      exact_mod_cast Nat.totient_pos.mpr (by have := (mem_Icc.mp he).1; omega)
    have hmu : -1 ≤ moebiusReal e := by
      have := abs_moebius_le_one (n := e)
      unfold moebiusReal
      have : |((μ e : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast this
      linarith [neg_abs_le ((μ e : ℤ) : ℝ)]
    have hsq := sq_nonneg (selbergMultiplesCoord N c e)
    nlinarith

/-! ## §2. Window successor correlation and window Dirichlet energy -/

/-- The window successor correlation is `K Q_Bez` up to twice the squared `ℓ¹` norm. -/
theorem abs_shortWindowShiftedCorrelation_sub_le (N A K : ℕ) (c : ℕ → ℝ) :
    |shortWindowShiftedCorrelation N A K c - (K : ℝ) * bezoutCoprimeQuadraticForm N c| ≤
      2 * (∑ d ∈ Icc 1 N, |c d|) ^ 2 := by
  have hwin : shortWindowShiftedCorrelation N A K c =
      (∑ k ∈ Icc 1 (A + K), sieveSeq N c k * sieveSeq N c (k + 1)) -
        ∑ k ∈ Icc 1 A, sieveSeq N c k * sieveSeq N c (k + 1) :=
    (sum_Icc_one_add_sub_eq_sum_Icc A K _).symm
  rw [hwin, sum_sieveSeq_mul_succ_eq_main_add_sawtooth, sum_sieveSeq_mul_succ_eq_main_add_sawtooth]
  have h1 := abs_bezoutSawtoothRemainderForm_le_sq_sum_abs (A + K) N c
  have h2 := abs_bezoutSawtoothRemainderForm_le_sq_sum_abs A N c
  push_cast
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- Polarization of the window Dirichlet energy into two window squares and a correlation. -/
theorem shortWindowDirichletEnergy_eq_squares_sub_correlation (N A K : ℕ) (c : ℕ → ℝ) :
    shortWindowDirichletEnergy N A K c =
      (∑ k ∈ Icc (A + 1 + 1) (A + 1 + K), sieveSeq N c k ^ 2) +
        (∑ k ∈ Icc (A + 1) (A + K), sieveSeq N c k ^ 2) -
          2 * shortWindowShiftedCorrelation N A K c := by
  have hshift : (∑ k ∈ Icc (A + 1 + 1) (A + 1 + K), sieveSeq N c k ^ 2) =
      ∑ k ∈ Icc (A + 1) (A + K), sieveSeq N c (k + 1) ^ 2 := by
    rw [show A + 1 + K = A + K + 1 by omega, ← Finset.map_add_right_Icc, Finset.sum_map]
    rfl
  unfold shortWindowDirichletEnergy shortWindowShiftedCorrelation
  rw [hshift, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun k _ => by ring

/-- The window Dirichlet energy is invariant under the unit shift of the response. -/
theorem shortWindowDirichletEnergy_sieveRowShift {N : ℕ} (hN : 1 ≤ N) (A K : ℕ)
    (c : ℕ → ℝ) (κ : ℝ) :
    shortWindowDirichletEnergy N A K (sieveRowShift c κ) = shortWindowDirichletEnergy N A K c := by
  unfold shortWindowDirichletEnergy
  refine sum_congr rfl fun k _ => ?_
  rw [sieveSeq_sieveRowShift hN, sieveSeq_sieveRowShift hN]
  ring

/-- The squared `ℓ¹` norm of the harmonically centered row is at most `S_N V`. -/
theorem sum_abs_sieveRowShift_sq_le {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    (∑ d ∈ Icc 1 N, |sieveRowShift c (finiteHarmonicSum N c) d|) ^ 2 ≤
      sieveWindowObservabilityConstant N * sieveVariance N c := by
  have h := sum_abs_sq_le_observabilityConstant_mul_selberg N
    (sieveRowShift c (finiteHarmonicSum N c))
  rwa [selbergTotientDiagonalForm_sieveRowShift hN, sub_self, zero_pow two_ne_zero, zero_add] at h

/-- **Window reserve sandwich.** At every phase, `|D_W - 2K R| ≤ 6 S_N V`. -/
theorem abs_shortWindowDirichletEnergy_sub_reserve_le {N : ℕ} (hN : 1 ≤ N) (A K : ℕ)
    (c : ℕ → ℝ) :
    |shortWindowDirichletEnergy N A K c - 2 * (K : ℝ) * sieveSuccessorReserve N c| ≤
      6 * (sieveWindowObservabilityConstant N * sieveVariance N c) := by
  set c' := sieveRowShift c (finiteHarmonicSum N c) with hc'
  have hℓ := sum_abs_sieveRowShift_sq_le hN c
  rw [← hc'] at hℓ
  rw [← shortWindowDirichletEnergy_sieveRowShift hN A K c (finiteHarmonicSum N c), ← hc',
    shortWindowDirichletEnergy_eq_squares_sub_correlation,
    ← sieveSuccessorReserve_sieveRowShift hN c (finiteHarmonicSum N c), ← hc',
    sieveSuccessorReserve]
  have h1 := abs_window_sum_sq_sieveSeq_sub_le N (A + 1) K c'
  have h2 := abs_window_sum_sq_sieveSeq_sub_le N A K c'
  have h3 := abs_shortWindowShiftedCorrelation_sub_le N A K c'
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- Two-sided window Dirichlet coercivity: `(K - 6 S_N) V ≤ D_W ≤ (4K + 6 S_N) V`. -/
theorem shortWindowDirichletEnergy_bounds {N : ℕ} (hN : 1 ≤ N) (A K : ℕ) (c : ℕ → ℝ) :
    ((K : ℝ) - 6 * sieveWindowObservabilityConstant N) * sieveVariance N c ≤
        shortWindowDirichletEnergy N A K c ∧
      shortWindowDirichletEnergy N A K c ≤
        (4 * (K : ℝ) + 6 * sieveWindowObservabilityConstant N) * sieveVariance N c := by
  have h := abs_shortWindowDirichletEnergy_sub_reserve_le hN A K c
  obtain ⟨hlo, hhi⟩ := half_sieveVariance_le_sieveSuccessorReserve hN c
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [abs_le] at h
  constructor <;> nlinarith [h.1, h.2]

/-! ## §3. Window Poincaré inequality and long-window dissipation -/

/-- **Window Poincaré inequality.** At every phase,
`Σ_W (s - H)² ≤ D_W + 7 S_N V`: the torus constant `1` holds up to `7 S_N V`. -/
theorem window_poincare {N : ℕ} (hN : 1 ≤ N) (A K : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - finiteHarmonicSum N c) ^ 2) ≤
      shortWindowDirichletEnergy N A K c +
        7 * (sieveWindowObservabilityConstant N * sieveVariance N c) := by
  have hs := abs_window_sum_sq_sub_le_observabilityConstant hN A K c (finiteHarmonicSum N c)
  rw [sub_self, zero_pow two_ne_zero, zero_add, abs_le] at hs
  have hd := abs_shortWindowDirichletEnergy_sub_reserve_le hN A K c
  rw [abs_le] at hd
  have hlo := (half_sieveVariance_le_sieveSuccessorReserve hN c).1
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith [hs.1, hs.2, hd.1, hd.2]

/-- Multiplicative window Poincaré inequality for windows longer than `6 S_N`. -/
theorem window_poincare_mul {N : ℕ} (hN : 1 ≤ N) (A K : ℕ) (c : ℕ → ℝ)
    (hK : 6 * sieveWindowObservabilityConstant N < K) :
    ((K : ℝ) - 6 * sieveWindowObservabilityConstant N) *
        (∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - finiteHarmonicSum N c) ^ 2) ≤
      ((K : ℝ) + sieveWindowObservabilityConstant N) * shortWindowDirichletEnergy N A K c := by
  have hs := abs_window_sum_sq_sub_le_observabilityConstant hN A K c (finiteHarmonicSum N c)
  rw [sub_self, zero_pow two_ne_zero, zero_add, abs_le] at hs
  have hd := (shortWindowDirichletEnergy_bounds hN A K c).1
  have hV : 0 ≤ sieveVariance N c :=
    sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hS := sieveWindowObservabilityConstant_nonneg N
  have hpos : 0 ≤ (K : ℝ) - 6 * sieveWindowObservabilityConstant N := by linarith
  calc ((K : ℝ) - 6 * sieveWindowObservabilityConstant N) *
        (∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - finiteHarmonicSum N c) ^ 2)
      ≤ ((K : ℝ) - 6 * sieveWindowObservabilityConstant N) *
          (((K : ℝ) + sieveWindowObservabilityConstant N) * sieveVariance N c) :=
        mul_le_mul_of_nonneg_left (by linarith [hs.2]) hpos
    _ = ((K : ℝ) + sieveWindowObservabilityConstant N) *
          (((K : ℝ) - 6 * sieveWindowObservabilityConstant N) * sieveVariance N c) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by linarith)

/-- **Long-window dissipation.** At every phase, `2 R_W ≤ 4 H² - (K - 11 S_N) V` for the
renormalized defect of the window `(A, A + K]`. -/
theorem two_mul_shortWindowRenormalizedDefect_le {N : ℕ} (hN : 1 ≤ N) (A K : ℕ) (c : ℕ → ℝ) :
    2 * shortWindowRenormalizedDefect N A K c ≤
      4 * finiteHarmonicSum N c ^ 2 -
        ((K : ℝ) - 11 * sieveWindowObservabilityConstant N) * sieveVariance N c := by
  set H := finiteHarmonicSum N c
  set c' := sieveRowShift c H with hc'
  set ℓ := ∑ d ∈ Icc 1 N, |c' d| with hℓdef
  have hℓ : ℓ ^ 2 ≤ sieveWindowObservabilityConstant N * sieveVariance N c :=
    sum_abs_sieveRowShift_sq_le hN c
  have hℓ0 : 0 ≤ ℓ := sum_nonneg fun _ _ => abs_nonneg _
  have hend : |sieveSeq N c' (A + K + 1)| ≤ ℓ := abs_sieveSeq_le_sum_abs N c' _
  have hstart : |sieveSeq N c' (A + 1)| ≤ ℓ := abs_sieveSeq_le_sum_abs N c' _
  have he := sieveSeq_sieveRowShift hN (A + K + 1) c H
  have hs := sieveSeq_sieveRowShift hN (A + 1) c H
  rw [← hc'] at he hs
  have hD := (shortWindowDirichletEnergy_bounds hN A K c).1
  rw [two_mul_shortWindowRenormalizedDefect_eq]
  -- boundary squares: `s² = (H + s')²`, with `|s'| ≤ ℓ`
  have hb : sieveSeq N c (A + K + 1) ^ 2 - sieveSeq N c (A + 1) ^ 2 ≤ 5 * ℓ ^ 2 + 4 * H ^ 2 := by
    have e1 : sieveSeq N c (A + K + 1) = sieveSeq N c' (A + K + 1) + H := by linarith
    have e2 : sieveSeq N c (A + 1) = sieveSeq N c' (A + 1) + H := by linarith
    rw [e1, e2]
    rw [abs_le] at hend hstart
    nlinarith [sq_nonneg (ℓ - 2 * |H|), abs_nonneg H, sq_abs H, abs_mul_abs_self H,
      mul_le_mul_of_nonneg_left hend.2 (abs_nonneg H), neg_abs_le H, le_abs_self H]
  nlinarith [hD, hb, hℓ]

/-- In `ker P`, every window longer than `11 S_N` is dissipative at every phase. -/
theorem shortWindowRenormalizedDefect_neg_of_harmonic_eq_zero {N : ℕ} (hN : 1 ≤ N) (A K : ℕ)
    (c : ℕ → ℝ) (hker : finiteHarmonicSum N c = 0)
    (hK : 11 * sieveWindowObservabilityConstant N < K) (hV : 0 < sieveVariance N c) :
    shortWindowRenormalizedDefect N A K c < 0 := by
  have h := two_mul_shortWindowRenormalizedDefect_le hN A K c
  rw [hker] at h
  have := mul_pos (sub_pos.mpr hK) hV
  nlinarith

end

end GaloisForLFunctions.BezoutValuationIncidence
