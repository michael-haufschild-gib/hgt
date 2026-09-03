import GaloisForLFunctions.RHTower.LegendreHalfSumEstimate

/-!
# The Laplace–Heine asymptotics of the Legendre polynomials

For `0 < φ < π` and `N ≥ 8`,

`|P_N(cos φ) − 2 C_N (2 sin φ)^{-1/2} cos((N + ½)φ − π/4)| ≤ 800 / (‖1 − e^{2iφ}‖ N)`,

with `C_N = binom(2N,N)/4^N ~ (πN)^{-1/2}`.  The convolution `P_N(cos φ) = Re[e^{-iNφ} T_N]`,
`T_N = Σ_{k≤N} C_k C_{N−k} ζ^k` (`ζ = e^{2iφ}`), splits into two halves each within `O(1/N)` of
`C_N (1 − ζ^{±1})^{-1/2}`, and `(1 − e^{2iφ})^{-1/2} = (2 sin φ)^{-1/2} e^{i(π/4 − φ/2)}`.
-/

open Finset Complex
open scoped BigOperators Real

namespace RHTower

namespace LegendreBoost

open RouteJProfile

/-- `ζ(φ) = e^{2iφ}`. -/
noncomputable def zetaPhase (φ : ℝ) : ℂ := cexp (((2 * φ : ℝ) : ℂ) * I)

theorem norm_zeta (φ : ℝ) : ‖zetaPhase φ‖ = 1 := by
  unfold zetaPhase
  exact Complex.norm_exp_ofReal_mul_I _

theorem zeta_mul_zeta_neg (φ : ℝ) : zetaPhase φ * zetaPhase (-φ) = 1 := by
  unfold zetaPhase
  rw [← Complex.exp_add]
  push_cast
  ring_nf
  exact Complex.exp_zero

theorem zeta_pow_sub (φ : ℝ) {N j : ℕ} (hj : j ≤ N) :
    zetaPhase φ ^ (N - j) = zetaPhase φ ^ N * zetaPhase (-φ) ^ j := by
  have h : zetaPhase φ ^ N = zetaPhase φ ^ (N - j) * zetaPhase φ ^ j := by rw [← pow_add, Nat.sub_add_cancel hj]
  rw [h, mul_assoc, ← mul_pow, zeta_mul_zeta_neg, one_pow, mul_one]

theorem zeta_ne_one {φ : ℝ} (h0 : 0 < φ) (hπ : φ < π) : zetaPhase φ ≠ 1 := by
  intro h
  have hre : (zetaPhase φ).re = 1 := by rw [h]; simp
  unfold zetaPhase at hre
  rw [Complex.exp_ofReal_mul_I_re] at hre
  obtain ⟨n, hn⟩ := Real.cos_eq_one_iff (2 * φ) |>.mp hre
  have h1 : (0 : ℝ) < n * (2 * π) := by rw [hn]; linarith
  have h2 : (n : ℝ) * (2 * π) < 1 * (2 * π) := by rw [hn]; linarith
  have hpi := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hn1 : (n : ℝ) < 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have : (0 : ℤ) < n := by exact_mod_cast hn0
  have : n < (1 : ℤ) := by exact_mod_cast hn1
  omega

theorem norm_one_sub_zeta_neg (φ : ℝ) : ‖1 - zetaPhase (-φ)‖ = ‖1 - zetaPhase φ‖ := by
  have hconj : zetaPhase (-φ) = starRingEnd ℂ (zetaPhase φ) := by
    unfold zetaPhase
    rw [← Complex.exp_conj]
    congr 1
    apply Complex.ext <;> simp
  rw [hconj, ← Complex.norm_conj (1 - zetaPhase φ)]
  congr 1
  simp

/-! ## The convolution sum and its split -/

/-- `T_N = Σ_{k ≤ N} C_k C_{N−k} ζ^k`. -/
noncomputable def convT (φ : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ range (N + 1), ((cb k * cb (N - k) : ℝ) : ℂ) * zetaPhase φ ^ k

theorem legendreConvCoeff_eq_convT (φ : ℝ) (N : ℕ) :
    legendreConvCoeff φ N = cexp (((-(N : ℝ) * φ : ℝ) : ℂ) * I) * convT φ N := by
  unfold legendreConvCoeff convT
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  dsimp only
  unfold zetaPhase
  rw [← Complex.exp_nat_mul]
  have hexp : cexp (((-(N : ℝ) * φ : ℝ) : ℂ) * I) * cexp ((k : ℂ) * (((2 * φ : ℝ) : ℂ) * I)) =
      cexp ((((k : ℝ) - ((N - k : ℕ) : ℝ)) * φ : ℝ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [← hexp]
  push_cast
  ring

/-- The half sum `Σ_{k<K} C_k C_{N−k} η^k`. -/
noncomputable def halfSum (η : ℂ) (N K : ℕ) : ℂ :=
  ∑ k ∈ range K, ((cb k * cb (N - k) : ℝ) : ℂ) * η ^ k

theorem convT_split (φ : ℝ) (N : ℕ) :
    convT φ N = halfSum (zetaPhase φ) N (N / 2) + zetaPhase φ ^ N * halfSum (zetaPhase (-φ)) N (N + 1 - N / 2) := by
  unfold convT halfSum
  rw [← sum_range_add_sum_Ico _ (by omega : N / 2 ≤ N + 1), sum_Ico_eq_sum_range, mul_sum]
  congr 1
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [show N / 2 + (N + 1 - N / 2 - 1 - j) = N - j by omega, show N - (N - j) = j by omega,
    zeta_pow_sub φ (by omega : j ≤ N)]
  push_cast
  ring

/-- **The convolution sum is within `O(1/N)` of its two boundary terms.** -/
theorem norm_convT_sub_le {φ : ℝ} (h0 : 0 < φ) (hπ : φ < π) {N : ℕ} (hN : 8 ≤ N) :
    ‖convT φ N - (cb N : ℂ) * ((1 - zetaPhase φ) ^ (-(1 / 2 : ℂ)) +
      zetaPhase φ ^ N * (1 - zetaPhase (-φ)) ^ (-(1 / 2 : ℂ)))‖ ≤ 800 / (‖1 - zetaPhase φ‖ * N) := by
  have hz1 := zeta_ne_one h0 hπ
  have hz1' : zetaPhase (-φ) ≠ 1 := by
    intro h
    apply hz1
    have := zeta_mul_zeta_neg φ
    rw [h, mul_one] at this
    exact this
  have hA := norm_halfSum_sub_le (norm_zeta φ) hz1 hN (K := N / 2) (by omega) (by omega)
  have hB := norm_halfSum_sub_le (norm_zeta (-φ)) hz1' hN (K := N + 1 - N / 2) (by omega) (by omega)
  rw [norm_one_sub_zeta_neg] at hB
  rw [convT_split]
  have hnz : ‖zetaPhase φ ^ N‖ = 1 := by rw [norm_pow, norm_zeta, one_pow]
  calc ‖halfSum (zetaPhase φ) N (N / 2) + zetaPhase φ ^ N * halfSum (zetaPhase (-φ)) N (N + 1 - N / 2) -
        (cb N : ℂ) * ((1 - zetaPhase φ) ^ (-(1 / 2 : ℂ)) + zetaPhase φ ^ N * (1 - zetaPhase (-φ)) ^ (-(1 / 2 : ℂ)))‖
      = ‖(halfSum (zetaPhase φ) N (N / 2) - (cb N : ℂ) * (1 - zetaPhase φ) ^ (-(1 / 2 : ℂ))) +
          zetaPhase φ ^ N * (halfSum (zetaPhase (-φ)) N (N + 1 - N / 2) -
            (cb N : ℂ) * (1 - zetaPhase (-φ)) ^ (-(1 / 2 : ℂ)))‖ := by congr 1; ring
    _ ≤ ‖halfSum (zetaPhase φ) N (N / 2) - (cb N : ℂ) * (1 - zetaPhase φ) ^ (-(1 / 2 : ℂ))‖ +
          ‖zetaPhase φ ^ N * (halfSum (zetaPhase (-φ)) N (N + 1 - N / 2) -
            (cb N : ℂ) * (1 - zetaPhase (-φ)) ^ (-(1 / 2 : ℂ)))‖ := norm_add_le _ _
    _ = ‖halfSum (zetaPhase φ) N (N / 2) - (cb N : ℂ) * (1 - zetaPhase φ) ^ (-(1 / 2 : ℂ))‖ +
          ‖halfSum (zetaPhase (-φ)) N (N + 1 - N / 2) - (cb N : ℂ) * (1 - zetaPhase (-φ)) ^ (-(1 / 2 : ℂ))‖ := by
        rw [norm_mul, hnz, one_mul]
    _ ≤ 400 / (‖1 - zetaPhase φ‖ * N) + 400 / (‖1 - zetaPhase φ‖ * N) := add_le_add hA hB
    _ = 800 / (‖1 - zetaPhase φ‖ * N) := by ring

/-! ## The closed form of `(1 − e^{±2iφ})^{-1/2}` -/

theorem one_sub_zeta_eq {φ : ℝ} (h0 : 0 < φ) (hπ : φ < π) :
    1 - zetaPhase φ = ((2 * Real.sin φ : ℝ) : ℂ) * cexp (((φ - π / 2 : ℝ) : ℂ) * I) := by
  set E := cexp ((φ : ℂ) * I) with hE
  have hE' : cexp (((φ - π / 2 : ℝ) : ℂ) * I) = -I * E := by
    rw [hE, Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
    push_cast
    linear_combination (Complex.sin (φ : ℂ)) * I_sq
  have h2 : ((2 * Real.sin φ : ℝ) : ℂ) = (cexp (-(φ : ℂ) * I) - E) * I := by
    rw [Complex.ofReal_mul, Complex.ofReal_sin, Complex.ofReal_ofNat, Complex.two_sin, hE]
  have h3 : zetaPhase φ = E * E := by
    unfold zetaPhase
    rw [hE, ← Complex.exp_add]
    push_cast
    ring_nf
  have h4 : cexp (-(φ : ℂ) * I) * E = 1 := by
    rw [hE, ← Complex.exp_add]
    ring_nf
    exact Complex.exp_zero
  rw [hE', h2, h3]
  linear_combination (-1 : ℂ) * h4 + (-(E ^ 2 - E * cexp (-(φ : ℂ) * I))) * I_sq

theorem one_sub_zeta_neg_eq {φ : ℝ} (h0 : 0 < φ) (hπ : φ < π) :
    1 - zetaPhase (-φ) = ((2 * Real.sin φ : ℝ) : ℂ) * cexp (((π / 2 - φ : ℝ) : ℂ) * I) := by
  set E := cexp ((φ : ℂ) * I) with hE
  set E' := cexp (-(φ : ℂ) * I) with hE'
  have hEx : cexp (((π / 2 - φ : ℝ) : ℂ) * I) = I * E' := by
    rw [hE', Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, Complex.cos_neg, Complex.sin_neg]
    push_cast
    linear_combination (Complex.sin (φ : ℂ)) * I_sq
  have h2 : ((2 * Real.sin φ : ℝ) : ℂ) = (E' - E) * I := by
    rw [Complex.ofReal_mul, Complex.ofReal_sin, Complex.ofReal_ofNat, Complex.two_sin, hE, hE']
  have h3 : zetaPhase (-φ) = E' * E' := by
    unfold zetaPhase
    rw [hE', ← Complex.exp_add]
    push_cast
    ring_nf
  have h4 : E' * E = 1 := by
    rw [hE, hE', ← Complex.exp_add]
    ring_nf
    exact Complex.exp_zero
  rw [hEx, h2, h3]
  linear_combination (-1 : ℂ) * h4 + (-(E' ^ 2 - E' * E)) * I_sq

theorem norm_one_sub_zeta {φ : ℝ} (h0 : 0 < φ) (hπ : φ < π) : ‖1 - zetaPhase φ‖ = 2 * Real.sin φ := by
  rw [one_sub_zeta_eq h0 hπ, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith [Real.sin_pos_of_pos_of_lt_pi h0 hπ])]

theorem one_sub_zeta_cpow {φ : ℝ} (h0 : 0 < φ) (hπ : φ < π) :
    (1 - zetaPhase φ) ^ (-(1 / 2 : ℂ)) =
      (((2 * Real.sin φ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (((π / 4 - φ / 2 : ℝ) : ℂ) * I) := by
  rw [one_sub_zeta_eq h0 hπ]
  have hr : 0 < 2 * Real.sin φ := by linarith [Real.sin_pos_of_pos_of_lt_pi h0 hπ]
  have hE0 : cexp (((φ - π / 2 : ℝ) : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  rw [MeixnerPollaczek.ofReal_pos_mul_cpow hr hE0]
  congr 1
  · rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hr.le]
  · rw [cpow_def_of_ne_zero hE0, Complex.log_exp]
    · congr 1
      push_cast
      ring
    · simp; linarith [Real.pi_pos]
    · simp; linarith [Real.pi_pos]

theorem one_sub_zeta_neg_cpow {φ : ℝ} (h0 : 0 < φ) (hπ : φ < π) :
    (1 - zetaPhase (-φ)) ^ (-(1 / 2 : ℂ)) =
      (((2 * Real.sin φ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (((φ / 2 - π / 4 : ℝ) : ℂ) * I) := by
  rw [one_sub_zeta_neg_eq h0 hπ]
  have hr : 0 < 2 * Real.sin φ := by linarith [Real.sin_pos_of_pos_of_lt_pi h0 hπ]
  have hE0 : cexp (((π / 2 - φ : ℝ) : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  rw [MeixnerPollaczek.ofReal_pos_mul_cpow hr hE0]
  congr 1
  · rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hr.le]
  · rw [cpow_def_of_ne_zero hE0, Complex.log_exp]
    · congr 1
      push_cast
      ring
    · simp; linarith [Real.pi_pos]
    · simp; linarith [Real.pi_pos]

/-! ## Laplace–Heine -/

/-- The main term `Re[e^{-iNφ} C_N ((1−ζ)^{-1/2} + ζ^N (1−ζ̄)^{-1/2})]`. -/
theorem re_main_term {φ : ℝ} (h0 : 0 < φ) (hπ : φ < π) (N : ℕ) :
    (cexp (((-(N : ℝ) * φ : ℝ) : ℂ) * I) * ((cb N : ℂ) * ((1 - zetaPhase φ) ^ (-(1 / 2 : ℂ)) +
      zetaPhase φ ^ N * (1 - zetaPhase (-φ)) ^ (-(1 / 2 : ℂ))))).re =
      2 * cb N * (2 * Real.sin φ) ^ (-(1 / 2 : ℝ)) * Real.cos (((N : ℝ) + 1 / 2) * φ - π / 4) := by
  rw [one_sub_zeta_cpow h0 hπ, one_sub_zeta_neg_cpow h0 hπ]
  set ψ : ℝ := ((N : ℝ) + 1 / 2) * φ - π / 4 with hψ
  have hz : zetaPhase φ ^ N = cexp (((2 * (N : ℝ) * φ : ℝ) : ℂ) * I) := by
    unfold zetaPhase
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have e1 : cexp (((-(N : ℝ) * φ : ℝ) : ℂ) * I) * cexp (((π / 4 - φ / 2 : ℝ) : ℂ) * I) =
      cexp (((-ψ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; rw [hψ]; push_cast; ring
  have e2 : cexp (((-(N : ℝ) * φ : ℝ) : ℂ) * I) * (cexp (((2 * (N : ℝ) * φ : ℝ) : ℂ) * I) *
      cexp (((φ / 2 - π / 4 : ℝ) : ℂ) * I)) = cexp ((ψ : ℂ) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; rw [hψ]; push_cast; ring
  rw [hz]
  have hexpand : cexp (((-(N : ℝ) * φ : ℝ) : ℂ) * I) * ((cb N : ℂ) *
      ((((2 * Real.sin φ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (((π / 4 - φ / 2 : ℝ) : ℂ) * I) +
        cexp (((2 * (N : ℝ) * φ : ℝ) : ℂ) * I) *
          ((((2 * Real.sin φ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (((φ / 2 - π / 4 : ℝ) : ℂ) * I)))) =
      ((cb N * (2 * Real.sin φ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (cexp (((-ψ : ℝ) : ℂ) * I) + cexp ((ψ : ℂ) * I)) := by
    rw [← e1, ← e2]
    push_cast
    ring
  rw [hexpand, Complex.re_ofReal_mul, Complex.add_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  ring

/-- **Laplace–Heine asymptotics of the Legendre polynomials:** for `0 < φ < π` and `N ≥ 8`,
`|P_N(cos φ) − 2 C_N (2 sin φ)^{-1/2} cos((N+½)φ − π/4)| ≤ 400 / (sin φ · N)`. -/
theorem legendre_laplaceHeine {φ : ℝ} (h0 : 0 < φ) (hπ : φ < π) {N : ℕ} (hN : 8 ≤ N) :
    |legendre N (Real.cos φ) -
      2 * cb N * (2 * Real.sin φ) ^ (-(1 / 2 : ℝ)) * Real.cos (((N : ℝ) + 1 / 2) * φ - π / 4)| ≤
      400 / (Real.sin φ * N) := by
  have hP : legendre N (Real.cos φ) = (cexp (((-(N : ℝ) * φ : ℝ) : ℂ) * I) * convT φ N).re := by
    have h := legendre_cos_eq_conv φ N
    rw [legendreConvCoeff_eq_convT] at h
    rw [← h, Complex.ofReal_re]
  rw [hP, ← re_main_term h0 hπ N, ← Complex.sub_re, ← mul_sub]
  have hb := norm_convT_sub_le h0 hπ hN
  rw [norm_one_sub_zeta h0 hπ] at hb
  calc |(cexp (((-(N : ℝ) * φ : ℝ) : ℂ) * I) * (convT φ N - (cb N : ℂ) *
        ((1 - zetaPhase φ) ^ (-(1 / 2 : ℂ)) + zetaPhase φ ^ N * (1 - zetaPhase (-φ)) ^ (-(1 / 2 : ℂ))))).re|
      ≤ ‖cexp (((-(N : ℝ) * φ : ℝ) : ℂ) * I) * (convT φ N - (cb N : ℂ) *
        ((1 - zetaPhase φ) ^ (-(1 / 2 : ℂ)) + zetaPhase φ ^ N * (1 - zetaPhase (-φ)) ^ (-(1 / 2 : ℂ))))‖ :=
        Complex.abs_re_le_norm _
    _ = ‖convT φ N - (cb N : ℂ) *
        ((1 - zetaPhase φ) ^ (-(1 / 2 : ℂ)) + zetaPhase φ ^ N * (1 - zetaPhase (-φ)) ^ (-(1 / 2 : ℂ)))‖ := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    _ ≤ 800 / (2 * Real.sin φ * N) := hb
    _ = 400 / (Real.sin φ * N) := by
        have hs := Real.sin_pos_of_pos_of_lt_pi h0 hπ
        have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        field_simp
        ring

end LegendreBoost

end RHTower
