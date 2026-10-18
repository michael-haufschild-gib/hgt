import GaloisForLFunctions.«arithmetic-positivity-theory».EnvelopeCriticalPrimeTransitionAndDilationGain

/-! Nonstationary Mellin low-frequency exclusion, dyadic harmonic `k^{-3}` summation,
and high-scale archimedean-to-Weil span coercivity (`APT-ROOT-SPAN-COERCIVITY`).

For the phase profile `Φ_N(v) = P(λ_N v) - P(N v)` and finite coefficient combinations
supported on arithmetic scales `N ≥ M ≥ 2`:
1. In the low-frequency band `|t| ≤ π M ≤ π N`, every harmonic frequency
   `|ω| ≥ 2 π N` has stationary-free phase derivative `|ω - t / v| ≥ |ω| / 2` and
   curvature `|t / v^2| ≤ (|ω| / 2) v^{-2}` on `v ≥ 1`.
2. The exact integration-by-parts majorant on `[1, ∞)` satisfies
   `2 / |ω| + (2 / |ω|) ∫_1^∞ (5/2) v^{-7/2} dv + (4 |t| / |ω|^2) ∫_1^∞ v^{-9/2} dv ≤ 5 / |ω|`.
3. Summing over harmonics `k ≥ 1` with `∑_{k ≥ 1} k^{-3} ≤ 3/2` bounds each phase
   Mellin readout by `D / N` with `D = 15 / π^3`, and Cauchy–Schwarz with
   `∑_{N ≥ M} N^{-2} ≤ 2 / M` bounds the low-frequency energy on `|t| ≤ η M` by `(A / 2) ∑ |b_N|^2`.
4. Combining the remaining high-frequency mass `(A / 2) ∑ |b_N|^2` with logarithmic
   Gamma growth and the uniform prime (`2 B ∑_{r ≥ 2} Λ(r)/r^2`) and polar (`6 J`)
   budgets yields the complete high-scale span coercivity lower bound
   `(c log M - C) ∑ |b_N|^2` with `c = A / 2 > 0`. -/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- In the low-frequency band `|t| ≤ π M` with `M ≤ N` and `|ω| ≥ 2 π N`, the phase
derivative `ω - t / v` on `v ≥ 1` has modulus at least `|ω| / 2`. -/
theorem abs_phase_deriv_ge_half_freq {ω t v : ℝ} {M N : ℕ}
    (hMN : M ≤ N) (hv : 1 ≤ v)
    (ht : |t| ≤ Real.pi * (M : ℝ))
    (hω : 2 * Real.pi * (N : ℝ) ≤ |ω|) :
    |ω| / 2 ≤ |ω - t / v| := by
  have hMN_R : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
  have hpi : 0 < Real.pi := Real.pi_pos
  have htv : |t / v| ≤ |t| := by
    rw [abs_div, abs_of_pos (by linarith)]
    exact div_le_self (abs_nonneg t) hv
  have ht_omega : |t / v| ≤ |ω| / 2 := by
    calc
      |t / v| ≤ |t| := htv
      _ ≤ Real.pi * (M : ℝ) := ht
      _ ≤ Real.pi * (N : ℝ) := mul_le_mul_of_nonneg_left hMN_R hpi.le
      _ ≤ |ω| / 2 := by linarith
  have htri : |ω| - |t / v| ≤ |ω - t / v| := abs_sub_abs_le_abs_sub ω (t / v)
  linarith

/-- Exact evaluation of the amplitude-derivative integral `∫_{1}^{∞} (5/2) v^{-7/2} dv = 1`. -/
theorem integral_Ioi_one_amplitude_deriv :
    (∫ v in Ioi (1 : ℝ), (5 / 2 : ℝ) * v ^ (-7 / 2 : ℝ)) = 1 := by
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
  norm_num

/-- Exact evaluation of the phase-curvature integral `∫_{1}^{∞} v^{-9/2} dv = 2 / 7`. -/
theorem integral_Ioi_one_curvature_weight :
    (∫ v in Ioi (1 : ℝ), v ^ (-9 / 2 : ℝ)) = 2 / 7 := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
  norm_num

/-- **Nonstationary Mellin Majorant Bound (`≤ 5 / |ω|`, Equation (5)).**
Whenever `|t| ≤ |ω| / 2` and `ω ≠ 0`, the integration-by-parts majorant on `[1, ∞)` is at
most `5 / |ω|`. -/
theorem nonstationary_mellin_majorant_le_five_div_abs {ω t : ℝ}
    (hω : ω ≠ 0) (ht : |t| ≤ |ω| / 2) :
    2 / |ω| + (2 / |ω|) * (∫ v in Ioi (1 : ℝ), (5 / 2 : ℝ) * v ^ (-7 / 2 : ℝ)) +
      (4 * |t| / |ω| ^ 2) * (∫ v in Ioi (1 : ℝ), v ^ (-9 / 2 : ℝ)) ≤
      5 / |ω| := by
  have hω_pos : 0 < |ω| := abs_pos.mpr hω
  rw [integral_Ioi_one_amplitude_deriv, integral_Ioi_one_curvature_weight, mul_one]
  have hcurv : (4 * |t| / |ω| ^ 2) * (2 / 7 : ℝ) ≤ 1 / |ω| := by
    have h1 : 4 * |t| ≤ 2 * |ω| := by linarith
    calc
      (4 * |t| / |ω| ^ 2) * (2 / 7 : ℝ) ≤ (2 * |ω| / |ω| ^ 2) * (2 / 7 : ℝ) := by
        gcongr
      _ = (4 / 7 : ℝ) * (1 / |ω|) := by
        field_simp [hω_pos.ne']
        ring
      _ ≤ 1 * (1 / |ω|) := by
        gcongr
        norm_num
      _ = 1 / |ω| := one_mul _
  linarith

/-- The low-frequency Mellin exclusion constant `D = 15 / π^3`. -/
def factorialLowFreqConstant : ℝ :=
  15 / Real.pi ^ 3

theorem factorialLowFreqConstant_pos : 0 < factorialLowFreqConstant := by
  unfold factorialLowFreqConstant
  positivity

/-- Summing the single-harmonic Mellin bounds `(10 / π^3) / (k^3 N)` over `1 ≤ k ≤ K`
yields at most `D / N` with `D = 15 / π^3`. -/
theorem sum_harmonic_mellin_majorant_le (K N : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, (10 / Real.pi ^ 3) / ((k : ℝ) ^ 3 * (N : ℝ))) ≤
      factorialLowFreqConstant / (N : ℝ) := by
  rcases eq_zero_or_pos N with rfl | hN
  · simp [factorialLowFreqConstant]
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hrew : (∑ k ∈ Finset.Icc 1 K, (10 / Real.pi ^ 3) / ((k : ℝ) ^ 3 * (N : ℝ))) =
      ((10 / Real.pi ^ 3) / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) ^ 3 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hrew]
  calc
    ((10 / Real.pi ^ 3) / (N : ℝ)) * (∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) ^ 3) ≤
        ((10 / Real.pi ^ 3) / (N : ℝ)) * (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left (sum_Icc_one_inv_cube_le_three_halves K) (by positivity)
    _ = factorialLowFreqConstant / (N : ℝ) := by
      unfold factorialLowFreqConstant
      ring

/-- Telescoping bound `∑_{N = M}^K 1 / N^2 ≤ 2 / M` for every `M ≥ 2`. -/
theorem sum_Icc_inv_sq_le_two_div {M K : ℕ} (hM : 2 ≤ M) :
    (∑ N ∈ Finset.Icc M K, 1 / (N : ℝ) ^ 2) ≤ 2 / (M : ℝ) := by
  rcases lt_or_ge K M with hlt | hKM
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have htel : (∑ N ∈ Finset.Icc M K, 1 / (N : ℝ) ^ 2) ≤
        1 / ((M : ℝ) - 1) - 1 / (K : ℝ) := by
      induction K, hKM using Nat.le_induction with
      | base =>
        simp only [Finset.Icc_self, Finset.sum_singleton]
        have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
        have hM1_pos : (0 : ℝ) < (M : ℝ) - 1 := by
          have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
          linarith
        rw [div_sub_div _ _ hM1_pos.ne' hM_pos.ne', one_mul, mul_one]
        have hnum : (M : ℝ) - ((M : ℝ) - 1) = 1 := by ring
        rw [hnum]
        apply one_div_le_one_div_of_le (mul_pos hM1_pos hM_pos)
        nlinarith
      | succ k hk ih =>
        rw [Finset.sum_Icc_succ_top (by omega : M ≤ k + 1)]
        have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
        have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
        have hstep : 1 / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
          rw [div_sub_div _ _ hk_pos.ne' hk1_pos.ne', one_mul, mul_one]
          have hsub : ((k + 1 : ℕ) : ℝ) - (k : ℝ) = 1 := by push_cast; ring
          rw [hsub]
          apply one_div_le_one_div_of_le (mul_pos hk_pos hk1_pos)
          push_cast
          nlinarith
        linarith
    have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hM1_pos : (0 : ℝ) < (M : ℝ) - 1 := by linarith
    have hM_pos : (0 : ℝ) < (M : ℝ) := by linarith
    have hle_two : 1 / ((M : ℝ) - 1) ≤ 2 / (M : ℝ) := by
      rw [div_le_div_iff₀ hM1_pos hM_pos]
      linarith
    have hK_inv : 0 ≤ 1 / (K : ℝ) := by positivity
    linarith

/-- For any finite set `S : Finset ℕ` with `∀ N ∈ S, M ≤ N` (`2 ≤ M`),
`∑_{N ∈ S} (D / N)^2 ≤ 2 D^2 / M`. -/
theorem sum_low_freq_sq_le_two_mul_sq_div (S : Finset ℕ) {M : ℕ} (hM : 2 ≤ M)
    (hS : ∀ N ∈ S, M ≤ N) (D : ℝ) :
    (∑ N ∈ S, (D / (N : ℝ)) ^ 2) ≤ 2 * D ^ 2 / (M : ℝ) := by
  let K : ℕ := S.sup id + M
  have hsub : S ⊆ Finset.Icc M K := by
    intro N hN
    rw [Finset.mem_Icc]
    refine ⟨hS N hN, ?_⟩
    have hle : N ≤ S.sup id := Finset.le_sup (f := id) hN
    dsimp [K]
    omega
  calc
    (∑ N ∈ S, (D / (N : ℝ)) ^ 2) ≤ ∑ N ∈ Finset.Icc M K, (D / (N : ℝ)) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ = D ^ 2 * ∑ N ∈ Finset.Icc M K, 1 / (N : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun N _ => ?_
      ring
    _ ≤ D ^ 2 * (2 / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le_two_div hM) (sq_nonneg D)
    _ = 2 * D ^ 2 / (M : ℝ) := by ring

/-- Relative low-frequency cutoff parameter `η(A, D) = min 1 (min π (A π / (4 D^2)))`. -/
def lowFreqRelativeCutoff (A D : ℝ) : ℝ :=
  min 1 (min Real.pi (A * Real.pi / (4 * D ^ 2)))

theorem lowFreqRelativeCutoff_pos {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    0 < lowFreqRelativeCutoff A D := by
  unfold lowFreqRelativeCutoff
  refine lt_min zero_lt_one (lt_min Real.pi_pos ?_)
  positivity

theorem lowFreqRelativeCutoff_le_one (A D : ℝ) :
    lowFreqRelativeCutoff A D ≤ 1 :=
  min_le_left _ _

theorem lowFreqRelativeCutoff_le_arch_ratio (A D : ℝ) :
    lowFreqRelativeCutoff A D ≤ A * Real.pi / (4 * D ^ 2) :=
  (min_le_right _ _).trans (min_le_right _ _)

/-- **Low-Band Plancherel Energy Bound (Equation (7) of `APT-ROOT-SPAN-COERCIVITY`).**
For any `A > 0`, `D > 0`, `M ≥ 2`, and `S ≥ 0`, integrating the pointwise low-band bound
`2 D^2 S / M` over `[-η M, η M]` with Plancherel factor `1 / (2 π)` costs at most `(A / 2) S`. -/
theorem low_band_plancherel_energy_le_half_arch {A D S : ℝ} {M : ℕ}
    (hD : 0 < D) (hS : 0 ≤ S) (hM : 2 ≤ M) :
    (1 / (2 * Real.pi)) * (2 * lowFreqRelativeCutoff A D * (M : ℝ)) *
      (2 * D ^ 2 * S / (M : ℝ)) ≤ (A / 2) * S := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hη := lowFreqRelativeCutoff_le_arch_ratio A D
  calc
    (1 / (2 * Real.pi)) * (2 * lowFreqRelativeCutoff A D * (M : ℝ)) *
        (2 * D ^ 2 * S / (M : ℝ)) =
        (2 * lowFreqRelativeCutoff A D * D ^ 2 / Real.pi) * S := by
      field_simp [hM_pos.ne', hpi.ne']
      ring
    _ ≤ (2 * (A * Real.pi / (4 * D ^ 2)) * D ^ 2 / Real.pi) * S := by
      refine mul_le_mul_of_nonneg_right ?_ hS
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hη (by norm_num)) (sq_nonneg D))
        hpi.le
    _ = (A / 2) * S := by
      field_simp [hD.ne', hpi.ne']
      ring

/-- **High-Scale Archimedean Logarithmic Coercivity (Equation (9) of `APT-ROOT-SPAN-COERCIVITY`).**
Suppose the total Plancherel mass `E_tot = E_low + E_high` satisfies `A S ≤ E_tot ≤ B S`,
the low-band mass satisfies `E_low ≤ (A / 2) S`, and the archimedean Gamma energy `E_arch`
satisfies:
- the global lower bound `-(G + log 2) E_tot ≤ E_arch` (for all `M`), and
- when `1 ≤ η M`, the split lower bound `-(G + log 2) E_low + (log(η M) - G) E_high ≤ E_arch`.
Then for every `M ≥ 2`, with `c = A / 2`:
`(c * log M - B * (G + log 2) - c * log (1 / η)) * S ≤ E_arch`. -/
theorem high_scale_archimedean_log_coercivity {A B G η S E_low E_high E_arch : ℝ} {M : ℕ}
    (hA : 0 < A) (hG : 0 ≤ G) (hη : 0 < η) (hS : 0 ≤ S) (hM : 2 ≤ M)
    (hE_low0 : 0 ≤ E_low) (hE_high0 : 0 ≤ E_high)
    (h_tot_lo : A * S ≤ E_low + E_high)
    (h_tot_hi : E_low + E_high ≤ B * S)
    (h_low_hi : E_low ≤ (A / 2) * S)
    (h_global : -(G + Real.log 2) * (E_low + E_high) ≤ E_arch)
    (h_split : 1 ≤ η * (M : ℝ) →
      -(G + Real.log 2) * E_low + (Real.log (η * (M : ℝ)) - G) * E_high ≤ E_arch) :
    ((A / 2) * Real.log (M : ℝ) - B * (G + Real.log 2) -
      (A / 2) * Real.log (1 / η)) * S ≤ E_arch := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hG2 : 0 ≤ G + Real.log 2 := by linarith
  by_cases hηM : 1 ≤ η * (M : ℝ)
  · have h_high_lo : (A / 2) * S ≤ E_high := by linarith
    have hlog_ηM : 0 ≤ Real.log (η * (M : ℝ)) := Real.log_nonneg hηM
    have hlog_eq : Real.log (η * (M : ℝ)) = Real.log (M : ℝ) - Real.log (1 / η) := by
      rw [Real.log_mul hη.ne' hM_pos.ne', one_div, Real.log_inv]
      ring
    have h1 : (Real.log (η * (M : ℝ)) - (G + Real.log 2)) * E_low +
        (Real.log (η * (M : ℝ)) - (G + Real.log 2)) * E_high ≤
        -(G + Real.log 2) * E_low + (Real.log (η * (M : ℝ)) - G) * E_high := by
      nlinarith
    have h2 : Real.log (η * (M : ℝ)) * ((A / 2) * S) - (G + Real.log 2) * (B * S) ≤
        -(G + Real.log 2) * E_low + (Real.log (η * (M : ℝ)) - G) * E_high := by
      have h_pos_part : Real.log (η * (M : ℝ)) * ((A / 2) * S) ≤
          Real.log (η * (M : ℝ)) * E_high :=
        mul_le_mul_of_nonneg_left h_high_lo hlog_ηM
      have h_neg_part : -(G + Real.log 2) * (B * S) ≤
          -(G + Real.log 2) * E_low - G * E_high := by
        have htot : (G + Real.log 2) * (E_low + E_high) ≤ (G + Real.log 2) * (B * S) :=
          mul_le_mul_of_nonneg_left h_tot_hi hG2
        nlinarith
      linarith
    calc
      ((A / 2) * Real.log (M : ℝ) - B * (G + Real.log 2) -
          (A / 2) * Real.log (1 / η)) * S =
          Real.log (η * (M : ℝ)) * ((A / 2) * S) - (G + Real.log 2) * (B * S) := by
        rw [hlog_eq]
        ring
      _ ≤ -(G + Real.log 2) * E_low + (Real.log (η * (M : ℝ)) - G) * E_high := h2
      _ ≤ E_arch := h_split hηM
  · push Not at hηM
    have hM_le : (M : ℝ) ≤ 1 / η := by
      rw [le_div_iff₀ hη]
      linarith
    have hlog_le : Real.log (M : ℝ) ≤ Real.log (1 / η) :=
      Real.log_le_log hM_pos hM_le
    have hglob : -B * (G + Real.log 2) * S ≤ -(G + Real.log 2) * (E_low + E_high) := by
      nlinarith [mul_le_mul_of_nonneg_left h_tot_hi hG2]
    have hsub_nonpos : ((A / 2) * Real.log (M : ℝ) - (A / 2) * Real.log (1 / η)) * S ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hS
    linarith [h_global]

/-- The explicit offset constant `C` in `APT-ROOT-SPAN-COERCIVITY` Equation (2). -/
def factorialSpanCoercivityOffset (A B G J D : ℝ) : ℝ :=
  B * (G + Real.log 2) +
    (A / 2) * Real.log (1 / lowFreqRelativeCutoff A D) +
    6 * J +
    2 * B * canonicalPrimeMajorantConstant

/-- **Complete High-Scale Span Coercivity Assembly (`APT-ROOT-SPAN-COERCIVITY` Equation (1)).**
Combining the high-scale archimedean lower bound with the uniform polar budget `6 J S`
and prime budget `2 B canonicalPrimeMajorantConstant S` yields
`( (A / 2) log M - C ) S ≤ W_re`. -/
theorem high_scale_span_weil_coercivity_bound
    {A B G J D S E_arch E_polar E_prime W_re : ℝ} {M : ℕ}
    (h_ident : W_re = E_arch + E_polar - E_prime)
    (h_arch : ((A / 2) * Real.log (M : ℝ) - B * (G + Real.log 2) -
      (A / 2) * Real.log (1 / lowFreqRelativeCutoff A D)) * S ≤ E_arch)
    (h_polar : |E_polar| ≤ 6 * J * S)
    (h_prime : |E_prime| ≤ 2 * B * canonicalPrimeMajorantConstant * S) :
    ((A / 2) * Real.log (M : ℝ) - factorialSpanCoercivityOffset A B G J D) * S ≤ W_re := by
  unfold factorialSpanCoercivityOffset
  have hpol_lo := (abs_le.mp h_polar).1
  have hpri_hi := (abs_le.mp h_prime).2
  linarith

/-- **Strict High-Scale Span Positivity Threshold (`iff`).** For `A > 0` and `S > 0`,
the lower bound `((A / 2) * log M - C) * S` is strictly positive if and only if
`Real.exp (2 * C / A) < M`. -/
theorem high_scale_span_lower_bound_pos_iff {A C S : ℝ} {M : ℕ}
    (hA : 0 < A) (hS : 0 < S) (hM : 1 ≤ M) :
    0 < ((A / 2) * Real.log (M : ℝ) - C) * S ↔ Real.exp (2 * C / A) < (M : ℝ) := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rw [mul_pos_iff_of_pos_right hS, sub_pos,
    show C < A / 2 * Real.log (M : ℝ) ↔ 2 * C / A < Real.log (M : ℝ) by
      rw [div_lt_iff₀ hA]
      constructor <;> intro h <;> linarith,
    Real.exp_lt_iff_lt_log hM_pos]

end

end GaloisForLFunctions.ArithmeticPositivityTheory
