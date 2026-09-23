import GaloisForLFunctions.RHTower.SelectionResonanceFactorizationBlock

/-!
# The factorized construction with a general factor `(L+1)/L`

Replacing the factor `2^{iu} + 3^{iu}` by `L^{iu} + (L+1)^{iu}` gives the polynomial
`D_L(u) = (L^{iu} + (L+1)^{iu}) · Σ_{3m⁴ ≤ k ≤ 4m⁴} (k/4m⁴)^{20} k^{iu}`, supported on
`[3Lm⁴, 4(L+1)m⁴] ⊆ [N, 2N]` with `N = 3Lm⁴`, and `|D_L(u)| = 2|cos(λ_L u/2)| · |B(u)|` with
`λ_L = log((L+1)/L) ∈ [1/(L+1), 1/L]`.  The period `P_L = 2π/λ_L` lies in `[2πL, 2π(L+1)]`.  For
`2 ≤ L ≤ m/1000` the same window and period analysis as for `L = 2` applies verbatim, with the
constant `19` replaced by `P_L ≤ 2π(L+1)`.
-/

open Complex Set Finset intervalIntegral MeasureTheory Real

namespace RHTower

noncomputable section

/-- `λ_L = log((L+1)/L)`. -/
def resLamL (L : ℕ) : ℝ := Real.log (((L : ℝ) + 1) / (L : ℝ))

theorem resLamL_pos {L : ℕ} (hL : 1 ≤ L) : 0 < resLamL L := by
  unfold resLamL
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  apply Real.log_pos
  rw [lt_div_iff₀ (by linarith)]; linarith

theorem resLamL_ge {L : ℕ} (hL : 1 ≤ L) : 1 / ((L : ℝ) + 1) ≤ resLamL L := by
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((L : ℝ) + 1) / (L : ℝ) by positivity)
  unfold resLamL
  have : 1 - (((L : ℝ) + 1) / (L : ℝ))⁻¹ = 1 / ((L : ℝ) + 1) := by
    field_simp; ring
  rw [this] at h; exact h

theorem resLamL_le {L : ℕ} (hL : 1 ≤ L) : resLamL L ≤ 1 / (L : ℝ) := by
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((L : ℝ) + 1) / (L : ℝ) by positivity)
  unfold resLamL
  have : ((L : ℝ) + 1) / (L : ℝ) - 1 = 1 / (L : ℝ) := by field_simp; ring
  rw [this] at h; exact h

/-- `P_L = 2π/λ_L`. -/
def resPeriodL (L : ℕ) : ℝ := 2 * π / resLamL L

theorem resPeriodL_pos {L : ℕ} (hL : 1 ≤ L) : 0 < resPeriodL L := by
  unfold resPeriodL; have := resLamL_pos hL; positivity

theorem resPeriodL_ge {L : ℕ} (hL : 1 ≤ L) : 2 * π * (L : ℝ) ≤ resPeriodL L := by
  unfold resPeriodL
  have hlam := resLamL_pos hL
  rw [le_div_iff₀ hlam]
  have h := resLamL_le hL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have : (L : ℝ) * resLamL L ≤ 1 := by
    calc (L : ℝ) * resLamL L ≤ (L : ℝ) * (1 / (L : ℝ)) := by gcongr
      _ = 1 := by field_simp
  nlinarith [Real.pi_pos]

theorem resPeriodL_le {L : ℕ} (hL : 1 ≤ L) : resPeriodL L ≤ 2 * π * ((L : ℝ) + 1) := by
  unfold resPeriodL
  have hlam := resLamL_pos hL
  rw [div_le_iff₀ hlam]
  have h := resLamL_ge hL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have : 1 ≤ ((L : ℝ) + 1) * resLamL L := by
    calc (1 : ℝ) = ((L : ℝ) + 1) * (1 / ((L : ℝ) + 1)) := by field_simp
      _ ≤ ((L : ℝ) + 1) * resLamL L := by gcongr
  nlinarith [Real.pi_pos]

theorem resPeriodL_gt_twelve {L : ℕ} (hL : 2 ≤ L) : 12 < resPeriodL L := by
  have h := resPeriodL_ge (by omega : 1 ≤ L)
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
  nlinarith [Real.pi_gt_three]

/-- The factorized polynomial with factor `(L+1)/L`. -/
def resPolyL (L m : ℕ) (u : ℝ) : ℂ :=
  ((L : ℂ) ^ ((u : ℂ) * I) + ((L : ℂ) + 1) ^ ((u : ℂ) * I)) * resBlock m u

theorem norm_L_cpow_add_succ_cpow {L : ℕ} (hL : 1 ≤ L) (u : ℝ) :
    ‖(L : ℂ) ^ ((u : ℂ) * I) + ((L : ℂ) + 1) ^ ((u : ℂ) * I)‖ =
      2 * |Real.cos (resLamL L * u / 2)| := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hL1 : (0 : ℝ) < (L : ℝ) + 1 := by linarith
  have h2 : (L : ℂ) ^ ((u : ℂ) * I) = Complex.exp (((Real.log L * u : ℝ) : ℂ) * I) := by
    rw [← Complex.ofReal_natCast]; exact cpow_ofReal_mul_I_eq_exp hLR u
  have h3 : ((L : ℂ) + 1) ^ ((u : ℂ) * I) =
      Complex.exp (((Real.log ((L : ℝ) + 1) * u : ℝ) : ℂ) * I) := by
    have := cpow_ofReal_mul_I_eq_exp hL1 u
    push_cast at this ⊢
    exact this
  rw [h2, h3]
  have hfac : Complex.exp (((Real.log L * u : ℝ) : ℂ) * I) +
      Complex.exp (((Real.log ((L : ℝ) + 1) * u : ℝ) : ℂ) * I) =
      Complex.exp (((Real.log L * u : ℝ) : ℂ) * I) *
        (1 + Complex.exp (((resLamL L * u : ℝ) : ℂ) * I)) := by
    rw [mul_add, mul_one, ← Complex.exp_add]
    congr 1
    congr 1
    unfold resLamL
    rw [Real.log_div hL1.ne' hLR.ne']
    push_cast; ring
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_one_add_exp_ofReal_mul_I]

theorem norm_resPolyL {L : ℕ} (hL : 1 ≤ L) (m : ℕ) (u : ℝ) :
    ‖resPolyL L m u‖ = 2 * |Real.cos (resLamL L * u / 2)| * ‖resBlock m u‖ := by
  unfold resPolyL
  rw [norm_mul, norm_L_cpow_add_succ_cpow hL]

theorem continuous_resPolyL {L m : ℕ} (hL : 1 ≤ L) (hm : 1 ≤ m) : Continuous (resPolyL L m) := by
  unfold resPolyL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  refine Continuous.mul (Continuous.add ?_ ?_) (continuous_resBlock hm)
  · exact continuous_cpow_const_ofReal_mul_I (by
      rw [Complex.mem_slitPlane_iff]; left; simpa using hLR)
  · exact continuous_cpow_const_ofReal_mul_I (by
      rw [Complex.mem_slitPlane_iff]; left; simp; linarith)

/-- The window: no large values for `3m ≤ u ≤ m²`. -/
theorem norm_resPolyL_lt_of_window {L m : ℕ} (hL : 1 ≤ L) (hm : 5 ≤ m) {u : ℝ}
    (hu3 : 3 * (m : ℝ) ≤ u) (hu : u ≤ (m : ℝ) ^ (2 : ℕ)) : ‖resPolyL L m u‖ < 4 * (m : ℝ) ^ (3 : ℕ) := by
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hu0 : 0 ≤ u := by linarith
  obtain ⟨-, hhi⟩ := resBlock_envelope hm hu0 hu
  rw [norm_resPolyL hL]
  have hcos : |Real.cos (resLamL L * u / 2)| ≤ 1 := Real.abs_cos_le_one _
  have hsqrt : 3 * (m : ℝ) ≤ Real.sqrt (441 + u ^ (2 : ℕ)) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]; nlinarith
  have hsqrt_pos : 0 < Real.sqrt (441 + u ^ (2 : ℕ)) := by linarith
  have hdiv : (401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / Real.sqrt (441 + u ^ (2 : ℕ)) ≤
      (401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / (3 * (m : ℝ)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrt
  have hdiv' : (401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / (3 * (m : ℝ)) = (401 / 300) * (m : ℝ) ^ (3 : ℕ) := by
    rw [div_eq_iff (by positivity)]; ring
  have hB : ‖resBlock m u‖ ≤ (401 / 300) * (m : ℝ) ^ (3 : ℕ) + 2 := by linarith
  have hBn : 0 ≤ ‖resBlock m u‖ := norm_nonneg _
  calc 2 * |Real.cos (resLamL L * u / 2)| * ‖resBlock m u‖
      ≤ 2 * 1 * ((401 / 300) * (m : ℝ) ^ (3 : ℕ) + 2) := by gcongr
    _ < 4 * (m : ℝ) ^ (3 : ℕ) := by nlinarith

/-- The outer threshold on the `k`-th period. -/
def resKappaL (L m k : ℕ) : ℝ :=
  2 * (m : ℝ) ^ (3 : ℕ) /
    ((401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / Real.sqrt (441 + ((k : ℝ) * resPeriodL L) ^ (2 : ℕ)) + 2)

/-- **Core condition** for the general factor. -/
theorem resPolyL_core {L m : ℕ} (hL : 1 ≤ L) (hm : 1000 ≤ m) {k : ℕ}
    (hk : ((k : ℝ) + 1) * resPeriodL L ≤ (69 / 50) * (m : ℝ)) {u : ℝ}
    (hu : u ∈ Icc ((k : ℝ) * resPeriodL L) (((k : ℝ) + 1) * resPeriodL L))
    (hcos : Real.sqrt 2 / 2 ≤ |Real.cos (resLamL L * u / 2)|) :
    4 * (m : ℝ) ^ (3 : ℕ) ≤ ‖resPolyL L m u‖ := by
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriodL_pos hL
  have hu0 : 0 ≤ u := le_trans (by positivity) hu.1
  have hu1 : u ≤ (69 / 50) * (m : ℝ) := le_trans hu.2 hk
  have hum : u ≤ (m : ℝ) ^ (2 : ℕ) := by nlinarith
  obtain ⟨hlo, -⟩ := resBlock_envelope (by omega) hu0 hum
  have hsqrt := sqrt_bound_of_le hm hu0 hu1
  have hsqrt_pos : 0 < Real.sqrt (441 + u ^ (2 : ℕ)) := Real.sqrt_pos.mpr (by positivity)
  have hdiv : (399 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / ((13802 / 10000) * (m : ℝ)) ≤
      (399 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / Real.sqrt (441 + u ^ (2 : ℕ)) :=
    div_le_div_of_nonneg_left (by positivity) hsqrt_pos hsqrt
  have hdiv' : (399 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / ((13802 / 10000) * (m : ℝ)) =
      (399 / 100 : ℝ) * (10000 / 13802) * (m : ℝ) ^ (3 : ℕ) := by
    rw [div_eq_iff (by positivity)]; ring
  have hB : (399 / 100 : ℝ) * (10000 / 13802) * (m : ℝ) ^ (3 : ℕ) - 2 ≤ ‖resBlock m u‖ := by linarith
  rw [norm_resPolyL hL]
  have hs2' : (14142 / 10000 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hBn : 0 ≤ (399 / 100 : ℝ) * (10000 / 13802) * (m : ℝ) ^ (3 : ℕ) - 2 := by nlinarith
  calc 4 * (m : ℝ) ^ (3 : ℕ)
      ≤ 2 * (Real.sqrt 2 / 2) * ((399 / 100 : ℝ) * (10000 / 13802) * (m : ℝ) ^ (3 : ℕ) - 2) := by
        nlinarith
    _ ≤ 2 * |Real.cos (resLamL L * u / 2)| * ‖resBlock m u‖ := by gcongr

/-- **Outer condition** for the general factor. -/
theorem resPolyL_outer {L m : ℕ} (hL : 1 ≤ L) (hm : 5 ≤ m) {k : ℕ}
    (hk : ((k : ℝ) + 1) * resPeriodL L ≤ (m : ℝ) ^ (2 : ℕ)) {u : ℝ}
    (hu : u ∈ Icc ((k : ℝ) * resPeriodL L) (((k : ℝ) + 1) * resPeriodL L))
    (hlarge : 4 * (m : ℝ) ^ (3 : ℕ) ≤ ‖resPolyL L m u‖) :
    resKappaL L m k ≤ |Real.cos (resLamL L * u / 2)| := by
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriodL_pos hL
  have hu0 : 0 ≤ u := le_trans (by positivity) hu.1
  have hum : u ≤ (m : ℝ) ^ (2 : ℕ) := le_trans hu.2 hk
  obtain ⟨-, hhi⟩ := resBlock_envelope hm hu0 hum
  rw [norm_resPolyL hL] at hlarge
  have hsqrt_mono : Real.sqrt (441 + ((k : ℝ) * resPeriodL L) ^ (2 : ℕ)) ≤ Real.sqrt (441 + u ^ (2 : ℕ)) := by
    apply Real.sqrt_le_sqrt
    have h1 := hu.1
    have hk0 : 0 ≤ (k : ℝ) * resPeriodL L := by positivity
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt (441 + ((k : ℝ) * resPeriodL L) ^ (2 : ℕ)) :=
    Real.sqrt_pos.mpr (by positivity)
  have hdiv : (401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / Real.sqrt (441 + u ^ (2 : ℕ)) ≤
      (401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / Real.sqrt (441 + ((k : ℝ) * resPeriodL L) ^ (2 : ℕ)) :=
    div_le_div_of_nonneg_left (by positivity) hsqrt_pos hsqrt_mono
  set Smax := (401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / Real.sqrt (441 + ((k : ℝ) * resPeriodL L) ^ (2 : ℕ)) + 2
    with hSmax
  have hSpos : 0 < Smax := by rw [hSmax]; positivity
  have hB : ‖resBlock m u‖ ≤ Smax := by rw [hSmax]; linarith
  have hcos0 : 0 ≤ |Real.cos (resLamL L * u / 2)| := abs_nonneg _
  unfold resKappaL
  rw [← hSmax, div_le_iff₀ hSpos]
  nlinarith [mul_le_mul_of_nonneg_left hB (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hcos0)]

theorem resKappaL_pos {L m : ℕ} (hm : 1 ≤ m) (k : ℕ) : 0 < resKappaL L m k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold resKappaL
  have : 0 < Real.sqrt (441 + ((k : ℝ) * resPeriodL L) ^ (2 : ℕ)) := Real.sqrt_pos.mpr (by positivity)
  positivity

theorem resKappaL_le_sqrt_two_div_two {L m : ℕ} (hL : 1 ≤ L) (hm : 1000 ≤ m) {k : ℕ}
    (hk : (k : ℝ) * resPeriodL L ≤ (69 / 50) * (m : ℝ)) :
    resKappaL L m k ≤ Real.sqrt 2 / 2 := by
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriodL_pos hL
  have hk0 : 0 ≤ (k : ℝ) * resPeriodL L := by positivity
  have hsqrt := sqrt_bound_of_le hm hk0 hk
  have hsqrt_pos : 0 < Real.sqrt (441 + ((k : ℝ) * resPeriodL L) ^ (2 : ℕ)) :=
    Real.sqrt_pos.mpr (by positivity)
  have hs2' : (14142 / 10000 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  unfold resKappaL
  have hden : (401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / ((13802 / 10000) * (m : ℝ)) ≤
      (401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / Real.sqrt (441 + ((k : ℝ) * resPeriodL L) ^ (2 : ℕ)) :=
    div_le_div_of_nonneg_left (by positivity) hsqrt_pos hsqrt
  have hden' : (401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / ((13802 / 10000) * (m : ℝ)) =
      (401 / 100 : ℝ) * (10000 / 13802) * (m : ℝ) ^ (3 : ℕ) := by
    rw [div_eq_iff (by positivity)]; ring
  rw [div_le_iff₀ (by positivity)]
  have hA : (401 / 100 : ℝ) * (10000 / 13802) * (m : ℝ) ^ (3 : ℕ) + 2 ≤
      (401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / Real.sqrt (441 + ((k : ℝ) * resPeriodL L) ^ (2 : ℕ)) + 2 := by
    linarith
  have hB := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / 2)
  have hC := mul_le_mul_of_nonneg_right hs2'.le
    (by positivity : (0 : ℝ) ≤ (401 / 100 : ℝ) * (10000 / 13802) * (m : ℝ) ^ (3 : ℕ) + 2)
  have hm3 : (1000 : ℝ) ^ (3 : ℕ) ≤ (m : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) hmR 3
  nlinarith

theorem resKappaL_ge {L m : ℕ} (hL : 1 ≤ L) (hm : 1000 ≤ m) {k : ℕ}
    (hk : (k : ℝ) * resPeriodL L ≤ (69 / 50) * (m : ℝ)) :
    (k : ℝ) * resPeriodL L / ((201 / 100) * (m : ℝ)) ≤ resKappaL L m k := by
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriodL_pos hL
  have hk0 : 0 ≤ (k : ℝ) * resPeriodL L := by positivity
  have hsqrt := sqrt_bound_of_le hm hk0 hk
  have hsqrt_ge : (k : ℝ) * resPeriodL L ≤ Real.sqrt (441 + ((k : ℝ) * resPeriodL L) ^ (2 : ℕ)) := by
    rw [Real.le_sqrt hk0 (by positivity)]; linarith
  have hsqrt_pos : 0 < Real.sqrt (441 + ((k : ℝ) * resPeriodL L) ^ (2 : ℕ)) :=
    Real.sqrt_pos.mpr (by positivity)
  unfold resKappaL
  set s := Real.sqrt (441 + ((k : ℝ) * resPeriodL L) ^ (2 : ℕ)) with hs
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hfrac : (401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / s + 2 = ((401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) + 2 * s) / s := by
    field_simp
  rw [hfrac, ← mul_div_assoc, div_le_iff₀ hsqrt_pos]
  have h1 : (k : ℝ) * resPeriodL L * ((401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) + 2 * s) ≤
      s * ((401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) + 2 * s) := by
    apply mul_le_mul_of_nonneg_right hsqrt_ge; positivity
  have h2 : 2 * s ≤ (1 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) := by
    have hm3 : (1000 : ℝ) ^ (3 : ℕ) ≤ (m : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) hmR 3
    have hm4 : (1 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) = (m : ℝ) * ((1 / 100) * (m : ℝ) ^ (3 : ℕ)) := by ring
    rw [hm4]
    nlinarith [mul_le_mul_of_nonneg_left hm3 (by positivity : (0 : ℝ) ≤ m)]
  nlinarith

/-- **Nonnegativity condition** for the general factor. -/
theorem resPolyL_nonneg_period {L m : ℕ} (hL : 1 ≤ L) (hm : 1000 ≤ m) {k : ℕ}
    (hk : (36 / 25) * (m : ℝ) ≤ (k : ℝ) * resPeriodL L)
    (hk' : ((k : ℝ) + 1) * resPeriodL L ≤ (m : ℝ) ^ (2 : ℕ)) {u : ℝ}
    (hu : u ∈ Icc ((k : ℝ) * resPeriodL L) (((k : ℝ) + 1) * resPeriodL L))
    (hlarge : 4 * (m : ℝ) ^ (3 : ℕ) ≤ ‖resPolyL L m u‖) :
    Real.sqrt 2 / 2 ≤ |Real.cos (resLamL L * u / 2)| := by
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriodL_pos hL
  have hu0 : 0 ≤ u := le_trans (by positivity) hu.1
  have hum : u ≤ (m : ℝ) ^ (2 : ℕ) := le_trans hu.2 hk'
  have hu1 : (36 / 25) * (m : ℝ) ≤ u := le_trans hk hu.1
  obtain ⟨-, hhi⟩ := resBlock_envelope (by omega) hu0 hum
  rw [norm_resPolyL hL] at hlarge
  have hsqrt_ge : (36 / 25) * (m : ℝ) ≤ Real.sqrt (441 + u ^ (2 : ℕ)) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]; nlinarith
  have hsqrt_pos : 0 < Real.sqrt (441 + u ^ (2 : ℕ)) := Real.sqrt_pos.mpr (by positivity)
  have hdiv : (401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / Real.sqrt (441 + u ^ (2 : ℕ)) ≤
      (401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / ((36 / 25) * (m : ℝ)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrt_ge
  have hdiv' : (401 / 100 : ℝ) * (m : ℝ) ^ (4 : ℕ) / ((36 / 25) * (m : ℝ)) =
      (401 / 100 : ℝ) * (25 / 36) * (m : ℝ) ^ (3 : ℕ) := by
    rw [div_eq_iff (by positivity)]; ring
  have hB : ‖resBlock m u‖ ≤ (401 / 100 : ℝ) * (25 / 36) * (m : ℝ) ^ (3 : ℕ) + 2 := by linarith
  have hcos0 : 0 ≤ |Real.cos (resLamL L * u / 2)| := abs_nonneg _
  have hs2 := sqrt_two_lt
  by_contra hcon
  push Not at hcon
  have : 2 * |Real.cos (resLamL L * u / 2)| * ‖resBlock m u‖ <
      2 * (Real.sqrt 2 / 2) * ((401 / 100 : ℝ) * (25 / 36) * (m : ℝ) ^ (3 : ℕ) + 2) := by
    have hBn : 0 ≤ ‖resBlock m u‖ := norm_nonneg _
    have hpos : 0 < (401 / 100 : ℝ) * (25 / 36) * (m : ℝ) ^ (3 : ℕ) + 2 := by positivity
    calc 2 * |Real.cos (resLamL L * u / 2)| * ‖resBlock m u‖
        ≤ 2 * |Real.cos (resLamL L * u / 2)| * ((401 / 100 : ℝ) * (25 / 36) * (m : ℝ) ^ (3 : ℕ) + 2) := by
          gcongr
      _ < 2 * (Real.sqrt 2 / 2) * ((401 / 100 : ℝ) * (25 / 36) * (m : ℝ) ^ (3 : ℕ) + 2) := by
          gcongr
  have hC := mul_lt_mul_of_pos_right hs2
    (by positivity : (0 : ℝ) < (401 / 100 : ℝ) * (25 / 36) * (m : ℝ) ^ (3 : ℕ) + 2)
  have hm3 : (1000 : ℝ) ^ (3 : ℕ) ≤ (m : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) hmR 3
  nlinarith

end

end RHTower
