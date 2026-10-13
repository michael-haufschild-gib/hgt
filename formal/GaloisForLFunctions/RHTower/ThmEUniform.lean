import GaloisForLFunctions.RHTower.ThmEUniformSeam
import GaloisForLFunctions.RHTower.ThmEUniformErrorBudget
import GaloisForLFunctions.RHTower.ThmEUniformRates

/-!
# Theorem E uniformly in the modulus

**Theorem** (`thmE_uniform`).  Fix `λ ∈ (0, 1)` and `A ≥ 0`.  For every `ε > 0` there is `T₀` such that for
all `T ≥ T₀`, every modulus `1 < q ≤ T^A` and every primitive character `χ` modulo `q`,

`(H(λ_{1,q}(T)) − ε) · N_χ(T, 2T) ≤ N₀*_χ(T, 2T)`,

where `H(x) = 2 − 1/x − x/3`, `λ_{1,q}(T) = λ log(T/2π)/(log(qT/2π) + 2 log 2 − 1)`, `N_χ(T, 2T)` counts the
nontrivial zeros of `L(s, χ)` with ordinate in `(T, 2T]` with multiplicity and `N₀*_χ(T, 2T)` counts the
distinct ones on the critical line.

Alpöge–Furman's Theorem E is the same inequality for each fixed `q` with `T₀` depending on `q`.  Here
`T₀` depends only on `λ`, `A` and `ε`.  The proof runs the rank–trace certificate at one height
(`seam_at`) with the modulus-uniform inputs (trace, Frobenius norm, Riemann–von Mangoldt formula,
local and boundary zero counts) and checks that each error is below its share of `ε N_χ(T, 2T)`
(`seam_error_le`) through rates that do not involve `q` (`ThmEUniformRates`).
-/

open MeasureTheory Real Set Filter Topology Zeta23 Zeta23.ThmE Zeta23.PrimeSide Zeta23.Assembly

noncomputable section

namespace RHTower

/-- The modulus-free majorant of the Frobenius error. -/
def frobMajorant (lam A T : ℝ) : ℝ :=
  (1 + A * Real.log T) ^ 2 * ((lam * Zeta23.l T) * Zeta23.l T * Real.log (Zeta23.l T)
      * (Zeta23.l T ^ 2 + Real.exp (lam * Zeta23.l T))
      + Zeta23.l T ^ 2 * Real.log (lam * Zeta23.l T)
      + Zeta23.l T * Real.sqrt (Real.exp (lam * Zeta23.l T)))
    + (lam * Zeta23.l T) ^ 2 * Real.exp (lam * Zeta23.l T)
    + (1 + Real.log (A * Real.log T + 8) ^ 2) * T * (lam * Zeta23.l T) ^ 2

/-- The modulus-free relative Frobenius error. -/
def rhoE (lam A C₂ T : ℝ) : ℝ :=
  C₂ * (2 * π * frobMajorant lam A T / (T * (lam * Zeta23.l T) * Zeta23.l T ^ 2)
    + 2 * π / Zeta23.l T ^ 2)

/-- **The relative Frobenius error tends to zero.** -/
theorem eventually_rhoE_le {lam A C₂ δ : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (hA : 0 ≤ A)
    (hC₂ : 0 ≤ C₂) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, rhoE lam A C₂ T ≤ δ ∧ 4 / (lam * Zeta23.l T) ≤ δ := by
  set d := δ / (2 * π * 6 * (C₂ + 1) + 1) with hd
  have hd0 : 0 < d := by positivity
  have hK : 0 ≤ (1 + A) ^ 2 := sq_nonneg _
  filter_upwards [eventually_l_bounds, eventually_gt_atTop (0:ℝ),
    eventually_log_pow_rpow_le_const 4 (by norm_num : (-1:ℝ) < 0) hK (by positivity : (0:ℝ) < d / 2),
    eventually_log_pow_rpow_le_const 2 (by linarith : lam - 1 < 0) hK (by positivity : (0:ℝ) < d / 2),
    eventually_log_pow_rpow_le_const 2 (by norm_num : (-1:ℝ) < 0) hK hd0,
    eventually_log_pow_rpow_le_const 2 (by linarith : lam / 2 - 1 < 0)
      (by positivity : (0:ℝ) ≤ (1 + A) ^ 2 / lam) hd0,
    eventually_log_pow_rpow_le_const 0 (by linarith : lam - 1 < 0) zero_le_one hd0,
    eventually_log_sq_le hA (by positivity : (0:ℝ) < d / 4),
    Real.tendsto_log_atTop.eventually_ge_atTop (8 / d),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.sqrt (8 * π / d)),
    Real.tendsto_log_atTop.eventually_ge_atTop (8 / (lam * δ))]
    with T ⟨hlog1, hl1, hlo, hhi⟩ hT0 r1 r2 r3 r4 r5 r6 r7 r8 r9
  have hlogT : 0 < Real.log T := by linarith
  have hl0 : 0 < Zeta23.l T := by linarith
  set l := Zeta23.l T with hldef
  set X := Real.exp (lam * l) with hXdef
  have hX0 : 0 < X := Real.exp_pos _
  have hXT : X ≤ T ^ lam := exp_lam_l_le h0.le hT0 hhi
  have hsX : Real.sqrt X ≤ T ^ (lam / 2) := sqrt_exp_lam_l_le h0.le hT0 hhi
  have hΛ : 1 + A * Real.log T ≤ (1 + A) * Real.log T := by nlinarith only [hlog1, hA]
  have hΛ0 : 0 ≤ 1 + A * Real.log T := by positivity
  have hΛ2 : (1 + A * Real.log T) ^ 2 ≤ (1 + A) ^ 2 * Real.log T ^ 2 := by
    have := pow_le_pow_left₀ hΛ0 hΛ 2; rwa [mul_pow] at this
  have hloglel : Real.log l ≤ l := (Real.log_le_sub_one_of_pos hl0).trans (by linarith)
  have hlogl0 : 0 ≤ Real.log l := Real.log_nonneg hl1
  have hL0 : 0 < lam * l := by positivity
  have hLle : lam * l ≤ l := mul_le_of_le_one_left hl0.le h1.le
  have hlogL : Real.log (lam * l) ≤ lam * l :=
    (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  have hTpos : 0 < T * (lam * l) * l ^ 2 := by positivity
  -- the five pieces of the majorant
  have f1 : (1 + A * Real.log T) ^ 2 * ((lam * l) * l * Real.log l * (l ^ 2 + X))
      / (T * (lam * l) * l ^ 2) ≤ d := by
    have e : (1 + A * Real.log T) ^ 2 * ((lam * l) * l * Real.log l * (l ^ 2 + X))
        / (T * (lam * l) * l ^ 2) = (1 + A * Real.log T) ^ 2 * (Real.log l / l) * (l ^ 2 + X) / T := by
      field_simp
    rw [e]
    have hll : Real.log l / l ≤ 1 := by rw [div_le_one hl0]; exact hloglel
    have hll0 : 0 ≤ Real.log l / l := div_nonneg hlogl0 hl0.le
    have hl2 : l ^ 2 ≤ Real.log T ^ 2 := pow_le_pow_left₀ hl0.le hhi 2
    have step : (1 + A * Real.log T) ^ 2 * (Real.log l / l) * (l ^ 2 + X) / T
        ≤ (1 + A) ^ 2 * Real.log T ^ 2 * (Real.log T ^ 2 + T ^ lam) / T := by
      apply div_le_div_of_nonneg_right _ hT0.le
      have h3 : 0 ≤ l ^ 2 + X := by positivity
      calc (1 + A * Real.log T) ^ 2 * (Real.log l / l) * (l ^ 2 + X)
          ≤ (1 + A) ^ 2 * Real.log T ^ 2 * 1 * (l ^ 2 + X) := by gcongr
        _ ≤ (1 + A) ^ 2 * Real.log T ^ 2 * 1 * (Real.log T ^ 2 + T ^ lam) := by gcongr
        _ = (1 + A) ^ 2 * Real.log T ^ 2 * (Real.log T ^ 2 + T ^ lam) := by ring
    refine step.trans ?_
    have e2 : (1 + A) ^ 2 * Real.log T ^ 2 * (Real.log T ^ 2 + T ^ lam) / T
        = (1 + A) ^ 2 * Real.log T ^ 4 * T ^ (-1 : ℝ)
          + (1 + A) ^ 2 * Real.log T ^ 2 * T ^ (lam - 1) := by
      rw [Real.rpow_neg_one, Real.rpow_sub_one hT0.ne']; field_simp
    rw [e2]; linarith only [r1, r2]
  have f2 : (1 + A * Real.log T) ^ 2 * (l ^ 2 * Real.log (lam * l)) / (T * (lam * l) * l ^ 2) ≤ d := by
    have e : (1 + A * Real.log T) ^ 2 * (l ^ 2 * Real.log (lam * l)) / (T * (lam * l) * l ^ 2)
        = (1 + A * Real.log T) ^ 2 * (Real.log (lam * l) / (lam * l)) / T := by field_simp
    rw [e]
    have hq1 : Real.log (lam * l) / (lam * l) ≤ 1 := by rw [div_le_one hL0]; exact hlogL
    have hlogL0 : 0 ≤ Real.log (lam * l) / (lam * l) ∨ Real.log (lam * l) / (lam * l) < 0 :=
      le_or_gt _ _
    calc (1 + A * Real.log T) ^ 2 * (Real.log (lam * l) / (lam * l)) / T
        ≤ (1 + A * Real.log T) ^ 2 * 1 / T := by
          apply div_le_div_of_nonneg_right _ hT0.le
          exact mul_le_mul_of_nonneg_left hq1 (sq_nonneg _)
      _ ≤ (1 + A) ^ 2 * Real.log T ^ 2 * T ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one, mul_one, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hΛ2 (by positivity)
      _ ≤ d := r3
  have f3 : (1 + A * Real.log T) ^ 2 * (l * Real.sqrt X) / (T * (lam * l) * l ^ 2) ≤ d := by
    have e : (1 + A * Real.log T) ^ 2 * (l * Real.sqrt X) / (T * (lam * l) * l ^ 2)
        = (1 + A * Real.log T) ^ 2 * Real.sqrt X / (lam * l ^ 2) / T := by field_simp
    rw [e]
    have hl2 : 1 ≤ l ^ 2 := one_le_pow₀ hl1
    calc (1 + A * Real.log T) ^ 2 * Real.sqrt X / (lam * l ^ 2) / T
        ≤ (1 + A) ^ 2 * Real.log T ^ 2 * T ^ (lam / 2) / lam / T := by
          apply div_le_div_of_nonneg_right _ hT0.le
          calc (1 + A * Real.log T) ^ 2 * Real.sqrt X / (lam * l ^ 2)
              ≤ (1 + A * Real.log T) ^ 2 * Real.sqrt X / lam :=
                div_le_div_of_nonneg_left (by positivity) h0 (le_mul_of_one_le_right h0.le hl2)
            _ ≤ (1 + A) ^ 2 * Real.log T ^ 2 * T ^ (lam / 2) / lam := by gcongr
      _ = (1 + A) ^ 2 / lam * Real.log T ^ 2 * T ^ (lam / 2 - 1) := by
          rw [Real.rpow_sub_one hT0.ne']; field_simp
      _ ≤ d := r4
  have f4 : (lam * l) ^ 2 * X / (T * (lam * l) * l ^ 2) ≤ d := by
    have e : (lam * l) ^ 2 * X / (T * (lam * l) * l ^ 2) = lam / l * X / T := by field_simp
    rw [e]
    have hll : lam / l ≤ 1 := by rw [div_le_one hl0]; linarith
    calc lam / l * X / T ≤ 1 * T ^ lam / T := by
          apply div_le_div_of_nonneg_right _ hT0.le
          exact mul_le_mul hll hXT hX0.le zero_le_one
      _ = 1 * Real.log T ^ 0 * T ^ (lam - 1) := by rw [Real.rpow_sub_one hT0.ne']; ring
      _ ≤ d := r5
  have f5 : (1 + Real.log (A * Real.log T + 8) ^ 2) * T * (lam * l) ^ 2 / (T * (lam * l) * l ^ 2)
      ≤ d := by
    have e : (1 + Real.log (A * Real.log T + 8) ^ 2) * T * (lam * l) ^ 2 / (T * (lam * l) * l ^ 2)
        = lam * (1 + Real.log (A * Real.log T + 8) ^ 2) / l := by field_simp
    rw [e]
    have hnum : 0 ≤ 1 + Real.log (A * Real.log T + 8) ^ 2 := by positivity
    calc lam * (1 + Real.log (A * Real.log T + 8) ^ 2) / l
        ≤ 1 * (1 + Real.log (A * Real.log T + 8) ^ 2) / (Real.log T / 2) := by
          apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right h1.le hnum)
            (by positivity) hlo
      _ = 2 / Real.log T + 2 * (Real.log (A * Real.log T + 8) ^ 2 / Real.log T) := by
          field_simp
      _ ≤ d / 4 + 2 * (d / 4) := by
          have hA1 : 2 / Real.log T ≤ d / 4 := by
            rw [div_le_iff₀ hlogT]; rw [div_le_iff₀ hd0] at r7; linarith only [r7]
          have hA2 : Real.log (A * Real.log T + 8) ^ 2 / Real.log T ≤ d / 4 := by
            rw [div_le_iff₀ hlogT]; exact r6
          linarith only [hA1, hA2]
      _ ≤ d := by linarith only [hd0]
  have f6 : 2 * π / l ^ 2 ≤ d := by
    have hl2 : Real.log T ^ 2 / 4 ≤ l ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hlo 2; rw [div_pow] at this; linarith only [this]
    have hsq : 8 * π / d ≤ Real.log T ^ 2 := by
      have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) r8 2
      rwa [Real.sq_sqrt (by positivity)] at h
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hd0] at hsq
    have h4 : d * (Real.log T ^ 2 / 4) ≤ d * l ^ 2 := mul_le_mul_of_nonneg_left hl2 hd0.le
    nlinarith only [hsq, h4, Real.pi_gt_three]
  -- assemble
  have hmaj : 2 * π * frobMajorant lam A T / (T * (lam * l) * l ^ 2) ≤ 2 * π * (5 * d) := by
    have e : frobMajorant lam A T / (T * (lam * l) * l ^ 2)
        = (1 + A * Real.log T) ^ 2 * ((lam * l) * l * Real.log l * (l ^ 2 + X))
            / (T * (lam * l) * l ^ 2)
          + (1 + A * Real.log T) ^ 2 * (l ^ 2 * Real.log (lam * l)) / (T * (lam * l) * l ^ 2)
          + (1 + A * Real.log T) ^ 2 * (l * Real.sqrt X) / (T * (lam * l) * l ^ 2)
          + (lam * l) ^ 2 * X / (T * (lam * l) * l ^ 2)
          + (1 + Real.log (A * Real.log T + 8) ^ 2) * T * (lam * l) ^ 2 / (T * (lam * l) * l ^ 2) := by
      unfold frobMajorant; rw [← hldef, ← hXdef]; field_simp
    have : 2 * π * frobMajorant lam A T / (T * (lam * l) * l ^ 2)
        = 2 * π * (frobMajorant lam A T / (T * (lam * l) * l ^ 2)) := by ring
    rw [this, e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith only [f1, f2, f3, f4, f5]
  refine ⟨?_, ?_⟩
  · unfold rhoE
    rw [← hldef]
    calc C₂ * (2 * π * frobMajorant lam A T / (T * (lam * l) * l ^ 2) + 2 * π / l ^ 2)
        ≤ C₂ * (2 * π * (5 * d) + d) :=
          mul_le_mul_of_nonneg_left (by linarith only [hmaj, f6]) hC₂
      _ ≤ (C₂ + 1) * (2 * π * (5 * d) + d) :=
          mul_le_mul_of_nonneg_right (by linarith only) (by positivity)
      _ ≤ (C₂ + 1) * (2 * π * 6 * d) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith only [Real.pi_gt_three, hd0]
      _ = (2 * π * 6 * (C₂ + 1)) * d := by ring
      _ ≤ δ := by
          rw [hd, ← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith only [hδ]
  · rw [div_le_iff₀ hL0]
    rw [div_le_iff₀ (by positivity)] at r9
    have h := mul_le_mul_of_nonneg_left hlo (by positivity : (0:ℝ) ≤ lam * δ)
    linarith only [r9, h]

/-- `log(2π) ≤ 2`. -/
theorem log_two_pi_le_two : Real.log (2 * π) ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have := Real.exp_one_gt_d9
  rw [he]
  nlinarith [Real.pi_lt_d2]

/-- `ℓ_{1,q}(T) = log q + l(T) + 2 log 2 − 1`. -/
theorem ell1q_eq_log_add {q : ℕ} (hq : 1 ≤ q) {T : ℝ} (hT : 0 < T) :
    ell1q q T = Real.log q + Zeta23.l T + 2 * Real.log 2 - 1 := by
  unfold ell1q Zeta23.l
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [mul_div_assoc, Real.log_mul hq0.ne' (by positivity)]

/-- **The shape constant `c_λ = 1/λ_{1,q} + λ_{1,q}/3` is bounded uniformly for `q ≤ T^A`.** -/
theorem clam_le {lam A : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) (hA : 0 ≤ A) {q : ℕ} (hq : 1 ≤ q)
    {T : ℝ} (hT : 0 < T) (hl1 : 1 ≤ Zeta23.l T) (hlq : Real.log q ≤ A * Real.log T) :
    0 < 1 / lam1q (stdParams lam) q T + lam1q (stdParams lam) q T / 3
      ∧ 1 / lam1q (stdParams lam) q T + lam1q (stdParams lam) q T / 3 ≤ (3 * A + 2) / lam + 1 := by
  have hl0 : 0 < Zeta23.l T := by linarith
  have hell := ell1q_eq_log_add hq hT
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hlogT : Real.log T = Zeta23.l T + Real.log (2 * π) := by
    unfold Zeta23.l; rw [Real.log_div hT.ne' (by positivity)]; ring
  have h2π := log_two_pi_le_two
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog20 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2' : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hge : Zeta23.l T ≤ ell1q q T := by rw [hell]; linarith
  have hle : ell1q q T ≤ (3 * A + 2) * Zeta23.l T := by
    rw [hell]
    have : A * Real.log T ≤ A * (Zeta23.l T + 2) := by
      rw [hlogT]; exact mul_le_mul_of_nonneg_left (by linarith) hA
    nlinarith
  have hpos : 0 < ell1q q T := by linarith
  have hlam1 : lam1q (stdParams lam) q T = lam * Zeta23.l T / ell1q q T := rfl
  have hlampos : 0 < lam1q (stdParams lam) q T := by rw [hlam1]; positivity
  refine ⟨by positivity, ?_⟩
  have hinv : 1 / lam1q (stdParams lam) q T ≤ (3 * A + 2) / lam := by
    rw [hlam1, one_div_div, div_le_div_iff₀ (by positivity) h0]
    nlinarith
  have hl3 : lam1q (stdParams lam) q T / 3 ≤ 1 := by
    rw [hlam1, div_div, div_le_one (by positivity)]
    nlinarith
  linarith

/-- The uniform Frobenius error is nonnegative. -/
theorem tr2ErrUniform_nonneg {lam : ℝ} (h0 : 0 < lam) {q : ℕ} (hq : 1 ≤ q) {T : ℝ} (hT : 0 < T)
    (hl1 : 1 ≤ Zeta23.l T) (hL1 : 1 ≤ lam * Zeta23.l T) :
    0 ≤ tr2ErrUniform (stdParams lam) q T := by
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have h1 : 0 ≤ Real.log (Zeta23.l T) := Real.log_nonneg hl1
  have h2 : 0 ≤ Real.log (lam * Zeta23.l T) := Real.log_nonneg hL1
  have hL : (stdParams lam).L T = lam * Zeta23.l T := rfl
  unfold tr2ErrUniform
  rw [hL]
  have : 0 ≤ (stdParams lam).X T := (Real.exp_pos _).le
  positivity

/-- **The relative Frobenius error is below the modulus-free majorant.** -/
theorem ET_le_rhoE {lam A C₂ : ℝ} (h0 : 0 < lam) (hC₂ : 0 ≤ C₂) {q : ℕ} (hq : 1 ≤ q)
    {T : ℝ} (hT : 0 < T) (hl1 : 1 ≤ Zeta23.l T) (hL1 : 1 ≤ lam * Zeta23.l T)
    (hlq : Real.log q ≤ A * Real.log T) :
    C₂ * tr2ErrUniform (stdParams lam) q T / mainTr2Chi (stdParams lam) q T ≤ rhoE lam A C₂ T := by
  have hl0 : 0 < Zeta23.l T := by linarith
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hL : (stdParams lam).L T = lam * Zeta23.l T := rfl
  have hX : (stdParams lam).X T = Real.exp (lam * Zeta23.l T) := rfl
  have hell : Zeta23.l T ≤ ell1q q T := l_le_ell1q hq hT
  have hell0 : 0 < ell1q q T := by linarith
  set l := Zeta23.l T with hldef
  set L := lam * l with hLdef
  have hL0 : 0 < L := by positivity
  set X := Real.exp L with hXdef
  set ell := ell1q q T with helldef
  -- the modulus-dependent part is below the majorant
  have hΛ : (1 + Real.log q) ^ 2 ≤ (1 + A * Real.log T) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hll : Real.log (Real.log q + 8) ^ 2 ≤ Real.log (A * Real.log T + 8) ^ 2 := by
    have h1 : Real.log (Real.log q + 8) ≤ Real.log (A * Real.log T + 8) :=
      Real.log_le_log (by linarith) (by linarith)
    exact pow_le_pow_left₀ (Real.log_nonneg (by linarith)) h1 2
  have hinner : 0 ≤ L * l * Real.log l * (l ^ 2 + X) + l ^ 2 * Real.log L + l * Real.sqrt X := by
    have := Real.log_nonneg hl1; have := Real.log_nonneg hL1; positivity
  have hmaj : tr2ErrUniform (stdParams lam) q T ≤ frobMajorant lam A T + T * L * ell ^ 2 / l ^ 2 := by
    unfold tr2ErrUniform frobMajorant
    rw [hL, hX, ← hldef, ← hLdef, ← hXdef, ← helldef]
    have e1 := mul_le_mul_of_nonneg_right hΛ hinner
    have e2 : (1 + Real.log (Real.log q + 8) ^ 2) * T * L ^ 2
        ≤ (1 + Real.log (A * Real.log T + 8) ^ 2) * T * L ^ 2 := by
      have : 0 ≤ T * L ^ 2 := by positivity
      nlinarith
    linarith
  -- the main term from below
  have hmain : mainTr2Chi (stdParams lam) q T = T * L / (2 * π) * (ell ^ 2 + L ^ 2 / 3) := by
    unfold mainTr2Chi; rw [hL]
  have hm1 : T * L / (2 * π) * ell ^ 2 ≤ mainTr2Chi (stdParams lam) q T := by
    rw [hmain]; nlinarith [show 0 ≤ T * L / (2 * π) * (L ^ 2 / 3) by positivity]
  have hm2 : T * L / (2 * π) * l ^ 2 ≤ T * L / (2 * π) * ell ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0.le hell 2) (by positivity)
  have hmpos : 0 < mainTr2Chi (stdParams lam) q T := by
    have : 0 < T * L / (2 * π) * l ^ 2 := by positivity
    linarith
  have hfrob0 : 0 ≤ frobMajorant lam A T := by
    unfold frobMajorant
    rw [← hldef, ← hLdef, ← hXdef]
    have : 0 ≤ (1 + A * Real.log T) ^ 2 * (L * l * Real.log l * (l ^ 2 + X)
        + l ^ 2 * Real.log L + l * Real.sqrt X) := mul_nonneg (sq_nonneg _) hinner
    positivity
  have hdiv1 : frobMajorant lam A T / mainTr2Chi (stdParams lam) q T
      ≤ 2 * π * frobMajorant lam A T / (T * L * l ^ 2) := by
    rw [div_le_div_iff₀ hmpos (by positivity)]
    have : T * L * l ^ 2 = 2 * π * (T * L / (2 * π) * l ^ 2) := by field_simp
    rw [this]
    have h := mul_le_mul_of_nonneg_left (hm2.trans hm1) hfrob0
    calc frobMajorant lam A T * (2 * π * (T * L / (2 * π) * l ^ 2))
        = 2 * π * (frobMajorant lam A T * (T * L / (2 * π) * l ^ 2)) := by ring
      _ ≤ 2 * π * (frobMajorant lam A T * mainTr2Chi (stdParams lam) q T) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 * π * frobMajorant lam A T * mainTr2Chi (stdParams lam) q T := by ring
  have hdiv2 : T * L * ell ^ 2 / l ^ 2 / mainTr2Chi (stdParams lam) q T ≤ 2 * π / l ^ 2 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : T * L * ell ^ 2 = 2 * π * (T * L / (2 * π) * ell ^ 2) := by field_simp
    rw [this]
    have h := mul_le_mul_of_nonneg_left hm1 (by positivity : (0:ℝ) ≤ 2 * π * l ^ 2)
    nlinarith
  unfold rhoE
  rw [← hldef, ← hLdef]
  calc C₂ * tr2ErrUniform (stdParams lam) q T / mainTr2Chi (stdParams lam) q T
      = C₂ * (tr2ErrUniform (stdParams lam) q T / mainTr2Chi (stdParams lam) q T) := by ring
    _ ≤ C₂ * ((frobMajorant lam A T + T * L * ell ^ 2 / l ^ 2) / mainTr2Chi (stdParams lam) q T) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmaj hmpos.le) hC₂
    _ = C₂ * (frobMajorant lam A T / mainTr2Chi (stdParams lam) q T
          + T * L * ell ^ 2 / l ^ 2 / mainTr2Chi (stdParams lam) q T) := by rw [add_div]
    _ ≤ C₂ * (2 * π * frobMajorant lam A T / (T * L * l ^ 2) + 2 * π / l ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hdiv1 hdiv2) hC₂


/-- **Theorem E, uniformly in the modulus.** -/
theorem thmE_uniform {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {A : ℝ} (hA : 0 ≤ A) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q →
      (q : ℝ) ≤ T ^ A → χ.IsPrimitive →
      (Hfun (lam1q (stdParams lam) q T) - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) := by
  intro ε hε
  obtain ⟨ε', hε'def⟩ : ∃ x : ℝ, x = min ε 1 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε'def]; exact lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := by rw [hε'def]; exact min_le_right _ _
  have hε'ε : ε' ≤ ε := by rw [hε'def]; exact min_le_left _ _
  have hP : (stdParams lam).Valid := paramsOf_valid taperProfile_stdProfile h0 h1.le
  have hPfam : ParamsValidFam (stdParams lam) := ⟨hP.taper, hP.lam_pos, hP.one_le_w⟩
  obtain ⟨Cr, Tr, hrvm⟩ := mainChi_uniform
  obtain ⟨Ct, Tt, hCt, htr⟩ := prop_trace_uniform (stdParams lam).crho ⟨h0, h1.le⟩ (|Cr| * (A + 1))
  obtain ⟨C₂, T₂, hC₂, htr2⟩ := tr2_upper_uniform (stdParams lam) hP
  obtain ⟨TL, hTL⟩ := PrimeSide.localHypsEventually hP
  obtain ⟨R, hRdef⟩ : ∃ x : ℝ, x = Taper.l1Deriv2 stdProfile := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hRdef]; exact MeasureTheory.integral_nonneg fun x => abs_nonneg _
  have huA1 : 1 ≤ uniformA := one_le_uniformLocalCountConst
  obtain ⟨Cl, hCldef⟩ : ∃ x : ℝ, x = (3 * A + 2) / lam + 1 := ⟨_, rfl⟩
  have hCl1 : 1 ≤ Cl := by
    rw [hCldef]; have : 0 ≤ (3 * A + 2) / lam := by positivity
    linarith
  obtain ⟨δ, hδdef⟩ : ∃ x : ℝ, x = min 1 (ε' / (64 * Cl)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδε : δ ≤ ε' / (64 * Cl) := by rw [hδdef]; exact min_le_right _ _
  obtain ⟨δB, hδBdef⟩ : ∃ x : ℝ, x = min 1 (min (ε' / 40) (ε' / (16 * Real.sqrt (Cl + 1)))) :=
    ⟨_, rfl⟩
  have hsCl : 0 < Real.sqrt (Cl + 1) := Real.sqrt_pos.mpr (by linarith)
  have hδB0 : 0 < δB := by
    rw [hδBdef]; exact lt_min one_pos (lt_min (by positivity) (by positivity))
  have hδB1 : δB ≤ 1 := by rw [hδBdef]; exact min_le_left _ _
  have hδB2 : δB ≤ ε' / 40 := by rw [hδBdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδB3 : δB ≤ ε' / (16 * Real.sqrt (Cl + 1)) := by
    rw [hδBdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨K₅, hK₅def⟩ : ∃ x : ℝ, x = 64 * uniformA * R ^ 2 * (1 + A) / lam := ⟨_, rfl⟩
  have hK₅ : 0 ≤ K₅ := by rw [hK₅def]; have := huA1; positivity
  have hc32 : 0 < ε' / (32 * π) := by positivity
  -- the rates
  have ev := (eventually_l_bounds.and (eventually_ge_atTop
      (max (max (max Tr Tt) (max T₂ TL)) (max 300 (4 * π))))).and
    ((Real.tendsto_log_atTop.eventually_ge_atTop (16 / lam)).and
    ((eventually_rhoE_le h0 h1 hA hC₂ hδ0).and
    ((eventually_log_pow_rpow_le 1 (by norm_num : (0:ℝ) < 1)
        (by positivity : (0:ℝ) ≤ |Cr| * (A + 1)) (by positivity : (0:ℝ) < 1 / (4 * π))).and
    ((eventually_log_pow_rpow_le 1 (by norm_num : (0:ℝ) < 1)
        (by positivity : (0:ℝ) ≤ 8 * Cl * (|Cr| * (A + 1))) hc32).and
    ((eventually_log_pow_rpow_le 1 (by linarith : lam / 2 < 1)
        (by positivity : (0:ℝ) ≤ 8 * Ct * (1 + A)) hc32).and
    ((eventually_log_pow_rpow_le 2 (by norm_num : (1:ℝ) / 2 < 1)
        (by positivity : (0:ℝ) ≤ 18 * uniformA * (1 + A)) hc32).and
    (eventually_log_pow_rpow_le_const 1 (by linarith : lam / 2 - 1 < 0) hK₅ hδB0)))))))
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp ev
  refine ⟨T₀, fun T hT q _ χ hq hqT hprim => ?_⟩
  obtain ⟨⟨⟨hlog1, hl1, hlo, hhi⟩, hTge⟩, hlogL, ⟨hrho, hfourL⟩, r0, r3, r1, r4, r5⟩ := hT₀ T hT
  -- thresholds
  have hTr : Tr ≤ T := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hTge
  have hTt : Tt ≤ T := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hTge
  have hT2 : T₂ ≤ T := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hTge
  have hTLT : TL ≤ T := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hTge
  have hT300 : Tail.T₀ ≤ T := by
    show (300 : ℝ) ≤ T
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTge
  have hT4π : 4 * π ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hTge
  have hT0 : 0 < T := by have : (300:ℝ) ≤ T := hT300; linarith
  -- the parameters at T
  have hLdef : (stdParams lam).L T = lam * Zeta23.l T := rfl
  have hXdef : (stdParams lam).X T = Real.exp (lam * Zeta23.l T) := rfl
  have hw : (stdParams lam).w = 1 := rfl
  have hL8 : 8 ≤ (stdParams lam).L T := by
    rw [hLdef]
    rw [div_le_iff₀ h0] at hlogL
    have := mul_le_mul_of_nonneg_left hlo h0.le
    linarith only [hlogL, this]
  have hwL : 8 * (stdParams lam).w ≤ (stdParams lam).L T := by rw [hw]; linarith only [hL8]
  have hL1 : 1 ≤ lam * Zeta23.l T := by rw [← hLdef]; linarith only [hL8]
  have ha2 : 1 / 2 ≤ (stdParams lam).a T := half_le_a_fam hPfam hwL
  have ha1 : (stdParams lam).a T ≤ 1 := Params.a_le_one hP hwL
  have haL : 1 - 2 / (stdParams lam).L T ≤ (stdParams lam).a T := by
    have h1' := Params.one_sub_le_b hP hwL
    have h2' := Params.b_le_a hP hwL
    rw [hw, mul_one] at h1'
    linarith only [h1', h2']
  -- the modulus
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlq : Real.log q ≤ A * Real.log T := by
    rw [← Real.log_rpow hT0]; exact Real.log_le_log (by positivity) hqT
  have hΛ : 1 + Real.log q ≤ (1 + A) * Real.log T := by linarith only [hlq, hlog1]
  -- Riemann–von Mangoldt
  obtain ⟨N, hNdef⟩ : ∃ x : ℝ, x = (NcountL χ T (2 * T) : ℝ) := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hNdef]; exact Nat.cast_nonneg _
  have hRN : |(NcountL χ T (2 * T) : ℝ) - T / (2 * π) * ell1q q T| ≤ |Cr| * (A + 1) * Real.log T := by
    refine (hrvm q χ hq hprim T hTr).trans ?_
    have h1' : Real.log q + Real.log T ≤ (A + 1) * Real.log T := by linarith only [hlq]
    calc Cr * (Real.log q + Real.log T) ≤ |Cr| * (Real.log q + Real.log T) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith only [hlq0, hlog1])
      _ ≤ |Cr| * ((A + 1) * Real.log T) := mul_le_mul_of_nonneg_left h1' (abs_nonneg _)
      _ = |Cr| * (A + 1) * Real.log T := by ring
  have hRvM' : T * ell1q q T / (2 * π) ≤ (NcountL χ T (2 * T) : ℝ) + |Cr| * (A + 1) * Real.log T := by
    have := (abs_le.mp hRN).1
    have e : T / (2 * π) * ell1q q T = T * ell1q q T / (2 * π) := by ring
    linarith only [this, e]
  -- the trace
  have hcok := (coeffUnimodular_of_primitive hq hprim).toCoeffOK
  have htr1 : |trGtildeChi (stdParams lam) (parity χ) q (coeff χ) T
      - (stdParams lam).a T * (stdParams lam).L T * (NcountL χ T (2 * T) : ℝ)|
      ≤ Ct * (1 + Real.log q) * ((stdParams lam).L T * Real.sqrt ((stdParams lam).X T)) :=
    htr (parity χ) q parity_le_one hq.le (coeff χ) hcok ((stdParams lam).toSetting T)
      ((stdParams lam).localFun T) rfl hTt (hTL T hTLT).toCore _ hRN
  -- the Frobenius norm
  have htwo := htr2 (parity χ) q parity_le_one hq.le (coeff χ)
    (coeffUnimodular_of_primitive hq hprim) T hT2
  have hl0 : 0 < Zeta23.l T := by linarith
  have hell : Zeta23.l T ≤ ell1q q T := l_le_ell1q hq.le hT0
  have hmpos : 0 < mainTr2Chi (stdParams lam) q T := by
    unfold mainTr2Chi; rw [hLdef]
    have : 0 < ell1q q T := by linarith
    positivity
  obtain ⟨ET, hETdef⟩ : ∃ x : ℝ,
      x = C₂ * tr2ErrUniform (stdParams lam) q T / mainTr2Chi (stdParams lam) q T := ⟨_, rfl⟩
  have hET0 : 0 ≤ ET := by
    rw [hETdef]
    exact div_nonneg (mul_nonneg hC₂ (tr2ErrUniform_nonneg h0 hq.le hT0 hl1 hL1)) hmpos.le
  have htr2' : trGtildeSqChi (stdParams lam) (parity χ) q (coeff χ) T - mainTr2Chi (stdParams lam) q T
      ≤ ET * mainTr2Chi (stdParams lam) q T := by
    rw [hETdef, div_mul_cancel₀ _ hmpos.ne']; exact htwo
  have hE : ET ≤ rhoE lam A C₂ T := by
    rw [hETdef]; exact ET_le_rhoE h0 hC₂ hq.le hT0 hl1 hL1 hlq
  -- the seam
  have hseam := seam_at h0 h1.le hq hprim hT300 hwL htr1 hET0 htr2' hRvM'
  -- the error budget
  obtain ⟨hc0, hc⟩ := clam_le h0 h1.le hA hq.le hT0 hl1 hlq
  rw [← hCldef] at hc
  have hNl0 : 0 < T * Zeta23.l T / (4 * π) := by positivity
  have hNl1 : 1 ≤ T * Zeta23.l T / (4 * π) := by
    rw [le_div_iff₀ (by positivity)]
    have := le_mul_of_one_le_right hT0.le hl1
    linarith only [this, hT4π]
  have hlogT0 : 0 < Real.log T := by linarith
  have hT1l : T ≤ T * Zeta23.l T := le_mul_of_one_le_right hT0.le hl1
  have hshare : ε' / (32 * π) * T ≤ ε' / 8 * (T * Zeta23.l T / (4 * π)) := by
    have : ε' / 8 * (T * Zeta23.l T / (4 * π)) = ε' / (32 * π) * (T * Zeta23.l T) := by
      field_simp; ring
    rw [this]; exact mul_le_mul_of_nonneg_left hT1l hc32.le
  rw [Real.rpow_zero, mul_one, pow_one] at r0 r3
  rw [pow_one] at r1 r5
  have hNlow : T * Zeta23.l T / (4 * π) ≤ (NcountL χ T (2 * T) : ℝ) := by
    have h1' : T * Zeta23.l T / (2 * π) ≤ T * ell1q q T / (2 * π) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hell hT0.le) (by positivity)
    have h2' : |Cr| * (A + 1) * Real.log T ≤ T * Zeta23.l T / (4 * π) := by
      have : 1 / (4 * π) * T ≤ T * Zeta23.l T / (4 * π) := by
        rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hT1l (by positivity)
      linarith only [this, r0]
    have e : T * Zeta23.l T / (2 * π) = 2 * (T * Zeta23.l T / (4 * π)) := by field_simp; ring
    linarith only [h1', h2', e, hRvM']
  have hr2 : 4 * Cl * (rhoE lam A C₂ T + 4 / (stdParams lam).L T) ≤ ε' / 8 := by
    rw [hLdef]
    have h1' : rhoE lam A C₂ T + 4 / (lam * Zeta23.l T) ≤ 2 * δ := by linarith only [hrho, hfourL]
    calc 4 * Cl * (rhoE lam A C₂ T + 4 / (lam * Zeta23.l T)) ≤ 4 * Cl * (2 * δ) :=
          mul_le_mul_of_nonneg_left h1' (by positivity)
      _ ≤ 4 * Cl * (2 * (ε' / (64 * Cl))) :=
          mul_le_mul_of_nonneg_left (by linarith only [hδε]) (by positivity)
      _ = ε' / 8 := by field_simp; ring
  have hr3 : 8 * Cl * (|Cr| * (A + 1) * Real.log T) ≤ ε' / 8 * (T * Zeta23.l T / (4 * π)) := by
    have e : 8 * Cl * (|Cr| * (A + 1) * Real.log T) = 8 * Cl * (|Cr| * (A + 1)) * Real.log T := by ring
    rw [e]; exact r3.trans hshare
  have hsX : Real.sqrt ((stdParams lam).X T) ≤ T ^ (lam / 2) := by
    rw [hXdef]; exact sqrt_exp_lam_l_le h0.le hT0 hhi
  have hR₁ : 4 * (Ct * (1 + Real.log q) * Real.sqrt ((stdParams lam).X T) / (stdParams lam).a T)
      ≤ ε' / 8 * (T * Zeta23.l T / (4 * π)) := by
    have ha0 : 0 < (stdParams lam).a T := by linarith
    have hsX0 : 0 ≤ Real.sqrt ((stdParams lam).X T) := Real.sqrt_nonneg _
    have h1' : Ct * (1 + Real.log q) * Real.sqrt ((stdParams lam).X T) / (stdParams lam).a T
        ≤ 2 * (Ct * (1 + Real.log q) * Real.sqrt ((stdParams lam).X T)) := by
      rw [div_le_iff₀ ha0]
      have h0' : 0 ≤ Ct * (1 + Real.log q) * Real.sqrt ((stdParams lam).X T) := by positivity
      have := mul_le_mul_of_nonneg_left ha2 h0'
      linarith only [this]
    have h2' : Ct * (1 + Real.log q) * Real.sqrt ((stdParams lam).X T)
        ≤ Ct * ((1 + A) * Real.log T) * T ^ (lam / 2) := by
      gcongr
    have h3' : 8 * (Ct * ((1 + A) * Real.log T) * T ^ (lam / 2))
        = 8 * Ct * (1 + A) * Real.log T * T ^ (lam / 2) := by ring
    linarith only [r1, hshare, h1', h2', h3']
  have hNII : 3 * (NII (LZeros (LSeam_of hq hprim)) T : ℝ) ≤ ε' / 8 * (T * Zeta23.l T / (4 * π)) := by
    have h1' := uniform_NII_le hq hprim hT300
    have hlog4 : Real.log (4 * T) ≤ 2 * Real.log T := by
      rw [Real.log_mul (by norm_num) hT0.ne']
      have : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num)
        (by linarith only [hT4π, Real.pi_gt_three])
      linarith only [this]
    have hsT : Real.sqrt T = T ^ ((1:ℝ) / 2) := Real.sqrt_eq_rpow T
    have hsT0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
    have h2' : 3 * (2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) * (1 + Real.log q))
          * Real.sqrt T * Real.log (4 * T)
        ≤ 3 * (uniformA * ((1 + A) * Real.log T)) * Real.sqrt T * (2 * Real.log T) := by
      have hu0 : 0 ≤ uniformA := by linarith only [huA1]
      have hlog40 : 0 ≤ Real.log (4 * T) := Real.log_nonneg (by linarith only [hT4π, Real.pi_gt_three])
      gcongr
    have h3' : 3 * (3 * (uniformA * ((1 + A) * Real.log T)) * Real.sqrt T * (2 * Real.log T))
        = 18 * uniformA * (1 + A) * Real.log T ^ 2 * T ^ ((1:ℝ) / 2) := by rw [hsT]; ring
    have h4' : 3 * (NII (LZeros (LSeam_of hq hprim)) T : ℝ)
        ≤ 3 * (3 * (uniformA * ((1 + A) * Real.log T)) * Real.sqrt T * (2 * Real.log T)) := by
      have := h1'.trans h2'
      linarith only [this]
    linarith only [r4, hshare, h3', h4']
  -- the tail term
  have hA₀0 : 0 ≤ uniformA * (1 + Real.log q) := by positivity
  have hθ := theta0_le_fam hPfam hT300 hA₀0 (Tail.C1_nonneg (stdParams lam) T)
    (show (stdParams lam).C1 T ≤ 2 * R by rw [hRdef]; exact C1_le_fam hPfam hwL)
  have hθ0 : 0 ≤ Tail.theta0 (uniformA * (1 + Real.log q))
      (Real.exp ((stdParams lam).L T / 4) * (stdParams lam).C1 T) T :=
    Tail.theta0_nonneg hA₀0 hT300
  have ha0 : 0 < (stdParams lam).a T := by linarith
  have hL0 : 0 < (stdParams lam).L T := by linarith
  have hB0 : 0 ≤ Tail.theta0 (uniformA * (1 + Real.log q))
      (Real.exp ((stdParams lam).L T / 4) * (stdParams lam).C1 T) T
        / ((stdParams lam).a T * (stdParams lam).L T) := div_nonneg hθ0 (by positivity)
  have hB : Tail.theta0 (uniformA * (1 + Real.log q))
      (Real.exp ((stdParams lam).L T / 4) * (stdParams lam).C1 T) T
        / ((stdParams lam).a T * (stdParams lam).L T)
      ≤ K₅ * Real.log T * T ^ (lam / 2 - 1) := by
    have hplam : (stdParams lam).lam = lam := rfl
    rw [hplam] at hθ
    have hTp : 0 ≤ T ^ (lam / 2 - 1) := by positivity
    have hden : (stdParams lam).L T / 2 ≤ (stdParams lam).a T * (stdParams lam).L T := by
      have := mul_le_mul_of_nonneg_right ha2 hL0.le
      linarith only [this]
    calc Tail.theta0 (uniformA * (1 + Real.log q))
          (Real.exp ((stdParams lam).L T / 4) * (stdParams lam).C1 T) T
          / ((stdParams lam).a T * (stdParams lam).L T)
        ≤ 32 * (uniformA * (1 + Real.log q)) * R ^ 2 * Zeta23.l T * T ^ (lam / 2 - 1)
          / ((stdParams lam).L T / 2) :=
          div_le_div₀ (by positivity) hθ (by positivity) hden
      _ = 64 * uniformA * (1 + Real.log q) * R ^ 2 / lam * T ^ (lam / 2 - 1) := by
          rw [hLdef]; field_simp; ring
      _ ≤ 64 * uniformA * ((1 + A) * Real.log T) * R ^ 2 / lam * T ^ (lam / 2 - 1) := by
          gcongr
      _ = K₅ * Real.log T * T ^ (lam / 2 - 1) := by rw [hK₅def]; ring
  have hρB1 : K₅ * Real.log T * T ^ (lam / 2 - 1) ≤ 1 := r5.trans hδB1
  have hr5 : 5 * (K₅ * Real.log T * T ^ (lam / 2 - 1)) ≤ ε' / 8 * (T * Zeta23.l T / (4 * π)) := by
    have h1' : 5 * (K₅ * Real.log T * T ^ (lam / 2 - 1)) ≤ ε' / 8 := by
      have := r5.trans hδB2; linarith only [this]
    have h2' : ε' / 8 ≤ ε' / 8 * (T * Zeta23.l T / (4 * π)) :=
      le_mul_of_one_le_right (by positivity) hNl1
    linarith only [h1', h2']
  have hr6 : 2 * (K₅ * Real.log T * T ^ (lam / 2 - 1)) * Real.sqrt (Cl + 1)
      ≤ ε' / 8 * Real.sqrt (T * Zeta23.l T / (4 * π)) := by
    have h1' : 2 * (K₅ * Real.log T * T ^ (lam / 2 - 1)) * Real.sqrt (Cl + 1) ≤ ε' / 8 := by
      have h := mul_le_mul_of_nonneg_right (r5.trans hδB3) (by positivity : (0:ℝ) ≤ 2 * Real.sqrt (Cl + 1))
      have e : ε' / (16 * Real.sqrt (Cl + 1)) * (2 * Real.sqrt (Cl + 1)) = ε' / 8 := by
        field_simp; ring
      rw [e] at h
      linarith only [h]
    have h2' : ε' / 8 ≤ ε' / 8 * Real.sqrt (T * Zeta23.l T / (4 * π)) :=
      le_mul_of_one_le_right (by positivity) (Real.one_le_sqrt.mpr hNl1)
    linarith only [h1', h2']
  have hbudget := seam_error_le (N := (NcountL χ T (2 * T) : ℝ))
    (Nl := T * Zeta23.l T / (4 * π)) (c := 1 / lam1q (stdParams lam) q T
      + lam1q (stdParams lam) q T / 3) (C := Cl) (E := ET) (ρE := rhoE lam A C₂ T)
    (RN := |Cr| * (A + 1) * Real.log T)
    (R₁ := Ct * (1 + Real.log q) * Real.sqrt ((stdParams lam).X T) / (stdParams lam).a T)
    (ρB := K₅ * Real.log T * T ^ (lam / 2 - 1)) (ε := ε')
    hNl0 hNlow ha2 ha1 (by linarith only [hL8]) haL hc0 hc hET0 hE (hrho.trans hδ1) hr2
    (by positivity) hr3 rfl hR₁ hNII hB0 hB hρB1 hr5 hr6 hε'0 hε'1
  have hmono : (Hfun (lam1q (stdParams lam) q T) - ε) * (NcountL χ T (2 * T) : ℝ)
      ≤ (Hfun (lam1q (stdParams lam) q T) - ε') * (NcountL χ T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have e : (Hfun (lam1q (stdParams lam) q T) - ε') * (NcountL χ T (2 * T) : ℝ)
      = Hfun (lam1q (stdParams lam) q T) * (NcountL χ T (2 * T) : ℝ)
        - ε' * (NcountL χ T (2 * T) : ℝ) := by ring
  linarith only [hseam, hbudget, hmono, e]

/-- `H(x) = 2 − 1/x − x/3` increases on `(0, 1]`. -/
theorem Hfun_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) : Hfun x ≤ Hfun y := by
  unfold Hfun
  have hy0 : 0 < y := lt_of_lt_of_le hx hxy
  have hxy1 : x * y ≤ 1 := by nlinarith
  have h : 1 / x - 1 / y = (y - x) / (x * y) := by field_simp
  have h2 : (y - x) / 3 ≤ (y - x) / (x * y) := by
    apply div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
  linarith

/-- **Two thirds, uniformly in the modulus.**  For every `ε > 0` there are `κ > 0` and `T₀` such that for
all `T ≥ T₀`, every modulus `1 < q ≤ T^κ` and every primitive `χ` modulo `q`, at least
`(2/3 − ε) N_χ(T, 2T)` distinct zeros of `L(s, χ)` with ordinate in `(T, 2T]` lie on the critical line. -/
theorem thmE_uniform_two_thirds :
    ∀ ε > 0, ∃ κ : ℝ, 0 < κ ∧ ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      1 < q → (q : ℝ) ≤ T ^ κ → χ.IsPrimitive →
      (2 / 3 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) := by
  intro ε hε
  obtain ⟨η, hηdef⟩ : ∃ x : ℝ, x = min (1 / 6) (ε / 12) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hηdef]; exact lt_min (by norm_num) (by positivity)
  have hη6 : η ≤ 1 / 6 := by rw [hηdef]; exact min_le_left _ _
  have hηε : η ≤ ε / 12 := by rw [hηdef]; exact min_le_right _ _
  have hlam0 : 0 < 1 - η := by linarith
  have hlam1 : 1 - η < 1 := by linarith
  obtain ⟨T₁, hT₁⟩ := thmE_uniform hlam0 hlam1 hη0.le (ε / 2) (by positivity)
  have ev : ∀ᶠ T : ℝ in atTop, T₁ ≤ T ∧ 0 < T ∧ 3 / η + 2 ≤ Real.log T :=
    (eventually_ge_atTop T₁).and ((eventually_gt_atTop 0).and
      (Real.tendsto_log_atTop.eventually_ge_atTop (3 / η + 2)))
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp ev
  refine ⟨η, hη0, T₀, fun T hT q _ χ hq hqT hprim => ?_⟩
  obtain ⟨hTT₁, hT0, hlogT⟩ := hT₀ T hT
  have h := hT₁ T hTT₁ q χ hq hqT hprim
  -- the effective bandwidth
  have h2π := log_two_pi_le_two
  have hl : Zeta23.l T = Real.log T - Real.log (2 * π) := by
    unfold Zeta23.l; rw [Real.log_div hT0.ne' (by positivity)]
  have h2π0 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hl3 : 3 / η ≤ Zeta23.l T := by rw [hl]; linarith
  have hη3 : 0 < 3 / η := by positivity
  have hl0 : 0 < Zeta23.l T := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hlq : Real.log q ≤ η * Real.log T := by
    rw [← Real.log_rpow hT0]; exact Real.log_le_log (by positivity) hqT
  have hell := ell1q_eq_log_add hq.le hT0
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hellge : Zeta23.l T ≤ ell1q q T := l_le_ell1q hq.le hT0
  have hell0 : 0 < ell1q q T := by linarith
  have hηl : 3 ≤ η * Zeta23.l T := by
    have := mul_le_mul_of_nonneg_left hl3 hη0.le
    rwa [mul_div_cancel₀ _ hη0.ne'] at this
  have hellle : ell1q q T ≤ (1 + 2 * η) * Zeta23.l T := by
    rw [hell]
    have hlogT' : Real.log T = Zeta23.l T + Real.log (2 * π) := by rw [hl]; ring
    have : η * Real.log T ≤ η * (Zeta23.l T + 2) := by
      rw [hlogT']; exact mul_le_mul_of_nonneg_left (by linarith) hη0.le
    nlinarith
  have hlam1q : lam1q (stdParams (1 - η)) q T = (1 - η) * Zeta23.l T / ell1q q T := rfl
  have hx₀ : (1 - η) / (1 + 2 * η) ≤ lam1q (stdParams (1 - η)) q T := by
    rw [hlam1q, div_le_div_iff₀ (by positivity) hell0]
    have := mul_le_mul_of_nonneg_left hellle hlam0.le
    nlinarith
  have hx₁ : lam1q (stdParams (1 - η)) q T ≤ 1 := by
    rw [hlam1q, div_le_one hell0]; nlinarith
  have hx₀pos : 0 < (1 - η) / (1 + 2 * η) := by positivity
  have hmono := Hfun_mono hx₀pos hx₀ hx₁
  -- `H((1−η)/(1+2η)) ≥ 2/3 − 6η`
  have hlow : 1 - 3 * η ≤ (1 - η) / (1 + 2 * η) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hmono2 := Hfun_mono (by linarith) hlow (le_trans hx₀ hx₁)
  have hH : 2 / 3 - 6 * η ≤ Hfun (1 - 3 * η) := by
    unfold Hfun
    have ht : 0 < 1 - 3 * η := by linarith
    have hinv : 1 / (1 - 3 * η) ≤ 1 + 6 * η := by
      rw [div_le_iff₀ ht]; nlinarith
    linarith
  have hHq : 2 / 3 - ε / 2 ≤ Hfun (lam1q (stdParams (1 - η)) q T) := by linarith
  have hN0 : (0 : ℝ) ≤ NcountL χ T (2 * T) := Nat.cast_nonneg _
  have hstep : (2 / 3 - ε) * (NcountL χ T (2 * T) : ℝ)
      ≤ (Hfun (lam1q (stdParams (1 - η)) q T) - ε / 2) * (NcountL χ T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN0
  linarith

end RHTower
