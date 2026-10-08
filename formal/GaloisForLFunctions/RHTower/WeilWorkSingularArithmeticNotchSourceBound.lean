import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticNotchBudget
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticNotchLocalization
import GaloisForLFunctions.RHTower.WeilLittleOVonMangoldtRigidity

/-!
# The actual notch pairing is bounded by the four mass terms

This converts the existing lower moment and shifted-pole pairing receivers
into the mass budget controlled on good scales.
-/

noncomputable section
open Set Finset MeasureTheory GaloisForLFunctions.HTGeometry

namespace RHTower.WeilSingularArithmetic
open WeilAbscissa ZetaNotch

/-- A positive logarithmic lower moment forces a positive notch mass budget. -/
theorem exists_pairing_notchMassBudget_bound {q : ℝ → ℝ} {Q : ℂ → ℂ}
    (hQd : Differentiable ℂ Q) {CQ : ℝ} (hQb1 : ∀ z : ℂ, |z.im| ≤ 1 → ‖Q z‖ ≤ CQ)
    (hQq : ∀ t : ℝ, Q t = q t) (hq0 : ∀ t, 0 ≤ q t) (hqc : Continuous q)
    (hqb : ∀ t, |q t| ≤ CQ) {v : ℕ → ℝ} (hv0 : v 0 = 0)
    {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hs34 : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-(3 / 4 : ℝ)))
    (hs1 : Summable fun n : ℕ => |v n| * (n : ℝ)⁻¹)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ))
    {k C₀ Dr c : ℝ} {T₀ : ℕ} (hk : 0 < k) (hC₀ : 0 ≤ C₀) (hDr : 0 ≤ Dr) (hc : 0 < c)
    (hE : ∀ N : ℕ, T₀ ≤ N → ∀ u : ℝ, 16 ≤ u →
      u * (k * Real.log u - C₀) - Dr * refErrSum v (range (N + 1)) c 7 u ≤
        ∑ n ∈ range (N + 1), v n * (ZetaNotch.weightedMoment u q (Real.log n)).re) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ, 32 + T₀ ≤ L →
      (2 * Real.exp (-1) * k) * Real.log (L - 1) ≤
        C₀ * gaussHalf + K * notchMassBudget (sqrtScaled v) (2 * c) L := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hmix⟩ := exists_sum_re_mixMoment_ge_of_ramp hqc hqb
  obtain ⟨Csh, Cdf, hCsh, hCdf, hpair⟩ :=
    exists_sum_re_mixMoment_le_of_pairing hQd hQb1 hQq hq0 hqc hqb
  obtain ⟨CU, hCU, hU⟩ := exists_critUniform_le 4 7 (by norm_num)
  let a := Dr * gaussHalf
  let b := 4 * a
  let t := a * (266 + 133 * CU) + 2 * (C₁ + C₂) + Cdf
  let K := a + b + t + Csh
  have ha0 : 0 ≤ a := mul_nonneg hDr gaussHalf_nonneg
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK0, fun L hL => ?_⟩
  have hT₀ : 0 ≤ (T₀ : ℝ) := by positivity
  have hL32 : 32 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hLp : 0 < 1 + L := by linarith
  let N := ⌈(1 + L) ^ 2⌉₊
  let F := range (N + 1)
  let d := sqrtScaled v
  let H := ∑ n ∈ F, |d n| / n
  let I := ∑ n ∈ F, |d n| / Real.sqrt n * (if (n : ℝ) ≤ 2 * c * L then 1 else 0)
  let TF := ∑ n ∈ F, |d n| / Real.sqrt n
  let M := Real.log L / Real.sqrt L * I
  let U := TF / (1 + L)
  let R := (1 + L) * ∑' i : ℕ,
    (|d (i + (N + 1))| / (i + (N + 1) : ℕ)) / Real.sqrt (i + (N + 1) : ℕ)
  have hNT : T₀ ≤ N := by
    have hN := Nat.le_ceil ((1 + L) ^ 2)
    have h : (T₀ : ℝ) ≤ N := by dsimp [N]; nlinarith
    exact_mod_cast h
  have hHeq : (∑ n ∈ F, |v n| * (Real.sqrt n)⁻¹) = H :=
    Finset.sum_congr rfl fun n _ => abs_mul_inv_sqrt_eq v n
  have hIeq : (∑ n ∈ F, |v n| * (if (n : ℝ) ≤ 2 * c * L then 1 else 0)) = I :=
    Finset.sum_congr rfl fun n _ => by rw [abs_eq_sqrtScaled_div hv0]
  have hTeq : (∑ n ∈ F, |v n|) = TF :=
    Finset.sum_congr rfl fun n _ => abs_eq_sqrtScaled_div hv0 n
  have htaileq : (∑' i : ℕ, |v (i + (N + 1))| * ((i + (N + 1) : ℕ) : ℝ)⁻¹) =
      ∑' i : ℕ, (|d (i + (N + 1))| / (i + (N + 1) : ℕ)) /
        Real.sqrt (i + (N + 1) : ℕ) := by
    apply tsum_congr
    intro i
    rw [abs_eq_sqrtScaled_div hv0]
    dsimp [d]
    ring
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun n _ => by positivity
  have hI0 : 0 ≤ I := Finset.sum_nonneg fun n _ => by split_ifs <;> positivity
  have hTF0 : 0 ≤ TF := Finset.sum_nonneg fun n _ => by positivity
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨hEi, hEb⟩ := setIntegral_refErrSum_local_le hL32 hc.le hI0 hCU
    (le_of_eq hHeq) (le_of_eq hIeq) (le_of_eq hTeq) hU
  have hexp : Real.exp (-(L ^ 2 / 8)) ≤ 133 / (1 + L) := by
    have h := (inv_one_add_bounds hL32).1
    have hp : 0 ≤ ((L / 2) ^ (4 + 1))⁻¹ := by positivity
    have he := Real.exp_pos (-(L ^ 2 / 256))
    linarith
  have hEb' : (∫ u in Ioi 16, scaleWeight L u / u * refErrSum v F c 7 u) ≤
      (H + 4 * M + (266 + 133 * CU) * U) * gaussHalf := by
    apply hEb.trans
    apply mul_le_mul_of_nonneg_right _ gaussHalf_nonneg
    have h := mul_le_mul_of_nonneg_right hexp hTF0
    dsimp [M, U]
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith only [h]
  have hlow := hmix F hL32 hDr hk.le hC₀ (hE N hNT) hEi
  have hup := hpair hv0 hA ha hs34 hs1 hPD hL0 N
  rw [hTeq] at hlow
  change (∑ n ∈ F, v n * (mixMoment L q (Real.log n)).re) ≤ _ at hup
  rw [hTeq, htaileq] at hup
  obtain ⟨-, hboundary, hdefect⟩ := abs_small_errors_le hL32 hTF0 hCU hC₁ hC₂ hCdf
  have hErr := mul_le_mul_of_nonneg_left hEb' hDr
  have htotal : (2 * Real.exp (-1) * k) * Real.log (L - 1) ≤
      C₀ * gaussHalf + a * H + b * M + t * U + Csh * R := by
    dsimp [a, b, t, U, R]
    dsimp [U] at hErr
    simp only [div_eq_mul_inv] at hErr hlow hup hboundary hdefect ⊢
    nlinarith only [hlow, hup, hboundary, hdefect, hErr]
  have haK : a ≤ K := by dsimp [K]; linarith
  have hbK : b ≤ K := by dsimp [K]; linarith
  have htK : t ≤ K := by dsimp [K]; linarith
  have hrK : Csh ≤ K := by dsimp [K]; linarith
  have h1 := mul_le_mul_of_nonneg_right haK hH0
  have h2 := mul_le_mul_of_nonneg_right hbK hM0
  have h3 := mul_le_mul_of_nonneg_right htK hU0
  have h4 := mul_le_mul_of_nonneg_right hrK hR0
  have hbudget : notchMassBudget d (2 * c) L = H + M + U + R := rfl
  change _ ≤ C₀ * gaussHalf + K * notchMassBudget d (2 * c) L
  rw [hbudget]
  linarith

end RHTower.WeilSingularArithmetic
