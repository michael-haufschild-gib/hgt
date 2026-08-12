import Mathlib

/-!
# The Wiener receiver scale of formal formation packets

For a radius `R` the Wiener receiver `W_R` consists of the power series whose coefficient sequence
is absolutely summable against `R^n`, normed by

`‖f‖_R = ∑ ‖a_n‖ R^n`.

This file builds the scale itself: the admission predicate, the norm, its behaviour under the
algebra operations, the submultiplicative bound, monotonicity in the radius, and the receiver
characters `ev_z` for `‖z‖ ≤ R`.
-/

namespace HTGeometry

open Finset PowerSeries

/-! ## Admission and norm -/

/-- Weight of the `n`-th coefficient of `f` at receiver radius `R`. -/
noncomputable def wienerScaleWeight (R : ℝ) (f : PowerSeries ℂ) (n : ℕ) : ℝ :=
  ‖(PowerSeries.coeff n) f‖ * R ^ n

/-- Admission to the Wiener receiver of radius `R`. -/
def WienerScaleAdmissible (R : ℝ) (f : PowerSeries ℂ) : Prop :=
  Summable (wienerScaleWeight R f)

/-- The Wiener norm at receiver radius `R`. -/
noncomputable def wienerScaleNorm (R : ℝ) (f : PowerSeries ℂ) : ℝ :=
  ∑' n, wienerScaleWeight R f n

theorem wienerScaleWeight_nonneg {R : ℝ} (hR : 0 ≤ R) (f : PowerSeries ℂ) (n : ℕ) :
    0 ≤ wienerScaleWeight R f n :=
  mul_nonneg (norm_nonneg _) (pow_nonneg hR n)

theorem wienerScaleNorm_nonneg {R : ℝ} (hR : 0 ≤ R) (f : PowerSeries ℂ) :
    0 ≤ wienerScaleNorm R f :=
  tsum_nonneg fun n => wienerScaleWeight_nonneg hR f n

/-! ### Constants and monomials -/

theorem wienerScaleWeight_zero (R : ℝ) : wienerScaleWeight R 0 = fun _ => 0 := by
  funext n
  simp [wienerScaleWeight]

theorem wienerScaleAdmissible_zero (R : ℝ) : WienerScaleAdmissible R 0 := by
  rw [WienerScaleAdmissible, wienerScaleWeight_zero]
  exact summable_zero

theorem wienerScaleNorm_zero (R : ℝ) : wienerScaleNorm R 0 = 0 := by
  rw [wienerScaleNorm, wienerScaleWeight_zero, tsum_zero]

theorem wienerScaleWeight_X_pow (R : ℝ) (m : ℕ) :
    wienerScaleWeight R (X ^ m) = fun n => if n = m then R ^ m else 0 := by
  funext n
  by_cases h : n = m <;> simp [wienerScaleWeight, PowerSeries.coeff_X_pow, h]

theorem wienerScaleAdmissible_X_pow (R : ℝ) (m : ℕ) : WienerScaleAdmissible R (X ^ m) := by
  rw [WienerScaleAdmissible, wienerScaleWeight_X_pow]
  exact summable_of_ne_finset_zero (s := {m}) fun n hn => by
    simp only [Finset.mem_singleton] at hn
    simp [hn]

theorem wienerScaleNorm_X_pow (R : ℝ) (m : ℕ) : wienerScaleNorm R (X ^ m) = R ^ m := by
  rw [wienerScaleNorm, wienerScaleWeight_X_pow]
  exact tsum_ite_eq m fun _ => R ^ m

theorem wienerScaleAdmissible_one (R : ℝ) : WienerScaleAdmissible R 1 := by
  simpa using wienerScaleAdmissible_X_pow R 0

theorem wienerScaleNorm_one (R : ℝ) : wienerScaleNorm R 1 = 1 := by
  simpa using wienerScaleNorm_X_pow R 0

theorem wienerScaleAdmissible_X (R : ℝ) : WienerScaleAdmissible R X := by
  simpa using wienerScaleAdmissible_X_pow R 1

theorem wienerScaleNorm_X (R : ℝ) : wienerScaleNorm R X = R := by
  simpa using wienerScaleNorm_X_pow R 1

/-! ### Additive structure -/

theorem wienerScaleWeight_add_le {R : ℝ} (hR : 0 ≤ R) (f g : PowerSeries ℂ) (n : ℕ) :
    wienerScaleWeight R (f + g) n ≤ wienerScaleWeight R f n + wienerScaleWeight R g n := by
  simp only [wienerScaleWeight, map_add]
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg hR n)

theorem WienerScaleAdmissible.add {R : ℝ} (hR : 0 ≤ R) {f g : PowerSeries ℂ}
    (hf : WienerScaleAdmissible R f) (hg : WienerScaleAdmissible R g) :
    WienerScaleAdmissible R (f + g) :=
  Summable.of_nonneg_of_le (fun n => wienerScaleWeight_nonneg hR _ n)
    (fun n => wienerScaleWeight_add_le hR f g n) (Summable.add hf hg)

theorem wienerScaleNorm_add_le {R : ℝ} (hR : 0 ≤ R) {f g : PowerSeries ℂ}
    (hf : WienerScaleAdmissible R f) (hg : WienerScaleAdmissible R g) :
    wienerScaleNorm R (f + g) ≤ wienerScaleNorm R f + wienerScaleNorm R g := by
  rw [wienerScaleNorm, wienerScaleNorm, wienerScaleNorm, ← (hf.tsum_add hg)]
  exact Summable.tsum_le_tsum (fun n => wienerScaleWeight_add_le hR f g n)
    (WienerScaleAdmissible.add hR hf hg) (Summable.add hf hg)

theorem wienerScaleWeight_neg (R : ℝ) (f : PowerSeries ℂ) :
    wienerScaleWeight R (-f) = wienerScaleWeight R f := by
  funext n
  simp [wienerScaleWeight]

theorem WienerScaleAdmissible.neg {R : ℝ} {f : PowerSeries ℂ} (hf : WienerScaleAdmissible R f) :
    WienerScaleAdmissible R (-f) := by
  rwa [WienerScaleAdmissible, wienerScaleWeight_neg]

theorem wienerScaleNorm_neg (R : ℝ) (f : PowerSeries ℂ) :
    wienerScaleNorm R (-f) = wienerScaleNorm R f := by
  rw [wienerScaleNorm, wienerScaleNorm, wienerScaleWeight_neg]

theorem wienerScaleWeight_smul (R : ℝ) (c : ℂ) (f : PowerSeries ℂ) :
    wienerScaleWeight R (c • f) = fun n => ‖c‖ * wienerScaleWeight R f n := by
  funext n
  simp only [wienerScaleWeight, PowerSeries.coeff_smul, smul_eq_mul, norm_mul]
  ring

theorem WienerScaleAdmissible.smul {R : ℝ} (c : ℂ) {f : PowerSeries ℂ}
    (hf : WienerScaleAdmissible R f) : WienerScaleAdmissible R (c • f) := by
  rw [WienerScaleAdmissible, wienerScaleWeight_smul]
  exact hf.mul_left _

theorem wienerScaleNorm_smul (R : ℝ) (c : ℂ) (f : PowerSeries ℂ) :
    wienerScaleNorm R (c • f) = ‖c‖ * wienerScaleNorm R f := by
  rw [wienerScaleNorm, wienerScaleNorm, wienerScaleWeight_smul, tsum_mul_left]

/-! ### Cauchy multiplication -/

theorem wienerScaleWeight_mul_le {R : ℝ} (hR : 0 ≤ R) (f g : PowerSeries ℂ) (n : ℕ) :
    wienerScaleWeight R (f * g) n
      ≤ ∑ p ∈ antidiagonal n, wienerScaleWeight R f p.1 * wienerScaleWeight R g p.2 := by
  rw [wienerScaleWeight, PowerSeries.coeff_mul]
  have h1 : ‖∑ p ∈ antidiagonal n, (PowerSeries.coeff p.1) f * (PowerSeries.coeff p.2) g‖
      ≤ ∑ p ∈ antidiagonal n, ‖(PowerSeries.coeff p.1) f‖ * ‖(PowerSeries.coeff p.2) g‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
    exact le_of_eq (norm_mul _ _)
  calc ‖∑ p ∈ antidiagonal n, (PowerSeries.coeff p.1) f * (PowerSeries.coeff p.2) g‖ * R ^ n
      ≤ (∑ p ∈ antidiagonal n,
          ‖(PowerSeries.coeff p.1) f‖ * ‖(PowerSeries.coeff p.2) g‖) * R ^ n :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg hR n)
    _ = ∑ p ∈ antidiagonal n, wienerScaleWeight R f p.1 * wienerScaleWeight R g p.2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p hp => ?_
        have hpn : p.1 + p.2 = n := List.Nat.mem_antidiagonal.mp hp
        rw [wienerScaleWeight, wienerScaleWeight, ← hpn, pow_add]
        ring

theorem wienerScaleWeight_summable_prod {R : ℝ} (hR : 0 ≤ R) {f g : PowerSeries ℂ}
    (hf : WienerScaleAdmissible R f) (hg : WienerScaleAdmissible R g) :
    Summable fun x : ℕ × ℕ => wienerScaleWeight R f x.1 * wienerScaleWeight R g x.2 :=
  hf.mul_of_nonneg hg (fun n => wienerScaleWeight_nonneg hR f n)
    (fun n => wienerScaleWeight_nonneg hR g n)

/-- **The Wiener receiver is closed under formation.** -/
theorem WienerScaleAdmissible.mul {R : ℝ} (hR : 0 ≤ R) {f g : PowerSeries ℂ}
    (hf : WienerScaleAdmissible R f) (hg : WienerScaleAdmissible R g) :
    WienerScaleAdmissible R (f * g) :=
  Summable.of_nonneg_of_le (fun n => wienerScaleWeight_nonneg hR _ n)
    (fun n => wienerScaleWeight_mul_le hR f g n)
    (summable_sum_mul_antidiagonal_of_summable_mul (wienerScaleWeight_summable_prod hR hf hg))

/-- **Submultiplicativity of the Wiener norm.** -/
theorem wienerScaleNorm_mul_le {R : ℝ} (hR : 0 ≤ R) {f g : PowerSeries ℂ}
    (hf : WienerScaleAdmissible R f) (hg : WienerScaleAdmissible R g) :
    wienerScaleNorm R (f * g) ≤ wienerScaleNorm R f * wienerScaleNorm R g := by
  have hFG := wienerScaleWeight_summable_prod hR hf hg
  have hH := summable_sum_mul_antidiagonal_of_summable_mul hFG
  have hprod := Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hf hg hFG
  calc wienerScaleNorm R (f * g)
      ≤ ∑' n, ∑ p ∈ antidiagonal n, wienerScaleWeight R f p.1 * wienerScaleWeight R g p.2 :=
        Summable.tsum_le_tsum (fun n => wienerScaleWeight_mul_le hR f g n) (hf.mul hR hg) hH
    _ = wienerScaleNorm R f * wienerScaleNorm R g := hprod.symm

/-! ### Radius monotonicity -/

theorem wienerScaleWeight_mono {R S : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S) (f : PowerSeries ℂ) (n : ℕ) :
    wienerScaleWeight R f n ≤ wienerScaleWeight S f n :=
  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR hRS n) (norm_nonneg _)

/-- A larger receiver radius is a stronger admission. -/
theorem WienerScaleAdmissible.mono {R S : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S) {f : PowerSeries ℂ}
    (hf : WienerScaleAdmissible S f) : WienerScaleAdmissible R f :=
  Summable.of_nonneg_of_le (fun n => wienerScaleWeight_nonneg hR f n)
    (fun n => wienerScaleWeight_mono hR hRS f n) hf

theorem wienerScaleNorm_mono {R S : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S) {f : PowerSeries ℂ}
    (hf : WienerScaleAdmissible S f) : wienerScaleNorm R f ≤ wienerScaleNorm S f :=
  Summable.tsum_le_tsum (fun n => wienerScaleWeight_mono hR hRS f n) (hf.mono hR hRS) hf

/-! ## Receiver evaluation -/

/-- Receiver evaluation of an admitted packet at the point `z`. -/
noncomputable def wienerScaleEval (f : PowerSeries ℂ) (z : ℂ) : ℂ :=
  ∑' n, (PowerSeries.coeff n) f * z ^ n

theorem wienerScaleEval_summable {R : ℝ} {f : PowerSeries ℂ} (hf : WienerScaleAdmissible R f)
    {z : ℂ} (hz : ‖z‖ ≤ R) : Summable fun n => (PowerSeries.coeff n) f * z ^ n := by
  refine Summable.of_norm_bounded hf fun n => ?_
  rw [norm_mul, norm_pow, wienerScaleWeight]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n) (norm_nonneg _)

/-- **Receiver bound.**  Evaluation on the closed receiver disc is contractive. -/
theorem norm_wienerScaleEval_le {R : ℝ} {f : PowerSeries ℂ} (hf : WienerScaleAdmissible R f)
    {z : ℂ} (hz : ‖z‖ ≤ R) : ‖wienerScaleEval f z‖ ≤ wienerScaleNorm R f := by
  refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hf
    rw [norm_mul, norm_pow, wienerScaleWeight]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n) (norm_nonneg _)
  · refine Summable.tsum_le_tsum (fun n => ?_)
      (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hf) hf
    · rw [norm_mul, norm_pow, wienerScaleWeight]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n) (norm_nonneg _)
    · rw [norm_mul, norm_pow, wienerScaleWeight]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n) (norm_nonneg _)

theorem wienerScaleEval_X_pow (m : ℕ) (z : ℂ) : wienerScaleEval (X ^ m) z = z ^ m := by
  have h : (fun n => (PowerSeries.coeff n) (X ^ m : PowerSeries ℂ) * z ^ n)
      = fun n => if n = m then z ^ m else 0 := by
    funext n
    by_cases h : n = m <;> simp [PowerSeries.coeff_X_pow, h]
  rw [wienerScaleEval, h]
  exact tsum_ite_eq m fun _ => z ^ m

theorem wienerScaleEval_one (z : ℂ) : wienerScaleEval 1 z = 1 := by
  simpa using wienerScaleEval_X_pow 0 z

theorem wienerScaleEval_X (z : ℂ) : wienerScaleEval X z = z := by
  simpa using wienerScaleEval_X_pow 1 z

theorem wienerScaleEval_add {R : ℝ} {f g : PowerSeries ℂ} (hf : WienerScaleAdmissible R f)
    (hg : WienerScaleAdmissible R g) {z : ℂ} (hz : ‖z‖ ≤ R) :
    wienerScaleEval (f + g) z = wienerScaleEval f z + wienerScaleEval g z := by
  rw [wienerScaleEval, wienerScaleEval, wienerScaleEval,
    ← (wienerScaleEval_summable hf hz).tsum_add (wienerScaleEval_summable hg hz)]
  exact tsum_congr fun n => by rw [map_add]; ring

theorem wienerScaleEval_smul (c : ℂ) (f : PowerSeries ℂ) (z : ℂ) :
    wienerScaleEval (c • f) z = c * wienerScaleEval f z := by
  rw [wienerScaleEval, wienerScaleEval, ← tsum_mul_left]
  exact tsum_congr fun n => by rw [PowerSeries.coeff_smul, smul_eq_mul]; ring

/-- **Receiver evaluation is multiplicative.** -/
theorem wienerScaleEval_mul {R : ℝ} (hR : 0 ≤ R) {f g : PowerSeries ℂ}
    (hf : WienerScaleAdmissible R f) (hg : WienerScaleAdmissible R g) {z : ℂ} (hz : ‖z‖ ≤ R) :
    wienerScaleEval (f * g) z = wienerScaleEval f z * wienerScaleEval g z := by
  have hfn : Summable fun n => ‖(PowerSeries.coeff n) f * z ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hf
    rw [norm_mul, norm_pow, wienerScaleWeight]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n) (norm_nonneg _)
  have hgn : Summable fun n => ‖(PowerSeries.coeff n) g * z ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hg
    rw [norm_mul, norm_pow, wienerScaleWeight]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n) (norm_nonneg _)
  rw [wienerScaleEval, wienerScaleEval, wienerScaleEval,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn]
  refine tsum_congr fun n => ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpn : p.1 + p.2 = n := List.Nat.mem_antidiagonal.mp hp
  rw [← hpn, pow_add]
  ring

end HTGeometry
