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
theorem wienerScaleEval_mul {R : ℝ} {f g : PowerSeries ℂ}
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

/-! ## Ghost formation and its exact collar loss -/

theorem collar_unit_bound {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ((n : ℝ) + 1) * q ^ n * (1 - q) ≤ 1 := by
  have hstep : ((n : ℝ) + 1) * q ^ n ≤ ∑ k ∈ Finset.range (n + 1), q ^ k := by
    have hterm : ∀ k ∈ Finset.range (n + 1), q ^ n ≤ q ^ k := by
      intro k hk
      exact pow_le_pow_of_le_one hq0 hq1.le
        (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hk)
    calc ((n : ℝ) + 1) * q ^ n = ∑ _k ∈ Finset.range (n + 1), q ^ n := by
          rw [Finset.sum_const, Finset.card_range]
          ring
      _ ≤ _ := Finset.sum_le_sum hterm
  have hgeom : (∑ k ∈ Finset.range (n + 1), q ^ k) * (1 - q) = 1 - q ^ (n + 1) := by
    have h := geom_sum_mul q (n + 1)
    nlinarith [h]
  nlinarith [pow_nonneg hq0 (n + 1), sub_nonneg.mpr hq1.le, hstep, hgeom]

/-- The monomial collar inequality behind the derivative bound. -/
theorem wienerScale_collar_bound {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (n : ℕ) :
    ((n : ℝ) + 1) * r ^ n * (R - r) ≤ R ^ (n + 1) := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  set q : ℝ := r / R with hqdef
  have hq0 : 0 ≤ q := div_nonneg hr hR.le
  have hq1 : q < 1 := (div_lt_one hR).mpr hrR
  have hrq : r = q * R := by
    rw [hqdef]
    field_simp
  have hkey := collar_unit_bound hq0 hq1 n
  have hmul := mul_le_mul_of_nonneg_left hkey (mul_nonneg (pow_nonneg hR.le n) hR.le)
  rw [hrq, mul_pow, pow_succ]
  nlinarith [hmul]

theorem norm_natCast_succ (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
  push_cast
  ring

theorem wienerScaleWeight_derivative_le {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (f : PowerSeries ℂ)
    (n : ℕ) :
    wienerScaleWeight r ((d⁄dX ℂ) f) n ≤ (R - r)⁻¹ * wienerScaleWeight R f (n + 1) := by
  have hRr : 0 < R - r := by linarith
  have hcol := wienerScale_collar_bound hr hrR n
  have hdiv : ((n : ℝ) + 1) * r ^ n ≤ (R - r)⁻¹ * R ^ (n + 1) := by
    rw [inv_mul_eq_div, le_div_iff₀ hRr]
    linarith [hcol]
  rw [wienerScaleWeight, wienerScaleWeight, PowerSeries.coeff_derivative, norm_mul,
    norm_natCast_succ]
  nlinarith [hdiv, norm_nonneg ((PowerSeries.coeff (n + 1)) f)]

theorem WienerScaleAdmissible.derivative {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {f : PowerSeries ℂ} (hf : WienerScaleAdmissible R f) :
    WienerScaleAdmissible r ((d⁄dX ℂ) f) :=
  Summable.of_nonneg_of_le (fun n => wienerScaleWeight_nonneg hr _ n)
    (fun n => wienerScaleWeight_derivative_le hr hrR f n)
    (((summable_nat_add_iff 1).mpr hf).mul_left _)

/-- **Exact derivative collar loss.**  Ghost formation costs exactly the reciprocal collar width. -/
theorem wienerScaleNorm_derivative_le {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {f : PowerSeries ℂ} (hf : WienerScaleAdmissible R f) :
    wienerScaleNorm r ((d⁄dX ℂ) f) ≤ (R - r)⁻¹ * wienerScaleNorm R f := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hRr : 0 < R - r := by linarith
  have hshift : Summable fun n => wienerScaleWeight R f (n + 1) :=
    (summable_nat_add_iff 1).mpr hf
  have hle : wienerScaleNorm r ((d⁄dX ℂ) f)
      ≤ ∑' n, (R - r)⁻¹ * wienerScaleWeight R f (n + 1) :=
    Summable.tsum_le_tsum (fun n => wienerScaleWeight_derivative_le hr hrR f n)
      (hf.derivative hr hrR) (hshift.mul_left _)
  have htail : ∑' n, wienerScaleWeight R f (n + 1) ≤ wienerScaleNorm R f := by
    have hsplit := hf.tsum_eq_zero_add
    have h0 := wienerScaleWeight_nonneg hR.le f 0
    rw [wienerScaleNorm, hsplit]
    linarith
  calc wienerScaleNorm r ((d⁄dX ℂ) f)
      ≤ ∑' n, (R - r)⁻¹ * wienerScaleWeight R f (n + 1) := hle
    _ = (R - r)⁻¹ * ∑' n, wienerScaleWeight R f (n + 1) := tsum_mul_left
    _ ≤ (R - r)⁻¹ * wienerScaleNorm R f :=
        mul_le_mul_of_nonneg_left htail (by positivity)

/-! ## Adams intervention -/

/-- Adams intervention `Ψ_q f(T) = f(T^q)`. -/
noncomputable def wienerScaleAdams (q : ℕ) (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => if q ∣ n then (PowerSeries.coeff (n / q)) f else 0

theorem coeff_wienerScaleAdams (q n : ℕ) (f : PowerSeries ℂ) :
    (PowerSeries.coeff n) (wienerScaleAdams q f)
      = if q ∣ n then (PowerSeries.coeff (n / q)) f else 0 := by
  rw [wienerScaleAdams, PowerSeries.coeff_mk]

theorem wienerScaleWeight_adams_apply {q : ℕ} (hq : 1 ≤ q) (r : ℝ) (f : PowerSeries ℂ) (m : ℕ) :
    wienerScaleWeight r (wienerScaleAdams q f) (q * m) = wienerScaleWeight (r ^ q) f m := by
  have hq0 : q ≠ 0 := by omega
  rw [wienerScaleWeight, wienerScaleWeight, coeff_wienerScaleAdams,
    if_pos (Dvd.intro m rfl), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hq0), ← pow_mul]

theorem wienerScaleWeight_adams_of_not_dvd {q : ℕ} (r : ℝ) (f : PowerSeries ℂ) {n : ℕ}
    (hn : ¬ q ∣ n) : wienerScaleWeight r (wienerScaleAdams q f) n = 0 := by
  rw [wienerScaleWeight, coeff_wienerScaleAdams, if_neg hn, norm_zero, zero_mul]

theorem wienerScaleAdams_mul_injective {q : ℕ} (hq : 1 ≤ q) :
    Function.Injective fun m : ℕ => q * m := by
  intro a b hab
  have hq0 : 0 < q := by omega
  exact Nat.eq_of_mul_eq_mul_left hq0 hab

theorem wienerScaleAdams_support {q : ℕ} (r : ℝ) (f : PowerSeries ℂ) :
    ∀ n ∉ Set.range fun m : ℕ => q * m, wienerScaleWeight r (wienerScaleAdams q f) n = 0 := by
  intro n hn
  refine wienerScaleWeight_adams_of_not_dvd r f fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩

/-- **Adams substitution is an exact radius power on the receiver scale.** -/
theorem wienerScaleNorm_adams {q : ℕ} (hq : 1 ≤ q) (r : ℝ) (f : PowerSeries ℂ) :
    wienerScaleNorm r (wienerScaleAdams q f) = wienerScaleNorm (r ^ q) f := by
  have hcomp : (fun m : ℕ => wienerScaleWeight r (wienerScaleAdams q f) (q * m))
      = wienerScaleWeight (r ^ q) f := by
    funext m
    exact wienerScaleWeight_adams_apply hq r f m
  have hsupp : Function.support (wienerScaleWeight r (wienerScaleAdams q f))
      ⊆ Set.range fun m : ℕ => q * m := by
    intro n hn
    by_contra hcon
    exact hn (wienerScaleAdams_support r f n hcon)
  have h := (wienerScaleAdams_mul_injective hq).tsum_eq hsupp
  rw [wienerScaleNorm, wienerScaleNorm, ← h, hcomp]

theorem wienerScaleAdmissible_adams_iff {q : ℕ} (hq : 1 ≤ q) (r : ℝ) (f : PowerSeries ℂ) :
    WienerScaleAdmissible r (wienerScaleAdams q f) ↔ WienerScaleAdmissible (r ^ q) f := by
  have hcomp : wienerScaleWeight r (wienerScaleAdams q f) ∘ (fun m : ℕ => q * m)
      = wienerScaleWeight (r ^ q) f := by
    funext m
    exact wienerScaleWeight_adams_apply hq r f m
  have h := (wienerScaleAdams_mul_injective hq).summable_iff (wienerScaleAdams_support r f)
  rw [WienerScaleAdmissible, WienerScaleAdmissible, ← h, hcomp]

theorem WienerScaleAdmissible.adams {q : ℕ} (hq : 1 ≤ q) {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r ^ q ≤ R) {f : PowerSeries ℂ} (hf : WienerScaleAdmissible R f) :
    WienerScaleAdmissible r (wienerScaleAdams q f) :=
  (wienerScaleAdmissible_adams_iff hq r f).mpr (hf.mono (pow_nonneg hr q) hrR)

/-- **Adams aperture transport.**  If `r^q ≤ R` then `Ψ_q` maps `W_R` into `W_r` contractively. -/
theorem wienerScaleNorm_adams_le {q : ℕ} (hq : 1 ≤ q) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ^ q ≤ R)
    {f : PowerSeries ℂ} (hf : WienerScaleAdmissible R f) :
    wienerScaleNorm r (wienerScaleAdams q f) ≤ wienerScaleNorm R f := by
  rw [wienerScaleNorm_adams hq]
  exact wienerScaleNorm_mono (pow_nonneg hr q) hrR hf

/-- **Receiver covariance of Adams intervention.**  The pullback of a receiver is its `q`-th
power. -/
theorem wienerScaleEval_adams {q : ℕ} (hq : 1 ≤ q) (f : PowerSeries ℂ) (z : ℂ) :
    wienerScaleEval (wienerScaleAdams q f) z = wienerScaleEval f (z ^ q) := by
  have hcomp : (fun m : ℕ =>
        (PowerSeries.coeff (q * m)) (wienerScaleAdams q f) * z ^ (q * m))
      = fun m : ℕ => (PowerSeries.coeff m) f * (z ^ q) ^ m := by
    funext m
    have hq0 : q ≠ 0 := by omega
    rw [coeff_wienerScaleAdams, if_pos (Dvd.intro m rfl),
      Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hq0), ← pow_mul]
  have hsupp : Function.support
      (fun n => (PowerSeries.coeff n) (wienerScaleAdams q f) * z ^ n)
      ⊆ Set.range fun m : ℕ => q * m := by
    intro n hn
    by_contra hcon
    have hdvd : ¬ q ∣ n := fun ⟨m, hm⟩ => hcon ⟨m, hm.symm⟩
    refine hn ?_
    show (PowerSeries.coeff n) (wienerScaleAdams q f) * z ^ n = 0
    rw [coeff_wienerScaleAdams, if_neg hdvd, zero_mul]
  have h := (wienerScaleAdams_mul_injective hq).tsum_eq hsupp
  rw [wienerScaleEval, wienerScaleEval, ← h, hcomp]

/-! ## Finite Witt admission and conservation -/

/-- The geometric formation packet `(1 - xT)⁻¹`. -/
noncomputable def wienerScaleGeom (x : ℂ) : PowerSeries ℂ := PowerSeries.mk fun n => x ^ n

/-- The exterior and formation packets of a single marked mode are inverse. -/
theorem one_sub_mul_wienerScaleGeom (x : ℂ) :
    (1 - PowerSeries.C x * X) * wienerScaleGeom x = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, wienerScaleGeom, PowerSeries.coeff_mk, mul_assoc,
    PowerSeries.coeff_C_mul]
  cases n with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_one]
      simp [pow_succ]
      ring

theorem wienerScaleWeight_geom (R : ℝ) (x : ℂ) :
    wienerScaleWeight R (wienerScaleGeom x) = fun n => (‖x‖ * R) ^ n := by
  funext n
  rw [wienerScaleWeight, wienerScaleGeom, PowerSeries.coeff_mk, norm_pow, mul_pow]

theorem wienerScaleAdmissible_geom {R : ℝ} (hR : 0 ≤ R) {x : ℂ} (h : ‖x‖ * R < 1) :
    WienerScaleAdmissible R (wienerScaleGeom x) := by
  rw [WienerScaleAdmissible, wienerScaleWeight_geom]
  exact summable_geometric_of_lt_one (by positivity) h

/-- **Quantitative admission margin.**  `‖(1-xT)⁻¹‖_R = (1 - ‖x‖R)⁻¹`. -/
theorem wienerScaleNorm_geom {R : ℝ} (hR : 0 ≤ R) {x : ℂ} (h : ‖x‖ * R < 1) :
    wienerScaleNorm R (wienerScaleGeom x) = (1 - ‖x‖ * R)⁻¹ := by
  rw [wienerScaleNorm, wienerScaleWeight_geom]
  exact tsum_geometric_of_lt_one (by positivity) h

theorem wienerScaleAdmissible_one_sub_C_mul_X {R : ℝ} (hR : 0 ≤ R) (x : ℂ) :
    WienerScaleAdmissible R (1 - PowerSeries.C x * X) := by
  have hxX : PowerSeries.C x * X = x • (X : PowerSeries ℂ) := by
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_smul, smul_eq_mul]
  have hsub : (1 : PowerSeries ℂ) - PowerSeries.C x * X = 1 + -(x • X) := by
    rw [hxX]
    ring
  rw [hsub]
  exact (wienerScaleAdmissible_one R).add hR (((wienerScaleAdmissible_X R).smul x).neg)

/-- **Admitted finite Witt fusion.**  The exterior packet and the formation packet of a finite
marked mode family multiply to one. -/
theorem wienerScale_witt_fusion {ι : Type*} (s : Finset ι) (x : ι → ℂ) :
    (∏ i ∈ s, (1 - PowerSeries.C (x i) * X)) * (∏ i ∈ s, wienerScaleGeom (x i)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => one_sub_mul_wienerScaleGeom (x i)

theorem wienerScaleAdmissible_witt_formation {R : ℝ} (hR : 0 ≤ R) {ι : Type*} (s : Finset ι)
    (x : ι → ℂ) (hx : ∀ i ∈ s, ‖x i‖ * R < 1) :
    WienerScaleAdmissible R (∏ i ∈ s, wienerScaleGeom (x i)) :=
  Finset.prod_induction _ (WienerScaleAdmissible R) (fun _ _ ha hb => ha.mul hR hb)
    (wienerScaleAdmissible_one R) fun i hi => wienerScaleAdmissible_geom hR (hx i hi)

theorem wienerScaleAdmissible_witt_exterior {R : ℝ} (hR : 0 ≤ R) {ι : Type*} (s : Finset ι)
    (x : ι → ℂ) : WienerScaleAdmissible R (∏ i ∈ s, (1 - PowerSeries.C (x i) * X)) :=
  Finset.prod_induction _ (WienerScaleAdmissible R) (fun _ _ ha hb => ha.mul hR hb)
    (wienerScaleAdmissible_one R) fun i _ => wienerScaleAdmissible_one_sub_C_mul_X hR (x i)

/-! ## The ghost/Adams exchange law -/

/-- **Ghost/Adams exchange.**  Formal differentiation and Adams intervention commute up to the
ramification multiplier `q T^{q-1}`. -/
theorem derivative_wienerScaleAdams {q : ℕ} (hq : 1 ≤ q) (f : PowerSeries ℂ) :
    (d⁄dX ℂ) (wienerScaleAdams q f)
      = (q : ℂ) • (wienerScaleAdams q ((d⁄dX ℂ) f) * X ^ (q - 1)) := by
  obtain ⟨e, rfl⟩ : ∃ e, q = e + 1 := ⟨q - 1, by omega⟩
  ext n
  rw [PowerSeries.coeff_derivative, coeff_wienerScaleAdams, PowerSeries.coeff_smul, smul_eq_mul,
    PowerSeries.coeff_mul_X_pow']
  simp only [Nat.add_sub_cancel]
  by_cases hdvd : (e + 1) ∣ (n + 1)
  · rw [if_pos hdvd]
    obtain ⟨k, hk⟩ := hdvd
    have hkpos : k ≠ 0 := by
      rintro rfl
      omega
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.mul_succ] at hk
    have hn : n = (e + 1) * m + e := by omega
    have hle : e ≤ n := by omega
    have hsub : n - e = (e + 1) * m := by omega
    have hdiv : (n + 1) / (e + 1) = m + 1 := by
      have : n + 1 = (e + 1) * (m + 1) := by rw [Nat.mul_succ]; omega
      rw [this, Nat.mul_div_cancel_left _ (by omega)]
    rw [if_pos hle, hsub, hdiv, coeff_wienerScaleAdams,
      if_pos (Dvd.intro m rfl), Nat.mul_div_cancel_left _ (by omega),
      PowerSeries.coeff_derivative]
    have hnat : n + 1 = (e + 1) * (m + 1) := by
      rw [Nat.mul_succ]
      omega
    have hcast : (n : ℂ) + 1 = ((e : ℂ) + 1) * ((m : ℂ) + 1) := by
      exact_mod_cast congrArg (fun t : ℕ => (t : ℂ)) hnat
    rw [hcast]
    push_cast
    ring
  · rw [if_neg hdvd, zero_mul]
    by_cases hle : e ≤ n
    · rw [if_pos hle, coeff_wienerScaleAdams, if_neg, mul_zero]
      rintro ⟨j, hj⟩
      exact hdvd ⟨j + 1, by rw [Nat.mul_succ]; omega⟩
    · rw [if_neg hle, mul_zero]

/-- **Exchange bound.**  The composite ghost/Adams operation costs the ramified collar. -/
theorem wienerScaleNorm_derivative_adams_le {q : ℕ} (hq : 1 ≤ q) {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r ^ q < R) {f : PowerSeries ℂ} (hf : WienerScaleAdmissible R f) :
    wienerScaleNorm r ((d⁄dX ℂ) (wienerScaleAdams q f))
      ≤ (q : ℝ) * r ^ (q - 1) / (R - r ^ q) * wienerScaleNorm R f := by
  have hrq : (0 : ℝ) ≤ r ^ q := pow_nonneg hr q
  have hRrq : 0 < R - r ^ q := by linarith
  have hDf : WienerScaleAdmissible (r ^ q) ((d⁄dX ℂ) f) := hf.derivative hrq hrR
  have hAd : WienerScaleAdmissible r (wienerScaleAdams q ((d⁄dX ℂ) f)) :=
    (wienerScaleAdmissible_adams_iff hq r ((d⁄dX ℂ) f)).mpr hDf
  have hXp : WienerScaleAdmissible r (X ^ (q - 1) : PowerSeries ℂ) :=
    wienerScaleAdmissible_X_pow r (q - 1)
  have hmul := wienerScaleNorm_mul_le hr hAd hXp
  rw [wienerScaleNorm_X_pow] at hmul
  have hadams : wienerScaleNorm r (wienerScaleAdams q ((d⁄dX ℂ) f)) = wienerScaleNorm (r ^ q) ((d⁄dX ℂ) f) :=
    wienerScaleNorm_adams hq r _
  have hcol : wienerScaleNorm (r ^ q) ((d⁄dX ℂ) f) ≤ (R - r ^ q)⁻¹ * wienerScaleNorm R f :=
    wienerScaleNorm_derivative_le hrq hrR hf
  have hnormq : ‖(q : ℂ)‖ = (q : ℝ) := by
    rw [Complex.norm_natCast]
  have hfnn : 0 ≤ wienerScaleNorm R f := wienerScaleNorm_nonneg (by linarith) f
  rw [derivative_wienerScaleAdams hq, wienerScaleNorm_smul, hnormq]
  have hstep : wienerScaleNorm r (wienerScaleAdams q ((d⁄dX ℂ) f) * X ^ (q - 1))
      ≤ (R - r ^ q)⁻¹ * wienerScaleNorm R f * r ^ (q - 1) := by
    refine hmul.trans ?_
    rw [hadams]
    exact mul_le_mul_of_nonneg_right hcol (pow_nonneg hr (q - 1))
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  calc (q : ℝ) * wienerScaleNorm r (wienerScaleAdams q ((d⁄dX ℂ) f) * X ^ (q - 1))
      ≤ (q : ℝ) * ((R - r ^ q)⁻¹ * wienerScaleNorm R f * r ^ (q - 1)) :=
        mul_le_mul_of_nonneg_left hstep hqnn
    _ = (q : ℝ) * r ^ (q - 1) / (R - r ^ q) * wienerScaleNorm R f := by
        field_simp

/-! ## The Wiener receiver algebra -/

theorem wienerScaleAdmissible_C (R : ℝ) (c : ℂ) : WienerScaleAdmissible R (PowerSeries.C c) := by
  have h : PowerSeries.C c = c • (1 : PowerSeries ℂ) := by
    ext n
    simp [PowerSeries.coeff_C]
  rw [h]
  exact (wienerScaleAdmissible_one R).smul c

/-- The Wiener receiver algebra `W_R` inside the formal packets. -/
def wienerScaleAlgebra {R : ℝ} (hR : 0 ≤ R) : Subalgebra ℂ (PowerSeries ℂ) where
  carrier := {f | WienerScaleAdmissible R f}
  mul_mem' ha hb := WienerScaleAdmissible.mul hR ha hb
  one_mem' := wienerScaleAdmissible_one R
  add_mem' ha hb := WienerScaleAdmissible.add hR ha hb
  zero_mem' := wienerScaleAdmissible_zero R
  algebraMap_mem' c := by
    show WienerScaleAdmissible R _
    rw [PowerSeries.algebraMap_apply]
    simpa using wienerScaleAdmissible_C R c

theorem mem_wienerScaleAlgebra {R : ℝ} (hR : 0 ≤ R) {f : PowerSeries ℂ} :
    f ∈ wienerScaleAlgebra hR ↔ WienerScaleAdmissible R f := Iff.rfl

theorem wienerScaleEval_zero (z : ℂ) : wienerScaleEval 0 z = 0 := by
  rw [wienerScaleEval]
  simp

theorem wienerScaleEval_C (c : ℂ) (z : ℂ) : wienerScaleEval (PowerSeries.C c) z = c := by
  have h : (fun n => (PowerSeries.coeff n) (PowerSeries.C c) * z ^ n)
      = fun n => if n = 0 then c else 0 := by
    funext n
    by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]
  rw [wienerScaleEval, h]
  exact tsum_ite_eq 0 fun _ => c

/-- **Receiver evaluation as a character of `W_R`.** -/
noncomputable def wienerScaleEvalHom {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    wienerScaleAlgebra hR →ₐ[ℂ] ℂ where
  toFun f := wienerScaleEval (f : PowerSeries ℂ) z
  map_one' := by
    show wienerScaleEval ((1 : wienerScaleAlgebra hR) : PowerSeries ℂ) z = 1
    rw [Subalgebra.coe_one, wienerScaleEval_one]
  map_mul' f g := wienerScaleEval_mul f.2 g.2 hz
  map_zero' := by
    show wienerScaleEval ((0 : wienerScaleAlgebra hR) : PowerSeries ℂ) z = 0
    rw [Subalgebra.coe_zero, wienerScaleEval_zero]
  map_add' f g := wienerScaleEval_add f.2 g.2 hz
  commutes' c := by
    show wienerScaleEval ((algebraMap ℂ (wienerScaleAlgebra hR) c : wienerScaleAlgebra hR) :
      PowerSeries ℂ) z = c
    rw [Subalgebra.coe_algebraMap, PowerSeries.algebraMap_apply]
    simpa using wienerScaleEval_C c z

/-! ## Truncation and the character theorem -/

/-- The degree-`< N` truncation of a formal packet. -/
noncomputable def wienerScaleTrunc (N : ℕ) (f : PowerSeries ℂ) : PowerSeries ℂ :=
  ∑ n ∈ Finset.range N, PowerSeries.C ((PowerSeries.coeff n) f) * X ^ n

theorem coeff_wienerScaleTrunc (N : ℕ) (f : PowerSeries ℂ) (m : ℕ) :
    (PowerSeries.coeff m) (wienerScaleTrunc N f)
      = if m < N then (PowerSeries.coeff m) f else 0 := by
  rw [wienerScaleTrunc, map_sum]
  have hterm : ∀ n ∈ Finset.range N,
      (PowerSeries.coeff m) (PowerSeries.C ((PowerSeries.coeff n) f) * X ^ n)
        = if n = m then (PowerSeries.coeff n) f else 0 := by
    intro n _
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    by_cases h : m = n
    · subst h
      simp
    · rw [if_neg h, if_neg (fun hh => h hh.symm), mul_zero]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq' (Finset.range N) m fun n => (PowerSeries.coeff n) f]
  simp [Finset.mem_range]

theorem wienerScaleAdmissible_trunc {R : ℝ} (hR : 0 ≤ R) (N : ℕ) (f : PowerSeries ℂ) :
    WienerScaleAdmissible R (wienerScaleTrunc N f) := by
  have h : wienerScaleTrunc N f ∈ wienerScaleAlgebra hR := by
    refine Subalgebra.sum_mem _ fun n _ => ?_
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.pow_mem _ (wienerScaleAdmissible_X R) n)
  exact h

theorem wienerScaleWeight_sub_trunc (R : ℝ) (N : ℕ) (f : PowerSeries ℂ) (n : ℕ) :
    wienerScaleWeight R (f - wienerScaleTrunc N f) n
      = if n < N then 0 else wienerScaleWeight R f n := by
  rw [wienerScaleWeight, wienerScaleWeight, map_sub, coeff_wienerScaleTrunc]
  by_cases h : n < N <;> simp [h]

/-- The truncation defect is the exact Wiener tail. -/
theorem wienerScaleNorm_sub_trunc {R : ℝ} {f : PowerSeries ℂ} (hf : WienerScaleAdmissible R f)
    (N : ℕ) :
    wienerScaleNorm R (f - wienerScaleTrunc N f) = ∑' n, wienerScaleWeight R f (n + N) := by
  have hfun : wienerScaleWeight R (f - wienerScaleTrunc N f)
      = fun n => if n < N then 0 else wienerScaleWeight R f n := by
    funext n
    exact wienerScaleWeight_sub_trunc R N f n
  have hsum : Summable fun n => if n < N then (0 : ℝ) else wienerScaleWeight R f n := by
    refine Summable.of_norm_bounded (g := fun n => ‖wienerScaleWeight R f n‖) hf.norm fun n => ?_
    by_cases h : n < N <;> simp [h]
  have hsplit := hsum.sum_add_tsum_nat_add N
  have hhead : ∑ i ∈ Finset.range N, (if i < N then (0 : ℝ) else wienerScaleWeight R f i) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [if_pos (Finset.mem_range.mp hi)]
  have htail : (∑' i, if i + N < N then (0 : ℝ) else wienerScaleWeight R f (i + N))
      = ∑' i, wienerScaleWeight R f (i + N) := by
    refine tsum_congr fun i => ?_
    rw [if_neg (by omega)]
  rw [wienerScaleNorm, hfun, ← hsplit, hhead, htail, zero_add]

/-- **Character classification.**  Every bounded unital character of `W_R` is receiver evaluation
at a point of the closed disc of radius `R`. -/
theorem exists_eval_of_bounded_character {R : ℝ} (hR : 0 < R)
    (χ : wienerScaleAlgebra hR.le →ₐ[ℂ] ℂ) {Cb : ℝ}
    (hbdd : ∀ f : wienerScaleAlgebra hR.le, ‖χ f‖ ≤ Cb * wienerScaleNorm R (f : PowerSeries ℂ)) :
    ∃ z : ℂ, ‖z‖ ≤ R ∧
      ∀ f : wienerScaleAlgebra hR.le, χ f = wienerScaleEval (f : PowerSeries ℂ) z := by
  classical
  set Xw : wienerScaleAlgebra hR.le := ⟨X, wienerScaleAdmissible_X R⟩ with hXw
  refine ⟨χ Xw, ?_, ?_⟩
  · have hpow : ∀ n : ℕ, ‖χ Xw‖ ^ n ≤ Cb * R ^ n := by
      intro n
      have hcoe : ((Xw ^ n : wienerScaleAlgebra hR.le) : PowerSeries ℂ) = X ^ n := by
        rw [Subalgebra.coe_pow, hXw]
      have h := hbdd (Xw ^ n)
      rw [map_pow, norm_pow, hcoe, wienerScaleNorm_X_pow] at h
      exact h
    by_contra hcon
    rw [not_le] at hcon
    have hratio : 1 < ‖χ Xw‖ / R := (one_lt_div hR).mpr hcon
    obtain ⟨n, hn⟩ :=
      ((tendsto_pow_atTop_atTop_of_one_lt hratio).eventually_gt_atTop Cb).exists
    have hle : (‖χ Xw‖ / R) ^ n ≤ Cb := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      linarith [hpow n]
    linarith
  · intro f
    set z : ℂ := χ Xw with hz
    have hzR : ‖z‖ ≤ R := by
      have hpow : ∀ n : ℕ, ‖χ Xw‖ ^ n ≤ Cb * R ^ n := by
        intro n
        have hcoe : ((Xw ^ n : wienerScaleAlgebra hR.le) : PowerSeries ℂ) = X ^ n := by
          rw [Subalgebra.coe_pow, hXw]
        have h := hbdd (Xw ^ n)
        rw [map_pow, norm_pow, hcoe, wienerScaleNorm_X_pow] at h
        exact h
      by_contra hcon
      rw [not_le] at hcon
      have hratio : 1 < ‖χ Xw‖ / R := (one_lt_div hR).mpr (by rw [← hz]; exact hcon)
      obtain ⟨n, hn⟩ :=
        ((tendsto_pow_atTop_atTop_of_one_lt hratio).eventually_gt_atTop Cb).exists
      have hle : (‖χ Xw‖ / R) ^ n ≤ Cb := by
        rw [div_pow, div_le_iff₀ (by positivity)]
        linarith [hpow n]
      linarith
    set a : ℕ → ℂ := fun n => (PowerSeries.coeff n) (f : PowerSeries ℂ) with ha
    set S : ℕ → ℂ := fun N => ∑ n ∈ Finset.range N, a n * z ^ n with hS
    have htruncElt : ∀ N : ℕ,
        ((∑ n ∈ Finset.range N, a n • Xw ^ n : wienerScaleAlgebra hR.le) : PowerSeries ℂ)
          = wienerScaleTrunc N (f : PowerSeries ℂ) := by
      intro N
      rw [AddSubmonoidClass.coe_finsetSum, wienerScaleTrunc]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Subalgebra.coe_smul, Subalgebra.coe_pow, hXw]
      ext m
      rw [PowerSeries.coeff_smul, PowerSeries.coeff_C_mul, smul_eq_mul]
    have hchiTrunc : ∀ N : ℕ,
        χ (∑ n ∈ Finset.range N, a n • Xw ^ n) = S N := by
      intro N
      rw [map_sum, hS]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_smul, map_pow, smul_eq_mul, ← hz]
    have hdefect : ∀ N : ℕ, ‖χ f - S N‖ ≤ Cb * ∑' n, wienerScaleWeight R (f : PowerSeries ℂ) (n + N) := by
      intro N
      have hsub := hbdd (f - ∑ n ∈ Finset.range N, a n • Xw ^ n)
      rw [map_sub, hchiTrunc N, Subalgebra.coe_sub, htruncElt N,
        wienerScaleNorm_sub_trunc f.2 N] at hsub
      exact hsub
    have hzero : Filter.Tendsto
        (fun N => Cb * ∑' n, wienerScaleWeight R (f : PowerSeries ℂ) (n + N))
        Filter.atTop (nhds 0) := by
      have h := tendsto_sum_nat_add (wienerScaleWeight R (f : PowerSeries ℂ))
      simpa using h.const_mul Cb
    have hSchi : Filter.Tendsto S Filter.atTop (nhds (χ f)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hzero
      rw [← norm_neg]
      simpa using hdefect N
    have hSeval : Filter.Tendsto S Filter.atTop
        (nhds (wienerScaleEval (f : PowerSeries ℂ) z)) := by
      have hsum := wienerScaleEval_summable f.2 hzR
      exact hsum.hasSum.tendsto_sum_nat
    exact tendsto_nhds_unique hSchi hSeval

/-- **Receiver uniqueness.**  Two receiver points inducing the same character agree. -/
theorem wienerScaleEval_injective_point {R : ℝ} {z w : ℂ}
    (h : ∀ f : PowerSeries ℂ, WienerScaleAdmissible R f →
      wienerScaleEval f z = wienerScaleEval f w) : z = w := by
  have := h X (wienerScaleAdmissible_X R)
  rwa [wienerScaleEval_X, wienerScaleEval_X] at this

end HTGeometry
