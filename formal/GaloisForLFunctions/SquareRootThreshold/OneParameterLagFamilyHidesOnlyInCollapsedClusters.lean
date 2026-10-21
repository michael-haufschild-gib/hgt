import GaloisForLFunctions.SquareRootThreshold.ZetaNearTopZerosHideOnlyInCollapsedClusters

/-!
# The one-parameter lag family hides only in collapsed clusters

The cluster theory of `ZetaNearTopZerosHideOnlyInCollapsedClusters` uses the bump modulated to the
height of a near-top zero. Here it is carried over to the one-parameter family itself, the
difference tests `κ_w(t + v/2) − κ_w(t − v/2)` of one fixed width `w`, whose window functionals are
the lag family `P_v`.

* **Coefficients** (`two_mul_sq_le_norm_evenCoeff_zero`). A zero `½ + z₀` and its conjugate enter
  the unmodulated family with the same coefficient: `|D(z₀)| = 2m|h_w(γ₀ − iδ₀)|² ≥ 2η²`,
  `η = |h_w(γ₀ − iδ₀)|`. For a generic width `η ≠ 0` at every zero.
* **Records** (`exists_loud_record`, `one_param_record_facts`). If `½ + z₀` is `1/V`-near the top,
  the record keeps `|D(z*)| ≥ 2η²/e`; the decay of `h_w` then bounds its height by
  `Γ₀(η) = (2880 · 80(e^{w/2}B_w)² e/(2η²))^{1/3}` (`oneParamRecordHeight`), and its depth is at least
  `δ₀/2` once `V δ₀ ≥ 2 log(80 log(180Γ₀)(e^{w/2}B_w)²/(2η²))`.
* **Mass** (`xi_ratio_le_general`). For the unmodulated family `|M| + W ≤ 32(e^{w/2}B_w)²(C + log 4)`,
  a constant of the width.
* **Collapse** (`one_param_cluster_collapse`). Positivity of `P_v` for `v ∈ [0, V]` forces the record
  to carry a cluster of `p ≤ P` zeros, `P ≥ 80 log(180Γ₀)`, with
  `Π_{z ∈ C}|z − z*| (κ₀/(2(P + 1)))^p V^{2k+p+1} (δ₀/8)^{2k+1} ≤ B₀(p)` (`oneParamCollapseBound`).

All constants are explicit in `w` and `η`. The near-top zero enters only through `η`, its depth, and
`1/V`-nearness: a hidden near-top zero of the one-parameter family needs, at its record, an
approximate multiple zero of multiplicity `≤ P + 1 = O(log(1/η))` at geometric radius
`e^{−cVδ₀/p}`, or `V ≲ log(log(1/η)/η)/δ₀`. For the smooth bump `κ_w`, `η` decays with the height `γ₀`,
which is the price of a fixed width against the modulation.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The coefficient of a zero in the one-parameter family -/

/-- For `ζ` the unmodulated family sees a zero `½ + z` and its conjugate with the same coefficient:
`|D(z)| ≥ 2 |h_w(−iz)|²`. -/
theorem two_mul_sq_le_norm_evenCoeff_zero {w : ℝ} (hw : 0 < w) {z : ℂ}
    (hz : (1 / 2 + z) ∈ zetaZeroConfig.carrier) :
    2 * ‖paperFT (scaledBump w) (-(I * z))‖ ^ 2 ≤
      ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ := by
  rw [evenCoeff_modScaledBump_zero zetaZeroConfig hw hz]
  have hzc : (1 / 2 + conj z) ∈ zetaZeroConfig.carrier := by
    have := conj_mem_zetaZeroConfig hz
    have e : conj (1 / 2 + z) = 1 / 2 + conj z := by apply Complex.ext <;> simp
    rwa [e] at this
  have hmc : zetaZeroConfig.mult (1 / 2 + conj z) = zetaZeroConfig.mult (1 / 2 + z) := by
    have := mult_conj_zetaZeroConfig hz
    have e : conj (1 / 2 + z) = 1 / 2 + conj z := by apply Complex.ext <;> simp
    rwa [e] at this
  rw [Set.indicator_of_mem hzc, hmc, norm_mul, norm_pow]
  have hm : (1 : ℝ) ≤ zetaZeroConfig.mult (1 / 2 + z) := by
    exact_mod_cast zetaZeroConfig.one_le_mult _ hz
  have hn : ‖((zetaZeroConfig.mult (1 / 2 + z) : ℂ) + (zetaZeroConfig.mult (1 / 2 + z) : ℂ))‖ =
      2 * zetaZeroConfig.mult (1 / 2 + z) := by
    rw [← two_mul, norm_mul, Complex.norm_natCast]; norm_num
  rw [hn]
  have := sq_nonneg ‖paperFT (scaledBump w) (-(I * z))‖
  nlinarith

/-- **A loud record for any bump.** If an exponent `z₀` right of the line is `1/V`-near the top,
the Legendre record `z*` at lag `V` exists and keeps `|D(z*)| ≥ |D(z₀)|/e`. -/
theorem exists_loud_record {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 < V) {z₀ : ℂ}
    (hD₀ : evenCoeff zetaZeroConfig b z₀ ≠ 0) (hre₀ : 0 < z₀.re)
    (htop : ∀ z, evenCoeff zetaZeroConfig b z ≠ 0 → z.re ≤ z₀.re + 1 / V) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig b z₁ ≠ 0 ∧ 0 < z₁.re ∧
      ‖evenCoeff zetaZeroConfig b z₀‖ / Real.exp 1 ≤ ‖evenCoeff zetaZeroConfig b z₁‖ ∧
      ∀ z, evenCoeff zetaZeroConfig b z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig b z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp (z₁.re * V) := by
  obtain ⟨z₁, hz₁, hre₁, hrec⟩ := exists_right_record zetaZeroConfig temperedConfig_zetaZeroConfig
    hb hbs hV.le hD₀ hre₀
  refine ⟨z₁, hz₁, hre₁, ?_, hrec⟩
  set D := evenCoeff zetaZeroConfig b with hDdef
  have h1 := hrec z₀ hD₀ hre₀
  have h2 := htop z₁ hz₁
  have h3 : Real.exp (z₁.re * V) ≤ Real.exp (z₀.re * V) * Real.exp 1 := by
    rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
    have : (z₁.re - z₀.re) * V ≤ 1 := by
      have := mul_le_mul_of_nonneg_right (show z₁.re - z₀.re ≤ 1 / V by linarith) hV.le
      rwa [div_mul_cancel₀ _ hV.ne'] at this
    linarith
  have hE := Real.exp_pos (z₀.re * V)
  have h5 : ‖D z₀‖ ≤ ‖D z₁‖ * Real.exp 1 := by
    have : ‖D z₀‖ * Real.exp (z₀.re * V) ≤ (‖D z₁‖ * Real.exp 1) * Real.exp (z₀.re * V) := by
      have := h1.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg (D z₁)))
      linarith
    exact le_of_mul_le_mul_right this hE
  rw [div_le_iff₀ (Real.exp_pos 1)]
  exact h5

/-! ### The record of the one-parameter family -/

/-- The height bound `Γ₀(η) = (2880 · 80(e^{w/2}B_w)² e/(2η²))^{1/3}` for the loud records of the
one-parameter family, when the near-top zero has `|h_w(γ₀ − iδ₀)| ≥ η`. -/
def oneParamRecordHeight (w η : ℝ) : ℝ :=
  (2880 * (80 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2 / Real.exp 1))) ^
    ((1 : ℝ) / 3)

/-- **Where the record of the one-parameter family sits.** Let `½ + z₀` be a zero right of the line,
`1/V`-near the top, with `|h_w(−iz₀)| ≥ η > 0`. Then the Legendre record `z*` of the unmodulated
family has `|D(z*)| ≥ 2η²/e`, `|Im z*| ≤ Γ₀(η)`, and `Re z* ≥ Re z₀/2` once
`V Re z₀ ≥ 2 log(80 log(180 Γ₀(η))(e^{w/2}B_w)²/(2η²))`. -/
theorem one_param_record_facts {w V : ℝ} (hw : 0 < w) (hV : 0 < V) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re) {η : ℝ} (hη : 0 < η)
    (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    (htop : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 → z.re ≤ z₀.re + 1 / V)
    (hV2 : 2 * Real.log (80 * Real.log (180 * oneParamRecordHeight w η) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2)) ≤ z₀.re * V) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w 0) z₁ ≠ 0 ∧ z₀.re / 2 ≤ z₁.re ∧
      |z₁.im| ≤ oneParamRecordHeight w η ∧
      2 * η ^ 2 / Real.exp 1 ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ ∧
      ∀ z, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ * Real.exp (z₁.re * V) := by
  set D := evenCoeff zetaZeroConfig (modScaledBump w 0) with hDdef
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  set Γ := oneParamRecordHeight w η with hΓdef
  have hK0 : 0 ≤ K₀ := by positivity
  have hD₀ : 2 * η ^ 2 ≤ ‖D z₀‖ := by
    refine le_trans ?_ (two_mul_sq_le_norm_evenCoeff_zero hw hz₀)
    have := pow_le_pow_left₀ hη.le hηle 2
    linarith
  have hD₀ne : D z₀ ≠ 0 := fun h => by
    rw [h, norm_zero] at hD₀; nlinarith [pow_pos hη 2]
  obtain ⟨z₁, hz₁, hre₁, hD₁', hrec⟩ := exists_loud_record (contDiff_modScaledBump_two w 0)
    (modScaledBump_support hw 0) hV hD₀ne hre₀ htop
  have hD₁ : 2 * η ^ 2 / Real.exp 1 ≤ ‖D z₁‖ :=
    le_trans (div_le_div_of_nonneg_right hD₀ (Real.exp_pos 1).le) hD₁'
  have hε : 0 < 2 * η ^ 2 / Real.exp 1 := by positivity
  have hup : |z₁.im| ≤ Γ := by
    have h := abs_im_le_of_norm_evenCoeff_modScaledBump_ge hw (c := 0) le_rfl hε hz₁ hD₁
    rw [mul_zero] at h
    refine h.trans (max_le ?_ le_rfl)
    rw [hΓdef, oneParamRecordHeight]; positivity
  refine ⟨z₁, hz₁, ?_, hup, hD₁, hrec⟩
  have h4 : 4 ≤ |z₁.im| := four_le_abs_im_of_evenCoeff_zeta hz₁
  have hDmax : ‖D z₁‖ ≤ 80 * Real.log (180 * Γ) * K₀ := by
    refine (norm_evenCoeff_modScaledBump_le_log hw 0 hz₁).trans ?_
    have : Real.log (180 * |z₁.im|) ≤ Real.log (180 * Γ) :=
      Real.log_le_log (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num)) hK0
  have h1 := hrec z₀ hD₀ne hre₀
  have hD1pos : 0 < ‖D z₁‖ := norm_pos_iff.mpr hz₁
  have hq : 0 < 80 * Real.log (180 * Γ) * K₀ / (2 * η ^ 2) := by
    have : 0 < 80 * Real.log (180 * Γ) * K₀ := lt_of_lt_of_le hD1pos hDmax
    positivity
  have h2 : Real.exp ((z₀.re - z₁.re) * V) ≤ 80 * Real.log (180 * Γ) * K₀ / (2 * η ^ 2) := by
    have hE0 := Real.exp_pos (z₀.re * V)
    have hE1 := Real.exp_pos (z₁.re * V)
    have e : Real.exp ((z₀.re - z₁.re) * V) = Real.exp (z₀.re * V) / Real.exp (z₁.re * V) := by
      rw [← Real.exp_sub]; ring_nf
    rw [e, div_le_iff₀ hE1]
    have : 2 * η ^ 2 * Real.exp (z₀.re * V) ≤ 80 * Real.log (180 * Γ) * K₀ * Real.exp (z₁.re * V) :=
      calc 2 * η ^ 2 * Real.exp (z₀.re * V) ≤ ‖D z₀‖ * Real.exp (z₀.re * V) :=
            mul_le_mul_of_nonneg_right hD₀ hE0.le
        _ ≤ ‖D z₁‖ * Real.exp (z₁.re * V) := h1
        _ ≤ _ := mul_le_mul_of_nonneg_right hDmax hE1.le
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have h3 := Real.log_le_log (Real.exp_pos _) h2
  rw [Real.log_exp] at h3
  nlinarith

/-- `Ξ/(|D|(e^κ − 1)) ≤ 4m₀/((e − 1)ε₀) + 6144 L` for `κ ≥ 1`, `|D| ≥ ε₀ > 0`, `W ≥ 0` and
`|M| + W ≤ m₀`. -/
theorem xi_ratio_le_general {M W D κ L ε₀ m₀ : ℝ} (hκ : 1 ≤ κ) (hε₀ : 0 < ε₀) (hD : ε₀ ≤ D)
    (hL : 0 ≤ L) (hW : 0 ≤ W) (hMW : |M| + W ≤ m₀) :
    4 * |M| + 4 * W + 3840 * L * D * Real.exp κ ≤
      (4 * m₀ / ((Real.exp 1 - 1) * ε₀) + 6144 * L) * (D * (Real.exp κ - 1)) := by
  have he1 : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  have hE1 : Real.exp 1 - 1 ≤ Real.exp κ - 1 := by linarith [Real.exp_le_exp.mpr hκ]
  have hD0 : 0 < D := lt_of_lt_of_le hε₀ hD
  have hm0 : 0 ≤ m₀ := le_trans (add_nonneg (abs_nonneg M) hW) hMW
  have hratio : Real.exp κ ≤ 8 / 5 * (Real.exp κ - 1) := by
    have : (8 : ℝ) / 3 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    linarith
  have hm1 : 4 * |M| + 4 * W ≤ 4 * m₀ / ((Real.exp 1 - 1) * ε₀) * (D * (Real.exp κ - 1)) := by
    have h1 : ε₀ * (Real.exp 1 - 1) ≤ D * (Real.exp κ - 1) := mul_le_mul hD hE1 he1.le hD0.le
    have e : 4 * m₀ / ((Real.exp 1 - 1) * ε₀) * (ε₀ * (Real.exp 1 - 1)) = 4 * m₀ := by
      field_simp
    have h2 : 0 ≤ 4 * m₀ / ((Real.exp 1 - 1) * ε₀) := by positivity
    have := mul_le_mul_of_nonneg_left h1 h2
    linarith
  have hm2 : 3840 * L * D * Real.exp κ ≤ 6144 * L * (D * (Real.exp κ - 1)) := by
    have := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 3840 * L * D by positivity)
    linarith
  rw [add_mul]
  linarith

/-! ### Collapse for the one-parameter family -/

/-- The bound `B₀(p) = (8/3)^p (4/3)^k 2κ₀ (4κ₀² + 4π²(k+p)²)^{k+p}
  (4m₀/((e − 1)(2η²/e)) + 6144 log(180(Γ₀(η) + 6)))`, `m₀ = 32(e^{w/2}B_w)²(C + log 4)`. -/
def oneParamCollapseBound (w η κ₀ : ℝ) (k p : ℕ) : ℝ :=
  (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀) * (4 * κ₀ ^ 2 + 4 * π ^ 2 * (k + p : ℕ) ^ 2) ^ (k + p) *
    (4 * (32 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
        (xiLineTwoLogDerivConstant + Real.log 4)) /
      ((Real.exp 1 - 1) * (2 * η ^ 2 / Real.exp 1)) +
      6144 * Real.log (180 * (oneParamRecordHeight w η + 6)))

/-- **The one-parameter family hides only in collapsed clusters.** Let `½ + z₀` be a zero right of
the line, `1/V`-near the top, with `η = |h_w(γ₀ − iδ₀)| > 0`, and let the difference tests
`κ_w(t + v/2) − κ_w(t − v/2)` be Weil nonnegative for `v ∈ [0, V]`. With `Γ₀ = Γ₀(η)`,
`P ≥ 80 log(180Γ₀)`, `k ≥ 1`, `κ₀ ≥ 1`, `r = δ₀/8`, `2κ₀/V ≤ δ₀/16`, `V ≥ π(k + P)`,
`Vr ≥ 4π(k + P)` and `V δ₀ ≥ 2 log(80 log(180Γ₀)(e^{w/2}B_w)²/(2η²))`, the Legendre record `z*` has a
cluster `C` of `p ≤ P` zeros (all zeros within `r − 2κ₀/V` of `z*`, none beyond `r + 2κ₀/V`) with
`Π_{z ∈ C}|z − z*| (κ₀/(2(P + 1)))^p V^{2k+p+1} r^{2k+1} ≤ B₀(p)` (`oneParamCollapseBound`). -/
theorem one_param_cluster_collapse {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    {V : ℝ} (hV : 0 < V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    (hneg : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re) {P : ℕ}
    (hP : 80 * Real.log (180 * oneParamRecordHeight w η) ≤ P)
    {κ₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hκ₀ : 1 ≤ κ₀)
    (hV2 : 2 * Real.log (80 * Real.log (180 * oneParamRecordHeight w η) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2)) ≤ z₀.re * V)
    (hκV : 2 * κ₀ / V ≤ z₀.re / 16) (hVk : π * (k + P : ℕ) ≤ V)
    (hVr : 4 * π * (k + P : ℕ) ≤ V * (z₀.re / 8)) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w 0) z₁ ≠ 0 ∧ z₀.re / 2 ≤ z₁.re ∧
      |z₁.im| ≤ oneParamRecordHeight w η ∧
      (∀ z, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ * Real.exp (z₁.re * V)) ∧
      ∃ C : Finset ℂ, z₁ ∉ C ∧ C.card ≤ P ∧
        (∀ z ∈ C, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 ∧
          ‖z - z₁‖ ≤ z₀.re / 8 + 2 * κ₀ / V) ∧
        (∀ z, z ≠ z₁ → evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 →
          ‖z - z₁‖ ≤ z₀.re / 8 - 2 * κ₀ / V → z ∈ C) ∧
        (∏ z ∈ C, ‖z - z₁‖) * (κ₀ / (2 * (P + 1))) ^ C.card * V ^ (2 * k + C.card + 1) *
            (z₀.re / 8) ^ (2 * k + 1) ≤ oneParamCollapseBound w η κ₀ k C.card := by
  classical
  set b := modScaledBump w 0 with hbdef
  set D := evenCoeff zetaZeroConfig b with hDdef
  set Γ := oneParamRecordHeight w η with hΓdef
  set r : ℝ := z₀.re / 8 with hr
  have hstrip := zetaZeroConfig.strip _ hz₀
  have hre₀1' : z₀.re ≤ 1 / 2 := by
    have e : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
    linarith [hstrip.2]
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr]; linarith [hre₀1']
  have hmem : ∀ x : ℂ, D x ≠ 0 → (1 / 2 + x) ∈ zetaZeroConfig.carrier := fun x hx => by
    rcases mem_of_evenCoeff_ne_zero hx with h | h
    · exact h
    · have := conj_mem_zetaZeroConfig h
      have e : conj (1 / 2 + conj x) = 1 / 2 + x := by apply Complex.ext <;> simp
      rwa [e] at this
  have htop' : ∀ z, D z ≠ 0 → z.re ≤ z₀.re + 1 / V := fun z hz => by
    have := htop _ (hmem z hz)
    have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
    linarith
  obtain ⟨z₁, hz₁, hre₁, hup, hD₁, hrec⟩ :=
    one_param_record_facts hw hV hz₀ hre₀ hη hηle htop' hV2
  refine ⟨z₁, hz₁, hre₁, hup, hrec, ?_⟩
  have hκ₀0 : 0 < κ₀ := by linarith
  have h2κ : 2 * κ₀ / V ≤ r / 2 := by rw [hr]; linarith
  -- the companions of the record, independent of the depth
  set R₀ : ℝ := r + 2 * κ₀ / V with hR₀
  set T : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b z₁ R₀).toFinset.erase z₁ with hT
  have hTbox : ∀ z ∈ T, (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧ |(1 / 2 + z).im| ≤ Γ + 1 ∧
      1 / 2 + z₀.re / 4 ≤ (1 / 2 + z).re := fun z hz => by
    rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset] at hz
    obtain ⟨-, hDz, hzr⟩ := hz
    refine ⟨hmem z hDz, ?_, ?_⟩
    · have e : (1 / 2 + z).im = z.im := by simp
      rw [e]
      have := Complex.abs_im_le_norm (z - z₁)
      rw [Complex.sub_im] at this
      have := abs_sub_abs_le_abs_sub z.im z₁.im
      have : R₀ ≤ 1 := by rw [hR₀]; linarith
      linarith
    · have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
      rw [e]
      have := Complex.abs_re_le_norm (z - z₁)
      rw [Complex.sub_re] at this
      have := neg_abs_le (z.re - z₁.re)
      have : R₀ ≤ z₀.re / 4 := by rw [hR₀, hr]; linarith
      linarith
  have hTcard : T.card ≤ P := by
    have h4 : 4 ≤ |z₁.im| := four_le_abs_im_of_evenCoeff_zeta hz₁
    have hloc := card_exponent_window_le (b := b) h4 T fun z hz => by
      rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset] at hz
      obtain ⟨-, hDz, hzr⟩ := hz
      refine ⟨hDz, ?_⟩
      have := Complex.abs_im_le_norm (z - z₁)
      rw [Complex.sub_im] at this
      have : R₀ ≤ 1 := by rw [hR₀]; linarith
      linarith
    have hlog : Real.log (180 * |z₁.im|) ≤ Real.log (180 * Γ) :=
      Real.log_le_log (by linarith) (by linarith)
    have : (T.card : ℝ) ≤ P := by linarith
    exact_mod_cast this
  -- a depth avoiding the mirror points of all companions
  obtain ⟨κ, hκ1, hκ2, hmirror⟩ := exists_depth_avoiding_mirrors T z₁ hTcard hκ₀0 hV
  set ε : ℝ := κ₀ / (2 * (P + 1) * V) with hε
  have hκ0 : 0 < κ := by linarith
  have hκV' : κ / V ≤ 2 * κ₀ / V := div_le_div_of_nonneg_right hκ2 hV.le
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  have hz₁s : ‖z₁ - s‖ = κ / V := by
    have : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hκ0 hV)]
  set S : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b s r).toFinset with hS
  have hz₁S : z₁ ∈ S := by
    rw [hS, Set.Finite.mem_toFinset]; exact ⟨hz₁, by rw [hz₁s]; linarith⟩
  have hSr : ∀ z ∈ S, ‖z - s‖ ≤ r := fun z hz => by
    rw [hS, Set.Finite.mem_toFinset] at hz; exact hz.2
  have hiso : ∀ z, z ∉ S → D z ≠ 0 → r ≤ ‖z - s‖ := fun z hz hDz => by
    rw [hS, Set.Finite.mem_toFinset] at hz
    by_contra h; push Not at h; exact hz ⟨hDz, h.le⟩
  have hST : S.erase z₁ ⊆ T := fun z hz => by
    rw [Finset.mem_erase] at hz
    have hzS := hz.2
    rw [hS, Set.Finite.mem_toFinset] at hzS
    rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset]
    refine ⟨hz.1, hzS.1, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z s z₁
    rw [norm_sub_rev s z₁, hz₁s] at h1
    have := hSr z hz.2
    rw [hR₀]; linarith
  set p := (S.erase z₁).card with hp
  have hpP : p ≤ P := (Finset.card_le_card hST).trans hTcard
  have hpP' : ((k + p : ℕ) : ℝ) ≤ (k + P : ℕ) := by exact_mod_cast (by omega : k + p ≤ k + P)
  have hrσ : r ≤ z₁.re - κ / V := by rw [hr] at h2κ ⊢; linarith
  have hεz : ∀ z ∈ S.erase z₁, ε ≤ ‖(z - s) + ((κ / V : ℝ) : ℂ)‖ := fun z hz => by
    have e : (z - s) + ((κ / V : ℝ) : ℂ) = (z - z₁) + ((2 * κ / V : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [hs]; ring
      · simp [hs]
    rw [e]; exact hmirror z (hST hz)
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hcol := zeta_full_cluster_collapse (contDiff_modScaledBump_two w _)
    (modScaledBump_support hw _) hneg hz₁ hrec hκ0 hr0 hr1 hrσ hk S hz₁S hSr hiso
    (le_trans (mul_le_mul_of_nonneg_left hpP' Real.pi_pos.le) hVk)
    (le_trans (mul_le_mul_of_nonneg_left hpP' (by positivity)) hVr) hε0 hεz
  rw [← hp] at hcol
  -- the cluster and its bound
  refine ⟨S.erase z₁, Finset.notMem_erase z₁ S, hpP, fun z hz => ?_, fun z hz1 hDz hzr => ?_, ?_⟩
  · have hzS := (Finset.mem_erase.mp hz).2
    rw [hS, Set.Finite.mem_toFinset] at hzS
    refine ⟨hzS.1, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z s z₁
    rw [norm_sub_rev s z₁, hz₁s] at h1
    linarith [hzS.2]
  · refine Finset.mem_erase.mpr ⟨hz1, ?_⟩
    rw [hS, Set.Finite.mem_toFinset]
    refine ⟨hDz, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z z₁ s
    rw [hz₁s] at h1
    linarith
  rw [← hp]
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (180 * (|z₁.im| + 6)) := ⟨_, rfl⟩
  obtain ⟨LΓ, hLΓ⟩ : ∃ LΓ : ℝ, LΓ = Real.log (180 * (Γ + 6)) := ⟨_, rfl⟩
  have hθ0 : 0 < κ / V := div_pos hκ0 hV
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) := ⟨_, rfl⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q₂ : ℝ, Q₂ = (4 * κ₀ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) :=
    ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (2 * (k + p)).factorial * (π / V) ^ (2 * (k + p)) := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hu]; exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (div_pos Real.pi_pos hV) _)
  have hbase : ∀ t : ℝ, 0 < t → 0 < t ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 := fun t ht =>
    add_pos_of_pos_of_nonneg (pow_pos ht 2)
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg π)) (sq_nonneg _))
  have hQ0 : 0 < Q := by rw [hQ]; exact pow_pos (hbase κ hκ0) _
  have hK : u * (Real.exp κ - 1) * V ^ (2 * (k + p) + 1) / (κ * Q) ≤
      ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ := by
    refine le_trans (le_of_eq ?_) (norm_fejerPowWin_ofReal_ge hV (k + p) hθ0)
    have hVne : V ≠ 0 := hV.ne'
    have hκne : κ ≠ 0 := hκ0.ne'
    have e : (κ / V) ^ 2 + (2 * π * ((k + p : ℕ) : ℝ) / V) ^ 2 =
        (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) / V ^ 2 := by
      field_simp; ring
    rw [e, div_mul_cancel₀ κ hVne, hu, hQ, div_pow, div_pow, ← pow_mul V 2 (k + p), pow_succ]
    field_simp
  rw [← hu] at hcol
  rw [← hL] at hcol
  -- the mass of the unmodulated family is bounded
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = 32 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
      (xiLineTwoLogDerivConstant + Real.log 4) := ⟨_, rfl⟩
  have hWb := tsum_norm_evenCoeff_modScaledBump_le hw 0
  have hMb := abs_two_re_lagStructure_zero_le zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w 0) (modScaledBump_support hw 0)
  rw [abs_zero, zero_add] at hWb
  have hW0 : 0 ≤ ∑' z : ℂ, ‖D z‖ := tsum_nonneg fun z => norm_nonneg _
  have hMW : |2 * (lagStructure zetaZeroConfig b 0).re| + ∑' z : ℂ, ‖D z‖ ≤ m₀ := by
    rw [hm₀]; linarith only [hWb, hMb]
  have hL0 : 0 ≤ L := by
    rw [hL]; exact Real.log_nonneg (by have := abs_nonneg z₁.im; linarith only [this])
  have hLL : L ≤ LΓ := by
    rw [hL, hLΓ]
    exact Real.log_le_log (by have := abs_nonneg z₁.im; positivity) (by linarith only [hup])
  have hκ1' : 1 ≤ κ := hκ₀.trans hκ1
  have hε₀ : 0 < 2 * η ^ 2 / Real.exp 1 := by positivity
  have hΞ := xi_ratio_le_general hκ1' hε₀ hD₁ hL0 hW0 hMW
  have hQQ : κ * Q ≤ 2 * κ₀ * Q₂ := by
    have hq : Q ≤ Q₂ := by
      rw [hQ, hQ₂]
      refine pow_le_pow_left₀ (hbase κ hκ0).le ?_ _
      have h2 : κ ^ 2 ≤ (2 * κ₀) ^ 2 := pow_le_pow_left₀ hκ0.le hκ2 2
      have e : (2 * κ₀) ^ 2 = 4 * κ₀ ^ 2 := by ring
      linarith only [h2, e]
    exact mul_le_mul hκ2 hq hQ0.le (by linarith only [hκ₀0])
  have he1 : 0 < Real.exp 1 - 1 := by linarith only [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  have hm00 : 0 ≤ m₀ := le_trans (add_nonneg (abs_nonneg _) hW0) hMW
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 4 * m₀ / ((Real.exp 1 - 1) * (2 * η ^ 2 / Real.exp 1)) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; exact div_nonneg (by linarith only [hm00]) (mul_pos he1 hε₀).le
  rw [← hX] at hΞ
  have hΞ' : 4 * |2 * (lagStructure zetaZeroConfig b 0).re| + 4 * ∑' z : ℂ, ‖D z‖ +
      3840 * L * ‖D z₁‖ * Real.exp κ ≤ (X + 6144 * L) * 1 * (‖D z₁‖ * (Real.exp κ - 1)) := by
    rw [mul_one]; exact hΞ
  have hE : 0 < Real.exp κ - 1 := by linarith only [Real.add_one_lt_exp hκ0.ne', hκ0]
  have hc0 : (0 : ℝ) ≤ (8 / 3) ^ p * (4 / 3) ^ k :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
  have hPr0 : 0 ≤ ∏ z ∈ S.erase z₁, ‖z - z₁‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hXL : 0 ≤ (X + 6144 * L) * 1 := by rw [mul_one]; linarith only [hX0, hL0]
  have hfin := cluster_log_arith (D := ‖D z₁‖) (u := u) (E := Real.exp κ - 1)
    (norm_pos_iff.mpr hz₁) hu0 hE hε0 hPr0 hr0 hV (mul_pos hκ0 hQ0) hcol hK hΞ' hc0 hQQ
    hXL (p := p) (m := 2 * (k + p) + 1) (k := k)
  have e : ε ^ p * V ^ (2 * (k + p) + 1) = (κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) := by
    have hVne : V ≠ 0 := hV.ne'
    rw [hε, show 2 * (k + p) + 1 = (2 * k + p + 1) + p by ring, pow_add, div_pow, div_pow, mul_pow]
    field_simp
  have hQ₂0 : 0 ≤ Q₂ := by
    rw [hQ₂]
    have : 0 < 4 * κ₀ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 := by
      have := hbase (2 * κ₀) (by linarith only [hκ₀0])
      have e : (2 * κ₀) ^ 2 = 4 * κ₀ ^ 2 := by ring
      linarith only [this, e]
    exact (pow_pos this _).le
  have h1 : (X + 6144 * L) * 1 ≤ X + 6144 * LΓ := by rw [mul_one]; linarith only [hLL]
  have h2 : 0 ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) :=
    mul_nonneg hc0 (mul_nonneg (by linarith only [hκ₀0]) hQ₂0)
  calc (∏ z ∈ S.erase z₁, ‖z - z₁‖) * (κ₀ / (2 * (P + 1))) ^ p * V ^ (2 * k + p + 1) * r ^ (2 * k + 1)
      = (∏ z ∈ S.erase z₁, ‖z - z₁‖) * ε ^ p * V ^ (2 * (k + p) + 1) * r ^ (2 * k + 1) := by
        rw [mul_assoc (∏ z ∈ S.erase z₁, ‖z - z₁‖), ← e]; ring
    _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * ((X + 6144 * L) * 1) := hfin
    _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * (X + 6144 * LΓ) :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = oneParamCollapseBound w η κ₀ k p := by
        rw [oneParamCollapseBound, ← hΓdef, ← hLΓ, ← hQ₂, hX, hm₀]; ring

end GaloisForLFunctions.SquareRootThreshold
