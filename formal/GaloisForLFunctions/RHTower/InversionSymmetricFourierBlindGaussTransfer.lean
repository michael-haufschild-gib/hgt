import GaloisForLFunctions.RHTower.InversionSymmetricFourierBlindRigidity

/-!
# The Gauss transfer series, and Fourier-blind functions of support ratio below `1 + 1/√2`

**The Gauss transfer series.**  Let `τ(z) = 2 + 1/(z − 1)` (`gaussBranchC`) and let `F` be the
Farey series `fareySeries a b`, holomorphic on `Re z > ½`.  The equation

`S(z) + S(τz)/(z − 1) = F(z)`   (`gaussTransferSeries_add_div`)

has the explicit solution `S = Σ_k (−1)^k F(τ^k z) P_k(z)`, `P_k(z) = Π_{j<k} (τ^j z − 1)⁻¹`
(`gaussTransferSeries`).  For `Re z > 2` the iterates satisfy `Re τ^k z > 2`, and two Gauss steps
land in `Re > 9/4`; so `|P_k| ≤ (25/16)(4/5)^k`, and the series is holomorphic and bounded on
`Re z > 2` (`differentiableOn_gaussTransferSeries`, `exists_norm_gaussTransferSeries_le`).  On a
real window mapped into itself by `τ`, bounded solutions of the equation are unique
(`eq_of_gaussWindow_equation`).

**Theorem** (`eq_zero_of_inversionSymmetric_fourierBlind_of_sqrt_two`).  Let `G : ℝ → ℝ` be
continuous and even, with `G(1/x) = x G(x)` for `x > 0`, vanishing on `[0, c)`, and with Fourier
transform vanishing at every integer `|n| ≥ 2`.  If `(1 − c)² < 2c − 1`, i.e. `c > 2 − √2`, so that
the support `[c, 1/c]` has `1/c < 1 + 1/√2`, then `G = 0`.  This extends
`eq_zero_of_inversionSymmetric_fourierBlind_of_five_thirds` (`1/c < 5/3`).

**Proof** for `c² + c < 1`.  Put `H(v) = G(1 − 1/v)/v`, `F = fareySeriesR (a₀ + 2a₁) (2a₁)`,
`w₂ = 1/(1 − c)` and `v* = c/(2c − 1)`.  Then `H = 0` on `[2, w₂]`, `H = F` on `[v*, ∞)`, and
`H(v) + H(v + 1) + H(τv)/(v − 1) = F(v) + F(v + 1)` for `v ≥ 2`.
* The hypothesis `(1 − c)² < 2c − 1` says `v* < w₂ + 1`.  So on the window `[w₂, v*]`, which `τ`
  maps into itself, the equation reads `H(v) + H(τv)/(v − 1) = F(v)`, and therefore `H = S`.
* For `v` slightly below `w₂` the equation reads `H(τv) = (v − 1)F(v)`, with `τv` in the window.
  So `S(τz) = (z − 1)F(z)` on a real interval.  Both sides are holomorphic on `Re z > 1`, hence
  equal there.
* Then `S(z) = F(z) − S(τz)/(z − 1) = 0` on `Re z > 2`, and `(z − 1)F(z) = S(τz) = 0`.  Thus
  `F = 0` on `(1, ∞)` and `H = 0` on `[2, ∞)`, so `G = 0`.

No limit at the fixed point of `τ` and no positivity is used.  The transfer series carries the
identity from a real interval to the whole half-plane.

**Corollary** (`eq_zero_of_cosDilationKernel_blind_of_sqrt_two`).  A continuous `f` supported in
`[α, β]` with `2β² + α² < 4αβ` (`β/α < 1 + 1/√2`) and `Ψ_f(n) = 0` for every integer `n ≥ 2`
vanishes.  This extends `eq_zero_of_cosDilationKernel_blind_of_lt_five_thirds_mul`.
-/

open MeasureTheory Set Real Filter Topology
open scoped FourierTransform

namespace RHTower

noncomputable section

/-! ### The complex Gauss branch -/

/-- The Gauss branch `τ(z) = 2 + 1/(z − 1)` on `ℂ`. -/
def gaussBranchC (z : ℂ) : ℂ := 2 + 1 / (z - 1)

theorem gaussBranchC_ofReal (v : ℝ) : gaussBranchC v = ((gaussBranch v : ℝ) : ℂ) := by
  unfold gaussBranchC gaussBranch
  push_cast
  ring

theorem sub_one_ne_zero_of_one_lt_re {z : ℂ} (hz : 1 < z.re) : z - 1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem lt_norm_sub_one_of_lt_re {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (hz : 1 + r < z.re) :
    r < ‖z - 1‖ := by
  have h := Complex.abs_re_le_norm (z - 1)
  have e : (z - 1).re = z.re - 1 := by simp
  rw [e, abs_of_pos (by linarith)] at h
  linarith

theorem re_gaussBranchC (z : ℂ) :
    (gaussBranchC z).re = 2 + (z - 1).re / Complex.normSq (z - 1) := by
  unfold gaussBranchC
  rw [Complex.add_re, one_div, Complex.inv_re]
  norm_num

theorem two_lt_re_gaussBranchC {z : ℂ} (hz : 1 < z.re) : 2 < (gaussBranchC z).re := by
  rw [re_gaussBranchC]
  have h : 0 < (z - 1).re / Complex.normSq (z - 1) :=
    div_pos (by simp; linarith) (Complex.normSq_pos.mpr (sub_one_ne_zero_of_one_lt_re hz))
  linarith

/-- Two Gauss steps from `Re z > 2` land in `Re > 9/4`. -/
theorem nine_fourths_lt_re_gaussBranchC_gaussBranchC {y : ℂ} (hy : 2 < y.re) :
    9 / 4 < (gaussBranchC (gaussBranchC y)).re := by
  set w : ℂ := 1 / (y - 1) with hw
  have hy1 : 1 < ‖y - 1‖ := lt_norm_sub_one_of_lt_re zero_le_one (by linarith)
  have hwn : ‖w‖ < 1 := by
    rw [hw, norm_div, norm_one]
    exact (div_lt_one (by linarith)).mpr hy1
  have hwre : 0 < w.re := by
    rw [hw, one_div, Complex.inv_re]
    exact div_pos (by simp; linarith)
      (Complex.normSq_pos.mpr (sub_one_ne_zero_of_one_lt_re (by linarith)))
  have hτ : gaussBranchC y - 1 = 1 + w := by unfold gaussBranchC; rw [hw]; ring
  rw [re_gaussBranchC, hτ]
  have hre : (1 + w).re = 1 + w.re := by simp
  have hns : Complex.normSq (1 + w) < 4 := by
    rw [Complex.normSq_eq_norm_sq]
    have h := norm_add_le (1 : ℂ) w
    rw [norm_one] at h
    have h0 : 0 ≤ ‖1 + w‖ := norm_nonneg _
    nlinarith
  have hpos : 0 < Complex.normSq (1 + w) := by
    rw [Complex.normSq_pos]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [hre]
  have : 1 / 4 < (1 + w.re) / Complex.normSq (1 + w) := by
    rw [lt_div_iff₀ hpos]
    nlinarith
  linarith

theorem two_lt_re_iterate_gaussBranchC (k : ℕ) {z : ℂ} (hz : 2 < z.re) :
    2 < (gaussBranchC^[k] z).re := by
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact two_lt_re_gaussBranchC (by linarith)

/-! ### The transfer weights -/

/-- The weights `P_0 = 1`, `P_{k+1}(z) = P_k(τz)/(z − 1)`, i.e. `P_k(z) = Π_{j<k} (τ^j z − 1)⁻¹`. -/
def gaussBranchWeight : ℕ → ℂ → ℂ
  | 0, _ => 1
  | k + 1, z => gaussBranchWeight k (gaussBranchC z) / (z - 1)

theorem norm_gaussBranchWeight_gaussBranchC_gaussBranchC_le (k : ℕ) {y : ℂ} (hy : 2 < y.re) :
    ‖gaussBranchWeight k (gaussBranchC (gaussBranchC y))‖ ≤ (4 / 5) ^ k := by
  induction k generalizing y with
  | zero => simp [gaussBranchWeight]
  | succ k ih =>
    have hy' : 2 < (gaussBranchC y).re := two_lt_re_gaussBranchC (by linarith)
    have h94 := nine_fourths_lt_re_gaussBranchC_gaussBranchC hy
    set u := gaussBranchC (gaussBranchC y) with hu
    have hu1 : 5 / 4 < ‖u - 1‖ := lt_norm_sub_one_of_lt_re (by norm_num) (by linarith)
    have h := ih hy'
    simp only [gaussBranchWeight]
    rw [norm_div, div_le_iff₀ (by linarith), pow_succ]
    have hp : 0 ≤ (4 / 5 : ℝ) ^ k := by positivity
    nlinarith

theorem norm_gaussBranchWeight_le (k : ℕ) {z : ℂ} (hz : 2 < z.re) :
    ‖gaussBranchWeight k z‖ ≤ 25 / 16 * (4 / 5) ^ k := by
  have hz1 : 1 < ‖z - 1‖ := lt_norm_sub_one_of_lt_re zero_le_one (by linarith)
  match k with
  | 0 => simp [gaussBranchWeight]; norm_num
  | 1 =>
    simp only [gaussBranchWeight]
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
    nlinarith
  | k + 2 =>
    have hτz : 2 < (gaussBranchC z).re := two_lt_re_gaussBranchC (by linarith)
    have hτ1 : 1 < ‖gaussBranchC z - 1‖ := lt_norm_sub_one_of_lt_re zero_le_one (by linarith)
    have h := norm_gaussBranchWeight_gaussBranchC_gaussBranchC_le k hz
    simp only [gaussBranchWeight]
    rw [norm_div, norm_div, div_div, div_le_iff₀ (by positivity)]
    have hp : 0 ≤ (4 / 5 : ℝ) ^ k := by positivity
    have e : (25 / 16 : ℝ) * (4 / 5) ^ (k + 2) = (4 / 5) ^ k := by ring
    rw [e]
    have : 1 ≤ ‖gaussBranchC z - 1‖ * ‖z - 1‖ := by nlinarith
    nlinarith

/-! ### The transfer series -/

/-- A uniform bound for the Farey series on `Re z > ½`. -/
theorem exists_norm_fareySeries_le (a b : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ z ∈ halfPlaneHalf, ‖fareySeries a b z‖ ≤ M := by
  set A₁ := ∑' k : ℕ, 4 / 3 * (1 / ((k : ℝ) + 1) ^ 2) with hA₁
  set A₂ := ∑' k : ℕ, 32 * π ^ 2 * (Real.exp (4 * π) + 1) * (1 / ((k : ℝ) + 1) ^ 2) with hA₂
  have hA₁0 : 0 ≤ A₁ := tsum_nonneg fun k => by positivity
  have hA₂0 : 0 ≤ A₂ := tsum_nonneg fun k => by positivity
  refine ⟨|a| * A₁ + |b| * A₂, by positivity, fun z hz => ?_⟩
  have h1 : ‖altHarmonic z‖ ≤ A₁ :=
    tsum_of_norm_bounded (summable_inv_succ_sq.mul_left (4 / 3)).hasSum
      fun k => norm_altHarmonicTerm_le hz k
  have h2 : ‖altCosDefect z‖ ≤ A₂ :=
    tsum_of_norm_bounded
      (summable_inv_succ_sq.mul_left (32 * π ^ 2 * (Real.exp (4 * π) + 1))).hasSum
      fun i => norm_altCosDefectTerm_le hz i
  unfold fareySeries
  calc ‖(a : ℂ) * altHarmonic z + (b : ℂ) * altCosDefect z‖
      ≤ ‖(a : ℂ) * altHarmonic z‖ + ‖(b : ℂ) * altCosDefect z‖ := norm_add_le _ _
    _ = |a| * ‖altHarmonic z‖ + |b| * ‖altCosDefect z‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ |a| * A₁ + |b| * A₂ := by gcongr

/-- The terms `(−1)^k F(τ^k z) P_k(z)` of the Gauss transfer series. -/
def gaussTransferTerm (a b : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  (-1) ^ k * fareySeries a b (gaussBranchC^[k] z) * gaussBranchWeight k z

/-- **The Gauss transfer series** `S(z) = Σ_k (−1)^k F(τ^k z) P_k(z)`. -/
def gaussTransferSeries (a b : ℝ) (z : ℂ) : ℂ := ∑' k, gaussTransferTerm a b k z

theorem gaussTransferTerm_succ (a b : ℝ) (k : ℕ) (z : ℂ) :
    gaussTransferTerm a b (k + 1) z = -(gaussTransferTerm a b k (gaussBranchC z) / (z - 1)) := by
  unfold gaussTransferTerm
  rw [Function.iterate_succ_apply]
  simp only [gaussBranchWeight]
  ring

theorem norm_gaussTransferTerm_le {a b M : ℝ} (hM : ∀ z ∈ halfPlaneHalf, ‖fareySeries a b z‖ ≤ M)
    (hM0 : 0 ≤ M) (k : ℕ) {z : ℂ} (hz : 2 < z.re) :
    ‖gaussTransferTerm a b k z‖ ≤ M * (25 / 16) * (4 / 5) ^ k := by
  unfold gaussTransferTerm
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hF := hM _ (show 1 / 2 < (gaussBranchC^[k] z).re by
    linarith [two_lt_re_iterate_gaussBranchC k hz])
  have hP := norm_gaussBranchWeight_le k hz
  calc ‖fareySeries a b (gaussBranchC^[k] z)‖ * ‖gaussBranchWeight k z‖
      ≤ M * (25 / 16 * (4 / 5) ^ k) := mul_le_mul hF hP (norm_nonneg _) hM0
    _ = M * (25 / 16) * (4 / 5) ^ k := by ring

theorem summable_gaussTransferTerm (a b : ℝ) {z : ℂ} (hz : 2 < z.re) :
    Summable fun k => gaussTransferTerm a b k z := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_fareySeries_le a b
  exact Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (M * (25 / 16)))
    fun k => norm_gaussTransferTerm_le hM hM0 k hz

/-- **The transfer equation** `S(z) + S(τz)/(z − 1) = F(z)` on `Re z > 2`. -/
theorem gaussTransferSeries_add_div (a b : ℝ) {z : ℂ} (hz : 2 < z.re) :
    gaussTransferSeries a b z + gaussTransferSeries a b (gaussBranchC z) / (z - 1) =
      fareySeries a b z := by
  unfold gaussTransferSeries
  rw [(summable_gaussTransferTerm a b hz).tsum_eq_zero_add]
  simp only [gaussTransferTerm_succ]
  rw [tsum_neg, tsum_div_const]
  have h0 : gaussTransferTerm a b 0 z = fareySeries a b z := by
    simp [gaussTransferTerm, gaussBranchWeight]
  rw [h0]
  ring

theorem exists_norm_gaussTransferSeries_le (a b : ℝ) :
    ∃ C, ∀ z : ℂ, 2 < z.re → ‖gaussTransferSeries a b z‖ ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_fareySeries_le a b
  refine ⟨M * (25 / 16) * (1 - 4 / 5)⁻¹, fun z hz => ?_⟩
  exact tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (M * (25 / 16)))
    fun k => norm_gaussTransferTerm_le hM hM0 k hz

theorem differentiableOn_gaussBranchC :
    DifferentiableOn ℂ gaussBranchC {z : ℂ | 1 < z.re} :=
  (differentiableOn_const 2).add ((differentiableOn_const 1).div
    (differentiableOn_id.sub_const 1) fun _ hz => sub_one_ne_zero_of_one_lt_re hz)

theorem mapsTo_gaussBranchC :
    MapsTo gaussBranchC {z : ℂ | 1 < z.re} {z : ℂ | 2 < z.re} :=
  fun _ hz => two_lt_re_gaussBranchC hz

theorem differentiableOn_iterate_gaussBranchC (k : ℕ) :
    DifferentiableOn ℂ (gaussBranchC^[k]) {z : ℂ | 2 < z.re} ∧
      MapsTo (gaussBranchC^[k]) {z : ℂ | 2 < z.re} {z : ℂ | 2 < z.re} := by
  have hsub : {z : ℂ | 2 < z.re} ⊆ {z : ℂ | 1 < z.re} := fun z hz => by
    show 1 < z.re; have : 2 < z.re := hz; linarith
  induction k with
  | zero => exact ⟨differentiableOn_id, mapsTo_id _⟩
  | succ k ih =>
    rw [Function.iterate_succ]
    exact ⟨ih.1.comp (differentiableOn_gaussBranchC.mono hsub) (mapsTo_gaussBranchC.mono_left hsub),
      ih.2.comp (mapsTo_gaussBranchC.mono_left hsub)⟩

theorem differentiableOn_gaussBranchWeight (k : ℕ) :
    DifferentiableOn ℂ (gaussBranchWeight k) {z : ℂ | 2 < z.re} := by
  have hsub : {z : ℂ | 2 < z.re} ⊆ {z : ℂ | 1 < z.re} := fun z hz => by
    show 1 < z.re; have : 2 < z.re := hz; linarith
  induction k with
  | zero => exact differentiableOn_const 1
  | succ k ih =>
    show DifferentiableOn ℂ (fun z => gaussBranchWeight k (gaussBranchC z) / (z - 1)) _
    exact (ih.comp (differentiableOn_gaussBranchC.mono hsub)
      (mapsTo_gaussBranchC.mono_left hsub)).div (differentiableOn_id.sub_const 1)
      fun z hz => sub_one_ne_zero_of_one_lt_re (hsub hz)

/-- The transfer series is holomorphic on `Re z > 2`. -/
theorem differentiableOn_gaussTransferSeries (a b : ℝ) :
    DifferentiableOn ℂ (gaussTransferSeries a b) {z : ℂ | 2 < z.re} := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_fareySeries_le a b
  have hV : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsub : {z : ℂ | 2 < z.re} ⊆ halfPlaneHalf := fun z hz => by
    show 1 / 2 < z.re; have : 2 < z.re := hz; linarith
  refine Complex.differentiableOn_tsum_of_summable_norm
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (M * (25 / 16)))
    (fun k => ?_) hV fun k z hz => norm_gaussTransferTerm_le hM hM0 k hz
  obtain ⟨hd, hm⟩ := differentiableOn_iterate_gaussBranchC k
  unfold gaussTransferTerm
  exact ((differentiableOn_const _).mul ((differentiableOn_fareySeries a b).comp hd
    (hm.mono_right hsub))).mul (differentiableOn_gaussBranchWeight k)

/-! ### Uniqueness on a window -/

/-- **Bounded solutions are unique on a `τ`-invariant window** `[p, q]` with `p > 2`. -/
theorem eq_of_gaussWindow_equation {X Y : ℝ → ℂ} {p q : ℝ} (hp : 2 < p)
    (hmaps : ∀ v, p ≤ v → v ≤ q → p ≤ gaussBranch v ∧ gaussBranch v ≤ q)
    (hXY : ∀ v, p ≤ v → v ≤ q →
      X v + X (gaussBranch v) / ((v : ℂ) - 1) = Y v + Y (gaussBranch v) / ((v : ℂ) - 1))
    (hbd : ∃ B, ∀ v, p ≤ v → v ≤ q → ‖X v - Y v‖ ≤ B) :
    ∀ v, p ≤ v → v ≤ q → X v = Y v := by
  obtain ⟨B, hB⟩ := hbd
  set θ := 1 / (p - 1) with hθ
  have hp1 : 1 < p - 1 := by linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by linarith)]; exact hp1
  have hstep : ∀ v, p ≤ v → v ≤ q → ‖X v - Y v‖ ≤ θ * ‖X (gaussBranch v) - Y (gaussBranch v)‖ := by
    intro v hpv hvq
    have hv1 : 0 < v - 1 := by linarith
    have e := hXY v hpv hvq
    have hne : ((v : ℂ) - 1) ≠ 0 := by
      rw [show ((v : ℂ) - 1) = ((v - 1 : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_ne_zero.mpr hv1.ne'
    have hD : X v - Y v = -((X (gaussBranch v) - Y (gaussBranch v)) / ((v : ℂ) - 1)) := by
      field_simp at e ⊢
      linear_combination e
    rw [hD, norm_neg, norm_div, show ((v : ℂ) - 1) = ((v - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg hv1.le, hθ, div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by linarith) (by linarith))
      (norm_nonneg _)
  have hiter : ∀ n : ℕ, ∀ v, p ≤ v → v ≤ q → ‖X v - Y v‖ ≤ B * θ ^ n := by
    intro n
    induction n with
    | zero => intro v hpv hvq; simpa using hB v hpv hvq
    | succ n ih =>
      intro v hpv hvq
      obtain ⟨h1, h2⟩ := hmaps v hpv hvq
      calc ‖X v - Y v‖ ≤ θ * ‖X (gaussBranch v) - Y (gaussBranch v)‖ := hstep v hpv hvq
        _ ≤ θ * (B * θ ^ n) := mul_le_mul_of_nonneg_left (ih _ h1 h2) hθ0
        _ = B * θ ^ (n + 1) := by ring
  intro v hpv hvq
  have hlim : Tendsto (fun n : ℕ => B * θ ^ n) atTop (𝓝 (B * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul B
  have h := ge_of_tendsto' hlim fun n => hiter n v hpv hvq
  rw [mul_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-! ### The theorem -/

/-- **Inversion-symmetric Fourier-blind functions of support ratio below `1 + 1/√2` vanish.** -/
theorem eq_zero_of_inversionSymmetric_fourierBlind_of_sqrt_two {G : ℝ → ℝ}
    (hG : Continuous G) (heven : ∀ x, G (-x) = G x) (hinv : ∀ x, 0 < x → G x⁻¹ = x * G x)
    {c : ℝ} (hc : (1 - c) ^ 2 < 2 * c - 1) (hsupp : ∀ x, 0 ≤ x → x < c → G x = 0)
    (hblind : ∀ n : ℤ, 2 ≤ |n| → 𝓕 (fun x => (G x : ℂ)) n = 0) (y : ℝ) : G y = 0 := by
  rcases lt_or_ge (c ^ 2 + c) 1 with hg | hg
  swap
  · exact eq_zero_of_inversionSymmetric_fourierBlind_of_five_thirds hG heven hinv
      (by nlinarith) hsupp hblind y
  have hhalf : 1 / 2 < c := by nlinarith
  have hc0 : 0 < c := by linarith
  have hc23 : c < 2 / 3 := by nlinarith
  have hsupp' := inversionSymmetric_eq_zero_of_le hG hc0 hsupp
  set a₀ := (𝓕 (fun x => (G x : ℂ)) 0).re with ha₀
  set a₁ := (𝓕 (fun x => (G x : ℂ)) 1).re with ha₁
  set a := a₀ + 2 * a₁ with ha
  set b := 2 * a₁ with hb
  set F := fareySeriesR a b with hF
  set H : ℝ → ℝ := fun v => G (1 - 1 / v) / v with hH
  have h2c : 0 < 2 * c - 1 := by linarith
  have h1c : 0 < 1 - c := by linarith
  set vs := c / (2 * c - 1) with hvs
  have hvs2 : 2 < vs := by rw [hvs, lt_div_iff₀ h2c]; linarith
  set w₂ := 1 / (1 - c) with hw₂
  have hw₂2 : 2 < w₂ := by rw [hw₂, lt_div_iff₀ h1c]; linarith
  have hvsw : vs < w₂ + 1 := by
    rw [hvs, hw₂, div_lt_iff₀ h2c]
    have e : (1 / (1 - c) + 1) * (2 * c - 1) = (2 * c - 1) / (1 - c) + (2 * c - 1) := by ring
    rw [e]
    have : 1 - c < (2 * c - 1) / (1 - c) := by rw [lt_div_iff₀ h1c]; nlinarith
    linarith
  have hw₂vs : w₂ ≤ vs := by
    rw [hw₂, hvs, div_le_div_iff₀ h1c h2c]
    nlinarith
  -- the profile, the support and the Gauss–Farey equation
  have hHF : ∀ v, vs ≤ v → H v = F v := fun v hv =>
    inversionSymmetric_profile_eq_fareySeriesR hG heven hinv hhalf hsupp hblind
      (max_le (by linarith) hv)
  have hHzero : ∀ v, 2 ≤ v → v ≤ w₂ → H v = 0 := by
    intro v hv2 hvw
    have hv0 : 0 < v := by linarith
    have hinvv : 1 / v ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hv2
    have hle : 1 - 1 / v ≤ c := by
      rw [hw₂, le_div_iff₀ h1c] at hvw
      rw [show 1 - 1 / v = (v - 1) / v by field_simp, div_le_iff₀ hv0]
      linarith
    simp only [hH]
    rw [hsupp' _ (by linarith) hle, zero_div]
  have hgf : ∀ v, 2 ≤ v →
      H v + H (v + 1) + H (gaussBranch v) / (v - 1) = F v + F (v + 1) := by
    intro v hv2
    have e : H v + H (v + 1) + H (gaussBranch v) / (v - 1) =
        (a₀ + 2 * a₁ * Real.cos (2 * π / v)) / v :=
      inversionSymmetric_gauss_farey_equation hG heven hinv hhalf hsupp hblind hv2
    rw [e, fareySeriesR_add_one a b (by linarith)]
    rw [ha, hb]; ring
  -- the window `[w₂, vs]` is mapped into itself by `τ`
  have hτleft : ∀ v, 1 < v → v ≤ vs → w₂ ≤ gaussBranch v := by
    intro v hv1 hvs'
    have hB : v * (2 * c - 1) ≤ c := by rw [hvs, le_div_iff₀ h2c] at hvs'; exact hvs'
    unfold gaussBranch
    set t := 1 / (v - 1) with ht
    have htv : t * (v - 1) = 1 := by rw [ht]; field_simp [show v - 1 ≠ 0 by linarith]
    have ht0 : 0 < t := by rw [ht]; exact one_div_pos.mpr (by linarith)
    rw [hw₂, div_le_iff₀ h1c]
    have hB' : (v - 1) * (2 * c - 1) ≤ 1 - c := by linarith
    have h1 := mul_le_mul_of_nonneg_left hB' ht0.le
    have e : t * ((v - 1) * (2 * c - 1)) = 2 * c - 1 := by rw [← mul_assoc, htv, one_mul]
    linarith
  have hτright : ∀ v, w₂ ≤ v → gaussBranch v ≤ vs := by
    intro v hvw
    have hv1 : 0 < v - 1 := by linarith
    have hA : 1 ≤ v * (1 - c) := by rw [hw₂, div_le_iff₀ h1c] at hvw; exact hvw
    unfold gaussBranch
    set t := 1 / (v - 1) with ht
    have htv : t * (v - 1) = 1 := by rw [ht]; field_simp
    have ht0 : 0 < t := by rw [ht]; exact one_div_pos.mpr hv1
    rw [hvs, le_div_iff₀ h2c]
    have hA' : c ≤ (v - 1) * (1 - c) := by linarith
    have h1 := mul_le_mul_of_nonneg_left hA' ht0.le
    have e : t * ((v - 1) * (1 - c)) = 1 - c := by rw [← mul_assoc, htv, one_mul]
    have htc : t * c ≤ 1 - c := by linarith
    have key : c * ((2 + t) * (2 * c - 1)) ≤ c * c := by
      nlinarith [mul_le_mul_of_nonneg_right htc h2c.le]
    exact le_of_mul_le_mul_left key hc0
  -- the window equation
  have hwin : ∀ v, w₂ ≤ v → v ≤ vs → H v + H (gaussBranch v) / (v - 1) = F v := by
    intro v hvw _
    have e := hgf v (by linarith)
    rw [hHF (v + 1) (by linarith)] at e
    linarith
  -- `H` is the transfer series on the window
  set S := gaussTransferSeries a b with hS
  obtain ⟨CS, hCS⟩ := exists_norm_gaussTransferSeries_le a b
  obtain ⟨CG, hCG⟩ : ∃ C, ∀ r, |G r| ≤ C := by
    obtain ⟨C, hC⟩ := (hasCompactSupport_of_inversionSymmetric hG heven hinv hc0
      hsupp).exists_bound_of_continuous hG
    exact ⟨C, fun r => by rw [← Real.norm_eq_abs]; exact hC r⟩
  have hSeq : ∀ v, w₂ ≤ v → v ≤ vs → ((H v : ℝ) : ℂ) = S v := by
    refine eq_of_gaussWindow_equation hw₂2
      (fun v h1 h2 => ⟨hτleft v (by linarith) h2, hτright v h1⟩) (fun v h1 h2 => ?_) ?_
    · have hv2 : 2 < (v : ℂ).re := by rw [Complex.ofReal_re]; linarith
      have eS := gaussTransferSeries_add_div a b hv2
      rw [gaussBranchC_ofReal] at eS
      rw [eS, fareySeries_ofReal, ← hF, ← hwin v h1 h2]
      push_cast
      ring
    · refine ⟨CG + CS, fun v h1 _ => ?_⟩
      have hv0 : 0 < v := by linarith
      have hHb : |H v| ≤ CG := by
        simp only [hH]
        rw [abs_div, abs_of_pos hv0, div_le_iff₀ hv0]
        have := hCG (1 - 1 / v)
        nlinarith [abs_nonneg (G (1 - 1 / v))]
      calc ‖((H v : ℝ) : ℂ) - S v‖ ≤ ‖((H v : ℝ) : ℂ)‖ + ‖S v‖ := norm_sub_le _ _
        _ ≤ CG + CS := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add hHb (hCS _ (by rw [Complex.ofReal_re]; linarith))
  -- the identity `S(τz) = (z − 1)F(z)` on a real interval below `w₂`
  set p := max (max 2 (vs - 1)) (1 + 1 / (vs - 2)) with hp
  have hvs2' : 0 < vs - 2 := by linarith
  have hpw : p < w₂ := by
    rw [hp, max_lt_iff, max_lt_iff]
    refine ⟨⟨hw₂2, by linarith⟩, ?_⟩
    have h1 : 1 / (vs - 2) < w₂ - 1 := by
      rw [div_lt_iff₀ hvs2']
      rw [hvs, hw₂]
      have e1 : c / (2 * c - 1) - 2 = (2 - 3 * c) / (2 * c - 1) := by
        rw [eq_div_iff h2c.ne', sub_mul, div_mul_cancel₀ _ h2c.ne']; ring
      have e2 : 1 / (1 - c) - 1 = c / (1 - c) := by
        rw [eq_div_iff h1c.ne', sub_mul, div_mul_cancel₀ _ h1c.ne']; ring
      rw [e1, e2, div_mul_div_comm, lt_div_iff₀ (mul_pos h1c h2c)]
      nlinarith
    linarith
  have hp2 : 2 ≤ p := le_trans (le_max_left _ _) (le_max_left _ _)
  have hint : ∀ x, p < x → x < w₂ → ((H (gaussBranch x) : ℝ) : ℂ) = ((x : ℂ) - 1) * F x := by
    intro x hpx hxw
    have hx2 : 2 ≤ x := by linarith
    have hx1 : vs - 1 ≤ x := by
      have := le_trans (le_max_right _ _) (le_max_left _ _) |>.trans hpx.le
      exact this
    have e := hgf x hx2
    rw [hHzero x hx2 hxw.le, hHF (x + 1) (by linarith)] at e
    have hx1' : 0 < x - 1 := by linarith
    have : H (gaussBranch x) = (x - 1) * F x := by
      field_simp at e
      linarith
    rw [this]
    push_cast
    ring
  set U₁ : Set ℂ := {z | 1 < z.re} with hU₁
  have hU₁o : IsOpen U₁ := isOpen_lt continuous_const Complex.continuous_re
  have hU₁sub : U₁ ⊆ halfPlaneHalf := fun z hz => by
    show 1 / 2 < z.re; have : 1 < z.re := hz; linarith
  set Φ : ℂ → ℂ := fun z => S (gaussBranchC z) - (z - 1) * fareySeries a b z with hΦ
  have hΦd : DifferentiableOn ℂ Φ U₁ :=
    ((differentiableOn_gaussTransferSeries a b).comp differentiableOn_gaussBranchC
      mapsTo_gaussBranchC).sub ((differentiableOn_id.sub_const 1).mul
        ((differentiableOn_fareySeries a b).mono hU₁sub))
  have hΦzero := eqOn_zero_of_real_interval (hΦd.analyticOnNhd hU₁o)
    (convex_halfSpace_re_gt 1).isPreconnected hpw
    (by show 1 < (((p + w₂) / 2 : ℝ) : ℂ).re; rw [Complex.ofReal_re]; linarith)
    fun x hx1 hx2 => by
      have hτx1 : w₂ ≤ gaussBranch x := hτleft x (by linarith) (by linarith)
      have hτx2 : gaussBranch x ≤ vs := by
        unfold gaussBranch
        have hx1 : 1 / (vs - 2) ≤ x - 1 := by
          have := le_max_right (max 2 (vs - 1)) (1 + 1 / (vs - 2))
          linarith
        have : 1 / (x - 1) ≤ vs - 2 := (one_div_le (by linarith) hvs2').mpr hx1
        linarith
      simp only [hΦ]
      rw [gaussBranchC_ofReal, ← hSeq _ hτx1 hτx2, hint x hx1 hx2, fareySeries_ofReal, ← hF]
      ring
  have hΦall : ∀ z : ℂ, 1 < z.re → S (gaussBranchC z) = (z - 1) * fareySeries a b z := by
    intro z hz
    have := hΦzero (show z ∈ U₁ from hz)
    simp only [hΦ, Pi.zero_apply] at this
    exact sub_eq_zero.mp this
  -- consequences: `S = 0` on `Re z > 2` and `F = 0` on `(1, ∞)`
  have hS0 : ∀ z : ℂ, 2 < z.re → S z = 0 := by
    intro z hz
    have e := gaussTransferSeries_add_div a b hz
    rw [← hS, hΦall z (by linarith)] at e
    have hne := sub_one_ne_zero_of_one_lt_re (z := z) (by linarith)
    rw [mul_div_cancel_left₀ _ hne] at e
    linear_combination e
  have hF0 : ∀ v, 1 < v → F v = 0 := by
    intro v hv
    have hv' : 1 < (v : ℂ).re := by rw [Complex.ofReal_re]; exact hv
    have e := hΦall v hv'
    rw [hS0 _ (two_lt_re_gaussBranchC hv'), fareySeries_ofReal, ← hF] at e
    have hne : ((v : ℂ) - 1) ≠ 0 := sub_one_ne_zero_of_one_lt_re hv'
    have := (mul_eq_zero.mp e.symm).resolve_left hne
    exact_mod_cast this
  -- `H = 0` on `[2, ∞)`
  have hHall : ∀ v, 2 ≤ v → H v = 0 := by
    intro v hv
    rcases le_or_gt v w₂ with h | h
    · exact hHzero v hv h
    rcases le_or_gt v vs with h' | h'
    · have := hSeq v h.le h'
      rw [hS0 _ (by rw [Complex.ofReal_re]; linarith)] at this
      exact_mod_cast this
    · rw [hHF v h'.le, hF0 v (by linarith)]
  refine eq_zero_of_inversionSymmetric_of_profile_zero hG heven hinv
    (fun x hx hx2 => hsupp x hx (by linarith)) (fun v hv => ?_) y
  have h := hHall v hv
  simp only [hH] at h
  exact (div_eq_zero_iff.mp h).resolve_right (by linarith)

/-- **Blind cores of support ratio below `1 + 1/√2` vanish.**  Let `f` be continuous and
supported in `[α, β]` with `0 < α ≤ β` and `2β² + α² < 4αβ`, i.e. `β/α < 1 + 1/√2`.  If the
cosine–dilation kernel satisfies `Ψ_f(n) = 0` for every integer `n ≥ 2`, then `f = 0`.

The even extension `r ↦ A_f(|r|)` is inversion-symmetric with Fourier transform `Ψ_f`
(`fourier_evenDilationAutocorr`), so it vanishes by
`eq_zero_of_inversionSymmetric_fourierBlind_of_sqrt_two`.  Then `Ψ_f(0) = 0`, and the short-core
rigidity theorem finishes. -/
theorem eq_zero_of_cosDilationKernel_blind_of_sqrt_two {f : ℝ → ℝ} (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : 2 * β ^ 2 + α ^ 2 < 4 * α * β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) (y : ℝ) : f y = 0 := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hβ2 : β ≤ 2 * α := by nlinarith
  set G : ℝ → ℝ := fun x => dilationAutocorr f |x| with hGdef
  set c := α / β with hc
  have hcβ : c * β = α := by rw [hc]; field_simp
  have hcrit : (1 - c) ^ 2 < 2 * c - 1 := by
    have key : ((1 - c) ^ 2 - (2 * c - 1)) * β ^ 2 < 0 := by
      have e : ((1 - c) ^ 2 - (2 * c - 1)) * β ^ 2 = (β - α) ^ 2 - (2 * α - β) * β := by
        rw [← hcβ]; ring
      rw [e]; nlinarith
    linarith [neg_of_mul_neg_left key (pow_pos hβ0 2).le]
  have hρ : (evenDilationAutocorr hf hα hsupp : ℝ → ℂ) = fun x => ((G x : ℝ) : ℂ) := rfl
  have hG0 : ∀ x, G x = 0 := by
    refine eq_zero_of_inversionSymmetric_fourierBlind_of_sqrt_two
      ((continuous_dilationAutocorr hf hα hsupp).comp continuous_abs)
      (fun x => by simp only [hGdef, abs_neg]) (fun x hx => ?_) hcrit (fun x hx hxc => ?_)
      (fun n hn => ?_)
    · simp only [hGdef]
      rw [abs_of_pos (inv_pos.mpr hx), abs_of_pos hx]
      exact dilationAutocorr_inv f hx
    · simp only [hGdef]
      refine dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp fun hm => ?_
      rw [abs_of_nonneg hx] at hm
      linarith [hm.1]
    · rw [← hρ, fourier_evenDilationAutocorr hf hα hαβ hsupp,
        cosDilationKernel_int_eq_zero hf hα hαβ hsupp hblind n hn, Complex.ofReal_zero]
  have hΨ0 : cosDilationKernel f 0 = 0 := by
    have h := fourier_evenDilationAutocorr hf hα hαβ hsupp 0
    have hz : (evenDilationAutocorr hf hα hsupp : ℝ → ℂ) = 0 := by
      rw [hρ]; funext x; simp [hG0 x]
    rw [hz, fourier_real_eq_integral_exp_smul] at h
    simp only [Pi.zero_apply, smul_zero, integral_zero] at h
    exact_mod_cast h.symm
  exact eq_zero_of_cosDilationKernel_blind_of_le_two_mul hf hα hαβ hβ2 hsupp hΨ0 hblind y

end

end RHTower
