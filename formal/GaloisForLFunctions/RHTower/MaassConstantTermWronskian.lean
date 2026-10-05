import GaloisForLFunctions.RHTower.ModularInversionGreen
import GaloisForLFunctions.RHTower.SelbergModularCurrentGreen

/-!
# The constant terms of two `SL₂(ℤ)`-invariant quarter eigenfunctions are proportional

Let `u_i(x + iy) = 4 Σ g_{i,n} √y K₀(2πny) cos(2πnx) + √y (b_i + a_i log y)` (`maassFun`) with
coefficients of polynomial growth, both invariant under `S(z) = −1/z`.  Then

`a₂ b₁ − a₁ b₂ = 0`  (`constTerm_wronskian_eq_zero`).

**Proof.**
* The Bessel series decay like `e^{−πy}` together with their first derivatives, uniformly in `x`
  (`exists_cosSeries_decay`).
* The current `J = u₁∇u₂ − u₂∇u₁` is divergence free, because both functions satisfy
  `Δu = −u/(4y²)`.  Green's formula on the truncated modular domain
  (`SelbergModularCurrentGreen.current_green_identity`) has no side flux (translation
  invariance) and no circular flux (radial anti-invariance under `S`), so the top flux
  `∫_{−1/2}^{1/2} J_y(x + iY) dx` vanishes for every `Y ≥ 1`.
* Up to an error `O(Y² e^{−πY})` the top flux is the Wronskian of the constant terms
  `√y(b₁ + a₁ log y)` and `√y(b₂ + a₂ log y)`, which is the constant `a₂ b₁ − a₁ b₂`.
-/

open Complex Set Filter MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace RHTower.MaassConstantTermWronskian

open MaassAxisContinuation MaassBesselSeries BesselKZero ModularInversionGreen
open GaloisForLFunctions.RHTower.SelbergMaassMean GaloisForLFunctions.RHTower.SelbergMaassTraceEnergy
  GaloisForLFunctions.RHTower.SelbergMaassTraceStokes GaloisForLFunctions.RHTower.SelbergModularDomainSlices
  GaloisForLFunctions.RHTower.SelbergModularCurrentGreen

variable {g : ℕ → ℂ}

/-! ## Decay of the Bessel series at the cusp -/

theorem yPart_nonneg (α : ℝ) (j k n : ℕ) {y : ℝ} (hy : 0 < y) : 0 ≤ yPart α j k n y :=
  mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) k) (Real.rpow_nonneg hy.le α))
    (kMoment_nonneg j _)

theorem yPart_le_exp (α : ℝ) (j k : ℕ) {n : ℕ} (hn : 1 ≤ n) {y₁ y : ℝ} (hy₁ : 0 < y₁)
    (h : y₁ ≤ y) :
    yPart α j k n y ≤ y ^ α * Real.exp (-(2 * Real.pi) * (y - y₁)) *
      ((n : ℝ) ^ k * kMoment j (2 * Real.pi * n * y₁)) := by
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : 0 < y := lt_of_lt_of_le hy₁ h
  have hr₁ : 0 < 2 * Real.pi * n * y₁ := by positivity
  have hK := kMoment_le_exp_mul j hr₁
    (show 2 * Real.pi * n * y₁ ≤ 2 * Real.pi * n * y by gcongr)
  have hp : 0 ≤ 2 * Real.pi * ((n : ℝ) - 1) * (y - y₁) :=
    mul_nonneg (mul_nonneg Real.two_pi_pos.le (by linarith)) (by linarith)
  have he : Real.exp (-(2 * Real.pi * n * y - 2 * Real.pi * n * y₁)) ≤
      Real.exp (-(2 * Real.pi) * (y - y₁)) :=
    Real.exp_le_exp.mpr (by nlinarith [hp])
  have hya := Real.rpow_nonneg hy.le α
  have hnk : 0 ≤ (n : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg n) k
  have hK0 := kMoment_nonneg j (2 * Real.pi * n * y₁)
  unfold yPart
  calc (n : ℝ) ^ k * y ^ α * kMoment j (2 * Real.pi * n * y)
      ≤ (n : ℝ) ^ k * y ^ α * (Real.exp (-(2 * Real.pi * n * y - 2 * Real.pi * n * y₁)) *
          kMoment j (2 * Real.pi * n * y₁)) := by gcongr
    _ ≤ (n : ℝ) ^ k * y ^ α * (Real.exp (-(2 * Real.pi) * (y - y₁)) *
          kMoment j (2 * Real.pi * n * y₁)) := by gcongr
    _ = _ := by ring

theorem summable_coeff_kMoment (hg : PolyGrowth g) (α : ℝ) (j k : ℕ) {y₁ : ℝ} (hy₁ : 0 < y₁) :
    Summable fun n : ℕ => ‖g (n + 1)‖ *
      (((n + 1 : ℕ) : ℝ) ^ k * kMoment j (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y₁)) := by
  obtain ⟨u, hu, hbd⟩ := exists_summable_bterm_bound hg α j k false (y₂ := y₁) hy₁
  have hpos : 0 < y₁ ^ α := Real.rpow_pos_of_pos hy₁ α
  refine (hu.div_const (y₁ ^ α)).of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _)
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) k) (kMoment_nonneg j _))) (fun n => ?_)
  have h := hbd n ((y₁ : ℂ) * I) (by simp) (by simp)
  have hb : |bterm α j k false (n + 1) ((y₁ : ℂ) * I)| =
      ((n + 1 : ℕ) : ℝ) ^ k * kMoment j (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y₁) * y₁ ^ α := by
    have hre : ((y₁ : ℂ) * I).re = 0 := by simp
    have him : ((y₁ : ℂ) * I).im = y₁ := by simp
    unfold bterm
    rw [hre, him]
    simp only [xPart, trigFun, Bool.false_eq_true, ↓reduceIte, mul_zero, Real.cos_zero, mul_one]
    rw [abs_of_nonneg (yPart_nonneg α j k (n + 1) hy₁)]
    unfold yPart
    ring
  rw [hb] at h
  rw [le_div_iff₀ hpos]
  calc ‖g (n + 1)‖ * (((n + 1 : ℕ) : ℝ) ^ k * kMoment j (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y₁)) *
        y₁ ^ α
      = ‖g (n + 1)‖ * (((n + 1 : ℕ) : ℝ) ^ k *
          kMoment j (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y₁) * y₁ ^ α) := by ring
    _ ≤ u n := h

/-- **Cusp decay of a Bessel series:** `‖S_{α,j,k,b}(z)‖ ≤ C y^α e^{−2πy}` for `y ≥ y₁ > 0`. -/
theorem norm_besselSeries_le (hg : PolyGrowth g) (α : ℝ) (j k : ℕ) (b : Bool) {y₁ : ℝ}
    (hy₁ : 0 < y₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, y₁ ≤ z.im →
      ‖besselSeries g α j k b z‖ ≤ C * (z.im ^ α * Real.exp (-(2 * Real.pi) * z.im)) := by
  set c : ℕ → ℝ := fun n => ‖g (n + 1)‖ *
    (((n + 1 : ℕ) : ℝ) ^ k * kMoment j (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y₁)) with hc_def
  have hc : Summable c := summable_coeff_kMoment hg α j k hy₁
  have hc0 : ∀ n, 0 ≤ c n := fun n => mul_nonneg (norm_nonneg _)
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) k) (kMoment_nonneg j _))
  refine ⟨Real.exp (2 * Real.pi * y₁) * ∑' n, c n,
    mul_nonneg (Real.exp_pos _).le (tsum_nonneg hc0), fun z hz => ?_⟩
  have hy : 0 < z.im := lt_of_lt_of_le hy₁ hz
  set E : ℝ := z.im ^ α * Real.exp (-(2 * Real.pi) * (z.im - y₁)) with hE
  have hE0 : 0 ≤ E := mul_nonneg (Real.rpow_nonneg hy.le α) (Real.exp_pos _).le
  have hterm : ∀ n, ‖sterm g α j k b n z‖ ≤ E * c n := by
    intro n
    unfold sterm
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb : |bterm α j k b (n + 1) z| ≤ yPart α j k (n + 1) z.im := by
      unfold bterm
      rw [abs_mul, abs_of_nonneg (yPart_nonneg α j k (n + 1) hy)]
      exact mul_le_of_le_one_right (yPart_nonneg α j k (n + 1) hy) (abs_trigFun_le _ _)
    have hy' := yPart_le_exp α j k (Nat.succ_le_succ (Nat.zero_le n)) hy₁ hz
    calc ‖g (n + 1)‖ * |bterm α j k b (n + 1) z| ≤ ‖g (n + 1)‖ * yPart α j k (n + 1) z.im :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ ≤ ‖g (n + 1)‖ * (E * (((n + 1 : ℕ) : ℝ) ^ k *
            kMoment j (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y₁))) :=
          mul_le_mul_of_nonneg_left hy' (norm_nonneg _)
      _ = E * c n := by rw [hc_def]; ring
  have hsum : Summable fun n => ‖sterm g α j k b n z‖ :=
    (hc.mul_left E).of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  calc ‖besselSeries g α j k b z‖ ≤ ∑' n, ‖sterm g α j k b n z‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n, E * c n := hsum.tsum_le_tsum hterm (hc.mul_left E)
    _ = E * ∑' n, c n := tsum_mul_left
    _ = _ := by
      rw [hE, show -(2 * Real.pi) * (z.im - y₁) = -(2 * Real.pi) * z.im + 2 * Real.pi * y₁ by ring,
        Real.exp_add]
      ring

theorem sqrt_mul_exp_le {y : ℝ} (hy : 0 ≤ y) :
    y ^ (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi) * y) ≤ Real.exp (-(Real.pi * y)) := by
  have hs : y ^ (1 / 2 : ℝ) ≤ Real.exp (Real.pi * y) := by
    rw [← Real.sqrt_eq_rpow]
    have h1 : Real.sqrt y ≤ y + 1 := by
      nlinarith [Real.sq_sqrt hy, Real.sqrt_nonneg y, sq_nonneg (Real.sqrt y - 1)]
    have h2 : y + 1 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    have h3 : Real.exp y ≤ Real.exp (Real.pi * y) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
    linarith
  calc y ^ (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi) * y)
      ≤ Real.exp (Real.pi * y) * Real.exp (-(2 * Real.pi) * y) :=
        mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
    _ = Real.exp (-(Real.pi * y)) := by rw [← Real.exp_add]; ring_nf

theorem rsqrt_mul_exp_le {y : ℝ} (hy : 1 / 2 ≤ y) :
    y ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(2 * Real.pi) * y) ≤ 2 * Real.exp (-(Real.pi * y)) := by
  have hy0 : 0 < y := by linarith
  have hs : y ^ ((1 / 2 : ℝ) - 1) ≤ 2 := by
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.rpow_neg hy0.le, ← Real.sqrt_eq_rpow]
    have hq : 1 / 2 ≤ Real.sqrt y :=
      (Real.le_sqrt (by norm_num) hy0.le).mpr (by nlinarith)
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have he : Real.exp (-(2 * Real.pi) * y) ≤ Real.exp (-(Real.pi * y)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  calc y ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(2 * Real.pi) * y)
      ≤ 2 * Real.exp (-(Real.pi * y)) :=
        mul_le_mul hs he (Real.exp_pos _).le (by norm_num)

/-- **Cusp decay of `cosSeries` and its first derivatives** on `y ≥ 1/2`. -/
theorem exists_cosSeries_decay (hg : PolyGrowth g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, 1 / 2 ≤ z.im →
      ‖cosSeries g z‖ ≤ K * Real.exp (-(Real.pi * z.im)) ∧
      ‖dirD 1 (cosSeries g) z‖ ≤ K * Real.exp (-(Real.pi * z.im)) ∧
      ‖dirD I (cosSeries g) z‖ ≤ K * Real.exp (-(Real.pi * z.im)) := by
  have h12 : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨C₀, hC₀, h₀⟩ := norm_besselSeries_le hg (1 / 2) 0 0 false h12
  obtain ⟨C₁, hC₁, h₁⟩ := norm_besselSeries_le hg (1 / 2) 0 1 true h12
  obtain ⟨C₂, hC₂, h₂⟩ := norm_besselSeries_le hg ((1 / 2) - 1) 0 0 false h12
  obtain ⟨C₃, hC₃, h₃⟩ := norm_besselSeries_le hg (1 / 2) 1 1 false h12
  have h2π := Real.two_pi_pos
  refine ⟨C₀ + 2 * Real.pi * C₁ + C₂ + 2 * Real.pi * C₃, by positivity, fun z hz => ?_⟩
  have hy : 0 < z.im := by linarith
  have hex := (Real.exp_pos (-(Real.pi * z.im))).le
  have hs := sqrt_mul_exp_le hy.le
  have hr := rsqrt_mul_exp_le hz
  have b₀ : ‖cosSeries g z‖ ≤ C₀ * Real.exp (-(Real.pi * z.im)) :=
    (h₀ z hz).trans (mul_le_mul_of_nonneg_left hs hC₀)
  have b₁ : ‖besselSeries g (1 / 2) 0 1 true z‖ ≤ C₁ * Real.exp (-(Real.pi * z.im)) :=
    (h₁ z hz).trans (mul_le_mul_of_nonneg_left hs hC₁)
  have b₂ : ‖besselSeries g ((1 / 2) - 1) 0 0 false z‖ ≤
      C₂ * (2 * Real.exp (-(Real.pi * z.im))) :=
    (h₂ z hz).trans (mul_le_mul_of_nonneg_left hr hC₂)
  have b₃ : ‖besselSeries g (1 / 2) 1 1 false z‖ ≤ C₃ * Real.exp (-(Real.pi * z.im)) :=
    (h₃ z hz).trans (mul_le_mul_of_nonneg_left hs hC₃)
  have hdx : dirD 1 (cosSeries g) z =
      ((2 * Real.pi * trigSign false : ℝ) : ℂ) * besselSeries g (1 / 2) 0 1 true z := by
    rw [cosSeries, dirD_one_besselSeries hg _ _ _ _ hy]; rfl
  have hdy : dirD I (cosSeries g) z = ((1 / 2 : ℝ) : ℂ) * besselSeries g ((1 / 2) - 1) 0 0 false z -
      ((2 * Real.pi : ℝ) : ℂ) * besselSeries g (1 / 2) 1 1 false z := by
    rw [cosSeries, dirD_I_besselSeries hg _ _ _ _ hy]; rfl
  set e := Real.exp (-(Real.pi * z.im)) with he
  have hKe : (C₀ + 2 * Real.pi * C₁ + C₂ + 2 * Real.pi * C₃) * e =
      C₀ * e + 2 * Real.pi * (C₁ * e) + C₂ * e + 2 * Real.pi * (C₃ * e) := by ring
  have n₀ : 0 ≤ C₀ * e := mul_nonneg hC₀ hex
  have n₁ : 0 ≤ 2 * Real.pi * (C₁ * e) := mul_nonneg h2π.le (mul_nonneg hC₁ hex)
  have n₂ : 0 ≤ C₂ * e := mul_nonneg hC₂ hex
  have n₃ : 0 ≤ 2 * Real.pi * (C₃ * e) := mul_nonneg h2π.le (mul_nonneg hC₃ hex)
  refine ⟨?_, ?_, ?_⟩
  · rw [hKe]; linarith
  · rw [hdx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have ht : |2 * Real.pi * trigSign false| = 2 * Real.pi := by
      simp [trigSign, abs_of_pos Real.pi_pos]
    rw [ht, hKe]
    linarith [mul_le_mul_of_nonneg_left b₁ h2π.le]
  · rw [hdy]
    calc ‖((1 / 2 : ℝ) : ℂ) * besselSeries g ((1 / 2) - 1) 0 0 false z -
          ((2 * Real.pi : ℝ) : ℂ) * besselSeries g (1 / 2) 1 1 false z‖
        ≤ ‖((1 / 2 : ℝ) : ℂ) * besselSeries g ((1 / 2) - 1) 0 0 false z‖ +
          ‖((2 * Real.pi : ℝ) : ℂ) * besselSeries g (1 / 2) 1 1 false z‖ := norm_sub_le _ _
      _ = 1 / 2 * ‖besselSeries g ((1 / 2) - 1) 0 0 false z‖ +
          2 * Real.pi * ‖besselSeries g (1 / 2) 1 1 false z‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_pos h2π]
      _ ≤ _ := by
        rw [hKe]
        have q₂ : 1 / 2 * ‖besselSeries g ((1 / 2) - 1) 0 0 false z‖ ≤ C₂ * e := by
          linarith [mul_le_mul_of_nonneg_left b₂ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        linarith [mul_le_mul_of_nonneg_left b₃ h2π.le]

/-! ## The constant term -/

theorem dirD_one_constTerm (a b : ℂ) {z : ℂ} (hz : 0 < z.im) : dirD 1 (constTerm a b) z = 0 := by
  have hc : constTerm a b = fun w => b * (sqrtPart w.im : ℂ) + a * (sqrtLogPart w.im : ℂ) := rfl
  rw [hc, dirD_add (differentiableAt_of_im (hasDerivAt_sqrtPart hz) b)
    (differentiableAt_of_im (hasDerivAt_sqrtLogPart hz) a),
    dirD_one_of_im (hasDerivAt_sqrtPart hz), dirD_one_of_im (hasDerivAt_sqrtLogPart hz), add_zero]

theorem dirD_I_constTerm (a b : ℂ) {z : ℂ} (hz : 0 < z.im) :
    dirD I (constTerm a b) z = b * (((1 / 2) * z.im ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) +
      a * (((1 / 2) * z.im ^ (-(1 / 2) : ℝ) * Real.log z.im + z.im ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
  have hc : constTerm a b = fun w => b * (sqrtPart w.im : ℂ) + a * (sqrtLogPart w.im : ℂ) := rfl
  rw [hc, dirD_add (differentiableAt_of_im (hasDerivAt_sqrtPart hz) b)
    (differentiableAt_of_im (hasDerivAt_sqrtLogPart hz) a),
    dirD_I_of_im (hasDerivAt_sqrtPart hz), dirD_I_of_im (hasDerivAt_sqrtLogPart hz)]

/-- **The Wronskian of two constant terms is constant:**
`W(√y(b₁ + a₁ log y), √y(b₂ + a₂ log y)) = a₂ b₁ − a₁ b₂`. -/
theorem constTerm_wronskian (a₁ b₁ a₂ b₂ : ℂ) {z : ℂ} (hz : 0 < z.im) :
    constTerm a₁ b₁ z * dirD I (constTerm a₂ b₂) z - constTerm a₂ b₂ z * dirD I (constTerm a₁ b₁) z =
      a₂ * b₁ - a₁ * b₂ := by
  rw [dirD_I_constTerm a₂ b₂ hz, dirD_I_constTerm a₁ b₁ hz]
  have hsr : z.im ^ (1 / 2 : ℝ) * z.im ^ (-(1 / 2) : ℝ) = 1 := by
    rw [← Real.rpow_add hz]; norm_num
  have hsr' : ((z.im ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((z.im ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hsr
  unfold constTerm sqrtPart sqrtLogPart
  push_cast
  linear_combination (a₂ * b₁ - a₁ * b₂) * hsr'

theorem norm_constTerm_le (a b : ℂ) {z : ℂ} (hz : 1 ≤ z.im) :
    ‖constTerm a b z‖ ≤ (‖a‖ + ‖b‖) * z.im ^ 2 := by
  have hy : 0 < z.im := by linarith
  have hs : z.im ^ (1 / 2 : ℝ) ≤ z.im := by
    simpa using Real.rpow_le_rpow_of_exponent_le hz (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hs0 := Real.rpow_nonneg hy.le (1 / 2 : ℝ)
  have hl0 := Real.log_nonneg hz
  have hl := Real.log_le_self hy.le
  unfold constTerm sqrtPart sqrtLogPart
  calc ‖b * ((z.im ^ (1 / 2 : ℝ) : ℝ) : ℂ) + a * ((z.im ^ (1 / 2 : ℝ) * Real.log z.im : ℝ) : ℂ)‖
      ≤ ‖b‖ * z.im ^ (1 / 2 : ℝ) + ‖a‖ * (z.im ^ (1 / 2 : ℝ) * Real.log z.im) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg hs0, abs_of_nonneg (mul_nonneg hs0 hl0)]
    _ ≤ ‖b‖ * z.im ^ 2 + ‖a‖ * z.im ^ 2 := by
        have h1 : z.im ^ (1 / 2 : ℝ) ≤ z.im ^ 2 := by nlinarith
        have h2 : z.im ^ (1 / 2 : ℝ) * Real.log z.im ≤ z.im ^ 2 := by nlinarith
        gcongr
    _ = _ := by ring

theorem norm_dirD_I_constTerm_le (a b : ℂ) {z : ℂ} (hz : 1 ≤ z.im) :
    ‖dirD I (constTerm a b) z‖ ≤ 2 * (‖a‖ + ‖b‖) * z.im ^ 2 := by
  have hy : 0 < z.im := by linarith
  rw [dirD_I_constTerm a b hy]
  have hr : z.im ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hz (by norm_num)
  have hr0 := Real.rpow_nonneg hy.le (-(1 / 2) : ℝ)
  have hl0 := Real.log_nonneg hz
  have hl := Real.log_le_self hy.le
  have hA : 0 ≤ (1 / 2) * z.im ^ (-(1 / 2) : ℝ) := by positivity
  have hB : 0 ≤ (1 / 2) * z.im ^ (-(1 / 2) : ℝ) * Real.log z.im + z.im ^ (-(1 / 2) : ℝ) := by
    positivity
  calc ‖b * (((1 / 2) * z.im ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) +
        a * (((1 / 2) * z.im ^ (-(1 / 2) : ℝ) * Real.log z.im + z.im ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)‖
      ≤ ‖b‖ * ((1 / 2) * z.im ^ (-(1 / 2) : ℝ)) +
        ‖a‖ * ((1 / 2) * z.im ^ (-(1 / 2) : ℝ) * Real.log z.im + z.im ^ (-(1 / 2) : ℝ)) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg hA, abs_of_nonneg hB]
    _ ≤ ‖b‖ * (2 * z.im ^ 2) + ‖a‖ * (2 * z.im ^ 2) := by
        have h1 : (1 / 2) * z.im ^ (-(1 / 2) : ℝ) ≤ 2 * z.im ^ 2 := by nlinarith
        have h2 : (1 / 2) * z.im ^ (-(1 / 2) : ℝ) * Real.log z.im + z.im ^ (-(1 / 2) : ℝ) ≤
            2 * z.im ^ 2 := by nlinarith
        gcongr
    _ = _ := by ring

/-- `∂ᵥu = 4 ∂ᵥS + ∂ᵥc`. -/
theorem dirD_maassFun (hg : PolyGrowth g) (a b v : ℂ) {z : ℂ} (hz : 0 < z.im) :
    dirD v (maassFun g a b) z = 4 * dirD v (cosSeries g) z + dirD v (constTerm a b) z := by
  have hS : DifferentiableAt ℝ (cosSeries g) z := differentiableAt_besselSeries hg _ _ _ _ hz
  have hC : DifferentiableAt ℝ (constTerm a b) z :=
    ((contDiffOn_constTerm a b).contDiffAt (isOpen_upper.mem_nhds hz)).differentiableAt (by simp)
  rw [show maassFun g a b = fun w => 4 * cosSeries g w + constTerm a b w from rfl,
    dirD_add (hS.const_mul 4) hC, dirD_const_mul hS]

/-! ## The Wronskian current -/

/-- The `v`-component of `V₁∇V₂ − V₂∇V₁`. -/
def wcur (V₁ V₂ : ℂ → ℂ) (v : ℂ) (z : ℂ) : ℂ := V₁ z * dirD v V₂ z - V₂ z * dirD v V₁ z

theorem dirD_mul {A B : ℂ → ℂ} {z : ℂ} (hA : DifferentiableAt ℝ A z)
    (hB : DifferentiableAt ℝ B z) (v : ℂ) :
    dirD v (fun w => A w * B w) z = dirD v A z * B z + A z * dirD v B z := by
  unfold dirD
  rw [show (fun w => A w * B w) = A * B from rfl, (hA.hasFDerivAt.mul hB.hasFDerivAt).fderiv]
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

variable {V₁ V₂ : ℂ → ℂ}

theorem contDiffOn_wcur (hV₁ : ContDiffOn ℝ ∞ V₁ upper) (hV₂ : ContDiffOn ℝ ∞ V₂ upper) (v : ℂ) :
    ContDiffOn ℝ ∞ (wcur V₁ V₂ v) upper :=
  (hV₁.mul (contDiffOn_dirD hV₂ v)).sub (hV₂.mul (contDiffOn_dirD hV₁ v))

/-- **The Wronskian current is divergence free.** -/
theorem div_wcur (hV₁ : ContDiffOn ℝ ∞ V₁ upper) (hV₂ : ContDiffOn ℝ ∞ V₂ upper)
    (hq₁ : ∀ z ∈ upper, quarterDefect V₁ z = 0) (hq₂ : ∀ z ∈ upper, quarterDefect V₂ z = 0)
    {z : ℂ} (hz : z ∈ upper) :
    dirD 1 (wcur V₁ V₂ 1) z + dirD I (wcur V₁ V₂ I) z = 0 := by
  have d₁ := differentiableAt_of_contDiffOn hV₁ hz
  have d₂ := differentiableAt_of_contDiffOn hV₂ hz
  have e₁ : ∀ v, DifferentiableAt ℝ (dirD v V₁) z := fun v =>
    differentiableAt_of_contDiffOn (contDiffOn_dirD hV₁ v) hz
  have e₂ : ∀ v, DifferentiableAt ℝ (dirD v V₂) z := fun v =>
    differentiableAt_of_contDiffOn (contDiffOn_dirD hV₂ v) hz
  have hw : ∀ v, dirD v (wcur V₁ V₂ v) z =
      V₁ z * dirD v (dirD v V₂) z - V₂ z * dirD v (dirD v V₁) z := by
    intro v
    have m₁ : DifferentiableAt ℝ (fun w => V₁ w * dirD v V₂ w) z := d₁.mul (e₂ v)
    have m₂ : DifferentiableAt ℝ (fun w => V₂ w * dirD v V₁ w) z := d₂.mul (e₁ v)
    rw [show wcur V₁ V₂ v = fun w => V₁ w * dirD v V₂ w - V₂ w * dirD v V₁ w from rfl,
      dirD_sub m₁ m₂, dirD_mul d₁ (e₂ v), dirD_mul d₂ (e₁ v)]
    ring
  rw [hw, hw]
  have h₁ := hq₁ z hz
  have h₂ := hq₂ z hz
  unfold quarterDefect at h₁ h₂
  rw [Complex.real_smul] at h₁ h₂
  linear_combination V₁ z * h₂ - V₂ z * h₁

theorem fderiv_clm_comp (ℓ : ℂ →L[ℝ] ℝ) {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (v : ℂ) : fderiv ℝ (fun w => ℓ (f w)) z v = ℓ (dirD v f z) := by
  rw [show (fun w => ℓ (f w)) = ℓ ∘ f from rfl, (ℓ.hasFDerivAt.comp z hf.hasFDerivAt).fderiv]
  rfl

theorem point_im (x y : ℝ) : (point x y).im = y := by simp [point]

/-- **The top flux of the Wronskian current vanishes** for `S`- and `T`-invariant quarter
eigenfunctions. -/
theorem top_flux_eq_zero (ℓ : ℂ →L[ℝ] ℝ) (hV₁ : ContDiffOn ℝ ∞ V₁ upper)
    (hV₂ : ContDiffOn ℝ ∞ V₂ upper)
    (hq₁ : ∀ z ∈ upper, quarterDefect V₁ z = 0) (hq₂ : ∀ z ∈ upper, quarterDefect V₂ z = 0)
    (hT₁ : ∀ z : ℂ, 0 < z.im → V₁ (z + 1) = V₁ z) (hT₂ : ∀ z : ℂ, 0 < z.im → V₂ (z + 1) = V₂ z)
    (hS₁ : ∀ z : ℂ, 0 < z.im → V₁ (invS z) = V₁ z) (hS₂ : ∀ z : ℂ, 0 < z.im → V₂ (invS z) = V₂ z)
    {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ℓ (wcur V₁ V₂ I (point x Y)) = 0 := by
  set F : ℂ → ℝ := fun w => ℓ (wcur V₁ V₂ 1 w) with hFdef
  set G : ℂ → ℝ := fun w => ℓ (wcur V₁ V₂ I w) with hGdef
  have hW : ∀ v, ContDiffOn ℝ ∞ (wcur V₁ V₂ v) upper := contDiffOn_wcur hV₁ hV₂
  have hF : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im} :=
    (ℓ.contDiff.comp_contDiffOn (hW 1)).of_le (by exact_mod_cast le_top)
  have hG : ContDiffOn ℝ 1 G {z : ℂ | 0 < z.im} :=
    (ℓ.contDiff.comp_contDiffOn (hW I)).of_le (by exact_mod_cast le_top)
  have hd : ∀ v, ∀ z ∈ upper, DifferentiableAt ℝ (wcur V₁ V₂ v) z := fun v z hz =>
    differentiableAt_of_contDiffOn (hW v) hz
  have h := current_green_identity F hF G hG hY
  -- the area term vanishes
  have hL : (∫ p in domain Y, dir 1 F (point p.1 p.2) + dir I G (point p.1 p.2)) = 0 := by
    rw [setIntegral_congr_fun (isCompact_domain Y).measurableSet (g := fun _ => (0 : ℝ))
      (fun p hp => ?_)]
    · simp
    have hp0 : point p.1 p.2 ∈ upper := by
      show 0 < (point p.1 p.2).im
      rw [point_im]; linarith [hp.1.2.1]
    show dir 1 F (point p.1 p.2) + dir I G (point p.1 p.2) = 0
    unfold dir
    rw [hFdef, hGdef, fderiv_clm_comp ℓ (hd 1 _ hp0), fderiv_clm_comp ℓ (hd I _ hp0), ← map_add,
      div_wcur hV₁ hV₂ hq₁ hq₂ hp0, map_zero]
  -- the side term vanishes
  have hside : (∫ y in arcFloor..Y, F (point (1 / 2) y) - F (point (-(1 / 2)) y)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun y hy => ?_)]
    · simp
    have hy0 : 0 < y := by
      rcases hy with ⟨h1, _⟩
      exact lt_of_lt_of_le (lt_min arcFloor_pos (by linarith)) h1
    have hpt : point (1 / 2) y = point (-(1 / 2)) y + 1 := by
      simp only [point]; push_cast; ring
    have hp : 0 < (point (-(1 / 2)) y).im := by rw [point_im]; exact hy0
    have v₁ : V₁ (point (1 / 2) y) = V₁ (point (-(1 / 2)) y) := by rw [hpt]; exact hT₁ _ hp
    have v₂ : V₂ (point (1 / 2) y) = V₂ (point (-(1 / 2)) y) := by rw [hpt]; exact hT₂ _ hp
    have w₁ : dirD 1 V₁ (point (1 / 2) y) = dirD 1 V₁ (point (-(1 / 2)) y) := by
      unfold dirD; rw [fderiv_side hT₁ hy0]
    have w₂ : dirD 1 V₂ (point (1 / 2) y) = dirD 1 V₂ (point (-(1 / 2)) y) := by
      unfold dirD; rw [fderiv_side hT₂ hy0]
    show F (point (1 / 2) y) - F (point (-(1 / 2)) y) = 0
    rw [hFdef]
    simp only [wcur, v₁, v₂, w₁, w₂, sub_self]
  -- the circular term vanishes
  have harc : (∫ x in (0 : ℝ)..(1 / 2), normalPair F G x) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun x hx => ?_)]
    · simp
    have hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
      exact ⟨by linarith [hx.1], hx.2⟩
    set hgt := arcHeight x with hgt_def
    have hh : 0 < hgt := arcHeight_pos hx
    have hxh : x ^ 2 + hgt ^ 2 = 1 := by rw [hgt_def, arcHeight_sq hx]; ring
    set p := point x hgt with hp_def
    set p' := point (-x) hgt with hp'_def
    have hpU : 0 < p.im := by rw [hp_def, point_im]; exact hh
    have hSp : invS p = p' := invS_point hxh
    have hp'U : 0 < p'.im := by rw [hp'_def, point_im]; exact hh
    have hv₁ : V₁ p' = V₁ p := by rw [← hSp]; exact hS₁ p hpU
    have hv₂ : V₂ p' = V₂ p := by rw [← hSp]; exact hS₂ p hpU
    set t : ℝ := x / hgt with ht
    have hh' : (hgt : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    have hxt : (x : ℂ) = (t : ℂ) * (hgt : ℂ) := by
      rw [ht]; push_cast; field_simp
    have hQ : ∀ V : ℂ → ℂ, ContDiffOn ℝ ∞ V upper → (∀ z : ℂ, 0 < z.im → V (invS z) = V z) →
        (t : ℂ) * dirD 1 V p + dirD I V p - (t : ℂ) * dirD 1 V p' + dirD I V p' = 0 := by
      intro V hV hSV
      have hr := fderiv_radial_invS hpU (differentiableAt_of_contDiffOn hV
        (show invS p ∈ upper by rw [hSp]; exact hp'U)) hSV
      rw [hSp, hp_def, hp'_def, apply_point, apply_point] at hr
      simp only [Complex.real_smul] at hr
      rw [← hp_def, ← hp'_def] at hr
      have hm : (hgt : ℂ) * ((t : ℂ) * dirD 1 V p + dirD I V p - (t : ℂ) * dirD 1 V p' +
          dirD I V p') = 0 := by
        unfold dirD
        push_cast at hr
        linear_combination hr + (fderiv ℝ V p' 1 - fderiv ℝ V p 1) * hxt
      rcases mul_eq_zero.mp hm with h0 | h0
      · exact absurd h0 (by exact_mod_cast hh.ne')
      · exact h0
    have hQ₁ := hQ V₁ hV₁ hS₁
    have hQ₂ := hQ V₂ hV₂ hS₂
    have hX : (-t) • wcur V₁ V₂ 1 p - wcur V₁ V₂ I p + t • wcur V₁ V₂ 1 p' - wcur V₁ V₂ I p' = 0 := by
      simp only [wcur, Complex.real_smul, hv₁, hv₂]
      push_cast
      linear_combination (-(V₁ p)) * hQ₂ + V₂ p * hQ₁
    have hN : normalPair F G x =
        ℓ ((-t) • wcur V₁ V₂ 1 p - wcur V₁ V₂ I p + t • wcur V₁ V₂ 1 p' - wcur V₁ V₂ I p') := by
      simp only [normalPair, hFdef, hGdef, map_sub, map_add, map_smul, smul_eq_mul]
      rw [← hgt_def, ← hp_def, ← hp'_def, ht, neg_div]
    show normalPair F G x = 0
    rw [hN, hX, map_zero]
  rw [hL, hside, harc, zero_add, add_zero] at h
  rw [hGdef] at h
  exact h.symm

/-! ## The Wronskian of the constant terms vanishes -/

variable {g₁ g₂ : ℕ → ℂ}

theorem norm_six_le (x₁ x₂ x₃ x₄ x₅ x₆ : ℂ) :
    ‖x₁ + x₂ - x₃ - x₄ + x₅ - x₆‖ ≤ ‖x₁‖ + ‖x₂‖ + ‖x₃‖ + ‖x₄‖ + ‖x₅‖ + ‖x₆‖ := by
  have h1 := norm_add_le x₁ x₂
  have h2 := norm_sub_le (x₁ + x₂) x₃
  have h3 := norm_sub_le (x₁ + x₂ - x₃) x₄
  have h4 := norm_add_le (x₁ + x₂ - x₃ - x₄) x₅
  have h5 := norm_sub_le (x₁ + x₂ - x₃ - x₄ + x₅) x₆
  linarith

theorem norm_four_mul_le {A B : ℂ} {Q P : ℝ} (hA : ‖A‖ ≤ Q) (hB : ‖B‖ ≤ P) :
    ‖4 * A * B‖ ≤ 4 * (Q * P) := by
  rw [norm_mul, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hA hB (norm_nonneg _)
    ((norm_nonneg _).trans hA)) (by norm_num)

theorem norm_sixteen_mul_le {A B : ℂ} {Q P : ℝ} (hA : 4 * ‖A‖ ≤ Q) (hB : ‖B‖ ≤ P) :
    ‖16 * A * B‖ ≤ 4 * (Q * P) := by
  rw [norm_mul, norm_mul, show ‖(16 : ℂ)‖ = 16 by norm_num,
    show (16 : ℝ) * ‖A‖ * ‖B‖ = 4 * ((4 * ‖A‖) * ‖B‖) by ring]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hA hB (norm_nonneg _)
    ((mul_nonneg (by norm_num) (norm_nonneg _)).trans hA)) (by norm_num)

/-- **Up to `O(y² e^{−πy})` the vertical Wronskian current is the constant `a₂ b₁ − a₁ b₂`.** -/
theorem exists_norm_wcur_sub_le (hg₁ : PolyGrowth g₁) (hg₂ : PolyGrowth g₂) (a₁ b₁ a₂ b₂ : ℂ) :
    ∃ K : ℝ, ∀ z : ℂ, 1 ≤ z.im →
      ‖wcur (maassFun g₁ a₁ b₁) (maassFun g₂ a₂ b₂) I z - (a₂ * b₁ - a₁ * b₂)‖ ≤
        K * (z.im ^ 2 * Real.exp (-(Real.pi * z.im))) := by
  obtain ⟨K₁, hK₁, h₁⟩ := exists_cosSeries_decay hg₁
  obtain ⟨K₂, hK₂, h₂⟩ := exists_cosSeries_decay hg₂
  set M₁ := ‖a₁‖ + ‖b₁‖ with hM₁
  set M₂ := ‖a₂‖ + ‖b₂‖ with hM₂
  have hM₁0 : 0 ≤ M₁ := by positivity
  have hM₂0 : 0 ≤ M₂ := by positivity
  set Q₀ := 2 * M₁ + 2 * M₂ + 4 * K₁ + 4 * K₂ with hQ₀
  set P₀ := K₁ + K₂ with hP₀
  refine ⟨24 * Q₀ * P₀, fun z hz => ?_⟩
  have hy : 0 < z.im := by linarith
  set e := Real.exp (-(Real.pi * z.im)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hy2 : 1 ≤ z.im ^ 2 := by nlinarith
  obtain ⟨s₁, -, t₁⟩ := h₁ z (by linarith)
  obtain ⟨s₂, -, t₂⟩ := h₂ z (by linarith)
  have c₁ := norm_constTerm_le a₁ b₁ hz
  have c₂ := norm_constTerm_le a₂ b₂ hz
  have d₁ := norm_dirD_I_constTerm_le a₁ b₁ hz
  have d₂ := norm_dirD_I_constTerm_le a₂ b₂ hz
  set Q := Q₀ * z.im ^ 2 with hQ
  set P := P₀ * e with hP
  have hK₁e : K₁ * e ≤ K₁ * z.im ^ 2 := mul_le_mul_of_nonneg_left (he1.trans hy2) hK₁
  have hK₂e : K₂ * e ≤ K₂ * z.im ^ 2 := mul_le_mul_of_nonneg_left (he1.trans hy2) hK₂
  have hQexp : Q = 2 * M₁ * z.im ^ 2 + 2 * M₂ * z.im ^ 2 + 4 * (K₁ * z.im ^ 2) +
      4 * (K₂ * z.im ^ 2) := by rw [hQ, hQ₀]; ring
  have hPexp : P = K₁ * e + K₂ * e := by rw [hP, hP₀]; ring
  have hMy₁ : 0 ≤ M₁ * z.im ^ 2 := by positivity
  have hMy₂ : 0 ≤ M₂ * z.im ^ 2 := by positivity
  have hKy₁ : 0 ≤ K₁ * z.im ^ 2 := by positivity
  have hKy₂ : 0 ≤ K₂ * z.im ^ 2 := by positivity
  have hKe₁ : 0 ≤ K₁ * e := mul_nonneg hK₁ he0
  have hKe₂ : 0 ≤ K₂ * e := mul_nonneg hK₂ he0
  -- big and small quantities
  have bC₁ : ‖constTerm a₁ b₁ z‖ ≤ Q := by rw [hQexp]; linarith
  have bC₂ : ‖constTerm a₂ b₂ z‖ ≤ Q := by rw [hQexp]; linarith
  have bD₁ : ‖dirD I (constTerm a₁ b₁) z‖ ≤ Q := by rw [hQexp]; linarith
  have bD₂ : ‖dirD I (constTerm a₂ b₂) z‖ ≤ Q := by rw [hQexp]; linarith
  have bS₁ : 4 * ‖cosSeries g₁ z‖ ≤ Q := by rw [hQexp]; linarith
  have bS₂ : 4 * ‖cosSeries g₂ z‖ ≤ Q := by rw [hQexp]; linarith
  have pS₁ : ‖cosSeries g₁ z‖ ≤ P := by rw [hPexp]; linarith
  have pS₂ : ‖cosSeries g₂ z‖ ≤ P := by rw [hPexp]; linarith
  have pT₁ : ‖dirD I (cosSeries g₁) z‖ ≤ P := by rw [hPexp]; linarith
  have pT₂ : ‖dirD I (cosSeries g₂) z‖ ≤ P := by rw [hPexp]; linarith
  have hw : wcur (maassFun g₁ a₁ b₁) (maassFun g₂ a₂ b₂) I z - (a₂ * b₁ - a₁ * b₂) =
      4 * constTerm a₁ b₁ z * dirD I (cosSeries g₂) z +
        4 * cosSeries g₁ z * dirD I (constTerm a₂ b₂) z -
        4 * constTerm a₂ b₂ z * dirD I (cosSeries g₁) z -
        4 * cosSeries g₂ z * dirD I (constTerm a₁ b₁) z +
        16 * cosSeries g₁ z * dirD I (cosSeries g₂) z -
        16 * cosSeries g₂ z * dirD I (cosSeries g₁) z := by
    have hW := constTerm_wronskian a₁ b₁ a₂ b₂ hy
    unfold wcur
    rw [dirD_maassFun hg₁ a₁ b₁ I hy, dirD_maassFun hg₂ a₂ b₂ I hy]
    simp only [maassFun]
    linear_combination hW
  rw [hw]
  refine (norm_six_le _ _ _ _ _ _).trans ?_
  have hfin : 24 * Q₀ * P₀ * (z.im ^ 2 * e) = 24 * (Q * P) := by rw [hQ, hP]; ring
  rw [hfin]
  -- the second and fourth terms have the small factor first
  have sw₁ : ‖4 * cosSeries g₁ z * dirD I (constTerm a₂ b₂) z‖ ≤ 4 * (Q * P) := by
    rw [show (4 : ℂ) * cosSeries g₁ z * dirD I (constTerm a₂ b₂) z =
      4 * dirD I (constTerm a₂ b₂) z * cosSeries g₁ z by ring]
    exact norm_four_mul_le bD₂ pS₁
  have sw₂ : ‖4 * cosSeries g₂ z * dirD I (constTerm a₁ b₁) z‖ ≤ 4 * (Q * P) := by
    rw [show (4 : ℂ) * cosSeries g₂ z * dirD I (constTerm a₁ b₁) z =
      4 * dirD I (constTerm a₁ b₁) z * cosSeries g₂ z by ring]
    exact norm_four_mul_le bD₁ pS₂
  linarith [norm_four_mul_le bC₁ pT₂, norm_four_mul_le bC₂ pT₁, norm_sixteen_mul_le bS₁ pT₂,
    norm_sixteen_mul_le bS₂ pT₁]

/-- **The constant terms of two `S`-invariant Maass functions are proportional:**
`a₂ b₁ − a₁ b₂ = 0`. -/
theorem constTerm_wronskian_eq_zero (hg₁ : PolyGrowth g₁) (hg₂ : PolyGrowth g₂)
    (a₁ b₁ a₂ b₂ : ℂ)
    (hS₁ : ∀ z : ℂ, 0 < z.im → maassFun g₁ a₁ b₁ (invS z) = maassFun g₁ a₁ b₁ z)
    (hS₂ : ∀ z : ℂ, 0 < z.im → maassFun g₂ a₂ b₂ (invS z) = maassFun g₂ a₂ b₂ z) :
    a₂ * b₁ - a₁ * b₂ = 0 := by
  have hV₁ := contDiffOn_maassFun hg₁ a₁ b₁
  have hV₂ := contDiffOn_maassFun hg₂ a₂ b₂
  have hq₁ : ∀ z ∈ upper, quarterDefect (maassFun g₁ a₁ b₁) z = 0 :=
    fun z hz => quarterDefect_maassFun hg₁ a₁ b₁ hz
  have hq₂ : ∀ z ∈ upper, quarterDefect (maassFun g₂ a₂ b₂) z = 0 :=
    fun z hz => quarterDefect_maassFun hg₂ a₂ b₂ hz
  have hT₁ : ∀ z : ℂ, 0 < z.im → maassFun g₁ a₁ b₁ (z + 1) = maassFun g₁ a₁ b₁ z :=
    fun z _ => maassFun_add_one a₁ b₁ z
  have hT₂ : ∀ z : ℂ, 0 < z.im → maassFun g₂ a₂ b₂ (z + 1) = maassFun g₂ a₂ b₂ z :=
    fun z _ => maassFun_add_one a₂ b₂ z
  obtain ⟨K, hK⟩ := exists_norm_wcur_sub_le hg₁ hg₂ a₁ b₁ a₂ b₂
  set V₁ := maassFun g₁ a₁ b₁
  set V₂ := maassFun g₂ a₂ b₂
  set W₀ := a₂ * b₁ - a₁ * b₂
  have hcont : ∀ Y : ℝ, 0 < Y → Continuous (fun x : ℝ => wcur V₁ V₂ I (point x Y)) := by
    intro Y hY
    exact (contDiffOn_wcur hV₁ hV₂ I).continuousOn.comp_continuous
      (by unfold point; fun_prop) (fun x => by show 0 < (point x Y).im; rw [point_im]; exact hY)
  have hT : ∀ Y : ℝ, 1 ≤ Y → ∫ x in (-(1 / 2 : ℝ))..(1 / 2), wcur V₁ V₂ I (point x Y) = 0 := by
    intro Y hY
    have hi := (hcont Y (by linarith)).intervalIntegrable (μ := volume) (-(1 / 2 : ℝ)) (1 / 2)
    have hre := top_flux_eq_zero reCLM hV₁ hV₂ hq₁ hq₂ hT₁ hT₂ hS₁ hS₂ hY
    have him := top_flux_eq_zero imCLM hV₁ hV₂ hq₁ hq₂ hT₁ hT₂ hS₁ hS₂ hY
    rw [ContinuousLinearMap.intervalIntegral_comp_comm reCLM hi] at hre
    rw [ContinuousLinearMap.intervalIntegral_comp_comm imCLM hi] at him
    exact Complex.ext (by simpa using hre) (by simpa using him)
  have hb : ∀ Y : ℝ, 1 ≤ Y → ‖W₀‖ ≤ K * (Y ^ 2 * Real.exp (-(Real.pi * Y))) := by
    intro Y hY
    have hi := (hcont Y (by linarith)).intervalIntegrable (μ := volume) (-(1 / 2 : ℝ)) (1 / 2)
    have hW : W₀ = ∫ x in (-(1 / 2 : ℝ))..(1 / 2), (W₀ - wcur V₁ V₂ I (point x Y)) := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const (μ := volume)) hi, hT Y hY,
        intervalIntegral.integral_const]
      norm_num
    rw [hW]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := K * (Y ^ 2 * Real.exp (-(Real.pi * Y)))) (fun x _ => ?_)).trans
      (le_of_eq (by norm_num))
    rw [norm_sub_rev]
    have h := hK (point x Y) (by rw [point_im]; exact hY)
    rwa [point_im] at h
  have ht : Tendsto (fun Y : ℝ => K * (Y ^ 2 * Real.exp (-(Real.pi * Y)))) atTop (𝓝 0) := by
    have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
    have hc : Tendsto (fun Y : ℝ => Real.pi * Y) atTop atTop :=
      tendsto_id.const_mul_atTop Real.pi_pos
    have h1 := (h0.comp hc).const_mul (K / Real.pi ^ 2)
    rw [mul_zero] at h1
    refine h1.congr fun Y => ?_
    simp only [Function.comp_apply]
    field_simp
  have hle : ‖W₀‖ ≤ 0 := ge_of_tendsto ht (eventually_atTop.mpr ⟨1, hb⟩)
  exact norm_le_zero_iff.mp hle

end RHTower.MaassConstantTermWronskian
