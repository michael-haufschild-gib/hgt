import GaloisForLFunctions.RHTower.MobiusHilbertLogarithmicMertensBound
import GaloisForLFunctions.RHTower.MobiusHilbertFormEquivalence

/-!
# The Möbius Hilbert form is not `o(log N)`

For `E_N = Σ_{m,n ≤ N} μ(m)μ(n)/(m+n) = ∫_0^∞ F_N²`, `F_N(x) = Σ_{n≤N} μ(n)e^{-nx}`:

* a logarithmic bound `E_N ≤ c log(N+1) + C` controls the tails `∫_y^1 F_N² ≤ 4c log(1/y) + O(1)`
  uniformly in `N`;
* integration by parts against `x^{2r}` (layer cake) turns this into `E_N(1+2r) ≤ 2c/r + O(1)`;
* by Fatou and Plancherel the Mellin transform `Γ(s)/ζ(s)` has `L²` mass `≤ 2π(2c/r + O(1))` on
  `Re s = 1/2 + r`;
* at a critical zero `ρ` (Hardy), `|Γ/ζ| ≥ c₀/r` on the window `|t - Im ρ| ≤ r` of that line.

Hence `c ≥ c₀²/(4π)`: the form is `Ω(log N)`.  With `RHTower.mobiusHilbertFormSubpower_iff_riemannHypothesis`
the RH-exact target sits between `Ω(log N)` (unconditional) and `O(N^ε)`; any `O(log N)` bound
already forces the pointwise weak Mertens bound (`MobiusHilbertLogarithmicMertensBound`).
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- The finite Möbius--Laplace pencil is continuous. -/
theorem continuous_finiteMobiusLaplacePencil (N : ℕ) :
    Continuous (finiteMobiusLaplacePencil N) := by
  unfold finiteMobiusLaplacePencil finiteRealLaplacePencil
  fun_prop

/-- Layer-cake by parts: a logarithmic tail bound on `(y, 1]` gives the weighted bound `A/s + B`. -/
theorem intervalIntegral_rpow_mul_le_of_tail_log {g : ℝ → ℝ} (hg : Continuous g)
    {A B s ε : ℝ} (hA : 0 ≤ A) (hs : 0 < s) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (htail : ∀ y ∈ Icc ε 1, ∫ x in y..1, g x ≤ A * (-Real.log y) + B) :
    ∫ x in ε..1, x ^ s * g x ≤ A / s + B := by
  set T : ℝ → ℝ := fun y => ∫ x in y..1, g x with hT
  have hTderiv : ∀ x, HasDerivAt T (-g x) x := by
    intro x
    have h := intervalIntegral.integral_hasDerivAt_left (hg.intervalIntegrable x 1)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
    simpa [T] using h
  have hpos : ∀ x ∈ uIcc ε 1, 0 < x := by
    intro x hx
    rw [uIcc_of_le hε1] at hx
    exact lt_of_lt_of_le hε0 hx.1
  have hu : ∀ x ∈ uIcc ε 1, HasDerivAt (fun x : ℝ => x ^ s) (s * x ^ (s - 1)) x :=
    fun x hx => Real.hasDerivAt_rpow_const (Or.inl (hpos x hx).ne')
  have hv : ∀ x ∈ uIcc ε 1, HasDerivAt (fun x => -T x) (g x) x := by
    intro x _
    have := (hTderiv x).neg
    rwa [neg_neg] at this
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (by
      apply ContinuousOn.intervalIntegrable
      intro x hx
      exact ((continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl (hpos x hx).ne'))).continuousWithinAt))
    (hg.intervalIntegrable _ _)
  have hT1 : T 1 = 0 := by simp [T]
  have hTcont : Continuous T := continuous_iff_continuousAt.mpr fun x => (hTderiv x).continuousAt
  have hcoef : ∀ x ∈ uIcc ε 1, 0 ≤ s * x ^ (s - 1) := fun x hx =>
    mul_nonneg hs.le (Real.rpow_nonneg (hpos x hx).le _)
  have hcoefCont : ContinuousOn (fun x : ℝ => s * x ^ (s - 1)) (uIcc ε 1) := fun x hx =>
    (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl (hpos x hx).ne'))).continuousWithinAt
  have hlogCont : ContinuousOn (fun x : ℝ => A * -Real.log x + B) (uIcc ε 1) := fun x hx =>
    ((continuousAt_const.mul (Real.continuousAt_log (hpos x hx).ne').neg).add
      continuousAt_const).continuousWithinAt
  have hmono : ∫ x in ε..1, s * x ^ (s - 1) * T x ≤
      ∫ x in ε..1, s * x ^ (s - 1) * (A * -Real.log x + B) := by
    apply intervalIntegral.integral_mono_on hε1
    · exact (hcoefCont.mul hTcont.continuousOn).intervalIntegrable
    · exact (hcoefCont.mul hlogCont).intervalIntegrable
    · intro x hx
      have hx' : x ∈ uIcc ε 1 := by rw [uIcc_of_le hε1]; exact hx
      exact mul_le_mul_of_nonneg_left (htail x hx) (hcoef x hx')
  have hPhi : ∀ x ∈ uIcc ε 1, HasDerivAt
      (fun x : ℝ => A * (x ^ s * (-Real.log x + 1 / s)) + B * x ^ s)
      (s * x ^ (s - 1) * (A * -Real.log x + B)) x := by
    intro x hx
    have hx0 := hpos x hx
    have h1 : HasDerivAt (fun x : ℝ => x ^ s) (s * x ^ (s - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx0.ne')
    have h2 : HasDerivAt (fun x : ℝ => -Real.log x + 1 / s) (-x⁻¹) x :=
      ((Real.hasDerivAt_log hx0.ne').neg).add_const _
    have h12 : HasDerivAt (fun x : ℝ => x ^ s * (-Real.log x + 1 / s))
        (s * x ^ (s - 1) * (-Real.log x + 1 / s) + x ^ s * -x⁻¹) x := h1.mul h2
    have h3 : HasDerivAt (fun x : ℝ => A * (x ^ s * (-Real.log x + 1 / s)) + B * x ^ s)
        (A * (s * x ^ (s - 1) * (-Real.log x + 1 / s) + x ^ s * -x⁻¹) +
          B * (s * x ^ (s - 1))) x := (h12.const_mul A).add (h1.const_mul B)
    refine h3.congr_deriv ?_
    have hxs : x ^ s * x⁻¹ = x ^ (s - 1) := by
      rw [Real.rpow_sub hx0, Real.rpow_one, div_eq_mul_inv]
    have hxs' : x ^ s * -x⁻¹ = -x ^ (s - 1) := by rw [mul_neg, hxs]
    rw [hxs']
    field_simp
    ring
  have hcalc : ∫ x in ε..1, s * x ^ (s - 1) * (A * -Real.log x + B) =
      (A * (1 / s) + B) - (A * (ε ^ s * (-Real.log ε + 1 / s)) + B * ε ^ s) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hPhi
      ((hcoefCont.mul hlogCont).intervalIntegrable)]
    simp
  have hmain : ∫ x in ε..1, x ^ s * g x =
      ε ^ s * T ε + ∫ x in ε..1, s * x ^ (s - 1) * T x := by
    rw [hibp, hT1]
    simp only [Real.one_rpow, mul_zero, zero_sub, neg_zero]
    rw [show (fun x => s * x ^ (s - 1) * -T x) = fun x => -(s * x ^ (s - 1) * T x) by
      funext x; ring, intervalIntegral.integral_neg]
    ring
  have hTε := htail ε ⟨le_rfl, hε1⟩
  have hεs : 0 ≤ ε ^ s := Real.rpow_nonneg hε0.le _
  rw [hmain]
  have : ε ^ s * T ε ≤ ε ^ s * (A * -Real.log ε + B) := mul_le_mul_of_nonneg_left hTε hεs
  have hAs : 0 ≤ A * ε ^ s / s := by positivity
  calc ε ^ s * T ε + ∫ x in ε..1, s * x ^ (s - 1) * T x
      ≤ ε ^ s * (A * -Real.log ε + B) +
          ((A * (1 / s) + B) - (A * (ε ^ s * (-Real.log ε + 1 / s)) + B * ε ^ s)) := by
        rw [← hcalc]; linarith
    _ = A / s + B - A * ε ^ s / s := by field_simp; ring
    _ ≤ A / s + B := by linarith

/-- The energy of the pencil on `[y, 1]` is at most the full Hilbert energy. -/
theorem intervalIntegral_sq_pencil_le_energy (N : ℕ) {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    ∫ x in y..1, finiteMobiusLaplacePencil N x ^ 2 ≤ finiteMobiusGammaHankelEnergy N 1 := by
  rw [intervalIntegral.integral_of_le hy1, ← integral_sq_finiteMobiusLaplacePencil]
  exact setIntegral_mono_set (integrableOn_sq_finiteMobiusLaplacePencil N)
    (ae_of_all _ fun x => sq_nonneg _)
    (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hy0.le)).eventuallyLE

/-- **Logarithmic tail.**  A logarithmic Hilbert bound `E_N ≤ c log(N+1) + C` gives, uniformly in
`N`, `∫_y^1 F_N² ≤ 4c log(1/y) + (2c log 3 + 2C + 8)`.  Compare `F_N` with `F_M`,
`M = ⌈y^{-2}⌉`: on `[y, 1]` their difference is at most `2e^{-1/y}/y ≤ 2`. -/
theorem intervalIntegral_sq_pencil_le_of_hilbert_log {c C : ℝ} (hc : 0 ≤ c)
    (hH : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ c * Real.log ((N : ℝ) + 1) + C)
    {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) (N : ℕ) :
    ∫ x in y..1, finiteMobiusLaplacePencil N x ^ 2 ≤
      4 * c * (-Real.log y) + (2 * c * Real.log 3 + 2 * C + 8) := by
  have hC : 0 ≤ C := by
    have h0 := hH 0
    rw [finiteMobiusGammaHankelEnergy_zero] at h0
    simpa using h0
  have hy2 : 0 < y ^ 2 := by positivity
  set Y : ℝ := (y ^ 2)⁻¹ with hYdef
  have hY1 : 1 ≤ Y := by
    rw [hYdef]
    exact one_le_inv₀ hy2 |>.mpr (by nlinarith)
  set M : ℕ := ⌈Y⌉₊ with hMdef
  have hYM : Y ≤ (M : ℝ) := Nat.le_ceil Y
  have hM1 : (M : ℝ) + 1 ≤ 3 * Y := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Y)
    linarith
  have hlogy : 0 ≤ -Real.log y := by
    have := Real.log_nonpos hy0.le hy1
    linarith
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlogM : Real.log ((M : ℝ) + 1) ≤ Real.log 3 + 2 * (-Real.log y) := by
    have h := Real.log_le_log (by positivity) hM1
    rw [Real.log_mul (by norm_num) (by positivity), hYdef, Real.log_inv, Real.log_pow] at h
    push_cast at h
    linarith
  rcases le_or_gt N M with hNM | hMN
  · have h1 := intervalIntegral_sq_pencil_le_energy N hy0 hy1
    have h2 := hH N
    have h3 : Real.log ((N : ℝ) + 1) ≤ Real.log ((M : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hNM 1)
    nlinarith
  · have hpt : ∀ x ∈ Icc y 1, finiteMobiusLaplacePencil N x ^ 2 ≤
        2 * finiteMobiusLaplacePencil M x ^ 2 + 8 := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hy0 hx.1
      have hdiff := abs_finiteMobiusLaplacePencil_sub_le hMN.le hx0
      have hden : x / 2 ≤ 1 - Real.exp (-x) := by
        have := exp_neg_le_one_sub_half hx0.le hx.2
        linarith
      have hnum : Real.exp (-x) ^ (M + 1) ≤ Real.exp (-(1 / y)) := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have hyY : y * Y = 1 / y := by
          rw [hYdef]; field_simp
        have : 1 / y ≤ x * ((M + 1 : ℕ) : ℝ) := by
          push_cast
          calc 1 / y = y * Y := hyY.symm
            _ ≤ x * ((M : ℝ) + 1) := mul_le_mul hx.1 (by linarith) (by linarith) hx0.le
        linarith
      have hexpy : Real.exp (-(1 / y)) ≤ y := by
        rw [← Real.le_log_iff_exp_le hy0]
        have := Real.log_le_sub_one_of_pos (show 0 < 1 / y by positivity)
        rw [one_div, Real.log_inv] at this
        rw [one_div]
        have hy' : y⁻¹ - 1 ≤ y⁻¹ := by linarith
        linarith
      have hbound : |finiteMobiusLaplacePencil N x - finiteMobiusLaplacePencil M x| ≤ 2 := by
        refine hdiff.trans ?_
        have hyx : y ≤ x := hx.1
        rw [div_le_iff₀ (by linarith)]
        linarith
      have hsq : (finiteMobiusLaplacePencil N x - finiteMobiusLaplacePencil M x) ^ 2 ≤ 4 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (finiteMobiusLaplacePencil N x - finiteMobiusLaplacePencil M x)]
      nlinarith [sq_nonneg (finiteMobiusLaplacePencil N x - 2 * finiteMobiusLaplacePencil M x)]
    have hcontN := continuous_finiteMobiusLaplacePencil N
    have hcontM := continuous_finiteMobiusLaplacePencil M
    have hc2 : Continuous fun x : ℝ => 2 * finiteMobiusLaplacePencil M x ^ 2 :=
      continuous_const.mul (hcontM.pow 2)
    have hmono : ∫ x in y..1, finiteMobiusLaplacePencil N x ^ 2 ≤
        ∫ x in y..1, (2 * finiteMobiusLaplacePencil M x ^ 2 + 8) :=
      intervalIntegral.integral_mono_on hy1 ((hcontN.pow 2).intervalIntegrable _ _)
        ((hc2.add continuous_const).intervalIntegrable _ _) hpt
    have heval : ∫ x in y..1, (2 * finiteMobiusLaplacePencil M x ^ 2 + 8) =
        2 * (∫ x in y..1, finiteMobiusLaplacePencil M x ^ 2) + 8 * (1 - y) := by
      have h1 : ∫ x in y..1, (2 * finiteMobiusLaplacePencil M x ^ 2 + 8) =
          (∫ x in y..1, 2 * finiteMobiusLaplacePencil M x ^ 2) + ∫ _x in y..1, (8 : ℝ) :=
        intervalIntegral.integral_add (hc2.intervalIntegrable _ _) intervalIntegrable_const
      have h2 : ∫ x in y..1, 2 * finiteMobiusLaplacePencil M x ^ 2 =
          2 * ∫ x in y..1, finiteMobiusLaplacePencil M x ^ 2 :=
        intervalIntegral.integral_const_mul _ _
      have h3 : ∫ _x in y..1, (8 : ℝ) = (1 - y) * 8 := by simp
      rw [h1, h2, h3]
      ring
    have hM := intervalIntegral_sq_pencil_le_energy M hy0 hy1
    have hHM := hH M
    have hcl := mul_le_mul_of_nonneg_left hlogM hc
    linarith

/-- A logarithmic Hilbert bound gives `E_N(1+2r) ≤ 2c/r + O(1)` uniformly in `N`, for `0 < r ≤ 1/2`.
The `1/r` comes from the layer-cake integration by parts, not from a dyadic sum. -/
theorem finiteMobiusGammaHankelEnergy_le_of_hilbert_log {c C : ℝ} (hc : 0 ≤ c)
    (hH : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ c * Real.log ((N : ℝ) + 1) + C)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 2) (N : ℕ) :
    finiteMobiusGammaHankelEnergy N (1 + 2 * r) ≤
      2 * c / r + (2 * c * Real.log 3 + 2 * C + 12) := by
  have hpos : 0 < 1 + 2 * r := by linarith
  set B : ℝ := 2 * c * Real.log 3 + 2 * C + 8 with hB
  have hInt := integrableOn_rpow_mul_sq_finiteMobiusLaplacePencil N hpos
  rw [← integral_finiteMobiusLaplacePencil_sq N hpos,
    ← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hInt.mono_set Ioc_subset_Ioi_self) (hInt.mono_set (Ioi_subset_Ioi zero_le_one))]
  have hfar := setIntegral_Ioi_one_rpow_mul_sq_pencil_le N hpos
  have hfar4 : 4 * ((1 / 2) ^ (1 + 2 * r) * Real.Gamma (1 + 2 * r)) ≤ 4 := by
    have hG := gamma_le_one_of_mem_Icc (by linarith : (1 : ℝ) ≤ 1 + 2 * r) (by linarith)
    have hG0 : 0 ≤ Real.Gamma (1 + 2 * r) := (Real.Gamma_pos_of_pos hpos).le
    have hh : (1 / 2 : ℝ) ^ (1 + 2 * r) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) hpos.le
    have hh0 : 0 ≤ (1 / 2 : ℝ) ^ (1 + 2 * r) := Real.rpow_nonneg (by norm_num) _
    nlinarith
  have hexp : (1 + 2 * r) - 1 = 2 * r := by ring
  have hcont : Continuous fun x : ℝ => finiteMobiusLaplacePencil N x ^ 2 :=
    (continuous_finiteMobiusLaplacePencil N).pow 2
  -- near part: for every δ > 0 it is at most 2c/r + B + δ
  have hnear : ∫ x in Ioc (0 : ℝ) 1, x ^ ((1 + 2 * r) - 1) * finiteMobiusLaplacePencil N x ^ 2 ≤
      2 * c / r + B := by
    rw [hexp, ← intervalIntegral.integral_of_le zero_le_one]
    apply le_of_forall_pos_le_add
    intro δ hδ
    set ε : ℝ := min 1 (δ / ((N : ℝ) ^ 2 + 1)) with hεdef
    have hε0 : 0 < ε := lt_min one_pos (by positivity)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεδ : ε * ((N : ℝ) ^ 2 + 1) ≤ δ := by
      have := min_le_right 1 (δ / ((N : ℝ) ^ 2 + 1))
      rw [← hεdef] at this
      calc ε * ((N : ℝ) ^ 2 + 1) ≤ δ / ((N : ℝ) ^ 2 + 1) * ((N : ℝ) ^ 2 + 1) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = δ := by field_simp
    have hfcont : ContinuousOn (fun x : ℝ => x ^ (2 * r) * finiteMobiusLaplacePencil N x ^ 2)
        (uIcc 0 1) := fun x _ =>
      ((Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))).mul
        hcont.continuousAt).continuousWithinAt
    have hi1 : IntervalIntegrable (fun x : ℝ => x ^ (2 * r) * finiteMobiusLaplacePencil N x ^ 2)
        volume 0 ε :=
      (hfcont.mono (uIcc_subset_uIcc (by simp) (by simp [hε0.le, hε1]))).intervalIntegrable
    have hi2 : IntervalIntegrable (fun x : ℝ => x ^ (2 * r) * finiteMobiusLaplacePencil N x ^ 2)
        volume ε 1 :=
      (hfcont.mono (uIcc_subset_uIcc (by simp [hε0.le, hε1]) (by simp))).intervalIntegrable
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    rw [← hsplit]
    have hsmall : ∫ x in (0 : ℝ)..ε, x ^ (2 * r) * finiteMobiusLaplacePencil N x ^ 2 ≤
        ε * ((N : ℝ) ^ 2 + 1) := by
      have hb : ∀ x ∈ Icc (0 : ℝ) ε, x ^ (2 * r) * finiteMobiusLaplacePencil N x ^ 2 ≤
          (N : ℝ) ^ 2 + 1 := by
        intro x hx
        have hx1 : x ≤ 1 := hx.2.trans hε1
        have hp : x ^ (2 * r) ≤ 1 := Real.rpow_le_one hx.1 hx1 (by linarith)
        have hp0 : 0 ≤ x ^ (2 * r) := Real.rpow_nonneg hx.1 _
        have hF := abs_finiteMobiusLaplacePencil_le_card N hx.1
        have hF2 : finiteMobiusLaplacePencil N x ^ 2 ≤ (N : ℝ) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hF 2
        nlinarith [sq_nonneg (finiteMobiusLaplacePencil N x)]
      have := intervalIntegral.integral_mono_on hε0.le hi1 intervalIntegrable_const hb
      rw [intervalIntegral.integral_const] at this
      simpa using this
    have hlayer := intervalIntegral_rpow_mul_le_of_tail_log hcont (A := 4 * c) (B := B)
      (by positivity) (by linarith : 0 < 2 * r) hε0 hε1
      (fun y hy => intervalIntegral_sq_pencil_le_of_hilbert_log hc hH
        (lt_of_lt_of_le hε0 hy.1) hy.2 N)
    have h4c : 4 * c / (2 * r) = 2 * c / r := by field_simp; ring
    rw [h4c] at hlayer
    linarith
  linarith

/-- Fatou: the logarithmic Möbius source on `Re s = 1/2 + r` has energy `≤ 2c/r + O(1)`. -/
theorem memLp_and_integral_le_of_hilbert_log {c C : ℝ} (hc : 0 ≤ c)
    (hH : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ c * Real.log ((N : ℝ) + 1) + C)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 2) :
    MemLp (mobiusLaplaceLogMellinLineSource (1 / 2 + r)) 2 volume ∧
      (∫ u : ℝ, ‖mobiusLaplaceLogMellinLineSource (1 / 2 + r) u‖ ^ 2) ≤
        2 * c / r + (2 * c * Real.log 3 + 2 * C + 12) := by
  apply memLp_and_integral_norm_sq_mobiusLaplaceLogMellinLineSource_le_of_energy_le
    (by linarith)
  intro N
  have h := finiteMobiusGammaHankelEnergy_le_of_hilbert_log hc hH hr hr1 N
  rwa [show 2 * (1 / 2 + r) = 1 + 2 * r by ring]

/-- **The Möbius Hilbert form is not `o(log N)`.**  There is `c > 0` such that no bound
`Σ_{m,n ≤ N} μ(m)μ(n)/(m+n) ≤ c log(N+1) + C` holds for all `N`.

Under such a bound the logarithmic source has energy `≤ 2c/r + O(1)` on `Re s = 1/2 + r`, while a
critical zero (Hardy) forces `‖Γ/ζ‖ ≥ c₀/r` on a vertical window of width `2r` there, i.e. line
energy `≥ 2c₀²/r`.  Plancherel makes these incompatible once `c < c₀²/(4π)`.  If the canonical
identity `mellin F · (s-1)ζ(s) = Γ(s)(s-1)` fails somewhere on `Re s > 1/2`, any logarithmic bound
already contradicts it. -/
theorem exists_pos_forall_not_hilbert_le_log :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ,
      ¬ ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ c * Real.log ((N : ℝ) + 1) + C := by
  obtain ⟨T₀, _, hT₀⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨τ, _, hζ⟩ := hT₀ T₀ le_rfl
  have hρre : (linePt τ).re = 1 / 2 := by simp [linePt]
  by_cases hid : ∀ z : ℂ, 1 / 2 < z.re →
      mellin mobiusDiscreteLaplaceTransform z * zetaResidueUnit z = Complex.Gamma z * (z - 1)
  · obtain ⟨c₀, hc₀, δ, hδ, hfloor⟩ :=
      exists_boundary_zero_vertical_window_floor_of_canonical_identity
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hρre hζ hid
    refine ⟨c₀ ^ 2 / (4 * Real.pi), by positivity, fun C hH => ?_⟩
    set c : ℝ := c₀ ^ 2 / (4 * Real.pi) with hcdef
    have hc : 0 ≤ c := by positivity
    have hC : 0 ≤ C := by
      have h0 := hH 0
      rw [finiteMobiusGammaHankelEnergy_zero] at h0
      simpa using h0
    set B : ℝ := 2 * c * Real.log 3 + 2 * C + 12 with hBdef
    have hB : 0 ≤ B := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
      positivity
    set r : ℝ := min (δ / 2) (min (1 / 4) (c₀ ^ 2 / (4 * Real.pi * B + 1))) with hrdef
    have hr : 0 < r := lt_min (by linarith) (lt_min (by norm_num) (by positivity))
    have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hr1 : r ≤ 1 / 2 := (min_le_right _ _).trans ((min_le_left _ _).trans (by norm_num))
    have hrc : r ≤ c₀ ^ 2 / (4 * Real.pi * B + 1) := (min_le_right _ _).trans (min_le_right _ _)
    obtain ⟨hbase, _⟩ := memLp_and_integral_le_of_hilbert_log hc hH (half_pos hr) (by linarith)
    obtain ⟨h2, hint⟩ := memLp_and_integral_le_of_hilbert_log hc hH hr hr1
    have h1 : Integrable (mobiusLaplaceLogMellinLineSource (1 / 2 + r)) := by
      have := integrable_mobiusLaplaceLogMellinLineSource_of_base hbase (half_pos hr)
      rwa [show 1 / 2 + r / 2 + r / 2 = 1 / 2 + r by ring] at this
    have hlineInt := integrable_norm_sq_mellin_line_of_logMellinLineSource h1 h2
    have hPl := integral_norm_sq_mellin_mobiusDiscreteLaplaceTransform_line_eq h1 h2
    have hlower := integral_norm_sq_ge_two_mul_sq_div_of_window_floor hr hc₀.le hlineInt
      (hfloor r hr hrδ)
    have hpi : 0 < Real.pi := Real.pi_pos
    have hchain : 2 * c₀ ^ 2 / r ≤ 2 * Real.pi * (2 * c / r + B) := by
      rw [hPl] at hlower
      nlinarith
    have hkey : 2 * c₀ ^ 2 ≤ c₀ ^ 2 + 2 * Real.pi * B * r := by
      have h := mul_le_mul_of_nonneg_right hchain hr.le
      have e1 : 2 * c₀ ^ 2 / r * r = 2 * c₀ ^ 2 := by field_simp
      have e2 : 2 * Real.pi * (2 * c / r + B) * r = c₀ ^ 2 + 2 * Real.pi * B * r := by
        rw [hcdef]; field_simp; ring
      linarith
    have hsmall : 2 * Real.pi * B * r < c₀ ^ 2 := by
      have hden : 0 < 4 * Real.pi * B + 1 := by positivity
      have hmul : r * (4 * Real.pi * B + 1) ≤ c₀ ^ 2 := by
        rwa [le_div_iff₀ hden] at hrc
      nlinarith [sq_nonneg c₀, mul_nonneg (mul_nonneg hpi.le hB) hr.le]
    nlinarith
  · refine ⟨1, one_pos, fun C hH => hid ?_⟩
    intro z hz
    set r : ℝ := min ((z.re - 1 / 2) / 2) (1 / 4) with hrdef
    have hr : 0 < r := lt_min (by linarith) (by norm_num)
    have hr1 : r ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
    have hrz : 1 / 2 + r < z.re := by
      have := min_le_left ((z.re - 1 / 2) / 2) (1 / 4)
      linarith
    obtain ⟨hmem, _⟩ := memLp_and_integral_le_of_hilbert_log zero_le_one hH hr hr1
    exact mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_base
      (by linarith) hmem z hrz

/-- Limit-superior form: for some `c > 0`, `E_N > c log(N+1) + C` for some `N`, for every `C`. -/
theorem exists_pos_forall_exists_hilbert_gt_log :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ, ∃ N : ℕ,
      c * Real.log ((N : ℝ) + 1) + C < finiteMobiusGammaHankelEnergy N 1 := by
  obtain ⟨c, hc, h⟩ := exists_pos_forall_not_hilbert_le_log
  refine ⟨c, hc, fun C => ?_⟩
  by_contra hcon
  push Not at hcon
  exact h C hcon

/-- Fatou along a subsequence: if the finite energies at exponent `2σ` are bounded by `B` for
infinitely many `N`, the full Möbius--Laplace line source is square integrable on `Re s = σ`. -/
theorem memLp_mobiusLaplaceLogMellinLineSource_of_frequently_energy_le
    {sigma B : ℝ} (hsigma : 0 < sigma)
    (hB : ∃ᶠ N in Filter.atTop, finiteMobiusGammaHankelEnergy N (2 * sigma) ≤ B) :
    MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume := by
  obtain ⟨φ, hφ, hφB⟩ := Filter.extraction_of_frequently_atTop hB
  let C₂ : ENNReal := ENNReal.ofReal (B ^ (2 : ℝ)⁻¹)
  have hbound : ∀ j : ℕ,
      eLpNorm (mobiusLaplaceFiniteSectionLogMellinLineSource (φ j) sigma) 2 volume ≤ C₂ := by
    intro j
    have hmem := mobiusLaplaceFiniteSectionLogMellinLineSource_memLp_two (φ j) hsigma
    rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, C₂]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow
    · exact integral_nonneg fun _ => sq_nonneg _
    · rw [integral_norm_sq_mobiusLaplaceFiniteSectionLogMellinLineSource (φ j) hsigma]
      exact hφB j
    · positivity
  have hmeas : ∀ j : ℕ,
      AEStronglyMeasurable (mobiusLaplaceFiniteSectionLogMellinLineSource (φ j) sigma) volume :=
    fun j =>
      (continuous_mobiusLaplaceFiniteSectionLogMellinLineSource (φ j) sigma).aestronglyMeasurable
  have htend : ∀ᵐ u : ℝ ∂volume,
      Filter.Tendsto (fun j : ℕ => mobiusLaplaceFiniteSectionLogMellinLineSource (φ j) sigma u)
        Filter.atTop (nhds (mobiusLaplaceLogMellinLineSource sigma u)) :=
    Filter.Eventually.of_forall fun u =>
      (tendsto_mobiusLaplaceFiniteSectionLogMellinLineSource_atTop sigma u).comp hφ.tendsto_atTop
  have hnorm := MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
    (p := (2 : ENNReal)) (Filter.Eventually.of_forall hbound) hmeas htend
  exact ⟨(continuous_mobiusLaplaceLogMellinLineSource sigma).aestronglyMeasurable,
    hnorm.trans_lt ENNReal.ofReal_lt_top⟩

/-- **A zero forces divergence.**  If `ζ ρ = 0` and `0 < r ≤ 2 Re ρ`, `r < 2`, then
`Σ_{m,n≤N} μ(m)μ(n)Γ(r)/(m+n)^r → ∞`.  A bound along a subsequence would make `Γ(s)/ζ(s)` square
integrable on `Re s = r/2` (Fatou), excluding zeros with `Re ρ ≥ r/2`. -/
theorem tendsto_finiteMobiusGammaHankelEnergy_atTop_of_riemannZeta_eq_zero {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) {r : ℝ} (hr0 : 0 < r) (hr2 : r < 2) (hrρ : r ≤ 2 * ρ.re) :
    Filter.Tendsto (fun N : ℕ => finiteMobiusGammaHankelEnergy N r) Filter.atTop
      Filter.atTop := by
  rw [Filter.tendsto_atTop]
  by_contra h
  rw [not_forall] at h
  obtain ⟨B, hB⟩ := h
  rw [Filter.not_eventually] at hB
  have hfreq : ∃ᶠ N in Filter.atTop, finiteMobiusGammaHankelEnergy N (2 * (r / 2)) ≤ B :=
    hB.mono fun N hN => by
      rw [show 2 * (r / 2) = r by ring]
      exact (not_le.mp hN).le
  have hmem := memLp_mobiusLaplaceLogMellinLineSource_of_frequently_energy_le
    (sigma := r / 2) (by linarith) hfreq
  refine riemannZeta_ne_zero_of_memLp_mobiusLaplaceLogMellinLineSource_closed
    (sigma := r / 2) (by linarith) (by linarith) hmem (by linarith) ?_ hζ
  rintro rfl
  exact riemannZeta_ne_zero_of_one_le_re (by simp) hζ

/-- **The Möbius Gamma--Hankel energies diverge along every sequence** for `0 < r ≤ 1`:
Hardy's critical zeros force `Σ_{m,n≤N} μ(m)μ(n)Γ(r)/(m+n)^r → ∞`. -/
theorem tendsto_finiteMobiusGammaHankelEnergy_atTop {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    Filter.Tendsto (fun N : ℕ => finiteMobiusGammaHankelEnergy N r) Filter.atTop
      Filter.atTop := by
  obtain ⟨T₀, _, hT₀⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨τ, _, hζ⟩ := hT₀ T₀ le_rfl
  exact tendsto_finiteMobiusGammaHankelEnergy_atTop_of_riemannZeta_eq_zero hζ hr0
    (by linarith) (by simp [linePt]; linarith)

end RHTower
