import GaloisForLFunctions.RHTower.MaassThetaRelation
import GaloisForLFunctions.RHTower.MaassConverseAutomorphy

/-!
# The level-one Maass converse theorem at eigenvalue `1/4`

Let `G(s) = Σ g_n n^{−s}` converge absolutely for `Re s > 1` and suppose `Λ̂(s) = s²(s−1)²Γ_ℝ(s)²G(s)`
extends to an entire function with `Λ̂(1 − s) = Λ̂(s)`, bounded on `−1/2 ≤ Re s ≤ 3/2`.  With
`a = Λ̂(1)`, `b = Λ̂'(1) − 2Λ̂(1)`, the function

`u(x + iy) = 4 Σ g_n √y K₀(2πny) cos(2πnx) + √y (b + a log y)`

is a smooth eigenfunction of the hyperbolic Laplacian with eigenvalue `1/4`, even, `1`-periodic,
and invariant under `z ↦ −1/z` (`maassFun_invS`), i.e. invariant under `SL₂(ℤ)`.

With the opposite sign `Λ̂(1 − s) = −Λ̂(s)`, the function with constant term `−√y (b + a log y)`
satisfies `u(−1/z) = −u(z)` (`maassFun_invS_sign`).

The axis relation `u(i/y) = u(iy)` is the theta relation of `Θ(y) = Σ g_n K₀(2πny)`
(`MaassThetaRelation.kTheta_relation`), and unique continuation from the axis
(`maassFun_inv_eq_of_axis`) propagates it to the whole upper half-plane.
-/

open Complex Set Filter
open scoped ContDiff

noncomputable section

namespace RHTower.MaassConverseLevelOne

open MaassThetaMellin MaassThetaRelation MaassBesselSeries BesselKZero MaassAxisContinuation

variable {g : ℕ → ℂ}

/-- Absolute convergence beyond `1` gives polynomial growth. -/
theorem polyGrowth_of_summable
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ)) : PolyGrowth g := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_le_sq hsum
  refine ⟨max M ‖g 0‖, le_max_of_le_right (norm_nonneg _), 2, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h := hM m
    have h1 : ((m : ℝ) + 1) ^ 2 ≤ (((m + 1 : ℕ) : ℝ) + 1) ^ 2 := by
      push_cast; nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    calc ‖g (m + 1)‖ ≤ M * ((m : ℝ) + 1) ^ 2 := h
      _ ≤ max M ‖g 0‖ * (((m + 1 : ℕ) : ℝ) + 1) ^ 2 :=
          mul_le_mul (le_max_left _ _) h1 (by positivity) (le_max_of_le_left hM0)

/-- On the imaginary axis the cosine series is `√y Θ(y)`. -/
theorem cosSeries_axis (y : ℝ) :
    cosSeries g ((y : ℂ) * I) = ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) * kTheta g y := by
  unfold cosSeries besselSeries kTheta
  rw [← tsum_mul_left]
  congr 1
  funext n
  simp only [sterm, bterm, yPart, xPart, trigFun, Bool.false_eq_true, ↓reduceIte]
  simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, mul_re,
    sub_zero, pow_zero, one_mul, Real.cos_zero]
  push_cast
  ring

/-- On the imaginary axis the constant term is `√y (b + a log y)`. -/
theorem constTerm_axis (a b : ℂ) {y : ℝ} :
    constTerm a b ((y : ℂ) * I) = ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (b + a * (Real.log y : ℂ)) := by
  simp only [constTerm, sqrtPart, sqrtLogPart, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
    mul_zero, add_zero]
  push_cast
  ring

/-- **The axis relation `u(i/y) = u(iy)`.** -/
theorem maassFun_axis (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ))
    {Λh : ℂ → ℂ} (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = Λh s)
    (heq : ∀ s : ℂ, 1 < s.re → Λh s = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries g s)
    (hbd : ∃ B : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖Λh s‖ ≤ B) {y : ℝ} (hy : 0 < y) :
    maassFun g (coeffA Λh) (coeffB Λh) (((1 / y : ℝ) : ℂ) * I) =
      maassFun g (coeffA Λh) (coeffB Λh) ((y : ℂ) * I) := by
  have hrel := kTheta_relation hsum hΛ hsym heq hbd hy
  have hy' : 0 < 1 / y := by positivity
  unfold maassFun
  rw [cosSeries_axis y, cosSeries_axis (1 / y), constTerm_axis, constTerm_axis]
  set r : ℝ := y ^ (1 / 2 : ℝ) with hr_def
  have hsq : ((1 / y) ^ (1 / 2 : ℝ) : ℝ) = r⁻¹ := by
    rw [hr_def, Real.div_rpow zero_le_one hy.le, Real.one_rpow, one_div]
  have hlog : Real.log (1 / y) = -Real.log y := by rw [one_div, Real.log_inv]
  have hr : r ^ 2 = y := by
    rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul hy.le]; norm_num
  have hr0 : (0 : ℝ) < r := Real.rpow_pos_of_pos hy _
  have hinv : (y : ℂ) ^ (-1 : ℂ) = (y : ℂ)⁻¹ := Complex.cpow_neg_one _
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have hrc : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  have hrc2 : (r : ℂ) ^ 2 = (y : ℂ) := by exact_mod_cast hr
  have hΘ : kTheta g (1 / y) = (y : ℂ) * (kTheta g y - (1 / 4) * ((coeffB Λh - coeffA Λh *
      Real.log y) / y - coeffB Λh - coeffA Λh * Real.log y)) := by
    rw [← hrel, hinv, one_div]
    field_simp
    ring
  rw [hsq, hlog, hΘ]
  push_cast
  rw [← hrc2]
  field_simp
  ring

/-- **`SL₂(ℤ)`-invariance: `u(−1/z) = u(z)`.** -/
theorem maassFun_invS (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ))
    {Λh : ℂ → ℂ} (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = Λh s)
    (heq : ∀ s : ℂ, 1 < s.re → Λh s = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries g s)
    (hbd : ∃ B : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖Λh s‖ ≤ B) {z : ℂ}
    (hz : 0 < z.im) :
    maassFun g (coeffA Λh) (coeffB Λh) (invS z) = maassFun g (coeffA Λh) (coeffB Λh) z :=
  maassFun_inv_eq_of_axis (polyGrowth_of_summable hsum) _ _
    (fun _ hy => maassFun_axis hsum hΛ hsym heq hbd hy) hz

/-! ## The functional equation with a sign -/

/-- **The axis relation with sign `ε`:** for `u = u_{εa, εb}`, `u(i/y) = ε u(iy)`. -/
theorem maassFun_axis_sign
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ))
    {Λh : ℂ → ℂ} {ε : ℂ} (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = ε * Λh s)
    (hε : ε * ε = 1)
    (heq : ∀ s : ℂ, 1 < s.re → Λh s = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries g s)
    (hbd : ∃ B : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖Λh s‖ ≤ B) {y : ℝ} (hy : 0 < y) :
    maassFun g (ε * coeffA Λh) (ε * coeffB Λh) (((1 / y : ℝ) : ℂ) * I) =
      ε * maassFun g (ε * coeffA Λh) (ε * coeffB Λh) ((y : ℂ) * I) := by
  have hrel := kTheta_relation_sign hsum hΛ hsym hε heq hbd hy
  unfold maassFun
  rw [cosSeries_axis y, cosSeries_axis (1 / y), constTerm_axis, constTerm_axis]
  set r : ℝ := y ^ (1 / 2 : ℝ) with hr_def
  have hsq : ((1 / y) ^ (1 / 2 : ℝ) : ℝ) = r⁻¹ := by
    rw [hr_def, Real.div_rpow zero_le_one hy.le, Real.one_rpow, one_div]
  have hlog : Real.log (1 / y) = -Real.log y := by rw [one_div, Real.log_inv]
  have hr : r ^ 2 = y := by
    rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul hy.le]; norm_num
  have hr0 : (0 : ℝ) < r := Real.rpow_pos_of_pos hy _
  have hinv : (y : ℂ) ^ (-1 : ℂ) = (y : ℂ)⁻¹ := Complex.cpow_neg_one _
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have hrc : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  have hrc2 : (r : ℂ) ^ 2 = (y : ℂ) := by exact_mod_cast hr
  have hΘ : kTheta g (1 / y) = ε * (y : ℂ) * (kTheta g y - (1 / 4) * ((coeffB Λh - coeffA Λh *
      Real.log y) / y - ε * (coeffB Λh + coeffA Λh * Real.log y))) := by
    rw [hinv] at hrel
    rw [show (1 / y : ℝ) = y⁻¹ from one_div y]
    have hyy : (y : ℂ) * (y : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hyc
    linear_combination (-(ε * (y : ℂ))) * hrel - kTheta g y⁻¹ * (y : ℂ) * (y : ℂ)⁻¹ * hε -
      kTheta g y⁻¹ * hyy
  rw [hsq, hlog, hΘ]
  push_cast
  rw [← hrc2]
  field_simp
  ring

/-- **Axis symmetry with a sign implies the automorphy `u(−1/z) = ε u(z)`.** -/
theorem maassFun_inv_eq_smul_of_axis (hg : PolyGrowth g) (a b ε : ℂ)
    (haxis : ∀ y : ℝ, 0 < y →
      maassFun g a b ((1 / y : ℝ) * I) = ε * maassFun g a b ((y : ℂ) * I))
    {z : ℂ} (hz : 0 < z.im) : maassFun g a b (invS z) = ε * maassFun g a b z := by
  set V : ℂ → ℂ := fun w => ε * maassFun g a b w - maassFun g a b (invS w) with hV
  have hu := contDiffOn_maassFun hg a b
  have hεu : ContDiffOn ℝ ∞ (fun w => ε * maassFun g a b w) upper :=
    (hu.const_smul ε).congr fun w _ => by simp [smul_eq_mul]
  have hVs : ContDiffOn ℝ ∞ V upper := hεu.sub (contDiffOn_comp_invS hu)
  have hVpde : ∀ w ∈ upper, quarterDefect V w = 0 := by
    intro w hw
    have hG : ContDiffOn ℝ ∞ (fun w => (-1 : ℂ) * maassFun g a b (invS w)) upper :=
      ((contDiffOn_comp_invS hu).const_smul (-1 : ℂ)).congr fun w _ => by simp [smul_eq_mul]
    have h1 := quarterDefect_maassFun hg a b (show 0 < w.im from hw)
    have h2 := quarterDefect_comp_invS hu (fun v hv => quarterDefect_maassFun hg a b hv) hw
    have hsum := quarterDefect_add (F := fun w => ε * maassFun g a b w)
      (G := fun w => (-1 : ℂ) * maassFun g a b (invS w)) hεu hG hw
    have hneg := quarterDefect_const_mul (contDiffOn_comp_invS hu) (-1 : ℂ) hw
    have hpos := quarterDefect_const_mul hu ε hw
    have hVeq : V = fun w => (fun w => ε * maassFun g a b w) w +
        (-1 : ℂ) * maassFun g a b (invS w) := by
      funext w; simp only [hV]; ring
    rw [hVeq, hsum, hneg, hpos, h1, h2]
    ring
  have hVeven : ∀ w ∈ upper, V (-(starRingEnd ℂ) w) = V w := by
    intro w _
    simp only [hV, maassFun_neg_conj, invS_neg_conj]
  have hVax : ∀ y : ℝ, 0 < y → V ((y : ℂ) * I) = 0 := by
    intro y hy
    simp only [hV, invS_I_mul y, haxis y hy, sub_self]
  have hVana : ∀ y : ℝ, 0 < y → AnalyticOnNhd ℝ (fun x : ℝ => V ((x : ℂ) + (y : ℂ) * I)) univ := by
    intro y hy x hx
    exact (analyticAt_const.mul (analyticOnNhd_maassFun_line hg a b hy x hx)).sub
      (analyticOnNhd_maassFun_inv_line hg a b hy x hx)
  have h0 := MaassAxisContinuation.eq_zero_of_axis hVs hVpde hVeven hVax hVana z hz
  simp only [hV] at h0
  exact (sub_eq_zero.mp h0).symm

/-- **`u(−1/z) = ε u(z)`** for `Λ̂(1 − s) = ε Λ̂(s)`, `u = u_{εa, εb}`. -/
theorem maassFun_invS_sign
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ))
    {Λh : ℂ → ℂ} {ε : ℂ} (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = ε * Λh s)
    (hε : ε * ε = 1)
    (heq : ∀ s : ℂ, 1 < s.re → Λh s = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries g s)
    (hbd : ∃ B : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖Λh s‖ ≤ B) {z : ℂ}
    (hz : 0 < z.im) :
    maassFun g (ε * coeffA Λh) (ε * coeffB Λh) (invS z) =
      ε * maassFun g (ε * coeffA Λh) (ε * coeffB Λh) z :=
  maassFun_inv_eq_smul_of_axis (polyGrowth_of_summable hsum) _ _ ε
    (fun _ hy => maassFun_axis_sign hsum hΛ hsym hε heq hbd hy) hz

end RHTower.MaassConverseLevelOne
