import GaloisForLFunctions.RHTower.ZetaNotchDualContour
import GaloisForLFunctions.HTGeometry.SmoothBlockWindow

/-!
# Height oscillation of the critical dual weight

Let `ω = ω_L` be the smooth block window, equal to `1` on `[L, 2L]` and supported in
`[L/2, 5L/2]`. For `Y > 0` and a frequency `ξ ≠ 0` consider

`J(Y, ξ) = ∫ ω(t) W_t(Y) e^{−iξt} dt`,

where `W_t` is the dual weight of the product approximate functional equation at `(½+it, ½−it)`.
By Fubini, `J` is a Gaussian average over the Mellin variable of the windowed carriers
`∫ ω(t) G_t(w) e^{−iξt} dt`. One integration by parts in the height uses the carrier law
`∂_t G_t = G_t D_t` and the increment bound `‖D_t(w)‖ ≤ 20‖w‖/t`.

* **Dual line `Re w = −1`** (`norm_notchDualOscillation_le`):
  `‖J(Y, ξ)‖ ≤ (C/Y)(L²/|ξ| + L³ e^{−L²/32})`. The carrier has size `≍ t²`.
* **Right line `Re w = δ = 1/4`**, after the residue shift `W_t = 1 + W_t^{(−δ)}`
  (`norm_notchDualOscillation_sub_window_le`):
  `‖J(Y, ξ) − ω̂(ξ)‖ ≤ C Y^{1/4}(L^{−1/2}/|ξ| + L e^{−L²/32})`. The carrier has size
  `≍ t^{−1/2}`.

The first bound controls large `Y`, the second small `Y`. Together they give the uniform
height-oscillation law of the dual part of `|ζ(½+it)|²`.
-/

noncomputable section

namespace RHTower.ZetaNotch

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

/-! ## The notch window -/

/-- The notch window: `1` on `[L, 2L]`, `0` outside `[L/2, 5L/2]`. -/
def notchWindow (L : ℝ) : ℝ → ℂ := blockWindowC L (2 * L) (L / 2)

theorem notchWindow_eq_zero {L t : ℝ} (hL : 0 < L) (ht : t ∉ Icc (L / 2) (5 * L / 2)) :
    notchWindow L t = 0 := by
  have hη : (0 : ℝ) < L / 2 := by linarith
  have ht' : t ∉ Icc (L - L / 2) (2 * L + L / 2) := by
    rw [show L - L / 2 = L / 2 by ring, show 2 * L + L / 2 = 5 * L / 2 by ring]
    exact ht
  have h := iteratedDeriv_blockWindowC_eq_zero 0 hη ht'
  simpa [notchWindow] using h

theorem norm_notchWindow_le_one (L t : ℝ) : ‖notchWindow L t‖ ≤ 1 := by
  unfold notchWindow blockWindowC
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (blockWindow_nonneg _ _ _ _)]
  exact blockWindow_le_one _ _ _ _

theorem contDiff_notchWindow (L : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (notchWindow L) :=
  contDiff_blockWindowC _ _ _

theorem hasDerivAt_notchWindow (L t : ℝ) :
    HasDerivAt (notchWindow L) (deriv (notchWindow L) t) t :=
  ((contDiff_notchWindow L).differentiable (by simp)).differentiableAt.hasDerivAt

theorem norm_deriv_notchWindow_le {L : ℝ} (hL : 0 < L) (t : ℝ) :
    ‖deriv (notchWindow L) t‖ ≤ 2 * blockWindowConst 1 / L := by
  have h := norm_iteratedDeriv_blockWindowC_le 1 L (2 * L) (η := L / 2) (by linarith) t
  rw [iteratedDeriv_one] at h
  unfold notchWindow
  calc _ ≤ blockWindowConst 1 / (L / 2) ^ 1 := h
    _ = 2 * blockWindowConst 1 / L := by rw [pow_one]; field_simp

theorem deriv_notchWindow_eq_zero {L t : ℝ} (hL : 0 < L) (ht : t ∉ Icc (L / 2) (5 * L / 2)) :
    deriv (notchWindow L) t = 0 := by
  have hη : (0 : ℝ) < L / 2 := by linarith
  have ht' : t ∉ Icc (L - L / 2) (2 * L + L / 2) := by
    rw [show L - L / 2 = L / 2 by ring, show 2 * L + L / 2 = 5 * L / 2 by ring]
    exact ht
  have h := iteratedDeriv_blockWindowC_eq_zero 1 hη ht'
  rw [iteratedDeriv_one] at h
  exact h

theorem continuous_notchWindow (L : ℝ) : Continuous (notchWindow L) :=
  (contDiff_notchWindow L).continuous

theorem continuous_deriv_notchWindow (L : ℝ) : Continuous (deriv (notchWindow L)) :=
  (contDiff_notchWindow L).continuous_deriv (by simp)

/-! ## One integration by parts -/

/-- **One integration by parts against `e^{−iξx}`**, for an amplitude vanishing at both ends. -/
theorem norm_intervalIntegral_mul_cexp_le {g g' : ℝ → ℂ} {a b ξ : ℝ} (hab : a ≤ b) (hξ : ξ ≠ 0)
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g' x) x) (hg' : IntervalIntegrable g' volume a b)
    (ha : g a = 0) (hb : g b = 0) :
    ‖∫ x in a..b, g x * Complex.exp (-(ξ * x) * I)‖ ≤ (∫ x in a..b, ‖g' x‖) / |ξ| := by
  have hξC : (-(ξ : ℂ) * I) ≠ 0 := by
    simp [hξ, Complex.I_ne_zero]
  set v : ℝ → ℂ := fun x => Complex.exp (-(ξ * x) * I) / (-(ξ : ℂ) * I) with hvdef
  have hv : ∀ x ∈ uIcc a b, HasDerivAt v (Complex.exp (-(ξ * x) * I)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -((ξ : ℂ) * (y : ℂ)) * I) (-(ξ : ℂ) * I) x := by
      have := ((hasDerivAt_id (x : ℂ)).const_mul (ξ : ℂ)).neg.mul_const I
      simpa using this.comp_ofReal
    have h2 := (h1.cexp).div_const (-(ξ : ℂ) * I)
    rw [mul_div_cancel_right₀ _ hξC] at h2
    exact h2
  have hvcont : IntervalIntegrable (fun x : ℝ => Complex.exp (-(ξ * x) * I)) volume a b :=
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (-(ξ * x) * I)).intervalIntegrable _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hg hv hg' hvcont
  rw [hparts, ha, hb, zero_mul, zero_mul, sub_zero, zero_sub, norm_neg]
  have hvnorm : ∀ x : ℝ, ‖v x‖ = 1 / |ξ| := by
    intro x
    simp only [hvdef, norm_div, norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_real,
      Real.norm_eq_abs]
    rw [Complex.norm_exp]
    simp
  calc ‖∫ x in a..b, g' x * v x‖ ≤ ∫ x in a..b, ‖g' x‖ * (1 / |ξ|) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ (hg'.norm.mul_const _)
        exact Filter.Eventually.of_forall fun x _ => by rw [norm_mul, hvnorm]
    _ = (∫ x in a..b, ‖g' x‖) / |ξ| := by
        rw [intervalIntegral.integral_mul_const]
        ring

/-- The windowed height integral over `ℝ` equals the interval integral over `[L/4, 3L]`. -/
theorem integral_notchWindow_mul_eq_intervalIntegral {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ) :
    ∫ t, notchWindow L t * f t = ∫ t in (L / 4)..(3 * L), notchWindow L t * f t := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  rw [← integral_Icc_eq_integral_Ioc]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  rw [notchWindow_eq_zero hL, zero_mul]
  intro ht'
  apply ht
  exact ⟨by linarith [ht'.1], by linarith [ht'.2]⟩

/-- **Windowed carrier oscillation**, abstract form: if `‖G_t‖ ≤ A` and `‖G_t D_t‖ ≤ A·B` on the
support of the window, the oscillation integral is at most `A(4c + 2L·B)/|ξ|`, with
`c = blockWindowConst 1`. -/
theorem norm_integral_notchWindow_mul_cexp_le {L : ℝ} (hL : 0 < L) {G G' : ℝ → ℂ} {A B ξ : ℝ}
    (hξ : ξ ≠ 0) (hG : ∀ t, HasDerivAt G (G' t) t) (hG'c : Continuous G')
    (hA : ∀ t ∈ Icc (L / 2) (5 * L / 2), ‖G t‖ ≤ A)
    (hB : ∀ t ∈ Icc (L / 2) (5 * L / 2), ‖G' t‖ ≤ A * B) :
    ‖∫ t, notchWindow L t * G t * Complex.exp (-(ξ * t) * I)‖ ≤
      A * (4 * blockWindowConst 1 + 2 * L * B) / |ξ| := by
  have hc := blockWindowConst_nonneg 1
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA L ⟨by linarith, by linarith⟩)
  set g : ℝ → ℂ := fun t => notchWindow L t * G t with hgdef
  set g' : ℝ → ℂ := fun t => deriv (notchWindow L) t * G t + notchWindow L t * G' t with hg'def
  have hgd : ∀ t, HasDerivAt g (g' t) t := fun t =>
    (hasDerivAt_notchWindow L t).mul (hG t)
  have hGc : Continuous G := continuous_iff_continuousAt.mpr fun t => (hG t).continuousAt
  have hg'c : Continuous g' :=
    ((continuous_deriv_notchWindow L).mul hGc).add ((continuous_notchWindow L).mul hG'c)
  have hrw : ∫ t, notchWindow L t * G t * Complex.exp (-(ξ * t) * I) =
      ∫ t in (L / 4)..(3 * L), g t * Complex.exp (-(ξ * t) * I) := by
    have := integral_notchWindow_mul_eq_intervalIntegral hL
      (fun t => G t * Complex.exp (-(ξ * t) * I))
    simpa only [hgdef, mul_assoc] using this
  rw [hrw]
  have hga : g (L / 4) = 0 := by
    simp only [hgdef]
    rw [notchWindow_eq_zero hL (fun h => by linarith [h.1]), zero_mul]
  have hgb : g (3 * L) = 0 := by
    simp only [hgdef]
    rw [notchWindow_eq_zero hL (fun h => by linarith [h.2]), zero_mul]
  have hibp := norm_intervalIntegral_mul_cexp_le (by linarith : L / 4 ≤ 3 * L) hξ
    (fun x _ => hgd x) (hg'c.intervalIntegrable _ _) hga hgb
  refine hibp.trans ?_
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  -- pointwise bound on `‖g'‖`
  have hpt : ∀ t, ‖g' t‖ ≤ (Icc (L / 2) (5 * L / 2)).indicator
      (fun _ => A * (2 * blockWindowConst 1 / L) + A * B) t := by
    intro t
    by_cases ht : t ∈ Icc (L / 2) (5 * L / 2)
    · rw [indicator_of_mem ht]
      simp only [hg'def]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have h1 : ‖deriv (notchWindow L) t‖ * ‖G t‖ ≤ (2 * blockWindowConst 1 / L) * A :=
        mul_le_mul (norm_deriv_notchWindow_le hL t) (hA t ht) (norm_nonneg _) (by positivity)
      have h2 : ‖notchWindow L t‖ * ‖G' t‖ ≤ 1 * (A * B) :=
        mul_le_mul (norm_notchWindow_le_one L t) (hB t ht) (norm_nonneg _) zero_le_one
      linarith
    · rw [indicator_of_notMem ht]
      simp only [hg'def, deriv_notchWindow_eq_zero hL ht, notchWindow_eq_zero hL ht, zero_mul,
        add_zero, norm_zero, le_refl]
  have hB0 : 0 ≤ A * B := (norm_nonneg _).trans (hB L ⟨by linarith, by linarith⟩)
  calc ∫ x in (L / 4)..(3 * L), ‖g' x‖
      ≤ ∫ x in (L / 4)..(3 * L), (Icc (L / 2) (5 * L / 2)).indicator
          (fun _ => A * (2 * blockWindowConst 1 / L) + A * B) x := by
        apply intervalIntegral.integral_mono_on (by linarith) (hg'c.norm.intervalIntegrable _ _)
        · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
            |>.intervalIntegrable
        · intro x _; exact hpt x
    _ = (A * (2 * blockWindowConst 1 / L) + A * B) * (2 * L) := by
        rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
          setIntegral_indicator measurableSet_Icc]
        rw [show Icc (L / 4) (3 * L) ∩ Icc (L / 2) (5 * L / 2) = Icc (L / 2) (5 * L / 2) by
          ext x; simp only [mem_inter_iff, mem_Icc]; constructor
          · intro h; exact h.2
          · intro h; exact ⟨⟨by linarith [h.1], by linarith [h.2]⟩, h⟩]
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring
    _ = A * (4 * blockWindowConst 1 + 2 * L * B) := by
        field_simp
        ring

/-- The trivial bound for a windowed carrier. -/
theorem norm_integral_notchWindow_mul_cexp_le_trivial {L : ℝ} (hL : 0 < L) {G : ℝ → ℂ} {A ξ : ℝ}
    (hA : ∀ t ∈ Icc (L / 2) (5 * L / 2), ‖G t‖ ≤ A) :
    ‖∫ t, notchWindow L t * G t * Complex.exp (-(ξ * t) * I)‖ ≤ 2 * L * A := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA L ⟨by linarith, by linarith⟩)
  have hrw := integral_notchWindow_mul_eq_intervalIntegral hL
    (fun t => G t * Complex.exp (-(ξ * t) * I))
  simp only [← mul_assoc] at hrw
  rw [hrw]
  have hpt : ∀ t, ‖notchWindow L t * G t * Complex.exp (-(ξ * t) * I)‖ ≤
      (Icc (L / 2) (5 * L / 2)).indicator (fun _ => A) t := by
    intro t
    by_cases ht : t ∈ Icc (L / 2) (5 * L / 2)
    · rw [indicator_of_mem ht, norm_mul, norm_mul, Complex.norm_exp]
      have hre : (-(↑ξ * ↑t) * I).re = 0 := by simp
      rw [hre, Real.exp_zero, mul_one]
      exact (mul_le_mul (norm_notchWindow_le_one L t) (hA t ht) (norm_nonneg _)
        zero_le_one).trans (by rw [one_mul])
    · rw [indicator_of_notMem ht, notchWindow_eq_zero hL ht]
      simp
  calc _ ≤ ∫ x in (L / 4)..(3 * L), (Icc (L / 2) (5 * L / 2)).indicator (fun _ => A) x := by
        apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
        · exact Filter.Eventually.of_forall fun x _ => hpt x
        · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
            |>.intervalIntegrable
    _ = 2 * L * A := by
        rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
          setIntegral_indicator measurableSet_Icc]
        rw [show Icc (L / 4) (3 * L) ∩ Icc (L / 2) (5 * L / 2) = Icc (L / 2) (5 * L / 2) by
          ext x; simp only [mem_inter_iff, mem_Icc]; constructor
          · intro h; exact h.2
          · intro h; exact ⟨⟨by linarith [h.1], by linarith [h.2]⟩, h⟩]
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring

end RHTower.ZetaNotch
