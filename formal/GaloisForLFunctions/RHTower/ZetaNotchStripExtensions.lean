import GaloisForLFunctions.RHTower.ZetaNotchBohrLift
import GaloisForLFunctions.RHTower.StripHorizontalShift
import GaloisForLFunctions.HTGeometry.GammaReciprocalStripBound

/-!
# The factors of the `|ζ|²` notch in the strip `|Im z| < 1/2`

The three factors of the notch test `ω q w^{−1}` continue holomorphically off the real line:

* the reciprocal Gamma weight `W(z) = (2/(¼+z²))² Γℝ(½+iz)^{−1} Γℝ(½−iz)^{−1}` is holomorphic on
  `|Im z| < 1/2` (the double poles of `(¼+z²)^{−2}` sit at `±i/2`; `1/Γℝ` is entire), with
  `‖W(z)‖ ≤ C e^{π|Re z|}` on every closed substrip (`exists_norm_gammaWeightC_le`);
* `Z(z) = ζ(½+iz) ζ(½−iz)` is holomorphic on `|Im z| < 1/2` (the poles of `ζ` sit at `z = ∓i/2`),
  with `‖Z(z)‖ ≤ C (1 + |Re z|)²` on every closed substrip (`exists_norm_zetaSqC_le`);
* the notch weight `q` is a trigonometric polynomial, hence entire and bounded on horizontal strips
  (`exists_norm_notchWeightC_le`).

A horizontal shift then turns holomorphy on `|Im z| ≤ c` with integrable real-direction decay into
exponential decay of the transform (`norm_integral_mul_cexp_le_of_strip`):

`‖∫ G(x) e^{−ivx} dx‖ ≤ C E e^{−c|v|}`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.ZetaNotch

open RHTower.SmoothNumbers

/-! ## Bounds on compact boxes -/

/-- A function continuous on the box `|Re z| ≤ a`, `|Im z| ≤ c` is bounded there. -/
theorem exists_bound_on_box {f : ℂ → ℂ} {a c : ℝ}
    (hf : ∀ z : ℂ, |z.re| ≤ a → |z.im| ≤ c → ContinuousAt f z) :
    ∃ M, 0 ≤ M ∧ ∀ z : ℂ, |z.re| ≤ a → |z.im| ≤ c → ‖f z‖ ≤ M := by
  have hK : IsCompact (Icc (-a) a ×ℂ Icc (-c) c) := isCompact_Icc.reProdIm isCompact_Icc
  have hmem : ∀ z : ℂ, z ∈ Icc (-a) a ×ℂ Icc (-c) c ↔ |z.re| ≤ a ∧ |z.im| ≤ c := by
    intro z
    rw [Complex.mem_reProdIm, mem_Icc, mem_Icc, abs_le, abs_le]
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := f) fun z hz =>
    (hf z ((hmem z).mp hz).1 ((hmem z).mp hz).2).continuousWithinAt
  exact ⟨max M 0, le_max_right _ _, fun z hre him =>
    (hM z ((hmem z).mpr ⟨hre, him⟩)).trans (le_max_left _ _)⟩

/-! ## The reciprocal Gamma weight -/

/-- The reciprocal Gamma weight `(2/(¼+z²))² Γℝ(½+iz)^{−1} Γℝ(½−iz)^{−1}`. -/
def gammaWeightC (z : ℂ) : ℂ :=
  (2 / (1 / 4 + z ^ 2)) ^ 2 * ((Complex.Gammaℝ (1 / 2 + z * I))⁻¹ *
    (Complex.Gammaℝ (1 / 2 - z * I))⁻¹)

theorem gammaWeightC_ofReal (t : ℝ) : gammaWeightC t = gammaWeightInv t := by
  unfold gammaWeightC gammaWeightInv linePt
  push_cast
  ring_nf

theorem re_quarter_add_sq (z : ℂ) : (1 / 4 + z ^ 2).re = 1 / 4 + z.re ^ 2 - z.im ^ 2 := by
  simp [sq]
  ring

theorem quarter_sub_le_norm {z : ℂ} : 1 / 4 - z.im ^ 2 ≤ ‖(1 / 4 : ℂ) + z ^ 2‖ := by
  have h := Complex.re_le_norm ((1 / 4 : ℂ) + z ^ 2)
  rw [re_quarter_add_sq] at h
  nlinarith [sq_nonneg z.re]

theorem quarter_add_sq_ne_zero {z : ℂ} (hz : |z.im| < 1 / 2) : (1 / 4 : ℂ) + z ^ 2 ≠ 0 := by
  intro h
  have h1 := quarter_sub_le_norm (z := z)
  rw [h, norm_zero] at h1
  have : z.im ^ 2 < 1 / 4 := by
    have := abs_lt.mp hz
    nlinarith
  linarith

theorem differentiableAt_gammaWeightC {z : ℂ} (hz : |z.im| < 1 / 2) :
    DifferentiableAt ℂ gammaWeightC z := by
  have hq := quarter_add_sq_ne_zero hz
  have hG : Differentiable ℂ fun s : ℂ => (Complex.Gammaℝ s)⁻¹ := Complex.differentiable_Gammaℝ_inv
  have h0 : DifferentiableAt ℂ (fun w : ℂ => (1 / 4 : ℂ) + w ^ 2) z :=
    (differentiableAt_const _).add (differentiableAt_id.pow 2)
  have h1 : DifferentiableAt ℂ (fun w : ℂ => (2 / ((1 / 4 : ℂ) + w ^ 2)) ^ 2) z :=
    ((differentiableAt_const (2 : ℂ)).div h0 hq).pow 2
  have h2 : DifferentiableAt ℂ (fun w : ℂ => (Complex.Gammaℝ (1 / 2 + w * I))⁻¹) z :=
    DifferentiableAt.comp (g := fun s : ℂ => (Complex.Gammaℝ s)⁻¹)
      (f := fun w : ℂ => 1 / 2 + w * I) z hG.differentiableAt
      ((differentiableAt_const _).add (differentiableAt_id.mul (differentiableAt_const _)))
  have h3 : DifferentiableAt ℂ (fun w : ℂ => (Complex.Gammaℝ (1 / 2 - w * I))⁻¹) z :=
    DifferentiableAt.comp (g := fun s : ℂ => (Complex.Gammaℝ s)⁻¹)
      (f := fun w : ℂ => 1 / 2 - w * I) z hG.differentiableAt
      ((differentiableAt_const _).sub (differentiableAt_id.mul (differentiableAt_const _)))
  exact h1.mul (h2.mul h3)

/-- `‖Γℝ(½ + iz)^{−1}‖ ≤ C e^{π|Re z|/2}` for `|Im z| ≤ c < 1/2`. -/
theorem exists_norm_inv_Gammaℝ_half_add_le {c : ℝ} (hc : c < 1 / 2) :
    ∃ C, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ c →
      ‖(Complex.Gammaℝ (1 / 2 + z * I))⁻¹‖ ≤ C * Real.exp (Real.pi * |z.re| / 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_norm_inv_Gammaℝ 0 1 (by norm_num)
  have hG : Differentiable ℂ fun s : ℂ => (Complex.Gammaℝ s)⁻¹ := Complex.differentiable_Gammaℝ_inv
  obtain ⟨M, hM0, hM⟩ := exists_bound_on_box (f := fun z : ℂ => (Complex.Gammaℝ (1 / 2 + z * I))⁻¹)
    (a := 2) (c := c) fun z _ _ => (hG.differentiableAt.comp z (by fun_prop)).continuousAt
  refine ⟨max C₁ M, le_max_of_le_left hC₁0, fun z hz => ?_⟩
  have hre : (1 / 2 + z * I).re = 1 / 2 - z.im := by simp; ring
  have him : (1 / 2 + z * I).im = z.re := by simp
  have he : 1 ≤ Real.exp (Real.pi * |z.re| / 2) := Real.one_le_exp (by positivity)
  rcases le_or_gt 2 |z.re| with h2 | h2
  · have h := hC₁ (1 / 2 + z * I) (by rw [hre]; linarith [(abs_le.mp hz).2])
      (by rw [hre]; linarith [(abs_le.mp hz).1]) (by rw [him]; exact h2)
    rw [him] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · calc ‖(Complex.Gammaℝ (1 / 2 + z * I))⁻¹‖ ≤ M := hM z h2.le hz
      _ ≤ max C₁ M * 1 := by rw [mul_one]; exact le_max_right _ _
      _ ≤ max C₁ M * Real.exp (Real.pi * |z.re| / 2) :=
          mul_le_mul_of_nonneg_left he (le_max_of_le_left hC₁0)

/-- **The reciprocal Gamma weight on a substrip**: `‖W(z)‖ ≤ C e^{π|Re z|}` for `|Im z| ≤ c`. -/
theorem exists_norm_gammaWeightC_le {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ C, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ c → ‖gammaWeightC z‖ ≤ C * Real.exp (Real.pi * |z.re|) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_inv_Gammaℝ_half_add_le hc
  have hq0 : 0 < 1 / 4 - c ^ 2 := by nlinarith
  refine ⟨(2 / (1 / 4 - c ^ 2)) ^ 2 * (C * C), by positivity, fun z hz => ?_⟩
  have h1 := hC z hz
  have h2 := hC (-z) (by rw [Complex.neg_im, abs_neg]; exact hz)
  rw [Complex.neg_re, abs_neg, show (1 / 2 : ℂ) + -z * I = 1 / 2 - z * I by ring] at h2
  have hnq : 1 / 4 - c ^ 2 ≤ ‖(1 / 4 : ℂ) + z ^ 2‖ := by
    have := quarter_sub_le_norm (z := z)
    have : z.im ^ 2 ≤ c ^ 2 := by
      have := abs_le.mp hz
      nlinarith
    linarith
  have hfrac : ‖(2 / (1 / 4 + z ^ 2)) ^ 2‖ ≤ (2 / (1 / 4 - c ^ 2)) ^ 2 := by
    rw [norm_pow, norm_div]
    have hn2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hn2]
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left (by norm_num) hq0 hnq) 2
  unfold gammaWeightC
  rw [norm_mul, norm_mul]
  have hexp : Real.exp (Real.pi * |z.re| / 2) * Real.exp (Real.pi * |z.re| / 2) =
      Real.exp (Real.pi * |z.re|) := by rw [← Real.exp_add]; ring_nf
  calc ‖(2 / (1 / 4 + z ^ 2)) ^ 2‖ * (‖(Complex.Gammaℝ (1 / 2 + z * I))⁻¹‖ *
        ‖(Complex.Gammaℝ (1 / 2 - z * I))⁻¹‖)
      ≤ (2 / (1 / 4 - c ^ 2)) ^ 2 * ((C * Real.exp (Real.pi * |z.re| / 2)) *
          (C * Real.exp (Real.pi * |z.re| / 2))) :=
        mul_le_mul hfrac (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
          (by positivity) (by positivity)
    _ = (2 / (1 / 4 - c ^ 2)) ^ 2 * (C * C) * Real.exp (Real.pi * |z.re|) := by
        rw [← hexp]; ring

/-! ## `ζ(½+iz) ζ(½−iz)` in the strip -/

/-- `‖ζ(½ + iz)‖ ≤ C (1 + |Re z|)` for `|Im z| ≤ c < 1/2`. -/
theorem exists_norm_zeta_half_add_le {c : ℝ} (hc : c < 1 / 2) :
    ∃ C, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ c →
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + z * I)‖ ≤ C * (1 + |z.re|) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_on_box
    (f := fun z : ℂ => riemannZeta (((1 / 2 : ℝ) : ℂ) + z * I)) (a := 2) (c := c) fun z _ hz =>
      ((differentiableAt_riemannZeta (half_add_mul_I_ne_one (lt_of_le_of_lt hz hc))).comp z
        (by fun_prop)).continuousAt
  have hσ : 0 < 1 / 2 - c := by linarith
  refine ⟨max M (2 + 2 / (1 / 2 - c)), le_max_of_le_left hM0, fun z hz => ?_⟩
  have h1 : 1 ≤ 1 + |z.re| := by linarith [abs_nonneg z.re]
  rcases le_or_gt 2 |z.re| with h2 | h2
  · set σ : ℝ := 1 / 2 - z.im with hσdef
    have hσlo : 1 / 2 - c ≤ σ := by rw [hσdef]; linarith [(abs_le.mp hz).2]
    have hσhi : σ ≤ 1 := by
      rw [hσdef]; linarith [(abs_le.mp hz).1, abs_nonneg z.im, le_trans (abs_nonneg _) hz]
    have h := RHTower.ZetaGateProductAFE.norm_riemannZeta_le_strip' (σ := σ) (t := z.re)
      ⟨by linarith, by linarith⟩ h2
    rw [half_add_mul_I_eq]
    have hn : 2 ≤ ‖1 - ((σ : ℂ) + z.re * I)‖ := by
      have := Complex.abs_im_le_norm (1 - ((σ : ℂ) + z.re * I))
      have him' : (1 - ((σ : ℂ) + (z.re : ℂ) * I)).im = -z.re := by simp
      rw [him', abs_neg] at this
      linarith
    have hinv : 1 / ‖1 - ((σ : ℂ) + z.re * I)‖ ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hn
    have hdiv : 2 * |z.re| / σ ≤ 2 / (1 / 2 - c) * |z.re| := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) hσ]
      have := abs_nonneg z.re
      nlinarith
    calc ‖riemannZeta ((σ : ℂ) + z.re * I)‖
        ≤ 3 / 2 + 1 / ‖1 - ((σ : ℂ) + z.re * I)‖ + 2 * |z.re| / σ := h
      _ ≤ 2 + 2 / (1 / 2 - c) * |z.re| := by linarith
      _ ≤ (2 + 2 / (1 / 2 - c)) * (1 + |z.re|) := by
          have := abs_nonneg z.re
          have : 0 ≤ 2 / (1 / 2 - c) := by positivity
          nlinarith
      _ ≤ max M (2 + 2 / (1 / 2 - c)) * (1 + |z.re|) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  · calc ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + z * I)‖ ≤ M := hM z h2.le hz
      _ ≤ max M (2 + 2 / (1 / 2 - c)) * 1 := by rw [mul_one]; exact le_max_left _ _
      _ ≤ max M (2 + 2 / (1 / 2 - c)) * (1 + |z.re|) :=
          mul_le_mul_of_nonneg_left h1 (le_max_of_le_left hM0)

/-- **`ζ(½+iz) ζ(½−iz)` on a substrip**: `‖Z(z)‖ ≤ C (1 + |Re z|)²` for `|Im z| ≤ c < 1/2`. -/
theorem exists_norm_zetaPairC_le {c : ℝ} (hc : c < 1 / 2) :
    ∃ C, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ c → ‖zetaPairC z‖ ≤ C * (1 + |z.re|) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_zeta_half_add_le hc
  refine ⟨C * C, by positivity, fun z hz => ?_⟩
  have h1 := hC z hz
  have h2 := hC (-z) (by rw [Complex.neg_im, abs_neg]; exact hz)
  rw [Complex.neg_re, abs_neg] at h2
  unfold zetaPairC
  rw [norm_mul]
  calc ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + z * I)‖ * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + -z * I)‖
      ≤ (C * (1 + |z.re|)) * (C * (1 + |z.re|)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = C * C * (1 + |z.re|) ^ 2 := by ring

/-! ## The Bohr extension of the notch weight -/

variable {P : Finset ℕ}

/-- The entire extension `Σ m_{j,c} e^{i f_{j,c} z}` of the notch weight. -/
def notchWeightC (P : Finset ℕ) (ε : ℝ) (n₀ : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
    (modeCoeff ε j c : ℂ) * Complex.exp (z * modeFreq n₀ j c * I)

theorem notchWeightC_ofReal (P : Finset ℕ) (ε : ℝ) (n₀ : ℕ) (t : ℝ) :
    notchWeightC P ε n₀ t = notchWeight P ε n₀ t := by
  rw [notchWeight_eq_sum]
  unfold notchWeightC
  push_cast
  rfl

theorem differentiable_notchWeightC (P : Finset ℕ) (ε : ℝ) (n₀ : ℕ) :
    Differentiable ℂ (notchWeightC P ε n₀) := by
  unfold notchWeightC
  fun_prop

theorem exists_norm_notchWeightC_le (P : Finset ℕ) (ε : ℝ) (n₀ : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ 1 → ‖notchWeightC P ε n₀ z‖ ≤ C := by
  classical
  refine ⟨∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
    |modeCoeff ε j c| * Real.exp |modeFreq n₀ j c|,
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => by positivity, fun z hz => ?_⟩
  unfold notchWeightC
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
  have hre : (z * (modeFreq n₀ j c : ℂ) * I).re = -(z.im * modeFreq n₀ j c) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have h1 := abs_le.mp hz
  have h2 : |z.im * modeFreq n₀ j c| ≤ |modeFreq n₀ j c| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hz
  linarith [neg_abs_le (z.im * modeFreq n₀ j c)]

/-! ## Exponential decay of transforms -/

/-- The lower-line form of the horizontal shift. -/
theorem integral_horizontal_shift_lower {F : ℂ → ℂ} {c C r : ℝ} (hc : 0 ≤ c) (hr : 0 < r)
    (hF : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ F z)
    (hbound : ∀ z : ℂ, |z.im| ≤ c → ‖F z‖ ≤ C * Real.exp (-(r * |z.re|))) :
    (∫ x : ℝ, F ((x : ℂ) - (c : ℂ) * I)) = ∫ x : ℝ, F (x : ℂ) := by
  let G : ℂ → ℂ := fun z => F (-z)
  have hG : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ G z := fun z hz =>
    (hF (-z) (by simpa using hz)).comp z (by fun_prop)
  have hGb : ∀ z : ℂ, |z.im| ≤ c → ‖G z‖ ≤ C * Real.exp (-(r * |z.re|)) := fun z hz => by
    simpa [G] using hbound (-z) (by simpa using hz)
  have hshift := integral_horizontal_shift_of_decay hc hr hG hGb
  have hleft : (∫ x : ℝ, G ((x : ℂ) + (c : ℂ) * I)) = ∫ x : ℝ, F ((x : ℂ) - (c : ℂ) * I) := by
    rw [← integral_neg_eq_self (fun x : ℝ => F ((x : ℂ) - (c : ℂ) * I)) volume]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [G]
    congr 1
    push_cast
    ring
  have hright : (∫ x : ℝ, G (x : ℂ)) = ∫ x : ℝ, F (x : ℂ) := by
    simpa [G] using integral_neg_eq_self (fun x : ℝ => F (x : ℂ)) volume
  rw [← hleft, hshift, hright]

theorem re_neg_mul_mul_I (v : ℝ) (z : ℂ) : (-((v : ℂ) * z) * I).re = v * z.im := by
  simp [Complex.mul_re, Complex.mul_im]

/-- **Exponential decay by a horizontal shift.** If `G` is holomorphic on `|Im z| ≤ c` with
`‖G(z)‖ ≤ C e^{−|Re z|}` there, then `‖∫ G(x) e^{−ivx} dx‖ ≤ C E e^{−c|v|}`, `E = ∫ e^{−|x|} dx`. -/
theorem norm_integral_mul_cexp_le_of_strip {G : ℂ → ℂ} {c C : ℝ} (hc : 0 ≤ c)
    (hG : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ G z)
    (hbound : ∀ z : ℂ, |z.im| ≤ c → ‖G z‖ ≤ C * Real.exp (-|z.re|)) (v : ℝ) :
    ‖∫ x : ℝ, G x * Complex.exp (-(v * x) * I)‖ ≤
      C * (∫ x : ℝ, Real.exp (-(1 * |x|))) * Real.exp (-(c * |v|)) := by
  set F : ℂ → ℂ := fun z => G z * Complex.exp (-((v : ℂ) * z) * I) with hFdef
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hbound 0 (by simpa using hc))
    simpa using h
  have hFd : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ F z := fun z hz =>
    (hG z hz).mul (by fun_prop)
  have hnormF : ∀ z : ℂ, ‖F z‖ = ‖G z‖ * Real.exp (v * z.im) := by
    intro z
    rw [hFdef, norm_mul, Complex.norm_exp, re_neg_mul_mul_I]
  have hFb : ∀ z : ℂ, |z.im| ≤ c →
      ‖F z‖ ≤ (C * Real.exp (|v| * c)) * Real.exp (-(1 * |z.re|)) := by
    intro z hz
    rw [hnormF, one_mul]
    have hvz : v * z.im ≤ |v| * c := by
      calc v * z.im ≤ |v * z.im| := le_abs_self _
        _ = |v| * |z.im| := abs_mul _ _
        _ ≤ |v| * c := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    calc ‖G z‖ * Real.exp (v * z.im) ≤ (C * Real.exp (-|z.re|)) * Real.exp (|v| * c) :=
          mul_le_mul (hbound z hz) (Real.exp_le_exp.mpr hvz) (Real.exp_pos _).le (by positivity)
      _ = C * Real.exp (|v| * c) * Real.exp (-|z.re|) := by ring
  have hE : Integrable (fun x : ℝ => Real.exp (-(1 * |x|))) := integrable_exp_neg_mul_abs' one_pos
  have hline : ∀ y : ℝ, |y| ≤ c → v * y ≤ -(c * |v|) →
      ‖∫ x : ℝ, F ((x : ℂ) + (y : ℂ) * I)‖ ≤
        C * (∫ x : ℝ, Real.exp (-(1 * |x|))) * Real.exp (-(c * |v|)) := by
    intro y hy hvy
    have hRHS : C * (∫ x : ℝ, Real.exp (-(1 * |x|))) * Real.exp (-(c * |v|)) =
        ∫ x : ℝ, C * Real.exp (-(c * |v|)) * Real.exp (-(1 * |x|)) := by
      rw [integral_const_mul]; ring
    rw [hRHS]
    refine norm_integral_le_of_norm_le (hE.const_mul _) (Eventually.of_forall fun x => ?_)
    have hz : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
    have hzr : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
    rw [hnormF, hz]
    have hb := hbound ((x : ℂ) + (y : ℂ) * I) (by rw [hz]; exact hy)
    rw [hzr] at hb
    rw [one_mul]
    calc ‖G ((x : ℂ) + (y : ℂ) * I)‖ * Real.exp (v * y)
        ≤ (C * Real.exp (-|x|)) * Real.exp (-(c * |v|)) :=
          mul_le_mul hb (Real.exp_le_exp.mpr hvy) (Real.exp_pos _).le
            (mul_nonneg hC0 (Real.exp_pos _).le)
      _ = C * Real.exp (-(c * |v|)) * Real.exp (-|x|) := by ring
  have hid : (∫ x : ℝ, G x * Complex.exp (-(v * x) * I)) = ∫ x : ℝ, F (x : ℂ) := rfl
  rw [hid]
  rcases le_or_gt 0 v with hv | hv
  · rw [← integral_horizontal_shift_lower hc one_pos hFd hFb]
    have h := hline (-c) (by rw [abs_neg, abs_of_nonneg hc]) (by
      rw [abs_of_nonneg hv]; linarith)
    simpa [sub_eq_add_neg] using h
  · rw [← integral_horizontal_shift_of_decay hc one_pos hFd hFb]
    exact hline c (by rw [abs_of_nonneg hc]) (by rw [abs_of_neg hv]; linarith)

end RHTower.ZetaNotch
