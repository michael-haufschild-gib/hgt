import GaloisForLFunctions.RHTower.WeilDeviationSpectralPairing

/-!
# Frequency packets against a translation-bounded weight

Let `w ≥ 0` be a weight on `ℕ` whose pairing with Cauchy profiles is bounded:
`Σ_n w(n)(P_{η,s}(log n) + P_{η,s}(−log n)) ≤ D` for all `0 < η ≤ 1` and all `s`, where
`P_{η,s}(u) = η/(1 + (η(u − s))²)`. This is how the deficit of a Weil-positive system with summable
excess behaves (`exists_tsum_deficit_cauchyProfile_le`).

A *frequency packet* is `ξ ↦ B((ξ − γ)/η)`. Its transform is `η e^{−2πiγu} 𝓕B(ηu)`: a wave of
frequency `γ` over a window of length `1/η`.

**Packet limit** (`norm_weightPairing_fourier_mul_packet_sub_le`). For an amplitude `h`, the pairing
of `w` with `𝓕(h · packet)` is `h(γ)` times the pairing with `𝓕(packet)`, up to an error at most

`2 C'_B D ∫ |𝓕h(s)| η|s|(1 + η²s²) ds`,

where `C'_B` bounds `(1 + x²)|(𝓕B)'(x)|`. The error tends to `0` with `η` and is scale-covariant.

**Proof.**
- Fourier inversion writes `𝓕(h · packet)` as the convolution `∫ 𝓕h(s) 𝓕(packet)(u − s) ds`.
- Shifting the window by `s` changes the transform by at most
  `2C'_B η|s|(1 + η²s²) P_{η,0}(u)`, by the mean value theorem and Peetre's inequality.
- `∫ 𝓕h(s) e^{2πiγs} ds = h(γ)`.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate ENNReal

namespace RHTower.WeilExcess

noncomputable section

/-! ## A Tonelli helper -/

/-- Interchange of a series and an integral for nonnegative terms, with a bound. -/
theorem summable_integral_le_of_tsum_le {f : ℕ → ℝ → ℝ} (hf0 : ∀ n x, 0 ≤ f n x)
    (hfm : ∀ n, Measurable (f n)) {G : ℝ → ℝ} (hGi : Integrable G)
    (hs : ∀ x, Summable fun n => f n x) (hle : ∀ x, ∑' n, f n x ≤ G x) :
    (∀ n, Integrable (f n)) ∧ Summable (fun n => ∫ x, f n x) ∧
      ∑' n, ∫ x, f n x ≤ ∫ x, G x := by
  have hfn : ∀ n x, f n x ≤ G x := fun n x =>
    ((hs x).le_tsum n fun m _ => hf0 m x).trans (hle x)
  have hfi : ∀ n, Integrable (f n) := fun n =>
    hGi.mono' (hfm n).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 n x)]; exact hfn n x)
  have hG0 : ∀ x, 0 ≤ G x := fun x => (hf0 0 x).trans (hfn 0 x)
  refine ⟨hfi, ?_⟩
  have hint0 : ∀ n, 0 ≤ ∫ x, f n x := fun n => integral_nonneg (hf0 n)
  have hlin : ∑' n, ENNReal.ofReal (∫ x, f n x) = ∫⁻ x, ENNReal.ofReal (∑' n, f n x) := by
    have e1 : ∀ n, ENNReal.ofReal (∫ x, f n x) = ∫⁻ x, ENNReal.ofReal (f n x) := fun n =>
      ofReal_integral_eq_lintegral_ofReal (hfi n) (Eventually.of_forall (hf0 n))
    simp only [e1]
    rw [← lintegral_tsum fun n => (hfm n).ennreal_ofReal.aemeasurable]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => hf0 n x) (hs x)]
  have hle' : ∫⁻ x, ENNReal.ofReal (∑' n, f n x) ≤ ENNReal.ofReal (∫ x, G x) := by
    rw [ofReal_integral_eq_lintegral_ofReal hGi (Eventually.of_forall hG0)]
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hle x)
  have htot := hlin ▸ hle'
  have hne : ∑' n, ENNReal.ofReal (∫ x, f n x) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top htot
  have hsg : Summable fun n => ∫ x, f n x :=
    (ENNReal.summable_toReal hne).congr fun n => ENNReal.toReal_ofReal (hint0 n)
  refine ⟨hsg, ?_⟩
  have e := ENNReal.ofReal_tsum_of_nonneg hint0 hsg
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hG0)).mp (e ▸ htot)

/-! ## Weight pairings and profile bounds -/

/-- The pairing of a weight on `ℕ` with a test function on the `u`-line. -/
def weightPairing (w : ℕ → ℝ) (φ : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, (w n : ℂ) * (φ (Real.log n) + φ (-Real.log n))

theorem summable_weightPairing_of_profile {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {D : ℝ}
    (hD : CauchyBounded w D) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {s C : ℝ} {φ : ℝ → ℂ}
    (hφ : ∀ u, ‖φ u‖ ≤ C * cauchyProfile η s u) :
    Summable (fun n : ℕ => (w n : ℂ) * (φ (Real.log n) + φ (-Real.log n))) ∧
      ‖weightPairing w φ‖ ≤ C * D := by
  obtain ⟨hs, hle⟩ := hD η hη0 hη1 s
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hφ s)
    have hp : 0 < cauchyProfile η s s := by simp only [cauchyProfile]; positivity
    exact nonneg_of_mul_nonneg_left h hp
  have hb : ∀ n : ℕ, ‖(w n : ℂ) * (φ (Real.log n) + φ (-Real.log n))‖ ≤
      C * (w n * (cauchyProfile η s (Real.log n) + cauchyProfile η s (-Real.log n))) := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw n)]
    have h1 := hφ (Real.log n)
    have h2 := hφ (-Real.log n)
    calc w n * ‖φ (Real.log n) + φ (-Real.log n)‖
        ≤ w n * (C * cauchyProfile η s (Real.log n) + C * cauchyProfile η s (-Real.log n)) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 h2)) (hw n)
      _ = C * (w n * (cauchyProfile η s (Real.log n) + cauchyProfile η s (-Real.log n))) := by ring
  have hsum : Summable (fun n : ℕ => (w n : ℂ) * (φ (Real.log n) + φ (-Real.log n))) :=
    Summable.of_norm_bounded (hs.mul_left C) hb
  refine ⟨hsum, ?_⟩
  unfold weightPairing
  calc ‖∑' n : ℕ, (w n : ℂ) * (φ (Real.log n) + φ (-Real.log n))‖
      ≤ ∑' n : ℕ, C * (w n * (cauchyProfile η s (Real.log n) + cauchyProfile η s (-Real.log n))) :=
        tsum_of_norm_bounded (hs.mul_left C).hasSum hb
    _ = C * ∑' n : ℕ, w n * (cauchyProfile η s (Real.log n) + cauchyProfile η s (-Real.log n)) :=
        tsum_mul_left
    _ ≤ C * D := mul_le_mul_of_nonneg_left hle hC

/-! ## Packets -/

/-- The frequency packet `ξ ↦ B((ξ − γ)/η)`. -/
def packet (B : ℝ → ℂ) (γ η : ℝ) (ξ : ℝ) : ℂ := B ((ξ - γ) / η)

/-- The transform of a packet: `η e^{−2πiγu} 𝓕B(ηu)`. -/
theorem fourier_packet (B : ℝ → ℂ) (γ : ℝ) {η : ℝ} (hη : 0 < η) (u : ℝ) :
    𝓕 (packet B γ η) u =
      (η : ℂ) * Complex.exp (-(2 * π * γ * u : ℝ) * I) * 𝓕 B (η * u) := by
  rw [fourier_eq_integral, fourier_eq_integral]
  set f : ℝ → ℂ := fun ξ => Complex.exp (-(2 * π * ξ * u : ℝ) * I) * packet B γ η ξ with hf
  have key : ∫ ξ, f ξ = (η : ℂ) * ∫ x, f (γ + η * x) := by
    rw [Measure.integral_comp_mul_left (fun y => f (γ + y)) η,
      integral_add_left_eq_self (μ := volume) f γ, abs_inv, abs_of_pos hη, Complex.real_smul, ← mul_assoc]
    push_cast
    rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hη.ne'), one_mul]
  rw [key, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hf, packet, show γ + η * x - γ = η * x by ring, mul_div_cancel_left₀ _ hη.ne']
  rw [show (-((2 * π * (γ + η * x) * u : ℝ) : ℂ)) * I =
      -((2 * π * γ * u : ℝ) : ℂ) * I + -((2 * π * x * (η * u) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_add]
  ring

theorem integrable_packet {B : ℝ → ℂ} (hB : Integrable B) (γ : ℝ) {η : ℝ} (hη : 0 < η) :
    Integrable (packet B γ η) := by
  have h1 : Integrable (fun x => B (η⁻¹ * x)) := hB.comp_mul_left' (inv_ne_zero hη.ne')
  have h2 := h1.comp_sub_right γ
  refine h2.congr (Eventually.of_forall fun ξ => ?_)
  simp only [packet, div_eq_inv_mul]

/-- **Convolution formula.** `𝓕(h · P)(u) = ∫ 𝓕h(s) 𝓕P(u − s) ds`. -/
theorem fourier_mul_eq_integral {h P : ℝ → ℂ} (hc : Continuous h) (hi : Integrable h)
    (hFi : Integrable (𝓕 h)) (hP : Integrable P) (u : ℝ) :
    𝓕 (fun ξ => h ξ * P ξ) u = ∫ s, 𝓕 h s * 𝓕 P (u - s) := by
  have hinv : ∀ ξ, h ξ = ∫ s, Complex.exp ((2 * π * s * ξ : ℝ) * I) * 𝓕 h s := by
    intro ξ
    rw [← fourierInv_eq_integral, hi.fourierInv_fourier_eq hFi hc.continuousAt]
  set F : ℝ → ℝ → ℂ := fun ξ s => Complex.exp (-(2 * π * ξ * (u - s) : ℝ) * I) * (P ξ * 𝓕 h s)
    with hF
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hprod : Integrable (fun p : ℝ × ℝ => P p.1 * 𝓕 h p.2) (volume.prod volume) :=
      hP.mul_prod hFi
    refine hprod.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
    · refine AEStronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop)) ?_
      exact AEStronglyMeasurable.mul hP.aestronglyMeasurable.comp_fst
        hFi.aestronglyMeasurable.comp_snd
    · simp only [Function.uncurry, hF, norm_mul]
      rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [fourier_eq_integral]
  have h1 : (∫ ξ, Complex.exp (-(2 * π * ξ * u : ℝ) * I) * (h ξ * P ξ)) = ∫ ξ, ∫ s, F ξ s := by
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [hinv ξ, ← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [hF]
    rw [show (-((2 * π * ξ * (u - s) : ℝ) : ℂ)) * I =
      -((2 * π * ξ * u : ℝ) : ℂ) * I + ((2 * π * s * ξ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_add]
    ring
  rw [h1, integral_integral_swap hFint]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  dsimp only
  rw [fourier_eq_integral P (u - s), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [hF]; ring

/-! ## The shift estimate -/

theorem peetre (a b : ℝ) : 1 + a ^ 2 ≤ 2 * (1 + (a - b) ^ 2) * (1 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b - b * (a - b)), sq_nonneg b, sq_nonneg (a - b), sq_nonneg (a - 2 * b),
    mul_nonneg (sq_nonneg b) (sq_nonneg (a - b))]

/-- Moving a window of length `1/η` by `s` changes it by at most
`2C' η|s|(1 + η²s²) P_{η,0}(u)`. -/
theorem norm_scaled_sub_le {f df : ℝ → ℂ} {C' : ℝ} (hf : ∀ x, HasDerivAt f (df x) x)
    (hdf : ∀ x, ‖df x‖ ≤ C' / (1 + x ^ 2)) {η : ℝ} (hη : 0 < η) (s u : ℝ) :
    ‖(η : ℂ) * f (η * (u - s)) - (η : ℂ) * f (η * u)‖ ≤
      2 * C' * (η * |s| * (1 + η ^ 2 * s ^ 2)) * cauchyProfile η 0 u := by
  have hC' : 0 ≤ C' := by
    have := (norm_nonneg _).trans (hdf 0); simpa using this
  set M : ℝ := 2 * C' * (1 + η ^ 2 * s ^ 2) / (1 + (η * u) ^ 2) with hM
  have hbound : ∀ x ∈ segment ℝ (η * u) (η * (u - s)), ‖df x‖ ≤ M := by
    intro x hx
    obtain ⟨θ, hθ0, hθ1, rfl⟩ : ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ x = η * u - θ * (η * s) := by
      rw [segment_eq_image'] at hx
      obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hx
      exact ⟨θ, hθ0, hθ1, by ring⟩
    refine (hdf _).trans ?_
    have hp := peetre (η * u) (θ * (η * s))
    have hθs : (θ * (η * s)) ^ 2 ≤ η ^ 2 * s ^ 2 := by
      have : θ ^ 2 ≤ 1 := by nlinarith
      calc (θ * (η * s)) ^ 2 = θ ^ 2 * (η ^ 2 * s ^ 2) := by ring
        _ ≤ 1 * (η ^ 2 * s ^ 2) := mul_le_mul_of_nonneg_right this (by positivity)
        _ = η ^ 2 * s ^ 2 := one_mul _
    rw [hM, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 1 + (η * u) ^ 2 ≤ 2 * (1 + (η * u - θ * (η * s)) ^ 2) * (1 + η ^ 2 * s ^ 2) :=
      hp.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    nlinarith
  have hmv := (convex_segment (η * u) (η * (u - s))).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := df) (fun x _ => (hf x).hasDerivWithinAt) hbound
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  have hd : ‖η * (u - s) - η * u‖ = η * |s| := by
    rw [Real.norm_eq_abs, show η * (u - s) - η * u = -(η * s) by ring, abs_neg, abs_mul,
      abs_of_pos hη]
  rw [hd] at hmv
  calc η * ‖f (η * (u - s)) - f (η * u)‖ ≤ η * (M * (η * |s|)) :=
        mul_le_mul_of_nonneg_left hmv hη.le
    _ = 2 * C' * (η * |s| * (1 + η ^ 2 * s ^ 2)) * cauchyProfile η 0 u := by
        simp only [hM, cauchyProfile, sub_zero]
        field_simp

/-! ## The packet limit -/

theorem continuous_cauchyProfile_center (η u : ℝ) : Continuous fun s => cauchyProfile η s u := by
  unfold cauchyProfile
  exact continuous_const.div (by fun_prop) fun s => by positivity

/-- The inversion formula as an integral against `𝓕h`. -/
theorem eq_integral_fourier {h : ℝ → ℂ} (hc : Continuous h) (hi : Integrable h)
    (hFi : Integrable (𝓕 h)) (γ : ℝ) :
    h γ = ∫ s, Complex.exp ((2 * π * s * γ : ℝ) * I) * 𝓕 h s := by
  rw [← fourierInv_eq_integral, hi.fourierInv_fourier_eq hFi hc.continuousAt]

/-- **Packet limit.** -/
theorem norm_weightPairing_fourier_mul_packet_sub_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {D : ℝ}
    (hD : CauchyBounded w D) {B dB : ℝ → ℂ} {CB CB' : ℝ} (hBi : Integrable B)
    (hFB : ∀ x, ‖𝓕 B x‖ ≤ CB / (1 + x ^ 2)) (hdFB : ∀ x, HasDerivAt (𝓕 B) (dB x) x)
    (hdB : ∀ x, ‖dB x‖ ≤ CB' / (1 + x ^ 2))
    {h : ℝ → ℂ} (hc : Continuous h) (hi : Integrable h) (hFi : Integrable (𝓕 h))
    (hFm : Integrable fun s => ‖𝓕 h s‖ * (|s| * (1 + s ^ 2)))
    (γ : ℝ) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    Summable (fun n : ℕ => (w n : ℂ) * (𝓕 (fun ξ => h ξ * packet B γ η ξ) (Real.log n) +
        𝓕 (fun ξ => h ξ * packet B γ η ξ) (-Real.log n))) ∧
    ‖weightPairing w (𝓕 fun ξ => h ξ * packet B γ η ξ) -
        h γ * weightPairing w (𝓕 (packet B γ η))‖ ≤
      2 * CB' * D * ∫ s, ‖𝓕 h s‖ * (η * |s| * (1 + η ^ 2 * s ^ 2)) := by
  set P := packet B γ η with hP
  have hPi : Integrable P := integrable_packet hBi γ hη0
  have hCB : 0 ≤ CB := by have := (norm_nonneg _).trans (hFB 0); simpa using this
  have hCB' : 0 ≤ CB' := by have := (norm_nonneg _).trans (hdB 0); simpa using this
  have hD0 : 0 ≤ D := by
    obtain ⟨-, hle⟩ := hD 1 one_pos le_rfl 0
    exact le_trans (tsum_nonneg fun n => mul_nonneg (hw n) (add_nonneg
      (cauchyProfile_nonneg zero_le_one 0 _) (cauchyProfile_nonneg zero_le_one 0 _))) hle
  -- the shifted windows
  set φ : ℝ → ℝ → ℂ := fun s u => (η : ℂ) * Complex.exp (-(2 * π * γ * u : ℝ) * I) *
    𝓕 B (η * (u - s)) with hφ
  have hFP : ∀ s u, 𝓕 P (u - s) = Complex.exp ((2 * π * s * γ : ℝ) * I) * φ s u := by
    intro s u
    rw [hP, fourier_packet B γ hη0, hφ]
    simp only
    rw [show (-((2 * π * γ * (u - s) : ℝ) : ℂ)) * I =
      ((2 * π * s * γ : ℝ) : ℂ) * I + -((2 * π * γ * u : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_add]
    ring
  have hφ0 : ∀ u, 𝓕 P u = φ 0 u := fun u => by
    have := hFP 0 u
    simpa using this
  have hφbound : ∀ s u, ‖φ s u‖ ≤ CB * cauchyProfile η s u := by
    intro s u
    simp only [hφ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη0]
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one]
    calc η * ‖𝓕 B (η * (u - s))‖ ≤ η * (CB / (1 + (η * (u - s)) ^ 2)) :=
          mul_le_mul_of_nonneg_left (hFB _) hη0.le
      _ = CB * cauchyProfile η s u := by simp only [cauchyProfile]; ring
  have hdiff : ∀ s u, ‖φ s u - φ 0 u‖ ≤
      2 * CB' * (η * |s| * (1 + η ^ 2 * s ^ 2)) * cauchyProfile η 0 u := by
    intro s u
    have h1 := norm_scaled_sub_le hdFB hdB hη0 s u
    have e : φ s u - φ 0 u = Complex.exp (-(2 * π * γ * u : ℝ) * I) *
        ((η : ℂ) * 𝓕 B (η * (u - s)) - (η : ℂ) * 𝓕 B (η * u)) := by
      simp only [hφ, sub_zero]; ring
    rw [e, norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact h1
  -- the pointwise identities
  set H : ℝ → ℂ := fun s => Complex.exp ((2 * π * s * γ : ℝ) * I) * 𝓕 h s with hH
  have hHn : ∀ s, ‖H s‖ = ‖𝓕 h s‖ := fun s => by
    simp only [hH, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hconv : ∀ u, 𝓕 (fun ξ => h ξ * P ξ) u = ∫ s, H s * φ s u := by
    intro u
    rw [fourier_mul_eq_integral hc hi hFi hPi]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [hH, hFP]; ring
  have hHi : Integrable H := by
    refine hFi.norm.mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      hFi.aestronglyMeasurable) (Eventually.of_forall fun s => ?_)
    rw [hHn]
  have hφc : ∀ u, Continuous fun s => φ s u := fun u => by
    simp only [hφ]
    exact continuous_const.mul ((continuous_fourier_integrable hBi).comp (by fun_prop))
  have hHφi : ∀ s₀ u, Integrable fun s => H s * (φ s u - φ s₀ u) := by
    intro s₀ u
    refine (hFi.norm.mul_const (2 * CB * η)).mono'
      (hHi.aestronglyMeasurable.mul ((hφc u).sub continuous_const).aestronglyMeasurable)
      (Eventually.of_forall fun s => ?_)
    rw [norm_mul, hHn]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h1 := hφbound s u
    have h2 := hφbound s₀ u
    have hcp : ∀ t, cauchyProfile η t u ≤ η := fun t => by
      simp only [cauchyProfile]
      rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (η * (u - t))]
    calc ‖φ s u - φ s₀ u‖ ≤ ‖φ s u‖ + ‖φ s₀ u‖ := norm_sub_le _ _
      _ ≤ CB * η + CB * η := add_le_add (h1.trans (mul_le_mul_of_nonneg_left (hcp s) hCB))
          (h2.trans (mul_le_mul_of_nonneg_left (hcp s₀) hCB))
      _ = 2 * CB * η := by ring
  have hHφi' : ∀ u, Integrable fun s => H s * φ s u := by
    intro u
    refine (hFi.norm.mul_const (CB * η)).mono'
      (hHi.aestronglyMeasurable.mul (hφc u).aestronglyMeasurable)
      (Eventually.of_forall fun s => ?_)
    rw [norm_mul, hHn]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (hφbound s u).trans (mul_le_mul_of_nonneg_left ?_ hCB)
    simp only [cauchyProfile]
    rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (η * (u - s))]
  have hid : ∀ u, 𝓕 (fun ξ => h ξ * P ξ) u - h γ * 𝓕 P u = ∫ s, H s * (φ s u - φ 0 u) := by
    intro u
    rw [hconv, hφ0, eq_integral_fourier hc hi hFi γ, ← integral_mul_const,
      ← integral_sub (hHφi' u) ((hHi.mul_const (φ 0 u)))]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [hH]; ring
  -- nonnegative majorants
  set f₁ : ℕ → ℝ → ℝ := fun n s => w n * (‖𝓕 h s‖ * (CB *
    (cauchyProfile η s (Real.log n) + cauchyProfile η s (-Real.log n)))) with hf₁
  set f₂ : ℕ → ℝ → ℝ := fun n s => w n * (‖𝓕 h s‖ *
    (2 * CB' * (η * |s| * (1 + η ^ 2 * s ^ 2)) *
      (cauchyProfile η 0 (Real.log n) + cauchyProfile η 0 (-Real.log n)))) with hf₂
  have hFc : Continuous fun s => ‖𝓕 h s‖ := (continuous_fourier_integrable hi).norm
  have hFhc := continuous_fourier_integrable hi
  obtain ⟨hi₁, hs₁, hle₁⟩ := summable_integral_le_of_tsum_le (f := f₁)
    (G := fun s => ‖𝓕 h s‖ * (CB * D))
    (fun n s => mul_nonneg (hw n) (mul_nonneg (norm_nonneg _) (mul_nonneg hCB
      (add_nonneg (cauchyProfile_nonneg hη0.le _ _) (cauchyProfile_nonneg hη0.le _ _)))))
    (fun n => (continuous_const.mul (hFc.mul (continuous_const.mul
      ((continuous_cauchyProfile_center η _).add (continuous_cauchyProfile_center η _))))).measurable)
    (hFi.norm.mul_const _)
    (fun s => by
      obtain ⟨hsm, -⟩ := hD η hη0 hη1 s
      exact (hsm.mul_left (‖𝓕 h s‖ * CB)).congr fun n => by simp only [hf₁]; ring)
    (fun s => by
      obtain ⟨hsm, hle⟩ := hD η hη0 hη1 s
      calc ∑' n, f₁ n s = ‖𝓕 h s‖ * CB * ∑' n : ℕ, w n *
            (cauchyProfile η s (Real.log n) + cauchyProfile η s (-Real.log n)) := by
            rw [← tsum_mul_left]; exact tsum_congr fun n => by simp only [hf₁]; ring
        _ ≤ ‖𝓕 h s‖ * CB * D := mul_le_mul_of_nonneg_left hle (by positivity)
        _ = ‖𝓕 h s‖ * (CB * D) := by ring)
  obtain ⟨hsm0, hle0⟩ := hD η hη0 hη1 0
  have hwt : Integrable fun s => ‖𝓕 h s‖ * (2 * CB' * (η * |s| * (1 + η ^ 2 * s ^ 2)) * D) := by
    refine (hFm.mul_const (2 * CB' * D)).mono' (by fun_prop) (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hη2 : η ^ 2 ≤ 1 := by nlinarith
    have h1 : η * |s| * (1 + η ^ 2 * s ^ 2) ≤ |s| * (1 + s ^ 2) := by
      have : η * |s| ≤ |s| := by nlinarith [abs_nonneg s]
      have : 1 + η ^ 2 * s ^ 2 ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg s]
      exact mul_le_mul (by assumption) this (by positivity) (abs_nonneg s)
    calc ‖𝓕 h s‖ * (2 * CB' * (η * |s| * (1 + η ^ 2 * s ^ 2)) * D)
        = (‖𝓕 h s‖ * (η * |s| * (1 + η ^ 2 * s ^ 2))) * (2 * CB' * D) := by ring
      _ ≤ (‖𝓕 h s‖ * (|s| * (1 + s ^ 2))) * (2 * CB' * D) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
            (by positivity)
  obtain ⟨hi₂, hs₂, hle₂⟩ := summable_integral_le_of_tsum_le (f := f₂)
    (G := fun s => ‖𝓕 h s‖ * (2 * CB' * (η * |s| * (1 + η ^ 2 * s ^ 2)) * D))
    (fun n s => mul_nonneg (hw n) (mul_nonneg (norm_nonneg _) (mul_nonneg (by positivity)
      (add_nonneg (cauchyProfile_nonneg hη0.le _ _) (cauchyProfile_nonneg hη0.le _ _)))))
    (fun n => Continuous.measurable (by simp only [hf₂]; fun_prop))
    hwt
    (fun s => (hsm0.mul_left (‖𝓕 h s‖ * (2 * CB' * (η * |s| * (1 + η ^ 2 * s ^ 2))))).congr
      fun n => by simp only [hf₂]; ring)
    (fun s => by
      calc ∑' n, f₂ n s = ‖𝓕 h s‖ * (2 * CB' * (η * |s| * (1 + η ^ 2 * s ^ 2))) *
            ∑' n : ℕ, w n *
              (cauchyProfile η 0 (Real.log n) + cauchyProfile η 0 (-Real.log n)) := by
            rw [← tsum_mul_left]; exact tsum_congr fun n => by simp only [hf₂]; ring
        _ ≤ ‖𝓕 h s‖ * (2 * CB' * (η * |s| * (1 + η ^ 2 * s ^ 2))) * D :=
            mul_le_mul_of_nonneg_left hle0 (by positivity)
        _ = _ := by ring)
  -- summability of the pairing with the modulated packet
  have hb₁ : ∀ n : ℕ, ‖(w n : ℂ) * (𝓕 (fun ξ => h ξ * P ξ) (Real.log n) +
      𝓕 (fun ξ => h ξ * P ξ) (-Real.log n))‖ ≤ ∫ s, f₁ n s := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw n), hconv, hconv,
      ← integral_add (hHφi' _) (hHφi' _)]
    refine (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (hw n)).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun s => mul_nonneg (hw n)
      (norm_nonneg _)) (hi₁ n) (Eventually.of_forall fun s => ?_)
    dsimp only
    rw [← mul_add, norm_mul, hHn]
    have := norm_add_le (φ s (Real.log n)) (φ s (-Real.log n))
    have := add_le_add (hφbound s (Real.log n)) (hφbound s (-Real.log n))
    simp only [hf₁]
    have hw' := hw n
    have hn := norm_nonneg (𝓕 h s)
    calc w n * (‖𝓕 h s‖ * ‖φ s (Real.log n) + φ s (-Real.log n)‖)
        ≤ w n * (‖𝓕 h s‖ * (CB * cauchyProfile η s (Real.log n) +
            CB * cauchyProfile η s (-Real.log n))) := by gcongr; linarith
      _ = _ := by ring
  have hsum₁ : Summable (fun n : ℕ => (w n : ℂ) * (𝓕 (fun ξ => h ξ * P ξ) (Real.log n) +
      𝓕 (fun ξ => h ξ * P ξ) (-Real.log n))) := Summable.of_norm_bounded hs₁ hb₁
  refine ⟨hsum₁, ?_⟩
  -- the difference as a single series
  have hsum₀ := (summable_weightPairing_of_profile hw hD hη0 hη1 (s := 0) (C := CB)
    (φ := 𝓕 P) (fun u => by rw [hφ0]; exact hφbound 0 u)).1
  have hdiffsum : weightPairing w (𝓕 fun ξ => h ξ * P ξ) - h γ * weightPairing w (𝓕 P) =
      ∑' n : ℕ, (w n : ℂ) * ((𝓕 (fun ξ => h ξ * P ξ) (Real.log n) - h γ * 𝓕 P (Real.log n)) +
        (𝓕 (fun ξ => h ξ * P ξ) (-Real.log n) - h γ * 𝓕 P (-Real.log n))) := by
    unfold weightPairing
    rw [← tsum_mul_left, ← Summable.tsum_sub hsum₁ (hsum₀.mul_left _)]
    exact tsum_congr fun n => by ring
  have hb₂ : ∀ n : ℕ, ‖(w n : ℂ) * ((𝓕 (fun ξ => h ξ * P ξ) (Real.log n) -
      h γ * 𝓕 P (Real.log n)) + (𝓕 (fun ξ => h ξ * P ξ) (-Real.log n) -
        h γ * 𝓕 P (-Real.log n)))‖ ≤ ∫ s, f₂ n s := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw n), hid, hid,
      ← integral_add (hHφi 0 _) (hHφi 0 _)]
    refine (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (hw n)).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun s => mul_nonneg (hw n)
      (norm_nonneg _)) (hi₂ n) (Eventually.of_forall fun s => ?_)
    · dsimp only
      rw [← mul_add, norm_mul, hHn]
      have := norm_add_le (φ s (Real.log n) - φ 0 (Real.log n))
        (φ s (-Real.log n) - φ 0 (-Real.log n))
      have := add_le_add (hdiff s (Real.log n)) (hdiff s (-Real.log n))
      simp only [hf₂]
      have hw' := hw n
      have hn := norm_nonneg (𝓕 h s)
      calc w n * (‖𝓕 h s‖ * ‖φ s (Real.log n) - φ 0 (Real.log n) +
            (φ s (-Real.log n) - φ 0 (-Real.log n))‖)
          ≤ w n * (‖𝓕 h s‖ * (2 * CB' * (η * |s| * (1 + η ^ 2 * s ^ 2)) *
              cauchyProfile η 0 (Real.log n) + 2 * CB' * (η * |s| * (1 + η ^ 2 * s ^ 2)) *
              cauchyProfile η 0 (-Real.log n))) := by gcongr; linarith
        _ = _ := by ring
  rw [hdiffsum]
  calc _ ≤ ∑' n, ∫ s, f₂ n s := tsum_of_norm_bounded hs₂.hasSum hb₂
    _ ≤ ∫ s, ‖𝓕 h s‖ * (2 * CB' * (η * |s| * (1 + η ^ 2 * s ^ 2)) * D) := hle₂
    _ = 2 * CB' * D * ∫ s, ‖𝓕 h s‖ * (η * |s| * (1 + η ^ 2 * s ^ 2)) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun s => by ring)

end

end RHTower.WeilExcess
