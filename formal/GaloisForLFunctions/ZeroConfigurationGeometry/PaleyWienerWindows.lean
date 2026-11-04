import GaloisForLFunctions.ZeroConfigurationGeometry.BlindWindowsForPerturbedLattices
import GaloisForLFunctions.HTGeometry.EvenEntireCompactSource

/-!
# Paley–Wiener windows

Kernel design is the vanishing problem for entire functions of exponential type.

* **Converse Paley–Wiener** (`exists_smooth_source_of_entire`). An entire `Q` with
  `‖Q(z)‖ ≤ C e^{A|Im z|}/(1 + (Re z)²)` and rapid decay on the real line is the transform of a
  smooth window supported in `[−A, A]`. The support comes from the contour shift of
  `HTGeometry.angularInverse_zero_of_type_lt`, applied to `Q` and to `Q(−·)`; smoothness from the
  real moments; the identity from Fourier inversion on `ℝ` and the identity theorem.
* **Windows from entire functions** (`exists_window_of_entire`). If `F` is entire with
  `‖F(z)‖ ≤ C(1 + |z|)^N e^{τ|Im z|}`, then for every `r > τ` and every `z₀` there is a window of
  aperture `r` whose transform is `F b̂` with `b̂(z₀) = 1`: the bump's transform decays faster than
  any power on every horizontal line (`exists_pow_mul_norm_paperFT_le_exp`).
* **The equivalence** (`blind_windows_iff_entire`). A set `Λ` has, at every aperture above `τ`, a
  window blind to it that sees `z₀`, if and only if, at every type above `τ`, some entire function
  of polynomial growth on horizontal lines vanishes on `Λ` and not at `z₀`. The forward direction
  is the transform of the window itself.

So the camera's separating power against a real configuration is a statement about entire
functions of exponential type vanishing on it: the completeness radius of the exponentials on the
configuration. Lattices, their bounded perturbations, finite unions and zero sets of density
transforms are the cases solved explicitly in this programme.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real FourierTransform ContDiff

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23

theorem angularInverse_comp_neg (Q : ℂ → ℂ) (u : ℝ) :
    HTGeometry.angularInverse (fun z => Q (-z)) u = HTGeometry.angularInverse Q (-u) := by
  unfold HTGeometry.angularInverse
  conv_lhs => rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Complex.ofReal_neg, neg_neg]
  congr 2
  ring

/-- **Converse Paley–Wiener.** -/
theorem exists_smooth_source_of_entire {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q) {C A : ℝ}
    (hC : 0 ≤ C) (hb : ∀ z, ‖Q z‖ ≤ C * Real.exp (A * |z.im|) * (1 + z.re ^ 2)⁻¹)
    (hd : ∀ n : ℕ, ∃ M : ℝ, ∀ x : ℝ, ‖Q x‖ * (1 + |x|) ^ n ≤ M) :
    ∃ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ tsupport f ⊆ Icc (-A) A ∧ ∀ z, paperFT f z = Q z := by
  set Q' : ℂ → ℂ := fun z => Q (-z) with hQ'
  have hQ'd : Differentiable ℂ Q' := hQ.comp differentiable_neg
  have hb' : ∀ z, ‖Q' z‖ ≤ C * Real.exp (A * |z.im|) * (1 + z.re ^ 2)⁻¹ := fun z => by
    simpa [hQ'] using hb (-z)
  have hd' : ∀ n : ℕ, ∃ M : ℝ, ∀ x : ℝ, ‖Q' x‖ * (1 + |x|) ^ n ≤ M := fun n => by
    obtain ⟨M, hM⟩ := hd n
    exact ⟨M, fun x => by simpa [hQ'] using hM (-x)⟩
  set f := HTGeometry.compactInverse Q' with hf
  have hzero : ∀ u, A < |u| → HTGeometry.angularInverse Q' u = 0 := by
    intro u hu
    rcases lt_abs.mp hu with h | h
    · exact HTGeometry.angularInverse_zero_of_type_lt hQ'd hC hb' h
    · rw [angularInverse_comp_neg]
      exact HTGeometry.angularInverse_zero_of_type_lt hQ hC hb h
  have hfs : tsupport f ⊆ Icc (-A) A := closure_minimal (fun u hu => by
    by_contra hout
    apply hu
    simp only [hf, HTGeometry.compactInverse]
    rw [hzero u ?_, smul_zero]
    by_contra hle
    push Not at hle
    exact hout (abs_le.mp hle)) isClosed_Icc
  have hfc : ContDiff ℝ ∞ f := (HTGeometry.angularInverse_smooth hQ'd.continuous hd').const_smul _
  have hfcs : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs
  set V := fun x : ℝ => Q' ((2 * π * x : ℝ) : ℂ) with hV
  have hQr : Continuous fun x : ℝ => Q' x := hQ'd.continuous.comp Complex.continuous_ofReal
  have hQi : Integrable fun x : ℝ => Q' x := (integrable_norm_iff hQr.aestronglyMeasurable).mp
    (by simpa only [pow_zero, one_mul] using
      HTGeometry.integrable_moments_of_real_decay hQ'd.continuous hd' 0)
  have hVi : Integrable V := hQi.comp_mul_left' (by positivity)
  have hVc : Continuous V := hQ'd.continuous.comp (by fun_prop)
  have hfi : Integrable f := hfc.continuous.integrable_of_hasCompactSupport hfcs
  have hFourier : 𝓕 V = fun x => f (-x) := by
    funext x
    rw [hf, HTGeometry.compactInverse_eq_fourierInv, Real.fourierInv_eq_fourier_neg, neg_neg]
  have hFi : Integrable (𝓕 V) := by rw [hFourier]; exact hfi.comp_neg
  have hfinv : 𝓕 f = V := by
    rw [hf, HTGeometry.compactInverse_eq_fourierInv]
    exact hVc.fourier_fourierInv_eq hVi hFi
  have hreal : ∀ x : ℝ, paperFT f x = Q x := by
    intro x
    rw [Zeta23.paperFT_ofReal_eq_fourier, hfinv]
    change Q' ((2 * π * (-x / (2 * π)) : ℝ) : ℂ) = Q x
    rw [show 2 * π * (-x / (2 * π)) = -x by field_simp]
    simp [hQ']
  refine ⟨f, by exact_mod_cast hfc, hfs, fun z => ?_⟩
  apply sub_eq_zero.mp
  have hft : Differentiable ℂ (paperFT f) :=
    _root_.RHTower.EvenSector.differentiable_paperFT_of_compact hfc.continuous hfcs
  exact HTGeometry.entire_eq_zero_of_vanishing_on_real_interval (hft.sub hQ) (t₀ := 0) (r := 1)
    (by norm_num) (fun x _ => sub_eq_zero.mpr (hreal x)) z

theorem tsupport_iterate_deriv_subset (b : ℝ → ℂ) (j : ℕ) :
    tsupport (deriv^[j] b) ⊆ tsupport b := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact tsupport_deriv_subset.trans ih

/-- **The transform of a bump decays faster than any power on every horizontal line.** -/
theorem exists_pow_mul_norm_paperFT_le_exp {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) {r₀ : ℝ}
    (hr₀ : 0 ≤ r₀) (hbs : tsupport b ⊆ Icc (-r₀) r₀) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, (1 + ‖z‖) ^ m * ‖paperFT b z‖ ≤ C * Real.exp (r₀ * |z.im|) := by
  have hbc : HasCompactSupport b := isCompact_Icc.of_isClosed_subset (isClosed_tsupport b) hbs
  obtain ⟨hdm, hdmc, hft⟩ := iterate_deriv_props hb hbc m
  obtain ⟨M0, hM0⟩ := hb.continuous.bounded_above_of_compact_support hbc
  obtain ⟨Mm, hMm⟩ := hdm.continuous.bounded_above_of_compact_support hdmc
  have hM0' : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0)
  have hMm' : 0 ≤ Mm := (norm_nonneg _).trans (hMm 0)
  refine ⟨2 ^ m * (M0 + Mm) * (2 * r₀), by positivity, fun z => ?_⟩
  have h0 := norm_paperFT_le_of_tsupport hr₀ hbs hM0 z
  have hm := norm_paperFT_le_of_tsupport hr₀ ((tsupport_iterate_deriv_subset b m).trans hbs) hMm z
  rw [hft, norm_mul, norm_pow, norm_neg, norm_mul, Complex.norm_I, one_mul] at hm
  have hpow : (1 + ‖z‖) ^ m ≤ 2 ^ m * (1 + ‖z‖ ^ m) := by
    rcases le_total ‖z‖ 1 with hx | hx
    · calc (1 + ‖z‖) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
        _ ≤ 2 ^ m * (1 + ‖z‖ ^ m) := le_mul_of_one_le_right (by positivity)
            (by linarith [pow_nonneg (norm_nonneg z) m])
    · calc (1 + ‖z‖) ^ m ≤ (2 * ‖z‖) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
        _ = 2 ^ m * ‖z‖ ^ m := mul_pow _ _ _
        _ ≤ 2 ^ m * (1 + ‖z‖ ^ m) := by nlinarith [pow_nonneg (two_pos.le : (0 : ℝ) ≤ 2) m]
  calc (1 + ‖z‖) ^ m * ‖paperFT b z‖ ≤ 2 ^ m * (1 + ‖z‖ ^ m) * ‖paperFT b z‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = 2 ^ m * (‖paperFT b z‖ + ‖z‖ ^ m * ‖paperFT b z‖) := by ring
    _ ≤ 2 ^ m * (M0 * Real.exp (r₀ * |z.im|) * (2 * r₀) + Mm * Real.exp (r₀ * |z.im|) * (2 * r₀)) :=
        by gcongr
    _ = 2 ^ m * (M0 + Mm) * (2 * r₀) * Real.exp (r₀ * |z.im|) := by ring

/-- **Windows from entire functions of exponential type.** -/
theorem exists_window_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) {C τ : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (hFb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ N * Real.exp (τ * |z.im|))
    {r : ℝ} (hr : τ < r) (z₀ : ℂ) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧ ∃ g : ℂ → ℂ, g z₀ = 1 ∧ ∀ z, paperFT f z = F z * g z := by
  set ε := r - τ with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨b, hb, hbc, hbs, hb1⟩ := exists_smooth_window_paperFT_eq_one hε0 z₀
  set Q : ℂ → ℂ := fun z => F z * paperFT b z with hQ
  have hbd : Differentiable ℂ (paperFT b) :=
    _root_.RHTower.EvenSector.differentiable_paperFT_of_compact hb.continuous hbc
  obtain ⟨Cb, hCb0, hCb⟩ := exists_pow_mul_norm_paperFT_le_exp hb hε0.le hbs (N + 2)
  have hQb : ∀ z, ‖Q z‖ ≤ C * Cb * Real.exp (r * |z.im|) * (1 + z.re ^ 2)⁻¹ := by
    intro z
    have h1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have hre : 1 + z.re ^ 2 ≤ (1 + ‖z‖) ^ 2 := by
      have := Complex.abs_re_le_norm z
      nlinarith [sq_abs z.re, abs_nonneg z.re, norm_nonneg z]
    have hbz := hCb z
    have hexp : Real.exp (τ * |z.im|) * Real.exp (ε * |z.im|) = Real.exp (r * |z.im|) := by
      rw [← Real.exp_add, hε]; ring_nf
    rw [hQ, norm_mul]
    calc ‖F z‖ * ‖paperFT b z‖ ≤ C * (1 + ‖z‖) ^ N * Real.exp (τ * |z.im|) * ‖paperFT b z‖ :=
          mul_le_mul_of_nonneg_right (hFb z) (norm_nonneg _)
      _ = C * Real.exp (τ * |z.im|) * ((1 + ‖z‖) ^ (N + 2) * ‖paperFT b z‖) / (1 + ‖z‖) ^ 2 := by
          field_simp; ring
      _ ≤ C * Real.exp (τ * |z.im|) * (Cb * Real.exp (ε * |z.im|)) / (1 + ‖z‖) ^ 2 := by gcongr
      _ = C * Cb * Real.exp (r * |z.im|) / (1 + ‖z‖) ^ 2 := by rw [← hexp]; ring
      _ ≤ C * Cb * Real.exp (r * |z.im|) / (1 + z.re ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hre
      _ = _ := by rw [div_eq_mul_inv]
  have hQd : ∀ n : ℕ, ∃ M : ℝ, ∀ x : ℝ, ‖Q x‖ * (1 + |x|) ^ n ≤ M := by
    intro n
    obtain ⟨Cn, hCn0, hCn⟩ := exists_pow_mul_norm_paperFT_le hb hbc (N + n)
    refine ⟨C * Cn, fun x => ?_⟩
    have hnx : ‖(x : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have hFx := hFb x
    rw [hnx, Complex.ofReal_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at hFx
    rw [hQ, norm_mul]
    calc ‖F x‖ * ‖paperFT b x‖ * (1 + |x|) ^ n ≤ C * (1 + |x|) ^ N * ‖paperFT b x‖ * (1 + |x|) ^ n := by
          gcongr
      _ = C * ((1 + |x|) ^ (N + n) * ‖paperFT b x‖) := by ring
      _ ≤ C * Cn := by gcongr; exact hCn x
  have hQdiff : Differentiable ℂ Q := hF.mul hbd
  obtain ⟨f, hf, hfs, hft⟩ := exists_smooth_source_of_entire hQdiff (by positivity) hQb hQd
  exact ⟨f, ⟨hf.of_le (by norm_cast), hfs⟩, paperFT b, hb1, hft⟩

/-- **Blind windows and entire functions.** For a set `Λ ⊂ ℂ`, a point `z₀` and `τ ≥ 0`: every
aperture above `τ` carries a window blind to `Λ` that sees `z₀` if and only if every type above `τ`
carries an entire function of polynomial growth on horizontal lines, vanishing on `Λ` and not at
`z₀`. -/
theorem blind_windows_iff_entire (Λ : Set ℂ) (z₀ : ℂ) {τ : ℝ} (hτ : 0 ≤ τ) :
    (∀ r, τ < r → ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ μ ∈ Λ, paperFT f μ = 0) ∧
        paperFT f z₀ ≠ 0) ↔
      (∀ r, τ < r → ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
        (∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ N * Real.exp (r * |z.im|)) ∧
        (∀ μ ∈ Λ, F μ = 0) ∧ F z₀ ≠ 0) := by
  constructor
  · intro h r hr
    obtain ⟨f, hf, hfΛ, hf0⟩ := h r hr
    have hfc := hf.hasCompactSupport
    obtain ⟨M, hM⟩ := hf.1.continuous.bounded_above_of_compact_support hfc
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hr0 : 0 ≤ r := by linarith
    refine ⟨paperFT f, _root_.RHTower.EvenSector.differentiable_paperFT_of_compact
      hf.1.continuous hfc, ⟨M * (2 * r), 0, by positivity, fun z => ?_⟩, hfΛ, hf0⟩
    have := norm_paperFT_le_of_tsupport hr0 hf.2 hM z
    rw [pow_zero, mul_one]
    linarith
  · intro h r hr
    set r' := (τ + r) / 2 with hr'
    obtain ⟨F, hF, ⟨C, N, hC, hFb⟩, hFΛ, hF0⟩ := h r' (by rw [hr']; linarith)
    obtain ⟨f, hf, g, hg1, hfg⟩ := exists_window_of_entire hF hC hFb
      (show r' < r by rw [hr']; linarith) z₀
    refine ⟨f, hf, fun μ hμ => by rw [hfg, hFΛ μ hμ, zero_mul], ?_⟩
    rw [hfg, hg1, mul_one]
    exact hF0

end GaloisForLFunctions.ZeroConfigurationGeometry
