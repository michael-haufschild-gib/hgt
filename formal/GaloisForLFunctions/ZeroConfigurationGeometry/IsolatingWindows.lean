import GaloisForLFunctions.ZeroConfigurationGeometry.BlindWindowsAtTheDensityAperture
import GaloisForLFunctions.ZeroConfigurationGeometry.DifferentialWindowsInvertTheCamera

/-!
# Isolating windows

The differential window `g ↦ g' + iκg` multiplies the transform by `−i(w − κ)` without enlarging
the support (`DifferentialWindowsInvertTheCamera`). This module inverts it at transform zeros.

* **Division** (`exists_window_div`). If `f̂(κ) = 0`, then `g(u) = e^{−iκu} ∫_{−r}^{u} e^{iκs} f(s) ds`
  solves `g' + iκg = f`. It vanishes below `−r`, and above `r` it equals `e^{−iκu} f̂(κ) = 0`. So `g`
  is a window of the same aperture with `f̂(w) = −i(w − κ) ĝ(w)`.
* **Isolation** (`exists_isolating_window`). A window blind to a configuration `Λ` with a simple
  transform zero at `κ ∈ Λ` divides into a window of the same aperture that is blind to `Λ \ {κ}`
  and sees `κ`: differentiating `f̂ = −i(w − κ)ĝ` at `κ` gives `ĝ(κ) = i f̂'(κ) ≠ 0`.
* **Isolating a lattice point** (`exists_window_isolating_lattice_point`). For every aperture
  `r > π/h` and every `k₀`, some window sees `k₀h` and no other point of `hℤ`.

So a single camera of the density aperture reads one chosen point of a lattice and nothing else
of it. Blindness and isolation cost no aperture beyond the density: division and multiplication
by linear factors keep the support.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23

theorem eq_zero_of_not_mem_Icc_of_tsupport {f : ℝ → ℂ} {r : ℝ} (hf : tsupport f ⊆ Icc (-r) r)
    {u : ℝ} (hu : u ∉ Icc (-r) r) : f u = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hu (hf h)

/-- A continuous window supported in `[−r, r]` vanishes wherever `|u| ≥ r`. -/
theorem eq_zero_of_le_abs {f : ℝ → ℂ} {r : ℝ} (hc : Continuous f) (hf : tsupport f ⊆ Icc (-r) r)
    {u : ℝ} (hu : r ≤ |u|) : f u = 0 := by
  have hclosed : IsClosed {u : ℝ | f u = 0} := isClosed_eq hc continuous_const
  rcases lt_or_eq_of_le hu with h | h
  · exact eq_zero_of_not_mem_Icc_of_tsupport hf fun hm => by
      have := abs_le.mpr hm; linarith
  · have h1 : Ioi r ⊆ {u | f u = 0} := fun x hx =>
      eq_zero_of_not_mem_Icc_of_tsupport hf fun hm => by linarith [hm.2, Set.mem_Ioi.mp hx]
    have h2 : Iio (-r) ⊆ {u | f u = 0} := fun x hx =>
      eq_zero_of_not_mem_Icc_of_tsupport hf fun hm => by linarith [hm.1, Set.mem_Iio.mp hx]
    rcases abs_eq (h ▸ abs_nonneg u) |>.mp h.symm with hu' | hu'
    · have := hclosed.closure_subset_iff.mpr h1
      rw [closure_Ioi] at this
      exact this (by rw [hu']; exact Set.self_mem_Ici)
    · have := hclosed.closure_subset_iff.mpr h2
      rw [closure_Iio] at this
      exact this (by rw [hu']; exact Set.self_mem_Iic)

/-- The quotient window `g(u) = e^{−iκu} ∫_{−r}^{u} e^{iκs} f(s) ds`, solving `g' + iκg = f`. -/
def divWindow (r : ℝ) (κ : ℂ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  cexp (-(I * κ * u)) * ∫ s in (-r)..u, cexp (I * κ * s) * f s

theorem contDiff_cexp_mul (c : ℂ) : ContDiff ℝ (⊤ : ℕ∞) fun s : ℝ => cexp (c * s) :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem hasDerivAt_divWindow {f : ℝ → ℂ} (hfc : Continuous f) (r : ℝ) (κ : ℂ) (u : ℝ) :
    HasDerivAt (divWindow r κ f) (-(I * κ) * divWindow r κ f u + f u) u := by
  have hhc : Continuous fun s : ℝ => cexp (I * κ * s) * f s :=
    (contDiff_cexp_mul _).continuous.mul hfc
  have hFd := intervalIntegral.integral_hasDerivAt_right (a := -r) (hhc.intervalIntegrable _ u)
    (hhc.stronglyMeasurableAtFilter _ _) hhc.continuousAt
  have h1 : HasDerivAt (fun u : ℝ => cexp (-(I * κ * u))) (cexp (-(I * κ * u)) * (-(I * κ))) u := by
    have := (((hasDerivAt_id (u : ℂ)).const_mul (I * κ)).neg.cexp).comp_ofReal
    refine this.congr_deriv ?_
    simp
  refine (h1.mul hFd).congr_deriv ?_
  simp only [divWindow]
  rw [show cexp (-(I * κ * u)) * (cexp (I * κ * u) * f u) =
    (cexp (-(I * κ * u)) * cexp (I * κ * u)) * f u by ring, ← Complex.exp_add,
    show -(I * κ * u) + I * κ * u = 0 by ring, Complex.exp_zero, one_mul]
  ring

theorem deriv_divWindow {f : ℝ → ℂ} (hfc : Continuous f) (r : ℝ) (κ : ℂ) :
    deriv (divWindow r κ f) = fun u => -(I * κ) * divWindow r κ f u + f u :=
  funext fun u => (hasDerivAt_divWindow hfc r κ u).deriv

/-- The quotient window is as smooth as `f`. -/
theorem contDiff_divWindow {f : ℝ → ℂ} (r : ℝ) (κ : ℂ) :
    ∀ n : ℕ, ContDiff ℝ n f → ContDiff ℝ n (divWindow r κ f) := by
  intro n
  induction n with
  | zero =>
    intro hf
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun u =>
      (hasDerivAt_divWindow (contDiff_zero.mp hf) r κ u).continuousAt)
  | succ n ih =>
    intro hf
    have hfc : Continuous f := hf.continuous
    have hfn : ContDiff ℝ n f := hf.of_le (by norm_cast; omega)
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast]
    refine contDiff_succ_iff_deriv.mpr ⟨fun u => (hasDerivAt_divWindow hfc r κ u).differentiableAt,
      by simp, ?_⟩
    rw [deriv_divWindow hfc]
    exact (contDiff_const.mul (ih hfn)).add hfn

theorem contDiff_top_divWindow {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (r : ℝ) (κ : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (divWindow r κ f) :=
  contDiff_infty.mpr fun n => contDiff_divWindow r κ n (hf.of_le (by exact_mod_cast le_top))

/-- Above and below the support the quotient window vanishes when `f̂(κ) = 0`. -/
theorem divWindow_eq_zero {r : ℝ} {f : ℝ → ℂ} (hfc : Continuous f) (hfs : tsupport f ⊆ Icc (-r) r)
    (hr : 0 ≤ r) {κ : ℂ} (hκ : paperFT f κ = 0) {u : ℝ} (hu : r < |u|) : divWindow r κ f u = 0 := by
  have hhc : Continuous fun s : ℝ => cexp (I * κ * s) * f s :=
    (contDiff_cexp_mul _).continuous.mul hfc
  have hhz : ∀ s, r ≤ |s| → cexp (I * κ * s) * f s = 0 := fun s hs => by
    rw [eq_zero_of_le_abs hfc hfs hs, mul_zero]
  simp only [divWindow, mul_eq_zero]
  right
  rcases lt_abs.mp hu with hpos | hneg
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := r) (hhc.intervalIntegrable _ _)
      (hhc.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_congr (a := r) (b := u) (g := fun _ => (0 : ℂ))
      fun s hs => hhz s ?_, intervalIntegral.integral_zero, add_zero]
    · rw [intervalIntegral.integral_of_le (by linarith),
        setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => hhz s ?_]
      · rw [← hκ, paperFT_def]
        exact integral_congr_ae (Eventually.of_forall fun s => by ring)
      · rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hs
        rcases hs with hs | hs
        · exact le_trans (by linarith) (neg_le_abs s)
        · exact le_trans hs.le (le_abs_self s)
    · rw [Set.uIcc_of_le hpos.le] at hs
      exact le_trans hs.1 (le_abs_self s)
  · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun s hs => hhz s ?_,
      intervalIntegral.integral_zero]
    rw [Set.uIcc_of_ge (by linarith : u ≤ -r)] at hs
    exact le_trans (by linarith [hs.2]) (neg_le_abs s)

theorem tsupport_divWindow_subset {r : ℝ} {f : ℝ → ℂ} (hfc : Continuous f)
    (hfs : tsupport f ⊆ Icc (-r) r) (hr : 0 ≤ r) {κ : ℂ} (hκ : paperFT f κ = 0) :
    tsupport (divWindow r κ f) ⊆ Icc (-r) r := closure_minimal (fun u hu => by
  by_contra hout
  apply hu
  refine divWindow_eq_zero hfc hfs hr hκ ?_
  by_contra hle
  push Not at hle
  exact hout (abs_le.mp hle)) isClosed_Icc

/-- The transform of the quotient window: `f̂(w) = −i(w − κ) ĝ(w)`. -/
theorem paperFT_divWindow {r : ℝ} {f : ℝ → ℂ} (hf1 : ContDiff ℝ 1 f)
    (hfs : tsupport f ⊆ Icc (-r) r) (hr : 0 ≤ r) {κ : ℂ} (hκ : paperFT f κ = 0) (w : ℂ) :
    paperFT f w = -I * (w - κ) * paperFT (divWindow r κ f) w := by
  have hfc := hf1.continuous
  have hg1 : ContDiff ℝ 1 (divWindow r κ f) := by exact_mod_cast contDiff_divWindow r κ 1 hf1
  have hgc : HasCompactSupport (divWindow r κ f) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (tsupport_divWindow_subset hfc hfs hr hκ)
  have hfeq : f = fun u => deriv (divWindow r κ f) u + (I * κ) * divWindow r κ f u := by
    funext u
    rw [deriv_divWindow hfc]
    ring
  rw [hfeq, paperFT_add_smul (hg1.continuous_deriv le_rfl) hgc.deriv hg1.continuous hgc,
    _root_.RHTower.EvenSector.paperFT_deriv_of_compact hg1 hgc]
  ring

/-- **Division at a zero of the transform.** -/
theorem exists_window_div {r : ℝ} {f : ℝ → ℂ} (hf : ApertureWindow r f) {κ : ℂ}
    (hκ : paperFT f κ = 0) :
    ∃ g : ℝ → ℂ, ApertureWindow r g ∧ ∀ w, paperFT f w = -I * (w - κ) * paperFT g w := by
  have hfc : Continuous f := hf.1.continuous
  rcases lt_or_ge r 0 with hr | hr
  · -- an empty aperture: `f = 0`
    have hf0 : f = 0 := funext fun u =>
      eq_zero_of_not_mem_Icc_of_tsupport hf.2 fun hm => by linarith [hm.1, hm.2]
    refine ⟨0, ⟨contDiff_const, by simp⟩, fun w => ?_⟩
    rw [hf0, paperFT_def]
    simp
  refine ⟨divWindow r κ f, ⟨by exact_mod_cast contDiff_divWindow r κ 2 hf.1,
    tsupport_divWindow_subset hfc hf.2 hr hκ⟩, paperFT_divWindow (hf.1.of_le (by norm_num)) hf.2 hr hκ⟩

/-- **Smooth division.** For a smooth window the quotient window is smooth. -/
theorem exists_smooth_window_div {r : ℝ} (hr : 0 ≤ r) {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfs : tsupport f ⊆ Icc (-r) r) {κ : ℂ} (hκ : paperFT f κ = 0) :
    ∃ g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧ tsupport g ⊆ Icc (-r) r ∧
      ∀ w, paperFT f w = -I * (w - κ) * paperFT g w :=
  ⟨divWindow r κ f, contDiff_top_divWindow hf r κ,
    tsupport_divWindow_subset hf.continuous hfs hr hκ,
    paperFT_divWindow (hf.of_le (by exact_mod_cast le_top)) hfs hr hκ⟩

/-- **Isolating windows.** A window blind to `Λ` with a simple transform zero at `κ ∈ Λ` divides
into a window of the same aperture that is blind to `Λ \ {κ}` and sees `κ`. -/
theorem exists_isolating_window {r : ℝ} {f : ℝ → ℂ} (hf : ApertureWindow r f) {Λ : Set ℂ}
    (hΛ : ∀ μ ∈ Λ, paperFT f μ = 0) {κ : ℂ} (hκ : κ ∈ Λ) (hsimple : deriv (paperFT f) κ ≠ 0) :
    ∃ g : ℝ → ℂ, ApertureWindow r g ∧ (∀ μ ∈ Λ, μ ≠ κ → paperFT g μ = 0) ∧ paperFT g κ ≠ 0 := by
  obtain ⟨g, hg, hfg⟩ := exists_window_div hf (hΛ κ hκ)
  refine ⟨g, hg, fun μ hμ hne => ?_, fun h0 => hsimple ?_⟩
  · have h := hfg μ
    rw [hΛ μ hμ] at h
    have hne' : -I * (μ - κ) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (sub_ne_zero.mpr hne)
    exact (mul_eq_zero.mp h.symm).resolve_left hne'
  · -- differentiate `f̂ = −i(w − κ)ĝ` at `κ`
    have hgd := (_root_.RHTower.EvenSector.differentiable_paperFT_of_compact hg.1.continuous
      hg.hasCompactSupport κ).hasDerivAt
    have hprod := (((hasDerivAt_id κ).sub_const κ).const_mul (-I)).mul hgd
    have hfun : paperFT f = fun w => -I * (id w - κ) * paperFT g w := funext fun w => hfg w
    rw [hfun]
    show deriv ((fun y => -I * (id y - κ)) * paperFT g) κ = 0
    rw [hprod.deriv, h0]
    simp

/-- **Isolating a lattice point.** For every aperture `r > π/h` and every `k₀`, some window of
aperture `r` sees `k₀h` and no other point of `hℤ`. -/
theorem exists_window_isolating_lattice_point {h r : ℝ} (hh : 0 < h) (hr : π / h < r) (k₀ : ℤ) :
    ∃ g : ℝ → ℂ, ApertureWindow r g ∧ (∀ k : ℤ, k ≠ k₀ → paperFT g ((k : ℂ) * h) = 0) ∧
      paperFT g ((k₀ : ℂ) * h) ≠ 0 := by
  set c := π / h with hc
  have hc0 : 0 < c := by positivity
  set κ : ℂ := (k₀ : ℂ) * h with hκ
  obtain ⟨b, hb, hb1⟩ := exists_window_paperFT_eq_one (by linarith : 0 < r - c) κ
  obtain ⟨f, hf, hft⟩ := apertureWindow_sine (τ := 0) hc0.le hb
  rw [sub_add_cancel] at hf
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hlat : ∀ k : ℤ, (c : ℂ) * ((k : ℂ) * h - ((0 : ℝ) : ℂ)) = k * π := fun k => by
    rw [hc]; push_cast; field_simp; ring
  set Λ : Set ℂ := Set.range fun k : ℤ => (k : ℂ) * h with hΛ
  have hblind : ∀ μ ∈ Λ, paperFT f μ = 0 := by
    rintro μ ⟨k, rfl⟩
    rw [hft, hlat, Complex.sin_int_mul_pi, zero_mul]
  -- the zero at `κ` is simple: `f̂'(κ) = c cos(k₀π) ≠ 0`
  have hsimple : deriv (paperFT f) κ ≠ 0 := by
    have hbd := (_root_.RHTower.EvenSector.differentiable_paperFT_of_compact hb.1.continuous
      hb.hasCompactSupport κ).hasDerivAt
    have hsin := (Complex.hasDerivAt_sin ((c : ℂ) * (κ - ((0 : ℝ) : ℂ)))).comp κ
      (((hasDerivAt_id κ).sub_const ((0 : ℝ) : ℂ)).const_mul (c : ℂ))
    have hfun : paperFT f = fun w => Complex.sin ((c : ℂ) * (id w - ((0 : ℝ) : ℂ))) * paperFT b w :=
      funext fun w => hft w
    rw [hfun]
    show deriv ((Complex.sin ∘ fun y => (c : ℂ) * (id y - ((0 : ℝ) : ℂ))) * paperFT b) κ ≠ 0
    rw [(hsin.mul hbd).deriv, hb1]
    simp only [id, mul_one, Function.comp_apply]
    rw [show (c : ℂ) * (κ - ((0 : ℝ) : ℂ)) = k₀ * π from hlat k₀, Complex.sin_int_mul_pi, zero_mul,
      add_zero]
    have hcos : Complex.cos ((k₀ : ℂ) * π) ≠ 0 := by
      intro h0
      have := Complex.sin_sq_add_cos_sq ((k₀ : ℂ) * π)
      rw [h0, Complex.sin_int_mul_pi] at this
      norm_num at this
    exact mul_ne_zero hcos (Complex.ofReal_ne_zero.mpr hc0.ne')
  obtain ⟨g, hg, hgΛ, hgκ⟩ := exists_isolating_window hf hblind ⟨k₀, rfl⟩ hsimple
  refine ⟨g, hg, fun k hk => hgΛ _ ⟨k, rfl⟩ fun h0 => hk ?_, hgκ⟩
  have := congrArg (fun z : ℂ => z / h) h0
  simp only [mul_div_assoc, div_self hh', mul_one] at this
  exact_mod_cast this

end GaloisForLFunctions.ZeroConfigurationGeometry
