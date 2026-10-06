import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Zeta23.Defs

/-!
# Zero flipping: rigid compactly supported functions have real Fourier zeros

For `f` continuous and supported in `[-L, L]` write `f̂(z) = ∫ f(u) e^{izu} du` (`paperFT`), an
entire function.  If `f̂(z₀) = 0`, the **zero flip**

`h = f + (z₀ − z̄₀) g`,  `g(x) = −i e^{−iz₀x} ∫_{−L}^{x} e^{iz₀y} f(y) dy`,

is again continuous and supported in `[-L, L]` (`supportedIn_zeroFlip`; the primitive vanishes
at both ends because `f̂(z₀) = 0`), and integration by parts gives

`ĥ(w) = f̂(w) (w − z̄₀)/(w − z₀)`,  `w ≠ z₀` (`paperFT_zeroFlip`).

So `|ĥ| = |f̂|` on the real line (`norm_paperFT_zeroFlip`), `h` keeps every other zero of `f̂`,
and the zero `z₀` has moved to `z̄₀`.  No Paley–Wiener theorem is used: the flip is explicit.

**Theorem** (`im_eq_zero_of_zeroFlip_rigid`).  Let `f₀ ≠ 0` be continuous, supported in
`[-L, L]`, with `f̂₀ = 0` on a set `E`.  If every such function with the same Fourier modulus on
`ℝ` is a scalar multiple of `f₀`, then every zero of `f̂₀` outside `E` is real.  The `Cⁿ`
version (`im_eq_zero_of_zeroFlip_rigid_contDiff`) restricts the comparison class to `Cⁿ`
functions, which the flip preserves (`contDiff_zeroFlip`).

**Corollary** (`im_eq_zero_of_simple_rayleigh`, `im_eq_zero_of_simple_rayleigh_contDiff`).  For
a real symbol `S`, the form `∫ S |f̂|²` on functions supported in `[-L, L]` depends only on `|f̂|`
on `ℝ`.  If the extremal Rayleigh value `∫ S|f̂|² / ∫ |f̂|²` has the single eigenline `ℂ f₀`,
then `f̂₀` has no non-real zeros outside `E`.  This is the Connes–van Suijlekom mechanism: a
simple ground state of a translation-invariant form on an interval has a real-rooted transform.

**Proof of the theorem.**  If `Im z₀ ≠ 0`, rigidity gives `h = c f₀`, hence
`f̂₀(t)((t − z̄₀) − c(t − z₀)) = 0` for real `t`.  For `c = 1` the bracket is `z₀ − z̄₀ ≠ 0`;
otherwise it vanishes at no more than one real point.  Either way `f̂₀ = 0` on `ℝ` off one
point, and Fourier inversion (`eq_zero_of_paperFT_eq_zero`) gives `f₀ = 0`.
-/

noncomputable section
open Complex MeasureTheory Set intervalIntegral Filter Topology Zeta23

namespace GaloisForLFunctions.HTGeometry.FourierZeroFlip

/-- `f` vanishes off `[-L, L]`. -/
def SupportedIn (L : ℝ) (f : ℝ → ℂ) : Prop := ∀ x, x ∉ Icc (-L) L → f x = 0

theorem left_zero {L : ℝ} {f : ℝ → ℂ} (hc : Continuous f) (hs : SupportedIn L f) {y : ℝ}
    (hy : y ≤ -L) : f y = 0 := by
  rcases hy.lt_or_eq with hy | hy
  · exact hs y fun h => by linarith [h.1]
  · subst hy
    have h1 : Tendsto f (𝓝[<] (-L)) (𝓝 (f (-L))) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto f (𝓝[<] (-L)) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (hs x fun h => by linarith [h.1, show x < -L from hx]).symm
    exact tendsto_nhds_unique h1 h2

theorem right_zero {L : ℝ} {f : ℝ → ℂ} (hc : Continuous f) (hs : SupportedIn L f) {y : ℝ}
    (hy : L ≤ y) : f y = 0 := by
  rcases hy.lt_or_eq with hy | hy
  · exact hs y fun h => by linarith [h.2]
  · subst hy
    have h1 : Tendsto f (𝓝[>] L) (𝓝 (f L)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto f (𝓝[>] L) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (hs x fun h => by linarith [h.2, show L < x from hx]).symm
    exact tendsto_nhds_unique h1 h2

theorem paperFT_eq_intervalIntegral {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hs : SupportedIn L f)
    (z : ℂ) : paperFT f z = ∫ x in (-L)..L, f x * cexp (I * z * x) := by
  unfold paperFT
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  rw [hs x hx, zero_mul]

/-- The primitive `A(x) = ∫_{-L}^x e^{i z₀ y} f(y) dy`. -/
def prim (L : ℝ) (f : ℝ → ℂ) (z₀ : ℂ) (x : ℝ) : ℂ := ∫ y in (-L)..x, cexp (I * z₀ * y) * f y

theorem continuous_primIntegrand {f : ℝ → ℂ} (hc : Continuous f) (z₀ : ℂ) :
    Continuous fun y : ℝ => cexp (I * z₀ * y) * f y := by fun_prop

theorem hasDerivAt_prim (L : ℝ) {f : ℝ → ℂ} (hc : Continuous f) (z₀ : ℂ) (x : ℝ) :
    HasDerivAt (prim L f z₀) (cexp (I * z₀ * x) * f x) x :=
  ((continuous_primIntegrand hc z₀).integral_hasStrictDerivAt (-L) x).hasDerivAt

theorem prim_eq_zero_of_le {L : ℝ} {f : ℝ → ℂ} (hc : Continuous f) (hs : SupportedIn L f)
    (z₀ : ℂ) {x : ℝ} (hx : x ≤ -L) : prim L f z₀ x = 0 := by
  unfold prim
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)), intervalIntegral.integral_zero]
  intro y hy
  rw [uIcc_of_ge hx] at hy
  simp [left_zero hc hs hy.2]

theorem prim_eq_paperFT_of_ge {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hc : Continuous f)
    (hs : SupportedIn L f) (z₀ : ℂ) {x : ℝ} (hx : L ≤ x) : prim L f z₀ x = paperFT f z₀ := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun y : ℝ => cexp (I * z₀ * y) * f y) volume a b :=
    fun a b => (continuous_primIntegrand hc z₀).intervalIntegrable a b
  unfold prim
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-L) L) (hi L x),
    intervalIntegral.integral_congr (a := L) (b := x) (g := fun _ => (0 : ℂ)),
    intervalIntegral.integral_zero, add_zero, paperFT_eq_intervalIntegral hL hs]
  · exact intervalIntegral.integral_congr fun y _ => mul_comm _ _
  · intro y hy
    rw [uIcc_of_le hx] at hy
    simp [right_zero hc hs hy.1]

/-- The flip correction `g(x) = -i e^{-i z₀ x} A(x)`. -/
def flipAux (L : ℝ) (f : ℝ → ℂ) (z₀ : ℂ) (x : ℝ) : ℂ :=
  -I * cexp (-(I * z₀ * x)) * prim L f z₀ x

/-- The zero flip `h = f + (z₀ - z̄₀) g`; its transform is `f̂ · (w - z̄₀)/(w - z₀)`. -/
def zeroFlip (L : ℝ) (f : ℝ → ℂ) (z₀ : ℂ) (x : ℝ) : ℂ :=
  f x + (z₀ - (starRingEnd ℂ) z₀) * flipAux L f z₀ x

theorem continuous_prim (L : ℝ) {f : ℝ → ℂ} (hc : Continuous f) (z₀ : ℂ) :
    Continuous (prim L f z₀) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_prim L hc z₀ x).continuousAt

theorem continuous_zeroFlip (L : ℝ) {f : ℝ → ℂ} (hc : Continuous f) (z₀ : ℂ) :
    Continuous (zeroFlip L f z₀) := by
  have := continuous_prim L hc z₀
  unfold zeroFlip flipAux
  fun_prop

theorem supportedIn_zeroFlip {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hc : Continuous f)
    (hs : SupportedIn L f) {z₀ : ℂ} (hz : paperFT f z₀ = 0) : SupportedIn L (zeroFlip L f z₀) := by
  intro x hx
  have hfx := hs x hx
  have hp : prim L f z₀ x = 0 := by
    rcases le_or_gt x (-L) with h | h
    · exact prim_eq_zero_of_le hc hs z₀ h
    · have : L ≤ x := by
        by_contra hlt
        exact hx ⟨h.le, (not_le.mp hlt).le⟩
      rw [prim_eq_paperFT_of_ge hL hc hs z₀ this, hz]
  simp [zeroFlip, flipAux, hfx, hp]

theorem supportedIn_flipAux {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hc : Continuous f)
    (hs : SupportedIn L f) {z₀ : ℂ} (hz : paperFT f z₀ = 0) : SupportedIn L (flipAux L f z₀) := by
  intro x hx
  have hp : prim L f z₀ x = 0 := by
    rcases le_or_gt x (-L) with h | h
    · exact prim_eq_zero_of_le hc hs z₀ h
    · have : L ≤ x := by
        by_contra hlt
        exact hx ⟨h.le, (not_le.mp hlt).le⟩
      rw [prim_eq_paperFT_of_ge hL hc hs z₀ this, hz]
  simp [flipAux, hp]

/-- The transform of the flip correction: `ĝ(w) = f̂(w)/(w - z₀)`. -/
theorem paperFT_flipAux {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hc : Continuous f)
    (hs : SupportedIn L f) {z₀ : ℂ} (hz : paperFT f z₀ = 0) {w : ℂ} (hw : w ≠ z₀) :
    paperFT (flipAux L f z₀) w = paperFT f w / (w - z₀) := by
  have hwz : w - z₀ ≠ 0 := sub_ne_zero.mpr hw
  have hIw : I * (w - z₀) ≠ 0 := mul_ne_zero I_ne_zero hwz
  rw [paperFT_eq_intervalIntegral hL (supportedIn_flipAux hL hc hs hz),
    paperFT_eq_intervalIntegral hL hs]
  set v : ℝ → ℂ := fun x => cexp (I * (w - z₀) * x) / (I * (w - z₀)) with hv
  have hvd : ∀ x : ℝ, HasDerivAt v (cexp (I * (w - z₀) * x)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => I * (w - z₀) * (x : ℂ)) (I * (w - z₀)) x := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul (I * (w - z₀))).comp_ofReal
    exact (h1.cexp.div_const (I * (w - z₀))).congr_deriv (mul_div_cancel_right₀ _ hIw)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -L) (b := L)
    (u := prim L f z₀) (v := v) (u' := fun x => cexp (I * z₀ * x) * f x)
    (v' := fun x => cexp (I * (w - z₀) * x))
    (fun x _ => hasDerivAt_prim L hc z₀ x) (fun x _ => hvd x)
    ((continuous_primIntegrand hc z₀).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun x : ℝ => cexp (I * (w - z₀) * x)).intervalIntegrable _ _)
  rw [prim_eq_paperFT_of_ge hL hc hs z₀ le_rfl, hz, prim_eq_zero_of_le hc hs z₀ le_rfl] at hparts
  simp only [zero_mul, sub_zero, zero_sub] at hparts
  have hL1 : (∫ x in (-L)..L, flipAux L f z₀ x * cexp (I * w * x)) =
      -I * ∫ x in (-L)..L, prim L f z₀ x * cexp (I * (w - z₀) * x) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [flipAux]
    have : cexp (-(I * z₀ * x)) * cexp (I * w * x) = cexp (I * (w - z₀) * x) := by
      rw [← Complex.exp_add]; ring_nf
    linear_combination (-I * prim L f z₀ x) * this
  have hL2 : (∫ x in (-L)..L, cexp (I * z₀ * x) * f x * v x) =
      (∫ x in (-L)..L, f x * cexp (I * w * x)) / (I * (w - z₀)) := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hv]
    have : cexp (I * z₀ * x) * cexp (I * (w - z₀) * x) = cexp (I * w * x) := by
      rw [← Complex.exp_add]; ring_nf
    rw [← this]
    ring
  rw [hL1, hparts, hL2]
  field_simp


theorem continuous_flipAux (L : ℝ) {f : ℝ → ℂ} (hc : Continuous f) (z₀ : ℂ) :
    Continuous (flipAux L f z₀) := by
  have := continuous_prim L hc z₀
  unfold flipAux
  fun_prop

/-- The transform of the zero flip: `ĥ(w) = f̂(w)·(w − z̄₀)/(w − z₀)` for `w ≠ z₀`. -/
theorem paperFT_zeroFlip {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hc : Continuous f)
    (hs : SupportedIn L f) {z₀ : ℂ} (hz : paperFT f z₀ = 0) {w : ℂ} (hw : w ≠ z₀) :
    paperFT (zeroFlip L f z₀) w = paperFT f w * (w - (starRingEnd ℂ) z₀) / (w - z₀) := by
  have hwz : w - z₀ ≠ 0 := sub_ne_zero.mpr hw
  have hg := paperFT_flipAux hL hc hs hz hw
  rw [paperFT_eq_intervalIntegral hL (supportedIn_flipAux hL hc hs hz)] at hg
  rw [paperFT_eq_intervalIntegral hL (supportedIn_zeroFlip hL hc hs hz)]
  have hfi : IntervalIntegrable (fun x : ℝ => f x * cexp (I * w * x)) volume (-L) L :=
    (by fun_prop : Continuous fun x : ℝ => f x * cexp (I * w * x)).intervalIntegrable _ _
  have hgi : IntervalIntegrable (fun x : ℝ => (z₀ - (starRingEnd ℂ) z₀) *
      (flipAux L f z₀ x * cexp (I * w * x))) volume (-L) L := by
    have := continuous_flipAux L hc z₀
    exact (by fun_prop : Continuous fun x : ℝ => (z₀ - (starRingEnd ℂ) z₀) *
      (flipAux L f z₀ x * cexp (I * w * x))).intervalIntegrable _ _
  have hsplit : (∫ x in (-L)..L, zeroFlip L f z₀ x * cexp (I * w * x)) =
      (∫ x in (-L)..L, f x * cexp (I * w * x)) +
        (z₀ - (starRingEnd ℂ) z₀) * ∫ x in (-L)..L, flipAux L f z₀ x * cexp (I * w * x) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hfi hgi]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [zeroFlip]
    ring
  rw [hsplit, hg, ← paperFT_eq_intervalIntegral hL hs]
  field_simp
  ring

theorem norm_sub_conj_eq (t : ℝ) (z₀ : ℂ) :
    ‖(t : ℂ) - (starRingEnd ℂ) z₀‖ = ‖(t : ℂ) - z₀‖ := by
  rw [← Complex.norm_conj ((t : ℂ) - z₀), map_sub, conj_ofReal]

/-- On the real line the zero flip has the same Fourier modulus. -/
theorem norm_paperFT_zeroFlip {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hc : Continuous f)
    (hs : SupportedIn L f) {z₀ : ℂ} (hz : paperFT f z₀ = 0) (him : z₀.im ≠ 0) (t : ℝ) :
    ‖paperFT (zeroFlip L f z₀) t‖ = ‖paperFT f t‖ := by
  have ht : (t : ℂ) ≠ z₀ := fun h => him (by rw [← h]; simp)
  have hn : ‖(t : ℂ) - z₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr ht)
  rw [paperFT_zeroFlip hL hc hs hz ht, norm_div, norm_mul, norm_sub_conj_eq, mul_div_assoc,
    div_self hn, mul_one]

theorem paperFT_smul (c : ℂ) (f : ℝ → ℂ) (w : ℂ) : paperFT (c • f) w = c * paperFT f w := by
  unfold paperFT
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Injectivity.** A continuous function supported in `[-L, L]` whose transform vanishes on the
real line off one point is zero. -/
theorem eq_zero_of_paperFT_eq_zero {L : ℝ} {f : ℝ → ℂ} (hc : Continuous f) (hs : SupportedIn L f)
    (t₀ : ℝ) (h0 : ∀ t : ℝ, t ≠ t₀ → paperFT f t = 0) : f = 0 := by
  have hcs : HasCompactSupport f := HasCompactSupport.intro isCompact_Icc fun x hx => hs x hx
  have hint : Integrable f := hc.integrable_of_hasCompactSupport hcs
  have hval : ∀ w : ℝ, w ≠ -t₀ / (2 * Real.pi) → FourierTransform.fourier f w = 0 := by
    intro w hw
    rw [Real.fourier_eq']
    have hne : -2 * Real.pi * w ≠ t₀ := by
      intro h
      apply hw
      field_simp
      linarith
    have := h0 (-2 * Real.pi * w) hne
    unfold paperFT at this
    rw [← this]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
    rw [mul_comm]
    congr 1
    push_cast
    ring_nf
  have hae : FourierTransform.fourier f =ᵐ[volume] (0 : ℝ → ℂ) := by
    have : {w : ℝ | FourierTransform.fourier f w ≠ 0} ⊆ {-t₀ / (2 * Real.pi)} := by
      intro w hw
      by_contra h
      exact hw (hval w h)
    exact measure_mono_null this Real.volume_singleton
  have hFi : Integrable (FourierTransform.fourier f) := (integrable_zero _ _ _).congr hae.symm
  have hinv := hc.fourierInv_fourier_eq hint hFi
  funext x
  rw [← hinv, Real.fourierInv_eq']
  simp only [Pi.zero_apply]
  rw [MeasureTheory.integral_congr_ae (g := fun _ => (0 : ℂ))]
  · simp
  · filter_upwards [hae] with v hv
    rw [hv]
    simp


/-- **Core.** If the zero flip of `f₀ ≠ 0` at a zero `z₀` of `f̂₀` is a scalar multiple of `f₀`,
then `z₀` is real. -/
theorem im_eq_zero_of_zeroFlip_eq_smul {L : ℝ} (hL : 0 ≤ L) {f₀ : ℝ → ℂ} (hc : Continuous f₀)
    (hs : SupportedIn L f₀) (hne : f₀ ≠ 0) {z₀ : ℂ} (hz : paperFT f₀ z₀ = 0)
    (hflip : ∃ c : ℂ, zeroFlip L f₀ z₀ = c • f₀) : z₀.im = 0 := by
  by_contra him
  obtain ⟨c, hcf⟩ := hflip
  have key : ∀ t : ℝ, paperFT f₀ t * (((t : ℂ) - (starRingEnd ℂ) z₀) - c * ((t : ℂ) - z₀)) = 0 := by
    intro t
    have ht : (t : ℂ) ≠ z₀ := fun h => him (by rw [← h]; simp)
    have htz : (t : ℂ) - z₀ ≠ 0 := sub_ne_zero.mpr ht
    have h1 := paperFT_zeroFlip hL hc hs hz ht
    rw [hcf, paperFT_smul] at h1
    field_simp at h1
    linear_combination -h1
  have hconj : z₀ - (starRingEnd ℂ) z₀ ≠ 0 := by
    intro h
    apply him
    have := congrArg Complex.im h
    simp [Complex.conj_im] at this
    linarith
  by_cases hc1 : c = 1
  · apply hne
    refine eq_zero_of_paperFT_eq_zero hc hs 0 fun t _ => ?_
    have := key t
    rw [hc1] at this
    have h2 : paperFT f₀ t * (z₀ - (starRingEnd ℂ) z₀) = 0 := by
      linear_combination this
    exact (mul_eq_zero.mp h2).resolve_right hconj
  · have h1c : (1 : ℂ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
    set t₁ : ℂ := ((starRingEnd ℂ) z₀ - c * z₀) / (1 - c)
    apply hne
    refine eq_zero_of_paperFT_eq_zero hc hs t₁.re fun t ht => ?_
    have hP : ((t : ℂ) - (starRingEnd ℂ) z₀) - c * ((t : ℂ) - z₀) ≠ 0 := by
      intro h
      apply ht
      have : (t : ℂ) = t₁ := by
        simp only [t₁]
        field_simp
        linear_combination h
      rw [← this]
      simp
    exact (mul_eq_zero.mp (key t)).resolve_right hP

theorem paperFT_zeroFlip_eq_zero {L : ℝ} (hL : 0 ≤ L) {f₀ : ℝ → ℂ} (hc : Continuous f₀)
    (hs : SupportedIn L f₀) {z₀ : ℂ} (hz : paperFT f₀ z₀ = 0) {w : ℂ} (hw : paperFT f₀ w = 0)
    (hwz : w ≠ z₀) : paperFT (zeroFlip L f₀ z₀) w = 0 := by
  rw [paperFT_zeroFlip hL hc hs hz hwz, hw]
  simp

/-- **Zero-flip rigidity.** Let `f₀ ≠ 0` be continuous and supported in `[-L, L]`, with transform
vanishing on a set `E`.  If every such function with the same Fourier modulus on `ℝ` is a scalar
multiple of `f₀`, then every zero of `f̂₀` outside `E` is real. -/
theorem im_eq_zero_of_zeroFlip_rigid {L : ℝ} (hL : 0 ≤ L) {f₀ : ℝ → ℂ} (hc : Continuous f₀)
    (hs : SupportedIn L f₀) (hne : f₀ ≠ 0) {E : Set ℂ} (hE : ∀ w ∈ E, paperFT f₀ w = 0)
    (hrigid : ∀ f : ℝ → ℂ, Continuous f → SupportedIn L f → (∀ w ∈ E, paperFT f w = 0) →
      (∀ t : ℝ, ‖paperFT f t‖ = ‖paperFT f₀ t‖) → ∃ c : ℂ, f = c • f₀)
    {z₀ : ℂ} (hz : paperFT f₀ z₀ = 0) (hzE : z₀ ∉ E) : z₀.im = 0 := by
  by_contra him
  exact him (im_eq_zero_of_zeroFlip_eq_smul hL hc hs hne hz
    (hrigid _ (continuous_zeroFlip L hc z₀) (supportedIn_zeroFlip hL hc hs hz)
      (fun w hw => paperFT_zeroFlip_eq_zero hL hc hs hz (hE w hw) fun h => hzE (h ▸ hw))
      (norm_paperFT_zeroFlip hL hc hs hz him)))

theorem contDiff_prim (L : ℝ) {n : ℕ} {f : ℝ → ℂ} (hf : ContDiff ℝ n f) (z₀ : ℂ) :
    ContDiff ℝ n (prim L f z₀) := by
  have hc : Continuous f := hf.continuous
  have h : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (prim L f z₀) := by
    refine contDiff_succ_iff_deriv.mpr ⟨fun x => (hasDerivAt_prim L hc z₀ x).differentiableAt,
      by simp, ?_⟩
    have hd : deriv (prim L f z₀) = fun x : ℝ => cexp (I * z₀ * x) * f x :=
      funext fun x => (hasDerivAt_prim L hc z₀ x).deriv
    rw [hd]
    have he : ContDiff ℝ n fun x : ℝ => cexp (I * z₀ * x) := by
      have : ContDiff ℝ n fun x : ℝ => I * z₀ * (x : ℂ) :=
        contDiff_const.mul Complex.ofRealCLM.contDiff
      exact Complex.contDiff_exp.comp this
    exact he.mul hf
  exact h.of_succ

theorem contDiff_zeroFlip (L : ℝ) {n : ℕ} {f : ℝ → ℂ} (hf : ContDiff ℝ n f) (z₀ : ℂ) :
    ContDiff ℝ n (zeroFlip L f z₀) := by
  have hp := contDiff_prim L hf z₀
  have he : ContDiff ℝ n fun x : ℝ => cexp (-(I * z₀ * x)) := by
    have : ContDiff ℝ n fun x : ℝ => -(I * z₀ * (x : ℂ)) :=
      (contDiff_const.mul Complex.ofRealCLM.contDiff).neg
    exact Complex.contDiff_exp.comp this
  exact hf.add (contDiff_const.mul ((contDiff_const.mul he).mul hp))

/-- **Zero-flip rigidity for `Cⁿ` classes.** As `im_eq_zero_of_zeroFlip_rigid`, with the comparison
class restricted to `Cⁿ` functions (the zero flip preserves `Cⁿ`). -/
theorem im_eq_zero_of_zeroFlip_rigid_contDiff {L : ℝ} (hL : 0 ≤ L) {n : ℕ} {f₀ : ℝ → ℂ}
    (hf : ContDiff ℝ n f₀) (hs : SupportedIn L f₀) (hne : f₀ ≠ 0) {E : Set ℂ}
    (hE : ∀ w ∈ E, paperFT f₀ w = 0)
    (hrigid : ∀ f : ℝ → ℂ, ContDiff ℝ n f → SupportedIn L f → (∀ w ∈ E, paperFT f w = 0) →
      (∀ t : ℝ, ‖paperFT f t‖ = ‖paperFT f₀ t‖) → ∃ c : ℂ, f = c • f₀)
    {z₀ : ℂ} (hz : paperFT f₀ z₀ = 0) (hzE : z₀ ∉ E) : z₀.im = 0 := by
  have hc : Continuous f₀ := hf.continuous
  by_contra him
  exact him (im_eq_zero_of_zeroFlip_eq_smul hL hc hs hne hz
    (hrigid _ (contDiff_zeroFlip L hf z₀) (supportedIn_zeroFlip hL hc hs hz)
      (fun w hw => paperFT_zeroFlip_eq_zero hL hc hs hz (hE w hw) fun h => hzE (h ▸ hw))
      (norm_paperFT_zeroFlip hL hc hs hz him)))

/-- **Simple extremal eigenline ⇒ real zeros (Connes–van Suijlekom mechanism).**  For a real symbol
`S`, put `Q(f) = ∫ S|f̂|²` and `N(f) = ∫ |f̂|²` over the real line.  If, among continuous functions
supported in `[-L, L]` with transform vanishing on `E`, every `f` with `Q f · N f₀ = Q f₀ · N f`
is a multiple of `f₀` (the extremal Rayleigh value has the single eigenline `ℂ f₀`), then every zero
of `f̂₀` outside `E` is real. -/
theorem im_eq_zero_of_simple_rayleigh {L : ℝ} (hL : 0 ≤ L) (S : ℝ → ℝ) {f₀ : ℝ → ℂ}
    (hc : Continuous f₀) (hs : SupportedIn L f₀) (hne : f₀ ≠ 0) {E : Set ℂ}
    (hE : ∀ w ∈ E, paperFT f₀ w = 0)
    (hsimple : ∀ f : ℝ → ℂ, Continuous f → SupportedIn L f → (∀ w ∈ E, paperFT f w = 0) →
      (∫ t : ℝ, S t * ‖paperFT f t‖ ^ 2) * (∫ t : ℝ, ‖paperFT f₀ t‖ ^ 2) =
        (∫ t : ℝ, S t * ‖paperFT f₀ t‖ ^ 2) * (∫ t : ℝ, ‖paperFT f t‖ ^ 2) →
      ∃ c : ℂ, f = c • f₀)
    {z₀ : ℂ} (hz : paperFT f₀ z₀ = 0) (hzE : z₀ ∉ E) : z₀.im = 0 := by
  refine im_eq_zero_of_zeroFlip_rigid hL hc hs hne hE (fun f hfc hfs hfE hmod => ?_) hz hzE
  refine hsimple f hfc hfs hfE ?_
  have h1 : (∫ t : ℝ, S t * ‖paperFT f t‖ ^ 2) = ∫ t : ℝ, S t * ‖paperFT f₀ t‖ ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun t => by simp only [hmod t])
  have h2 : (∫ t : ℝ, ‖paperFT f t‖ ^ 2) = ∫ t : ℝ, ‖paperFT f₀ t‖ ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun t => by simp only [hmod t])
  rw [h1, h2]


/-- **Simple extremal eigenline ⇒ real zeros, `Cⁿ` classes.** -/
theorem im_eq_zero_of_simple_rayleigh_contDiff {L : ℝ} (hL : 0 ≤ L) (S : ℝ → ℝ) {n : ℕ}
    {f₀ : ℝ → ℂ} (hf : ContDiff ℝ n f₀) (hs : SupportedIn L f₀) (hne : f₀ ≠ 0) {E : Set ℂ}
    (hE : ∀ w ∈ E, paperFT f₀ w = 0)
    (hsimple : ∀ f : ℝ → ℂ, ContDiff ℝ n f → SupportedIn L f → (∀ w ∈ E, paperFT f w = 0) →
      (∫ t : ℝ, S t * ‖paperFT f t‖ ^ 2) * (∫ t : ℝ, ‖paperFT f₀ t‖ ^ 2) =
        (∫ t : ℝ, S t * ‖paperFT f₀ t‖ ^ 2) * (∫ t : ℝ, ‖paperFT f t‖ ^ 2) →
      ∃ c : ℂ, f = c • f₀)
    {z₀ : ℂ} (hz : paperFT f₀ z₀ = 0) (hzE : z₀ ∉ E) : z₀.im = 0 := by
  refine im_eq_zero_of_zeroFlip_rigid_contDiff hL hf hs hne hE
    (fun f hfc hfs hfE hmod => hsimple f hfc hfs hfE ?_) hz hzE
  have h1 : (∫ t : ℝ, S t * ‖paperFT f t‖ ^ 2) = ∫ t : ℝ, S t * ‖paperFT f₀ t‖ ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun t => by simp only [hmod t])
  have h2 : (∫ t : ℝ, ‖paperFT f t‖ ^ 2) = ∫ t : ℝ, ‖paperFT f₀ t‖ ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun t => by simp only [hmod t])
  rw [h1, h2]

end GaloisForLFunctions.HTGeometry.FourierZeroFlip
