import GaloisForLFunctions.ZeroConfigurationGeometry.FiniteModificationsAreSeenAtEveryAperture
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity

/-!
# Differential windows invert the camera

The window operator `A_z g = g' + i z g` multiplies the transform by a linear factor:
`(A_z g)^(w) = −i(w − z) ĝ(w)` (`paperFT_annihilate`, integration by parts). It keeps smoothness and
support. Composing such operators over a finite set `T` of frequencies gives windows whose transform
is `∏_{z ∈ T} (−i(w − z))·b̂(w)` (`exists_annihilating_window`): they vanish at every point of `T`,
and their size at one remaining point is the product of its gaps to `T`.

* **Exact coefficient extraction** (`exists_window_sum_eq_coeff_mul_gaps`). For a finite set `S` of
  frequencies, a point `w₀ ∈ S` and any aperture `r > 0`, there is a smooth window of aperture `r`
  with `Σ_{w ∈ S} a_w f̂(w) = a_{w₀} ∏_{w ∈ S∖{w₀}} (−i(w₀ − w))`.
* **The explicit inverse of the camera** (`exists_windows_W_sub_W_eq`). If two tempered
  configurations differ by the signed multiplicity `c` on a finite set `S`, for each `z₀ ∈ S` and
  each `r > 0` there are windows `f, g` of aperture `r` with
  `W_Z(f, g) − W_{Z'}(f, g) = c(z₀) ∏_{z ∈ S∖{z₀}} (−i(γ_{z₀} − γ_z))`.

So identification of finite modifications is constructive, and its conditioning is the product of
the gaps `|γ_{z₀} − γ_z|`, depths included. Near-collisions make the inverse ill-conditioned: the
coalescent regime of the field is where this product is small.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- The window operator `A_z g = g' + i z g`. -/
def annihilate (z : ℂ) (g : ℝ → ℂ) : ℝ → ℂ := fun u => deriv g u + I * z * g u

theorem contDiff_annihilate {z : ℂ} {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (annihilate z g) :=
  (contDiff_infty_iff_deriv.mp hg).2.add (contDiff_const.mul hg)

theorem tsupport_annihilate_subset (z : ℂ) (g : ℝ → ℂ) :
    tsupport (annihilate z g) ⊆ tsupport g :=
  (tsupport_add _ _).trans (union_subset tsupport_deriv_subset
    (tsupport_mul_subset_right (f := fun _ => I * z)))

/-- **The window operator multiplies the transform by `−i(w − z)`.** -/
theorem paperFT_annihilate {z : ℂ} {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (w : ℂ) :
    paperFT (annihilate z g) w = -I * (w - z) * paperFT g w := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_cast)
  have hd : Continuous (deriv g) := hg1.continuous_deriv le_rfl
  change paperFT (fun u => deriv g u + (I * z) * g u) w = _
  rw [paperFT_add_smul hd hgc.deriv hg.continuous hgc,
    _root_.RHTower.EvenSector.paperFT_deriv_of_compact hg1 hgc]
  ring

/-- **Annihilating windows.** For a finite set `T` of frequencies there is a smooth window, supported
inside the support of `b`, whose transform is `∏_{z ∈ T} (−i(w − z)) b̂(w)`. -/
theorem exists_annihilating_window (T : Finset ℂ) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) :
    ∃ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ tsupport f ⊆ tsupport b ∧
      ∀ w, paperFT f w = (∏ z ∈ T, (-I * (w - z))) * paperFT b w := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨b, hb, subset_rfl, fun w => by simp⟩
  | @insert z T hz ih =>
    obtain ⟨f, hf, hfs, hfw⟩ := ih
    have hfc : HasCompactSupport f := IsCompact.of_isClosed_subset hbc (isClosed_tsupport f) hfs
    refine ⟨annihilate z f, contDiff_annihilate hf, (tsupport_annihilate_subset z f).trans hfs,
      fun w => ?_⟩
    rw [paperFT_annihilate hf hfc, hfw, Finset.prod_insert hz]
    ring

/-- A smooth window of aperture `r` whose transform equals `1` at the frequency `w₀`. -/
theorem exists_smooth_window_paperFT_eq_one {r : ℝ} (hr : 0 < r) (w₀ : ℂ) :
    ∃ b : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧ tsupport b ⊆ Icc (-r) r ∧
      paperFT b w₀ = 1 := by
  let B : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by linarith, by linarith⟩
  have hBs : tsupport (B.normed volume) ⊆ Icc (-r) r := by
    rw [B.tsupport_normed_eq]
    intro u hu
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, show B.rOut = r from rfl] at hu
    exact abs_le.mp hu
  have hsupp : tsupport (fun u : ℝ => (B.normed volume u : ℂ) * cexp (-(I * w₀ * u))) ⊆
      Icc (-r) r :=
    (tsupport_mul_subset_left).trans
      ((tsupport_comp_subset (g := fun y : ℝ => (y : ℂ)) Complex.ofReal_zero _).trans hBs)
  refine ⟨fun u => (B.normed volume u : ℂ) * cexp (-(I * w₀ * u)), ?_, ?_, hsupp, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp B.contDiff_normed).mul
      ((contDiff_const.mul Complex.ofRealCLM.contDiff).neg.cexp)
  · exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hsupp
  · rw [paperFT_def]
    have : ∀ u : ℝ, (B.normed volume u : ℂ) * cexp (-(I * w₀ * u)) * cexp (I * w₀ * u) =
        (B.normed volume u : ℂ) := fun u => by
      rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    simp_rw [this]
    rw [integral_complex_ofReal, B.integral_normed, Complex.ofReal_one]

/-- **Exact coefficient extraction.** -/
theorem exists_window_sum_eq_coeff_mul_gaps {S : Finset ℂ} (a : ℂ → ℂ) {w₀ : ℂ} (hw₀ : w₀ ∈ S)
    {r : ℝ} (hr : 0 < r) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧
      ∑ w ∈ S, a w * paperFT f w = a w₀ * ∏ z ∈ S.erase w₀, (-I * (w₀ - z)) := by
  classical
  obtain ⟨b, hb, hbc, hbs, hb1⟩ := exists_smooth_window_paperFT_eq_one hr w₀
  obtain ⟨f, hf, hfs, hfw⟩ := exists_annihilating_window (S.erase w₀) hb hbc
  refine ⟨f, ⟨hf.of_le (by norm_cast), hfs.trans hbs⟩, ?_⟩
  rw [Finset.sum_eq_single w₀ (fun w hw hne => by
      rw [hfw, Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, hw⟩) (by ring), zero_mul,
        mul_zero])
    (fun h => absurd hw₀ h), hfw, hb1, mul_one]

theorem gammaOf_injective : Function.Injective gammaOf := fun z z' h => by
  simpa [gammaOf, div_left_inj' Complex.I_ne_zero, sub_left_inj] using h

/-- **The explicit inverse of the camera.** Each coefficient of a finite modification is read by
one pair of windows of any aperture, with amplitude the product of the gaps to the other points. -/
theorem exists_windows_W_sub_W_eq {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {S : Finset ℂ} (hS : ∀ z ∉ S, multDiff Z Z' z = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ S) {r : ℝ} (hr : 0 < r) :
    ∃ f g : ℝ → ℂ, ApertureWindow r f ∧ ApertureWindow r g ∧
      Z.W f g - Z'.W f g =
        multDiff Z Z' z₀ * ∏ z ∈ S.erase z₀, (-I * (gammaOf z₀ - gammaOf z)) := by
  classical
  obtain ⟨g, hg, hg1⟩ := exists_window_paperFT_eq_one hr (conj (gammaOf z₀))
  obtain ⟨b, hb, hbc, hbs, hb1⟩ := exists_smooth_window_paperFT_eq_one hr (gammaOf z₀)
  obtain ⟨f, hf, hfs, hfw⟩ :=
    exists_annihilating_window ((S.erase z₀).image gammaOf) hb hbc
  have hfwin : ApertureWindow r f := ⟨hf.of_le (by norm_cast), hfs.trans hbs⟩
  refine ⟨f, g, hfwin, hg, ?_⟩
  rw [W_sub_W_eq_sum hZ hZ' hS hfwin.1 hfwin.hasCompactSupport hg.1 hg.hasCompactSupport]
  rw [Finset.sum_eq_single z₀ (fun z hz hne => by
      rw [pointImage, hfw, Finset.prod_eq_zero
        (Finset.mem_image_of_mem gammaOf (Finset.mem_erase.mpr ⟨hne, hz⟩)) (by ring), zero_mul,
        zero_mul, mul_zero])
    (fun h => absurd hz₀ h)]
  rw [pointImage, hfw, hb1, hg1, map_one, mul_one, mul_one,
    Finset.prod_image fun z _ z' _ h => gammaOf_injective h]
