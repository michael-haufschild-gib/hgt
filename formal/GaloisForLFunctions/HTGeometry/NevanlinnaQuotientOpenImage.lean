import GaloisForLFunctions.HTGeometry.CauchyKernelDensityVanishing
import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierBridge
import Mathlib.Analysis.Complex.OpenMapping

/-!
# The Weyl pole map has open image in each half-plane

The projective pole `q(z) = −d(z)/c(z)` of an analytic Nevanlinna carrier family is holomorphic off
the real axis and cannot be constant on a half-plane: on the real axis both lower-row entries are
real and never vanish simultaneously, so a constant nonreal value is impossible.  The open mapping
theorem therefore makes the image of each half-plane an open set, and the Weyl map places those
images in the opposite half-planes.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Set Topology

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- The projective pole map is analytic wherever the denominator entry does not vanish. -/
theorem analyticOnNhd_quotient {S : Set ℂ} (_hSopen : IsOpen S) (hc : ∀ z ∈ S, F.c z ≠ 0) :
    AnalyticOnNhd ℂ F.quotient S := by
  intro z hz
  have hd : AnalyticAt ℂ F.d z := F.differentiable_d.analyticAt z
  have hcz : AnalyticAt ℂ F.c z := F.differentiable_c.analyticAt z
  exact hd.neg.div hcz (hc z hz)

/-- **The pole map is not constant on a half-plane.**  A nonreal constant value would force the
real lower row to vanish identically. -/
theorem quotient_not_constant {S : Set ℂ} (hSopen : IsOpen S) (hSne : S.Nonempty)
    (hc : ∀ z ∈ S, F.c z ≠ 0) {w : ℂ} (hw : w.im ≠ 0)
    (hconst : ∀ z ∈ S, F.quotient z = w) : False := by
  have hlin : ∀ z ∈ S, -F.d z = w * F.c z := by
    intro z hz
    have hz' := hconst z hz
    rw [quotient, div_eq_iff (hc z hz)] at hz'
    exact hz'
  -- the two entire functions agree on a nonempty open set, hence everywhere
  obtain ⟨z₀, hz₀⟩ := hSne
  have hA1 : AnalyticOnNhd ℂ (fun z => -F.d z) univ := fun z _ =>
    (F.differentiable_d.analyticAt z).neg
  have hA2 : AnalyticOnNhd ℂ (fun z => w * F.c z) univ := fun z _ =>
    (analyticAt_const).mul (F.differentiable_c.analyticAt z)
  have heq : EqOn (fun z => -F.d z) (fun z => w * F.c z) univ := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hA1 hA2
      (isPreconnected_univ) (mem_univ z₀) ?_
    filter_upwards [hSopen.mem_nhds hz₀] with z hz
    exact hlin z hz
  -- evaluate on the real axis
  have hreal : ∀ x : ℝ, -((F.base.toBoundaryFamily.matrix.d x : ℝ) : ℂ)
      = w * ((F.base.toBoundaryFamily.matrix.c x : ℝ) : ℂ) := by
    intro x
    have hx : -F.d ((x : ℝ) : ℂ) = w * F.c ((x : ℝ) : ℂ) := heq (mem_univ _)
    rw [F.d_real x, F.c_real x] at hx
    exact hx
  have hczero : ∀ x : ℝ, F.base.toBoundaryFamily.matrix.c x = 0 := by
    intro x
    have him := congrArg Complex.im (hreal x)
    simp only [Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.mul_im,
      Complex.ofReal_re] at him
    have : w.im * F.base.toBoundaryFamily.matrix.c x = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hw
    · exact h
  have hdzero : ∀ x : ℝ, F.base.toBoundaryFamily.matrix.d x = 0 := by
    intro x
    have := hreal x
    rw [hczero x] at this
    simp only [Complex.ofReal_zero, mul_zero, neg_eq_zero] at this
    exact_mod_cast this
  exact F.base.toBoundaryFamily.matrix.C_D_ne_zero 0 ⟨hczero 0, hdzero 0⟩

/-- **The image of a half-plane under the pole map is open.** -/
theorem isOpen_quotient_image {S : Set ℂ} (hSopen : IsOpen S) (hSconn : IsPreconnected S)
    (hSne : S.Nonempty) (hc : ∀ z ∈ S, F.c z ≠ 0)
    (hnonreal : ∀ z ∈ S, (F.quotient z).im ≠ 0) :
    IsOpen (F.quotient '' S) := by
  rcases (F.analyticOnNhd_quotient hSopen hc).is_constant_or_isOpen hSconn with hconst | hopen
  · obtain ⟨w, hw⟩ := hconst
    obtain ⟨z₀, hz₀⟩ := hSne
    have hval : F.quotient z₀ = w := hw z₀ hz₀
    have hwim : w.im ≠ 0 := by
      rw [← hval]
      exact hnonreal z₀ hz₀
    exact (F.quotient_not_constant hSopen ⟨z₀, hz₀⟩ hc hwim fun z hz => hw z hz).elim
  · exact hopen S (subset_refl _) hSopen

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
