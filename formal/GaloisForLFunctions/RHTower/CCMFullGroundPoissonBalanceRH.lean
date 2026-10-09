import GaloisForLFunctions.RHTower.CCMFullGroundZeroSideEigen
import GaloisForLFunctions.RHTower.PaleyWienerPoissonMajorant

/-!
# Poisson-balanced real-rooted ground states force RH

Let `u_j` be ground states of the unconstrained restricted Weil forms at apertures `a_j → ∞`, with
real-rooted Fourier–Laplace transforms and nonzero mass, and let `F_j(z) = ∫ f_j(t) e^{izt} dt` be the
transform of the physical function `f_j`. Suppose that for every `x ∈ ℝ` and `0 < y < 1/2 + η`
the Poisson mean of `log |F_j|` on the real line balances the exponential type:

`a_j y + (y/π) ∫ log |F_j(s)| / ((s - x)² + y²) ds ≤ log (C |∫ f_j|)`.

Then the Riemann hypothesis holds.

The hypothesis is a condition on the modulus of `F_j` on the real line only. By the Poisson
majorant of a Paley–Wiener transform it bounds `F_j` on the strip `0 < |Im z| < 1/2 + η`, and
continuity extends the bound to the real line. The strip-bounded capstone then applies.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower.CCMFullGroundEigen

open GaloisForLFunctions.HTGeometry
open RHTower.CCMRealRootedGround RHTower.CCMFullRealRootedGround

noncomputable section

/-- `|∫ conj(f(t)) e^{izt} dt| = |F(-z̄)|` with `F(w) = ∫ f(t) e^{iwt} dt`. -/
theorem norm_conjTransform_eq (f : ℝ → ℂ) (z : ℂ) :
    ‖conjTransform f z‖ = ‖suzukiEntireFourier f (-(starRingEnd ℂ) z)‖ := by
  rw [← Complex.norm_conj (conjTransform f z), conjTransform, ← integral_conj,
    suzukiEntireFourier]
  congr 2
  funext t
  rw [map_mul, Complex.conj_conj, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- A bound valid off the real line in the strip `|Im z| < Y` extends to the real line. -/
theorem norm_le_of_offAxis {g : ℂ → ℂ} (hg : Continuous g) {Y M : ℝ} (hY : 0 < Y)
    (h : ∀ z : ℂ, z.im ≠ 0 → |z.im| < Y → ‖g z‖ ≤ M) {z : ℂ} (hz : |z.im| < Y) :
    ‖g z‖ ≤ M := by
  by_cases h0 : z.im = 0
  · have ht : Tendsto (fun y : ℝ => ‖g (z + (y : ℂ) * I)‖) (𝓝[>] 0) (𝓝 ‖g z‖) := by
      have hc : Continuous fun y : ℝ => ‖g (z + (y : ℂ) * I)‖ := by fun_prop
      have := hc.tendsto 0
      simp only [ofReal_zero, zero_mul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT hY] with y hy
    have him : (z + (y : ℂ) * I).im = y := by simp [h0]
    refine h _ (by rw [him]; exact hy.1.ne') ?_
    rw [him, abs_of_pos hy.1]
    exact hy.2
  · exact h z h0 hz

/-- **Poisson-balanced real-rooted full ground states force RH.** -/
theorem riemannHypothesis_of_poissonBalancedFullGrounds {η C : ℝ} (hη : 0 < η) (hC : 0 < C)
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (hground : ∀ j, IsFullGround (a j) (u j))
    (hreal : ∀ j (w : ℂ), FourierLaplaceDivision.unitaryLaplace (timeRep (a j) (u j)) w = 0 →
      w.im = 0)
    (hmass : ∀ j, ∫ t : ℝ, timeRep (a j) (u j) t ≠ 0)
    (hbal : ∀ j (x y : ℝ), 0 < y → y < 1 / 2 + η →
      (a j).1 * y + y / Real.pi * ∫ s : ℝ,
        Real.log ‖suzukiEntireFourier (timeRep (a j) (u j)) s‖ / ((s - x) ^ 2 + y ^ 2) ≤
          Real.log (C * ‖∫ t : ℝ, timeRep (a j) (u j) t‖)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_stripBoundedFullGrounds (C := C) hη a ha u hground hreal hmass
    fun j z hz => ?_
  set f : ℝ → ℂ := timeRep (a j) (u j) with hf
  have hsupp := supportedIn_timeRep (a j) (u j)
  have hcont : Continuous (conjTransform f) :=
    (differentiable_conjTransform (a j).2.le (integrable_timeRep (a j) (u j)) hsupp).continuous
  have hMpos : 0 < C * ‖∫ t : ℝ, f t‖ := mul_pos hC (norm_pos_iff.mpr (hmass j))
  refine norm_le_of_offAxis hcont (by linarith) (fun w hw0 hw => ?_) hz
  set v : ℂ := -(starRingEnd ℂ) w with hv
  have hvre : v.re = -w.re := by simp [hv]
  have hvim : v.im = w.im := by simp [hv]
  rw [norm_conjTransform_eq]
  refine (norm_suzukiEntireFourier_le_exp_poisson (a j).2.le (integrable_timeRep (a j) (u j))
    (bound_support_of_supportedIn hsupp) (by rw [hvim]; exact hw0)).trans ?_
  rw [← Real.exp_log hMpos, Real.exp_le_exp, hvim, ← sq_abs w.im]
  exact hbal j v.re |w.im| (abs_pos.mpr hw0) hw

end

end RHTower.CCMFullGroundEigen
