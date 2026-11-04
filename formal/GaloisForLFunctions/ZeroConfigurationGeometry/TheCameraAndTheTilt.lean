import GaloisForLFunctions.RHTower.ZeroLatticeDepthNyquistLaw

/-!
# The camera and the tilt

The transform `f̂(z) = ∫ f(u) e^{izu} du` (`Zeta23.paperFT`) of a window `f` is the camera of the
explicit formula: a zero `ρ` enters every image through `f̂(γ_ρ)`, `γ_ρ = γ − iδ`, `δ = β − ½`.

A camera of aperture `r` uses the windows `ApertureWindow r`: `C²`, supported in `[−r, r]`.

* **Depth is tilt** (`paperFT_gammaOf`). `f̂(γ − iδ) = (f·e^{δu})^(γ)`: every zero is a real point
  of the camera tilted by its depth. In the Gram matrix of the matrix explicit formula an off-line
  zero is the rank-one block of the tilted window at its real ordinate (`Gsummand_eq_tilted`).
* **Pairs are analytic in the squared gap** (`paperFT_add_add_sub`). For every complex `w`,
  `f̂(c + w) + f̂(c − w) = (2cos(wu)·f)^(c)`, an even function of `w`. A real pair (`w` real), a
  collision (`w = 0`) and a tilted pair (`w = iδ`) are the three signs of the real number `w²`.
  For an off-line pair `{ρ, 1 − ρ̄}` the window is `2cosh(δu)·f` (`paperFT_gammaOf_add_reflect`).
* **The depth signal** (`depthSignal_eq`). A tilted pair minus its doubled real centre is the real
  centre seen through `4 sinh²(δu/2)·f`. At aperture `r` its size is at most
  `4 sinh²(δr/2) ∫|f|` (`norm_depthSignal_le`), and every value below that bound is attained by a
  smooth window of unit mass (`exists_depthSignal_ge`). Depth enters an image quadratically when
  `δr ≪ 1` and like `e^{δr}` when `δr ≫ 1`.
-/

open MeasureTheory Complex
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 RHTower

/-! ### Windows -/

/-- Windows of aperture `r`: `C²` and supported in `[−r, r]`. -/
def ApertureWindow (r : ℝ) (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ 2 f ∧ tsupport f ⊆ Set.Icc (-r) r

theorem ApertureWindow.hasCompactSupport {r : ℝ} {f : ℝ → ℂ} (hf : ApertureWindow r f) :
    HasCompactSupport f :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hf.2

theorem ApertureWindow.add_smul {r : ℝ} {f g : ℝ → ℂ} (hf : ApertureWindow r f)
    (hg : ApertureWindow r g) (c : ℂ) : ApertureWindow r fun u => f u + c * g u :=
  ⟨hf.1.add (contDiff_const.mul hg.1), (tsupport_add _ _).trans
    (Set.union_subset hf.2 ((tsupport_mul_subset_right (f := fun _ => c)).trans hg.2))⟩

/-! ### Depth is tilt -/

/-- The window `f` tilted by `e^{δu}`. -/
def tilt (δ : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun u => f u * (Real.exp (δ * u) : ℂ)

/-- The depth `β − ½` of a point `ρ = β + iγ`. -/
def depth (ρ : ℂ) : ℝ := ρ.re - 1 / 2

theorem gammaOf_eq (ρ : ℂ) : gammaOf ρ = (ρ.im : ℂ) - I * (depth ρ : ℂ) := by
  apply Complex.ext <;> simp [gammaOf, depth]

theorem depth_reflect (ρ : ℂ) : depth (reflect ρ) = -depth ρ := by
  simp only [depth, reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]; ring

theorem im_reflect (ρ : ℂ) : (reflect ρ).im = ρ.im := by
  simp [reflect]

/-- **Depth is tilt.** A vertical displacement by `−iδ` is the tilt `e^{δu}` of the window. -/
theorem paperFT_sub_I_mul_eq_tilt (f : ℝ → ℂ) (x δ : ℝ) :
    paperFT f ((x : ℂ) - I * δ) = paperFT (tilt δ f) x :=
  paperFT_sub_I_mul f x δ

/-- **Every zero is a real point of its tilted camera.** -/
theorem paperFT_gammaOf (f : ℝ → ℂ) (ρ : ℂ) :
    paperFT f (gammaOf ρ) = paperFT (tilt (depth ρ) f) ρ.im := by
  rw [gammaOf_eq]; exact paperFT_sub_I_mul f _ _

/-- **The Gram block of a zero is the rank-one block of its tilted camera.** In the matrix explicit
formula of `Zeta23`, the summand of `ρ` at the grid points `τ_k, τ_l` is the product of the two
evaluations of the `(β − ½)`-tilted taper at the real offsets `γ − τ_k`, `γ − τ_l`. -/
theorem Gsummand_eq_tilted (Z : ZeroConfig) (P : Params) (T : ℝ) (k l : ℤ) (ρ : ℂ) :
    Z.Gsummand P T k l ρ = (Z.mult ρ : ℂ) *
      paperFT (tilt (depth ρ) fun u => (P.phi T u : ℂ)) ((ρ.im - P.tau T k : ℝ) : ℂ) *
      paperFT (tilt (depth ρ) fun u => (P.phi T u : ℂ)) ((ρ.im - P.tau T l : ℝ) : ℂ) := by
  have h : ∀ j : ℤ, P.phiHat T (gammaOf ρ - P.tau T j) =
      paperFT (tilt (depth ρ) fun u => (P.phi T u : ℂ)) ((ρ.im - P.tau T j : ℝ) : ℂ) := fun j => by
    rw [Params.phiHat, gammaOf_eq, show (ρ.im : ℂ) - I * (depth ρ : ℂ) - (P.tau T j : ℂ) =
      ((ρ.im - P.tau T j : ℝ) : ℂ) - I * (depth ρ : ℂ) by push_cast; ring]
    exact paperFT_sub_I_mul _ _ _
  rw [ZeroConfig.Gsummand, h k, h l]

/-! ### Pairs -/

theorem integrable_mul_cexp {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) :
    Integrable fun u : ℝ => g u * cexp (I * z * u) :=
  (hg.mul (by fun_prop)).integrable_of_hasCompactSupport (hgc.mul_right)

/-- **Pairs are analytic in the squared gap.** For every complex `w` the two points `c ± w` are
seen together as the centre `c` through the window `2cos(wu)·f`, an even function of `w`. -/
theorem paperFT_add_add_sub {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (c w : ℂ) :
    paperFT f (c + w) + paperFT f (c - w) =
      paperFT (fun u => 2 * Complex.cos (w * u) * f u) c := by
  rw [paperFT_def, paperFT_def, paperFT_def, ← integral_add (integrable_mul_cexp hf hfc _)
    (integrable_mul_cexp hf hfc _)]
  congr 1 with u
  rw [Complex.two_cos, show I * (c + w) * u = I * c * u + w * u * I by ring,
    show I * (c - w) * u = I * c * u + -(w * u) * I by ring, Complex.exp_add, Complex.exp_add]
  ring

/-- **An off-line pair is its real centre seen through `2cosh(δu)`.** -/
theorem paperFT_pair_eq_cosh {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (x δ : ℝ) :
    paperFT f ((x : ℂ) - I * δ) + paperFT f ((x : ℂ) + I * δ) =
      paperFT (fun u => ((2 * Real.cosh (δ * u) : ℝ) : ℂ) * f u) x := by
  have h := paperFT_add_add_sub hf hfc (x : ℂ) (-(I * δ))
  rw [← sub_eq_add_neg, sub_neg_eq_add] at h
  rw [h]
  congr 1 with u
  rw [show -(I * (δ : ℂ)) * (u : ℂ) = -(((δ * u : ℝ) : ℂ) * I) by push_cast; ring,
    Complex.cos_neg, Complex.cos_mul_I]
  push_cast; ring

/-- A real pair `c ± Δ` is its centre seen through `2cos(Δu)`. -/
theorem paperFT_realPair_eq_cos {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (c Δ : ℝ) :
    paperFT f ((c : ℂ) + Δ) + paperFT f ((c : ℂ) - Δ) =
      paperFT (fun u => ((2 * Real.cos (Δ * u) : ℝ) : ℂ) * f u) c := by
  rw [paperFT_add_add_sub hf hfc]
  congr 1 with u
  push_cast; ring

/-- **The FE pair of a zero.** `ρ` and `1 − ρ̄` are the real ordinate seen through
`2cosh((β − ½)u)`. -/
theorem paperFT_gammaOf_add_reflect {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (ρ : ℂ) :
    paperFT f (gammaOf ρ) + paperFT f (gammaOf (reflect ρ)) =
      paperFT (fun u => ((2 * Real.cosh (depth ρ * u) : ℝ) : ℂ) * f u) ρ.im := by
  rw [gammaOf_eq ρ, gammaOf_eq (reflect ρ), depth_reflect, im_reflect,
    show (ρ.im : ℂ) - I * ((-depth ρ : ℝ) : ℂ) = (ρ.im : ℂ) + I * (depth ρ : ℂ) by push_cast; ring]
  exact paperFT_pair_eq_cosh hf hfc _ _

/-! ### The depth signal -/

/-- The **depth signal** of a pair of depth `δ` at the real centre `x`: the pair minus the doubled
centre. -/
def depthSignal (f : ℝ → ℂ) (x δ : ℝ) : ℂ :=
  paperFT f ((x : ℂ) - I * δ) + paperFT f ((x : ℂ) + I * δ) - 2 * paperFT f x

theorem two_cosh_sub_two (y : ℝ) : 2 * Real.cosh y - 2 = 4 * Real.sinh (y / 2) ^ 2 := by
  have h := Real.cosh_two_mul (y / 2)
  rw [show 2 * (y / 2) = y by ring] at h
  rw [h, Real.cosh_sq]; ring

/-- **The depth signal is the centre seen through `4 sinh²(δu/2)`.** -/
theorem depthSignal_eq {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (x δ : ℝ) :
    depthSignal f x δ =
      paperFT (fun u => ((4 * Real.sinh (δ * u / 2) ^ 2 : ℝ) : ℂ) * f u) x := by
  have hc : Continuous fun u : ℝ => ((2 * Real.cosh (δ * u) : ℝ) : ℂ) * f u := by fun_prop
  rw [depthSignal, paperFT_pair_eq_cosh hf hfc, paperFT_def, paperFT_def, paperFT_def,
    ← integral_const_mul,
    ← integral_sub (integrable_mul_cexp hc (hfc.mul_left) _)
      ((integrable_mul_cexp hf hfc _).const_mul _)]
  congr 1 with u
  rw [show δ * u / 2 = (δ * u) / 2 by ring, ← two_cosh_sub_two]
  push_cast; ring

theorem sinh_sq_le_sinh_sq {a b : ℝ} (h : |a| ≤ |b|) : Real.sinh a ^ 2 ≤ Real.sinh b ^ 2 := by
  rw [Real.sinh_sq, Real.sinh_sq]
  have hc := Real.cosh_le_cosh.mpr h
  nlinarith [Real.one_le_cosh a]

/-- **The depth signal is at most `4 sinh²(δr/2)` per unit mass at aperture `r`.** -/
theorem norm_depthSignal_le {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) {r : ℝ}
    (hsupp : tsupport f ⊆ Set.Icc (-r) r) (x δ : ℝ) :
    ‖depthSignal f x δ‖ ≤ 4 * Real.sinh (δ * r / 2) ^ 2 * ∫ u, ‖f u‖ := by
  rw [depthSignal_eq hf hfc, paperFT_def, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((hf.norm.integrable_of_hasCompactSupport hfc.norm).const_mul _)
    (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_mul, norm_mul, show I * (x : ℂ) * (u : ℂ) = ((x * u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  by_cases hu : f u = 0
  · rw [hu, norm_zero, mul_zero, mul_zero]
  · obtain ⟨h1, h2⟩ := hsupp (subset_tsupport _ hu)
    have hur : |u| ≤ |r| := (abs_le.mpr ⟨h1, h2⟩).trans (le_abs_self r)
    have hr : |δ * u / 2| ≤ |δ * r / 2| := by
      rw [abs_div, abs_div, abs_mul, abs_mul]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hur (abs_nonneg δ))
        (by norm_num)
    exact mul_le_mul_of_nonneg_right (by nlinarith [sinh_sq_le_sinh_sq hr]) (norm_nonneg _)

/-- **The depth signal bound is sharp.** For `0 ≤ s < r` there is a smooth window of unit mass,
supported in `[−r, r]`, whose depth signal at `x` is at least `4 sinh²(δs/2)`: a normalized bump
on `[s, r]` modulated to the height `x`. -/
theorem exists_depthSignal_ge {r s : ℝ} (hs : 0 ≤ s) (hsr : s < r) (x δ : ℝ) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ tsupport f ⊆ Set.Icc (-r) r ∧
      ∫ u, ‖f u‖ = 1 ∧ 4 * Real.sinh (δ * s / 2) ^ 2 ≤ ‖depthSignal f x δ‖ := by
  let b : ContDiffBump ((s + r) / 2) := ⟨(r - s) / 4, (r - s) / 2, by linarith, by linarith⟩
  let B : ℝ → ℝ := b.normed volume
  have hB0 : ∀ u, 0 ≤ B u := b.nonneg_normed
  have hrO : b.rOut = (r - s) / 2 := rfl
  have hBs : ∀ u, B u ≠ 0 → s < u ∧ u < r := fun u hu => by
    have : u ∈ Function.support B := hu
    rw [b.support_normed_eq, Metric.mem_ball, Real.dist_eq, abs_lt, hrO] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hBc : Continuous B := b.continuous_normed
  have hBcs : HasCompactSupport B := b.hasCompactSupport_normed
  let f : ℝ → ℂ := fun u => (B u : ℂ) * cexp (-(I * x * u))
  have hfc : Continuous f := by fun_prop
  have hfcs : HasCompactSupport f := (hBcs.comp_left Complex.ofReal_zero).mul_right
  have hnorm : ∀ u, ‖f u‖ = B u := fun u => by
    rw [norm_mul, show -(I * (x : ℂ) * (u : ℂ)) = ((-(x * u) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hB0 u)]
  have hBint : Integrable B := b.integrable_normed
  refine ⟨f, ?_, hfcs, ?_, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp b.contDiff_normed).mul
      ((contDiff_const.mul Complex.ofRealCLM.contDiff).neg.cexp)
  · intro u hu
    have hu' : u ∈ tsupport B := by
      refine (tsupport_mul_subset_left (f := fun u => (B u : ℂ))) hu |> fun h => ?_
      exact (tsupport_comp_subset (g := fun y : ℝ => (y : ℂ)) Complex.ofReal_zero B) h
    rw [b.tsupport_normed_eq, Metric.mem_closedBall, Real.dist_eq, abs_le, hrO] at hu'
    exact ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
  · simp_rw [hnorm]; exact b.integral_normed
  · rw [depthSignal_eq hfc hfcs, paperFT_def]
    have hval : ∀ u : ℝ, ((4 * Real.sinh (δ * u / 2) ^ 2 : ℝ) : ℂ) * f u * cexp (I * x * u) =
        ((4 * Real.sinh (δ * u / 2) ^ 2 * B u : ℝ) : ℂ) := fun u => by
      simp only [f]
      rw [show ((4 * Real.sinh (δ * u / 2) ^ 2 : ℝ) : ℂ) * ((B u : ℂ) * cexp (-(I * x * u))) *
          cexp (I * x * u) = ((4 * Real.sinh (δ * u / 2) ^ 2 : ℝ) : ℂ) * (B u : ℂ) *
          (cexp (-(I * x * u)) * cexp (I * x * u)) by ring, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, mul_one]
      push_cast; ring
    simp_rw [hval]
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs]
    have hmono : ∫ u, 4 * Real.sinh (δ * s / 2) ^ 2 * B u ≤
        ∫ u, 4 * Real.sinh (δ * u / 2) ^ 2 * B u := by
      refine integral_mono (hBint.const_mul _)
        ((((by fun_prop : Continuous fun u : ℝ => 4 * Real.sinh (δ * u / 2) ^ 2).mul hBc)
          ).integrable_of_hasCompactSupport hBcs.mul_left) fun u => ?_
      by_cases hu : B u = 0
      · simp [hu]
      · obtain ⟨h1, -⟩ := hBs u hu
        have : |δ * s / 2| ≤ |δ * u / 2| := by
          rw [abs_div, abs_div, abs_mul, abs_mul]
          rw [abs_of_nonneg hs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u)]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1.le (abs_nonneg δ))
            (by norm_num)
        exact mul_le_mul_of_nonneg_right (by nlinarith [sinh_sq_le_sinh_sq this]) (hB0 u)
    rw [integral_const_mul, b.integral_normed, mul_one] at hmono
    exact hmono.trans (le_abs_self _)

end GaloisForLFunctions.ZeroConfigurationGeometry
