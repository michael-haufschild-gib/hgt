import GaloisForLFunctions.RHTower.SelbergModularPotentialGreen
import GaloisForLFunctions.RHTower.MaassConverseAutomorphy

/-!
# Green's formula for functions invariant under `z ↦ z + 1` and `z ↦ −1/z`

Let `V` be invariant under `S(z) = −1/z` on the upper half-plane.  The chain rule gives
`DV(z)v = DV(Sz)(v/z²)` (`fderiv_apply_of_invS`), with two consequences:

* the radial derivative is anti-invariant, `DV(z)z = −DV(Sz)(Sz)` (`fderiv_radial_invS`);
* the gradient density `y²(|∂ₓV|² + |∂ᵧV|²)` is `S`-invariant (`gradDensity_invS`), because a
  real-linear map `L : ℂ → ℂ` satisfies `|L c|² + |L(ic)|² = |c|²(|L 1|² + |L i|²)`.

On the unit circle `S(x + iy) = −x + iy` (`invS_point`), so the radial anti-invariance is the
matching condition of the oriented circular currents in the planar Green formula on the truncated
modular domain, and invariance under `z ↦ z + 1` matches the side currents (`fderiv_side`).  For an
invariant `C²` potential the Green formula leaves only the top current
(`area_laplacian_eq_top_of_invariant`).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ContDiff

noncomputable section

namespace RHTower.ModularInversionGreen

open MaassAxisContinuation MaassBesselSeries
open GaloisForLFunctions.RHTower.SelbergMaassMean GaloisForLFunctions.RHTower.SelbergMaassTraceEnergy
  GaloisForLFunctions.RHTower.SelbergModularPotentialGreen
  GaloisForLFunctions.RHTower.SelbergModularDomainSlices

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The chain rule for `S` -/

theorem hasFDerivAt_invS {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt invS ((ContinuousLinearMap.toSpanSingleton ℂ (z ^ 2)⁻¹).restrictScalars ℝ) z := by
  have hd : HasDerivAt invS (z ^ 2)⁻¹ z := by
    rw [← deriv_invS]
    exact ((contDiffAt_invS hz).differentiableAt (by simp)).hasDerivAt
  exact hd.hasFDerivAt.restrictScalars ℝ

/-- `DV(z)v = DV(Sz)(v/z²)` for `S`-invariant `V`. -/
theorem fderiv_apply_of_invS {V : ℂ → E} {z : ℂ} (hz : 0 < z.im)
    (hV : DifferentiableAt ℝ V (invS z)) (hinv : ∀ w : ℂ, 0 < w.im → V (invS w) = V w) (v : ℂ) :
    fderiv ℝ V z v = fderiv ℝ V (invS z) (v * (z ^ 2)⁻¹) := by
  have hz0 : z ≠ 0 := ne_zero_of_mem_upper hz
  have hc := hV.hasFDerivAt.comp z (hasFDerivAt_invS hz0)
  have he : (V ∘ invS) =ᶠ[𝓝 z] V := by
    filter_upwards [isOpen_upper.mem_nhds hz] with w hw
    exact hinv w hw
  rw [← he.fderiv_eq, hc.fderiv]
  simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- **Radial anti-invariance:** `DV(z)z = −DV(Sz)(Sz)`. -/
theorem fderiv_radial_invS {V : ℂ → E} {z : ℂ} (hz : 0 < z.im)
    (hV : DifferentiableAt ℝ V (invS z)) (hinv : ∀ w : ℂ, 0 < w.im → V (invS w) = V w) :
    fderiv ℝ V z z = -fderiv ℝ V (invS z) (invS z) := by
  have hz0 : z ≠ 0 := ne_zero_of_mem_upper hz
  rw [fderiv_apply_of_invS hz hV hinv z, show z * (z ^ 2)⁻¹ = -invS z by
    unfold invS; field_simp, map_neg]

/-- `S(x + iy) = −x + iy` on the unit circle. -/
theorem invS_point {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) : invS (point x y) = point (-x) y := by
  have hmul : point x y * point x (-y) = 1 := by
    apply Complex.ext <;> simp [point] <;> nlinarith [hxy]
  unfold invS
  rw [inv_eq_of_mul_eq_one_right hmul]
  apply Complex.ext <;> simp [point]

/-- `L(x + iy) = x L 1 + y L i`. -/
theorem apply_point (L : ℂ →L[ℝ] E) (x y : ℝ) : L (point x y) = x • L 1 + y • L I := by
  have h : point x y = x • (1 : ℂ) + y • I := by
    simp [point, Complex.real_smul]
  rw [h, map_add, map_smul, map_smul]

/-- Translation invariance matches the derivatives on the two sides `x = ±1/2`. -/
theorem fderiv_side {V : ℂ → E} (hT : ∀ w : ℂ, 0 < w.im → V (w + 1) = V w) {y : ℝ} (hy : 0 < y) :
    fderiv ℝ V (point (1 / 2) y) = fderiv ℝ V (point (-(1 / 2)) y) := by
  have hp : 0 < (point (-(1 / 2)) y).im := by simpa [point] using hy
  have he : (fun w => V (w + 1)) =ᶠ[𝓝 (point (-(1 / 2)) y)] V := by
    filter_upwards [isOpen_upper.mem_nhds hp] with w hw
    exact hT w hw
  rw [← he.fderiv_eq, fderiv_comp_add_right]
  congr 1
  simp only [point]
  push_cast
  ring

/-! ## The gradient density -/

/-- `|L c|² + |L(ic)|² = |c|²(|L 1|² + |L i|²)` for a real-linear `L : ℂ → ℂ`. -/
theorem normSq_apply_add_normSq_apply_I_mul (L : ℂ →L[ℝ] ℂ) (c : ℂ) :
    Complex.normSq (L c) + Complex.normSq (L (I * c)) =
      Complex.normSq c * (Complex.normSq (L 1) + Complex.normSq (L I)) := by
  have hc : c = c.re • (1 : ℂ) + c.im • I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have hIc : I * c = (-c.im) • (1 : ℂ) + c.re • I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have h1 : L c = c.re • L 1 + c.im • L I := by
    conv_lhs => rw [hc]
    rw [map_add, map_smul, map_smul]
  have h2 : L (I * c) = (-c.im) • L 1 + c.re • L I := by
    rw [hIc, map_add, map_smul, map_smul]
  rw [h1, h2]
  simp only [Complex.real_smul, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The Euclidean gradient density `|∂ₓV|² + |∂ᵧV|²`. -/
def gradDensity (V : ℂ → ℂ) (z : ℂ) : ℝ :=
  Complex.normSq (fderiv ℝ V z 1) + Complex.normSq (fderiv ℝ V z I)

theorem gradDensity_nonneg (V : ℂ → ℂ) (z : ℂ) : 0 ≤ gradDensity V z :=
  add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- **The hyperbolic gradient density `y²(|∂ₓV|² + |∂ᵧV|²)` is `S`-invariant.** -/
theorem gradDensity_invS {V : ℂ → ℂ} {z : ℂ} (hz : 0 < z.im)
    (hV : DifferentiableAt ℝ V (invS z)) (hinv : ∀ w : ℂ, 0 < w.im → V (invS w) = V w) :
    (invS z).im ^ 2 * gradDensity V (invS z) = z.im ^ 2 * gradDensity V z := by
  have hz0 : z ≠ 0 := ne_zero_of_mem_upper hz
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
  have hg : gradDensity V z =
      Complex.normSq (z ^ 2)⁻¹ * gradDensity V (invS z) := by
    unfold gradDensity
    rw [fderiv_apply_of_invS hz hV hinv 1, fderiv_apply_of_invS hz hV hinv I, one_mul,
      normSq_apply_add_normSq_apply_I_mul]
  rw [hg, invS_im, map_inv₀, map_pow]
  field_simp

/-! ## Green's formula for an invariant potential -/

/-- **Green's formula for an `S`- and `T`-invariant `C²` potential:** only the top current
survives. -/
theorem area_laplacian_eq_top_of_invariant (P : ℂ → ℝ) (hP : ContDiffOn ℝ 2 P {z : ℂ | 0 < z.im})
    (hT : ∀ w : ℂ, 0 < w.im → P (w + 1) = P w) (hS : ∀ w : ℂ, 0 < w.im → P (invS w) = P w)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, realLaplacian P (point p.1 p.2)) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), currentAt P I x Y := by
  have hdiff : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ P w := fun w hw =>
    (hP.contDiffAt (isOpen_upper.mem_nhds hw)).differentiableAt (by norm_num)
  refine area_laplacian_eq_top P hP (fun {y} hy => ?_) (fun {x y} hy hxy => ?_) hY
  · unfold currentAt dir
    rw [fderiv_side hT hy]
  · have hp : 0 < (point x y).im := by simpa [point] using hy
    have hr := fderiv_radial_invS hp (hdiff _ (invS_mem_upper hp)) hS
    rw [invS_point (by simpa using hxy), apply_point, apply_point] at hr
    simp only [smul_eq_mul] at hr
    unfold currentAt dir
    have key : x * (fderiv ℝ P (point (-x) y) 1 - fderiv ℝ P (point x y) 1) -
        y * fderiv ℝ P (point (-x) y) I - y * fderiv ℝ P (point x y) I = 0 := by
      linear_combination -hr
    have hy0 : y ≠ 0 := hy.ne'
    calc x / y * (fderiv ℝ P (point (-x) y) 1 - fderiv ℝ P (point x y) 1) -
          fderiv ℝ P (point (-x) y) I - fderiv ℝ P (point x y) I
        = (x * (fderiv ℝ P (point (-x) y) 1 - fderiv ℝ P (point x y) 1) -
            y * fderiv ℝ P (point (-x) y) I - y * fderiv ℝ P (point x y) I) / y := by
          field_simp
      _ = 0 := by rw [key, zero_div]

end RHTower.ModularInversionGreen
