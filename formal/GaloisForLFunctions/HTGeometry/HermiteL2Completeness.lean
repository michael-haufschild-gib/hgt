import GaloisForLFunctions.HTGeometry.HermiteL2Moments
import GaloisForLFunctions.HTGeometry.SchwartzProduct

/-!
# Completeness of the Hermite system in `L²(ℝ)`

The Gaussian multiple of an `L²` function orthogonal to every Hermite function has vanishing
Fourier transform, because the Fourier transform is the exponential integral at an imaginary
exponent.  The self-adjointness of the Fourier transform then turns that into the vanishing of the
integral against every Schwartz function, since the Fourier transform is onto the Schwartz space.
Schwartz functions are dense in `L²`, so the Gaussian multiple vanishes, and the Gaussian is
nowhere zero.

So the Hermite functions are a complete orthogonal system in `L²(ℝ)`: the only `L²` function
orthogonal to all of them is zero.  This is the input that turns the Hermite expansion of a
Schwartz function into an identity.

* `l2GaussMul` : the Gaussian multiple of an `L²` function.
* `fourier_l2GaussMul_eq_zero` : its Fourier transform vanishes.
* `integral_l2GaussMul_schwartz_eq_zero` : it integrates to zero against every Schwartz function.
* `hermite_l2_complete` : **an `L²` function orthogonal to every Hermite function is zero.**
-/

open scoped Real SchwartzMap FourierTransform
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

variable {u : Lp ℂ 2 (volume : Measure ℝ)}

/-! ## The Gaussian multiple -/

/-- The Gaussian multiple of an `L²` function. -/
def l2GaussMul (u : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ :=
  fun x => (u : ℝ → ℂ) x * ((gaussReal x : ℝ) : ℂ)

theorem memLp_gaussReal_complex :
    MemLp (fun x : ℝ => ((gaussReal x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
  have h := gaussianSchwartz.memLp 2 (volume : Measure ℝ)
  have hfun : (⇑gaussianSchwartz : ℝ → ℂ) = fun x : ℝ => ((gaussReal x : ℝ) : ℂ) :=
    funext fun x => gaussianSchwartz_apply x
  rwa [hfun] at h

theorem aestronglyMeasurable_l2GaussMul :
    AEStronglyMeasurable (l2GaussMul u) (volume : Measure ℝ) :=
  (Lp.memLp u).aestronglyMeasurable.mul
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))).aestronglyMeasurable

theorem memLp_l2GaussMul : MemLp (l2GaussMul u) 2 (volume : Measure ℝ) := by
  refine (Lp.memLp u).of_le aestronglyMeasurable_l2GaussMul ?_
  filter_upwards with x
  have hg : ‖((gaussReal x : ℝ) : ℂ)‖ = gaussReal x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussReal_pos x)]
  rw [l2GaussMul, norm_mul, hg]
  calc ‖(u : ℝ → ℂ) x‖ * gaussReal x ≤ ‖(u : ℝ → ℂ) x‖ * 1 :=
        mul_le_mul_of_nonneg_left (gaussReal_le_one x) (norm_nonneg _)
    _ = ‖(u : ℝ → ℂ) x‖ := mul_one _

theorem integrable_l2GaussMul : Integrable (l2GaussMul u) (volume : Measure ℝ) := by
  have hmul : MemLp ((u : ℝ → ℂ) * fun x : ℝ => ((gaussReal x : ℝ) : ℂ)) 1
      (volume : Measure ℝ) := memLp_gaussReal_complex.mul (Lp.memLp u)
  have hint := memLp_one_iff_integrable.mp hmul
  have hfun : ((u : ℝ → ℂ) * fun x : ℝ => ((gaussReal x : ℝ) : ℂ)) = l2GaussMul u := rfl
  rwa [hfun] at hint

/-! ## The Fourier transform of the Gaussian multiple -/

/-- **The Fourier transform of the Gaussian multiple vanishes**, for an `L²` function orthogonal
to every Hermite function: it is the exponential integral at an imaginary exponent. -/
theorem fourier_l2GaussMul_eq_zero
    (hu : ∀ n : ℕ, inner ℂ ((hermiteSchwartz n).toLp 2 (volume : Measure ℝ)) u = 0) (t : ℝ) :
    𝓕 (l2GaussMul u) t = 0 := by
  have hexp := integral_gaussMul_exp_l2_eq_zero hu (-(2 * (π : ℂ) * t) * Complex.I)
  rw [Real.fourier_eq', ← hexp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, l2GaussMul]
  have hinner : (inner ℝ x t : ℝ) = x * t := Real.inner_apply x t
  rw [hinner]
  have hexpeq : Complex.exp ((((-2 * π * (x * t) : ℝ)) : ℂ) * Complex.I)
      = Complex.exp (-(2 * (π : ℂ) * t) * Complex.I * x) := by
    congr 1
    push_cast
    ring
  rw [hexpeq]
  ring

/-- Every Schwartz function is the Fourier transform of a Schwartz function. -/
theorem exists_schwartz_fourier_eq (g : 𝓢(ℝ, ℂ)) :
    ∃ h : 𝓢(ℝ, ℂ), 𝓕 (h : ℝ → ℂ) = (g : ℝ → ℂ) := by
  refine ⟨𝓕⁻ g, ?_⟩
  rw [← SchwartzMap.fourier_coe]
  congr 1
  exact FourierTransform.fourier_fourierInv_eq g

/-- **The Gaussian multiple integrates to zero against every Schwartz function.**  The Fourier
transform is self-adjoint for the integral pairing and maps the Schwartz space onto itself, so the
vanishing of the Fourier transform transfers to the whole Schwartz space. -/
theorem integral_l2GaussMul_schwartz_eq_zero
    (hu : ∀ n : ℕ, inner ℂ ((hermiteSchwartz n).toLp 2 (volume : Measure ℝ)) u = 0)
    (g : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, l2GaussMul u x * g x = 0 := by
  obtain ⟨h, hh⟩ := exists_schwartz_fourier_eq g
  have hkey : ∫ ξ : ℝ, 𝓕 (l2GaussMul u) ξ • (h : ℝ → ℂ) ξ
      = ∫ x : ℝ, l2GaussMul u x • 𝓕 (h : ℝ → ℂ) x := by
    simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner (integrable_l2GaussMul (u := u)) h.integrable
  have hzero : ∫ ξ : ℝ, 𝓕 (l2GaussMul u) ξ • (h : ℝ → ℂ) ξ = 0 := by
    have hfun : (fun ξ : ℝ => 𝓕 (l2GaussMul u) ξ • (h : ℝ → ℂ) ξ) = fun _ : ℝ => (0 : ℂ) := by
      funext ξ
      rw [fourier_l2GaussMul_eq_zero hu ξ, zero_smul]
    rw [hfun, integral_zero]
  rw [hzero, hh] at hkey
  have hfun : (fun x : ℝ => l2GaussMul u x • (g : ℝ → ℂ) x)
      = fun x : ℝ => l2GaussMul u x * g x := by
    funext x
    rw [smul_eq_mul]
  rw [hfun] at hkey
  exact hkey.symm

/-! ## Completeness -/

/-- **The Hermite functions are a complete system in `L²(ℝ)`**: an `L²` function orthogonal to
every Hermite function is zero. -/
theorem hermite_l2_complete
    (hu : ∀ n : ℕ, inner ℂ ((hermiteSchwartz n).toLp 2 (volume : Measure ℝ)) u = 0) : u = 0 := by
  set v : Lp ℂ 2 (volume : Measure ℝ) :=
    MemLp.toLp (l2GaussMul u) (memLp_l2GaussMul (u := u)) with hv
  have hortho : ∀ g : 𝓢(ℝ, ℂ), inner ℂ (g.toLp 2 (volume : Measure ℝ)) v = 0 := by
    intro g
    rw [MeasureTheory.L2.inner_def]
    have hzero := integral_l2GaussMul_schwartz_eq_zero hu (SchwartzMap.conjSLM g)
    rw [← hzero]
    refine integral_congr_ae ?_
    filter_upwards [SchwartzMap.coeFn_toLp g 2 (volume : Measure ℝ),
      (memLp_l2GaussMul (u := u)).coeFn_toLp] with x hx hy
    rw [hx, hy, RCLike.inner_apply, SchwartzMap.conjSLM_apply, mul_comm]
  have hv0 : v = 0 := by
    have hd : DenseRange (SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 (volume : Measure ℝ)) :=
      SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
    have hfun : (fun y : Lp ℂ 2 (volume : Measure ℝ) => (inner ℂ y v : ℂ)) = fun _ => 0 := by
      refine hd.equalizer ?_ continuous_const ?_
      · exact ((innerSL ℂ (E := Lp ℂ 2 (volume : Measure ℝ))).flip v).continuous
      · funext g
        exact hortho g
    have hself := congrFun hfun v
    simpa using hself
  have hae : l2GaussMul u =ᵐ[(volume : Measure ℝ)] 0 := by
    have h1 : (v : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)] 0 := Lp.eq_zero_iff_ae_eq_zero.mp hv0
    have h2 : (v : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)] l2GaussMul u :=
      (memLp_l2GaussMul (u := u)).coeFn_toLp
    filter_upwards [h1, h2] with x hx hy
    rw [← hy, hx]
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  filter_upwards [hae] with x hx
  have hg : ((gaussReal x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (gaussReal_pos x).ne'
  have hx' : (u : ℝ → ℂ) x * ((gaussReal x : ℝ) : ℂ) = 0 := hx
  exact (mul_eq_zero.mp hx').resolve_right hg

end GaloisForLFunctions

end
