import GaloisForLFunctions.RHTower.DeningerMeyerRapidDecayLanding

/-!
# Paugam's reciprocal operator on the value-level Meyer quotient proxy

Paugam's symplectic construction starts from the weight-one reciprocal
operator

`Jg(x) = x⁻¹ g(x⁻¹)`

on the positive idele-class ray.  This file constructs that exact operator
on the support-corrected value-level rapid target from
`DeningerMeyerRapidDecayLanding`.

The hard analytic point is proved rather than postulated: `J` exchanges the
two rapid-decay ends.  The small-end estimate with exponent `1-a` becomes
the large-end estimate with exponent `a`, and conversely.  Fourier
inversion and the Meyer--Poisson reflection law then show that `J` maps
actual Poisson boundaries to actual Poisson boundaries.  Consequently it
descends to an involution on that quotient proxy.  It does not establish
preservation of the full all-derivative Bruhat--Schwartz target; that stronger
theorem is proved in `DeningerMeyerStrongLogTarget`.

This supplies Paugam's reciprocal duality operator on the radial quotient.
It does not manufacture the subsequent convolution nuclear trace or the
upper/lower spectral splitting: those belong to the full idele-class
spectral realization and remain distinct infrastructure.

No Riemann-hypothesis premise, positivity assumption, numerical
computation, or abstract pairing hypothesis occurs.
-/

open Complex Filter Topology MeasureTheory Set
open scoped SchwartzMap FourierTransform
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Reciprocal operator and rapid decay -/

/-- Paugam's weight-one reciprocal operator, extended by zero off the positive ray. -/
def deningerMeyerPaugamJFun (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then ((x⁻¹ : ℝ) : ℂ) * g x⁻¹ else 0

@[simp]
theorem deningerMeyerPaugamJFun_of_pos
    (g : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    deningerMeyerPaugamJFun g x =
      ((x⁻¹ : ℝ) : ℂ) * g x⁻¹ := by
  simp [deningerMeyerPaugamJFun, hx]

@[simp]
theorem deningerMeyerPaugamJFun_of_nonpos
    (g : ℝ → ℂ) {x : ℝ} (hx : x ≤ 0) :
    deningerMeyerPaugamJFun g x = 0 := by
  simp [deningerMeyerPaugamJFun, not_lt.mpr hx]

/-- Reciprocal reflection preserves continuity on the positive ray. -/
theorem continuousOn_deningerMeyerPaugamJFun
    {g : ℝ → ℂ} (hg : ContinuousOn g (Ioi 0)) :
    ContinuousOn (deningerMeyerPaugamJFun g) (Ioi 0) := by
  have hbase :
      ContinuousOn
        (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ) * g x⁻¹)
        (Ioi 0) := by
    intro x hx
    have hxpos : 0 < x := hx
    have hinvpos : 0 < x⁻¹ := inv_pos.mpr hxpos
    have hinv : ContinuousAt (fun y : ℝ => y⁻¹) x :=
      continuousAt_inv₀ hxpos.ne'
    have hcast :
        ContinuousAt (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ)) x :=
      Complex.continuous_ofReal.continuousAt.comp hinv
    have hgAt : ContinuousAt g x⁻¹ :=
      (hg x⁻¹ hinvpos).continuousAt
        (Ioi_mem_nhds hinvpos)
    exact
      (hcast.mul (hgAt.comp hinv)).continuousWithinAt
  exact hbase.congr fun x hx => by
    have hxpos : 0 < x := hx
    simp [deningerMeyerPaugamJFun, hxpos]

/--
The small-end exponent `1-a` transforms into the large-end exponent `a`
under Paugam's weight-one reciprocal operator.
-/
theorem deningerMeyerPaugamJFun_isBigO_atTop
    {g : ℝ → ℂ} (hg : RapidDecayRay g) (a : ℝ) :
    deningerMeyerPaugamJFun g =O[atTop]
      fun x : ℝ => x ^ (-a) := by
  have hcomp :=
    (hg.decayZero (1 - a)).comp_tendsto
      (tendsto_inv_atTop_nhdsGT_zero :
        Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝[>] 0))
  change (fun x : ℝ => g x⁻¹) =O[atTop]
    (fun x : ℝ => (x⁻¹) ^ (-(1 - a))) at hcomp
  have hweight :
      (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)) =O[atTop]
        (fun x : ℝ => x⁻¹) := by
    apply Filter.Eventually.isBigO
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hx)]
  have hmul := hweight.mul hcomp
  apply hmul.congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [deningerMeyerPaugamJFun, hx]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : 0 ≤ x := hx.le
    rw [show x⁻¹ = x ^ (-1 : ℝ) by
      exact (Real.rpow_neg_one x).symm]
    rw [← Real.rpow_mul hx0]
    rw [← Real.rpow_add hx]
    congr 1
    ring

/--
The large-end exponent `1-b` transforms into the small-end exponent `b`
under Paugam's weight-one reciprocal operator.
-/
theorem deningerMeyerPaugamJFun_isBigO_zero
    {g : ℝ → ℂ} (hg : RapidDecayRay g) (b : ℝ) :
    deningerMeyerPaugamJFun g =O[𝓝[>] 0]
      fun x : ℝ => x ^ (-b) := by
  have hcomp :=
    (hg.decayTop (1 - b)).comp_tendsto
      (tendsto_inv_nhdsGT_zero :
        Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) atTop)
  change (fun x : ℝ => g x⁻¹) =O[𝓝[>] 0]
    (fun x : ℝ => (x⁻¹) ^ (-(1 - b))) at hcomp
  have hweight :
      (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)) =O[𝓝[>] 0]
        (fun x : ℝ => x⁻¹) := by
    apply Filter.Eventually.isBigO
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hx)]
  have hmul := hweight.mul hcomp
  apply hmul.congr'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := hx
    simp [deningerMeyerPaugamJFun, hxpos]
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : 0 ≤ x := hx.le
    rw [show x⁻¹ = x ^ (-1 : ℝ) by
      exact (Real.rpow_neg_one x).symm]
    rw [← Real.rpow_mul hx0]
    rw [← Real.rpow_add hx]
    congr 1
    ring

/-- Paugam's reciprocal operator preserves the complete rapid-decay condition. -/
theorem rapidDecayRay_deningerMeyerPaugamJFun
    {g : ℝ → ℂ} (hg : RapidDecayRay g) :
    RapidDecayRay (deningerMeyerPaugamJFun g) where
  contOn := continuousOn_deningerMeyerPaugamJFun hg.contOn
  decayTop := deningerMeyerPaugamJFun_isBigO_atTop hg
  decayZero := deningerMeyerPaugamJFun_isBigO_zero hg

/-! ## Fourier stability of Meyer's source -/

/-- Fourier transform squared agrees with the source at the zero mode. -/
theorem deningerMeyer_fourier_fourier_zero
    (f : SchwartzMap ℝ ℂ) :
    (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)
      (FourierTransform.fourierCLE ℂ
        (SchwartzMap ℝ ℂ) f)) 0 = f 0 := by
  have h : 𝓕⁻ (𝓕 f) = f :=
    FourierTransform.fourierInv_fourier_eq f
  rw [SchwartzMap.fourierInv_apply_eq] at h
  have h0 := congrArg
    (fun g : SchwartzMap ℝ ℂ => g 0) h
  simpa using h0

/-- Fourier transform preserves Meyer's even two-endpoint source. -/
def deningerMeyerCapFourierLM :
    DeningerMeyerCap →ₗ[ℂ] DeningerMeyerCap where
  toFun f :=
    ⟨FourierTransform.fourierCLE ℂ
        (SchwartzMap ℝ ℂ) f, by
      rw [deningerMeyerCap_mem_iff]
      obtain ⟨heven, hf0, hF0⟩ :=
        (deningerMeyerCap_mem_iff
          (f : SchwartzMap ℝ ℂ)).mp f.property
      exact
        ⟨deningerFourier_even_of_even f heven,
          hF0, by
            rw [deningerMeyer_fourier_fourier_zero]
            exact hf0⟩⟩
  map_add' f g := by
    apply Subtype.ext
    exact (FourierTransform.fourierCLE ℂ
      (SchwartzMap ℝ ℂ)).map_add f g
  map_smul' c f := by
    apply Subtype.ext
    exact (FourierTransform.fourierCLE ℂ
      (SchwartzMap ℝ ℂ)).map_smul c f

/-! ## Descent to the value-level quotient proxy -/

/-- Paugam's `J` as a complex-linear endomorphism of the value-level rapid target. -/
def deningerMeyerPaugamJ :
    DeningerMeyerRapidTarget →ₗ[ℂ]
      DeningerMeyerRapidTarget where
  toFun g :=
    ⟨deningerMeyerPaugamJFun g,
      (mem_deningerMeyerRapidTarget_iff _).2
        ⟨rapidDecayRay_deningerMeyerPaugamJFun
            ((mem_deningerMeyerRapidTarget_iff
              (g : ℝ → ℂ)).mp g.property).1,
          fun x hx => by
            simp [deningerMeyerPaugamJFun,
              not_lt.mpr hx]⟩⟩
  map_add' g h := by
    apply Subtype.ext
    funext x
    by_cases hx : 0 < x
    · simp [deningerMeyerPaugamJFun, hx]
      ring
    · simp [deningerMeyerPaugamJFun, hx]
  map_smul' c g := by
    apply Subtype.ext
    funext x
    by_cases hx : 0 < x
    · simp [deningerMeyerPaugamJFun, hx]
      ring
    · simp [deningerMeyerPaugamJFun, hx]

/-- Paugam's weight-one reciprocal operator is an involution on the target. -/
@[simp]
theorem deningerMeyerPaugamJ_sq
    (g : DeningerMeyerRapidTarget) :
    deningerMeyerPaugamJ
        (deningerMeyerPaugamJ g) = g := by
  apply Subtype.ext
  funext x
  by_cases hx : 0 < x
  · simp [deningerMeyerPaugamJ,
      deningerMeyerPaugamJFun, hx]
    have hxC : (x : ℂ) ≠ 0 := by
      exact_mod_cast hx.ne'
    field_simp
  · have hg0 :
        (g : ℝ → ℂ) x = 0 :=
      ((mem_deningerMeyerRapidTarget_iff
        (g : ℝ → ℂ)).mp g.property).2
          x (not_lt.mp hx)
    simp [deningerMeyerPaugamJ,
      deningerMeyerPaugamJFun, hx, hg0]

/--
Meyer--Poisson reflection identifies a Fourier-transformed boundary under
`J` with the original boundary.
-/
@[simp]
theorem deningerMeyerPaugamJ_boundary_fourier
    (f : DeningerMeyerCap) :
    deningerMeyerPaugamJ
        (deningerMeyerRapidSumLM
          (deningerMeyerCapFourierLM f)) =
      deningerMeyerRapidSumLM f := by
  apply Subtype.ext
  funext x
  by_cases hx : 0 < x
  · simp only [deningerMeyerPaugamJ,
      LinearMap.coe_mk, AddHom.coe_mk,
      deningerMeyerPaugamJFun, hx, ↓reduceIte,
      deningerMeyerRapidSumLM_apply_pos _
        (inv_pos.mpr hx),
      deningerMeyerRapidSumLM_apply_pos _ hx]
    simpa [deningerMeyerCapFourierLM] using
      (deningerMeyerPoisson_reflection
        f f.property hx).symm
  · simp [deningerMeyerPaugamJ,
      deningerMeyerPaugamJFun,
      deningerMeyerRapidSumLM_apply_nonpos
        f (not_lt.mp hx), hx]

/-- Equivalently, `J` sends each boundary to the Fourier-transformed boundary. -/
@[simp]
theorem deningerMeyerPaugamJ_boundary
    (f : DeningerMeyerCap) :
    deningerMeyerPaugamJ
        (deningerMeyerRapidSumLM f) =
      deningerMeyerRapidSumLM
        (deningerMeyerCapFourierLM f) := by
  calc
    deningerMeyerPaugamJ
        (deningerMeyerRapidSumLM f) =
      deningerMeyerPaugamJ
        (deningerMeyerPaugamJ
          (deningerMeyerRapidSumLM
            (deningerMeyerCapFourierLM f))) :=
      congrArg deningerMeyerPaugamJ
        (deningerMeyerPaugamJ_boundary_fourier f).symm
    _ = deningerMeyerRapidSumLM
          (deningerMeyerCapFourierLM f) :=
      deningerMeyerPaugamJ_sq _

/-- The Poisson boundary submodule is invariant under Paugam's `J`. -/
theorem deningerMeyerPaugamJ_range_le :
    LinearMap.range deningerMeyerRapidSumLM ≤
      (LinearMap.range deningerMeyerRapidSumLM).comap
        deningerMeyerPaugamJ := by
  rintro _ ⟨f, rfl⟩
  exact
    ⟨deningerMeyerCapFourierLM f,
      (deningerMeyerPaugamJ_boundary f).symm⟩

/-- Paugam's reciprocal involution descended to the value-level quotient proxy. -/
def deningerMeyerRapidCohomologyPaugamJ :
    DeningerMeyerRapidCohomology →ₗ[ℂ]
      DeningerMeyerRapidCohomology :=
  (LinearMap.range deningerMeyerRapidSumLM).mapQ
    (LinearMap.range deningerMeyerRapidSumLM)
    deningerMeyerPaugamJ
    deningerMeyerPaugamJ_range_le

@[simp]
theorem deningerMeyerRapidCohomologyPaugamJ_mk
    (g : DeningerMeyerRapidTarget) :
    deningerMeyerRapidCohomologyPaugamJ
        (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk
        (deningerMeyerPaugamJ g) :=
  rfl

/-- The descended reciprocal operator remains an involution. -/
@[simp]
theorem deningerMeyerRapidCohomologyPaugamJ_sq
    (q : DeningerMeyerRapidCohomology) :
    deningerMeyerRapidCohomologyPaugamJ
        (deningerMeyerRapidCohomologyPaugamJ q) =
      q := by
  obtain ⟨g, rfl⟩ :=
    Submodule.Quotient.mk_surjective
      (LinearMap.range deningerMeyerRapidSumLM) q
  simp

end

end RHTower
