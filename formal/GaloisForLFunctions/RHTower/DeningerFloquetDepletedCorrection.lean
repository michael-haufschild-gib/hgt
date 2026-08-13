import GaloisForLFunctions.RHTower.DeningerFloquetBoundedCorrection
import GaloisForLFunctions.RHTower.DeningerPoissonMellin

/-!
# The bounded-correction no-go on the Euler-depleted sector

Euler depletion of a Poisson boundary is the Poisson boundary of the Euler-depleted test function,
and on the critical line it multiplies the Mellin transform by the invertible scalar
`1 - e^{-Ls}`.  Scaling the depleted explicit test function therefore realizes the same family of
critical-line characters times a still nowhere-vanishing profile, so the depleted boundaries have
the same closure and the bounded-correction no-go holds verbatim on the depleted sector.

* `deningerMeyerCapDepletion` : `1 - τ_L` on Meyer's space.
* `mellin_deningerMeyerCapDepletion` : `M(Δ_L f) = (1 - e^{-Ls}) M f`.
* `deningerFloquetDepletedBoundary_topologicalClosure` : the depleted boundaries have the same
  closure.
* `deningerFloquetDepletedCorrection_factors` : **the no-go on the depleted sector.**
-/

namespace RHTower

open MeasureTheory Complex Set SchwartzMap
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace

noncomputable section

/-! ## The depletion operator on Meyer's space -/

/-- The scaling flow is a group action. -/
theorem deningerMeyerCapFlow_flow (c d : ℝ) (f : DeningerMeyerCap) :
    deningerMeyerCapFlow c (deningerMeyerCapFlow d f) = deningerMeyerCapFlow (c + d) f := by
  refine Subtype.ext (SchwartzMap.ext fun x => ?_)
  rw [deningerMeyerCapFlow_apply, deningerMeyerCapFlow_apply, deningerMeyerCapFlow_apply]
  congr 1
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Euler depletion at collar length `L`.** -/
def deningerMeyerCapDepletion (L : ℝ) : DeningerMeyerCap →ₗ[ℂ] DeningerMeyerCap :=
  LinearMap.id - deningerMeyerCapFlow (-L)

theorem deningerMeyerCapDepletion_apply (L : ℝ) (f : DeningerMeyerCap) :
    deningerMeyerCapDepletion L f = f - deningerMeyerCapFlow (-L) f := rfl

theorem deningerMeyerCapFlow_depletion (L c : ℝ) (f : DeningerMeyerCap) :
    deningerMeyerCapFlow c (deningerMeyerCapDepletion L f)
      = deningerMeyerCapDepletion L (deningerMeyerCapFlow c f) := by
  rw [deningerMeyerCapDepletion_apply, deningerMeyerCapDepletion_apply, map_sub,
    deningerMeyerCapFlow_flow, deningerMeyerCapFlow_flow, add_comm]

/-- **Depletion multiplies the Mellin transform by `1 - e^{-Ls}`.** -/
theorem mellin_deningerMeyerCapDepletion (L : ℝ) (f : DeningerMeyerCap) {s : ℂ} (hs : 0 < s.re) :
    mellin (((deningerMeyerCapDepletion L f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) s
      = (1 - Complex.exp (-(L : ℂ) * s))
        * mellin (((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) s := by
  have hfun : (((deningerMeyerCapDepletion L f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = fun x : ℝ => (((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x
          - (((deningerMeyerCapFlow (-L) f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x := by
    funext x
    rfl
  rw [hfun, (hasMellin_sub (mellinConvergent_schwartz _ hs) (mellinConvergent_schwartz _ hs)).2,
    mellin_deningerMeyerCapFlow]
  push_cast
  ring

theorem deningerCriticalLine_depletionFactor_ne_zero {L : ℝ} (hL : 0 < L) (ξ : ℝ) :
    (1 : ℂ) - Complex.exp (-(L : ℂ) * deningerCriticalLine ξ) ≠ 0 := by
  intro hzero
  have hone : Complex.exp (-(L : ℂ) * deningerCriticalLine ξ) = 1 := by
    have := sub_eq_zero.1 hzero
    exact this.symm
  have hre : (-(L : ℂ) * deningerCriticalLine ξ).re = -(L / 2) := by
    rw [deningerCriticalLine]
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hnorm : ‖Complex.exp (-(L : ℂ) * deningerCriticalLine ξ)‖ = Real.exp (-(L / 2)) := by
    rw [Complex.norm_exp, hre]
  rw [hone, norm_one] at hnorm
  have hlt : Real.exp (-(L / 2)) < 1 := by
    refine Real.exp_lt_one_iff.2 ?_
    linarith
  linarith [hnorm]

theorem mellin_deningerMeyerCapDepletion_test_ne_zero {L : ℝ} (hL : 0 < L) (ξ : ℝ) :
    mellin (((deningerMeyerCapDepletion L meyerPoissonTestSource : DeningerMeyerCap) :
      𝓢(ℝ, ℂ)) : ℝ → ℂ) (deningerCriticalLine ξ) ≠ 0 := by
  rw [mellin_deningerMeyerCapDepletion L _ (deningerCriticalLine_re_pos ξ)]
  exact mul_ne_zero (deningerCriticalLine_depletionFactor_ne_zero hL ξ)
    (deningerFloquetProfile_ne_zero ξ)

/-! ## The depleted boundary -/

/-- The span of the Mellin samples of the Euler-depleted Poisson boundaries. -/
def deningerFloquetDepletedBoundary (L : ℝ) : Submodule ℂ (Lp ℂ 2 deningerFloquetMeasure) :=
  Submodule.span ℂ (Set.range fun f : DeningerMeyerCap =>
    deningerFloquetLp (deningerPoissonSource (deningerMeyerCapDepletion L f)))

theorem deningerFloquetDepletedBoundary_le (L : ℝ) :
    deningerFloquetDepletedBoundary L ≤ deningerFloquetResonanceSpanᗮ := by
  refine Submodule.span_le.2 ?_
  rintro u ⟨f, rfl⟩
  exact deningerFloquetBoundary_le (Submodule.subset_span ⟨_, rfl⟩)

theorem deningerFloquetDepletedBoundary_orthogonal_inf_eq_bot {L : ℝ} (hL : 0 < L) :
    (deningerFloquetDepletedBoundary L)ᗮ ⊓ deningerFloquetResonanceSpanᗮ = ⊥ :=
  deningerFloquetFlow_orthogonal_inf_eq_bot (deningerMeyerCapDepletion L meyerPoissonTestSource)
    (mellin_deningerMeyerCapDepletion_test_ne_zero hL)
    (fun c => by
      rw [deningerMeyerCapFlow_depletion]
      exact Submodule.subset_span ⟨_, rfl⟩)

/-- **The depleted Poisson boundaries have the same closure as the undepleted ones.** -/
theorem deningerFloquetDepletedBoundary_topologicalClosure {L : ℝ} (hL : 0 < L) :
    (deningerFloquetDepletedBoundary L).topologicalClosure = deningerFloquetResonanceSpanᗮ :=
  submodule_topologicalClosure_eq_of_orthogonal_inf_eq_bot (deningerFloquetDepletedBoundary_le L)
    (Submodule.isClosed_orthogonal _) (deningerFloquetDepletedBoundary_orthogonal_inf_eq_bot hL)

/-! ## The no-go on the depleted sector -/

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem deningerFloquetDepletedCorrection_vanishing {L : ℝ} (hL : 0 < L)
    (A : Lp ℂ 2 deningerFloquetMeasure →L[ℂ] Y)
    (hA : ∀ f : DeningerMeyerCap,
      A (deningerFloquetLp (deningerPoissonSource (deningerMeyerCapDepletion L f))) = 0)
    {x : Lp ℂ 2 deningerFloquetMeasure} (hx : x ∈ deningerFloquetResonanceSpanᗮ) : A x = 0 := by
  have hker : deningerFloquetDepletedBoundary L
      ≤ LinearMap.ker (A : Lp ℂ 2 deningerFloquetMeasure →ₗ[ℂ] Y) := by
    refine Submodule.span_le.2 ?_
    rintro u ⟨f, rfl⟩
    exact hA f
  have hclosed : (deningerFloquetDepletedBoundary L).topologicalClosure
      ≤ LinearMap.ker (A : Lp ℂ 2 deningerFloquetMeasure →ₗ[ℂ] Y) :=
    Submodule.topologicalClosure_minimal _ hker A.isClosed_ker
  rw [deningerFloquetDepletedBoundary_topologicalClosure hL] at hclosed
  exact hclosed hx

/-- **The bounded-correction no-go on the Euler-depleted sector.** -/
theorem deningerFloquetDepletedCorrection_factors {L : ℝ} (hL : 0 < L)
    (A : Lp ℂ 2 deningerFloquetMeasure →L[ℂ] Y)
    (hA : ∀ f : DeningerMeyerCap,
      A (deningerFloquetLp (deningerPoissonSource (deningerMeyerCapDepletion L f))) = 0)
    (x : Lp ℂ 2 deningerFloquetMeasure) :
    A x = A (deningerFloquetResonanceSpan.topologicalClosure.starProjection x) := by
  have hsub : x - deningerFloquetResonanceSpan.topologicalClosure.starProjection x
      ∈ deningerFloquetResonanceSpanᗮ :=
    Submodule.orthogonal_le deningerFloquetResonanceSpan.le_topologicalClosure
      (Submodule.sub_starProjection_mem_orthogonal x)
  have hzero := deningerFloquetDepletedCorrection_vanishing hL A hA hsub
  rw [map_sub] at hzero
  exact sub_eq_zero.1 hzero

end

end RHTower
