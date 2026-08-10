import GaloisForLFunctions.RHTower.DeningerMeyerTopology
import GaloisForLFunctions.RHTower.DeningerMomentSeminormBound

/-!
# The weighted preimage as a continuous map into `L¹` of the ray

The canonical preimage is linear in the cochain — the Möbius series is absolutely convergent on
every positive ray, so it may be added and scaled term by term — and its weighted `L¹` norm is
bounded by a single Meyer seminorm.  That is exactly continuity in the Meyer topology.

* `deningerMobiusPreimage_add`, `_smul` : linearity of the preimage on the ray.
* `deningerMomentLM` : the linear map `h ↦ x^r f_h ∈ L¹(0,∞)`.
* `deningerMomentLM_continuous` : **`(13)`: the map is continuous.**
* `deningerMomentCLM` : the resulting continuous linear map.
-/

namespace RHTower

open MeasureTheory SchwartzMap ArithmeticFunction

noncomputable section

/-! ## Linearity of the preimage -/

theorem deningerMobiusPreimage_add {f g : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz)
    (hg : g ∈ DeningerExpSchwartz) {x : ℝ} (hx : 0 < x) :
    deningerMobiusPreimage (f + g) x
      = deningerMobiusPreimage f x + deningerMobiusPreimage g x := by
  have hsf := deningerMobiusRay_summable hf hx
  have hsg := deningerMobiusRay_summable hg hx
  rw [deningerMobiusPreimage, deningerMobiusPreimage, deningerMobiusPreimage,
    ← hsf.tsum_add hsg]
  refine tsum_congr fun n => ?_
  have hcoe : deningerLogPull (f + g) ((n : ℝ) * x)
      = deningerLogPull f ((n : ℝ) * x) + deningerLogPull g ((n : ℝ) * x) := rfl
  rw [hcoe]
  ring

theorem deningerMobiusPreimage_smul (c : ℂ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deningerMobiusPreimage (c • f) x = c * deningerMobiusPreimage f x := by
  rw [deningerMobiusPreimage, deningerMobiusPreimage, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hcoe : deningerLogPull (c • f) ((n : ℝ) * x)
      = c * deningerLogPull f ((n : ℝ) * x) := rfl
  rw [hcoe]
  ring

/-! ## The `L¹` element -/

/-- The `x^r`-weighted canonical preimage, as a function of the ray. -/
def deningerMomentFun (r : ℕ) (h : DeningerMeyerSource) : ℝ → ℂ := fun x =>
  ((x ^ r : ℝ) : ℂ) *
    deningerMobiusPreimage
      (((DeningerMeyerSource.toSource h : ↥DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) x

theorem deningerMomentFun_memLp (r : ℕ) (h : DeningerMeyerSource) :
    MemLp (deningerMomentFun r h) 1 (volume.restrict (Set.Ioi (0 : ℝ))) :=
  memLp_one_iff_integrable.mpr
    (deningerMobiusPreimage_moment_integrable (DeningerMeyerSource.toSource h).2 r)

/-- The `x^r`-weighted canonical preimage, as an element of `L¹(0,∞)`. -/
def deningerMomentLp (r : ℕ) (h : DeningerMeyerSource) :
    Lp ℂ 1 (volume.restrict (Set.Ioi (0 : ℝ))) :=
  (deningerMomentFun_memLp r h).toLp _

theorem deningerMomentLp_add (r : ℕ) (h₁ h₂ : DeningerMeyerSource) :
    deningerMomentLp r (h₁ + h₂) = deningerMomentLp r h₁ + deningerMomentLp r h₂ := by
  have hae : deningerMomentFun r (h₁ + h₂)
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        deningerMomentFun r h₁ + deningerMomentFun r h₂ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    show ((x ^ r : ℝ) : ℂ) * deningerMobiusPreimage _ x
      = ((x ^ r : ℝ) : ℂ) * deningerMobiusPreimage _ x
        + ((x ^ r : ℝ) : ℂ) * deningerMobiusPreimage _ x
    rw [deningerMobiusPreimage_add (DeningerMeyerSource.toSource h₁).2
      (DeningerMeyerSource.toSource h₂).2 hx0]
    ring
  rw [deningerMomentLp, deningerMomentLp, deningerMomentLp,
    MemLp.toLp_congr (deningerMomentFun_memLp r (h₁ + h₂))
      ((deningerMomentFun_memLp r h₁).add (deningerMomentFun_memLp r h₂)) hae,
    MemLp.toLp_add]

theorem deningerMomentLp_smul (r : ℕ) (c : ℂ) (h : DeningerMeyerSource) :
    deningerMomentLp r (c • h) = c • deningerMomentLp r h := by
  have hae : deningerMomentFun r (c • h)
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] c • deningerMomentFun r h := by
    filter_upwards with x
    show ((x ^ r : ℝ) : ℂ) * deningerMobiusPreimage _ x
      = c * (((x ^ r : ℝ) : ℂ) * deningerMobiusPreimage _ x)
    rw [deningerMobiusPreimage_smul]
    ring
  rw [deningerMomentLp, deningerMomentLp,
    MemLp.toLp_congr (deningerMomentFun_memLp r (c • h))
      ((deningerMomentFun_memLp r h).const_smul c) hae,
    MemLp.toLp_const_smul]

/-- **The weighted preimage as a linear map into `L¹(0,∞)`.** -/
def deningerMomentLM (r : ℕ) :
    DeningerMeyerSource →ₗ[ℂ] Lp ℂ 1 (volume.restrict (Set.Ioi (0 : ℝ))) where
  toFun := deningerMomentLp r
  map_add' := deningerMomentLp_add r
  map_smul' c h := deningerMomentLp_smul r c h

/-! ## Continuity -/

theorem deningerMomentLp_norm (r : ℕ) (h : DeningerMeyerSource) :
    ‖deningerMomentLp r h‖ = ∫ x in Set.Ioi (0 : ℝ), ‖deningerMomentFun r h x‖ := by
  rw [deningerMomentLp, L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (deningerMomentFun_memLp r h)] with x hx
  rw [hx]

/-- **`(13)`: the weighted preimage is continuous into `L¹(0,∞)`.**  The `L¹` norm is bounded by a
single Meyer seminorm, with a constant depending only on the order. -/
theorem deningerMomentLM_continuous (r : ℕ) : Continuous (deningerMomentLM r) := by
  refine WithSeminorms.continuous_normedSpace_rng _ DeningerMeyerSource.withSeminorms
    (deningerMomentLM r) ?_
  refine ⟨{(r + 2, 1)},
    ⟨(deningerCoefficientSum r * deningerMomentMajorantMass r).toNNReal, fun h => ?_⟩⟩
  have hKnn : 0 ≤ deningerCoefficientSum r * deningerMomentMajorantMass r :=
    mul_nonneg (deningerCoefficientSum_nonneg r) (deningerMomentMajorantMass_nonneg r)
  have hcast : (((r + 2 : ℕ) : ℝ)) = (r : ℝ) + 2 := by push_cast; ring
  have hbound := deningerPreimageMoment_le_seminorm r (DeningerMeyerSource.toSource h)
  have hnorm : ‖deningerMomentLM r h‖
      = ∫ x in Set.Ioi (0 : ℝ), ‖deningerMomentFun r h x‖ := deningerMomentLp_norm r h
  have hgoal : ‖deningerMomentLM r h‖
      ≤ (deningerCoefficientSum r * deningerMomentMajorantMass r) *
        deningerMeyerSeminormFun ((r : ℝ) + 2) 1 (DeningerMeyerSource.toSource h) := by
    rw [hnorm]
    exact hbound
  calc ((normSeminorm ℂ (Lp ℂ 1 (volume.restrict (Set.Ioi (0 : ℝ))))).comp
        (deningerMomentLM r)) h
      = ‖deningerMomentLM r h‖ := rfl
    _ ≤ (deningerCoefficientSum r * deningerMomentMajorantMass r) *
        deningerMeyerSeminormFun ((r : ℝ) + 2) 1 (DeningerMeyerSource.toSource h) := hgoal
    _ = (((deningerCoefficientSum r * deningerMomentMajorantMass r).toNNReal : ℝ)) *
        deningerMeyerSeminormFun (((r + 2 : ℕ) : ℝ)) 1 (DeningerMeyerSource.toSource h) := by
        rw [Real.coe_toNNReal _ hKnn, hcast]
    _ = ((deningerCoefficientSum r * deningerMomentMajorantMass r).toNNReal •
        ({(r + 2, 1)} : Finset (ℕ × ℕ)).sup DeningerMeyerSource.seminorms) h := by
        rw [Finset.sup_singleton]
        rfl

/-- **The weighted preimage as a continuous linear map** `H_- → L¹(0,∞)`. -/
def deningerMomentCLM (r : ℕ) :
    DeningerMeyerSource →L[ℂ] Lp ℂ 1 (volume.restrict (Set.Ioi (0 : ℝ))) where
  toLinearMap := deningerMomentLM r
  cont := deningerMomentLM_continuous r

end

end RHTower
