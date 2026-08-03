import GaloisForLFunctions.HTGeometry.ClockGoursatDerivContinuity

/-!
# The pure second derivatives of the Goursat solution

The chart d'Alembertian reads second partial derivatives one direction at a time, so the mixed
derivatives of the Goursat solution are not enough: the *pure* derivatives `∂ξ²u` and `∂η²u` are
needed as well. They exist as soon as the kernel is continuously differentiable, because each first
derivative is a parametric interval integral of the solution itself:

`∂ξ u(ξ,η) = ∫_b^η K(ξ,t) u(ξ,t) dt`,  `∂η u(ξ,η) = ∫_{ξ₀}^{ξ} K(τ,η) u(τ,η) dτ`.

Differentiating the first in `ξ` and the second in `η` under the integral sign expresses each pure
second derivative through the data already available — the kernel, its partial derivative, the
solution and the solution's first derivatives. Neither step needs a new estimate; the bootstrap is
the Leibniz rule applied to the Goursat identities themselves.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory

/-- The unordered interval between a point and the centre stays inside a symmetric window. -/
theorem uIcc_subset_Ioo_of_mem {ξ₀ h ξ : ℝ} (hh : 0 < h) (hξ : ξ ∈ Ioo (ξ₀ - h) (ξ₀ + h)) :
    uIcc ξ₀ ξ ⊆ Ioo (ξ₀ - h) (ξ₀ + h) := by
  intro τ hτ
  rcases Set.mem_uIcc.mp hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by linarith, by linarith [hξ.2]⟩
  · exact ⟨by linarith [hξ.1], by linarith⟩

/-- **The second derivative of the Goursat solution along the first characteristic.**

Differentiating `∂ξ u(ξ,η) = ∫_b^η K(ξ,t)u(ξ,t) dt` once more in `ξ` under the integral sign. -/
theorem hasDerivAt_goursat_xi_second {K Ka u : ℝ → ℝ → ℝ} {b b' c c' ξ₀ h : ℝ} {s : Set ℝ}
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hKa : Continuous fun p : ℝ × ℝ => Ka p.1 p.2)
    (hKd : ∀ ξ t : ℝ, HasDerivAt (fun w => K w t) (Ka ξ t) ξ)
    (hu : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hs : IsOpen s) (hsc : s ⊆ Ioo c c') (hsh : s ⊆ Ioo (ξ₀ - h) (ξ₀ + h))
    (hud : ∀ ξ ∈ Ioo (ξ₀ - h) (ξ₀ + h), ∀ η : ℝ,
      HasDerivAt (fun z => u z η) (volterraFun (K (clampTo c c' ξ)) b b' (u ξ) η) ξ)
    {ξ : ℝ} (hξ : ξ ∈ s) (η : ℝ) :
    HasDerivAt (fun z => volterraFun (K (clampTo c c' z)) b b' (u z) η)
      (∫ t in b..clampTo b b' η,
        Ka (clampTo c c' ξ) t * u ξ t
          + K (clampTo c c' ξ) t * volterraFun (K (clampTo c c' ξ)) b b' (u ξ) t) ξ := by
  classical
  have hclamp : Continuous (clampTo c c') := continuous_clampTo c c'
  have hker : Continuous fun p : ℝ × ℝ => K (clampTo c c' p.1) p.2 :=
    hK.comp ((hclamp.comp continuous_fst).prodMk continuous_snd)
  have hkera : Continuous fun p : ℝ × ℝ => Ka (clampTo c c' p.1) p.2 :=
    hKa.comp ((hclamp.comp continuous_fst).prodMk continuous_snd)
  have hf : Continuous fun p : ℝ × ℝ => K (clampTo c c' p.1) p.2 * u p.1 p.2 := hker.mul hu
  have hf' : Continuous fun p : ℝ × ℝ =>
      Ka (clampTo c c' p.1) p.2 * u p.1 p.2
        + K (clampTo c c' p.1) p.2 * volterraFun (K (clampTo c c' p.1)) b b' (u p.1) p.2 :=
    (hkera.mul hu).add (hker.mul (continuous_goursatXiDeriv hK hu b b' c c'))
  refine hasDerivAt_parametric_intervalIntegral_on (s := s)
    (f := fun w t => K (clampTo c c' w) t * u w t)
    (f' := fun w t => Ka (clampTo c c' w) t * u w t
      + K (clampTo c c' w) t * volterraFun (K (clampTo c c' w)) b b' (u w) t)
    hs hξ hf hf' b (clampTo b b' η) ?_
  intro z hz t _
  -- on `s` the clamp is the identity, so the integrand is a genuine product of two factors
  have hzc : clampTo c c' z = z := clampTo_of_mem (Ioo_subset_Icc_self (hsc hz))
  have hprod : HasDerivAt (fun w => K w t * u w t)
      (Ka z t * u z t + K z t * volterraFun (K (clampTo c c' z)) b b' (u z) t) z :=
    (hKd z t).mul (hud z (hsh hz) t)
  rw [hzc] at hprod
  have heq : (fun w => K (clampTo c c' w) t * u w t) =ᶠ[nhds z] fun w => K w t * u w t := by
    refine Filter.eventuallyEq_of_mem ((hs.inter isOpen_Ioo).mem_nhds ⟨hz, hsc hz⟩) ?_
    intro w hw
    show K (clampTo c c' w) t * u w t = K w t * u w t
    rw [clampTo_of_mem (Ioo_subset_Icc_self hw.2)]
  show HasDerivAt (fun w => K (clampTo c c' w) t * u w t)
    (Ka (clampTo c c' z) t * u z t
      + K (clampTo c c' z) t * volterraFun (K (clampTo c c' z)) b b' (u z) t) z
  rw [hzc]
  exact hprod.congr_of_eventuallyEq heq

/-- **The second derivative of the Goursat solution along the second characteristic.**

Differentiating `∂η u(ξ,η) = ∫_{ξ₀}^{ξ} K(τ,η)u(τ,η) dτ` once more in `η` under the integral
sign. -/
theorem hasDerivAt_goursat_eta_second {K Kb u : ℝ → ℝ → ℝ} {b b' c c' ξ₀ h : ℝ}
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hKb : Continuous fun p : ℝ × ℝ => Kb p.1 p.2)
    (hKd : ∀ ξ t : ℝ, HasDerivAt (fun w => K ξ w) (Kb ξ t) t)
    (hu : Continuous fun p : ℝ × ℝ => u p.1 p.2) (hh : 0 < h)
    (huη : ∀ ξ ∈ Ioo (ξ₀ - h) (ξ₀ + h), ∀ η ∈ Ioo b b',
      HasDerivAt (fun z => u ξ z) (∫ τ in ξ₀..ξ, K (clampTo c c' τ) η * u τ η) η)
    {ξ : ℝ} (hξ : ξ ∈ Ioo (ξ₀ - h) (ξ₀ + h)) {η : ℝ} (hη : η ∈ Ioo b b') :
    HasDerivAt (fun z => ∫ τ in ξ₀..ξ, K (clampTo c c' τ) z * u τ z)
      (∫ τ in ξ₀..ξ,
        Kb (clampTo c c' τ) η * u τ η
          + K (clampTo c c' τ) η * ∫ σ in ξ₀..τ, K (clampTo c c' σ) η * u σ η) η := by
  classical
  have hclamp : Continuous (clampTo c c') := continuous_clampTo c c'
  have hker : Continuous fun p : ℝ × ℝ => K (clampTo c c' p.2) p.1 :=
    hK.comp ((hclamp.comp continuous_snd).prodMk continuous_fst)
  have hkerb : Continuous fun p : ℝ × ℝ => Kb (clampTo c c' p.2) p.1 :=
    hKb.comp ((hclamp.comp continuous_snd).prodMk continuous_fst)
  have hval : Continuous fun p : ℝ × ℝ => u p.2 p.1 := hu.comp continuous_swap
  have hf : Continuous fun p : ℝ × ℝ => K (clampTo c c' p.2) p.1 * u p.2 p.1 := hker.mul hval
  have hinner : Continuous fun p : ℝ × ℝ => ∫ σ in ξ₀..p.2, K (clampTo c c' σ) p.1 * u σ p.1 :=
    (continuous_goursatEtaDeriv hK hu c c' ξ₀).comp continuous_swap
  have hf' : Continuous fun p : ℝ × ℝ =>
      Kb (clampTo c c' p.2) p.1 * u p.2 p.1
        + K (clampTo c c' p.2) p.1 * ∫ σ in ξ₀..p.2, K (clampTo c c' σ) p.1 * u σ p.1 :=
    (hkerb.mul hval).add (hker.mul hinner)
  refine hasDerivAt_parametric_intervalIntegral_on (s := Ioo b b')
    (f := fun w τ => K (clampTo c c' τ) w * u τ w)
    (f' := fun w τ => Kb (clampTo c c' τ) w * u τ w
      + K (clampTo c c' τ) w * ∫ σ in ξ₀..τ, K (clampTo c c' σ) w * u σ w)
    isOpen_Ioo hη hf hf' ξ₀ ξ ?_
  intro z hz τ hτ
  have hτmem : τ ∈ Ioo (ξ₀ - h) (ξ₀ + h) :=
    uIcc_subset_Ioo_of_mem hh hξ (uIoc_subset_uIcc hτ)
  exact (hKd (clampTo c c' τ) z).mul (huη τ hτmem z hz)

end GaloisForLFunctions.HTGeometry
