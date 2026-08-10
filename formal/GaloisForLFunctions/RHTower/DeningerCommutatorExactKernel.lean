import GaloisForLFunctions.RHTower.DeningerCommutatorKernelConverse
import GaloisForLFunctions.RHTower.DeningerPreimageContinuous
import GaloisForLFunctions.RHTower.DeningerEvenPreimageMassZero
import GaloisForLFunctions.RHTower.DeningerPoissonPreimage
import GaloisForLFunctions.RHTower.DeningerMobiusRightInverse

/-!
# The exact kernel of the Möbius–Fourier commutator

The Schwartz representative of a kernel element is even, and both Meyer endpoint conditions are
*mass* conditions: the value of a Fourier transform at the origin is the total mass of its argument,
and the canonical preimage has zero mass.  So `(12)` supplies both endpoints at once — no Poisson
summation is needed.

The pointwise right inverse then identifies the kernel element as the Poisson boundary of that
Schwartz function, and with the boundary inclusion already proved this closes the exact kernel

`ker 𝔖_μ = Z(H_∩)`.

* `deningerKernelSchwartz_mem` : the representative lies in Meyer's space.
* `deningerKernel_eq_poissonSource` : **a kernel element is a Poisson boundary.**
* `deningerCommutator_exact_kernel` : **`ker 𝔖_μ = Z(H_∩)`.**
-/

namespace RHTower

open MeasureTheory SchwartzMap FourierTransform GaloisForLFunctions

noncomputable section

/-- The value of a Fourier transform at the origin is the total mass. -/
theorem deningerFourier_at_zero (F : ℝ → ℂ) : 𝓕 F 0 = ∫ v : ℝ, F v := by
  rw [Real.fourier_eq]
  simp

/-- **The Schwartz representative of a kernel element agrees with the preimage on the ray.** -/
theorem deningerKernelSchwartz_eqOn {h : DeningerExpSchwartz} {f : 𝓢(ℝ, ℂ)}
    (hae : deningerEvenPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) =ᵐ[volume] (f : ℝ → ℂ))
    {x : ℝ} (hx : 0 < x) :
    (f : ℝ → ℂ) x = deningerMobiusPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) x := by
  have heq := deningerEqOn_of_ae isOpen_Ioi (deningerEvenPreimage_continuousOn h.2)
    f.continuous.continuousOn hae hx
  rw [← heq, deningerEvenPreimage_of_pos _ hx]

/-- The Schwartz representative is even, being a Fourier transform of an even density. -/
theorem deningerKernelSchwartz_even {h : DeningerExpSchwartz} {f : 𝓢(ℝ, ℂ)}
    (hfour : (f : ℝ → ℂ) = 𝓕 (deningerEvenPreimage
      ((deningerCollarExchange h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))) (x : ℝ) :
    (f : ℝ → ℂ) (-x) = (f : ℝ → ℂ) x := by
  set G : ℝ → ℂ := deningerEvenPreimage
    ((deningerCollarExchange h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) with hG
  have hGeven : (fun y : ℝ => G (-y)) = G := by
    funext y
    exact deningerEvenPreimage_even _ y
  rw [hfour]
  have h1 : 𝓕 G (-x) = 𝓕⁻ G x := (Real.fourierInv_eq_fourier_neg G x).symm
  rw [h1, Real.fourierInv_eq_fourier_comp_neg, hGeven]

/-- **The Schwartz representative vanishes at the origin**, because the opposite collar's preimage
has zero mass. -/
theorem deningerKernelSchwartz_zero {h : DeningerExpSchwartz} {f : 𝓢(ℝ, ℂ)}
    (hfour : (f : ℝ → ℂ) = 𝓕 (deningerEvenPreimage
      ((deningerCollarExchange h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))) :
    (f : ℝ → ℂ) 0 = 0 := by
  rw [hfour, deningerFourier_at_zero]
  exact deningerEvenPreimage_integral_zero (deningerCollarExchange h).2

/-- **The Fourier transform of the Schwartz representative vanishes at the origin**, because the
preimage itself has zero mass. -/
theorem deningerKernelSchwartz_fourier_zero {h : DeningerExpSchwartz} {f : 𝓢(ℝ, ℂ)}
    (hae : deningerEvenPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) =ᵐ[volume] (f : ℝ → ℂ)) :
    𝓕 ((f : ℝ → ℂ)) 0 = 0 := by
  rw [deningerFourier_at_zero]
  have hcongr : (∫ v : ℝ, (f : ℝ → ℂ) v)
      = ∫ v : ℝ, deningerEvenPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) v :=
    integral_congr_ae (Filter.EventuallyEq.symm hae)
  rw [hcongr]
  exact deningerEvenPreimage_integral_zero h.2

/-- **The Schwartz representative lies in Meyer's space.** -/
theorem deningerKernelSchwartz_mem {h : DeningerExpSchwartz} {f : 𝓢(ℝ, ℂ)}
    (hae : deningerEvenPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) =ᵐ[volume] (f : ℝ → ℂ))
    (hfour : (f : ℝ → ℂ) = 𝓕 (deningerEvenPreimage
      ((deningerCollarExchange h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))) :
    f ∈ DeningerMeyerCap := by
  refine (deningerMeyerCap_mem_iff f).mpr
    ⟨deningerKernelSchwartz_even hfour, deningerKernelSchwartz_zero hfour, ?_⟩
  have hcle : (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ) f) 0 = 𝓕 ((f : ℝ → ℂ)) 0 := rfl
  rw [hcle]
  exact deningerKernelSchwartz_fourier_zero hae

/-- **A kernel element is the Poisson boundary of its Schwartz representative.** -/
theorem deningerKernel_eq_poissonSource {h : DeningerExpSchwartz} {f : 𝓢(ℝ, ℂ)}
    (hmem : f ∈ DeningerMeyerCap)
    (hae : deningerEvenPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) =ᵐ[volume] (f : ℝ → ℂ)) :
    deningerPoissonSource ⟨f, hmem⟩ = h := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  rw [deningerPoissonSource_apply, deningerPoissonLog_eq]
  have hxpos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hray : deningerPoissonValue f (Real.exp t)
      = deningerRaySum (deningerMobiusPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
        (Real.exp t) := by
    rw [deningerPoissonValue, deningerRaySum]
    refine tsum_congr fun n => ?_
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) * Real.exp t := by positivity
    have hcomm : Real.exp t * ((n : ℝ) + 1) = ((n : ℝ) + 1) * Real.exp t := by ring
    rw [hcomm]
    exact deningerKernelSchwartz_eqOn hae hpos
  rw [hray, deningerMobius_rightInverse h.2 hxpos, deningerLogPull_apply, Real.log_exp]

/-- **The exact kernel of the Möbius--Fourier commutator.**  It is exactly the Poisson image of
Meyer's space: the boundary inclusion is the corpus's Möbius inversion of the Poisson sum, and the
converse is the Fourier repair of the singular radial preimage together with the zero-mass
statement `(12)`, which supplies both Meyer endpoints. -/
theorem deningerCommutator_exact_kernel :
    {h : DeningerExpSchwartz | deningerMobiusCommutator h = 0}
      = Set.range deningerPoissonSource := by
  refine Set.Subset.antisymm (fun h hker => ?_) deningerPoissonRange_subset_commutatorKernel
  obtain ⟨f, hae, hfour⟩ := deningerCommutatorKernel_schwartz hker
  exact ⟨⟨f, deningerKernelSchwartz_mem hae hfour⟩,
    deningerKernel_eq_poissonSource (deningerKernelSchwartz_mem hae hfour) hae⟩

end

end RHTower
