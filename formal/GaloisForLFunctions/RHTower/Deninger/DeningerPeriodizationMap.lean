import GaloisForLFunctions.RHTower.Deninger.DeningerPeriodizationSmooth
import GaloisForLFunctions.RHTower.Deninger.DeningerTomographyInjective

/-!
# The periodization as a map to the smooth periodic test space

Assembling the pointwise periodization into a linear map
`Per_L : H_- → C^∞(ℝ/Lℤ)` and, for a family of periods, into the tomography map
`𝒫_Q : H_- → ∏_{L ∈ Q} C^∞(ℝ/Lℤ)`.

* `deningerPeriodizationMap` : **`Per_L` as a linear map into `C^∞(ℝ/Lℤ)`.**
* `deningerPeriodizationMap_ker` : its kernel is the range of the periodization defect.
* `deningerTomographyMap` : **`𝒫_Q` for a family of periods.**
* `deningerTomographyMap_injective` : **`ker 𝒫_Q = 0` for an infinite prime family.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

theorem deningerPeriodizationSum_add {f g : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz)
    (hg : g ∈ DeningerExpSchwartz) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    deningerPeriodizationSum (f + g) L t
      = deningerPeriodizationSum f L t + deningerPeriodizationSum g L t := by
  rw [deningerPeriodizationSum, deningerPeriodizationSum, deningerPeriodizationSum,
    ← (deningerShiftInt_summable hf hL t).tsum_add (deningerShiftInt_summable hg hL t)]
  rfl

theorem deningerPeriodizationSum_smul (c : ℂ) (f : 𝓢(ℝ, ℂ)) (L t : ℝ) :
    deningerPeriodizationSum (c • f) L t = c * deningerPeriodizationSum f L t := by
  rw [deningerPeriodizationSum, deningerPeriodizationSum, ← tsum_mul_left]
  rfl

/-- **The periodization as a linear map into `C^∞(ℝ/Lℤ)`.** -/
def deningerPeriodizationMap {L : ℝ} (hL : 0 < L) :
    DeningerExpSchwartz →ₗ[ℂ] DeningerSmoothPeriodic L where
  toFun h := ⟨deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L,
    deningerPeriodizationMem h.2 hL⟩
  map_add' h g := by
    refine Subtype.ext (funext fun t => ?_)
    exact deningerPeriodizationSum_add h.2 g.2 hL t
  map_smul' c h := by
    refine Subtype.ext (funext fun t => ?_)
    exact deningerPeriodizationSum_smul c _ L t

theorem deningerPeriodizationMap_apply {L : ℝ} (hL : 0 < L) (h : DeningerExpSchwartz) (t : ℝ) :
    ((deningerPeriodizationMap hL h : DeningerSmoothPeriodic L) : ℝ → ℂ) t
      = deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t := rfl

/-- **The kernel of the periodization is the range of the periodization defect.** -/
theorem deningerPeriodizationMap_ker {L : ℝ} (hL : 0 < L) :
    LinearMap.ker (deningerPeriodizationMap hL) = LinearMap.range (deningerPeriodizationDefect L) := by
  ext h
  constructor
  · intro hmem
    have hzero : ∀ t : ℝ,
        deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t = 0 := by
      intro t
      have := congrArg (fun u : DeningerSmoothPeriodic L => (u : ℝ → ℂ) t)
        (LinearMap.mem_ker.1 hmem)
      simpa [deningerPeriodizationMap_apply] using this
    have hrange : h ∈ Set.range (deningerPeriodizationDefect L) := by
      rw [deningerPeriodization_range_eq_kernel hL]
      exact hzero
    exact hrange
  · intro hmem
    obtain ⟨g, hg⟩ := LinearMap.mem_range.1 hmem
    have hzero : ∀ t : ℝ,
        deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t = 0 := by
      have hrange : h ∈ Set.range (deningerPeriodizationDefect L) := ⟨g, hg⟩
      rw [deningerPeriodization_range_eq_kernel hL] at hrange
      exact hrange
    refine LinearMap.mem_ker.2 (Subtype.ext (funext fun t => ?_))
    exact hzero t

/-- **The cofinal tomography map `𝒫_Q` of a family of periods.** -/
def deningerTomographyMap {ι : Type*} (L : ι → ℝ) (hL : ∀ i, 0 < L i) :
    DeningerExpSchwartz →ₗ[ℂ] ((i : ι) → DeningerSmoothPeriodic (L i)) where
  toFun h i := deningerPeriodizationMap (hL i) h
  map_add' h g := funext fun i => (deningerPeriodizationMap (hL i)).map_add h g
  map_smul' c h := funext fun i => (deningerPeriodizationMap (hL i)).map_smul c h

theorem deningerTomographyMap_apply {ι : Type*} (L : ι → ℝ) (hL : ∀ i, 0 < L i)
    (h : DeningerExpSchwartz) (i : ι) :
    deningerTomographyMap L hL h i = deningerPeriodizationMap (hL i) h := rfl

/-- **The tomography map of an infinite prime family is injective.**  This is `ker 𝒫_Q = 0` in the
form of the map into the product of smooth orbit spaces. -/
theorem deningerTomographyMap_injective {Q : Set ℕ} (hQinf : Q.Infinite)
    (hQp : ∀ q ∈ Q, Nat.Prime q)
    (hL : ∀ q : Q, 0 < Real.log (q : ℕ)) :
    Function.Injective (deningerTomographyMap (fun q : Q => Real.log (q : ℕ)) hL) := by
  intro a b hab
  refine Subtype.ext (deningerCofinalPrimeTomography_eq a.2 b.2 hQinf hQp fun q hq t => ?_)
  have := congrArg (fun u : (q : Q) → DeningerSmoothPeriodic (Real.log (q : ℕ)) =>
    ((u ⟨q, hq⟩ : DeningerSmoothPeriodic (Real.log q)) : ℝ → ℂ) t) hab
  simpa [deningerTomographyMap_apply, deningerPeriodizationMap_apply] using this

end

end RHTower
