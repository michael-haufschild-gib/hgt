import GaloisForLFunctions.RHTower.HardyModulationRay
import GaloisForLFunctions.RHTower.SuzukiDeBrangesSpace

noncomputable section

/-!
# The chain of spaces `V(t)` and its Fourier image

`V(t) = L²(t,∞) ∩ K L²(t,∞)` is the intersection of a translated datum ray with its image under the
conjugate-linear involution `K`.  Under the Fourier transform the translated ray becomes the
modulated Hardy space and `K` becomes `κ f = Θ conj f`, so

```text
𝖥(V(t)) = e^{2πitξ}H² ∩ κ(e^{2πitξ}H²).
```

At `t = 0` this is the model space `K(Θ)`.  The pair of Blaschke symbols is exchanged by `κ`, so an
element with a vanishing Cauchy transform at a point above the axis may be divided by the Blaschke
factor there while staying in `𝖥(V(t))`: the first component uses the vanishing, and the second gets
the inner factor, which needs nothing.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- **`L²(t,∞)`.**  In the datum coordinate of the corpus the ray points to the left, so this is the
translate of the negative ray. -/
def suzukiRayL2 (t : ℝ) : Submodule ℂ L2R :=
  Submodule.map (translateL2 t).toLinearMap lowerHalfLineL2

theorem mem_suzukiRayL2_iff' (t : ℝ) (f : L2R) :
    f ∈ suzukiRayL2 t ↔ translateL2 (-t) f ∈ lowerHalfLineL2 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    show translateL2 (-t) (translateL2 t g) ∈ lowerHalfLineL2
    rw [translateL2_neg_translateL2]
    exact hg
  · intro h
    refine ⟨translateL2 (-t) f, h, ?_⟩
    show translateL2 t (translateL2 (-t) f) = f
    rw [translateL2_translateL2, neg_add_cancel]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [coeFn_translateL2 (0 : ℝ) f] with x h1
    rw [h1, add_zero]

theorem mem_suzukiRayL2_iff (t : ℝ) (f : L2R) :
    f ∈ suzukiRayL2 t ↔ ∀ᵐ x : ℝ, -t < x → (f : ℝ → ℂ) x = 0 := by
  rw [mem_suzukiRayL2_iff', mem_lowerHalfLineL2_iff]
  have hmp := measurePreserving_add_right (volume : Measure ℝ) t
  have hmp' := measurePreserving_add_right (volume : Measure ℝ) (-t)
  have hshift := hmp.quasiMeasurePreserving.tendsto_ae
  have hshift' := hmp'.quasiMeasurePreserving.tendsto_ae
  constructor
  · intro h
    filter_upwards [hshift.eventually h,
      (coeFn_translateL2 (-t) f).comp_tendsto hshift] with u hu hu2 hlt
    have hpos : (0 : ℝ) < u + t := by linarith
    have h3 := hu hpos
    have hu2' : (translateL2 (-t) f : ℝ → ℂ) (u + t) = (f : ℝ → ℂ) (u + t + -t) := hu2
    rw [hu2'] at h3
    simpa using h3
  · intro h
    filter_upwards [hshift'.eventually h, coeFn_translateL2 (-t) f] with x hx hx2 hpos
    rw [hx2]
    exact hx (by linarith)

theorem suzukiRayL2_zero : suzukiRayL2 0 = lowerHalfLineL2 := by
  ext f
  rw [mem_suzukiRayL2_iff, mem_lowerHalfLineL2_iff, neg_zero]

theorem map_fourier_suzukiRayL2 (t : ℝ) :
    Submodule.map ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.toLinearMap)
        (suzukiRayL2 t) = hardyRay t := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) g, ⟨g, hg, rfl⟩, ?_⟩
    show modulationMul t ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) g)
      = (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) (translateL2 t g)
    exact (fourierTransform_translateL2 t g).symm
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨translateL2 t g, ⟨g, hg, rfl⟩, ?_⟩
    show (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) (translateL2 t g)
      = modulationMul t ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) g)
    exact fourierTransform_translateL2 t g

/-! ## The spaces `V(t)` -/

/-- **Suzuki equation (5.2).**  `V(t) = L²(t,∞) ∩ K L²(t,∞)`. -/
def suzukiV (t : ℝ) : Submodule ℂ L2R :=
  suzukiRayL2 t ⊓ Submodule.map suzukiKₛₗ (suzukiRayL2 t)

theorem suzukiV_zero : suzukiV 0 = suzukiV0 := by
  rw [suzukiV, suzukiV0, suzukiRayL2_zero]

/-- The conjugate-linear involution `κ f = Θ conj f`, the Fourier conjugate of `K`. -/
def suzukiKappaₛₗ : L2R →ₛₗ[starRingEnd ℂ] L2R where
  toFun f := thetaMul (star f)
  map_add' f g := by rw [lpStar_add, map_add]
  map_smul' c f := by rw [lpStar_smul, map_smul]

@[simp] theorem suzukiKappaₛₗ_apply (f : L2R) : suzukiKappaₛₗ f = thetaMul (star f) := rfl

theorem suzukiKappaₛₗ_involutive (f : L2R) : suzukiKappaₛₗ (suzukiKappaₛₗ f) = f :=
  thetaMul_star_thetaMul_star f

theorem fourier_suzukiKₛₗ (f : L2R) :
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) (suzukiKₛₗ f)
      = suzukiKappaₛₗ ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) f) :=
  fourier_suzukiKFun f

theorem mem_map_suzukiKappa_iff (S : Submodule ℂ L2R) (G : L2R) :
    G ∈ Submodule.map suzukiKappaₛₗ S ↔ suzukiKappaₛₗ G ∈ S := by
  constructor
  · rintro ⟨H, hH, rfl⟩
    rw [suzukiKappaₛₗ_involutive]
    exact hH
  · intro h
    exact ⟨suzukiKappaₛₗ G, h, suzukiKappaₛₗ_involutive G⟩

/-- The Fourier image of `V(t)`. -/
def suzukiModelRay (t : ℝ) : Submodule ℂ L2R :=
  hardyRay t ⊓ Submodule.map suzukiKappaₛₗ (hardyRay t)

theorem mem_suzukiModelRay_iff (t : ℝ) (G : L2R) :
    G ∈ suzukiModelRay t ↔ G ∈ hardyRay t ∧ thetaMul (star G) ∈ hardyRay t := by
  rw [suzukiModelRay, Submodule.mem_inf, mem_map_suzukiKappa_iff]
  rfl

theorem map_fourier_suzukiV (t : ℝ) :
    Submodule.map ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.toLinearMap)
        (suzukiV t) = suzukiModelRay t := by
  rw [suzukiV, Submodule.map_inf _ (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).injective,
    map_fourier_suzukiRayL2, suzukiModelRay]
  congr 1
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) g, ?_, ?_⟩
    · exact (map_fourier_suzukiRayL2 t) ▸ ⟨g, hg, rfl⟩
    · exact (fourier_suzukiKₛₗ g).symm
  · rintro _ ⟨H, hH, rfl⟩
    obtain ⟨g, hg, rfl⟩ : ∃ g ∈ suzukiRayL2 t,
        (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) g = H := by
      have := (map_fourier_suzukiRayL2 t) ▸ hH
      obtain ⟨g, hg, hgH⟩ := this
      exact ⟨g, hg, hgH⟩
    exact ⟨suzukiKₛₗ g, ⟨g, hg, rfl⟩, fourier_suzukiKₛₗ g⟩

theorem suzukiModelRay_zero : suzukiModelRay 0 = suzukiModelSpace := by
  refine le_antisymm ?_ ?_
  · intro G hG
    rw [mem_suzukiModelRay_iff, hardyRay_zero] at hG
    exact (mem_suzukiModelSpace_iff_conj G).mpr hG
  · intro G hG
    rw [mem_suzukiModelRay_iff, hardyRay_zero]
    exact (mem_suzukiModelSpace_iff_conj G).mp hG

theorem suzukiModelRay_le_suzukiModelSpace {t : ℝ} (ht : 0 ≤ t) :
    suzukiModelRay t ≤ suzukiModelSpace := by
  intro G hG
  rw [mem_suzukiModelRay_iff] at hG
  exact (mem_suzukiModelSpace_iff_conj G).mpr
    ⟨hardyRay_le_hardyL2 ht hG.1, hardyRay_le_hardyL2 ht hG.2⟩

/-! ## Blaschke stability -/

/-- **Axiom (dB3), boundary form.**  Dividing out a zero above the axis keeps an element of
`𝖥(V(t))` inside `𝖥(V(t))`: the Blaschke symbol needs the vanishing Cauchy transform, and the
involution turns it into the inner factor, which is unconditional. -/
theorem blaschkeMul_mem_suzukiModelRay {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : 0 < w.im)
    {G : L2R} (hG : G ∈ suzukiModelRay t)
    (hzero : (∫ x : ℝ, (G : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w)) = 0) :
    blaschkeMul w G ∈ suzukiModelRay t := by
  rw [mem_suzukiModelRay_iff] at hG ⊢
  refine ⟨blaschkeMul_mem_hardyRay ht hw hG.1 hzero, ?_⟩
  rw [thetaMul_star_blaschkeMul]
  exact blaschkeMulInv_mem_hardyRay hw hG.2

/-- **Axiom (dB2), boundary form.**  `𝖥(V(t))` is stable under the involution. -/
theorem suzukiKappa_mem_suzukiModelRay {t : ℝ} {G : L2R} (hG : G ∈ suzukiModelRay t) :
    thetaMul (star G) ∈ suzukiModelRay t := by
  rw [mem_suzukiModelRay_iff] at hG ⊢
  refine ⟨hG.2, ?_⟩
  rw [thetaMul_star_thetaMul_star]
  exact hG.1


end RHTower
