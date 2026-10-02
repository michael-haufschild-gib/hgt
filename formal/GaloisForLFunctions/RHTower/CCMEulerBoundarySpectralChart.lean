import GaloisForLFunctions.RHTower.CCMEulerBoundaryTransition

/-!
# The actual spectral chart of an Euler boundary

The original source quotient also carries its Fourier restriction. This gives
a bounded spectral chart, determined on every source vector. In these charts
the actual prime-insertion transitions are exactly Fourier restriction.
-/

noncomputable section

open IsDedekindDomain

namespace RHTower

/-- Empty Euler data gives the literal Fourier shell carrier. -/
theorem mem_ccmEulerBoundaryAnnulus_empty_iff (b c : ℝ) (u : evenSubspace) :
    u ∈ ccmEulerBoundaryAnnulus ∅ b c ↔
      evenFourierCutoff b u = 0 ∧ evenFourierCutoff c u = u := by
  simpa only [ccmFiniteEulerCarrierScale, Finset.prod_empty, div_one] using
    mem_ccmEulerBoundaryAnnulus_iff ∅ b c u

/-- The actual Euler boundary and its source Fourier restriction have the same kernel. -/
theorem ccmEulerBoundaryMap_ker_eq_spectral (S : Finset (HeightOneSpectrum ℤ))
    (b : ℝ) (hb : 0 < b) :
    (ccmEulerBoundaryMap S b 1 hb zero_lt_one).ker =
      (ccmEulerBoundaryMap ∅ b (ccmFiniteEulerCarrierScale S) hb
        (ccmFiniteEulerCarrierScale_pos S)).ker := by
  rw [ccmEulerBoundaryMap_ker, ccmEulerBoundaryMap_ker]
  simp only [ccmFiniteEulerCarrierScale, Finset.prod_empty, one_mul, mul_one]

/-- Descend the actual source Fourier restriction through the Euler boundary quotient. -/
def ccmEulerBoundarySpectralMap (S : Finset (HeightOneSpectrum ℤ)) (b : ℝ) (hb : 0 < b) :
    ccmEulerBoundaryAnnulus S b 1 →L[ℂ]
      ccmEulerBoundaryAnnulus ∅ b (ccmFiniteEulerCarrierScale S) :=
  ((ccmEulerBoundaryMap S b 1 hb zero_lt_one).ker.liftQL
    (ccmEulerBoundaryMap ∅ b (ccmFiniteEulerCarrierScale S) hb (ccmFiniteEulerCarrierScale_pos S))
      (ccmEulerBoundaryMap_ker_eq_spectral S b hb).le).comp
    (ccmEulerBoundaryQuotientEquiv S b 1 hb zero_lt_one).symm.toContinuousLinearMap

theorem ccmEulerBoundarySpectralMap_source (S : Finset (HeightOneSpectrum ℤ))
    (b : ℝ) (hb : 0 < b) (f : evenCentralSoninCarrier b) :
    ccmEulerBoundarySpectralMap S b hb (ccmEulerBoundaryMap S b 1 hb zero_lt_one f) =
      ccmEulerBoundaryMap ∅ b (ccmFiniteEulerCarrierScale S) hb
        (ccmFiniteEulerCarrierScale_pos S) f := by
  have hrepr := (ccmEulerBoundaryQuotientEquiv S b 1 hb zero_lt_one).symm_apply_apply
    (Submodule.Quotient.mk f)
  rw [ccmEulerBoundaryQuotientEquiv_apply_mk] at hrepr
  change ((ccmEulerBoundaryMap S b 1 hb zero_lt_one).ker.liftQL
    (ccmEulerBoundaryMap ∅ b (ccmFiniteEulerCarrierScale S) hb (ccmFiniteEulerCarrierScale_pos S))
      (ccmEulerBoundaryMap_ker_eq_spectral S b hb).le)
      ((ccmEulerBoundaryQuotientEquiv S b 1 hb zero_lt_one).symm
        (ccmEulerBoundaryMap S b 1 hb zero_lt_one f)) = _
  rw [hrepr]
  rfl

theorem ccmEulerBoundarySpectralMap_surjective (S : Finset (HeightOneSpectrum ℤ))
    (b : ℝ) (hb : 0 < b) : Function.Surjective (ccmEulerBoundarySpectralMap S b hb) := by
  intro u
  obtain ⟨f, rfl⟩ := ccmEulerBoundaryMap_surjective ∅ b (ccmFiniteEulerCarrierScale S) hb
    (ccmFiniteEulerCarrierScale_pos S) u
  exact ⟨ccmEulerBoundaryMap S b 1 hb zero_lt_one f, ccmEulerBoundarySpectralMap_source S b hb f⟩

theorem ccmEulerBoundarySpectralMap_ker (S : Finset (HeightOneSpectrum ℤ))
    (b : ℝ) (hb : 0 < b) : (ccmEulerBoundarySpectralMap S b hb).ker = ⊥ := by
  apply le_antisymm _ bot_le
  intro y hy
  obtain ⟨f, rfl⟩ := ccmEulerBoundaryMap_surjective S b 1 hb zero_lt_one y
  change ccmEulerBoundarySpectralMap S b hb (ccmEulerBoundaryMap S b 1 hb zero_lt_one f) = 0 at hy
  rw [ccmEulerBoundarySpectralMap_source] at hy
  have hf : f ∈ (ccmEulerBoundaryMap ∅ b (ccmFiniteEulerCarrierScale S) hb
      (ccmFiniteEulerCarrierScale_pos S)).ker := hy
  rw [← ccmEulerBoundaryMap_ker_eq_spectral S b hb] at hf
  change ccmEulerBoundaryMap S b 1 hb zero_lt_one f = 0 at hf
  simpa only [Submodule.mem_bot] using hf

/-- A bounded spectral chart of the original Euler boundary, with its source law retained. -/
def ccmEulerBoundarySpectralEquiv (S : Finset (HeightOneSpectrum ℤ)) (b : ℝ) (hb : 0 < b) :
    ccmEulerBoundaryAnnulus S b 1 ≃L[ℂ]
      ccmEulerBoundaryAnnulus ∅ b (ccmFiniteEulerCarrierScale S) :=
  ContinuousLinearEquiv.ofBijective (𝕜 := ℂ) (𝕜' := ℂ)
    (σ := RingHom.id ℂ) (σ' := RingHom.id ℂ)
    (E := ccmEulerBoundaryAnnulus S b 1)
    (F := ccmEulerBoundaryAnnulus ∅ b (ccmFiniteEulerCarrierScale S))
    (ccmEulerBoundarySpectralMap S b hb) (ccmEulerBoundarySpectralMap_ker S b hb)
      (LinearMap.range_eq_top.mpr (ccmEulerBoundarySpectralMap_surjective S b hb))

/-- The chart recovers the actual finite Fourier band of each original Sonin source. -/
theorem ccmEulerBoundarySpectralEquiv_source (S : Finset (HeightOneSpectrum ℤ))
    (b : ℝ) (hb : 0 < b) (f : evenCentralSoninCarrier b) :
    (ccmEulerBoundarySpectralEquiv S b hb (ccmEulerBoundaryMap S b 1 hb zero_lt_one f) : evenSubspace) =
      evenFourierCutoff (ccmFiniteEulerCarrierScale S) (f : evenSubspace) := by
  change (ccmEulerBoundarySpectralMap S b hb
    (ccmEulerBoundaryMap S b 1 hb zero_lt_one f) : evenSubspace) = _
  rw [ccmEulerBoundarySpectralMap_source]
  change evenFourierCutoff (ccmFiniteEulerCarrierScale S)
    (ccmFiniteEulerDenominator ∅ (f : evenSubspace)) = _
  simp only [ccmFiniteEulerDenominator, Finset.toList_empty, List.map_nil, List.prod_nil,
    one_apply_eq_self]

/-- The source-preserving cofinal system is exactly Fourier restriction in its actual charts. -/
theorem ccmEulerBoundaryTransition_spectral (S T : Finset (HeightOneSpectrum ℤ))
    (hST : S ⊆ T) (b : ℝ) (hb : 0 < b) (y : ccmEulerBoundaryAnnulus T b 1) :
    (ccmEulerBoundarySpectralEquiv S b hb (ccmEulerBoundaryTransition S T hST b hb y) : evenSubspace) =
      evenFourierCutoff (ccmFiniteEulerCarrierScale S)
        (ccmEulerBoundarySpectralEquiv T b hb y : evenSubspace) := by
  obtain ⟨f, rfl⟩ := ccmEulerBoundaryMap_surjective T b 1 hb zero_lt_one y
  rw [ccmEulerBoundaryTransition_source, ccmEulerBoundarySpectralEquiv_source,
    ccmEulerBoundarySpectralEquiv_source]
  exact (DFunLike.congr_fun (evenFourierCutoff_mul_of_le _ _
    (ccmFiniteEulerCarrierScale_mono hST)) (f : evenSubspace)).symm

/-- Exact transition kernel in the actual source chart. -/
theorem ccmEulerBoundaryTransition_eq_zero_iff (S T : Finset (HeightOneSpectrum ℤ))
    (hST : S ⊆ T) (b : ℝ) (hb : 0 < b) (y : ccmEulerBoundaryAnnulus T b 1) :
    ccmEulerBoundaryTransition S T hST b hb y = 0 ↔
      evenFourierCutoff (ccmFiniteEulerCarrierScale S)
        (ccmEulerBoundarySpectralEquiv T b hb y : evenSubspace) = 0 := by
  constructor
  · intro hy
    have h := ccmEulerBoundaryTransition_spectral S T hST b hb y
    rw [hy, map_zero] at h
    exact h.symm
  · intro hy
    apply (ccmEulerBoundarySpectralEquiv S b hb).injective
    apply Subtype.ext
    rw [map_zero]
    exact (ccmEulerBoundaryTransition_spectral S T hST b hb y).trans hy

end RHTower
