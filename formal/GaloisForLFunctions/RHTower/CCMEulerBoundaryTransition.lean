import GaloisForLFunctions.RHTower.CCMEulerBoundaryQuotient

/-!
# Source-preserving transitions of the actual Euler boundaries

The enlarged-gap kernels are nested in the direction forced by prime insertion.
Descending the original earlier boundary through the later source kernel gives
the unique bounded transition. Its composition law and adjoint return retain
the actual source rather than a freely chosen identification of annuli.
-/

noncomputable section

open IsDedekindDomain
open scoped BigOperators

namespace RHTower

theorem ccmFiniteEulerCarrierScale_mono {S T : Finset (HeightOneSpectrum ℤ)}
    (hST : S ⊆ T) : ccmFiniteEulerCarrierScale S ≤ ccmFiniteEulerCarrierScale T := by
  unfold ccmFiniteEulerCarrierScale
  have hp (v : HeightOneSpectrum ℤ) : (1 : ℝ) ≤ (Rat.HeightOneSpectrum.primesEquiv v : ℕ) := by
    exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv v).property.one_lt.le
  exact Finset.prod_le_prod_of_subset_of_one_le hST
    (fun v _ => zero_le_one.trans (hp v)) (fun v _ _ => hp v)

/-- Later prime stages forget a smaller source kernel. -/
theorem ccmEulerBoundaryMap_ker_antitone {S T : Finset (HeightOneSpectrum ℤ)}
    (hST : S ⊆ T) (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (ccmEulerBoundaryMap T b c hb hc).ker ≤ (ccmEulerBoundaryMap S b c hb hc).ker := by
  rw [ccmEulerBoundaryMap_ker, ccmEulerBoundaryMap_ker]
  intro f hf
  change evenFourierCutoff (ccmFiniteEulerCarrierScale T * c) (f : evenSubspace) = 0 at hf
  change evenFourierCutoff (ccmFiniteEulerCarrierScale S * c) (f : evenSubspace) = 0
  calc
    evenFourierCutoff (ccmFiniteEulerCarrierScale S * c) (f : evenSubspace) =
        evenFourierCutoff (ccmFiniteEulerCarrierScale S * c)
          (evenFourierCutoff (ccmFiniteEulerCarrierScale T * c) (f : evenSubspace)) :=
      (DFunLike.congr_fun (evenFourierCutoff_mul_of_le _ _
        (mul_le_mul_of_nonneg_right (ccmFiniteEulerCarrierScale_mono hST) hc.le))
          (f : evenSubspace)).symm
    _ = 0 := by rw [hf, map_zero]

/-- Descend the original earlier source boundary through the later source quotient. -/
def ccmEulerBoundaryTransition (S T : Finset (HeightOneSpectrum ℤ))
    (hST : S ⊆ T) (b : ℝ) (hb : 0 < b) :
    ccmEulerBoundaryAnnulus T b 1 →L[ℂ] ccmEulerBoundaryAnnulus S b 1 :=
  ((ccmEulerBoundaryMap T b 1 hb zero_lt_one).ker.liftQL
    (ccmEulerBoundaryMap S b 1 hb zero_lt_one)
      (ccmEulerBoundaryMap_ker_antitone hST b 1 hb zero_lt_one)).comp
    (ccmEulerBoundaryQuotientEquiv T b 1 hb zero_lt_one).symm.toContinuousLinearMap

/-- Exact source law, which determines the transition on its entire domain. -/
theorem ccmEulerBoundaryTransition_source (S T : Finset (HeightOneSpectrum ℤ))
    (hST : S ⊆ T) (b : ℝ) (hb : 0 < b) (f : evenCentralSoninCarrier b) :
    ccmEulerBoundaryTransition S T hST b hb (ccmEulerBoundaryMap T b 1 hb zero_lt_one f) =
      ccmEulerBoundaryMap S b 1 hb zero_lt_one f := by
  have hrepr := (ccmEulerBoundaryQuotientEquiv T b 1 hb zero_lt_one).symm_apply_apply
    (Submodule.Quotient.mk f)
  rw [ccmEulerBoundaryQuotientEquiv_apply_mk] at hrepr
  change ((ccmEulerBoundaryMap T b 1 hb zero_lt_one).ker.liftQL
    (ccmEulerBoundaryMap S b 1 hb zero_lt_one)
      (ccmEulerBoundaryMap_ker_antitone hST b 1 hb zero_lt_one))
    ((ccmEulerBoundaryQuotientEquiv T b 1 hb zero_lt_one).symm
      (ccmEulerBoundaryMap T b 1 hb zero_lt_one f)) = _
  rw [hrepr]
  rfl

theorem ccmEulerBoundaryTransition_surjective (S T : Finset (HeightOneSpectrum ℤ))
    (hST : S ⊆ T) (b : ℝ) (hb : 0 < b) :
    Function.Surjective (ccmEulerBoundaryTransition S T hST b hb) := by
  intro y
  obtain ⟨f, rfl⟩ := ccmEulerBoundaryMap_surjective S b 1 hb zero_lt_one y
  exact ⟨ccmEulerBoundaryMap T b 1 hb zero_lt_one f,
    ccmEulerBoundaryTransition_source S T hST b hb f⟩

/-- No other bounded map can retain the same actual source law. -/
theorem ccmEulerBoundaryTransition_unique (S T : Finset (HeightOneSpectrum ℤ))
    (hST : S ⊆ T) (b : ℝ) (hb : 0 < b)
    (L : ccmEulerBoundaryAnnulus T b 1 →L[ℂ] ccmEulerBoundaryAnnulus S b 1)
    (hL : ∀ f : evenCentralSoninCarrier b,
      L (ccmEulerBoundaryMap T b 1 hb zero_lt_one f) = ccmEulerBoundaryMap S b 1 hb zero_lt_one f) :
    L = ccmEulerBoundaryTransition S T hST b hb := by
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨f, rfl⟩ := ccmEulerBoundaryMap_surjective T b 1 hb zero_lt_one y
  exact (hL f).trans (ccmEulerBoundaryTransition_source S T hST b hb f).symm

theorem ccmEulerBoundaryTransition_self (S : Finset (HeightOneSpectrum ℤ))
    (b : ℝ) (hb : 0 < b) :
    ccmEulerBoundaryTransition S S (fun _ h => h) b hb = 1 := by
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨f, rfl⟩ := ccmEulerBoundaryMap_surjective S b 1 hb zero_lt_one y
  exact ccmEulerBoundaryTransition_source S S (fun _ h => h) b hb f

/-- Composition is forced by the original Euler source, with all factors retained. -/
theorem ccmEulerBoundaryTransition_comp (S T U : Finset (HeightOneSpectrum ℤ))
    (hST : S ⊆ T) (hTU : T ⊆ U) (b : ℝ) (hb : 0 < b) :
    (ccmEulerBoundaryTransition S T hST b hb).comp
      (ccmEulerBoundaryTransition T U hTU b hb) =
        ccmEulerBoundaryTransition S U (fun _ hv => hTU (hST hv)) b hb := by
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨f, rfl⟩ := ccmEulerBoundaryMap_surjective U b 1 hb zero_lt_one y
  simp only [ContinuousLinearMap.comp_apply, ccmEulerBoundaryTransition_source]

/-- The transition retains the actual earlier current return on every later source datum. -/
theorem ccmEulerBoundaryTransition_reconstructs_current
    (S T : Finset (HeightOneSpectrum ℤ)) (hST : S ⊆ T) (b : ℝ) (hb : 1 ≤ b)
    (f : evenCentralSoninCarrier b) :
    ccmFiniteEulerSourceCurrent S (f : evenSubspace) =
      -ContinuousLinearMap.adjoint (ccmFiniteEulerDenominator S)
        (ccmEulerBoundaryTransition S T hST b (zero_lt_one.trans_le hb)
          (ccmEulerBoundaryMap T b 1 (zero_lt_one.trans_le hb) zero_lt_one f) : evenSubspace) := by
  rw [ccmEulerBoundaryTransition_source]
  exact ccmFiniteEulerSourceCurrent_apply_sonin S hb f.property

end RHTower
