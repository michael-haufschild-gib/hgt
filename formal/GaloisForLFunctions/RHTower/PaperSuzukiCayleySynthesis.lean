import GaloisForLFunctions.RHTower.PaperSuzukiCayleyReconstruction
import GaloisForLFunctions.RHTower.PaperSuzukiCarrierNullSets
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiCarrierCayleySynthesisOperator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Order.Filter.AtTopBot.Interval

/-! # Full pointwise convergence of the actual Suzuki synthesis operators

The paper Fourier endpoint supplies full-sequence pointwise convergence. The
existing native norm limit identifies that limit with the actual reference and
carrier synthesis operators. Countable input families and all finite complex
mixtures share one Lebesgue-null exceptional set.
-/

namespace RiemannGaussian
noncomputable section
open MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal lp
local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- The circle reconstruction of the literal bilateral coefficient sequence. -/
def paperSuzukiCircleSynthesis (a : ℓ²(ℤ, ℂ)) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := Real.pi)) :=
  (fourierBasis (T := Real.pi)).repr.symm a

theorem paperSuzukiCircleSynthesis_fourierCoeff (a : ℓ²(ℤ, ℂ)) (n : ℤ) :
    fourierCoeff (paperSuzukiCircleSynthesis a) n = a n := by
  rw [← fourierBasis_repr, paperSuzukiCircleSynthesis, LinearIsometryEquiv.apply_symm_apply]

/-- The literal finite Laurent polynomial in the native Cayley boundary coordinate. -/
def paperSuzukiBilateralPartialSum (a : ℓ²(ℤ, ℂ)) (M : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a n * suzukiXiCarrierCayleyBoundaryZPower n t

theorem paperSuzukiBilateralPartialSum_eq (a : ℓ²(ℤ, ℂ)) (M : ℕ) (t : ℝ) :
    paperSuzukiBilateralPartialSum a M t =
      paperCircleFourierPartialSum Real.pi (paperSuzukiCircleSynthesis a) M
        (paperSuzukiCayleyChart t) := by
  simp only [paperSuzukiBilateralPartialSum, paperCircleFourierPartialSum,
    paperSuzukiCircleSynthesis_fourierCoeff,
    suzukiXiCarrierCayleyBoundaryZPower_eq_shifted_fourier, paperSuzukiCayleyChart]

private theorem circle_limit_ae (a : ℓ²(ℤ, ℂ)) :
    ∀ᵐ t ∂volume, Tendsto (fun M => paperSuzukiBilateralPartialSum a M t) atTop
      (𝓝 (paperSuzukiCircleSynthesis a (paperSuzukiCayleyChart t))) := by
  obtain ⟨E, _, hz, hc⟩ := paperCircleLp_fourier_convergence Real.pi
    (paperSuzukiCircleSynthesis a)
  have h : ∀ᵐ x ∂AddCircle.haarAddCircle,
      Tendsto (fun M => paperCircleFourierPartialSum Real.pi (paperSuzukiCircleSynthesis a) M x)
        atTop (𝓝 (paperSuzukiCircleSynthesis a x)) := by
    filter_upwards [compl_mem_ae_iff.mpr hz] with x hx
    exact hc x hx
  simpa only [← paperSuzukiBilateralPartialSum_eq] using
    paperSuzukiCayleyChart_quasiMeasurePreserving.ae h

private theorem reference_partial_ae (a : ℓ²(ℤ, ℂ)) (M : ℕ) :
    (∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a n • suzukiXiCarrierCayleyReferenceOrbit n :
      Lp ℂ 2 suzukiXiCarrierCayleyReferenceMeasure) =ᵐ[
      suzukiXiCarrierCayleyReferenceMeasure] paperSuzukiBilateralPartialSum a M := by
  have hsum := Lp.coeFn_fun_finsetSum (Finset.Icc (-(M : ℤ)) (M : ℤ))
    (fun n => a n • suzukiXiCarrierCayleyReferenceOrbit n)
  have hterms : ∀ᵐ t ∂suzukiXiCarrierCayleyReferenceMeasure, ∀ n : ℤ,
      (a n • suzukiXiCarrierCayleyReferenceOrbit n) t =
        a n * suzukiXiCarrierCayleyBoundaryZPower n t := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [Lp.coeFn_smul (a n) (suzukiXiCarrierCayleyReferenceOrbit n),
      suzukiXiCarrierCayleyReferenceOrbit_ae n] with t hs ho
    simp only [hs, Pi.smul_apply, smul_eq_mul, ho]
  filter_upwards [hsum, hterms] with t hs ht
  exact hs.trans (Finset.sum_congr rfl (fun n _ => ht n))

private theorem reference_partial_tendsto (a : ℓ²(ℤ, ℂ)) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      a n • suzukiXiCarrierCayleyReferenceOrbit n) atTop
      (𝓝 (suzukiXiCarrierCayleyReferenceSynthesisOperator a)) := by
  have hsingle : HasSum (fun n : ℤ => lp.single 2 n (a n)) a :=
    lp.hasSum_single ENNReal.ofNat_ne_top a
  have hs : HasSum (fun n : ℤ => a n • suzukiXiCarrierCayleyReferenceOrbit n)
      (suzukiXiCarrierCayleyReferenceSynthesisOperator a) := by
    simpa only [suzukiXiCarrierCayleyReferenceSynthesisOperator_single] using
      suzukiXiCarrierCayleyReferenceSynthesisOperator.hasSum hsingle
  exact hs.comp (Finset.tendsto_Icc_neg (R := ℤ))

/-- The native infinite reference operator is the actual circle reconstruction in Cayley coordinates. -/
theorem paperSuzukiReferenceSynthesis_ae (a : ℓ²(ℤ, ℂ)) :
    suzukiXiCarrierCayleyReferenceSynthesisOperator a =ᵐ[suzukiXiCarrierCayleyReferenceMeasure]
      fun t => paperSuzukiCircleSynthesis a (paperSuzukiCayleyChart t) := by
  have hac : suzukiXiCarrierCayleyReferenceMeasure ≪ volume :=
    withDensity_absolutelyContinuous volume _
  obtain ⟨ns, hns, hc⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (reference_partial_tendsto a)).exists_seq_tendsto_ae
  have he := ae_all_iff.mpr (reference_partial_ae a)
  filter_upwards [hc, he, (circle_limit_ae a).filter_mono hac.ae_le] with t ht he hp
  have ht' : Tendsto (fun M => paperSuzukiBilateralPartialSum a (ns M) t) atTop
      (𝓝 (suzukiXiCarrierCayleyReferenceSynthesisOperator a t)) := by
    simpa only [he] using ht
  exact tendsto_nhds_unique ht' (hp.comp hns.tendsto_atTop)

private theorem reference_ae_reconstruction (a : ℓ²(ℤ, ℂ)) :
    ∀ᵐ t ∂volume, Tendsto (fun M => paperSuzukiBilateralPartialSum a M t) atTop
      (𝓝 (suzukiXiCarrierCayleyReferenceSynthesisOperator a t)) := by
  have hac : volume ≪ suzukiXiCarrierCayleyReferenceMeasure := by
    apply withDensity_absolutelyContinuous'
    · exact (measurable_const.add (measurable_id.pow_const 2)).inv.ennreal_ofReal.aemeasurable
    · exact Eventually.of_forall (fun t => by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        positivity)
  filter_upwards [hac.ae_eq (paperSuzukiReferenceSynthesis_ae a), circle_limit_ae a] with t he ht
  rwa [he]

/-- The reference synthesis operator is recovered at Lebesgue-almost every point, along all cutoffs. -/
theorem paperSuzukiReference_common_reconstruction {κ : Type*} [Countable κ]
    (a : κ → ℓ²(ℤ, ℂ)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, ∀ j, Tendsto (fun M => paperSuzukiBilateralPartialSum (a j) M t) atTop
        (𝓝 (suzukiXiCarrierCayleyReferenceSynthesisOperator (a j) t)) := by
  have ha := ae_all_iff.mpr (fun j => reference_ae_reconstruction (a j))
  obtain ⟨E, hsub, hm, hz⟩ := exists_measurable_superset_of_null (ae_iff.mp ha)
  refine ⟨E, hm, hz, ?_⟩
  intro t ht
  by_contra h
  exact ht (hsub h)

/-- The original arithmetic carrier synthesis is recovered Lebesgue-almost everywhere. -/
theorem paperSuzukiCarrier_common_reconstruction {κ : Type*} [Countable κ]
    (a : κ → ℓ²(ℤ, ℂ)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, ∀ j, Tendsto (fun M => paperSuzukiBilateralPartialSum (a j) M t) atTop
        (𝓝 (suzukiXiCarrierCayleyBilateralSynthesisOperator (a j) t)) := by
  have hac : suzukiXiCarrierNevanlinnaMeasure ≪ volume :=
    withDensity_absolutelyContinuous volume _
  have ha : ∀ᵐ t ∂suzukiXiCarrierNevanlinnaMeasure, ∀ j,
      Tendsto (fun M => paperSuzukiBilateralPartialSum (a j) M t) atTop
        (𝓝 (suzukiXiCarrierCayleyBilateralSynthesisOperator (a j) t)) := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [(reference_ae_reconstruction (a j)).filter_mono hac.ae_le,
      suzukiXiCarrierCayleyReferenceToCarrier_ae
        (suzukiXiCarrierCayleyReferenceSynthesisOperator (a j))] with t ht he
    change suzukiXiCarrierCayleyBilateralSynthesisOperator (a j) t =
      suzukiXiCarrierCayleyReferenceSynthesisOperator (a j) t at he
    rwa [he]
  have hv := ha.filter_mono paperSuzukiVolume_absolutelyContinuous_carrier.ae_le
  obtain ⟨E, hsub, hm, hz⟩ := exists_measurable_superset_of_null (ae_iff.mp hv)
  refine ⟨E, hm, hz, ?_⟩
  intro t ht
  by_contra h
  exact ht (hsub h)

/-- Every finite mixture of reference-synthesized inputs shares the Lebesgue-null set. -/
theorem paperSuzukiReference_common_span_reconstruction {κ : Type*} [Countable κ]
    (a : κ → ℓ²(ℤ, ℂ)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, ∀ (S : Finset κ) (c : κ → ℂ),
        Tendsto (fun M => ∑ j ∈ S, c j * paperSuzukiBilateralPartialSum (a j) M t) atTop
          (𝓝 (∑ j ∈ S, c j * suzukiXiCarrierCayleyReferenceSynthesisOperator (a j) t)) := by
  obtain ⟨E, hm, hz, hc⟩ := paperSuzukiReference_common_reconstruction a
  exact ⟨E, hm, hz, fun t ht S c => tendsto_finsetSum S
    (fun j _ => (hc t ht j).const_mul (c j))⟩

/-- Arbitrary finite complex mixtures of actual carrier outputs share one Lebesgue-null set. -/
theorem paperSuzukiCarrier_common_span_reconstruction {κ : Type*} [Countable κ]
    (a : κ → ℓ²(ℤ, ℂ)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, ∀ (S : Finset κ) (c : κ → ℂ),
        Tendsto (fun M => ∑ j ∈ S, c j * paperSuzukiBilateralPartialSum (a j) M t) atTop
          (𝓝 (∑ j ∈ S, c j * suzukiXiCarrierCayleyBilateralSynthesisOperator (a j) t)) := by
  obtain ⟨E, hm, hz, hc⟩ := paperSuzukiCarrier_common_reconstruction a
  exact ⟨E, hm, hz, fun t ht S c => tendsto_finsetSum S
    (fun j _ => (hc t ht j).const_mul (c j))⟩

end
end RiemannGaussian
