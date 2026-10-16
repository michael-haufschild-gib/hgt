import GaloisForLFunctions.RHTower.CHMDCardinalOperatorAction

/-!
# Algebraic images of finite-sample mass vectors

Finite Xi-sample support is stable under real linear combinations. Its actual
signed generator images form a subspace of the literal sampling-kernel span.
Every translated cardinal phase kernel is an image of a constructed source.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

theorem massFourierReadout_zero {z : ℂ} (hz : |z.im| ≤ 1/2) :
    massFourierReadout (0 : MassSpace) z = 0 := by
  rw [← massFourierReadoutCLM_apply _ hz, map_zero]

theorem massFourierReadout_add (u v : MassSpace) {z : ℂ} (hz : |z.im| ≤ 1/2) :
    massFourierReadout (u+v) z = massFourierReadout u z + massFourierReadout v z := by
  simpa only [massFourierReadoutCLM_apply] using (massFourierReadoutCLM z hz).map_add u v

theorem massFourierReadout_smul (c : ℝ) (w : MassSpace) {z : ℂ} (hz : |z.im| ≤ 1/2) :
    massFourierReadout (c • w) z = (c : ℂ) * massFourierReadout w z := by
  simpa only [massFourierReadoutCLM_apply, Complex.real_smul] using
    (massFourierReadoutCLM z hz).map_smul c w

theorem FiniteMassSampleSupport.zero (S : Finset zetaZeroConfig.carrier) :
    FiniteMassSampleSupport S 0 := by
  intro ρ _
  exact ⟨massFourierReadout_zero (gammaOf_mem_closedStrip ρ),
    massFourierReadout_zero (neg_gammaOf_mem_closedStrip ρ)⟩

open Classical in
theorem FiniteMassSampleSupport.add {S T : Finset zetaZeroConfig.carrier}
    {u v : MassSpace} (hu : FiniteMassSampleSupport S u) (hv : FiniteMassSampleSupport T v) :
    FiniteMassSampleSupport (S ∪ T) (u+v) := by
  classical
  intro ρ hρ
  have hs : ρ ∉ S := fun h => hρ (Finset.mem_union.mpr (Or.inl h))
  have ht : ρ ∉ T := fun h => hρ (Finset.mem_union.mpr (Or.inr h))
  constructor
  · rw [massFourierReadout_add _ _ (gammaOf_mem_closedStrip ρ), (hu ρ hs).1, (hv ρ ht).1, add_zero]
  · rw [massFourierReadout_add _ _ (neg_gammaOf_mem_closedStrip ρ), (hu ρ hs).2, (hv ρ ht).2, add_zero]

theorem FiniteMassSampleSupport.smul {S : Finset zetaZeroConfig.carrier}
    {w : MassSpace} (hw : FiniteMassSampleSupport S w) (c : ℝ) :
    FiniteMassSampleSupport S (c • w) := by
  intro ρ hρ
  constructor
  · rw [massFourierReadout_smul _ _ (gammaOf_mem_closedStrip ρ), (hw ρ hρ).1, mul_zero]
  · rw [massFourierReadout_smul _ _ (neg_gammaOf_mem_closedStrip ρ), (hw ρ hρ).2, mul_zero]

/-- Actual signed generator images of finite-sample mass vectors. -/
def finiteSampleImageSpace : Submodule ℝ MassSpace where
  carrier b := ∃ (S : Finset zetaZeroConfig.carrier) (w : MassSpace),
    FiniteMassSampleSupport S w ∧ resolvent ((2 : ℝ) • w + b) = w
  zero_mem' := ⟨∅, 0, FiniteMassSampleSupport.zero _, by simp⟩
  add_mem' := by
    classical
    rintro b c ⟨S, u, hu, hru⟩ ⟨T, v, hv, hrv⟩
    refine ⟨S ∪ T, u+v, hu.add hv, ?_⟩
    calc
      _ = resolvent (((2 : ℝ) • u + b) + ((2 : ℝ) • v + c)) := congrArg resolvent (by module)
      _ = u+v := by rw [map_add, hru, hrv]
  smul_mem' := by
    rintro c b ⟨S, w, hw, hr⟩
    refine ⟨S, c • w, hw.smul c, ?_⟩
    calc
      _ = resolvent (c • ((2 : ℝ) • w + b)) := congrArg resolvent (by module)
      _ = c • w := by rw [map_smul, hr]

theorem massWeightedRealKernel_mem_submodule (P : Submodule ℝ MassSpace)
    (c : ℂ) (a : MassSamplePoint) (hr : massSampleRealKernel a ∈ P)
    (hi : massSampleImagKernel a ∈ P) : massWeightedRealKernel c a ∈ P :=
  P.sub_mem (P.smul_mem _ hr) (P.smul_mem _ hi)

theorem massWeightedImagKernel_mem_submodule (P : Submodule ℝ MassSpace)
    (c : ℂ) (a : MassSamplePoint) (hr : massSampleRealKernel a ∈ P)
    (hi : massSampleImagKernel a ∈ P) : massWeightedImagKernel c a ∈ P :=
  P.add_mem (P.smul_mem _ hr) (P.smul_mem _ hi)

theorem massSampleRealKernel_mem_span (a : MassSamplePoint) :
    massSampleRealKernel a ∈ massSamplingSpan := Submodule.subset_span (Or.inl ⟨a, rfl⟩)

theorem massSampleImagKernel_mem_span (a : MassSamplePoint) :
    massSampleImagKernel a ∈ massSamplingSpan := Submodule.subset_span (Or.inr ⟨a, rfl⟩)

theorem massFiniteImage_mem_samplingSpan (S : Finset zetaZeroConfig.carrier) (w : MassSpace) :
    massFiniteImage S w ∈ massSamplingSpan := by
  apply massSamplingSpan.add_mem
  · apply massSamplingSpan.sum_mem
    intro ρ _
    exact massSamplingSpan.add_mem
      (massWeightedRealKernel_mem_submodule _ _ _ (massSampleRealKernel_mem_span _)
        (massSampleImagKernel_mem_span _))
      (massWeightedRealKernel_mem_submodule _ _ _ (massSampleRealKernel_mem_span _)
        (massSampleImagKernel_mem_span _))
  · exact massSamplingSpan.sub_mem
      (massSamplingSpan.smul_mem _ (massSampleRealKernel_mem_span _))
      (massSamplingSpan.smul_mem _ (massSampleRealKernel_mem_span _))

theorem finiteSampleImageSpace_le_samplingSpan : finiteSampleImageSpace ≤ massSamplingSpan := by
  rintro b ⟨S, w, hw, hr⟩
  have he : b = massFiniteImage S w := add_left_cancel
    (resolvent_injective (hr.trans (finite_samples_resolvent_identity hw).symm))
  rw [he]
  exact massFiniteImage_mem_samplingSpan S w

theorem translated_cardinal_re_finite_support {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0)
    (t : ℝ) {p : SourceGraph}
    (hp : p.val.fst =ᵐ[massMeasure]
      phiDoobInv (CHMDTranslation.translate (fun x => (divisorCardinalSource a x).re) t)) :
    FiniteMassSampleSupport (cardinalCarrierFinset a) (sourceMap p) := by
  apply finiteMassSampleSupport_of_orbit
  intro z hzero ho
  rw [massFourierReadout_source _ (abs_im_lt_half_of_XiC_eq_zero hzero).le,
    graphFourierReadout_of_source hp, paperFT_translate_real]
  have he := cardinalRealSource_paperFT ha hz 1 hzero
  rw [cardinalOrbitValue_eq_zero ho] at he
  have h0 : paperFT (fun x => ((divisorCardinalSource a x).re : ℂ)) z = 0 := by
    simpa only [cardinalRealSource, one_mul] using he
  rw [h0, mul_zero]

theorem translated_cardinal_im_finite_support {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0)
    (t : ℝ) {p : SourceGraph}
    (hp : p.val.fst =ᵐ[massMeasure]
      phiDoobInv (CHMDTranslation.translate (fun x => (divisorCardinalSource a x).im) t)) :
    FiniteMassSampleSupport (cardinalCarrierFinset a) (sourceMap p) := by
  apply finiteMassSampleSupport_of_orbit
  intro z hzero ho
  rw [massFourierReadout_source _ (abs_im_lt_half_of_XiC_eq_zero hzero).le,
    graphFourierReadout_of_source hp, paperFT_translate_real]
  have he := cardinalRealSource_paperFT ha hz (-I) hzero
  rw [cardinalOrbitValue_eq_zero ho] at he
  have h0 : paperFT (fun x => ((divisorCardinalSource a x).im : ℂ)) z = 0 := by
    simpa [cardinalRealSource, Complex.mul_re] using he
  rw [h0, mul_zero]

/-- The phase kernels themselves, after division by the positive orbit mass,
are signed images of actual finite-support sources. -/
theorem phase_kernels_mem_finiteSampleImageSpace {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0)
    (t : ℝ) (ht : |t| ≤ CHMDThetaTranslate.radius) :
    massShiftedCosineRealKernel ⟨a, Or.inl hz⟩ t ∈ finiteSampleImageSpace ∧
    massShiftedCosineImagKernel ⟨a, Or.inl hz⟩ t ∈ finiteSampleImageSpace := by
  obtain ⟨u, v, hu, hv, hus, hvs, hgu, hgv⟩ := exists_translatedCardinalOperatorFrame ha hz t ht
  have hru := arithmeticGenerator_identity ⟨sourceMap u, hu⟩
  have hrv := arithmeticGenerator_identity ⟨sourceMap v, hv⟩
  rw [hgu] at hru
  rw [hgv] at hrv
  have hR : cardinalOrbitMass a • massShiftedCosineRealKernel ⟨a, Or.inl hz⟩ t ∈
      finiteSampleImageSpace := ⟨cardinalCarrierFinset a, sourceMap u,
    translated_cardinal_re_finite_support ha hz t hus, by simpa only [two_smul, add_assoc] using hru⟩
  have hI : cardinalOrbitMass a • massShiftedCosineImagKernel ⟨a, Or.inl hz⟩ t ∈
      finiteSampleImageSpace := ⟨cardinalCarrierFinset a, sourceMap v,
    translated_cardinal_im_finite_support ha hz t hvs, by simpa only [two_smul, add_assoc] using hrv⟩
  have hm := (cardinalOrbitMass_pos ha hz).ne'
  constructor
  · simpa only [smul_smul, inv_mul_cancel₀ hm, one_smul] using
      finiteSampleImageSpace.smul_mem (cardinalOrbitMass a)⁻¹ hR
  · simpa only [smul_smul, inv_mul_cancel₀ hm, one_smul] using
      finiteSampleImageSpace.smul_mem (cardinalOrbitMass a)⁻¹ hI

end RHTower.CHMDDoobGraph
