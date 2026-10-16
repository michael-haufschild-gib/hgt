import GaloisForLFunctions.RHTower.CHMDFiniteSampleGenerator

/-!
# Arithmetic operator images of actual cardinal sources

Every literal cardinal frame belongs to the maximal arithmetic operator domain.
Its signed generator images are the weighted cosine kernels. Small translated
frames have the explicit phase-weighted Fourier kernels as their images, so the
operator construction retains both Fourier directions.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

def cardinalCarrierFinset (a : ℂ) : Finset zetaZeroConfig.carrier :=
  ((cardinalOrbit_finite a).preimage gammaOf_carrier_injective.injOn).toFinset

theorem mem_cardinalCarrierFinset (a : ℂ) (ρ : zetaZeroConfig.carrier) :
    ρ ∈ cardinalCarrierFinset a ↔ gammaOf ρ ∈ cardinalOrbit a :=
  Set.Finite.mem_toFinset _

theorem cardinalOrbit_neg_mem {a z : ℂ} (hz : z ∈ cardinalOrbit a) :
    -z ∈ cardinalOrbit a := by
  simp only [cardinalOrbit, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with h | h | h | h <;> simp [cardinalOrbit, h]

theorem finiteMassSampleSupport_of_orbit {a : ℂ} {w : MassSpace}
    (h : ∀ z : ℂ, XiC z = 0 → z ∉ cardinalOrbit a → massFourierReadout w z = 0) :
    FiniteMassSampleSupport (cardinalCarrierFinset a) w := by
  intro ρ hρ
  have hn : gammaOf ρ ∉ cardinalOrbit a := by
    simpa only [mem_cardinalCarrierFinset] using hρ
  have hneg : -gammaOf ρ ∉ cardinalOrbit a := by
    intro he
    exact hn (by simpa only [neg_neg] using cardinalOrbit_neg_mem he)
  have hz := CHMDStage16.XiC_gammaOf_eq_zero ρ
  exact ⟨h _ hz hn, h _ (by rw [XiC_even, hz]) hneg⟩

theorem CardinalGraphFrame.mass_re_sample {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) {z : ℂ} (hzero : XiC z = 0) :
    massFourierReadout (sourceMap F.reVector) z = cardinalOrbitValue a 1 z := by
  rw [massFourierReadout_source _ (abs_im_lt_half_of_XiC_eq_zero hzero).le,
    graphFourierReadout_of_source F.re_source]
  simpa only [cardinalRealSource, one_mul] using cardinalRealSource_paperFT ha hz 1 hzero

theorem CardinalGraphFrame.mass_im_sample {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) {z : ℂ} (hzero : XiC z = 0) :
    massFourierReadout (sourceMap F.imVector) z = cardinalOrbitValue a (-I) z := by
  rw [massFourierReadout_source _ (abs_im_lt_half_of_XiC_eq_zero hzero).le,
    graphFourierReadout_of_source F.im_source]
  simpa [cardinalRealSource, Complex.mul_re] using cardinalRealSource_paperFT ha hz (-I) hzero

theorem CardinalGraphFrame.finite_re_support {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) :
    FiniteMassSampleSupport (cardinalCarrierFinset a) (sourceMap F.reVector) := by
  apply finiteMassSampleSupport_of_orbit
  intro z hzero ho
  rw [F.mass_re_sample ha hz hzero, cardinalOrbitValue_eq_zero ho]

theorem CardinalGraphFrame.finite_im_support {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) :
    FiniteMassSampleSupport (cardinalCarrierFinset a) (sourceMap F.imVector) := by
  apply finiteMassSampleSupport_of_orbit
  intro z hzero ho
  rw [F.mass_im_sample ha hz hzero, cardinalOrbitValue_eq_zero ho]

def cardinalRealGeneratorImage (a : ℂ) (hz : XiC a = 0) : MassSpace :=
  cardinalOrbitMass a • massShiftedCosineRealKernel ⟨a, Or.inl hz⟩ 0

def cardinalImagGeneratorImage (a : ℂ) (hz : XiC a = 0) : MassSpace :=
  cardinalOrbitMass a • massShiftedCosineImagKernel ⟨a, Or.inl hz⟩ 0

theorem cardinalRealGeneratorImage_pair {a : ℂ} (hz : XiC a = 0) (q : SourceGraph) :
    ⟪cardinalRealGeneratorImage a hz, sourceMap q⟫_ℝ =
      cardinalOrbitMass a * (graphCosineReadout q a).re := by
  rw [cardinalRealGeneratorImage, real_inner_smul_left, massShiftedCosineRealKernel_pair,
    graphCosineReadout_eq_half_fourier q (abs_im_lt_half_of_XiC_eq_zero hz).le]
  simp only [shiftedCosineReadout, Complex.ofReal_zero, mul_zero, exp_zero, one_mul]

theorem cardinalImagGeneratorImage_pair {a : ℂ} (hz : XiC a = 0) (q : SourceGraph) :
    ⟪cardinalImagGeneratorImage a hz, sourceMap q⟫_ℝ =
      cardinalOrbitMass a * (graphCosineReadout q a).im := by
  rw [cardinalImagGeneratorImage, real_inner_smul_left, massShiftedCosineImagKernel_pair,
    graphCosineReadout_eq_half_fourier q (abs_im_lt_half_of_XiC_eq_zero hz).le]
  simp only [shiftedCosineReadout, Complex.ofReal_zero, mul_zero, exp_zero, one_mul]

theorem CardinalGraphFrame.re_resolvent_preimage {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) :
    resolvent ((2 : ℝ) • sourceMap F.reVector + cardinalRealGeneratorImage a hz) =
      sourceMap F.reVector := by
  apply resolvent_preimage_of_sourcePair
  intro q
  rw [sourcePair_symm, F.pair_re ha hz, cardinalRealGeneratorImage_pair]

theorem CardinalGraphFrame.im_resolvent_preimage {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) :
    resolvent ((2 : ℝ) • sourceMap F.imVector + cardinalImagGeneratorImage a hz) =
      sourceMap F.imVector := by
  apply resolvent_preimage_of_sourcePair
  intro q
  rw [sourcePair_symm, F.pair_im ha hz, cardinalImagGeneratorImage_pair]

theorem CardinalGraphFrame.finite_re_image {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) :
    massFiniteImage (cardinalCarrierFinset a) (sourceMap F.reVector) =
      cardinalRealGeneratorImage a hz :=
  add_left_cancel (resolvent_injective ((finite_samples_resolvent_identity
    (F.finite_re_support ha hz)).trans (F.re_resolvent_preimage ha hz).symm))

theorem CardinalGraphFrame.finite_im_image {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) :
    massFiniteImage (cardinalCarrierFinset a) (sourceMap F.imVector) =
      cardinalImagGeneratorImage a hz :=
  add_left_cancel (resolvent_injective ((finite_samples_resolvent_identity
    (F.finite_im_support ha hz)).trans (F.im_resolvent_preimage ha hz).symm))

theorem CardinalGraphFrame.re_mem_arithmetic_domain {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) : sourceMap F.reVector ∈ arithmeticGenerator.domain :=
  finite_samples_mem_arithmetic_domain (F.finite_re_support ha hz)

theorem CardinalGraphFrame.im_mem_arithmetic_domain {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) : sourceMap F.imVector ∈ arithmeticGenerator.domain :=
  finite_samples_mem_arithmetic_domain (F.finite_im_support ha hz)

theorem CardinalGraphFrame.re_generator_eq {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) :
    arithmeticGenerator ⟨sourceMap F.reVector, F.re_mem_arithmetic_domain ha hz⟩ =
      sourceMap F.reVector + cardinalRealGeneratorImage a hz :=
  arithmeticGenerator_of_resolvent_preimage (F.re_resolvent_preimage ha hz)

theorem CardinalGraphFrame.im_generator_eq {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) :
    arithmeticGenerator ⟨sourceMap F.imVector, F.im_mem_arithmetic_domain ha hz⟩ =
      sourceMap F.imVector + cardinalImagGeneratorImage a hz :=
  arithmeticGenerator_of_resolvent_preimage (F.im_resolvent_preimage ha hz)

/-- Actual translated cardinal detectors belong to the maximal domain and have
explicit phase-weighted Fourier images. Both source representatives are retained. -/
theorem exists_translatedCardinalOperatorFrame {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0)
    (t : ℝ) (ht : |t| ≤ CHMDThetaTranslate.radius) :
    ∃ (u v : SourceGraph) (hu : sourceMap u ∈ arithmeticGenerator.domain)
      (hv : sourceMap v ∈ arithmeticGenerator.domain),
      u.val.fst =ᵐ[massMeasure]
        phiDoobInv (CHMDTranslation.translate (fun x => (divisorCardinalSource a x).re) t) ∧
      v.val.fst =ᵐ[massMeasure]
        phiDoobInv (CHMDTranslation.translate (fun x => (divisorCardinalSource a x).im) t) ∧
      arithmeticGenerator ⟨sourceMap u, hu⟩ = sourceMap u +
        cardinalOrbitMass a • massShiftedCosineRealKernel ⟨a, Or.inl hz⟩ t ∧
      arithmeticGenerator ⟨sourceMap v, hv⟩ = sourceMap v +
        cardinalOrbitMass a • massShiftedCosineImagKernel ⟨a, Or.inl hz⟩ t := by
  obtain ⟨u, v, hus, hvs, hu, hv⟩ := exists_translatedCardinalFrame ha hz t ht
  have hru : resolvent ((2 : ℝ) • sourceMap u +
      cardinalOrbitMass a • massShiftedCosineRealKernel ⟨a, Or.inl hz⟩ t) = sourceMap u := by
    apply resolvent_preimage_of_sourcePair
    intro q
    rw [sourcePair_symm, hu, real_inner_smul_left, massShiftedCosineRealKernel_pair]
  have hrv : resolvent ((2 : ℝ) • sourceMap v +
      cardinalOrbitMass a • massShiftedCosineImagKernel ⟨a, Or.inl hz⟩ t) = sourceMap v := by
    apply resolvent_preimage_of_sourcePair
    intro q
    rw [sourcePair_symm, hv, real_inner_smul_left, massShiftedCosineImagKernel_pair]
  exact ⟨u, v, mem_arithmetic_domain_of_resolvent_preimage hru,
    mem_arithmetic_domain_of_resolvent_preimage hrv, hus, hvs,
    arithmeticGenerator_of_resolvent_preimage hru, arithmeticGenerator_of_resolvent_preimage hrv⟩

/-- A nonzero actual cardinal packet with positive signed energy is in the
maximal arithmetic domain, with its literal generator image identified. -/
theorem exists_positive_cardinal_operator_packet :
    ∃ (a : ℝ) (hz : XiC (a : ℂ) = 0) (F : CardinalGraphFrame (a : ℂ)),
      0 < a ∧ 0 < sourceEnergy F.reVector ∧
      sourceMap F.reVector ∈ arithmeticGenerator.domain ∧
      resolvent ((2 : ℝ) • sourceMap F.reVector + cardinalRealGeneratorImage (a : ℂ) hz) =
        sourceMap F.reVector := by
  obtain ⟨a, F, ha, hz, hE, _, _⟩ := exists_positive_primitive_cardinal_frame
  exact ⟨a, hz, F, ha, hE, F.re_mem_arithmetic_domain ha hz, F.re_resolvent_preimage ha hz⟩

end RHTower.CHMDDoobGraph
