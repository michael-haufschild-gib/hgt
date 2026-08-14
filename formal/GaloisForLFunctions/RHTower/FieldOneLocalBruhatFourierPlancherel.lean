import GaloisForLFunctions.RHTower.FieldOneFiniteStageSelfDualHaar
import GaloisForLFunctions.RHTower.FieldOnePadicBruhatFourierPlancherel

/-!
# Local Plancherel on rational height-one completions

The canonical continuous algebra equivalence from every rational completion
`ℚ_v` to literal `ℚ_p` transports source conductor-zero Haar measure and
source additive character exactly.  Consequently the literal local Fourier
integral preserves the `L²` norm of every local Bruhat function.  No scalar or
isometry premise remains.
-/

namespace GaloisForLFunctions.RHTower
noncomputable section
open IsDedekindDomain MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

instance fieldOneRationalCompletionPrimeFact (v : HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v)) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- Continuous additive equivalence underlying the canonical local p-adic equivalence. -/
def fieldOneLocalPadicContinuousAddEquiv (v : HeightOneSpectrum ℤ) :
    v.adicCompletion ℚ ≃ₜ+ ℚ_[Rat.HeightOneSpectrum.primesEquiv v] :=
  { toAddEquiv := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv.toAddEquiv
    continuous_toFun := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).continuous
    continuous_invFun := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.continuous }

set_option backward.isDefEq.respectTransparency false in
 theorem fieldOneLocalSelfDualHaar_map_padic (v : HeightOneSpectrum ℤ) :
    Measure.map (fun x => fieldOneLocalPadicContinuousAddEquiv v x)
        (fieldOneLocalSelfDualAddHaar v) =
      fieldOnePadicUnitBallNormalizedHaar
        (Rat.HeightOneSpectrum.primesEquiv v) := by
  let p : ℕ := Rat.HeightOneSpectrum.primesEquiv v
  let e := fieldOneLocalPadicContinuousAddEquiv v
  let μmap := Measure.map (fun x => e x) (fieldOneLocalSelfDualAddHaar v)
  letI : μmap.IsAddHaarMeasure := by
    dsimp [μmap]
    exact ContinuousAddEquiv.isAddHaarMeasure_map
      (fieldOneLocalSelfDualAddHaar v) e
  have hmass : μmap (Set.range ((↑) : ℤ_[p] → ℚ_[p])) = 1 := by
    have hball : MeasurableSet (Set.range ((↑) : ℤ_[p] → ℚ_[p])) :=
      PadicInt.isOpenEmbedding_coe.isOpen_range.measurableSet
    change Measure.map (fun x => e x)
      (fieldOneLocalSelfDualAddHaar v)
        (Set.range ((↑) : ℤ_[p] → ℚ_[p])) = 1
    have hmap :
        Measure.map (fun x => e x) (fieldOneLocalSelfDualAddHaar v)
            (Set.range ((↑) : ℤ_[p] → ℚ_[p])) =
          fieldOneLocalSelfDualAddHaar v
            ((fun x => e x) ⁻¹' Set.range ((↑) : ℤ_[p] → ℚ_[p])) :=
      Measure.map_apply (f := fun x => e x)
        e.continuous.measurable hball
    rw [hmap]
    rw [show e ⁻¹' Set.range ((↑) : ℤ_[p] → ℚ_[p]) =
        (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) by
      ext x
      constructor
      · intro hx
        have hex : Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x ∈
            PadicInt.subring p := by
          simpa [e, fieldOneLocalPadicContinuousAddEquiv, p] using hx
        obtain ⟨z, hz, hzx⟩ :=
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).surjOn hex
        have hzx' : z = x :=
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective hzx
        simpa [hzx'] using hz
      · intro hx
        have hmap := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo hx
        simpa [e, fieldOneLocalPadicContinuousAddEquiv, p] using hmap]
    exact fieldOneLocalSelfDualAddHaar_integers v
  have heq := Measure.isAddLeftInvariant_eq_smul_of_regular
    μmap (fieldOnePadicUnitBallNormalizedHaar p)
  let c : ℝ≥0 := Measure.addHaarScalarFactor μmap
    (fieldOnePadicUnitBallNormalizedHaar p)
  have hc : c = 1 := by
    have hmass' := congrArg
      (fun μ : Measure ℚ_[p] => μ (Set.range ((↑) : ℤ_[p] → ℚ_[p]))) heq
    have hpadicmass : fieldOnePadicUnitBallNormalizedHaar p
        (Set.range ((↑) : ℤ_[p] → ℚ_[p])) = 1 :=
      fieldOnePadicUnitBallNormalizedHaar_unitBall p
    rw [hmass] at hmass'
    change 1 = (c : ℝ≥0∞) *
      fieldOnePadicUnitBallNormalizedHaar p
        (Set.range ((↑) : ℤ_[p] → ℚ_[p])) at hmass'
    rw [hpadicmass, mul_one] at hmass'
    apply ENNReal.coe_injective
    simpa only [ENNReal.coe_one] using hmass'.symm
  change μmap = fieldOnePadicUnitBallNormalizedHaar p
  rw [heq, show Measure.addHaarScalarFactor μmap
      (fieldOnePadicUnitBallNormalizedHaar p) = 1 by exact hc, one_smul]

/-- Local standard complex additive character, using the source unit-circle character. -/
def fieldOneLocalStandardAddChar (v : HeightOneSpectrum ℤ) :
    AddChar (v.adicCompletion ℚ) ℂ :=
  Circle.coeHom.compAddChar <|
    AddCircle.toCircle_addChar.compAddMonoidHom <|
      fieldOneFiniteAdeleLocalUnitCharacter v

/-- Transport a local Bruhat function to the literal p-adic model. -/
def fieldOneLocalBruhatToPadic (v : HeightOneSpectrum ℤ)
    (f : compactlySupportedLocallyConstant (v.adicCompletion ℚ)) :
    compactlySupportedLocallyConstant
      ℚ_[Rat.HeightOneSpectrum.primesEquiv v] := by
  let e := fieldOneLocalPadicContinuousAddEquiv v
  let f' : LocallyConstant ℚ_[Rat.HeightOneSpectrum.primesEquiv v] ℂ :=
    LocallyConstant.comap ⟨fun y => e.symm y, e.symm.continuous⟩ f.1
  refine ⟨f', ?_⟩
  exact f.2.comp_homeomorph e.symm.toHomeomorph

@[simp] theorem fieldOneLocalBruhatToPadic_apply
    (v : HeightOneSpectrum ℤ)
    (f : compactlySupportedLocallyConstant (v.adicCompletion ℚ))
    (y : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) :
    (fieldOneLocalBruhatToPadic v f).1 y =
      f.1 ((fieldOneLocalPadicContinuousAddEquiv v).symm y) := rfl

/-- Literal standard local Fourier transform on a rational completion. -/
def fieldOneLocalBruhatFourier (v : HeightOneSpectrum ℤ)
    (f : compactlySupportedLocallyConstant (v.adicCompletion ℚ))
    (y : v.adicCompletion ℚ) : ℂ :=
  ∫ x, fieldOneLocalStandardAddChar v (-(x * y)) * f.1 x
    ∂fieldOneLocalSelfDualAddHaar v

 theorem fieldOneLocalStandardAddChar_eq_padic
    (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    fieldOneLocalStandardAddChar v x =
      fieldOnePadicStandardAddChar
        (Rat.HeightOneSpectrum.primesEquiv v)
        (fieldOneLocalPadicContinuousAddEquiv v x) := by
  rfl

 theorem fieldOneLocalBruhatFourier_eq_padic
    (v : HeightOneSpectrum ℤ)
    (f : compactlySupportedLocallyConstant (v.adicCompletion ℚ))
    (y : v.adicCompletion ℚ) :
    fieldOneLocalBruhatFourier v f y =
      fieldOnePadicBruhatFourier
        (Rat.HeightOneSpectrum.primesEquiv v)
        (fieldOneLocalBruhatToPadic v f)
        (fieldOneLocalPadicContinuousAddEquiv v y) := by
  let e := fieldOneLocalPadicContinuousAddEquiv v
  let μ := fieldOneLocalSelfDualAddHaar v
  let ν := fieldOnePadicUnitBallNormalizedHaar
    (Rat.HeightOneSpectrum.primesEquiv v)
  change (∫ x, fieldOneLocalStandardAddChar v (-(x * y)) * f.1 x ∂μ) =
    ∫ z, fieldOnePadicStandardAddChar
      (Rat.HeightOneSpectrum.primesEquiv v)
      (-(z * e y)) * (fieldOneLocalBruhatToPadic v f).1 z ∂ν
  rw [show ν = Measure.map (fun x => e x) μ by
    exact (fieldOneLocalSelfDualHaar_map_padic v).symm]
  have hemb : MeasurableEmbedding (fun x => e x) := e.measurableEmbedding
  rw [hemb.integral_map]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [fieldOneLocalStandardAddChar_eq_padic]
  change fieldOnePadicStandardAddChar
      (Rat.HeightOneSpectrum.primesEquiv v)
      (e (-(x * y))) * f.1 x =
    fieldOnePadicStandardAddChar
      (Rat.HeightOneSpectrum.primesEquiv v)
      (-(e x * e y)) * f.1 (e.symm (e x))
  have heval : e (-(x * y)) = -(e x * e y) := by
    change Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (-(x * y)) =
      -(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x *
        Rat.HeightOneSpectrum.adicCompletion.padicEquiv v y)
    rw [map_neg, map_mul]
  rw [heval, e.symm_apply_apply]

 theorem fieldOneLocalBruhatFourier_plancherel
    (v : HeightOneSpectrum ℤ)
    (f : compactlySupportedLocallyConstant (v.adicCompletion ℚ)) :
    ∫ y, Complex.normSq (fieldOneLocalBruhatFourier v f y)
        ∂fieldOneLocalSelfDualAddHaar v =
      ∫ x, Complex.normSq (f.1 x)
        ∂fieldOneLocalSelfDualAddHaar v := by
  let e := fieldOneLocalPadicContinuousAddEquiv v
  let μ := fieldOneLocalSelfDualAddHaar v
  let ν := fieldOnePadicUnitBallNormalizedHaar
    (Rat.HeightOneSpectrum.primesEquiv v)
  have hmap : Measure.map (fun x => e x) μ = ν :=
    fieldOneLocalSelfDualHaar_map_padic v
  have hemb : MeasurableEmbedding (fun x => e x) := e.measurableEmbedding
  have hleft :
      (∫ y, Complex.normSq (fieldOneLocalBruhatFourier v f y) ∂μ) =
      ∫ z, Complex.normSq (fieldOnePadicBruhatFourier
        (Rat.HeightOneSpectrum.primesEquiv v)
        (fieldOneLocalBruhatToPadic v f) z) ∂ν := by
    rw [← hmap, hemb.integral_map]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [fieldOneLocalBruhatFourier_eq_padic]
  have hright :
      (∫ x, Complex.normSq (f.1 x) ∂μ) =
      ∫ z, Complex.normSq ((fieldOneLocalBruhatToPadic v f).1 z) ∂ν := by
    rw [← hmap, hemb.integral_map]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [fieldOneLocalBruhatToPadic_apply, e.symm_apply_apply]
  rw [hleft, hright]
  exact fieldOnePadicBruhatFourier_plancherel
    (Rat.HeightOneSpectrum.primesEquiv v) (fieldOneLocalBruhatToPadic v f)

end
end GaloisForLFunctions.RHTower

