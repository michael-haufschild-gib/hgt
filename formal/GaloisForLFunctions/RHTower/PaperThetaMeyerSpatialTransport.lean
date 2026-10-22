import GaloisForLFunctions.RHTower.PaperThetaFiniteSpatialRealization
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerFiniteXiCausalSolvability

/-! # Literal theta--Meyer transport of finite differential equations

The comparison intertwines the original centered Meyer generator with the
actual source differential expression. It therefore transports every finite
word of scalar shifts, retaining every full-multiplicity chain slot.
-/

noncomputable section
open Complex Set
open scoped Classical

namespace RHTower.PaperThetaEndpoint

def thetaFiniteStep (S : Finset XiDivisorSupport)
    (q : DeningerMeyerFiniteXiJetSlot S) : DeningerMeyerFiniteXiJetPacket S :=
  xiSpectralPointSupport q.1.1 • Pi.single q 1 +
    if h : q.2.val = 0 then 0 else Pi.single ⟨q.1, ⟨q.2.val-1, by omega⟩⟩ 1

def thetaFinitePacketGenerator (S : Finset XiDivisorSupport) :
    Module.End ℂ (DeningerMeyerFiniteXiJetPacket S) :=
  Fintype.linearCombination ℂ (thetaFiniteStep S)

private theorem thetaFinite_step (S : Finset XiDivisorSupport)
    (q : DeningerMeyerFiniteXiJetSlot S) :
    thetaSpatialGenerator (thetaRightHasseJet (xiSpectralPointSupport q.1.1) q.2.val) =
      thetaFiniteSynthesis S (thetaFiniteStep S q) := by
  by_cases h : q.2.val = 0
  · simp [thetaFiniteStep, h, thetaFiniteSynthesis, thetaSpatialGenerator_hasse_zero]
  · have hj : q.2.val-1+1 = q.2.val := by omega
    have he := thetaSpatialGenerator_hasse_succ (xiSpectralPointSupport q.1.1) (q.2.val-1)
    rw [hj] at he
    simpa [thetaFiniteStep, h, thetaFiniteSynthesis] using he

private theorem meyerFinite_step (S : Finset XiDivisorSupport)
    (q : DeningerMeyerFiniteXiJetSlot S) :
    deningerMeyerCenteredCohomologyGenerator
        (deningerMeyerHedenmalmClass q.1.1 ⟨q.2.val+1, by omega⟩) =
      meyerFiniteHedenmalmSynthesis S (thetaFiniteStep S q) := by
  rw [deningerMeyerHedenmalmClass_jordan q.1.1 q.2]
  by_cases h : q.2.val = 0
  · simp [thetaFiniteStep, h, meyerFiniteHedenmalmSynthesis,
      deningerMeyerHedenmalmClass_eq, deningerMeyerXiCausalClass_zero]
  · have hj : q.2.val-1+1 = q.2.val := by omega
    simp [thetaFiniteStep, h, meyerFiniteHedenmalmSynthesis, hj]

theorem thetaFiniteSynthesis_generator (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    thetaSpatialGenerator (thetaFiniteSynthesis S c) =
      thetaFiniteSynthesis S (thetaFinitePacketGenerator S c) := by
  change thetaSpatialGenerator (∑ q, c q •
    thetaRightHasseJet (xiSpectralPointSupport q.1.1) q.2.val) =
    thetaFiniteSynthesis S (∑ q, c q • thetaFiniteStep S q)
  simp only [map_sum, map_smul, thetaFinite_step]

theorem meyerFiniteHedenmalmSynthesis_generator (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerCenteredCohomologyGenerator (meyerFiniteHedenmalmSynthesis S c) =
      meyerFiniteHedenmalmSynthesis S (thetaFinitePacketGenerator S c) := by
  change deningerMeyerCenteredCohomologyGenerator (∑ q, c q •
    deningerMeyerHedenmalmClass q.1.1 ⟨q.2.val+1, by omega⟩) =
    meyerFiniteHedenmalmSynthesis S (∑ q, c q • thetaFiniteStep S q)
  simp only [map_sum, map_smul, meyerFinite_step]

private theorem thetaFinite_invariant (S : Finset XiDivisorSupport)
    (f : thetaRightJetSpace) (hf : f ∈ LinearMap.range (thetaFiniteSynthesis S)) :
    thetaSpatialGenerator f ∈ LinearMap.range (thetaFiniteSynthesis S) := by
  obtain ⟨c, rfl⟩ := hf
  exact ⟨thetaFinitePacketGenerator S c, (thetaFiniteSynthesis_generator S c).symm⟩

private theorem meyerFinite_invariant (S : Finset XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology)
    (hu : u ∈ LinearMap.range (meyerFiniteHedenmalmSynthesis S)) :
    deningerMeyerCenteredCohomologyGenerator u ∈
      LinearMap.range (meyerFiniteHedenmalmSynthesis S) := by
  obtain ⟨c, rfl⟩ := hu
  exact ⟨thetaFinitePacketGenerator S c, (meyerFiniteHedenmalmSynthesis_generator S c).symm⟩

def thetaFiniteSpatialGenerator (S : Finset XiDivisorSupport) :
    Module.End ℂ (LinearMap.range (thetaFiniteSynthesis S)) where
  toFun f := ⟨thetaSpatialGenerator f, thetaFinite_invariant S f f.property⟩
  map_add' f g := Subtype.ext (map_add thetaSpatialGenerator f.val g.val)
  map_smul' c f := Subtype.ext (map_smul thetaSpatialGenerator c f.val)

def meyerFiniteCenteredGenerator (S : Finset XiDivisorSupport) :
    Module.End ℂ (LinearMap.range (meyerFiniteHedenmalmSynthesis S)) where
  toFun u := ⟨deningerMeyerCenteredCohomologyGenerator u, meyerFinite_invariant S u u.property⟩
  map_add' u v := Subtype.ext (map_add deningerMeyerCenteredCohomologyGenerator u.val v.val)
  map_smul' c u := Subtype.ext (map_smul deningerMeyerCenteredCohomologyGenerator c u.val)

@[simp] theorem thetaFiniteSpatialGenerator_coordinates (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    thetaFiniteSpatialGenerator S (thetaFiniteCoordinates S c) =
      thetaFiniteCoordinates S (thetaFinitePacketGenerator S c) :=
  Subtype.ext (thetaFiniteSynthesis_generator S c)

@[simp] theorem meyerFiniteCenteredGenerator_coordinates (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    meyerFiniteCenteredGenerator S (meyerFiniteHedenmalmCoordinates S c) =
      meyerFiniteHedenmalmCoordinates S (thetaFinitePacketGenerator S c) :=
  Subtype.ext (meyerFiniteHedenmalmSynthesis_generator S c)

@[simp] theorem meyerThetaFiniteEquiv_coordinates (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    meyerThetaFiniteEquiv S (meyerFiniteHedenmalmCoordinates S c) = thetaFiniteCoordinates S c := by
  simp [meyerThetaFiniteEquiv]

/-- The comparison intertwines actual source generators, including every predecessor. -/
theorem meyerThetaFiniteEquiv_generator (S : Finset XiDivisorSupport)
    (u : LinearMap.range (meyerFiniteHedenmalmSynthesis S)) :
    meyerThetaFiniteEquiv S (meyerFiniteCenteredGenerator S u) =
      thetaFiniteSpatialGenerator S (meyerThetaFiniteEquiv S u) := by
  obtain ⟨c, rfl⟩ := (meyerFiniteHedenmalmCoordinates S).surjective u
  simp only [meyerFiniteCenteredGenerator_coordinates, meyerThetaFiniteEquiv_coordinates,
    thetaFiniteSpatialGenerator_coordinates]

/-- Iterated literal source differential expressions on functions. -/
def thetaSpatialWord : List ℂ → (ℝ → ℂ) → (ℝ → ℂ)
  | [], f => f
  | z :: L, f => thetaSpatialAction (thetaSpatialWord L f) - z • thetaSpatialWord L f

theorem thetaFiniteSpatialWord_literal (S : Finset XiDivisorSupport) (L : List ℂ)
    (f : LinearMap.range (thetaFiniteSynthesis S)) :
    (deningerMeyerGeneratorWord (thetaFiniteSpatialGenerator S) L f).val.val =
      thetaSpatialWord L f.val.val := by
  induction L with
  | nil => rfl
  | cons z L ih =>
      change thetaSpatialAction
        (deningerMeyerGeneratorWord (thetaFiniteSpatialGenerator S) L f).val.val -
        z • (deningerMeyerGeneratorWord (thetaFiniteSpatialGenerator S) L f).val.val = _
      rw [ih]
      rfl

/-- Every finite source equation has its faithful literal differential realization. -/
theorem meyerThetaFiniteEquiv_word (S : Finset XiDivisorSupport) (L : List ℂ)
    (u : LinearMap.range (meyerFiniteHedenmalmSynthesis S)) :
    meyerThetaFiniteEquiv S (deningerMeyerGeneratorWord (meyerFiniteCenteredGenerator S) L u) =
      deningerMeyerGeneratorWord (thetaFiniteSpatialGenerator S) L (meyerThetaFiniteEquiv S u) := by
  induction L with
  | nil => rfl
  | cons z L ih =>
      simp only [deningerMeyerGeneratorWord, LinearMap.comp_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul,
        meyerThetaFiniteEquiv_generator, ih]
      rfl

theorem meyerThetaFiniteEquiv_literal_word (S : Finset XiDivisorSupport) (L : List ℂ)
    (u : LinearMap.range (meyerFiniteHedenmalmSynthesis S)) :
    thetaSpatialWord L (meyerThetaFiniteEquiv S u).val.val =
      (meyerThetaFiniteEquiv S
        (deningerMeyerGeneratorWord (meyerFiniteCenteredGenerator S) L u)).val.val := by
  rw [meyerThetaFiniteEquiv_word, thetaFiniteSpatialWord_literal]

end RHTower.PaperThetaEndpoint
