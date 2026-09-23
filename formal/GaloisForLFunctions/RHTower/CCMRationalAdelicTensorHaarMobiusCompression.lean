import GaloisForLFunctions.RHTower.CCMRationalMobiusHaarEndpointConservation

/-!
# Full-tensor Haar--Möbius compression

The pure-tensor profinite Haar formula is additive only after its Bochner
integrability is established.  This file performs that passage on the literal
algebraic adelic Bruhat tensor product.  Every tensor has one even Schwartz
source whose Meyer sum is its Haar-averaged rational trace after the physical
zero mode is removed.  Both source endpoints are exactly twice the two Tate
endpoints of the tensor.
-/

noncomputable section

open MeasureTheory IsDedekindDomain
open scoped Classical BigOperators RestrictedProduct algebraMap FourierTransform SchwartzMap

namespace GaloisForLFunctions.RHTower

private abbrev Core_cCMRationalAdelicEpsilonOne_cCMRationalAdelicTensorHaarMobiusCompression := CCMRationalAdelicBruhatSimpleTensor
private abbrev U := CCMRationalProfiniteUnit

/-- Profinite Haar average of the full rational diagonal trace of an
arbitrary algebraic adelic Bruhat tensor. -/
def ccmRationalAdelicTensorProfiniteHaarRationalLogTrace
    (x : Core_cCMRationalAdelicEpsilonOne_cCMRationalAdelicTensorHaarMobiusCompression) (t : ℝ) : ℂ :=
  ∫ u : U, (∑' q : ℚ,
    ccmRationalAdelicBruhatTensorOrbit
      x (Real.exp t) u.1 q) ∂ccmRationalProfiniteUnitHaar

/-- The full rational diagonal trace is Haar integrable in the profinite
coordinate for every algebraic tensor and every logarithmic radius. -/
theorem integrable_ccmRationalAdelicTensorRationalLogTrace
    (x : Core_cCMRationalAdelicEpsilonOne_cCMRationalAdelicTensorHaarMobiusCompression) (t : ℝ) :
    Integrable (fun u : U => ∑' q : ℚ,
      ccmRationalAdelicBruhatTensorOrbit
        x (Real.exp t) u.1 q) ccmRationalProfiniteUnitHaar := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simp [ccmRationalAdelicBruhatTensorOrbit]
  | tmul f phi =>
      obtain ⟨P⟩ := ccmRationalFiniteBruhat_exists_haarRadialPacket phi
      letI : NeZero P.period := P.period_neZero
      let fD := ccmRationalPositiveDenominatorDilation
        f P.denominator P.denominator_pos
      let L : Fin P.period → ℂ := fun r => ∑' k : ℤ,
        fD (Real.exp t * ((k : ℝ) * (P.period : ℝ) + (r : ℝ)))
      have horbit (u : U) :
          (∑' q : ℚ, ccmRationalAdelicBruhatTensorOrbit
            (f ⊗ₜ[ℂ] phi) (Real.exp t) u.1 q) =
            ccmRationalPeriodicWeightedTrace P.period
              (P.sampleFinWeight u) fD (Real.exp t) := by
        simpa only [ccmRationalAdelicBruhatTensorOrbit_tmul] using
          ccmRationalAdelicBruhatPureTensorOrbitSum_eq_haarPacketTrace
            f phi P u (Real.exp t)
      have hresidue (u : U) :
          ccmRationalPeriodicWeightedTrace P.period
              (P.sampleFinWeight u) fD (Real.exp t) =
            ∑ r : Fin P.period, P.sampleFinWeight u r * L r := by
        rw [ccmRationalPeriodicWeightedTrace_eq_sum_residues
          P.period (P.sampleFinWeight u) fD (Real.exp_ne_zero t)]
        apply Finset.sum_congr rfl
        intro r hr
        rw [← tsum_mul_left]
      have hI : Integrable (fun u : U =>
          ∑ r : Fin P.period, P.sampleFinWeight u r * L r)
          ccmRationalProfiniteUnitHaar := by
        exact integrable_finsetSum Finset.univ (fun r _ =>
          (P.integrable_sampleFinWeight r).mul_const (L r))
      exact hI.congr (Filter.Eventually.of_forall fun u =>
        ((horbit u).trans (hresidue u)).symm)
  | add x y hx hy =>
      have hsum (u : U) :
          (∑' q : ℚ, ccmRationalAdelicBruhatTensorOrbit
            (x + y) (Real.exp t) u.1 q) =
            (∑' q : ℚ, ccmRationalAdelicBruhatTensorOrbit
              x (Real.exp t) u.1 q) +
            ∑' q : ℚ, ccmRationalAdelicBruhatTensorOrbit
              y (Real.exp t) u.1 q := by
        have hxs := summable_norm_iff.mp
          (ccmRationalAdelicBruhatTensorOrbit_summable
            x (Real.exp_ne_zero t) u.1)
        have hys := summable_norm_iff.mp
          (ccmRationalAdelicBruhatTensorOrbit_summable
            y (Real.exp_ne_zero t) u.1)
        rw [← hxs.tsum_add hys]
        apply tsum_congr
        intro q
        exact ccmRationalAdelicBruhatTensorOrbit_add
          x y (Real.exp t) u.1 q
      exact (hx.add hy).congr (Filter.Eventually.of_forall fun u =>
        (hsum u).symm)

@[simp]
theorem ccmRationalAdelicTensorProfiniteHaarRationalLogTrace_zero :
    ccmRationalAdelicTensorProfiniteHaarRationalLogTrace 0 = 0 := by
  funext t
  simp [ccmRationalAdelicTensorProfiniteHaarRationalLogTrace,
    ccmRationalAdelicBruhatTensorOrbit]

theorem ccmRationalAdelicTensorProfiniteHaarRationalLogTrace_tmul
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz) :
    ccmRationalAdelicTensorProfiniteHaarRationalLogTrace
        (f ⊗ₜ[ℂ] phi) =
      ccmRationalAdelicPureTensorProfiniteHaarLogTrace f phi := by
  rfl

theorem ccmRationalAdelicTensorProfiniteHaarRationalLogTrace_add
    (x y : Core_cCMRationalAdelicEpsilonOne_cCMRationalAdelicTensorHaarMobiusCompression) :
    ccmRationalAdelicTensorProfiniteHaarRationalLogTrace (x + y) =
      ccmRationalAdelicTensorProfiniteHaarRationalLogTrace x +
        ccmRationalAdelicTensorProfiniteHaarRationalLogTrace y := by
  funext t
  change (∫ u : U, (∑' q : ℚ,
      ccmRationalAdelicBruhatTensorOrbit
        (x + y) (Real.exp t) u.1 q)
        ∂ccmRationalProfiniteUnitHaar) =
    (∫ u : U, (∑' q : ℚ,
      ccmRationalAdelicBruhatTensorOrbit
        x (Real.exp t) u.1 q)
        ∂ccmRationalProfiniteUnitHaar) +
    ∫ u : U, (∑' q : ℚ,
      ccmRationalAdelicBruhatTensorOrbit
        y (Real.exp t) u.1 q)
        ∂ccmRationalProfiniteUnitHaar
  rw [← integral_add
    (integrable_ccmRationalAdelicTensorRationalLogTrace x t)
    (integrable_ccmRationalAdelicTensorRationalLogTrace y t)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    have hx := summable_norm_iff.mp
      (ccmRationalAdelicBruhatTensorOrbit_summable
        x (Real.exp_ne_zero t) u.1)
    have hy := summable_norm_iff.mp
      (ccmRationalAdelicBruhatTensorOrbit_summable
        y (Real.exp_ne_zero t) u.1)
    change (∑' q : ℚ, ccmRationalAdelicBruhatTensorOrbit
        (x + y) (Real.exp t) u.1 q) =
      (∑' q : ℚ, ccmRationalAdelicBruhatTensorOrbit
        x (Real.exp t) u.1 q) +
      ∑' q : ℚ, ccmRationalAdelicBruhatTensorOrbit
        y (Real.exp t) u.1 q
    rw [← hx.tsum_add hy]
    apply tsum_congr
    intro q
    exact ccmRationalAdelicBruhatTensorOrbit_add
      x y (Real.exp t) u.1 q

/-- One exact universal Möbius source for an arbitrary algebraic tensor. -/
structure CCMRationalAdelicTensorHaarMobiusPacket (x : Core_cCMRationalAdelicEpsilonOne_cCMRationalAdelicTensorHaarMobiusCompression) where
  source : CCMRationalArchimedeanSchwartz
  source_even : ∀ z : ℝ, source (-z) = source z
  haarTrace_eq :
    ccmRationalAdelicTensorProfiniteHaarRationalLogTrace x =
      fun t => ccmRationalAdelicBruhatZeroEval x +
        RHTower.deningerMeyerSum source (Real.exp t)
  source_zero :
    source 0 = 2 * ccmRationalAdelicBruhatZeroEval x
  source_fourier_zero :
    (𝓕 source) 0 = 2 * ccmRationalAdelicBruhatIntegral x

/-- Every algebraic adelic Bruhat tensor has an exact Haar--Möbius packet.
Cancellation is allowed globally between tensor summands. -/
theorem ccmRationalAdelicTensor_exists_haarMobiusPacket
    (x : Core_cCMRationalAdelicEpsilonOne_cCMRationalAdelicTensorHaarMobiusCompression) : Nonempty (CCMRationalAdelicTensorHaarMobiusPacket x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      refine ⟨{
        source := 0
        source_even := by simp
        haarTrace_eq := ?_
        source_zero := by simp
        source_fourier_zero := by simp }⟩
      funext t
      rw [ccmRationalAdelicTensorProfiniteHaarRationalLogTrace_zero]
      simp only [Pi.zero_apply, map_zero, zero_add]
      have hz := (RHTower.deningerMeyerPositiveSumLM
        (Real.exp t) (Real.exp_ne_zero t)).map_zero
      rw [RHTower.deningerMeyerPositiveSumLM_apply] at hz
      exact hz.symm
  | tmul f phi =>
      obtain ⟨P⟩ := ccmRationalFiniteBruhat_exists_haarRadialPacket phi
      letI : NeZero P.period := P.period_neZero
      let fD := ccmRationalPositiveDenominatorDilation
        f P.denominator P.denominator_pos
      let F := ccmRationalUnitInvariantMobiusSource
        P.period P.averageWeight fD
      have hend := ccmRationalAdelicPureTensorMobiusSource_endpoints f phi P
      refine ⟨{
        source := F
        source_even := ccmRationalUnitInvariantMobiusSource_even
          P.period_neZero.out P.averageWeight fD
        haarTrace_eq := ?_
        source_zero := hend.1
        source_fourier_zero := hend.2 }⟩
      have hconstant : P.averageWeight 0 * fD 0 =
          ccmRationalAdelicBruhatZeroEval (f ⊗ₜ[ℂ] phi) := by
        rw [P.averageWeight_zero]
        simp [fD, ccmRationalPositiveDenominatorDilation_apply,
          ccmRationalAdelicBruhatZeroEval_tmul]
        ring
      rw [ccmRationalAdelicTensorProfiniteHaarRationalLogTrace_tmul,
        ccmRationalAdelicPureTensorProfiniteHaarLogTrace_eq_mobiusMeyer
          f phi P]
      funext t
      rw [hconstant]
  | add x y hx hy =>
      obtain ⟨P⟩ := hx
      obtain ⟨Q⟩ := hy
      refine ⟨{
        source := P.source + Q.source
        source_even := ?_
        haarTrace_eq := ?_
        source_zero := ?_
        source_fourier_zero := ?_ }⟩
      · intro z
        simp only [add_apply]
        rw [P.source_even z, Q.source_even z]
      · rw [ccmRationalAdelicTensorProfiniteHaarRationalLogTrace_add,
          P.haarTrace_eq, Q.haarTrace_eq]
        funext t
        rw [map_add]
        change
          (ccmRationalAdelicBruhatZeroEval x +
              RHTower.deningerMeyerSum P.source (Real.exp t)) +
            (ccmRationalAdelicBruhatZeroEval y +
              RHTower.deningerMeyerSum Q.source (Real.exp t)) =
            ccmRationalAdelicBruhatZeroEval x +
              ccmRationalAdelicBruhatZeroEval y +
              RHTower.deningerMeyerSum (P.source + Q.source) (Real.exp t)
        have hM := (RHTower.deningerMeyerPositiveSumLM
          (Real.exp t) (Real.exp_ne_zero t)).map_add P.source Q.source
        simp only [RHTower.deningerMeyerPositiveSumLM_apply] at hM
        have hcoe : (⇑(P.source + Q.source) : ℝ → ℂ) =
            (⇑P.source : ℝ → ℂ) + ⇑Q.source := by
          funext z
          rfl
        rw [hcoe] at hM
        rw [hM]
        ring
      · simp only [add_apply]
        rw [P.source_zero, Q.source_zero, map_add]
        ring
      · change RHTower.deningerFourierEval (P.source + Q.source) = _
        have hPF : RHTower.deningerFourierEval P.source =
            2 * ccmRationalAdelicBruhatIntegral x := by
          rw [RHTower.deningerFourierEval_apply]
          exact P.source_fourier_zero
        have hQF : RHTower.deningerFourierEval Q.source =
            2 * ccmRationalAdelicBruhatIntegral y := by
          rw [RHTower.deningerFourierEval_apply]
          exact Q.source_fourier_zero
        rw [map_add, hPF, hQF, map_add]
        ring

/-- With both literal Tate endpoints zero, the packet source is a genuine
element of Meyer's cap. -/
theorem CCMRationalAdelicTensorHaarMobiusPacket.source_mem_meyerCap
    {x : Core_cCMRationalAdelicEpsilonOne_cCMRationalAdelicTensorHaarMobiusCompression} (P : CCMRationalAdelicTensorHaarMobiusPacket x)
    (hzero : ccmRationalAdelicBruhatZeroEval x = 0)
    (hone : ccmRationalAdelicBruhatIntegral x = 0) :
    P.source ∈ RHTower.DeningerMeyerCap := by
  rw [RHTower.deningerMeyerCap_mem_iff]
  refine ⟨P.source_even,
    by rw [P.source_zero, hzero, mul_zero], ?_⟩
  change RHTower.deningerFourierEval P.source = 0
  rw [RHTower.deningerFourierEval_apply]
  exact P.source_fourier_zero.trans (by rw [hone, mul_zero])

/-- Canonical cap element carried by an endpoint-zero Haar--Möbius packet. -/
def CCMRationalAdelicTensorHaarMobiusPacket.toMeyerCap
    {x : Core_cCMRationalAdelicEpsilonOne_cCMRationalAdelicTensorHaarMobiusCompression} (P : CCMRationalAdelicTensorHaarMobiusPacket x)
    (hzero : ccmRationalAdelicBruhatZeroEval x = 0)
    (hone : ccmRationalAdelicBruhatIntegral x = 0) :
    RHTower.DeningerMeyerCap :=
  ⟨P.source, P.source_mem_meyerCap hzero hone⟩

end GaloisForLFunctions.RHTower
