import GaloisForLFunctions.RHTower.DeningerMeyerFiniteXiCausalSplitting

/-!
# Literal Meyer realization of the Hedenmalm divisor chains

The existing Hedenmalm divided differences of Xi are centered Mellin
transforms of explicit all-weight Meyer sources.  This identifies the
finite invariant source calculus with the preexisting entire divisor-chain
calculus, including every actual multiplicity.
-/

open Complex Set Filter Topology
open scoped Classical

namespace RHTower
noncomputable section

private theorem causalSource_centered_transform (rho : XiDivisorSupport)
    (k : ℕ) (hk : k ≤ xiSupportMultiplicity rho) :
    (fun z => deningerMeyerCenteredMellin (deningerMeyerXiCausalSource rho k hk) z) =
      fun z => (-I) ^ k * xiThetaDividedChain (xiSpectralPointSupport rho) k z := by
  apply Continuous.ext_on (dense_compl_singleton (xiSpectralPointSupport rho))
    (differentiable_deningerMeyerCenteredMellin
      (deningerMeyerXiCausalSource rho k hk)).continuous
    (continuous_const.mul (continuous_iff_continuousAt.mpr fun z =>
      (xiThetaDividedChain_analyticAt (xiSpectralPointSupport rho) k z).continuousAt))
  intro z hz
  have hne : z - xiSpectralPointSupport rho ≠ 0 := sub_ne_zero.mpr hz
  have hshift : 1 / 2 + I * z - (rho : ℂ) = I * (z - xiSpectralPointSupport rho) := by
    rw [← deningerMeyer_uncenter_xiSpectralPointSupport rho]
    ring
  have hm := deningerMeyerXiCausalSource_factor rho k hk (1 / 2 + I * z)
  rw [hshift, mul_pow] at hm
  have hc := xiThetaDividedChain_partial_factorization rho hk z
  have hm' : XiC z = I ^ k * (z - xiSpectralPointSupport rho) ^ k *
      deningerMeyerCenteredMellin (deningerMeyerXiCausalSource rho k hk) z := by
    simpa only [XiC, deningerMeyerCenteredMellin_apply, mul_comm I z] using hm
  have hcancel : I ^ k * deningerMeyerCenteredMellin
      (deningerMeyerXiCausalSource rho k hk) z =
        xiThetaDividedChain (xiSpectralPointSupport rho) k z := by
    apply mul_left_cancel₀ (pow_ne_zero k hne)
    linear_combination hc - hm'
  have hI : (-I) ^ k * I ^ k = 1 := by
    rw [← mul_pow]
    simp
  rw [← hcancel, ← mul_assoc, hI, one_mul]

/-- Canonical actual source of the existing Hedenmalm divided chain, including its phase. -/
def deningerMeyerHedenmalmSource (rho : XiDivisorSupport)
    (k : Fin (xiSupportMultiplicity rho + 1)) : DeningerMeyerStrongLogTarget :=
  I ^ k.val • deningerMeyerXiCausalSource rho k.val (Nat.le_of_lt_succ k.isLt)

/-- Every existing finite Hedenmalm divisor-chain member has a literal Meyer source. -/
theorem deningerMeyerHedenmalmSource_transform (rho : XiDivisorSupport)
    (k : Fin (xiSupportMultiplicity rho + 1)) (z : ℂ) :
    deningerMeyerCenteredMellin (deningerMeyerHedenmalmSource rho k) z =
      xiThetaDividedChain (xiSpectralPointSupport rho) k.val z := by
  change deningerMeyerCenteredMellinLM
    (I ^ k.val • deningerMeyerXiCausalSource rho k.val (Nat.le_of_lt_succ k.isLt)) z = _
  rw [map_smul]
  change I ^ k.val * deningerMeyerCenteredMellin
    (deningerMeyerXiCausalSource rho k.val (Nat.le_of_lt_succ k.isLt)) z = _
  rw [congrFun (causalSource_centered_transform rho k.val (Nat.le_of_lt_succ k.isLt)) z,
    ← mul_assoc, ← mul_pow]
  simp

/-- The centered generator in the same spectral coordinate as the Hedenmalm chains. -/
def deningerMeyerCenteredCohomologyGenerator : Module.End ℂ DeningerMeyerStrongLogCohomology :=
  (-I) • (deningerMeyerCohomologyGenerator - (1 / 2 : ℂ) • LinearMap.id)

def deningerMeyerHedenmalmClass (rho : XiDivisorSupport)
    (k : Fin (xiSupportMultiplicity rho + 1)) : DeningerMeyerStrongLogCohomology :=
  Submodule.Quotient.mk (deningerMeyerHedenmalmSource rho k)

theorem deningerMeyerHedenmalmClass_eq (rho : XiDivisorSupport)
    (k : Fin (xiSupportMultiplicity rho + 1)) :
    deningerMeyerHedenmalmClass rho k =
      I ^ k.val • deningerMeyerXiCausalClass rho k.val (Nat.le_of_lt_succ k.isLt) := by
  simp only [deningerMeyerHedenmalmClass, deningerMeyerHedenmalmSource,
    deningerMeyerXiCausalClass, Submodule.Quotient.mk_smul]

/-- The Hedenmalm Jordan recurrence holds in actual Meyer cohomology, before comparison. -/
theorem deningerMeyerHedenmalmClass_jordan (rho : XiDivisorSupport)
    (k : Fin (xiSupportMultiplicity rho)) :
    deningerMeyerCenteredCohomologyGenerator
        (deningerMeyerHedenmalmClass rho ⟨k.val + 1, by omega⟩) =
      xiSpectralPointSupport rho •
        deningerMeyerHedenmalmClass rho ⟨k.val + 1, by omega⟩ +
          deningerMeyerHedenmalmClass rho ⟨k.val, by omega⟩ := by
  simp only [deningerMeyerHedenmalmClass_eq,
    deningerMeyerCenteredCohomologyGenerator, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_smul,
    deningerMeyerXiCausalClass_generator]
  have hcenter : (-I) * ((rho : ℂ) - 1 / 2) = xiSpectralPointSupport rho := by
    calc (-I) * ((rho : ℂ) - 1 / 2) = (-I) * (I * xiSpectralPointSupport rho) := by
           rw [← deningerMeyer_uncenter_xiSpectralPointSupport rho]
           congr 1
           ring
         _ = xiSpectralPointSupport rho := by rw [← mul_assoc]; simp
  have hstep : (-I) * I ^ (k.val + 1) = I ^ k.val := by
    rw [pow_succ]
    calc (-I) * (I ^ k.val * I) = ((-I) * I) * I ^ k.val := by ring
         _ = I ^ k.val := by simp
  rw [← hcenter, ← hstep]
  module

/-- Actual source synthesis; the slot index here counts upwards along each Jordan chain. -/
def deningerMeyerFiniteXiRawSource (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) : DeningerMeyerStrongLogTarget :=
  ∑ q : DeningerMeyerFiniteXiJetSlot S,
    c q • deningerMeyerXiCausalSource q.1.1 (q.2.val + 1) (by omega)

/-- The finite Jordan part of the actual source generator, with its bottom boundary removed. -/
def deningerMeyerFiniteXiRawJordanPart (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) : DeningerMeyerStrongLogTarget :=
  ∑ q : DeningerMeyerFiniteXiJetSlot S, c q •
    ((q.1.1 : ℂ) • deningerMeyerXiCausalSource q.1.1 (q.2.val + 1) (by omega) +
      if q.2.val = 0 then 0 else deningerMeyerXiCausalSource q.1.1 q.2.val (by omega))

/-- All bottom-chain coefficients feed the same fixed actual Xi boundary. -/
def deningerMeyerFiniteXiBoundaryAmplitude (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) : ℂ :=
  ∑ q : DeningerMeyerFiniteXiJetSlot S, if q.2.val = 0 then c q else 0

/-- Exact universal one-boundary defect, before passage to Meyer cohomology. -/
theorem deningerMeyerFiniteXiRawSource_generator (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerStrongLogGenerator (deningerMeyerFiniteXiRawSource S c) =
      deningerMeyerFiniteXiRawJordanPart S c +
        deningerMeyerFiniteXiBoundaryAmplitude S c •
          deningerMeyerStrongLogSumLM deningerMeyerXiCapSource := by
  classical
  have hzero (rho : XiDivisorSupport) :
      deningerMeyerXiCausalSource rho 0 (Nat.zero_le _) =
        deningerMeyerStrongLogSumLM deningerMeyerXiCapSource := rfl
  rw [deningerMeyerFiniteXiRawSource, map_sum]
  simp_rw [map_smul, deningerMeyerXiCausalSource_generator]
  rw [deningerMeyerFiniteXiRawJordanPart, deningerMeyerFiniteXiBoundaryAmplitude,
    Finset.sum_smul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q.2.val = 0
  · simp [hq, hzero, smul_add]
  · simp [hq]

end
end RHTower
