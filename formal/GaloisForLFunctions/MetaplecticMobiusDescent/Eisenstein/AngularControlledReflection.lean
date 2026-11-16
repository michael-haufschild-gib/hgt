import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularFixedArrays
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.ControlledStratumReflection

/-!
# Angular reflection through finite phase decompositions

Finite Fourier inversion applies to the periodic coefficient alone. Its exact phase
decomposition reflects the angular completed sum through the same source cusps, without
requiring the angular character to factor through a finite quotient.
-/

open Complex MeasureTheory Set
open scoped BigOperators Classical ContDiff ComplexConjugate
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion NormalizedReflection
open GaloisForLFunctions.FamilyContinuationTheory
noncomputable section

lemma angularSourceTwist_norm_le_one (k : ℕ) (Ψ : O →* ℂ)
    (hΨ : ∀ h, ‖Ψ h‖ ≤ 1) (h : O) : ‖angularSourceTwist k Ψ h‖ ≤ 1 := by
  rw [angularSourceTwist_apply, norm_mul, norm_pow]
  exact (mul_le_mul (hΨ h)
    (pow_le_one₀ (norm_nonneg _) (norm_elemPsiSix_le_one h))
    (pow_nonneg (norm_nonneg _) _) zero_le_one).trans_eq (one_mul 1)

lemma SourceCuspDatum.angularSmoothedKernel_source (d : SourceCuspDatum) (k : ℕ)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    d.angularSmoothedKernel k W X = ∑' h : O,
      (elemPsiSix h ^ k * sourceBarRadialCoefficient d.point h) *
        Vstar W (sourceCuspRadialLength h / X) := by
  rw [d.angularSmoothedKernel_eq_reflected_series]
  exact (d.angular_smoothed_reflection k (Vstar W) a b ha (Vstar_support W a b hs)
    (Vstar_contDiff W a b ha hs hW) X hX).symm

/-- Every exact finite phase decomposition reflects the angular source at its actual cusps. -/
theorem completedT_angular_finite_phase_reflection (k : ℕ) {ι : Type*} [Fintype ι]
    (Ψ : O →* ℂ) (d : ι → SourceCuspDatum) (weight : ι → ℂ)
    (hphase : ∀ h : O, (∑ i, weight i * tracePhase (-cuspFrequency h * (d i).point)) =
      fixedThetaTwist Ψ h)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    completedT (angularSourceTwist k Ψ) W X =
      thetaDerivativeScalar⁻¹ * ∑ i, weight i * (d i).angularSmoothedKernel k W X := by
  have hsum := weighted_compact_test_norm_summable sourceCuspRadialLength sourceCuspRadialLength_pos
    (fun h => elemPsiSix h ^ k * sourceBarRadialCoefficient 0 h) (3 / 2)
    (angularSourceBar_weighted_summable k 0) (Vstar W) a b ha
    (Vstar_support W a b hs) (Vstar_contDiff W a b ha hs hW) X hX
  have htest : Summable (fun h : O => ‖sourceBarRadialCoefficient 0 h *
      (elemPsiSix h ^ k * Vstar W (sourceCuspRadialLength h / X))‖) := by
    simpa only [mul_assoc, mul_left_comm] using hsum
  have he := sourceBar_smoothed_phase_translation (fun i => (d i).point) weight
    (fun h => elemPsiSix h ^ k * Vstar W (sourceCuspRadialLength h / X)) htest
  simp_rw [hphase] at he
  rw [completedT_source_identity]
  calc
    _ = thetaDerivativeScalar⁻¹ * ∑' h : O, fixedThetaTwist Ψ h * sourceBarRadialCoefficient 0 h *
        (elemPsiSix h ^ k * Vstar W (sourceCuspRadialLength h / X)) := by
      congr 1
      apply tsum_congr
      intro h
      rw [fixedThetaTwist_angularSourceTwist]
      ring
    _ = thetaDerivativeScalar⁻¹ * ∑ i, weight i * ∑' h : O,
        sourceBarRadialCoefficient (d i).point h *
          (elemPsiSix h ^ k * Vstar W (sourceCuspRadialLength h / X)) := by rw [← he]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [(d i).angularSmoothedKernel_source k W a b ha hs hW X hX]
      simp only [mul_assoc, mul_left_comm]

/-- The conductor hypothesis concerns only the finite coefficient of the angular twist. -/
theorem completedT_angular_canonical_smoothed_reflection (k : ℕ) (Ψ : O →* ℂ)
    (Q : Ideal O) (hperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : O) (hc : c ≠ 0) [Fintype (O ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : O)} * Q)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    completedT (angularSourceTwist k Ψ) W X = thetaDerivativeScalar⁻¹ *
      ∑ h : O ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) (fixedThetaQuotient Ψ c) h *
          (finiteTwistCusp c hc h).angularSmoothedKernel k W X := by
  have hp (n : O) : (∑ h : O ⧸ Ideal.span {c},
      finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) (fixedThetaQuotient Ψ c) h *
        tracePhase (-cuspFrequency n * (finiteTwistCusp c hc h).point)) = fixedThetaTwist Ψ n := by
    simp_rw [finiteTwistCusp_point]
    rw [thetaFourierTranslation_inversion, fixedThetaQuotient_mk Ψ Q hperiod c hcQ]
  exact completedT_angular_finite_phase_reflection k Ψ (finiteTwistCusp c hc)
    (finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) (fixedThetaQuotient Ψ c))
    hp W a b ha hs hW X hX


namespace ControlledStratumArithmetic
open CompletedDyadic
open scoped MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}
def angularSmoothedValue (D:ControlledStratumArithmetic p N a0 c0 mode) (k : ℕ)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,fourierWeight hp hg j v*
    (D.datum hN hr hbase s hp hc0 v).angularSmoothedKernel k W X

def angularReflectedValue (D:ControlledStratumArithmetic p N a0 c0 mode) (k : ℕ)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  fixedRadialCoefficientScalar*(s.stratumShapeFactor (c0*∏i,p i)*elemPsiSix (c0*∏i,p i)^(2*k))*
    ∑'t:ThetaFullIndex,
      (conj (elemPsiSix (thetaFullFrequency t))^k * s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
        ((ramifiedScale 1 completedRamifiedStep t.2.1*
          Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
      angularPaperKernel k (Vstar W)
        ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c0*∏i,p i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
          (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)*
      ((star D.fixedFactor*cuspBadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U
        (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))*
          D.bracketProduct hp hg j
            (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))

theorem angularSmoothed_eq_reflected (D:ControlledStratumArithmetic p N a0 c0 mode) (k : ℕ)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.angularSmoothedValue k hN hr hbase s hp hc0 hg j W X=D.angularReflectedValue k s hp hc0 hg j W X := by
  let (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  have hc:c0*(∏i,p i)≠0:=mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  have hC:∀v,((D.sourceGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode) 1 0=c0*∏i,p i := by
    intro v
    rw [D.sourceGamma_mul,D.denominator]
  have he:=s.sum_angularSmoothedKernel_integral_phase k (D.sourceGamma hN hr hbase) _ hc hC
    (fourierWeight hp hg j) W lo hi hlo hsupp hW X hX
  change D.angularSmoothedValue k hN hr hbase s hp hc0 hg j W X=_ at he
  rw [he]
  unfold angularReflectedValue
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*(s.stratumShapeFactor (c0*∏i,p i)*elemPsiSix (c0*∏i,p i)^(2*k))*z)
  apply tsum_congr
  intro t
  apply congrArg (fun z:ℂ=>
    (conj (elemPsiSix (thetaFullFrequency t))^k * s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
      ((ramifiedScale 1 completedRamifiedStep t.2.1*
        Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
      angularPaperKernel k (Vstar W)
        ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c0*∏i,p i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
          (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)*z)
  simpa only [multiplierSum,D.sourceGamma_character,D.sourceGamma_mul,map_mul] using
    D.multiplierSum_eq hN hr hbase hp hc0 hcop hg hchar j hj
      (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))

end ControlledStratumArithmetic

end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
