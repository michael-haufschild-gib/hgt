/-
Fixed cusp shapes and static phases adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.FixedFourierGeometry

/-!
# Fixed cusp shapes and static phases

Factorization modulo an ideal (`CanonicalCoefficientClass.FactorsModulo`), the amplitude and
shape factors of fixed cusp shapes and their static reflection phases; the different phase adds
modulus nine to the arithmetic character.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss
open scoped BigOperators Classical MatrixGroups
local notation "Eis" => Eisenstein.O
lemma fixedConjugateCuspArray_nonzero (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedConjugateCuspArray j u m I J≠0) :
    fixedCuspArrayEligible I J ∧
      sourceCuspCoefficient j (fixedCuspArrayIndex u m I J)≠0 := by
  have helig:fixedCuspArrayEligible I J:=by
    by_contra he
    apply h
    simp only [fixedConjugateCuspArray,fixedCuspArray,if_neg he,star_zero]
  refine ⟨helig,?_⟩
  intro hz
  apply h
  simp only [fixedConjugateCuspArray,fixedCuspArray,if_pos helig,hz,zero_div,star_zero]

lemma fixedCusp_ramified_index_pos (j:Fin 3) (hj:j≠0) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J)
    (h:sourceCuspCoefficient j (fixedCuspArrayIndex u m I J)≠0) : 0 < m := by
  apply Nat.pos_of_ne_zero
  intro hm
  have hp:lambda∣traceLambda:=by
    change lambda∣traceLambda
    rw [traceLambda_unit_mul]
    exact dvd_mul_left lambda _
  have hd:=hp.trans (sourceCuspCoefficients_ramified_divisibility j hj _ h)
  simp only [fixedCuspArrayIndex,hm,pow_zero,mul_one] at hd
  have hu:IsCoprime lambda (u:Eis):=⟨0,(↑u⁻¹:Eis),by simp⟩
  have hni:IsCoprime lambda (primaryIdealGenerator I):=coprime_of_dvd_sub_one lambda _
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryIdealGenerator_spec I helig.2.1).2)
  have hnj:IsCoprime lambda (primaryIdealGenerator J):=coprime_of_dvd_sub_one lambda _
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryIdealGenerator_spec J helig.2.2).2)
  exact residue_lambda_prime.2.1 (((hu.mul_right hni).mul_right hnj.pow_right).isUnit_of_dvd hd)

def sourcePhaseUnit (j:Fin 3) (w u:Eisˣ) : Eisˣ :=
  if j=0 then traceLambdaUnit*w^2*u else -(w^2*u*traceLambdaUnit⁻¹)

def sourcePhaseExponent (j:Fin 3) (m:ℕ) : ℕ :=
  if j=0 then m+1 else m-1

lemma traceLambdaQuotient_succ (u:Eisˣ) (m:ℕ) (n b:Eis) :
    traceLambdaQuotient ((u.val*lambda^(m+1))*n*b^3)=
      (traceLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3 := by
  have hp:traceLambda*((traceLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3)=
      (u.val*lambda^(m+1))*n*b^3 := by
    change traceLambda*((traceLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3)=_
    rw [traceLambda_unit_mul,pow_succ]
    have hi:(traceLambdaUnit:Eis)*(traceLambdaUnit⁻¹:Eisˣ)=1:=by simp
    calc
      _=((traceLambdaUnit:Eis)*(traceLambdaUnit⁻¹:Eisˣ))*(u.val*lambda^m*lambda*n*b^3):=by ring
      _=_:=by rw [hi,one_mul];ring
  have hd:traceLambda∣(u.val*lambda^(m+1))*n*b^3:=⟨_,hp.symm⟩
  have hn:traceLambda≠0:=traceLambda_ne_zero
  apply mul_left_cancel₀ hn
  rw [traceLambdaQuotient_mul _ hd,hp]

theorem sourceCuspPhaseNumerator_columns (j:Fin 3) (w u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J)
    (h:sourceCuspCoefficient j (fixedCuspArrayIndex u m I J)≠0) :
    sourceCuspPhaseNumerator j w.val (fixedCuspArrayIndex u m I J)=
      ((sourcePhaseUnit j w u).val*lambda^(sourcePhaseExponent j m))*
        (primaryIdealGenerator I*(primaryIdealGenerator J)^3) := by
  by_cases hj:j=0
  · subst j
    simp only [sourceCuspPhaseNumerator,sourcePhaseUnit,sourcePhaseExponent,ite_true,
      fixedCuspArrayIndex,Units.val_mul,Units.val_pow_eq_pow_val]
    change traceLambda*w.val^2*((u.val*lambda^m)*primaryIdealGenerator I*(primaryIdealGenerator J)^3)=_
    rw [traceLambda_unit_mul,pow_succ]
    ring
  · have hm:=fixedCusp_ramified_index_pos j hj u m I J helig h
    cases m with
    | zero => omega
    | succ m =>
      simp only [sourceCuspPhaseNumerator,sourcePhaseUnit,sourcePhaseExponent,if_neg hj,
        fixedCuspArrayIndex,Nat.succ_sub_succ_eq_sub,Nat.sub_zero,Units.val_neg,Units.val_mul,
        Units.val_pow_eq_pow_val]
      rw [traceLambdaQuotient_succ]
      ring

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

def phaseUpperUnit : Eisˣ := s.upper_unit.unit

lemma phaseUpperUnit_val : (s.phaseUpperUnit:Eis)=s.upper 0 0 := s.upper_unit.unit_spec

def modelDualNumerator (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  sourceCuspPhaseNumerator s.index (s.upper 0 0) (fixedCuspArrayIndex u m I J)

end FixedCuspShape

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic
open MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

lemma amplitude_source_nonzero (p:ThetaFullIndex)
    (hp:s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val≠0) :
    sourceCuspCoefficient s.index (thetaFullFrequency p)≠0 := by
  intro hz
  apply hp
  have hz':sourceCuspCoefficient s.index
      (fixedCuspArrayIndex p.1 p.2.1 p.2.2.1.val p.2.2.2.val)=0:=by
    simpa only [thetaFullFrequency_eq_fixedCuspArrayIndex] using hz
  simp only [amplitude,fixedConjugateCuspArray,fixedCuspArray,hz',zero_div,ite_self,
    star_zero,zero_mul]

lemma amplitude_integral_phase (p:ThetaFullIndex) (c d:Eis) (hc:c≠0) :
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
      tracePhase (cuspFrequency (thetaFullFrequency p)*ringComplex (s.upper 0 0)^2*
        (ringComplex d/ringComplex c)/(sourceCuspScale s.index:ℂ)) =
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
      tracePhase (-(ringComplex d*
        (ringComplex (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/(ringComplex traceLambda)^4))/
          ringComplex c) := by
  by_cases hp:s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val=0
  · rw [hp,zero_mul,zero_mul]
  · rw [sourceCuspPhaseNumerator_phase s.index (s.upper 0 0) (thetaFullFrequency p) c d hc
      (s.amplitude_source_nonzero p hp)]

lemma datum_integral_phase (g:rationalExtension) (c:Eis) (hc:c≠0)
    (hg:((g:SL(2,Eis))*H) 1 0=c) (p:ThetaFullIndex) :
    (fixedConjugateCuspArray s.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      angularFactor (thetaFullFrequency p))*
      tracePhase (-cuspFrequency (thetaFullFrequency p)*
        ((s.datum g (by rwa [hg])).dualPoint/(sourceCuspScale s.index:ℂ))) =
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      tracePhase (-(ringComplex (((g:SL(2,Eis))*H) 1 1)*
        (ringComplex (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/(ringComplex traceLambda)^4))/
          ringComplex c) := by
  have hphase:=s.datum_additive_phase g (by rwa [hg])
    (cuspFrequency (thetaFullFrequency p)) (sourceCuspScale s.index:ℂ)
  simp only [hg] at hphase
  calc
    _=s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
        tracePhase (cuspFrequency (thetaFullFrequency p)*ringComplex (s.upper 0 0)^2*
          (ringComplex (((g:SL(2,Eis))*H) 1 1)/ringComplex c)/(sourceCuspScale s.index:ℂ)) := by
      rw [show -cuspFrequency (thetaFullFrequency p)*
          ((s.datum g (by rwa [hg])).dualPoint/(sourceCuspScale s.index:ℂ))=
        -cuspFrequency (thetaFullFrequency p)*(s.datum g (by rwa [hg])).dualPoint/
          (sourceCuspScale s.index:ℂ) by ring,hphase]
      unfold amplitude
      rw [←thetaFullFrequency_eq_fixedCuspArrayIndex]
      ring
    _=_:=s.amplitude_integral_phase p c _ hc

def stratumShapeFactor (c:Eis) : ℂ :=
  -star (extendedComplexCharacter s.gamma)*ringComplex (s.upper 0 0)^2*
    ((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ)/ringComplex c^2

lemma datum_common_row_factor (g:rationalExtension) (c:Eis) (hc:c≠0)
    (hg:((g:SL(2,Eis))*H) 1 0=c) :
    (s.datum g (by rwa [hg])).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ)=
      s.stratumShapeFactor c*star (extendedComplexCharacter g) := by
  have hm:=s.smoothed_row_factor g (by rwa [hg])
  simp only [s.datum_heightScale,hg,ringComplex_norm_sq_eq_absNorm_span] at hm
  rw [hm]
  unfold stratumShapeFactor
  ring

end FixedCuspShape

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic
open MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)
theorem sum_smoothedKernel_integral_phase {ι:Type*} [Fintype ι]
    (g:ι → rationalExtension) (c:Eis) (hc:c≠0) (hC:∀v,((g v:SL(2,Eis))*H) 1 0=c)
    (w:ι→ℂ) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑v,w v*(s.datum (g v) (by rw [hC v];exact hc)).smoothedKernel W X)=
      fixedRadialCoefficientScalar*s.stratumShapeFactor c*
      ∑'p:ThetaFullIndex,
        (s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val /
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        paperKernel (Vstar W)
          ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3)*
        (∑v,w v*star (extendedComplexCharacter (g v))*
          tracePhase (-(ringComplex (((g v:SL(2,Eis))*H) 1 1)*
            (ringComplex (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/(ringComplex traceLambda)^4))/
              ringComplex c)) := by
  let d:ι→SourceCuspDatum:=fun v=>s.datum (g v) (by rw [hC v];exact hc)
  have hindex:∀v,(d v).index=s.index:=fun _=>rfl
  have hheight:∀v,(d v).heightScale=(Ideal.absNorm (Ideal.span {c}):ℝ):=by
    intro v
    dsimp only [d]
    rw [s.datum_heightScale,hC v,ringComplex_norm_sq_eq_absNorm_span]
  have he:=sum_smoothedKernel_common_cusp d w s.index (Ideal.absNorm (Ideal.span {c}):ℝ)
    hindex hheight W a b ha hsupp hW X hX
  rw [he]
  conv_rhs => rw [mul_assoc]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*z)
  rw [←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [sourceCusp_full_index_kernel_argument p s.index (Ideal.absNorm (Ideal.span {c}):ℝ) X]
  let A:ℂ:=fixedConjugateCuspArray s.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
    angularFactor (thetaFullFrequency p)
  let B:ℂ:=s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val
  let lengthScale:ι→ℂ:=fun v=>w v*((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
    tracePhase (-cuspFrequency (thetaFullFrequency p)*((d v).dualPoint/(sourceCuspScale s.index:ℂ)))
  let R:ι→ℂ:=fun v=>w v*star (extendedComplexCharacter (g v))*
    tracePhase (-(ringComplex (((g v:SL(2,Eis))*H) 1 1)*
      (ringComplex (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/(ringComplex traceLambda)^4))/ringComplex c)
  have hs:A*(∑v,lengthScale v)=s.stratumShapeFactor c*B*(∑v,R v):=by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [lengthScale,R]
    calc
      _=w v*(((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
          (A*tracePhase (-cuspFrequency (thetaFullFrequency p)*
            ((d v).dualPoint/(sourceCuspScale s.index:ℂ))))):=by ring
      _=w v*((s.stratumShapeFactor c*star (extendedComplexCharacter (g v)))*
          (B*tracePhase (-(ringComplex (((g v:SL(2,Eis))*H) 1 1)*
            (ringComplex (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/(ringComplex traceLambda)^4))/ringComplex c))):=by
        rw [s.datum_common_row_factor (g v) c hc (hC v),s.datum_integral_phase (g v) c hc (hC v) p]
      _=_:=by ring
  let D:ℂ:=((ramifiedScale 1 completedRamifiedStep p.2.1*
    Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ)
  let K:ℂ:=paperKernel (Vstar W)
    ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
      (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3)
  change A/D*K*(∑v,lengthScale v)=s.stratumShapeFactor c*(B/D*K*(∑v,R v))
  calc
    _=(A*(∑v,lengthScale v))/D*K:=by ring
    _=(s.stratumShapeFactor c*B*(∑v,R v))/D*K:=by rw [hs]
    _=_:=by ring

lemma stratumShapeFactor_norm (c:Eis) (hc:c≠0) : ‖s.stratumShapeFactor c‖=1 := by
  have hu:‖ringComplex (s.upper 0 0)‖=1:=by
    rcases s.upper_unit with ⟨u,hu⟩
    rw [←hu]
    exact norm_ringComplex_unit u
  have hn:‖ringComplex c‖^2≠0:=pow_ne_zero _ (norm_ne_zero_iff.mpr (ringComplex_ne_zero hc))
  rw [stratumShapeFactor,norm_div,norm_mul,norm_mul,norm_neg,norm_star,
    norm_extendedComplexCharacter,norm_pow,hu,one_pow,one_mul,one_mul,norm_pow,
    Complex.norm_real,Real.norm_of_nonneg (Nat.cast_nonneg _),
    ←ringComplex_norm_sq_eq_absNorm_span]
  exact div_self hn

end FixedCuspShape
end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
theorem fixedCuspArray_phase_brackets {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i) (exponent:ι→ℕ)
    (j:Fin 3) (w u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    fixedConjugateCuspArray j u m I J*
      (∏i,bracket (complexSexticChar (P i) (hg i)) (exponent i)
        (Ideal.Quotient.mk (P i) (sourceCuspPhaseNumerator j w.val (fixedCuspArrayIndex u m I J))))=
    fixedConjugateCuspArray j u m I J*
      ramifiedBranchPhase P hg exponent (sourcePhaseUnit j w u) (sourcePhaseExponent j m)*
      ∑e:ι→Fin 3,reflectedBranch P hg exponent e (primaryIdealGenerator I) (primaryIdealGenerator J) := by
  by_cases hz:fixedConjugateCuspArray j u m I J=0
  · rw [hz,zero_mul,zero_mul,zero_mul]
  · obtain ⟨he,hh⟩:=fixedConjugateCuspArray_nonzero j u m I J hz
    rw [sourceCuspPhaseNumerator_columns j w u m I J he hh,
      ramified_bracket_full_expansion]
    ring

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff
local notation "Eis" => Eisenstein.O

namespace CanonicalCoefficientClass
/-- A multiplicative character is constant on cosets of the ideal. -/
def FactorsModulo (Q : Ideal Eis) (Ψ : Eis →* ℂ) : Prop :=
  ∀ x y : Eis, x-y∈Q → Ψ x=Ψ y
end CanonicalCoefficientClass

/-- The different phase adds modulus nine to the arithmetic character. -/
theorem fixedThetaTwist_periodic (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (x y:Eis)
    (hxy:x-y∈Ideal.span {(9:Eis)}*Q) : fixedThetaTwist Ψ x=fixedThetaTwist Ψ y := by
  have h9:(9:Eis)∣x-y:=Ideal.mem_span_singleton.mp (Ideal.mul_le_right hxy)
  have hd:lambda^2∣x-y:=lambda_sq_dvd_three.trans ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9)
  have hp:lambda^2∣x-1 ↔ lambda^2∣y-1 := by
    constructor
    · intro hx
      convert dvd_sub hx hd using 1 <;> ring
    · intro hy
      convert dvd_add hd hy using 1 <;> ring
  by_cases hx:lambda^2∣x-1
  · rw [fixedThetaTwist_primary _ x hx,fixedThetaTwist_primary _ y (hp.mp hx),
      symbol_traceLambda_congr_mod_nine x y hx (hp.mp hx) h9,hΨ x y (Ideal.mul_le_left hxy)]
  · simp only [fixedThetaTwist,if_neg hx,if_neg (fun hy=>hx (hp.mpr hy))]

def fixedThetaQuotient (Ψ:Eis→*ℂ) (c:Eis) (x:Eis⧸Ideal.span {c}) : ℂ :=
  fixedThetaTwist Ψ (Quotient.out x)

lemma fixedThetaQuotient_mk (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (c:Eis)
    (hc:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) (x:Eis) :
    fixedThetaQuotient Ψ c (Ideal.Quotient.mk _ x)=fixedThetaTwist Ψ x := by
  apply fixedThetaTwist_periodic Ψ Q hΨ
  exact hc (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {c}) x)))

lemma fixedThetaQuotient_norm_le_one (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (c:Eis) (x:Eis⧸Ideal.span {c}) : ‖fixedThetaQuotient Ψ c x‖≤1 := by
  rw [fixedThetaQuotient,fixedThetaTwist_norm]
  split_ifs
  · exact hΨ _
  · norm_num

def fixedThetaRowCoeff (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (h:Eis⧸Ideal.span {c}) : ℂ :=
  finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) (fixedThetaQuotient φ c) h

lemma fixedThetaRowCoeff_norm (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (h:Eis⧸Ideal.span {c}) :
    ‖fixedThetaRowCoeff c hc φ h‖≤1 :=
  finiteAdditiveFourierCoeff_norm_le_one _ _ (fixedThetaQuotient_norm_le_one φ hφ c) h

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff
local notation "Eis" => Eisenstein.O
def activeStratumDatum {ι:Type*} [Fintype ι]
    (p:ι→Eis) (hp:∀i,p i≠0) (hprimary:∀i,lambda^2∣p i-1)
    {N a0 c0:Eis} {mode:Bool}
    (D:∀A:Finset ι,ControlledStratumArithmetic (fun i:A=>p i.val) N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hc0:c0≠0)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (A:Finset ι) (v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ) : SourceCuspDatum :=
  (D A).datum hN (primary_finset_product Finset.univ (fun i:A=>p i.val)
    (fun i _=>hprimary i.val)) hbase s (fun i=>hp i.val) hc0 v

abbrev FixedActiveCuspIndex {ι:Type*} (c:Eis) (p:ι→Eis) :=
  Σ_h:Eis⧸Ideal.span {c},ΣA:Finset ι,∀i:A,(Eis⧸Ideal.span {p i.val})ˣ

variable {ι:Type*} [Fintype ι] (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hp:∀i,p i≠0) (hprimary:∀i,lambda^2∣p i-1)
variable (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
variable (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
variable (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h) (N:Eis)
variable (hN:∀h,(9:Eis)*(G h).c0∣N)
variable (D:∀h:Eis⧸Ideal.span {c},∀A:Finset ι,
  ControlledStratumArithmetic (fun i:A=>p i.val) N (G h).a0 (G h).c0 (G h).mode)

def fixedActiveCuspDatum (t:FixedActiveCuspIndex c p) : SourceCuspDatum :=
  activeStratumDatum p hp hprimary (D t.1) (hN t.1) (G t.1).denominator_ne_zero
    (G t.1).primary (G t.1).shape t.2.1 t.2.2


end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
