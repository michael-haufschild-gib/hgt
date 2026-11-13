/-
Reflection on a controlled stratum adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.RowCompletion.FixedCuspShapes

/-!
# Reflection on a controlled stratum

Fixed base conductors and base-ray twist components; reflected and model row values of a
controlled stratum. The reflected kernel equals the compactly smoothed source at its cusp.
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
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
noncomputable def smoothedValue (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,fourierWeight hp hg j v*
    (D.datum hN hr hbase s hp hc0 v).smoothedKernel W X

noncomputable def reflectedValue (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  fixedRadialCoefficientScalar*s.stratumShapeFactor (c0*∏i,p i)*
    ∑'t:ThetaFullIndex,
      (s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
        ((ramifiedScale 1 completedRamifiedStep t.2.1*
          Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
      paperKernel (Vstar W)
        ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c0*∏i,p i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
          (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)*
      ((star D.fixedFactor*cuspBadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U
        (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))*
          D.bracketProduct hp hg j
            (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))

theorem smoothed_eq_reflected (D:ControlledStratumArithmetic p N a0 c0 mode)
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
    D.smoothedValue hN hr hbase s hp hc0 hg j W X=D.reflectedValue s hp hc0 hg j W X := by
  let (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  have hc:c0*(∏i,p i)≠0:=mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  have hC:∀v,((D.sourceGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode) 1 0=c0*∏i,p i := by
    intro v
    rw [D.sourceGamma_mul,D.denominator]
  have he:=s.sum_smoothedKernel_integral_phase (D.sourceGamma hN hr hbase) _ hc hC
    (fourierWeight hp hg j) W lo hi hlo hsupp hW X hX
  change D.smoothedValue hN hr hbase s hp hc0 hg j W X=_ at he
  rw [he]
  unfold reflectedValue
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*s.stratumShapeFactor (c0*∏i,p i)*z)
  apply tsum_congr
  intro t
  apply congrArg (fun z:ℂ=>
    (s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
      ((ramifiedScale 1 completedRamifiedStep t.2.1*
        Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
      paperKernel (Vstar W)
        ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c0*∏i,p i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
          (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)*z)
  simpa only [multiplierSum,D.sourceGamma_character,D.sourceGamma_mul,map_mul] using
    D.multiplierSum_eq hN hr hbase hp hc0 hcop hg hchar j hj
      (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))

end ControlledStratumArithmetic

theorem exists_constructed_stratum_reflection {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hprimary:∀i,lambda^2∣p i-1)
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (N a0 c0:Eis) (hc0:c0≠0) (hN:(9:Eis)*c0∣N)
    (mode:Bool) (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hac:IsCoprime a0 c0) (hNp:∀i,IsCoprime N (p i)) :
    ∃s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode),
      ∃D:ControlledStratumArithmetic p N a0 c0 mode,
      ∀j:ι→ℕ,(∀i,j i<6)→∀(W:ℝ→ℂ)(lo hi:ℝ),0<lo→
        Function.support W⊆Set.Icc lo hi → ContDiff ℝ ∞ W→∀X:ℝ,0<X→
        D.smoothedValue hN (primary_finset_product Finset.univ p (fun i _=>hprimary i))
          hbase s hp hc0 hg j W X=D.reflectedValue s hp hc0 hg j W X := by
  obtain ⟨s⟩:=exists_fixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)
  obtain ⟨D⟩:=exists_controlledStratumArithmetic p hp hcop hprimary N a0 c0 hc0 hN mode hbase hac hNp
  refine ⟨s,D,?_⟩
  intro j hj W lo hi hlo hsupp hW X hX
  exact D.smoothed_eq_reflected hN _ hbase s hp hc0 hcop hg hchar j hj W lo hi hlo hsupp hW X hX

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)
theorem model_array_brackets {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (c0:Eis) (hc0:c0≠0) (d U:Eis) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    (s.amplitude u m I J*cuspBadPhase c0 hc0 d U (s.modelDualNumerator u m I J))*
      (∏i,bracket (complexSexticChar (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))=
    ramifiedBranchPhase P hg j (sourcePhaseUnit s.index s.phaseUpperUnit u)
      (sourcePhaseExponent s.index m)*
      ∑e:ι→Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-d*U)) (s.modelDualNumerator u) u) m I J*
        reflectedBranch P hg j e (primaryIdealGenerator I) (primaryIdealGenerator J) := by
  let φ:=s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-d*U)) (s.modelDualNumerator u) u
  have hA:φ m I J*fixedConjugateCuspArray s.index u m I J=
      s.amplitude u m I J*cuspBadPhase c0 hc0 d U (s.modelDualNumerator u m I J) := by
    rw [cuspBadPhase_as_fixed_residue]
    exact s.fixedCuspArrayWithPhase_reflectionStaticPhase c0 hc0 _ _ u m I J
  have hbr:=fixedCuspArray_phase_brackets P hg j s.index s.phaseUpperUnit u m I J
  rw [s.phaseUpperUnit_val] at hbr
  change fixedConjugateCuspArray s.index u m I J*
    (∏i,bracket (complexSexticChar (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))=_ at hbr
  rw [←hA]
  calc
    _=φ m I J*(fixedConjugateCuspArray s.index u m I J*
      (∏i,bracket (complexSexticChar (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))) := by ring
    _=φ m I J*(fixedConjugateCuspArray s.index u m I J*
      ramifiedBranchPhase P hg j (sourcePhaseUnit s.index s.phaseUpperUnit u)
        (sourcePhaseExponent s.index m)*
        ∑e:ι→Fin 3,reflectedBranch P hg j e (primaryIdealGenerator I) (primaryIdealGenerator J)) := by rw [hbr]
    _=_ := by
      simp only [fixedCuspArrayWithPhase]
      rw [←Finset.mul_sum]
      dsimp only [φ]
      ring

end FixedCuspShape

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
noncomputable local instance coefficientField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P
noncomputable local instance coefficientFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

def activePhase (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) : ℂ :=
  ∏i,(((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (complexSexticChar (Ideal.span {p i}) (hg i)) (residueTraceQuotientChar 1 (p i) (hp i)) (j i) (D.epsilon i)

lemma activePhase_norm (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6) :
    ‖D.activePhase hp hg j‖=1 := by
  rw [activePhase,norm_prod]
  have he (i:ι):‖(((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (complexSexticChar (Ideal.span {p i}) (hg i)) (residueTraceQuotientChar 1 (p i) (hp i)) (j i) (D.epsilon i)‖=1 := by
    rw [norm_mul,finiteMulChar_unit_norm,one_mul]
    exact canonical_phase_norm (Ideal.span {p i}) (hg i) (hchar i) (residueTraceQuotientChar 1 (p i) (hp i))
      (residueTraceQuotientChar_primitive (p i) (hp i)) (j i) (hj i) (D.epsilon i)
  simp only [he,Finset.prod_const_one]

lemma bracketProduct_eq (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) :
    D.bracketProduct hp hg j x=D.activePhase hp hg j*
      ∏i,bracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x) := by
  exact Finset.prod_mul_distrib

def modelRowPhase (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (u:Eisˣ) (m:ℕ) : ℂ :=
  star D.fixedFactor*D.activePhase hp hg j*
    ramifiedBranchPhase (fun i=>Ideal.span {p i}) hg j
      (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)

theorem modelRowPhase_norm (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (u:Eisˣ) (m:ℕ) : ‖D.modelRowPhase s hp hg j u m‖=1 := by
  rw [modelRowPhase,norm_mul,norm_mul,norm_star,D.fixedFactor_norm hN hr hbase,
    D.activePhase_norm hp hg hchar j hj,ramifiedBranchPhase_norm,one_mul,one_mul]

theorem model_coefficient (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    s.amplitude u m I J*
      (star D.fixedFactor*cuspBadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U (s.modelDualNumerator u m I J))*
      D.bracketProduct hp hg j (s.modelDualNumerator u m I J)=
    D.modelRowPhase s hp hg j u m*
      ∑e:ι→Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U))
            (s.modelDualNumerator u) u) m I J*
        reflectedBranch (fun i=>Ideal.span {p i}) hg j e (primaryIdealGenerator I) (primaryIdealGenerator J) := by
  rw [D.bracketProduct_eq]
  have he:=s.model_array_brackets (fun i=>Ideal.span {p i}) hg j c0 hc0
    (D.matrix (fun _=>1) 1 1) D.U u m I J
  calc
    _=(star D.fixedFactor*D.activePhase hp hg j)*
      ((s.amplitude u m I J*cuspBadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U (s.modelDualNumerator u m I J))*
        (∏i,bracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk _ (s.modelDualNumerator u m I J)))) := by ring
    _=_ := by rw [he];dsimp only [modelRowPhase];ring

end ControlledStratumArithmetic

lemma fixed_stratum_kernel_scale (j:Fin 3) (c0 r:Eis) :
    27*(sourceCuspScale j)^2*(Ideal.absNorm (Ideal.span {c0*r}):ℝ)^2=
      fixedCuspLevelScale j c0*(Ideal.absNorm (Ideal.span {r}):ℝ)^2 := by
  rw [←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul,mul_pow,fixedCuspLevelScale]
  ring

end

noncomputable section
open Eisenstein CubicKubota CompletedGauss RationalSource NormalizedReflection
open scoped BigOperators Classical MatrixGroups
local notation "Eis" => Eisenstein.O
lemma theta_lifted_phase (c : Eis) (hc : c≠0) (lift n : Eis) :
    tracePhase (-cuspFrequency n*((ringComplex traceLambda)^2*ringComplex lift/ringComplex c)) =
      residueTraceQuotientChar 1 c hc (Ideal.Quotient.mk _ lift*Ideal.Quotient.mk _ n) := by
  rw [←map_mul,residueTraceQuotientChar_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_ofNat,mul_one,traceLambda_complex_square]
  congr 1
  field_simp

lemma ControlledStratumArithmetic.datum_fourier_phase {ι:Type*} [Fintype ι]
    {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
    (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (n:Eis) :
    tracePhase (-cuspFrequency n*(D.datum hN hr hbase s hp hc0 v).point)=
      tracePhase (-cuspFrequency n*(ringComplex a0/ringComplex c0))*
        ∏i,residueTraceQuotientChar 1 (p i) (hp i) ((v i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ n) := by
  rw [D.datum_point]
  have he:-cuspFrequency n*(ringComplex a0/ringComplex c0+
      (ringComplex traceLambda)^2*∑i,ringComplex (D.lift v i)/ringComplex (p i))=
      -cuspFrequency n*(ringComplex a0/ringComplex c0)+
        ∑i,-cuspFrequency n*((ringComplex traceLambda)^2*ringComplex (D.lift v i)/ringComplex (p i)):=by
    simp only [Finset.mul_sum,neg_mul,mul_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he,AddChar.map_add_eq_mul,tracePhase_finset_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [theta_lifted_phase,D.lift_residue]

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff
local notation "Eis" => Eisenstein.O

lemma SourceCuspDatum.smoothedKernel_eq (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) :
    d.smoothedKernel W X=d.smoothingMultiplier*∑'n:Eis,
      sourceCuspRadialCoefficient d.index d.dualPoint n*
        paperKernel (Vstar W) (d.smoothingScale X*sourceCuspRadialLength n) := by
  have ht:‖ringComplex traceLambda‖^2=3 := by
    rw [←norm_pow,traceLambda_complex_square]
    norm_num
  have hb:thetaBesselScale^2=1/27 := by
    simp only [thetaBesselScale,thetaFrequencyScale,norm_div,norm_one,norm_mul,
      div_pow,mul_pow,ht]
    norm_num
  have he:d.smoothingScale X=X/(27*(sourceCuspScale d.index)^2*d.heightScale^2) := by
    rw [SourceCuspDatum.smoothingScale,sourceCuspRadialScale,sourceCuspRadialScale,
      show sourceCuspScale 0=1 from rfl,div_one,div_pow,hb]
    ring
  rw [SourceCuspDatum.smoothedKernel,SourceCuspDatum.smoothingMultiplier,
    sourceCuspRadialScale_ratio]
  push_cast
  rw [mul_assoc d.multiplier]
  congr 1
  apply tsum_congr
  intro n
  rw [he]
  congr 2
  ring

/-- The reflected kernel equals the compactly smoothed source at its cusp. -/
lemma SourceCuspDatum.smoothedKernel_source (d:SourceCuspDatum)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hs:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    d.smoothedKernel W X=∑'n:Eis,sourceBarRadialCoefficient d.point n*
      Vstar W (sourceCuspRadialLength n/X) := by
  rw [d.smoothedKernel_eq]
  exact (d.smoothed_reflection (Vstar W) a b ha (Vstar_support W a b hs)
    (Vstar_contDiff W a b ha hs hW) X hX).symm

theorem completedT_canonical_smoothed_reflection (Ψ:Eis→*ℂ) (_hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hs:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT Ψ W X=thetaDerivativeScalar⁻¹*∑h:Eis⧸Ideal.span {c},
      finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) (fixedThetaQuotient Ψ c) h*
        (finiteTwistCusp c hc h).smoothedKernel W X := by
  have hp (n:Eis) : (∑h:Eis⧸Ideal.span {c},
      finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) (fixedThetaQuotient Ψ c) h*
        tracePhase (-cuspFrequency n*(finiteTwistCusp c hc h).point))=fixedThetaTwist Ψ n := by
    simp_rw [finiteTwistCusp_point]
    rw [thetaFourierTranslation_inversion,fixedThetaQuotient_mk Ψ Q hperiod c hcQ]
  simpa only [SourceCuspDatum.smoothedKernel_eq] using
    completedT_finite_phase_reflection Ψ (finiteTwistCusp c hc)
      (finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 c hc) (fixedThetaQuotient Ψ c))
      hp W a b ha hs hW X hX

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open SchwartzPlanePoisson.CanonicalQuadraticSieve
open UniqueFactorizationMonoid
open scoped BigOperators Classical
local notation "Eis" => Eisenstein.O
namespace CanonicalCoefficientClass
def fixedBaseConductor (m : ℕ) : Ideal Eisenstein.O := Ideal.span {(m : Eisenstein.O)}*Ideal.span {(4 : Eisenstein.O)}

lemma fixedBaseConductor_principal (m : ℕ) :
    fixedBaseConductor m=Ideal.span {((4*m : ℕ) : Eisenstein.O)} := by
  rw [fixedBaseConductor,Ideal.span_singleton_mul_span_singleton]
  congr 1
  push_cast
  ring_nf

lemma fixedBaseConductor_ne_zero (m : ℕ) (hm : m≠0) : fixedBaseConductor m≠0 := by
  rw [fixedBaseConductor_principal]
  change Ideal.span {((4*m : ℕ) : Eisenstein.O)}≠⊥
  rw [ne_eq,Ideal.span_singleton_eq_bot]
  exact_mod_cast Nat.mul_ne_zero (by decide : (4:ℕ)≠0) hm


end CanonicalCoefficientClass

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
local notation "Eis" => Eisenstein.O
namespace CanonicalRowCompletion
noncomputable def fiberGoodMaskRowData (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (m:Eis)
    (hm:m≠0) (hF:F≠0) (hrows:∀I∈rows,I≠0) (u:Eisˣ)
    (I:representativeRowFiber rows R (Ideal.span {m}*F)) :
    GoodMaskRowData m (cubicIdealGenerator F)
      (u.val*cubicIdealGenerator I.val) :=
  goodMaskRowData _ _ _ hm (cubicIdealGenerator_ne_zero F hF)
    (mul_ne_zero u.ne_zero (cubicIdealGenerator_ne_zero I.val
      (hrows I.val (Finset.mem_filter.mp I.property).1)))

end CanonicalRowCompletion
end

noncomputable section
open scoped ContDiff
namespace CanonicalRowCompletion
lemma normTwistedSource_contDiff (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W) (t:ℝ) :
    ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W t) := by
  have he:(CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t:ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t:=by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  rw [←he]
  exact (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t).smooth ⊤


end CanonicalRowCompletion
end

noncomputable section
namespace CanonicalCoefficientClass
open Eisenstein RayFourExpansion FirstPassCubeLabels
open InverseFirstRayAttachment InverseInitialRayAttachment

lemma IsBaseRayTwist.firstCore {base Ψ : O →* ℂ}
    (hΨ : IsBaseRayTwist base Ψ) (side : Bool) (χ : RayCharacter) (r : FirstCoreIndex) :
    IsBaseRayTwist base (firstCoreTwist side χ Ψ r) := by
  have hc : coreRayTwist side r.1 r.2.2 = rayMonoid (coreRayCharacter side r.1 r.2.2) := rfl
  unfold firstCoreTwist sideRayMonoid
  rw [hc]
  cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact (hΨ.mul_ray_right _).mul_ray _
  · exact (hΨ.mul_ray_right _).mul_ray _

lemma IsBaseRayTwist.secondMinus {base Ψ : O →* ℂ}
    (hΨ : IsBaseRayTwist base Ψ) (r : SecondRayIndex) :
    IsBaseRayTwist base (secondRayMinus Ψ r) := by
  have hc : (starRingEnd ℂ).toMonoidHom.comp (rayMonoid r.1) = rayMonoid (star r.1) := by
    ext x
    simp only [MonoidHom.comp_apply,
      rayMonoid_apply, MulChar.star_apply]
    rfl
  rw [secondRayMinus, hc]
  exact hΨ.mul_ray _

lemma IsBaseRayTwist.secondPlus {base Ψ : O →* ℂ}
    (hΨ : IsBaseRayTwist base Ψ) (r : SecondRayIndex) :
    IsBaseRayTwist base (secondRayPlus Ψ r) := hΨ.mul_ray _

end CanonicalCoefficientClass
end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
