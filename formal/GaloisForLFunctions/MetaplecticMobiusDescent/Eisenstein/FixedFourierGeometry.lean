/-
Fixed Fourier geometry adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.RowCompletion.CuspBadPhases
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.CanonicalLongSources
import GaloisForLFunctions.MetaplecticMobiusDescent.Cusp.ControlledStratumArithmetic

/-!
# Fixed Fourier geometry

Fixed cusps and fixed factors of a controlled stratum, the fixed Fourier geometry and level
bounds; amplitudes and static reflection phases of fixed cusp shapes; the exact reflected
radial series at a fixed cusp and fixed reflection ray counts.
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
open Eisenstein
open scoped BigOperators Classical MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

lemma frequency_congruence (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (D.matrix v 0 0)=
      (D.sigma i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}) := by
  rw [D.numerator,cuspCrossNumerator_local,D.sigma_value,D.lift_residue]

lemma numerator_congruence (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    N∣D.matrix v 0 0-a0*∏i,p i := by
  rw [D.numerator]
  exact cuspCrossNumerator_fixed N a0 c0 traceLambda p (D.lift v)
    (fun i=>(dvd_pow_self N (by decide : (2:ℕ)≠0)).trans (D.lift_period v i))

lemma numerator_mod_three (D:ControlledStratumArithmetic p N a0 c0 mode)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : (3:Eis)∣D.matrix v 0 0-a0 := by
  have hprod:=three_dvd_primary_sub_one (∏i,p i) hr
  convert dvd_add (h3N.trans (D.numerator_congruence v))
    (dvd_mul_of_dvd_right hprod a0) using 1 ; ring

lemma numerator_primary (D:ControlledStratumArithmetic p N a0 c0 mode)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1) (ha:lambda^2∣a0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : lambda^2∣D.matrix v 0 0-1 := by
  convert dvd_add (lambda_sq_dvd_three.trans (D.numerator_mod_three h3N hr v)) ha using 1 ; ring

lemma denominator_primary (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hr:lambda^2∣(∏i,p i)-1) (hc:lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : lambda^2∣D.matrix v 1 0-1 := by
  rw [D.denominator]
  exact primary_mul c0 (∏i,p i) hc hr

lemma ramified_relative (D:ControlledStratumArithmetic p N a0 c0 true)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1) (ha:lambda^2∣a0-1)
    (u:Eis) (hcu:(3:Eis)∣c0-u) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v*(lowerCuspMatrix u)⁻¹∈levelThree := by
  have hcond := D.conditions v
  simp only [ ↓reduceIte] at hcond
  apply primary_numerator_matrix_relative (D.matrix v) u
  · exact D.numerator_primary h3N hr ha v
  · exact hcond.1
  · rw [D.denominator]
    have hprod:=three_dvd_primary_sub_one (∏i,p i) hr
    convert dvd_add (dvd_mul_of_dvd_right hprod c0) hcu using 1 <;> ring
  · exact hcond.2

lemma unramified_relative (D:ControlledStratumArithmetic p N a0 c0 false)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1) (hc:lambda^2∣c0-1)
    (u:Eis) (hau:(3:Eis)∣a0-u) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v*(weylCuspMatrix u)⁻¹∈levelThree := by
  have hcond := D.conditions v
  simp only [Bool.false_eq_true, ↓reduceIte] at hcond
  apply primary_denominator_matrix_relative (D.matrix v) u
  · convert dvd_add (D.numerator_mod_three h3N hr v) hau using 1 <;> ring
  · exact hcond.1
  · exact D.denominator_primary hr hc v
  · exact hcond.2

lemma inverse_fixed (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    traceLambda^3*c0∣D.matrix v 1 1-D.matrix (fun _=>1) 1 1 := by
  have hD9:traceLambda^3*c0∣(9:Eis)*c0 := by
    refine ⟨traceLambda,?_⟩
    rw [←traceLambda_pow_four]
    ring
  exact (hD9.trans hN).trans (D.matrix_fixed v 1 1)

lemma determinant (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v 0 0*D.matrix v 1 1-D.matrix v 0 1*(c0*∏i,p i)=1 := by
  simpa only [Matrix.det_fin_two,D.denominator] using (D.matrix v).property


end ControlledStratumArithmetic
end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein
open scoped BigOperators Classical MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

def fixedCusp (a0 c0:Eis) (mode:Bool) : SL(2,Eis) :=
  if mode then lowerCuspMatrix c0 else weylCuspMatrix a0

lemma relative (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v*(fixedCusp a0 c0 mode)⁻¹∈levelThree := by
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
    ((dvd_mul_right 9 c0).trans hN)
  cases mode
  · exact D.unramified_relative h3N hr hbase a0 (by simp) v
  · exact D.ramified_relative h3N hr hbase c0 (by simp) v

def relativeGamma (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : levelThree :=
  ⟨D.matrix v*(fixedCusp a0 c0 mode)⁻¹,D.relative hN hr hbase v⟩

lemma relativeGamma_mul (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.relativeGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode=D.matrix v := by
  exact inv_mul_cancel_right (D.matrix v) (fixedCusp a0 c0 mode)

def fixedFactor (D:ControlledStratumArithmetic p N a0 c0 mode) : ℂ :=
  if mode then
    ringComplex (symbol (-c0) (D.matrix (fun _=>1) 0 0-c0*D.matrix (fun _=>1) 0 1)*
      symbol 1 (D.matrix (fun _=>1) 0 0))
  else ringComplex (symbol (D.matrix (fun _=>1) 0 0) c0)

theorem relative_character (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    complexCharacter (D.relativeGamma hN hr hbase v)=
      D.fixedFactor*ringComplex (symbol (D.matrix v 0 0) (∏i,p i)) := by
  have h9N : (9:Eis)∣N := (dvd_mul_right 9 c0).trans hN
  have h3N : (3:Eis)∣N := (show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N
  have hcN : c0∣N := (dvd_mul_left c0 9).trans hN
  cases mode
  · have hb := levelThree_primary (D.relativeGamma hN hr hbase v)
    change lambda^2∣(((D.matrix v*(weylCuspMatrix a0)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hb
    rw [weylCusp_relative_matrix] at hb
    change lambda^2∣(-D.matrix v 0 1)-1 at hb
    change complexCharacter ⟨D.matrix v*(weylCuspMatrix a0)⁻¹,_⟩=_
    rw [weylCusp_relative_character,cuspSymbol_weyl_factor _ _ _ _ _ (D.determinant v) hb
      (primary_mul c0 _ hbase hr) (dvd_mul_of_dvd_right (D.conditions v).2 _),map_mul]
    rw [cuspSymbol_weyl_fixed_congr N c0 _ _ hcN (D.matrix_fixed v 0 0)]
    rfl
  · have ha := D.numerator_primary h3N hr hbase v
    have ha0 := D.numerator_primary h3N hr hbase (fun _=>1)
    have hA := lowerCusp_relative_primary (D.matrix v) c0 (D.relative hN hr hbase v)
    have hA0 := lowerCusp_relative_primary (D.matrix (fun _=>1)) c0 (D.relative hN hr hbase (fun _=>1))
    change complexCharacter ⟨D.matrix v*(lowerCuspMatrix c0)⁻¹,_⟩=_
    rw [lowerCusp_relative_character,D.denominator]
    have he := cuspSymbol_ramified_factor (D.matrix v 0 0) (D.matrix v 0 1) 1 (∏i,p i)
      (D.matrix v 1 1) c0 (by simpa only [one_mul] using D.determinant v) ha hA hr
    simp only [one_mul] at he
    rw [he,cuspSymbol_ramified_fixed_congr N 1 c0 _ _ _ _ h9N (one_dvd _) hcN
      ha ha0 hA hA0 (D.matrix_fixed v 0 0) (D.matrix_fixed v 0 1),map_mul]
    rfl

theorem fixedFactor_norm (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1) : ‖D.fixedFactor‖=1 := by
  have h3N : (3:Eis)∣N := (show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
    ((dvd_mul_right 9 c0).trans hN)
  cases mode
  · exact cuspSymbol_weyl_fixed_norm _ _ _ _ _ (D.determinant (fun _=>1)) hbase
  · apply cuspSymbol_ramified_fixed_norm _ _ 1 (∏i,p i) _ c0
    · simpa only [one_mul] using D.determinant (fun _=>1)
    · exact D.numerator_primary h3N hr hbase (fun _=>1)
    · exact lowerCusp_relative_primary (D.matrix (fun _=>1)) c0
        (D.relative hN hr hbase (fun _=>1))

end ControlledStratumArithmetic

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein
open scoped BigOperators Classical MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
def sourceGamma (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : rationalExtension :=
  ⟨D.relativeGamma hN hr hbase v,levelThree_le_rationalExtension (D.relativeGamma hN hr hbase v).property⟩

lemma sourceGamma_mul (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.sourceGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode=D.matrix v :=
  D.relativeGamma_mul hN hr hbase v

lemma sourceGamma_character (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    extendedComplexCharacter (D.sourceGamma hN hr hbase v)=
      complexCharacter (D.relativeGamma hN hr hbase v) :=
  extendedComplexCharacter_restrict _

def datum (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : SourceCuspDatum :=
  s.datum (D.sourceGamma hN hr hbase v) (by
    rw [D.sourceGamma_mul,D.denominator]
    exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

lemma datum_point (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.datum hN hr hbase s hp hc0 v).point=ringComplex a0/ringComplex c0+
      (ringComplex traceLambda)^2*∑i,ringComplex (D.lift v i)/ringComplex (p i) := by
  rw [datum,s.datum_point,D.sourceGamma_mul,D.numerator,D.denominator]
  exact
    cuspCrossNumerator_fraction a0 c0 traceLambda p (D.lift v) hc0 hp


end ControlledStratumArithmetic
end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic
open MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
/-- The exact reflected radial series at a fixed cusp. -/
def SourceCuspDatum.smoothedKernel (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  (d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
    ∑'n:Eis,sourceCuspRadialCoefficient d.index d.dualPoint n*
      paperKernel (Vstar W)
        (X*sourceCuspRadialLength n/(27*(sourceCuspScale d.index)^2*d.heightScale^2))

lemma SourceCuspDatum.smoothedKernel_full_index (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) :
    d.smoothedKernel W X=
      (d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
        ∑'p:ThetaFullIndex,sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)*
          paperKernel (Vstar W)
            (X*sourceCuspRadialLength (thetaFullFrequency p)/
              (27*(sourceCuspScale d.index)^2*d.heightScale^2)) := by
  rw [SourceCuspDatum.smoothedKernel]
  congr 1
  exact sourceCuspRadial_tsum_full_index d.index d.dualPoint
    (fun h=>paperKernel (Vstar W)
      (X*sourceCuspRadialLength h/(27*(sourceCuspScale d.index)^2*d.heightScale^2)))


lemma SourceCuspDatum.smoothedKernel_full_index_norm_summable
    (d:SourceCuspDatum) (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    Summable (fun p:ThetaFullIndex=>
      ‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)*
        paperKernel (Vstar W)
          (X*sourceCuspRadialLength (thetaFullFrequency p)/
            (27*(sourceCuspScale d.index)^2*d.heightScale^2))‖) := by
  have hsum : Summable (fun h : Eis => ‖sourceCuspRadialCoefficient d.index d.dualPoint h‖ *
      sourceCuspRadialLength h ^ (-(3/2:ℝ))) := by
    simpa only [neg_div] using sourceCuspRadialCoefficient_weighted_summable d.index d.dualPoint
  have hs:=paperKernel_weighted_norm_summable sourceCuspRadialLength sourceCuspRadialLength_pos
    (sourceCuspRadialCoefficient d.index d.dualPoint)
    hsum
    (Vstar W) v0 v1 hv0 (Vstar_support W v0 v1 hWs) (Vstar_contDiff W v0 v1 hv0 hWs hW)
    (X/(27*(sourceCuspScale d.index)^2*d.heightScale^2))
    (by have := sourceCuspScale_pos d.index; have := d.heightScale_pos; positivity)
  have hp:=hs.comp_injective thetaFullFrequency_injective
  apply hp.congr
  intro p
  exact congrArg (fun y:ℝ=>‖sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)*
    paperKernel (Vstar W) y‖)
    (by ring :
      X/(27*(sourceCuspScale d.index)^2*d.heightScale^2)*sourceCuspRadialLength (thetaFullFrequency p)=
        X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale d.index)^2*d.heightScale^2))


end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic
open MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
lemma thetaFullIndex_denominator_pos (p:ThetaFullIndex) :
    0<ramifiedScale 1 completedRamifiedStep p.2.1*
      Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ) := by
  have hI:0<(Ideal.absNorm p.2.2.1.val:ℝ):=by
    rw [←primaryIdealGenerator_norm_sq _ p.2.2.1.property.2]
    exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero p.2.2.1.property.2))
  have hJ:0<(Ideal.absNorm p.2.2.2.val:ℝ):=by
    rw [←primaryIdealGenerator_norm_sq _ p.2.2.2.property]
    exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero p.2.2.2.property))
  rw [thetaRamifiedScale_eq]
  positivity

lemma SourceCuspDatum.smoothed_unit_phase_norm (d:SourceCuspDatum) :
    ‖d.multiplier*(d.heightScale:ℂ)‖=1 := by
  rw [norm_mul,d.multiplier_norm,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos d.heightScale_pos,inv_mul_cancel₀ d.heightScale_pos.ne']

theorem SourceCuspDatum.smoothedFullCoefficient_normalization (d:SourceCuspDatum) (p:ThetaFullIndex) :
    (d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
      sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)=
    (fixedRadialCoefficientScalar*(d.multiplier*(d.heightScale:ℂ)))*
      (fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
        angularFactor (thetaFullFrequency p)*
        tracePhase (-cuspFrequency (thetaFullFrequency p)*
          (d.dualPoint/(sourceCuspScale d.index:ℂ))))/
      ((ramifiedScale 1 completedRamifiedStep p.2.1*
        Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ) := by
  have hs:(sourceCuspScale d.index:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos _).ne'
  have hn:((ramifiedScale 1 completedRamifiedStep p.2.1*
      Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (thetaFullIndex_denominator_pos p).ne'
  simp only [thetaFullFrequency_eq_fixedCuspArrayIndex]
  rw [sourceCuspRadialCoefficient_fixed_array _ _ _ _ _ _
    ⟨p.2.2.1.property.1,p.2.2.1.property.2,p.2.2.2.property⟩]
  field_simp [hs,hn]

lemma SourceCuspDatum.smoothedFullCoefficient_norm_le (d:SourceCuspDatum) (p:ThetaFullIndex) :
    ‖(d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
      sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)‖≤
    ‖fixedRadialCoefficientScalar‖/
      (ramifiedScale 1 completedRamifiedStep p.2.1*
        Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)) := by
  have ha:‖fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      angularFactor (thetaFullFrequency p)*
      tracePhase (-cuspFrequency (thetaFullFrequency p)*
        (d.dualPoint/(sourceCuspScale d.index:ℂ)))‖≤1:=by
    rw [norm_mul,norm_mul,norm_angularFactor _ (thetaFullFrequency_ne_zero p),tracePhase_norm,mul_one,mul_one]
    exact fixedConjugateCuspArray_norm_le_one _ _ _ _ _
  rw [d.smoothedFullCoefficient_normalization,norm_div,norm_mul,norm_mul,
    d.smoothed_unit_phase_norm,mul_one,Complex.norm_real,Real.norm_of_nonneg (thetaFullIndex_denominator_pos p).le]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_right (norm_nonneg _) ha) (thetaFullIndex_denominator_pos p).le

theorem SourceCuspDatum.smoothedKernel_fixed_array (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) :
    d.smoothedKernel W X=(fixedRadialCoefficientScalar*(d.multiplier*(d.heightScale:ℂ)))*
      ∑'p:ThetaFullIndex,
        ((fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
          angularFactor (thetaFullFrequency p)*
          tracePhase (-cuspFrequency (thetaFullFrequency p)*
            (d.dualPoint/(sourceCuspScale d.index:ℂ))))/
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        paperKernel (Vstar W)
          ((X/(27*(sourceCuspScale d.index)^2*d.heightScale^2))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3) := by
  rw [d.smoothedKernel_full_index,←tsum_mul_left,←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [←mul_assoc,d.smoothedFullCoefficient_normalization,sourceCusp_full_index_kernel_argument]
  ring

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic
open MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
theorem sum_smoothedKernel_common_cusp {ι:Type*} [Fintype ι]
    (d:ι→SourceCuspDatum) (w:ι→ℂ) (j:Fin 3) (Q:ℝ)
    (hj:∀i,(d i).index=j) (hQ:∀i,(d i).heightScale=Q)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑i,w i*(d i).smoothedKernel W X)=fixedRadialCoefficientScalar*
      ∑'p:ThetaFullIndex,
        ((fixedConjugateCuspArray j p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
          angularFactor (thetaFullFrequency p))/
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        paperKernel (Vstar W)
          (X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale j)^2*Q^2))*
        (∑i,w i*((d i).multiplier*(Q:ℂ))*
          tracePhase (-cuspFrequency (thetaFullFrequency p)*
            ((d i).dualPoint/(sourceCuspScale j:ℂ)))) := by
  let F:ι→ThetaFullIndex→ℂ:=fun i p=>w i*
    ((d i).multiplier*((d i).heightScale:ℂ)*(sourceCuspScale (d i).index:ℂ)^2)*
    (sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p)*
      paperKernel (Vstar W)
        (X*sourceCuspRadialLength (thetaFullFrequency p)/
          (27*(sourceCuspScale (d i).index)^2*(d i).heightScale^2)))
  have hs (i:ι):Summable (F i):=by
    exact ((d i).smoothedKernel_full_index_norm_summable W a b ha hsupp hW X hX).of_norm.mul_left _
  have he (i:ι):w i*(d i).smoothedKernel W X=∑'p,F i p := by
    rw [(d i).smoothedKernel_full_index]
    simp only [F,tsum_mul_left]
    ring
  simp_rw [he]
  rw [←Summable.tsum_finsetSum (fun i _=>hs i),←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hn:=(d i).smoothedFullCoefficient_normalization p
  dsimp only [F]
  calc
    _=w i*(((d i).multiplier*((d i).heightScale:ℂ)*(sourceCuspScale (d i).index:ℂ)^2)*
      sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p))*
      paperKernel (Vstar W)
        (X*sourceCuspRadialLength (thetaFullFrequency p)/
          (27*(sourceCuspScale (d i).index)^2*(d i).heightScale^2)):=by ring
    _=_:=by rw [hn,hj i,hQ i]; ring

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss NormalizedReflection
open scoped BigOperators Classical MatrixGroups Matrix
local notation "Eis" => Eisenstein.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
noncomputable def fourierWeight [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∏i,finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (p i) (hp i))
    (fun t=>(complexSexticChar (Ideal.span {p i}) (hg i)^j i) t) (v i)

noncomputable def multiplierSum (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,
    fourierWeight hp hg j v*star (complexCharacter (D.relativeGamma hN hr hbase v))*
      tracePhase (-(ringComplex (D.matrix v 1 1)*(ringComplex x/(ringComplex traceLambda)^4))/
        (ringComplex c0*ringComplex (∏i,p i)))

noncomputable def bracketProduct (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) : ℂ := by
  letI (i:ι):Field (Eis⧸Ideal.span {p i}):=Ideal.Quotient.field _
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∏i,(((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    NormalizedReflection.phase (complexSexticChar (Ideal.span {p i}) (hg i)) (residueTraceQuotientChar 1 (p i) (hp i)) (j i) (D.epsilon i)*
    bracket (complexSexticChar (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x)

theorem multiplierSum_eq (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hp:∀i,p i≠0) (hc0:c0≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j:ι→ℕ) (hj:∀i,j i<6) (x:Eis) :
    D.multiplierSum hN hr hbase hp hg j x=
      (star D.fixedFactor*cuspBadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U x)*
        D.bracketProduct hp hg j x := by
  have hpair : Pairwise (Function.onFun IsCoprime p) := by
    intro i k hik
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp (hcop hik)
  have ht (i:ι) : ∃t:Eis,p i∣cuspPrimeCofactor p i*t-1 := by
    have hc : IsCoprime (p i) (cuspPrimeCofactor p i) :=
      IsCoprime.prod_right (fun k hk=>hpair (Ne.symm (Finset.mem_erase.mp hk).1))
    obtain ⟨a,b,hab⟩ := hc
    exact ⟨b,⟨-a,by linear_combination hab⟩⟩
  choose t ht using ht
  have he := cuspMatrix_character_frequency_sum p t hp hg hpair ht c0 D.U D.w x hc0
    D.bezout D.matrix (fun v=>by rw [D.denominator];exact dvd_mul_left _ _)
    (D.inverse_fixed hN) D.sigma D.epsilon D.frequency_congruence D.epsilon_value
    D.fixedFactor (fun v=>complexCharacter (D.relativeGamma hN hr hbase v))
    (D.relative_character hN hr hbase) j
  have hgprod :
      (∏i,((complexSexticChar (Ideal.span {p i}) (hg i))⁻¹^2) (D.sigma i)*
        finiteReflectionGauss (complexSexticChar (Ideal.span {p i}) (hg i))
          (residueTraceQuotientChar 1 (p i) (hp i)) (j i)
          ((D.epsilon i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ x)) =
      D.bracketProduct hp hg j x := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [canonical_gauss_eq_phase_bracket (Ideal.span {p i}) (hg i) (hchar i)
      _ (residueTraceQuotientChar_primitive (p i) (hp i)) (j i) (hj i)]
    ring
  simp_rw [←finiteReflectionGauss_product] at he
  rw [hgprod] at he
  rw [cuspBadPhase_eq]
  rw [show -(ringComplex (D.matrix (fun _ => 1) 1 1) * ringComplex D.U *
      (ringComplex x / ringComplex traceLambda ^ 4)) / ringComplex c0 =
      -(ringComplex (D.matrix (fun _ => 1) 1 1) * ringComplex D.U * ringComplex x) /
      (ringComplex traceLambda ^ 4 * ringComplex c0) by ring]
  refine Eq.trans ?_ he
  unfold multiplierSum fourierWeight
  apply Finset.sum_congr rfl
  intro v hv
  congr 2
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end ControlledStratumArithmetic

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
lemma divisor_principal_norm_le (c0 c:Eis) (hc:c≠0) (hdiv:c0∣c) :
    (Ideal.absNorm (Ideal.span {c0}):ℝ)≤(Ideal.absNorm (Ideal.span {c}):ℝ) := by
  have hp:0<Ideal.absNorm (Ideal.span {c}):=Nat.pos_of_ne_zero (by
    intro hz
    exact hc (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hd:Ideal.absNorm (Ideal.span {c0})∣Ideal.absNorm (Ideal.span {c}) := by
    obtain ⟨d,hd⟩:=hdiv
    rw [hd,←Ideal.span_singleton_mul_span_singleton,map_mul]
    exact dvd_mul_right _ _
  exact_mod_cast Nat.le_of_dvd hp hd

def fixedCuspLevelBound (c:Eis) : ℝ :=
  243*(Ideal.absNorm (Ideal.span {c}):ℝ)^2

def fixedCuspLevelScale (j:Fin 3) (c0:Eis) : ℝ :=
  27*(sourceCuspScale j)^2*(Ideal.absNorm (Ideal.span {c0}):ℝ)^2

lemma fixedCuspLevelBound_ge_one (c:Eis) (hc:c≠0) : 1≤fixedCuspLevelBound c := by
  have hp:1≤Ideal.absNorm (Ideal.span {c}):=Nat.one_le_iff_ne_zero.mpr (by
    intro hz
    exact hc (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hr:(1:ℝ)≤(Ideal.absNorm (Ideal.span {c}):ℝ):=by exact_mod_cast hp
  unfold fixedCuspLevelBound
  nlinarith

lemma fixedCuspLevelScale_pos (j:Fin 3) (c0:Eis) (hc0:c0≠0) : 0<fixedCuspLevelScale j c0 := by
  have hp:0<Ideal.absNorm (Ideal.span {c0}):=Nat.pos_of_ne_zero (by
    intro hz
    exact hc0 (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hr:(0:ℝ)<(Ideal.absNorm (Ideal.span {c0}):ℝ):=by exact_mod_cast hp
  have hs:=sourceCuspScale_pos j
  unfold fixedCuspLevelScale
  positivity

lemma fixedCuspLevelScale_le (j:Fin 3) (c0 c:Eis) (hc:c≠0) (hdiv:c0∣c) :
    fixedCuspLevelScale j c0≤fixedCuspLevelBound c := by
  have hd:=divisor_principal_norm_le c0 c hc hdiv
  have hs:(sourceCuspScale j)^2≤9:=by fin_cases j <;> norm_num [sourceCuspScale]
  unfold fixedCuspLevelScale fixedCuspLevelBound
  calc
    27*(sourceCuspScale j)^2*(Ideal.absNorm (Ideal.span {c0}):ℝ)^2≤
      27*9*(Ideal.absNorm (Ideal.span {c}):ℝ)^2:=by gcongr
    _=_:=by ring

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic
open MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

def amplitude (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  fixedConjugateCuspArray s.index u m I J*
    angularFactor (fixedCuspArrayIndex u m I J)*
    tracePhase (-cuspFrequency (fixedCuspArrayIndex u m I J)*
      ringComplex (s.upper 0 0*s.upper 0 1)/(sourceCuspScale s.index:ℂ))

lemma amplitude_norm (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ‖s.amplitude u m I J‖≤1 := by
  by_cases he:fixedCuspArrayEligible I J
  · rw [amplitude,norm_mul,norm_mul,tracePhase_norm,
      norm_angularFactor _ (fixedCuspArrayIndex_ne_zero u m I J he.2.1 he.2.2),mul_one,mul_one]
    exact fixedConjugateCuspArray_norm_le_one _ _ _ _ _
  · simp only [amplitude,fixedConjugateCuspArray,
      fixedCuspArray_zero_of_ineligible _ _ _ _ _ he,star_zero,zero_mul,norm_zero]
    norm_num

theorem smoothedKernel_fixed_shape (g:rationalExtension) (hc:((g:SL(2,Eis))*H) 1 0≠0)
    (W:ℝ→ℂ) (X:ℝ) :
    (s.datum g hc).smoothedKernel W X=
      (fixedRadialCoefficientScalar*((s.datum g hc).multiplier*
        (‖ringComplex (((g:SL(2,Eis))*H) 1 0)‖^2:ℝ)))*
      ∑'p:ThetaFullIndex,
        ((s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
          tracePhase (cuspFrequency (thetaFullFrequency p)*
            ringComplex (s.upper 0 0)^2*
            (ringComplex (((g:SL(2,Eis))*H) 1 1)/ringComplex (((g:SL(2,Eis))*H) 1 0))/
            (sourceCuspScale s.index:ℂ)))/
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        paperKernel (Vstar W)
          ((X/(27*(sourceCuspScale s.index)^2*‖ringComplex (((g:SL(2,Eis))*H) 1 0)‖^4))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3) := by
  rw [(s.datum g hc).smoothedKernel_fixed_array,s.datum_heightScale]
  have hi:(s.datum g hc).index=s.index:=rfl
  simp only [hi,←pow_mul,show (2:ℕ)*2=4 by norm_num]
  congr 1
  apply tsum_congr
  intro p
  have hp:=s.datum_additive_phase g hc (cuspFrequency (thetaFullFrequency p))
    (sourceCuspScale s.index:ℂ)
  rw [show -cuspFrequency (thetaFullFrequency p)*
      ((s.datum g hc).dualPoint/(sourceCuspScale s.index:ℂ))=
      -cuspFrequency (thetaFullFrequency p)*(s.datum g hc).dualPoint/(sourceCuspScale s.index:ℂ) by ring,hp]
  unfold amplitude
  rw [←thetaFullFrequency_eq_fixedCuspArrayIndex]
  ring

lemma smoothed_row_factor (g:rationalExtension) (hc:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g hc).multiplier*((s.datum g hc).heightScale:ℂ)=
      -star (extendedComplexCharacter g)*
        (star (extendedComplexCharacter s.gamma)*ringComplex (s.upper 0 0)^2)*
        ((‖ringComplex (((g:SL(2,Eis))*H) 1 0)‖^2:ℝ):ℂ)/
        ringComplex (((g:SL(2,Eis))*H) 1 0)^2 := by
  rw [s.datum_multiplier,s.datum_heightScale]
  push_cast
  ring

end FixedCuspShape
end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss
open scoped BigOperators Classical MatrixGroups
local notation "Eis" => Eisenstein.O
lemma norm_angularFactor_le_one (h:Eis) : ‖angularFactor h‖≤1 := by
  by_cases hh:h=0
  · simp only [hh,angularFactor,map_zero,norm_zero,Complex.ofReal_zero,div_zero]
    norm_num
  · exact (norm_angularFactor h hh).le

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

def reflectionStaticPhase (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {traceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) : ℂ :=
  angularFactor (fixedCuspArrayIndex u m I J)*
    tracePhase (-cuspFrequency (fixedCuspArrayIndex u m I J)*
      ringComplex (s.upper 0 0*s.upper 0 1)/(sourceCuspScale s.index:ℂ))*
    cuspResiduePhase c0 hc0 v (dualNumerator m I J)

lemma reflectionStaticPhase_norm_le_one (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {traceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) : ‖s.reflectionStaticPhase c0 hc0 v dualNumerator u m I J‖≤1 := by
  simp only [reflectionStaticPhase,norm_mul,tracePhase_norm,cuspResiduePhase_norm,mul_one]
  exact norm_angularFactor_le_one _

lemma fixedCuspArrayWithPhase_reflectionStaticPhase (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {traceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) :
    fixedCuspArrayWithPhase s.index u (s.reflectionStaticPhase c0 hc0 v dualNumerator u) m I J=
      s.amplitude u m I J*cuspResiduePhase c0 hc0 v (dualNumerator m I J) := by
  unfold fixedCuspArrayWithPhase reflectionStaticPhase amplitude
  ring

end FixedCuspShape
end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
structure FixedFourierGeometry (c:Eis) (h:Eis⧸Ideal.span {c}) where
  a0 : Eis
  c0 : Eis
  denominator_ne_zero : c0≠0
  denominator_dvd : c0∣c
  coprime : IsCoprime a0 c0
  point : ringComplex a0/ringComplex c0=thetaFourierTranslation c h
  mode : Bool
  primary : if mode then lambda^2∣a0-1 else lambda^2∣c0-1
  shape : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)

lemma exists_fixedFourierGeometry (c:Eis) (hc:c≠0) (h:Eis⧸Ideal.span {c}) :
    Nonempty (FixedFourierGeometry c h) := by
  obtain ⟨a0,c0,hc0,hcop,hdiv,hprimary,hpoint⟩ :=
    exists_primary_cusp_coordinates (-3*Quotient.out h) c hc
  have hp:ringComplex a0/ringComplex c0=thetaFourierTranslation c h := by
    rw [hpoint,thetaFourierTranslation]
    simp only [map_mul,map_neg,map_ofNat]
  rcases hprimary with ha | hc'
  · obtain ⟨s⟩:=exists_fixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 true)
    exact ⟨⟨a0,c0,hc0,hdiv,hcop,hp,true,ha,s⟩⟩
  · obtain ⟨s⟩:=exists_fixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 false)
    exact ⟨⟨a0,c0,hc0,hdiv,hcop,hp,false,hc',s⟩⟩


def fixedFourierGeometry (c:Eis) (hc:c≠0) (h:Eis⧸Ideal.span {c}) :
    FixedFourierGeometry c h := Classical.choice (exists_fixedFourierGeometry c hc h)

namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)

abbrev PhaseResidue := Eis⧸Ideal.span {traceLambda^3*G.c0}

instance phaseResidue_finite : Finite G.PhaseResidue :=
  (Ideal.span {traceLambda^3*G.c0}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (cuspBadModulus_ne_zero G.c0 G.denominator_ne_zero))

def levelScale : ℝ := fixedCuspLevelScale G.shape.index G.c0

lemma levelScale_pos : 0<G.levelScale :=
  fixedCuspLevelScale_pos G.shape.index G.c0 G.denominator_ne_zero

lemma levelScale_le (hc:c≠0) : G.levelScale≤fixedCuspLevelBound c :=
  fixedCuspLevelScale_le G.shape.index G.c0 c hc G.denominator_dvd

def dualNumerator (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  sourceCuspPhaseNumerator G.shape.index (G.shape.upper 0 0)
    (fixedCuspArrayIndex u m I J)

def staticPhase (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  G.shape.reflectionStaticPhase G.c0 G.denominator_ne_zero v (G.dualNumerator u) u m I J

lemma staticPhase_norm_le_one (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖G.staticPhase v u m I J‖≤1 :=
  G.shape.reflectionStaticPhase_norm_le_one G.c0 G.denominator_ne_zero v _ u m I J

def array (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase G.shape.index u (G.staticPhase v u) m I J

lemma array_norm_le_one (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖G.array v u m I J‖≤1 :=
  fixedCuspArrayWithPhase_norm_le_one G.shape.index u _ (G.staticPhase_norm_le_one v u) m I J

lemma array_eq (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    G.array v u m I J=G.shape.amplitude u m I J*
      cuspResiduePhase G.c0 G.denominator_ne_zero v (G.dualNumerator u m I J) :=
  G.shape.fixedCuspArrayWithPhase_reflectionStaticPhase G.c0 G.denominator_ne_zero v _ u m I J

end FixedFourierGeometry

def FixedReflectionRay (c:Eis) (hc:c≠0) :=
  Σh:Eis⧸Ideal.span {c},(fixedFourierGeometry c hc h).PhaseResidue×Eisˣ

instance fixedReflectionRay_finite (c:Eis) (hc:c≠0) : Finite (FixedReflectionRay c hc) := by
  let:Finite (Eis⧸Ideal.span {c}):=(Ideal.span {c}).finiteQuotientOfFreeOfNeBot (Ideal.span_singleton_eq_bot.not.mpr hc)
  let:Finite Eisˣ:=cubic_units_finite
  unfold FixedReflectionRay
  infer_instance

noncomputable instance fixedReflectionRay_fintype (c:Eis) (hc:c≠0) :
    Fintype (FixedReflectionRay c hc) := Fintype.ofFinite _

def fixedReflectionRayCount (c:Eis) (hc:c≠0) : ℕ := Fintype.card (FixedReflectionRay c hc)

def fixedReflectionRayEquiv (c:Eis) (hc:c≠0) :
    FixedReflectionRay c hc≃Fin (fixedReflectionRayCount c hc) := Fintype.equivFin _

lemma fixedReflectionRayCount_subpower (c:Eis) (hc:c≠0) (z:ℂ) (κ:ℝ) (hκ:0≤κ) :
    ∃C:ℝ,0≤C ∧ ∀Z:ℝ,1≤Z→
      (fixedReflectionRayCount c hc:ℝ)^2*‖z‖^2≤C*Z^κ := by
  refine ⟨(fixedReflectionRayCount c hc:ℝ)^2*‖z‖^2,by positivity,?_⟩
  intro Z hZ
  have hz:1≤Z^κ:=Real.one_le_rpow hZ hκ
  exact le_mul_of_one_le_right (by positivity) hz

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CompletedDyadic NormalizedReflection FirstPassCubeLabels
open scoped BigOperators Classical MatrixGroups Matrix ContDiff
local notation "Eis" => Eisenstein.O
section
variable {R:Type*} [CommRing R]
theorem inverse_residue_congr (D r r0 u u0 : R) (hcop : IsCoprime D r)
    (hr : D∣r-r0) (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) : D∣u-u0 := by
  apply hcop.dvd_of_dvd_mul_right
  have hh := dvd_sub (dvd_sub hu hu0) (dvd_mul_of_dvd_right hr u0)
  convert hh using 1 ; ring

theorem inverse_weight_residue_congr (D r r0 u u0 d d0 : R)
    (hcop : IsCoprime D r) (hr : D∣r-r0)
    (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) (hd : D∣d-d0) :
    D∣(-d*u)-(-d0*u0) := by
  have hi := inverse_residue_congr D r r0 u u0 hcop hr hu hu0
  have hh := dvd_add (dvd_mul_of_dvd_left hd u) (dvd_mul_of_dvd_right hi d0)
  convert dvd_neg.mpr hh using 1 ; ring


end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
