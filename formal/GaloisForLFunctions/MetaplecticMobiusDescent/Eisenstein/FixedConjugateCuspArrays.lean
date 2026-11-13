/-
Fixed conjugate cusp arrays adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.GaussSums.RayExpansionsAndCompletedSums

/-!
# Fixed conjugate cusp arrays

Base ray twists `CanonicalCoefficientClass.IsBaseRayTwist`: coefficients differ from a fixed
monoid character by a character modulo four. Fixed conjugate cusp arrays with one bound for
all three families; unit cubic symbols are trivial on the lattice of modulus `3λ`.
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

namespace CanonicalCoefficientClass
open Eisenstein SchwartzPlanePoisson RayFourExpansion
open scoped Classical

/-- Coefficients differ from a fixed monoid character by a character modulo four. -/
def IsBaseRayTwist (base Ψ:O→*ℂ):Prop:=
  Ψ=base ∨ ∃χ:RayCharacter,Ψ=rayMonoid χ*base

def baseRayOrbit (base:O→*ℂ):Finset (O→*ℂ):=
  insert base (Finset.univ.image (fun χ:RayCharacter=>rayMonoid χ*base))

lemma mem_baseRayOrbit (base Ψ:O→*ℂ):Ψ∈baseRayOrbit base ↔ IsBaseRayTwist base Ψ:=by
  simp only [baseRayOrbit,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and,IsBaseRayTwist]
  constructor
  · rintro (h|⟨χ,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨χ,h.symm⟩
  · rintro (h|⟨χ,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨χ,h.symm⟩

lemma baseRayOrbit_card (base:O→*ℂ):
    (baseRayOrbit base).card≤1+Fintype.card RayCharacter:=by
  have hi:=Finset.card_insert_le base (Finset.univ.image (fun χ:RayCharacter=>rayMonoid χ*base))
  have hm:=Finset.card_image_le (s:=(Finset.univ:Finset RayCharacter))
    (f:=fun χ:RayCharacter=>rayMonoid χ*base)
  simp only [Finset.card_univ] at hm
  unfold baseRayOrbit
  omega

lemma rayMonoid_mul (χ η:RayCharacter):rayMonoid (χ*η)=rayMonoid χ*rayMonoid η:=by
  ext x
  simp only [rayMonoid_apply,MulChar.mul_apply,MonoidHom.mul_apply]

lemma IsBaseRayTwist.mul_ray {base Ψ:O→*ℂ} (hΨ:IsBaseRayTwist base Ψ) (χ:RayCharacter):
    IsBaseRayTwist base (rayMonoid χ*Ψ):=by
  rcases hΨ with h|⟨η,h⟩
  · exact Or.inr ⟨χ,by rw [h]⟩
  · exact Or.inr ⟨χ*η,by rw [h,rayMonoid_mul,mul_assoc]⟩

lemma IsBaseRayTwist.mul_ray_right {base Ψ:O→*ℂ} (hΨ:IsBaseRayTwist base Ψ) (χ:RayCharacter):
    IsBaseRayTwist base (Ψ*rayMonoid χ):=by
  rw [mul_comm]
  exact hΨ.mul_ray χ

lemma IsBaseRayTwist.norm_le {base Ψ:O→*ℂ} (hΨ:IsBaseRayTwist base Ψ)
    (hbase:∀x,‖base x‖≤1) (x:O):‖Ψ x‖≤1:=by
  rcases hΨ with rfl|⟨χ,rfl⟩
  · exact hbase x
  · rw [MonoidHom.mul_apply,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (rayMonoid_norm_le χ x)).trans (hbase x)

end CanonicalCoefficientClass

open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss
open scoped BigOperators Classical
local notation "Eis" => Eisenstein.O
/-- One positive bound for all three cusp coefficient families. -/
def fixedCuspCoefficientBound : ℝ :=
  1 + ∑ j : Fin 3, sourceCuspCoefficientBaseBound j

lemma fixedCuspCoefficientBound_pos : 0 < fixedCuspCoefficientBound := by
  have hs := Finset.sum_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => sourceCuspCoefficientBaseBound_nonneg j)
  exact add_pos_of_pos_of_nonneg zero_lt_one hs

def fixedCuspArrayIndex (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  (u.val*lambda^m)*primaryIdealGenerator I*(primaryIdealGenerator J)^3

def fixedCuspArrayEligible (I J:Ideal Eis) : Prop :=
  Squarefree I ∧ primaryIdealGenerator I≠0 ∧ primaryIdealGenerator J≠0

def fixedCuspArrayWeight (m:ℕ) (J:Ideal Eis) : ℝ :=
  (3:ℝ)^((m:ℝ)/6)*Real.sqrt (Ideal.absNorm J:ℝ)

lemma fixedCuspArrayWeight_nonneg (m:ℕ) (J:Ideal Eis) :
    0≤fixedCuspArrayWeight m J := by
  unfold fixedCuspArrayWeight
  positivity

lemma fixedCuspArrayWeight_pos (m:ℕ) (J:Ideal Eis) (hJ:primaryIdealGenerator J≠0) :
    0<fixedCuspArrayWeight m J := by
  rw [fixedCuspArrayWeight,←primaryIdealGenerator_norm J hJ]
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (norm_pos_iff.mpr (ringComplex_ne_zero hJ))

lemma sourceCuspCoefficients_squarefree_cube_bound (j:Fin 3) (u:Eisˣ) (m:ℕ)
    (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J) :
    ‖sourceCuspCoefficient j (fixedCuspArrayIndex u m I J)‖≤
      fixedCuspCoefficientBound*fixedCuspArrayWeight m J := by
  rcases helig with ⟨hsq,hI,hJ⟩
  have hb := sourceCuspCoefficient_full_bound j (u,m,(⟨I,hsq,hI⟩,⟨J,hJ⟩))
  have hc : sourceCuspCoefficientBaseBound j ≤ fixedCuspCoefficientBound := by
    apply (Finset.single_le_sum (s := Finset.univ)
      (fun i _ => sourceCuspCoefficientBaseBound_nonneg i) (Finset.mem_univ j)).trans
    exact le_add_of_nonneg_left zero_le_one
  have hr : ‖ringComplex ((u:Eis)*lambda^m)‖^(1/3:ℝ) = (3:ℝ)^((m:ℝ)/6) := by
    rw [ramified_unit_norm,←Real.rpow_mul (by norm_num)]
    congr 1
    ring
  change ‖sourceCuspCoefficient j (fixedCuspArrayIndex u m I J)‖ ≤ _ at hb
  rw [hr,primaryIdealGenerator_norm J hJ] at hb
  exact hb.trans (by
    dsimp only [fixedCuspArrayWeight]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)))


def fixedCuspArray (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  if fixedCuspArrayEligible I J then
    sourceCuspCoefficient j (fixedCuspArrayIndex u m I J) /
      ((fixedCuspCoefficientBound*fixedCuspArrayWeight m J:ℝ):ℂ)
  else 0

lemma fixedCuspArray_zero_of_ineligible (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:¬fixedCuspArrayEligible I J) : fixedCuspArray j u m I J=0 := by
  simp only [fixedCuspArray,if_neg h]

lemma fixedCuspArray_norm_le_one (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖fixedCuspArray j u m I J‖≤1 := by
  by_cases h:fixedCuspArrayEligible I J
  · have hpos:=mul_pos fixedCuspCoefficientBound_pos (fixedCuspArrayWeight_pos m J h.2.2)
    rw [fixedCuspArray,if_pos h,norm_div,Complex.norm_real,Real.norm_of_nonneg hpos.le]
    exact (div_le_one hpos).mpr (sourceCuspCoefficients_squarefree_cube_bound j u m I J h)
  · simp only [fixedCuspArray,if_neg h,norm_zero,zero_le_one]

lemma fixedCuspArray_reconstruct (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayEligible I J) :
    sourceCuspCoefficient j (fixedCuspArrayIndex u m I J)=
      ((fixedCuspCoefficientBound*fixedCuspArrayWeight m J:ℝ):ℂ)*fixedCuspArray j u m I J := by
  have hpos:=mul_pos fixedCuspCoefficientBound_pos (fixedCuspArrayWeight_pos m J h.2.2)
  rw [fixedCuspArray,if_pos h,mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hpos.ne')]

def fixedConjugateCuspArray (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  star (fixedCuspArray j u m I J)

lemma fixedConjugateCuspArray_norm_le_one (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖fixedConjugateCuspArray j u m I J‖≤1 := by
  simpa only [fixedConjugateCuspArray,norm_star] using fixedCuspArray_norm_le_one j u m I J

lemma fixedConjugateCuspArray_reconstruct (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayEligible I J) :
    star (sourceCuspCoefficient j (fixedCuspArrayIndex u m I J))=
      ((fixedCuspCoefficientBound*fixedCuspArrayWeight m J:ℝ):ℂ)*fixedConjugateCuspArray j u m I J := by
  rw [fixedCuspArray_reconstruct j u m I J h,star_mul]
  simp only [fixedConjugateCuspArray,Complex.star_def,Complex.conj_ofReal]
  ring

lemma fixedConjugateCuspArray_reconstruct_explicit (j:Fin 3) (u:Eisˣ) (m:ℕ)
    (I J:Ideal Eis) (hsq:Squarefree I) (hI:primaryIdealGenerator I≠0) (hJ:primaryIdealGenerator J≠0) :
    star (sourceCuspCoefficient j
      ((u.val*lambda^m)*primaryIdealGenerator I*(primaryIdealGenerator J)^3))=
      ((fixedCuspCoefficientBound*(3:ℝ)^((m:ℝ)/6)*Real.sqrt (Ideal.absNorm J:ℝ):ℝ):ℂ)*
        fixedConjugateCuspArray j u m I J := by
  simpa only [fixedCuspArrayIndex,fixedCuspArrayWeight,mul_assoc] using
    fixedConjugateCuspArray_reconstruct j u m I J ⟨hsq,hI,hJ⟩

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein Eisenstein.Coordinates
open scoped BigOperators Classical
local notation "Eis" => Eisenstein.O

/-- Unit cubic symbols are trivial on the affine lattice of modulus `3λ`. -/
lemma unit_symbol_lambda_affine (u : Eisˣ) (x : Eis) :
    symbol (u:Eis) (1+3*(lambda*x)) = 1 := by
  obtain ⟨a,b,hx⟩ := exists_coordinates x
  have hp : lambda^2 ∣ (1+3*(lambda*x))-1 :=
    lambda_sq_dvd_three.trans ⟨lambda*x,by ring⟩
  have harg : 1+3*(lambda*x) = primaryCoord (-a-b) (a-2*b) := by
    rw [hx,primaryCoord_eq,lambda]
    push_cast
    linear_combination 3*(b:Eis)*cusp_omega_relation
  have ho : symbol omega (1+3*(lambda*x)) = 1 := by
    rw [symbol_omega_eq_linearRay _ hp,harg,linearRay_primaryCoord]
    simpa only [neg_one_mul,sub_eq_add_neg] using
      (cubicExp_eq_of_dvd_sub (show (3:ℤ) ∣ (2*(-a-b)-(a-2*b))-0
        from ⟨-a,by ring⟩)).trans cubicExp_zero
  obtain ⟨j,hj|hj⟩ := unit_eq_sign_omega u
  · rw [hj,symbol_pow_numerator _ _ hp,ho,one_pow]
  · rw [hj,symbol_neg_numerator _ _ hp,symbol_pow_numerator _ _ hp,ho,one_pow]

/-- The finite Fourier frequency of a unit symbol is divisible by the ramified prime. -/
lemma ramifiedArithmeticPhase_unit_dvd (u : Eisˣ) :
    lambda ∣ ramifiedArithmeticPhase u 0 := by
  let r := ramifiedArithmeticPhase u 0
  have he : residueTraceQuotientChar (r*lambda) 3 (by norm_num) = 1 := by
    ext z
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [residueTraceQuotientChar_three_phase,AddChar.one_apply]
    have hh := ramifiedArithmeticPhase_spec u 0 (lambda*x)
    simp only [pow_zero,mul_one,unit_symbol_lambda_affine,map_one] at hh
    convert hh.symm using 1 <;> simp only [cuspFrequency,map_mul] <;> congr 1 <;> ring
  have hz : Ideal.Quotient.mk (Ideal.span {(3:Eis)}) (r*lambda) = 0 := by
    apply AddChar.to_mulShift_inj_of_isPrimitive (residueTraceQuotientChar_primitive 3 (by norm_num))
    rw [←residueTraceQuotientChar_mulShift,AddChar.mulShift_zero]
    exact he
  have hd : lambda^2 ∣ r*lambda := lambda_sq_dvd_three.trans
    (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  obtain ⟨k,hk⟩ := hd
  refine ⟨k,?_⟩
  apply mul_right_cancel₀ residue_lambda_prime.ne_zero
  change r*lambda=(lambda*k)*lambda
  rw [hk]
  ring

lemma scaledAffineGaussWeight_unit_zero (q : Eis) (u : Eisˣ) (h : Eis) (s : ℂ)
    (hh : ¬lambda∣h) : scaledAffineGaussWeight q u 0 h s = 0 := by
  unfold scaledAffineGaussWeight
  split_ifs with hq hfreq
  · exfalso
    have h3 : lambda∣(3:Eis) :=
      (dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three
    have hk : lambda∣hq.choose := by
      convert dvd_sub (h3.trans hfreq) (ramifiedArithmeticPhase_unit_dvd u) using 1 <;> ring
    apply hh
    rw [hq.choose_spec]
    exact dvd_mul_of_dvd_right hk q
  · rfl
  · rfl

lemma ramifiedSixWeight_zero_of_not_lambda_dvd (u t : Eisˣ) (h : Eis) (i : RamifiedSixBranch)
    (s : ℂ) (hh : ¬lambda∣h) : ramifiedSixWeight u t h i s = 0 := by
  rcases i with i|i
  · simp only [ramifiedSixWeight,scaledAffineGaussWeight_unit_zero _ _ _ _ hh,mul_zero]
  rcases i with i|i
  · simp only [ramifiedSixWeight,scaledAffineGaussWeight_unit_zero _ _ _ _ hh,mul_zero]
  rcases i with i|j
  · simp only [ramifiedSixWeight,scaledAffineGaussWeight_unit_zero _ _ _ _ hh,mul_zero]
  · have hq : ¬onceCuspScale t*omega^j.val∣h := by
      intro hd
      apply hh
      apply (dvd_mul_of_dvd_left (show lambda∣onceCuspScale t from ?_) _).trans hd
      rw [onceCuspScale,traceLambda_eq_unit_mul_lambda]
      exact dvd_mul_of_dvd_right (dvd_mul_left lambda (-omega)) _
    simp only [ramifiedSixWeight,scaledAffineGaussWeight,dif_neg hq,mul_zero]

lemma ramifiedResidualFourierCoefficient_lambda_dvd (u t : Eisˣ) (h : Eis)
    (hh : ramifiedResidualFourierCoefficient u t h≠0) : lambda∣h := by
  by_contra hn
  have hz : ramifiedArithmeticResidue u t h=0 := by
    unfold ramifiedArithmeticResidue
    apply Finset.sum_eq_zero
    intro i hi
    rw [ramifiedSixWeight_zero_of_not_lambda_dvd _ _ _ _ _ hn,zero_mul]
  exact hh (by simp only [ramifiedResidualFourierCoefficient,hz,mul_zero,zero_div,zero_mul])

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss
open scoped BigOperators Classical MatrixGroups
local notation "Eis" => Eisenstein.O
def traceLambdaUnit : Eisˣ := -cuspOmegaUnit

lemma traceLambda_unit_mul : traceLambda = (traceLambdaUnit:Eis)*lambda := by
  simpa only [traceLambdaUnit,Units.val_neg,cuspOmegaUnit_val] using traceLambda_eq_unit_mul_lambda

lemma traceLambda_dvd_of_lambda_dvd (h:Eis) (hh:lambda∣h) :
    traceLambda∣h := by
  obtain ⟨q,hq⟩:=hh
  refine ⟨(traceLambdaUnit⁻¹:Eisˣ)*q,?_⟩
  change h=traceLambda*((traceLambdaUnit⁻¹:Eisˣ)*q)
  rw [traceLambda_unit_mul,hq]
  have hu : (traceLambdaUnit:Eis)*(traceLambdaUnit⁻¹:Eisˣ)=1 := by
    simpa only [Units.val_mul,Units.val_one] using
      congrArg (fun v:Eisˣ=>(v:Eis)) (mul_inv_cancel traceLambdaUnit)
  calc
    _=(traceLambdaUnit:Eis)*(traceLambdaUnit⁻¹:Eisˣ)*(lambda*q) := by rw [hu,one_mul]
    _=_ := by ring

def traceLambdaQuotient (h:Eis) : Eis :=
  if hh:traceLambda∣h then hh.choose else 0

lemma traceLambdaQuotient_mul (h:Eis) (hh:traceLambda∣h) :
    traceLambda*traceLambdaQuotient h=h := by
  simp only [traceLambdaQuotient,dif_pos hh]
  exact hh.choose_spec.symm

lemma sourceCuspCoefficients_ramified_divisibility (j:Fin 3) (hj:j≠0) (h:Eis)
    (hh:sourceCuspCoefficient j h≠0) : traceLambda∣h := by
  apply traceLambda_dvd_of_lambda_dvd
  fin_cases j
  · exact (hj rfl).elim
  · exact ramifiedResidualFourierCoefficient_lambda_dvd _ _ h hh
  · exact ramifiedResidualFourierCoefficient_lambda_dvd _ _ h hh


def sourceCuspPhaseNumerator (j:Fin 3) (u h:Eis) : Eis :=
  if j=0 then traceLambda*u^2*h else -u^2*traceLambdaQuotient h

lemma traceLambda_complex_square : (ringComplex traceLambda)^2 = (-3:ℂ) := by
  simpa only [map_pow,map_neg,map_ofNat] using congrArg ringComplex traceLambda_square

lemma sourceCuspPhaseNumerator_embedding (j:Fin 3) (u h:Eis)
    (hh:sourceCuspCoefficient j h≠0) :
    ringComplex (sourceCuspPhaseNumerator j u h)=
      -(ringComplex traceLambda)^4*cuspFrequency h*(ringComplex u)^2/(sourceCuspScale j:ℂ) := by
  by_cases hj:j=0
  · subst j
    simp only [sourceCuspPhaseNumerator,ite_true,map_mul,map_pow,
      cuspFrequency,sourceCuspScale]
    norm_num only [Matrix.cons_val_zero,Complex.ofReal_one,div_one]
    rw [show (ringComplex traceLambda)^4=(9:ℂ) from by
      calc
        (ringComplex traceLambda)^4=((ringComplex traceLambda)^2)^2 := by ring
        _=9 := by rw [traceLambda_complex_square]; norm_num]
    field_simp [(ringComplex_ne_zero traceLambda_ne_zero)]
    linear_combination (3*ringComplex h*(ringComplex u)^2)*traceLambda_complex_square
  · have hdiv:=sourceCuspCoefficients_ramified_divisibility j hj h hh
    have hprod:=congrArg ringComplex (traceLambdaQuotient_mul h hdiv)
    have hscale:sourceCuspScale j=3 := by fin_cases j <;> simp_all [sourceCuspScale]
    have hfour:(ringComplex traceLambda)^4=(9:ℂ) := by
      calc
        (ringComplex traceLambda)^4=((ringComplex traceLambda)^2)^2:=by ring
        _=9:=by rw [traceLambda_complex_square];norm_num
    rw [sourceCuspPhaseNumerator,if_neg hj]
    simp only [map_mul,map_neg,map_pow]
    rw [cuspFrequency,hscale,←hprod,map_mul,hfour]
    norm_num only [Complex.ofReal_ofNat]
    field_simp [(ringComplex_ne_zero traceLambda_ne_zero)]
    ; ring

lemma sourceCuspPhaseNumerator_phase (j:Fin 3) (u h c d:Eis) (hc:c≠0)
    (hh:sourceCuspCoefficient j h≠0) :
    tracePhase (cuspFrequency h*(ringComplex u)^2*
      (ringComplex d/ringComplex c)/(sourceCuspScale j:ℂ))=
    tracePhase (-(ringComplex d*
      (ringComplex (sourceCuspPhaseNumerator j u h)/(ringComplex traceLambda)^4))/ringComplex c) := by
  rw [sourceCuspPhaseNumerator_embedding j u h hh]
  congr 1
  field_simp [(ringComplex_ne_zero traceLambda_ne_zero),ringComplex_ne_zero hc,
    Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne']

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
