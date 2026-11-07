/-
Cubic Eisenstein Fourier coefficients adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisensteinFourierInterchange
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicCuspFourierKernels
import Mathlib.Algebra.Module.ZLattice.Summable

/-!
# Arithmetic Fourier coefficients of the cubic Eisenstein series

Unfold each primitive row over the actual cusp lattice. Summing the
finite residue classes gives the scattering Dirichlet series, absolutely
convergent for `Re s > 2`. The zero Fourier mode is the incoming height
power plus the explicit radial integral times the scattering coefficient.
-/
noncomputable section
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal

open Eisenstein CubicKubota CubicJacobi

def primitiveRowIntegral (v : ℝ) (s freq : ℂ) (c d : O) : ℂ :=
  ∫ z in periodDomain,primitiveTerm z v s c d*tracePhase (-freq*z)

lemma integral_summand_eq_primitiveRowIntegral (v : ℝ) (hv : 0 < v)
    (s freq : ℂ) (x : CuspCosets) :
    (∫ z in periodDomain,summand (upperSection z v hv) s x*tracePhase (-freq*z))=
      primitiveRowIntegral v s freq (cosetRow x 0) (cosetRow x 1) := by
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [summand_upperSection,inverse_cosetCharacter_eq_row_symbol]
    rfl

lemma hasSum_primitiveRowIntegrals (v : ℝ) (hv : 0 < v) (s freq : ℂ) (hs : 2 < s.re) :
    HasSum (fun p : Σ c : LevelLower,AdmissibleDenominator c.1 =>
      primitiveRowIntegral v s freq p.1.1 p.2.1)
      (∫ z in periodDomain,upperEisenstein z v hv s*tracePhase (-freq*z)) := by
  apply primitiveSigmaEquiv.hasSum_iff.mp
  apply primitiveRowEquiv.hasSum_iff.mp
  exact (hasSum_integral_upperEisenstein v hv s freq hs).congr_fun
    fun x => (integral_summand_eq_primitiveRowIntegral v hv s freq x).symm

lemma primitiveRowIntegral_sum_translate (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (h c d : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) (hd : (3:O) ∣ d-1) :
    (∑' n : O,primitiveRowIntegral v s (cuspFrequency h) c (d+3*c*n))=
      ∫ z : ℂ,primitiveTerm z v s c d*tracePhase (-cuspFrequency h*z) := by
  have hint := trace_mul_integrable (fun z => primitiveTerm z v s c d)
    (primitiveTerm_integrable v hv s hs c d hc) (cuspFrequency h)
  rw [integral_eq_period_integrals _ hint]
  apply tsum_congr
  intro n
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [primitiveTerm_shift z v s c d n hlevel hd,cuspFrequency_negative_period]

lemma primitiveTerm_fourier_integral (v : ℝ) (hv : 0 < v) (s freq : ℂ)
    (c d : O) (hc : c ≠ 0) :
    (∫ z : ℂ,primitiveTerm z v s c d*tracePhase (-freq*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (freq*v))*
        ((‖ringComplex c‖^2:ℝ):ℂ)^(-s)*
        (ringComplex (symbol c d)*tracePhase (freq*ringComplex d/ringComplex c)) := by
  simp_rw [primitiveTerm_eq_shiftedHeightKernel _ v hv s c d hc,mul_assoc]
  rw [integral_const_mul,integral_const_mul,traceIntegral_shiftedHeightKernel v hv s (ringComplex d/ringComplex c) freq]
  ring_nf

def arithmeticResidueSum (h c : O) : ℂ :=
  ∑' r : AdmissibleResidue c,ringComplex (symbol c (denominatorRep c r.1))*
    tracePhase (cuspFrequency h*ringComplex (denominatorRep c r.1)/ringComplex c)

lemma arithmeticResidueSum_finite (h c : O) (hc : c ≠ 0) :
    letI : Fintype (AdmissibleResidue c) := @Fintype.ofFinite _ (finite_admissibleResidue c hc)
    arithmeticResidueSum h c = ∑ r : AdmissibleResidue c,
      ringComplex (symbol c (denominatorRep c r.1))*
      tracePhase (cuspFrequency h*ringComplex (denominatorRep c r.1)/ringComplex c) := by
  let : Fintype (AdmissibleResidue c) := @Fintype.ofFinite _ (finite_admissibleResidue c hc)
  exact tsum_fintype _

lemma denominator_integral_formula (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re)
    (h : O) (c : LevelLower) (hc : c.1 ≠ 0) :
    (∑' d : AdmissibleDenominator c.1,primitiveRowIntegral v s (cuspFrequency h) c.1 d.1)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        ((‖ringComplex c.1‖^2:ℝ):ℂ)^(-s)*arithmeticResidueSum h c.1 := by
  have hsum : Summable (fun d : AdmissibleDenominator c.1 =>
      primitiveRowIntegral v s (cuspFrequency h) c.1 d.1) :=
    (hasSum_primitiveRowIntegrals v hv s (cuspFrequency h) hs).summable.sigma_factor c
  rw [denominator_sum_residues c.1 hc
    (fun d : O => primitiveRowIntegral v s (cuspFrequency h) c.1 d) hsum]
  calc
    _ = ∑' r : AdmissibleResidue c.1, ∫ z : ℂ,
        primitiveTerm z v s c.1 (denominatorRep c.1 r.1)*
          tracePhase (-cuspFrequency h*z) := by
      apply tsum_congr
      intro r
      exact primitiveRowIntegral_sum_translate v hv s (by linarith) h c.1
        (denominatorRep c.1 r.1) hc c.2 r.2.2
    _ = _ := by
      simp_rw [primitiveTerm_fourier_integral v hv s (cuspFrequency h) c.1 _ hc]
      exact tsum_mul_left

end

section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal Matrix

open Eisenstein CubicKubota CubicJacobi

instance cubicPeriodLatticeDiscrete : DiscreteTopology periodLattice := by unfold periodLattice; infer_instance
instance cubicPeriodLatticeIsZLattice : IsZLattice ℝ periodLattice := by unfold periodLattice; infer_instance

lemma summable_embedding_rpow (k : ℝ) (hk : k < -2) :
    Summable (fun n : O => ‖ringComplex n‖^k) := by
  have hrank : Module.finrank ℤ periodLattice=2 := by
    rw [ZLattice.rank ℝ periodLattice,Complex.finrank_real_complex]
  have hs := ZLattice.summable_norm_rpow periodLattice k (by rw [hrank]; norm_num; exact hk)
  have hcomp := periodEquiv.summable_iff.mpr hs
  have hscale := hcomp.mul_left (((3:ℝ)^k)⁻¹)
  apply hscale.congr
  intro n
  change ((3:ℝ)^k)⁻¹*‖(3:ℂ)*ringComplex n‖^k=‖ringComplex n‖^k
  rw [norm_mul,show ‖(3:ℂ)‖=(3:ℝ) by norm_num,
    Real.mul_rpow (by norm_num) (norm_nonneg _)]
  rw [← mul_assoc,inv_mul_cancel₀ (Real.rpow_pos_of_pos (by norm_num) k).ne',one_mul]

lemma norm_row_symbol (c d : O) (hc : (3:O) ∣ c) (hd : denominatorCondition c d) :
    ‖ringComplex (symbol c d)‖=1 := by
  let r : PrimitiveRow := ⟨![c,d],hd.1,hc,hd.2⟩
  let x := primitiveRowEquiv.symm r
  have heq : (cosetCharacter x)⁻¹=ringComplex (symbol c d) := by
    rw [inverse_cosetCharacter_eq_row_symbol]
    change ringComplex (symbol (cosetRow (primitiveRowEquiv.symm r) 0)
      (cosetRow (primitiveRowEquiv.symm r) 1))=ringComplex (symbol c d)
    rw [primitiveRowEquiv_symm_row r]
    rfl
  rw [← heq,norm_inv,norm_cosetCharacter,inv_one]

/-- Complex squared modulus is the absolute norm of the principal ideal. -/
lemma ringComplex_norm_sq_eq_absNorm_span (n : O) :
    ‖ringComplex n‖^2 = (Ideal.absNorm (Ideal.span {n}) : ℝ) := by
  have hn : (Algebra.norm ℤ n : ℝ) = ‖ringComplex n‖^2 := by
    rw [←Coordinates.eval_coords n,Coordinates.norm_eval,Coordinates.complex_norm_eval_sq]
    simp only [Int.cast_add,Int.cast_sub,Int.cast_pow,Int.cast_mul]
  rw [Ideal.absNorm_span_singleton,Nat.cast_natAbs,Int.cast_abs,hn,
    abs_of_nonneg (sq_nonneg _)]

lemma norm_arithmeticResidueSum_le (h c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) :
    ‖arithmeticResidueSum h c‖ ≤ 9*‖ringComplex c‖^2 := by
  let : Finite (DenominatorResidue c) := (Ideal.span {3*c}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (by norm_num) hc))
  let : Fintype (DenominatorResidue c) := Fintype.ofFinite _
  let : Fintype (AdmissibleResidue c) := Fintype.ofFinite _
  have hcard : (Fintype.card (DenominatorResidue c):ℝ)=9*‖ringComplex c‖^2 := by
    have hh := ringComplex_norm_sq_eq_absNorm_span (3*c)
    simp only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] at hh
    rw [← hh,map_mul,map_ofNat,norm_mul,mul_pow]
    norm_num
  rw [arithmeticResidueSum,tsum_fintype]
  calc
    _ ≤ ∑ r : AdmissibleResidue c, ‖ringComplex (symbol c (denominatorRep c r.1))*
        tracePhase (cuspFrequency h*ringComplex (denominatorRep c r.1)/ringComplex c)‖ :=
      norm_sum_le _ _
    _ = (Fintype.card (AdmissibleResidue c):ℝ) := by
      have hr (r : AdmissibleResidue c) :
          ‖ringComplex (symbol c (denominatorRep c r.1))‖=1 :=
        norm_row_symbol c (denominatorRep c r.1) hlevel r.2
      simp only [norm_mul,hr,tracePhase_norm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    _ ≤ (Fintype.card (DenominatorResidue c):ℝ) := by
      exact_mod_cast Fintype.card_subtype_le (fun r => denominatorCondition c (denominatorRep c r))
    _ = _ := hcard

def arithmeticDirichletTerm (s : ℂ) (h : O) (c : LevelLower) : ℂ :=
  if c.1=0 then 0 else ((‖ringComplex c.1‖^2:ℝ):ℂ)^(-s)*arithmeticResidueSum h c.1

lemma norm_arithmeticDirichletTerm_le (s : ℂ) (h : O) (c : LevelLower) :
    ‖arithmeticDirichletTerm s h c‖ ≤ 9*‖ringComplex c.1‖^(2-2*s.re) := by
  unfold arithmeticDirichletTerm
  split_ifs with hc
  · simp only [norm_zero]
    positivity
  · have hn : 0 < ‖ringComplex c.1‖ := norm_pos_iff.mpr (ringComplex_ne_zero hc)
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn)]
    change (‖ringComplex c.1‖^2)^(-s.re)*‖arithmeticResidueSum h c.1‖ ≤ _
    calc
      _ ≤ (‖ringComplex c.1‖^2)^(-s.re)*(9*‖ringComplex c.1‖^2) :=
        mul_le_mul_of_nonneg_left (norm_arithmeticResidueSum_le h c.1 hc c.2) (by positivity)
      _ = _ := by
        rw [← Real.rpow_natCast_mul hn.le 2 (-s.re)]
        rw [show 2-2*s.re=2+2*(-s.re) by ring,Real.rpow_add hn]
        norm_num only [Nat.cast_ofNat,Real.rpow_two]
        ring

theorem arithmeticDirichletTerm_summable_norm (s : ℂ) (hs : 2 < s.re) (h : O) :
    Summable (fun c : LevelLower => ‖arithmeticDirichletTerm s h c‖) := by
  have hbase := (summable_embedding_rpow (2-2*s.re) (by linarith)).subtype
    (fun c : O => (3:O) ∣ c)
  exact (hbase.mul_left 9).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_arithmeticDirichletTerm_le s h)

def arithmeticDirichletSeries (s : ℂ) (h : O) : ℂ :=
  ∑' c : LevelLower,arithmeticDirichletTerm s h c

def scatteringCoefficient (s : ℂ) (h : O) : ℂ :=
  arithmeticDirichletSeries s h/((9*Real.sqrt 3/2:ℝ):ℂ)

end

open MeasureTheory Set Filter
open scoped BigOperators Classical

open Eisenstein CubicKubota CubicJacobi

lemma zero_lower_integral (v : ℝ) (s : ℂ) (h : O) :
    (∑' d : AdmissibleDenominator 0,primitiveRowIntegral v s (cuspFrequency h) 0 d.1)=
      (v:ℂ)^s*(if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0) := by
  let d0 : AdmissibleDenominator 0 := ⟨1,isCoprime_one_right,by simp⟩
  rw [tsum_eq_single d0]
  · simp only [d0,primitiveRowIntegral,primitiveTerm,map_zero,map_one,zero_mul,zero_add,
      norm_one,norm_zero,one_pow,zero_pow (by decide : (2:ℕ) ≠ 0),add_zero,
      div_one,symbol_one,map_one]
    rw [integral_const_mul,integral_cusp_character,one_mul]
  · intro d hd
    exact False.elim (hd (Subtype.ext (denominator_zero_unique d)))

lemma integral_upperEisenstein_arithmetic (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) (h : O) :
    (∫ z in periodDomain,upperEisenstein z v hv s*tracePhase (-cuspFrequency h*z))=
      (v:ℂ)^s*(if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0)+
        ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*arithmeticDirichletSeries s h := by
  let c0 : LevelLower := ⟨0,dvd_zero _⟩
  let F (c : LevelLower) := ∑' d : AdmissibleDenominator c.1,
    primitiveRowIntegral v s (cuspFrequency h) c.1 d.1
  have hsum := hasSum_primitiveRowIntegrals v hv s (cuspFrequency h) hs
  have hF : Summable F := hsum.summable.sigma
  have hzero : F c0=(v:ℂ)^s*(if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0) :=
    zero_lower_integral v s h
  calc
    _ = ∑' c : LevelLower,F c := hsum.tsum_eq.symm.trans hsum.summable.tsum_sigma
    _ = F c0+∑' c : LevelLower,if c=c0 then 0 else F c := hF.tsum_eq_add_tsum_ite c0
    _ = _ := by
      rw [hzero]
      congr 1
      rw [arithmeticDirichletSeries,← tsum_mul_left]
      apply tsum_congr
      intro c
      by_cases hc : c.1=0
      · have heq : c=c0 := Subtype.ext hc
        simp only [heq,ite_true,arithmeticDirichletTerm,c0,mul_zero]
      · have heq : c ≠ c0 := fun heq => hc (congrArg Subtype.val heq)
        rw [if_neg heq]
        change (∑' d : AdmissibleDenominator c.1,
          primitiveRowIntegral v s (cuspFrequency h) c.1 d.1)=_
        rw [denominator_integral_formula v hv s hs h c hc]
        simp only [arithmeticDirichletTerm,if_neg hc]
        ring

def eisensteinFourierCoefficient (v : ℝ) (hv : 0 < v) (s : ℂ) (h : O) : ℂ :=
  (∫ z in periodDomain,upperEisenstein z v hv s*tracePhase (-cuspFrequency h*z))/
    ((9*Real.sqrt 3/2:ℝ):ℂ)

theorem eisensteinFourierCoefficient_formula (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) (h : O) :
    eisensteinFourierCoefficient v hv s h=(if h=0 then (v:ℂ)^s else 0)+
      (v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*scatteringCoefficient s h := by
  rw [eisensteinFourierCoefficient,integral_upperEisenstein_arithmetic v hv s hs h,scatteringCoefficient]
  have hvol : ((9*Real.sqrt 3/2:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  split_ifs <;> field_simp ; ring

theorem eisensteinConstantCoefficient_formula (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    eisensteinFourierCoefficient v hv s 0=(v:ℂ)^s+
      (v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0 := by
  rw [eisensteinFourierCoefficient_formula v hv s hs 0]
  simp only [ite_true,cuspFrequency,map_zero,zero_div,zero_mul]
  rw [sourceFourierKernel_zero s (by linarith)]


#print axioms ringComplex_norm_sq_eq_absNorm_span
#print axioms arithmeticDirichletTerm_summable_norm
#print axioms eisensteinFourierCoefficient_formula
#print axioms eisensteinConstantCoefficient_formula
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
