/-
Cubic Eisenstein residue rows adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.PrimitiveCubicEisensteinRows

/-!
# Residue-class periodization of the cubic Eisenstein series

Split primitive rows by their lower-left entry. For each nonzero entry
`c`, admissible denominators split uniquely as a residue modulo `3c`
plus `3c n`. Denominator congruence preserves the cubic row symbol, so
these fibers become horizontal periodizations of the original summands.
-/
noncomputable section
open scoped BigOperators Classical MatrixGroups Matrix
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota CubicJacobi

def denominatorCondition (c d : O) : Prop := IsCoprime c d ∧ (3 : O) ∣ d-1
abbrev AdmissibleDenominator (c : O) := {d : O // denominatorCondition c d}
abbrev LevelLower := {c : O // (3 : O) ∣ c}

lemma denominatorCondition_shift (c d n : O) :
    denominatorCondition c (d+3*c*n) ↔ denominatorCondition c d := by
  constructor
  · rintro ⟨⟨a,b,h⟩,hd⟩
    refine ⟨⟨a+b*3*n,b,by linear_combination h⟩, ?_⟩
    have h3 : (3 : O) ∣ 3*c*n := ⟨c*n,by ring⟩
    convert dvd_sub hd h3 using 1 ; ring
  · rintro ⟨⟨a,b,h⟩,hd⟩
    refine ⟨⟨a-b*3*n,b,by linear_combination h⟩, ?_⟩
    have h3 : (3 : O) ∣ 3*c*n := ⟨c*n,by ring⟩
    convert dvd_add hd h3 using 1 ; ring

lemma row_symbol_shift (c d n : O) (hc : (3 : O) ∣ c) (hd : (3 : O) ∣ d-1) :
    symbol c (d+3*c*n)=symbol c d := by
  have hdn : (3 : O) ∣ d+3*c*n-1 := by
    convert dvd_add hd (show (3 : O) ∣ 3*c*n from ⟨c*n,by ring⟩) using 1 ; ring
  have h9 : (9 : O) ∣ d+3*c*n-d := by
    obtain ⟨c0,rfl⟩ := hc
    exact ⟨c0*n,by ring⟩
  exact symbol_denominator_congr c (d+3*c*n) d
    (lambda_sq_dvd_three.trans hdn) (lambda_sq_dvd_three.trans hd) h9
    ⟨3*n,by ring⟩

def primitiveSigmaEquiv : PrimitiveRow ≃ Σ c : LevelLower, AdmissibleDenominator c.1 where
  toFun r := ⟨⟨r.1 0,r.2.2.1⟩,⟨r.1 1,r.2.1,r.2.2.2⟩⟩
  invFun p := ⟨![p.1.1,p.2.1],p.2.2.1,p.1.2,p.2.2.2⟩
  left_inv r := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv p := by rfl

abbrev DenominatorResidue (c : O) := O ⧸ Ideal.span {3*c}
def denominatorRep (c : O) (r : DenominatorResidue c) : O :=
  Classical.choose (Ideal.Quotient.mk_surjective r)
lemma denominatorRep_spec (c : O) (r : DenominatorResidue c) :
    Ideal.Quotient.mk (Ideal.span {3*c}) (denominatorRep c r)=r :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective r)
abbrev AdmissibleResidue (c : O) :=
  {r : DenominatorResidue c // denominatorCondition c (denominatorRep c r)}

lemma finite_admissibleResidue (c : O) (hc : c ≠ 0) : Finite (AdmissibleResidue c) := by
  let : Finite (DenominatorResidue c) :=
    (Ideal.span {3*c}).finiteQuotientOfFreeOfNeBot
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (by norm_num) hc))
  infer_instance

def residueDenominatorMap (c : O) (p : AdmissibleResidue c × O) : AdmissibleDenominator c :=
  ⟨denominatorRep c p.1.1+3*c*p.2,(denominatorCondition_shift c _ _).2 p.1.2⟩

lemma residueDenominatorMap_bijective (c : O) (hc : c ≠ 0) :
    Function.Bijective (residueDenominatorMap c) := by
  have h3c : 3*c ≠ 0 := mul_ne_zero (by norm_num) hc
  have hq (r : DenominatorResidue c) (n : O) :
      Ideal.Quotient.mk (Ideal.span {3*c}) (denominatorRep c r+3*c*n)=r := by
    have hzero : Ideal.Quotient.mk (Ideal.span {3*c}) (3*c)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [map_add, map_mul, hzero, zero_mul, add_zero, denominatorRep_spec]
  constructor
  · rintro ⟨r,n⟩ ⟨t,m⟩ heq
    have h := congrArg Subtype.val heq
    change denominatorRep c r.1+3*c*n=denominatorRep c t.1+3*c*m at h
    have hrt : r=t := by
      apply Subtype.ext
      simpa only [hq] using congrArg (Ideal.Quotient.mk (Ideal.span {3*c})) h
    subst t
    have hnm : n=m := mul_left_cancel₀ h3c (add_left_cancel h)
    subst m
    rfl
  · intro d
    let r : DenominatorResidue c := Ideal.Quotient.mk (Ideal.span {3*c}) d.1
    have hr : Ideal.Quotient.mk (Ideal.span {3*c}) (denominatorRep c r)=r := denominatorRep_spec c r
    have hdiv : 3*c ∣ d.1-denominatorRep c r := by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      exact hr.symm
    obtain ⟨n,hn⟩ := hdiv
    have hd : d.1=denominatorRep c r+3*c*n := by linear_combination hn
    have hrcond : denominatorCondition c (denominatorRep c r) := by
      apply (denominatorCondition_shift c _ n).1
      rw [← hd]
      exact d.2
    refine ⟨(⟨r,hrcond⟩,n), ?_⟩
    apply Subtype.ext
    exact hd.symm

def residueDenominatorEquiv (c : O) (hc : c ≠ 0) :
    AdmissibleResidue c × O ≃ AdmissibleDenominator c :=
  Equiv.ofBijective (residueDenominatorMap c) (residueDenominatorMap_bijective c hc)

lemma residueDenominatorEquiv_val (c : O) (hc : c ≠ 0) (p : AdmissibleResidue c × O) :
    ((residueDenominatorEquiv c hc) p).1=denominatorRep c p.1.1+3*c*p.2 := rfl

def primitiveTerm (z : ℂ) (v : ℝ) (s : ℂ) (c d : O) : ℂ :=
  ringComplex (symbol c d) *
    ((v/(‖ringComplex c*z+ringComplex d‖^2+‖ringComplex c‖^2*v^2):ℝ):ℂ)^s

theorem primitive_terms_summable (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    Summable (fun p : Σ c : LevelLower, AdmissibleDenominator c.1 =>
      primitiveTerm z v s p.1.1 p.2.1) := by
  apply primitiveSigmaEquiv.summable_iff.mp
  exact (primitive_rows_summable_norm z v hv s hs).of_norm

theorem upperEisenstein_eq_by_lower (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    upperEisenstein z v hv s=
      ∑' c : LevelLower, ∑' d : AdmissibleDenominator c.1, primitiveTerm z v s c.1 d.1 := by
  rw [upperEisenstein_eq_primitive_rows]
  exact (primitiveSigmaEquiv.tsum_eq (fun p : Σ c : LevelLower, AdmissibleDenominator c.1 =>
    primitiveTerm z v s p.1.1 p.2.1)).trans (primitive_terms_summable z v hv s hs).tsum_sigma

theorem denominator_sum_residues (c : O) (hc : c ≠ 0) (f : O → ℂ)
    (hf : Summable (fun d : AdmissibleDenominator c => f d.1)) :
    (∑' d : AdmissibleDenominator c, f d.1)=
      ∑' r : AdmissibleResidue c, ∑' n : O, f (denominatorRep c r.1+3*c*n) := by
  have hsum := (residueDenominatorEquiv c hc).summable_iff.mpr hf
  exact ((residueDenominatorEquiv c hc).tsum_eq
    (fun d : AdmissibleDenominator c => f d.1)).symm.trans hsum.tsum_prod

lemma primitiveTerm_shift (z : ℂ) (v : ℝ) (s : ℂ) (c d n : O)
    (hc : (3 : O) ∣ c) (hd : (3 : O) ∣ d-1) :
    primitiveTerm z v s c (d+3*c*n)=
      primitiveTerm (z+3*ringComplex n) v s c d := by
  unfold primitiveTerm
  rw [row_symbol_shift c d n hc hd]
  have harg : ringComplex c*z+ringComplex (d+3*c*n)=
      ringComplex c*(z+3*ringComplex n)+ringComplex d := by
    simp only [map_add,map_mul,map_ofNat]
    ring
  rw [harg]

lemma denominator_zero_unique (d : AdmissibleDenominator 0) : d.1=1 := by
  apply CubicJacobi.primary_isUnit_eq_one _ _ (lambda_sq_dvd_three.trans d.2.2)
  simpa only [isCoprime_zero_left] using d.2.1

lemma zero_lower_sum (z : ℂ) (v : ℝ) (s : ℂ) :
    (∑' d : AdmissibleDenominator 0, primitiveTerm z v s 0 d.1)=(v:ℂ)^s := by
  let d0 : AdmissibleDenominator 0 := ⟨1,isCoprime_one_right,by simp⟩
  rw [tsum_eq_single d0]
  · simp [primitiveTerm,d0,symbol_one]
  · intro d hd
    exfalso
    apply hd
    exact Subtype.ext (denominator_zero_unique d)

def residueSeries (z : ℂ) (v : ℝ) (s : ℂ) (c : O) : ℂ :=
  ∑' r : AdmissibleResidue c, ∑' n : O,
    primitiveTerm (z+3*ringComplex n) v s c (denominatorRep c r.1)

theorem upperEisenstein_eq_residue_series (z : ℂ) (v : ℝ) (hv : 0 < v)
    (s : ℂ) (hs : 2 < s.re) :
    upperEisenstein z v hv s =
      ∑' c : LevelLower, if c.1=0 then (v:ℂ)^s else residueSeries z v s c.1 := by
  rw [upperEisenstein_eq_by_lower z v hv s hs]
  apply tsum_congr
  rintro ⟨c,hlevel⟩
  dsimp only
  split_ifs with hc
  · subst c
    exact zero_lower_sum z v s
  · have hsum : Summable (fun d : AdmissibleDenominator c => primitiveTerm z v s c d.1) :=
      (primitive_terms_summable z v hv s hs).sigma_factor ⟨c, hlevel⟩
    rw [denominator_sum_residues c hc (fun d : O => primitiveTerm z v s c d) hsum]
    apply tsum_congr
    intro r
    apply tsum_congr
    intro n
    exact primitiveTerm_shift z v s c (denominatorRep c r.1) n hlevel r.2.2

lemma residueSeries_finite (z : ℂ) (v : ℝ) (s : ℂ) (c : O) (hc : c ≠ 0) :
    letI : Fintype (AdmissibleResidue c) := @Fintype.ofFinite _ (finite_admissibleResidue c hc)
    residueSeries z v s c = ∑ r : AdmissibleResidue c, ∑' n : O,
      primitiveTerm (z+3*ringComplex n) v s c (denominatorRep c r.1) := by
  let : Fintype (AdmissibleResidue c) := @Fintype.ofFinite _ (finite_admissibleResidue c hc)
  exact tsum_fintype _

#print axioms residueDenominatorMap_bijective
#print axioms primitiveTerm_shift
#print axioms upperEisenstein_eq_residue_series
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
