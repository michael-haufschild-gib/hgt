/-
Cubic admissible residue counts adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicConstantTermIsSupportedOnCubes

/-!
# Counting cubic admissible residues

Writing each denominator as `1+3u` identifies admissible classes with
an affine unit condition. Chinese remainders split ramified and
unramified factors. The ramified condition is automatic, giving
`3^n φ((m))` classes for the modulus `lambda^n m` with `m` coprime to three.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

private instance cubicResidueCountCyclotomic : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

lemma isUnit_quotient_span_iff (c d : O) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {c}) d) ↔ IsCoprime c d := by
  constructor
  · intro hd
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hd
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hdiv : c ∣ d*b-1 := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_sub,map_mul,map_one,sub_eq_zero] using hb
    obtain ⟨k,hk⟩ := hdiv
    exact ⟨-k,b,by linear_combination hk⟩
  · rintro ⟨a,b,hab⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk (Ideal.span {c}) b, ?_⟩
    have hc : Ideal.Quotient.mk (Ideal.span {c}) c=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have h := congrArg (Ideal.Quotient.mk (Ideal.span {c})) hab
    simpa only [map_add,map_mul,map_one,hc,mul_zero,zero_mul,zero_add,mul_comm] using h

/-- A chosen representative of a principal residue class. -/
def principalResidueRep (c : O) (r : O ⧸ Ideal.span {c}) : O :=
  Classical.choose (Ideal.Quotient.mk_surjective r)

lemma principalResidueRep_spec (c : O) (r : O ⧸ Ideal.span {c}) :
    Ideal.Quotient.mk (Ideal.span {c}) (principalResidueRep c r)=r :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective r)

abbrev AffineUnitResidue (c : O) :=
  {u : O ⧸ Ideal.span {c} // IsUnit (1+3*u)}

lemma affine_representative_condition (c : O) (u : AffineUnitResidue c) :
    denominatorCondition c (1+3*principalResidueRep c u.1) := by
  refine ⟨(isUnit_quotient_span_iff c _).mp ?_, ⟨_,by ring⟩⟩
  simpa only [map_add,map_mul,map_one,map_ofNat,
    principalResidueRep_spec] using u.2

def affineResidueMap (c : O) (u : AffineUnitResidue c) : AdmissibleResidue c :=
  ⟨Ideal.Quotient.mk (Ideal.span {3*c})
    (1+3*principalResidueRep c u.1), by
    apply (denominatorCondition_congr c _
      (1+3*principalResidueRep c u.1) ?_).mpr
      (affine_representative_condition c u)
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    exact denominatorRep_spec c _⟩

lemma affineResidueMap_bijective (c : O) : Function.Bijective (affineResidueMap c) := by
  constructor
  · intro u v huv
    have hdiv : 3*c ∣ (1+3*principalResidueRep c u.1)-
        (1+3*principalResidueRep c v.1) := by
      apply Ideal.mem_span_singleton.mp
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (congrArg Subtype.val huv)
    obtain ⟨k,hk⟩ := hdiv
    have hk' : principalResidueRep c u.1-
        principalResidueRep c v.1=c*k := by
      have h3 : (3:O) ≠ 0 := by norm_num
      apply mul_left_cancel₀ h3
      linear_combination hk
    apply Subtype.ext
    rw [← principalResidueRep_spec c u.1,
      ← principalResidueRep_spec c v.1]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr ⟨k,hk'⟩)
  · intro r
    obtain ⟨u,hu⟩ := r.2.2
    have hd : denominatorRep c r.1=1+3*u := by linear_combination hu
    let q : AffineUnitResidue c := ⟨Ideal.Quotient.mk (Ideal.span {c}) u, by
      have hh := (isUnit_quotient_span_iff c _).mpr r.2.1
      simpa only [hd,map_add,map_one,map_mul,map_ofNat] using hh⟩
    refine ⟨q,Subtype.ext ?_⟩
    change Ideal.Quotient.mk (Ideal.span {3*c})
      (1+3*principalResidueRep c q.1)=r.1
    rw [← denominatorRep_spec c r.1,hd]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hrep : c ∣ principalResidueRep c q.1-u := by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      exact principalResidueRep_spec c q.1
    obtain ⟨k,hk⟩ := hrep
    exact ⟨k,by linear_combination 3*hk⟩

def affineResidueEquiv (c : O) : AffineUnitResidue c ≃ AdmissibleResidue c :=
  Equiv.ofBijective (affineResidueMap c) (affineResidueMap_bijective c)

def unitsSubtypeEquiv (R : Type*) [Monoid R] : Rˣ ≃ {x : R // IsUnit x} where
  toFun u := ⟨u,u.isUnit⟩
  invFun x := x.2.unit
  left_inv u := Units.ext u.isUnit.unit_spec
  right_inv x := Subtype.ext x.2.unit_spec

def quotientProductEquiv (a b : O) (hab : IsCoprime a b) :
    (O ⧸ Ideal.span {a*b}) ≃+* (O ⧸ Ideal.span {a}) × (O ⧸ Ideal.span {b}) :=
  (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b).symm).trans
    (Ideal.quotientMulEquivQuotientProd _ _ ((Ideal.isCoprime_span_singleton_iff a b).mpr hab))

def affineCRTEq (a b : O) (hab : IsCoprime a b) :
    AffineUnitResidue (a*b) ≃ AffineUnitResidue a × AffineUnitResidue b :=
  ((quotientProductEquiv a b hab).toEquiv.subtypeEquiv (fun q => by
    rw [← MulEquiv.isUnit_map (quotientProductEquiv a b hab) (x := 1+3*q)]
    simp only [map_add,map_one,map_mul,map_ofNat,Prod.isUnit_iff]
    rfl)).trans Equiv.subtypeProdEquivProd

lemma affine_ramified_unit (n : ℕ) (q : O ⧸ Ideal.span {lambda^n}) : IsUnit (1+3*q) := by
  obtain ⟨d,rfl⟩ := Ideal.Quotient.mk_surjective q
  have hlam3 : lambda ∣ (3:O) :=
    (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
  have hcop : IsCoprime lambda (1+3*d) :=
    coprime_of_dvd_sub_one _ _ (by convert hlam3.mul_right d using 1 ; ring)
  have h := (isUnit_quotient_span_iff (lambda^n) (1+3*d)).mpr hcop.pow_left
  simpa only [map_add,map_one,map_mul,map_ofNat] using h

def affineRamifiedEquiv (n : ℕ) : AffineUnitResidue (lambda^n) ≃ (O ⧸ Ideal.span {lambda^n}) :=
  Equiv.subtypeUnivEquiv (affine_ramified_unit n)

def affineUnramifiedEquiv (m : O) (hm : IsCoprime m (3:O)) :
    AffineUnitResidue m ≃ (O ⧸ Ideal.span {m})ˣ := by
  let h3 : IsUnit (3 : O ⧸ Ideal.span {m}) := by
    simpa only [map_ofNat] using (isUnit_quotient_span_iff m 3).mpr hm
  let e : (O ⧸ Ideal.span {m}) ≃ (O ⧸ Ideal.span {m}) :=
    h3.unit.mulLeft.trans (Equiv.addLeft 1)
  refine (e.subtypeEquiv (fun q => ?_)).trans (unitsSubtypeEquiv _).symm
  change IsUnit (1+3*q) ↔ IsUnit (1+(h3.unit : O ⧸ Ideal.span {m})*q)
  rw [h3.unit_spec]

def idealTotient (I : Ideal O) : ℕ := Nat.card (O ⧸ I)ˣ

lemma card_admissible_ramified_product (n : ℕ) (m : O)
    (hm : IsCoprime m (3:O)) (hlamm : IsCoprime lambda m) :
    Nat.card (AdmissibleResidue (lambda^n*m)) =
      Nat.card (O ⧸ Ideal.span {lambda^n}) * idealTotient (Ideal.span {m}) := by
  calc
    _ = Nat.card (AffineUnitResidue (lambda^n*m)) :=
      Nat.card_congr (affineResidueEquiv _).symm
    _ = Nat.card (AffineUnitResidue (lambda^n) × AffineUnitResidue m) :=
      Nat.card_congr (affineCRTEq _ _ hlamm.pow_left)
    _ = Nat.card ((O ⧸ Ideal.span {lambda^n}) × (O ⧸ Ideal.span {m})ˣ) :=
      Nat.card_congr (Equiv.prodCongr (affineRamifiedEquiv n) (affineUnramifiedEquiv m hm))
    _ = _ := Nat.card_prod _ _

lemma absNorm_span_lambda : Ideal.absNorm (Ideal.span {lambda})=3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclotomicExtension {3^(0+1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {3} ℚ K)
  exact IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one 3 0
    (IsCyclotomicExtension.zeta_spec 3 ℚ K)

lemma card_quotient_lambda_pow (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {lambda^n})=3^n := by
  change Ideal.absNorm (Ideal.span {lambda^n})=3^n
  rw [← Ideal.span_singleton_pow,map_pow,absNorm_span_lambda]

theorem card_admissible_lambda_pow_mul (n : ℕ) (m : O)
    (hm : IsCoprime m (3:O)) :
    Nat.card (AdmissibleResidue (lambda^n*m)) = 3^n * idealTotient (Ideal.span {m}) := by
  have hlam3 : lambda ∣ (3:O) :=
    (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
  rw [card_admissible_ramified_product n m hm
    (hm.symm.of_isCoprime_of_dvd_left hlam3),card_quotient_lambda_pow]


#print axioms affineResidueEquiv
#print axioms card_admissible_lambda_pow_mul
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
