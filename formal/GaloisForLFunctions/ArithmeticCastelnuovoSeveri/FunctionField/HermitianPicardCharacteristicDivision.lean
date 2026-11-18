import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricProductFormula
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Characteristic division and Frobenius on geometric Hermitian classes

Prime-to-characteristic annihilators give unique p-power division in degree
zero. On the whole Picard group divisibility by pⁿ depends only on the
degree. Thus reduction modulo every pⁿ is the ordinary degree residue,
and the intersection of these multiples is the entire degree-zero group.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Pic" => HermitianGeometricPicard p s
local notation "δ" => hermitianPicardDegree p s
local notation "J" => AddMonoidHom.ker (hermitianPicardDegree p s)
local notation "∞ₕ" => hermitianGeometricClass p s ((0,1) : HermitianGeometricPlaceDivisor p s)

private theorem coprime_division {A : Type*} [AddCommGroup A] (x : A) (a b : ℕ)
    (hab : a.Coprime b) (hb : b • x = 0) : ∃ y : A, a • y = x := by
  have hg := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one,Nat.cast_one] at hg
  have hzero : (b:ℤ) • x = 0 := by simpa only [natCast_zsmul] using hb
  refine ⟨Nat.gcdA a b • x,?_⟩
  have he := congrArg (fun t : ℤ => t • x) hg
  rw [one_zsmul,add_smul,mul_smul,mul_comm (b:ℤ),mul_smul,hzero,smul_zero,add_zero,
    natCast_zsmul] at he
  exact he.symm

/-- Multiplication by any power of the characteristic is an automorphism on degree-zero classes. -/
theorem hermitianDegreeZero_characteristic_bijective (n : ℕ) :
    Function.Bijective (fun c : J => p^n • c) := by
  constructor
  · intro x y he
    exact Subtype.ext (hermitianPicard_p_power_injective p s n (congrArg (fun z : J => z.val) he))
  · intro c
    obtain ⟨m,_,hm,ht⟩ := (hermitianPicardDegree_zero_iff p s c.val).1 c.property
    exact coprime_division c (p^n) m (hm.pow_right n).symm (Subtype.ext ht)

def hermitianDegreeZero_characteristicEquiv (n : ℕ) : J ≃+ J :=
  AddEquiv.ofBijective (p^n • AddMonoidHom.id J) (hermitianDegreeZero_characteristic_bijective p s n)

private theorem split_division {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (e : A ≃+ B × C) {m : ℕ} {a : A} (b : B) (c : C)
    (hb : m • b = (e a).1) (hc : m • c = (e a).2) : ∃ u : A, m • u = a := by
  refine ⟨e.symm (b,c),e.injective ?_⟩
  rw [map_nsmul,e.apply_symm_apply]
  exact Prod.ext hb hc

/-- Exactly the degrees divisible by pⁿ occur in the pⁿ-multiple subgroup. -/
theorem hermitianPicard_characteristic_division_iff (n : ℕ) (c : Pic) :
    (∃ b : Pic, p^n • b = c) ↔ ((p^n:ℕ):ℤ) ∣ δ c := by
  constructor
  · rintro ⟨b,rfl⟩
    exact ⟨δ b,by rw [map_nsmul,nsmul_eq_mul]⟩
  · rintro ⟨z,hz⟩
    let t := hermitianPicardSplit p s c
    obtain ⟨b,hb⟩ := (hermitianDegreeZero_characteristic_bijective p s n).surjective t.2
    apply split_division (hermitianPicardSplit p s) z b ?_ hb
    change p^n • z = δ c
    rw [nsmul_eq_mul,hz]

/-- A divisor class has a pⁿ-th root exactly when its degree does, and the root is unique. -/
theorem hermitianPicard_unique_characteristic_root (n : ℕ) (c : Pic) :
    (∃! b : Pic, p^n • b = c) ↔ ((p^n:ℕ):ℤ) ∣ δ c := by
  rw [← hermitianPicard_characteristic_division_iff]
  exact ⟨ExistsUnique.exists,fun ⟨b,h⟩ => ⟨b,h,fun y hy =>
    hermitianPicard_p_power_injective p s n (hy.trans h.symm)⟩⟩

/-- Reduction modulo characteristic powers remembers exactly degree. -/
def hermitianPicard_mod_characteristic (n : ℕ) :
    Pic ⧸ (p^n • AddMonoidHom.id Pic).range ≃+ ZMod (p^n) := by
  let f := (Int.castAddHom (ZMod (p^n))).comp δ
  have he : (p^n • AddMonoidHom.id Pic).range = f.ker := by
    ext c
    change (∃ b : Pic, p^n • b = c) ↔ (δ c : ZMod (p^n)) = 0
    rw [hermitianPicard_characteristic_division_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  apply (QuotientAddGroup.quotientAddEquivOfEq he).trans
  apply QuotientAddGroup.quotientKerEquivOfSurjective
  intro x
  obtain ⟨z,rfl⟩ := ZMod.intCast_surjective x
  refine ⟨z • ∞ₕ,?_⟩
  change (δ (z • ∞ₕ) : ZMod (p^n)) = _
  rw [hermitianPicardDegree_infinity]

/-- The intersection of all characteristic-power multiples is exactly the degree-zero subgroup. -/
theorem hermitianPicard_characteristic_intersection :
    (⨅ n : ℕ, (p^n • AddMonoidHom.id Pic).range) = J := by
  ext c
  simp only [AddSubgroup.mem_iInf]
  change (∀ n : ℕ, ∃ b : Pic, p^n • b = c) ↔ δ c = 0
  simp_rw [hermitianPicard_characteristic_division_iff]
  refine ⟨fun h => ?_, fun he n => he ▸ dvd_zero _⟩
  by_contra hn
  let m := (δ c).natAbs
  obtain ⟨k,hk⟩ := h m
  have ha := congrArg Int.natAbs hk
  rw [Int.natAbs_mul,Int.natAbs_natCast] at ha
  have hle : p^m ≤ m := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) ⟨k.natAbs,ha⟩
  have htwo : 2^m ≤ p^m := Nat.pow_le_pow_left (Fact.out : p.Prime).two_le _
  exact (Nat.not_lt_of_ge (htwo.trans hle)) Nat.lt_two_pow_self

/-- The class of every normalized divisor transforms by -Q under geometric Frobenius. -/
theorem hermitianPicard_frobenius_normalized (D : HermitianGeometricPoint p s →₀ ℤ) :
    hermitianGeometricClass p s (hermitianGeometricDegreeZeroPart p s (hermitianGeometricFrobeniusDivisor p s D)) =
      -(p^(s+1) • hermitianGeometricClass p s (hermitianGeometricDegreeZeroPart p s D)) := by
  let A := hermitianGeometricDegreeZeroPart p s D
  let B := hermitianGeometricDegreeZeroPart p s (hermitianGeometricFrobeniusDivisor p s D)
  have h : hermitianGeometricClass p s ((((p^(s+1):ℕ):ℤ) • A) + B) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 ⟨Additive.ofMul (hermitianGeometricTangentProduct p s D),
      hermitianGeometricTangentProduct_divisor p s D⟩
  rw [map_add,map_zsmul,natCast_zsmul] at h
  change hermitianGeometricClass p s B = -(p^(s+1) • hermitianGeometricClass p s A)
  apply eq_neg_iff_add_eq_zero.mpr
  rwa [add_comm]

#print axioms hermitianDegreeZero_characteristic_bijective
#print axioms hermitianDegreeZero_characteristicEquiv
#print axioms hermitianPicard_characteristic_division_iff
#print axioms hermitianPicard_unique_characteristic_root
#print axioms hermitianPicard_mod_characteristic
#print axioms hermitianPicard_characteristic_intersection
#print axioms hermitianPicard_frobenius_normalized
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
