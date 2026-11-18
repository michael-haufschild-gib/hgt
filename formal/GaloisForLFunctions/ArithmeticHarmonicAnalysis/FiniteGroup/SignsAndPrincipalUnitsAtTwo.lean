import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Signs and principal units modulo a power of two

Reduction modulo four distinguishes the sign from the powers of five.
The two factors determine every power-kernel size, including the higher
dyadic ranks in Dahan's cyclic-subgroup estimate.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicUnits

abbrev U (s : ℕ) := (ZMod (2^(s+2)))ˣ
abbrev Cycle (m : ℕ) := Multiplicative (ZMod m)

private def five (s : ℕ) : U s :=
  ZMod.unitOfCoprime 5 ((by norm_num : Nat.Coprime 5 2).pow_right _)

private theorem five_order (s : ℕ) : orderOf (five s) = 2^s := by
  rw [← orderOf_units]
  exact ZMod.orderOf_five s

private def reduction (s : ℕ) : U s →* (ZMod 4)ˣ :=
  ZMod.unitsMap (show 2^2 ∣ 2^(s+2) from pow_dvd_pow 2 (by omega))

private def sign (s : ℕ) : ℤˣ →* U s := Units.map (Int.castRingHom _).toMonoidHom

private theorem principal_reduces (s : ℕ) (x : Subgroup.zpowers (five s)) :
    reduction s x.val = 1 := by
  obtain ⟨k,hk⟩ := x.property
  have h₅ : reduction s (five s) = 1 := by
    apply Units.ext
    change ZMod.castHom _ (ZMod 4) (5 : ZMod (2^(s+2))) = 1
    rw [map_ofNat]
    calc (5 : ZMod 4) = 1 + (4 : ℕ) := by norm_num
         _ = 1 := by rw [ZMod.natCast_self,add_zero]
  rw [← hk,map_zpow,h₅,one_zpow]

private theorem reduce_sign (s : ℕ) (e : ℤˣ) :
    ((reduction s (sign s e) : (ZMod 4)ˣ) : ZMod 4) = ((e : ℤ) : ZMod 4) := by
  change ZMod.castHom _ (ZMod 4) ((e : ℤ) : ZMod (2^(s+2))) = _
  exact map_intCast _ _

private def combine (s : ℕ) : ℤˣ × Subgroup.zpowers (five s) →* U s where
  toFun x := sign s x.1 * x.2.val
  map_one' := by simp
  map_mul' _ _ := by simp only [Prod.fst_mul,Prod.snd_mul,map_mul,Subgroup.coe_mul]; ac_rfl

private theorem combine_injective (s : ℕ) : Function.Injective (combine s) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ h
  change sign s a*x.val=sign s b*y.val at h
  have r := congrArg (reduction s) h
  rw [map_mul,map_mul,principal_reduces,principal_reduces,mul_one,mul_one] at r
  have rs := congrArg (fun v : (ZMod 4)ˣ => (v : ZMod 4)) r
  rw [reduce_sign,reduce_sign] at rs
  have hne : (-1 : ZMod 4) ≠ 1 := by
    intro he
    have hz : (2 : ZMod 4)=0 := by linear_combination -he
    exact (by norm_num : ¬4 ∣ 2) ((ZMod.natCast_eq_zero_iff 2 4).mp hz)
  have hab : a=b := by
    rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl
    · rfl
    · exact (hne (by simpa using rs.symm)).elim
    · exact (hne (by simpa using rs)).elim
    · rfl
  subst b
  exact Prod.ext rfl (Subtype.ext (mul_left_cancel h))

private theorem combine_card (s : ℕ) :
    Fintype.card (ℤˣ × Subgroup.zpowers (five s)) = Fintype.card (U s) := by
  rw [Fintype.card_prod,Fintype.card_units_int,Fintype.card_zpowers,five_order,
    ZMod.card_units_eq_totient,Nat.totient_prime_pow_succ Nat.prime_two,pow_succ]
  omega

/-- The factors have orders two and 2^s. This includes s=0, where the
principal-unit group is trivial. -/
def decomposition (s : ℕ) : U s ≃* Cycle 2 × Cycle (2^s) :=
  let e := MulEquiv.ofBijective (combine s)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨combine_injective s,combine_card s⟩)
  e.symm.trans (MulEquiv.prodCongr
    (mulEquivOfPrimeCardEq (p := 2) (by rw [Nat.card_eq_fintype_card,Fintype.card_units_int])
      (by change Nat.card (ZMod 2)=2; exact Nat.card_zmod _))
    (mulEquivOfCyclicCardEq (by
      change Nat.card (Subgroup.zpowers (five s))=Nat.card (ZMod (2^s))
      rw [Nat.card_zpowers,five_order,Nat.card_zmod])))

/-- Number of n-torsion elements, including the identity. -/
def torsionCount (G : Type*) [CommGroup G] (n : ℕ) := Nat.card {x : G // x^n=1}

theorem torsionCount_congr {G H : Type*} [CommGroup G] [CommGroup H] (e : G ≃* H) (n : ℕ) :
    torsionCount G n=torsionCount H n :=
  Nat.card_congr (e.toEquiv.subtypeEquiv (fun x => by simp only [← map_pow,e.map_eq_one_iff]))

theorem torsionCount_prod (G H : Type*) [CommGroup G] [CommGroup H] [Finite G] [Finite H] (n : ℕ) :
    torsionCount (G × H) n = torsionCount G n * torsionCount H n := by
  let e : {x : G × H // x^n=1} ≃ {x : G // x^n=1} × {y : H // y^n=1} :=
    { toFun x := (⟨x.val.1,congrArg Prod.fst x.property⟩,⟨x.val.2,congrArg Prod.snd x.property⟩)
      invFun x := ⟨(x.1.val,x.2.val),Prod.ext x.1.property x.2.property⟩
      left_inv _ := rfl, right_inv _ := rfl }
  exact (Nat.card_congr e).trans (Nat.card_prod _ _)

theorem torsionCount_cycle (m n : ℕ) [NeZero m] : torsionCount (Cycle m) n=m.gcd n := by
  change Nat.card (powMonoidHom n : Cycle m →* Cycle m).ker=_
  rw [IsCyclic.card_powMonoidHom_ker]
  change (Nat.card (ZMod m)).gcd n=_
  rw [Nat.card_zmod]

theorem dyadic_torsion (s n : ℕ) : torsionCount (U s) n = (Nat.gcd 2 n)*((2^s).gcd n) := by
  rw [torsionCount_congr (decomposition s),torsionCount_prod,torsionCount_cycle,torsionCount_cycle]

private theorem gcd_powers (s k : ℕ) : (2^s).gcd (2^k) = 2^(min s k) := by
  rcases le_total s k with h | h
  · rw [min_eq_left h,Nat.gcd_eq_left (pow_dvd_pow 2 h)]
  · rw [min_eq_right h,Nat.gcd_eq_right (pow_dvd_pow 2 h)]

/-- The jump from depth k to depth k+1 contains a sign bit only at k=0.
The principal unit contributes another bit at every k strictly below s. -/
theorem dyadic_torsion_layer (s k : ℕ) :
    torsionCount (U s) (2^(k+1)) =
      torsionCount (U s) (2^k) * (if k=0 then 2 else 1) * (if k<s then 2 else 1) := by
  have first (j : ℕ) : Nat.gcd 2 (2^j)=2^(min 1 j) := by simpa only [pow_one] using gcd_powers 1 j
  simp only [dyadic_torsion,first,gcd_powers]
  cases k with
  | zero => cases s <;> simp
  | succ k =>
    by_cases h : k+1<s
    · have h₁ : k+1≤s := h.le
      simp [h,min_eq_right h₁,min_eq_right h,pow_succ,mul_assoc]
    · have h₁ : s≤k+1 := by omega
      have h₂ : s≤k+1+1 := by omega
      simp [h,min_eq_left h₁,min_eq_left h₂]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicUnits

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicUnits.torsionCount_congr
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicUnits.torsionCount_prod
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicUnits.torsionCount_cycle
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicUnits.dyadic_torsion
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicUnits.dyadic_torsion_layer
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.DyadicUnits.decomposition
