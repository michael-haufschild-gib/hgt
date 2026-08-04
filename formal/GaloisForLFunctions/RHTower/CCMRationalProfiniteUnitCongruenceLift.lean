import GaloisForLFunctions.RHTower.CCMRationalClassSpaceSection
import GaloisForLFunctions.RHTower.CCMRationalIntegralFiniteAdeleCyclicQuotient
import Mathlib.Data.ZMod.Units

/-!
# Congruence lifting from finite units to actual profinite units

For every nonzero modulus `N`, every unit of `ZMod N` has a representative
in the literal profinite-unit subgroup of the rational finite ideles.  The
representative is congruent to the diagonal integer modulo `N Z-hat`.

The construction is coordinatewise.  At primes dividing `N` use the given
integer representative, which is a local unit by coprimality.  At all other
primes use `1`; multiplication by `N` is invertible there, so the difference
from the integer representative is an `N`-multiple.  The resulting family of
`p`-adic units is transported into the actual restricted-product finite
adele ring.  No inverse-limit identification is assumed.
-/

noncomputable section

open PadicInt
open scoped Classical RestrictedProduct algebraMap

namespace GaloisForLFunctions.RHTower

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

private abbrev ProfiniteIntegers := CCMRationalProfiniteIntegers
private abbrev IntegralFiniteAdeles :=
  ccmRationalIntegralFiniteAdelesAddSubgroup

/-- A natural number prime to `p` as a genuine unit of `Z_p`. -/
noncomputable def ccmPadicIntNatUnit
    (p : Nat.Primes) (n : ℕ) (hpn : ¬ p.1 ∣ n) : ℤ_[p]ˣ :=
  ((PadicInt.isUnit_iff).2
    ((PadicInt.norm_natCast_eq_one_iff).2
      (p.2.coprime_iff_not_dvd.2 hpn))).unit

@[simp]
theorem ccmPadicIntNatUnit_coe
    (p : Nat.Primes) (n : ℕ) (hpn : ¬ p.1 ∣ n) :
    (ccmPadicIntNatUnit p n hpn : ℤ_[p]) = n := by
  exact IsUnit.unit_spec _

/-- Transport a family of actual `p`-adic units to an integral finite adele. -/
def ccmRationalPadicUnitsIntegralFiniteAdele
    (a : ∀ p : Nat.Primes, ℤ_[p]ˣ) : IntegralFiniteAdeles :=
  ccmRationalProfiniteIntegersAddEquivIntegralFiniteAdeles
    (fun p => (a p : ℤ_[p]))

/-- Coordinatewise `p`-adic units define an actual profinite finite idele. -/
def ccmRationalProfiniteUnitOfPadicUnits
    (a : ∀ p : Nat.Primes, ℤ_[p]ˣ) : CCMRationalProfiniteUnit := by
  let z : IntegralFiniteAdeles :=
    ccmRationalPadicUnitsIntegralFiniteAdele a
  let zi : IntegralFiniteAdeles :=
    ccmRationalPadicUnitsIntegralFiniteAdele (fun p => (a p)⁻¹)
  have hmul : z.1 * zi.1 = 1 := by
    apply RestrictedProduct.ext
    intro v
    letI : Algebra ℤ (v.adicCompletionIntegers ℚ) :=
      Ring.toIntAlgebra _
    change
      ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm
          (a (Rat.HeightOneSpectrum.primesEquiv v) :
            ℤ_[Rat.HeightOneSpectrum.primesEquiv v]) :
          v.adicCompletion ℚ) *
        ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm
          (↑((a (Rat.HeightOneSpectrum.primesEquiv v))⁻¹) :
            ℤ_[Rat.HeightOneSpectrum.primesEquiv v]) :
          v.adicCompletion ℚ) = 1
    let e := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
    have hv :
        e.symm (a (Rat.HeightOneSpectrum.primesEquiv v) :
            ℤ_[Rat.HeightOneSpectrum.primesEquiv v]) *
          e.symm (↑((a (Rat.HeightOneSpectrum.primesEquiv v))⁻¹) :
            ℤ_[Rat.HeightOneSpectrum.primesEquiv v]) = 1 := by
      rw [← map_mul]
      simp
    exact congrArg
      (fun y : v.adicCompletionIntegers ℚ =>
        (y : v.adicCompletion ℚ)) hv
  have hmuli : zi.1 * z.1 = 1 := by
    rw [mul_comm]
    exact hmul
  let u : CCMRationalFiniteAdeleˣ :=
    ⟨z.1, zi.1, hmul, hmuli⟩
  refine ⟨u, ?_⟩
  exact ⟨z.2, by simpa [u] using zi.2⟩

@[simp]
theorem ccmRationalProfiniteUnitOfPadicUnits_integralVal
    (a : ∀ p : Nat.Primes, ℤ_[p]ˣ) :
    (⟨((ccmRationalProfiniteUnitOfPadicUnits a).1 :
          CCMRationalFiniteAdele),
        (ccmRationalProfiniteUnitOfPadicUnits a).2.1⟩ :
      IntegralFiniteAdeles) =
      ccmRationalPadicUnitsIntegralFiniteAdele a := by
  rfl

/-- Coordinate unit representative of a unit modulo `N`: use its integer
value at primes dividing `N`, and `1` elsewhere. -/
def ccmRationalZModUnitPadicLift
    (N : ℕ) (u : (ZMod N)ˣ) (p : Nat.Primes) : ℤ_[p]ˣ := by
  let k := (u : ZMod N).val
  by_cases hp : p.1 ∣ N
  · have hkp : ¬ p.1 ∣ k := by
      exact p.2.coprime_iff_not_dvd.mp
        ((ZMod.val_coe_unit_coprime u).coprime_dvd_right hp).symm
    exact ccmPadicIntNatUnit p k hkp
  · exact 1

/-- Coordinate quotient witnessing that the lifted unit differs from its
integer representative by an `N`-multiple. -/
def ccmRationalZModUnitPadicLiftQuotient
    (N : ℕ) (u : (ZMod N)ˣ) (p : Nat.Primes) : ℤ_[p] := by
  by_cases hp : p.1 ∣ N
  · exact 0
  · exact
      (↑((ccmPadicIntNatUnit p N hp)⁻¹) : ℤ_[p]) *
        (1 - ((u : ZMod N).val : ℤ_[p]))

theorem ccmRationalZModUnitPadicLift_sub_eq_nsmul
    (N : ℕ) (u : (ZMod N)ˣ) (p : Nat.Primes) :
    (ccmRationalZModUnitPadicLift N u p : ℤ_[p]) -
        ((u : ZMod N).val : ℤ_[p]) =
      N • ccmRationalZModUnitPadicLiftQuotient N u p := by
  by_cases hp : p.1 ∣ N
  · have hkp : ¬ p.1 ∣ (u : ZMod N).val := by
      exact p.2.coprime_iff_not_dvd.mp
        ((ZMod.val_coe_unit_coprime u).coprime_dvd_right hp).symm
    simp [ccmRationalZModUnitPadicLift,
      ccmRationalZModUnitPadicLiftQuotient, hp,
      ccmPadicIntNatUnit_coe]
  · simp only [ccmRationalZModUnitPadicLift,
      ccmRationalZModUnitPadicLiftQuotient, hp]
    rw [nsmul_eq_mul]
    have hu :
        (N : ℤ_[p]) *
            (↑((ccmPadicIntNatUnit p N hp)⁻¹) : ℤ_[p]) = 1 := by
      rw [← ccmPadicIntNatUnit_coe p N hp]
      exact Units.mul_inv _
    simpa [ccmRationalZModUnitPadicLift,
      ccmRationalZModUnitPadicLiftQuotient, hp,
      nsmul_eq_mul, ← mul_assoc, hu]

/-- Integral finite-adele value of a profinite unit. -/
def ccmRationalProfiniteUnitIntegralVal
    (u : CCMRationalProfiniteUnit) : IntegralFiniteAdeles :=
  ⟨(u.1 : CCMRationalFiniteAdele), u.2.1⟩

/-- **Finite-unit congruence lift.** Every unit modulo a nonzero `N` lifts
to a literal profinite unit congruent to its canonical integer representative
modulo `N Z-hat`. -/
theorem ccmRationalZModUnit_exists_profiniteUnit_congruent
    (N : ℕ) (hN : N ≠ 0) (u : (ZMod N)ˣ) :
    ∃ v : CCMRationalProfiniteUnit,
      ∃ z : IntegralFiniteAdeles,
        ccmRationalProfiniteUnitIntegralVal v -
            ccmRationalIntegralFiniteAdeleDiagonal
              ((u : ZMod N).val : ℤ) =
          N • z := by
  let a : ∀ p : Nat.Primes, ℤ_[p]ˣ :=
    ccmRationalZModUnitPadicLift N u
  let x : ProfiniteIntegers :=
    ccmRationalZModUnitPadicLiftQuotient N u
  let v : CCMRationalProfiniteUnit :=
    ccmRationalProfiniteUnitOfPadicUnits a
  let z : IntegralFiniteAdeles :=
    ccmRationalProfiniteIntegersAddEquivIntegralFiniteAdeles x
  have hx : ((fun p : Nat.Primes => (a p : ℤ_[p])) : ProfiniteIntegers) -
      ccmRationalProfiniteIntegerDiagonal ((u : ZMod N).val : ℤ) =
      N • x := by
    funext p
    change (a p : ℤ_[p]) - ((u : ZMod N).val : ℤ_[p]) = N • x p
    exact ccmRationalZModUnitPadicLift_sub_eq_nsmul N u p
  have hmap := congrArg
    ccmRationalProfiniteIntegersAddEquivIntegralFiniteAdeles hx
  rw [map_sub, map_nsmul,
    ccmRationalProfiniteIntegersAddEquivIntegralFiniteAdeles_diagonal] at hmap
  refine ⟨v, z, ?_⟩
  simpa [v, z, a, ccmRationalProfiniteUnitIntegralVal,
    ccmRationalPadicUnitsIntegralFiniteAdele] using hmap

end GaloisForLFunctions.RHTower
