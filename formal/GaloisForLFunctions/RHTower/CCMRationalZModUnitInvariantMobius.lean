import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Unit-orbit Möbius decomposition on `ZMod N`

Multiplication by `(ZMod N)ˣ` has one orbit for each divisor of a nonzero
modulus `N`.  This file proves the stronger linear statement needed for the
rational CCM Tate factorization: every unit-invariant function with values in
an arbitrary additive group is a finite sum of divisibility indicators, with
canonical coefficients supplied by Möbius inversion.

The proof does not count or enumerate units.  Mathlib's unit-times-divisor
factorization identifies the orbit label with `gcd(r.val, N)`; ordinary
Möbius inversion then changes the gcd label into the divisor basis.  This is
the finite universal law behind profinite Haar radialization.
-/

noncomputable section

open scoped Classical ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RHTower

/-- A function on `ZMod N` is invariant under multiplication by every unit. -/
def CCMRationalZModUnitInvariant
    {V : Type*} (N : ℕ) (g : ZMod N → V) : Prop :=
  ∀ (u : (ZMod N)ˣ) (r : ZMod N), g ((u : ZMod N) * r) = g r

/-- A unit-times-divisor presentation has divisor equal to the canonical gcd
orbit label. -/
theorem ccmRationalZMod_gcd_eq_of_eq_unit_mul_divisor
    {N d : ℕ} {a u : ZMod N}
    (hN : N ≠ 0) (hu : IsUnit u) (hd : d ∣ N)
    (ha : a = u * (d : ZMod N)) :
    a.val.gcd N = d := by
  letI : NeZero N := ⟨hN⟩
  have hz : (a.val : ZMod N) = (u.val * d : ℕ) := by
    rw [ZMod.natCast_zmod_val, Nat.cast_mul, ZMod.natCast_zmod_val]
    exact ha
  have hmod : a.val ≡ u.val * d [MOD N] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hz
  calc
    a.val.gcd N = (u.val * d).gcd N := hmod.gcd_eq
    _ = d := Nat.gcd_mul_of_coprime_of_dvd
      (by
        simpa [IsUnit.unit_spec] using
          ZMod.val_coe_unit_coprime hu.unit)
      hd

/-- Every residue is a genuine unit multiple of its canonical gcd label. -/
theorem ccmRationalZMod_exists_unit_mul_gcd
    {N : ℕ} (hN : N ≠ 0) (a : ZMod N) :
    ∃ u : (ZMod N)ˣ, a = (u : ZMod N) * (a.val.gcd N : ZMod N) := by
  obtain ⟨d, hd, u, hu, ha⟩ := ZMod.eq_unit_mul_divisor a
  have hlabel :=
    ccmRationalZMod_gcd_eq_of_eq_unit_mul_divisor hN hu hd ha
  refine ⟨hu.unit, ?_⟩
  rw [hlabel]
  simpa [IsUnit.unit_spec] using ha

/-- Unit-invariant functions depend only on the gcd orbit label. -/
theorem CCMRationalZModUnitInvariant.eq_gcd
    {V : Type*} {N : ℕ} {g : ZMod N → V}
    (hN : N ≠ 0) (hg : CCMRationalZModUnitInvariant N g) (a : ZMod N) :
    g a = g (a.val.gcd N : ZMod N) := by
  obtain ⟨u, hu⟩ := ccmRationalZMod_exists_unit_mul_gcd hN a
  calc
    g a = g ((u : ZMod N) * (a.val.gcd N : ZMod N)) := congrArg g hu
    _ = g (a.val.gcd N : ZMod N) := hg u _

/-- Canonical Möbius coefficient of a residue function, evaluated on natural
divisor representatives. -/
def ccmRationalZModMobiusDivisorCoefficient
    {V : Type*} [AddCommGroup V]
    (N : ℕ) (g : ZMod N → V) (d : ℕ) : V :=
  ∑ x ∈ d.divisorsAntidiagonal,
    ArithmeticFunction.moebius x.1 • g (x.2 : ZMod N)

/-- Möbius inversion reconstructs every natural representative from its
divisor coefficients.  No invariance is needed for this algebraic identity. -/
theorem ccmRationalZMod_sum_mobiusDivisorCoefficient
    {V : Type*} [AddCommGroup V]
    (N : ℕ) (g : ZMod N → V) {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors,
      ccmRationalZModMobiusDivisorCoefficient N g d) =
        g (n : ZMod N) := by
  exact
    ((ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
      (R := V)
      (f := ccmRationalZModMobiusDivisorCoefficient N g)
      (g := fun m => g (m : ZMod N))).2
        (by intro d hd; rfl)) n hn

/-- **Unit-orbit Möbius law.** Every unit-invariant function on `ZMod N`, for
`N ≠ 0`, is exactly the sum of its canonical coefficients over divisors of
the residue's gcd with `N`. -/
theorem CCMRationalZModUnitInvariant.eq_sum_mobiusDivisorCoefficient
    {V : Type*} [AddCommGroup V]
    {N : ℕ} (hN : N ≠ 0) {g : ZMod N → V}
    (hg : CCMRationalZModUnitInvariant N g) (a : ZMod N) :
    g a = ∑ d ∈ (a.val.gcd N).divisors,
      ccmRationalZModMobiusDivisorCoefficient N g d := by
  rw [hg.eq_gcd hN]
  exact (ccmRationalZMod_sum_mobiusDivisorCoefficient N g
    (Nat.gcd_pos_of_pos_right a.val (Nat.pos_of_ne_zero hN))).symm

/-- Divisors of the gcd are precisely simultaneous divisors of the residue
value and the modulus. -/
theorem ccmRational_mem_gcd_divisors_iff
    {N d : ℕ} (hN : N ≠ 0) (a : ZMod N) :
    d ∈ (a.val.gcd N).divisors ↔ d ∣ a.val ∧ d ∣ N := by
  simp [Nat.mem_divisors, Nat.dvd_gcd_iff,
    Nat.gcd_ne_zero_right hN]

end GaloisForLFunctions.RHTower
