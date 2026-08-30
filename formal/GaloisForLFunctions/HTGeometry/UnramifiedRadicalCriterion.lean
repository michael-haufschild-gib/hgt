import Mathlib

/-!
# The codimension-one condition of a radical extension

A radical extension `z^r = a` is unramified at a prime exactly when that prime's multiplicity in `a`
is divisible by `r`.  This file proves the direction the Kummer classification consumes: if a
discrete valuation upstairs sees the prime exactly once — that is, the extension is unramified there
— and an `r`-th root of `p^k · b` exists with `b` a unit at that place, then `r ∣ k`.

The proof is one application of multiplicativity: `r · w(z) = w(a) = k`.  Together with
`UfdPowerDescent.exists_unit_mul_pow_torus_kummer` this classifies the everywhere-unramified cyclic
radical extensions of a unique factorisation domain whose units are a constant times two monomial
exponents: the radicand is a unit times an `r`-th power, and the cover is trivial exactly when both
of the unit's torus exponents are divisible by `r`.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing

/-- **The unramified radical criterion.**  If a discrete valuation `w` sees the prime `p` exactly
once, sees the cofactor `b` not at all, and an `r`-th root of `p^k · b` exists in the valuation ring,
then `r` divides `k`.  This is the codimension-one condition of a radical extension: a radical
extension `z^r = a` is unramified at a prime exactly when that prime's multiplicity in `a` is
divisible by `r`. -/
theorem dvd_of_addVal_pow_mul_unit
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {p b : B} {k r : ℕ} {z : B}
    (hp : addVal B p = 1) (hb : addVal B b = 0)
    (hz : z ^ r = p ^ k * b) :
    r ∣ k := by
  have hval : addVal B (z ^ r) = addVal B (p ^ k * b) := by rw [hz]
  rw [AddValuation.map_pow, AddValuation.map_mul, AddValuation.map_pow, hp, hb] at hval
  simp only [add_zero, nsmul_eq_mul, mul_one] at hval
  rcases eq_or_ne (addVal B z) (⊤ : ℕ∞) with htop | hfin
  · rw [htop] at hval
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · refine ⟨0, ?_⟩
      have : (0 : ℕ∞) = (k : ℕ∞) := by simpa using hval
      have hk : k = 0 := by exact_mod_cast this.symm
      omega
    · have hrne : (r : ℕ∞) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        omega
      have htopmul : (r : ℕ∞) * (⊤ : ℕ∞) = ⊤ := ENat.mul_top hrne
      rw [htopmul] at hval
      exact absurd hval (by simp)
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℕ∞) = addVal B z := ENat.ne_top_iff_exists.mp hfin
    rw [← hm] at hval
    have hcast : ((r * m : ℕ) : ℕ∞) = ((k : ℕ) : ℕ∞) := by
      rw [← hval]; push_cast; ring
    have hk : r * m = k := by exact_mod_cast hcast
    exact ⟨m, hk.symm⟩

/-- **The unramified radical criterion, base-ring form.**  If the valuation of the base ring's prime
is one, every element prime to it is a unit, and the radicand `p^k · b` has an `r`-th root upstairs,
then `r ∣ k`. -/
theorem dvd_of_radical_root_of_unramified
    {R : Type*} [CommRing R] {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra R B] {p a b : R} {k r : ℕ} {z : B}
    (hp : addVal B (algebraMap R B p) = 1)
    (hb : addVal B (algebraMap R B b) = 0)
    (hfac : a = p ^ k * b)
    (hz : z ^ r = algebraMap R B a) :
    r ∣ k := by
  refine dvd_of_addVal_pow_mul_unit (p := algebraMap R B p) (b := algebraMap R B b)
    (z := z) hp hb ?_
  rw [hz, hfac, map_mul, map_pow]

/-- The ramification obstruction is sharp: if `r` does not divide the multiplicity, no `r`-th root
of the radicand exists in an unramified extension. -/
theorem not_exists_radical_root_of_not_dvd
    {R : Type*} [CommRing R] {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra R B] {p a b : R} {k r : ℕ}
    (hp : addVal B (algebraMap R B p) = 1)
    (hb : addVal B (algebraMap R B b) = 0)
    (hfac : a = p ^ k * b)
    (hnd : ¬ r ∣ k) :
    ¬ ∃ z : B, z ^ r = algebraMap R B a := by
  rintro ⟨z, hz⟩
  exact hnd (dvd_of_radical_root_of_unramified hp hb hfac hz)


end GaloisForLFunctions.HTGeometry
