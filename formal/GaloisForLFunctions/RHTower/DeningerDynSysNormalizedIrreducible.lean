/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3
(`t26n`), normalization.

Rational Witt vectors are normalized fractions `P / Q` with `P(0) = Q(0) = 1`, so the relevant
factorization of `F[t]` is into **normalized** irreducibles, whereas mathlib normalizes by making
polynomials monic.  Reversal `p ↦ p.reverse` is the bridge: it is multiplicative on a domain, an
involution on polynomials with nonzero constant coefficient, preserves degree and unit-hood there,
and therefore matches normalized irreducibles with monic ones (the monic irreducible `X` being the
sole exception, as it has constant coefficient zero).

The file closes with the other half of the dictionary: over an algebraically closed extension,
every monic irreducible polynomial is the minimal polynomial of one of its roots.
-/
import GaloisForLFunctions.RHTower.DeningerDynSysWittGaloisIntegrallyClosed

namespace RHTower

open Polynomial

variable {F : Type*} [Field F]

theorem deningerReverse_natDegree {p : Polynomial F} (h : p.coeff 0 ≠ 0) :
    p.reverse.natDegree = p.natDegree := by
  refine le_antisymm (Polynomial.reverse_natDegree_le p) (Polynomial.le_natDegree_of_ne_zero ?_)
  rw [Polynomial.coeff_reverse, Polynomial.revAt_le le_rfl, Nat.sub_self]
  exact h

theorem deningerReverse_coeff_zero (p : Polynomial F) :
    p.reverse.coeff 0 = p.leadingCoeff := by
  rw [Polynomial.coeff_reverse, Polynomial.revAt_le (Nat.zero_le _), Nat.sub_zero]
  rfl

/-- Reversal is an involution on polynomials with nonzero constant coefficient. -/
theorem deningerReverse_reverse {p : Polynomial F} (h : p.coeff 0 ≠ 0) :
    p.reverse.reverse = p := by
  ext n
  rw [Polynomial.coeff_reverse, Polynomial.coeff_reverse, deningerReverse_natDegree h,
    Polynomial.revAt_invol]

theorem deningerReverse_ne_zero {p : Polynomial F} (h : p.coeff 0 ≠ 0) : p.reverse ≠ 0 := by
  intro hz
  apply h
  have := deningerReverse_reverse h
  rw [hz] at this
  rw [← this]
  simp

/-- Reversal preserves being a unit, for polynomials with nonzero constant coefficient. -/
theorem deningerIsUnit_reverse_iff {p : Polynomial F} (h : p.coeff 0 ≠ 0) :
    IsUnit p.reverse ↔ IsUnit p := by
  have hpne : p ≠ 0 := fun hp => h (by rw [hp, Polynomial.coeff_zero])
  have hrne : p.reverse ≠ 0 := deningerReverse_ne_zero h
  rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.isUnit_iff_degree_eq_zero,
    Polynomial.degree_eq_natDegree hrne, Polynomial.degree_eq_natDegree hpne,
    deningerReverse_natDegree h]

/-- **Normalized versus monic irreducibility.**  Reversal matches irreducible polynomials with
nonzero constant coefficient with irreducible polynomials of the same degree; applied to a
polynomial with constant coefficient one it matches the normalized irreducibles of `F[t]` with the
monic ones. -/
theorem deningerIrreducible_reverse {p : Polynomial F} (h : p.coeff 0 ≠ 0)
    (hirr : Irreducible p) : Irreducible p.reverse := by
  refine ⟨fun hu => hirr.not_isUnit ((deningerIsUnit_reverse_iff h).1 hu), ?_⟩
  intro a b hab
  have hlead : p.reverse.coeff 0 ≠ 0 := by
    rw [deningerReverse_coeff_zero]
    exact Polynomial.leadingCoeff_ne_zero.2 (fun hp => h (by rw [hp, Polynomial.coeff_zero]))
  have hab0 : a.coeff 0 * b.coeff 0 ≠ 0 := by
    rw [← Polynomial.mul_coeff_zero, ← hab]
    exact hlead
  have ha0 : a.coeff 0 ≠ 0 := left_ne_zero_of_mul hab0
  have hb0 : b.coeff 0 ≠ 0 := right_ne_zero_of_mul hab0
  have hp : p = a.reverse * b.reverse := by
    rw [← Polynomial.reverse_mul_of_domain, ← hab, deningerReverse_reverse h]
  rcases hirr.isUnit_or_isUnit hp with hu | hu
  · exact Or.inl ((deningerIsUnit_reverse_iff ha0).1 hu)
  · exact Or.inr ((deningerIsUnit_reverse_iff hb0).1 hu)

theorem deningerIrreducible_reverse_iff {p : Polynomial F} (h : p.coeff 0 ≠ 0) :
    Irreducible p.reverse ↔ Irreducible p := by
  refine ⟨fun hirr => ?_, deningerIrreducible_reverse h⟩
  have hlead : p.reverse.coeff 0 ≠ 0 := by
    rw [deningerReverse_coeff_zero]
    exact Polynomial.leadingCoeff_ne_zero.2 (fun hp => h (by rw [hp, Polynomial.coeff_zero]))
  have := deningerIrreducible_reverse hlead hirr
  rwa [deningerReverse_reverse h] at this

/-- **Every monic irreducible polynomial is a minimal polynomial.**  Over an algebraically closed
extension every monic irreducible polynomial of `F[t]` is the minimal polynomial of one of its
roots. -/
theorem deningerExists_minpoly_eq {E : Type*} [Field E] [Algebra F E] [IsAlgClosed E]
    {q : Polynomial F} (hm : q.Monic) (hirr : Irreducible q) :
    ∃ x : E, minpoly F x = q := by
  have hqdeg : q.degree ≠ 0 := fun hd =>
    hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 hd)
  have hdeg : (q.map (algebraMap F E)).degree ≠ 0 := by
    rw [hm.degree_map]
    exact hqdeg
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
  have haeval : (Polynomial.aeval x) q = 0 := by
    have hx' := hx
    rw [Polynomial.IsRoot, Polynomial.eval_map] at hx'
    exact hx'
  have hint : IsIntegral F x := ⟨q, hm, haeval⟩
  refine ⟨x, Polynomial.eq_of_monic_of_associated (minpoly.monic hint) hm ?_⟩
  exact (minpoly.irreducible hint).associated_of_dvd hirr (minpoly.dvd F x haeval)

end RHTower
