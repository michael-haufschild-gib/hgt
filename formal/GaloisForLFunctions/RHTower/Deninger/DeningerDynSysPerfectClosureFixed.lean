/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3
(`t26n`), top row.

`κ^H = κ₀^perf` for `κ` an algebraic closure of `κ₀` and `H = Aut_{κ₀}(κ)`, and consequently

  `W_rat (κ)^H = W_rat (κ₀^perf)`.

An element of an algebraic closure fixed by every automorphism has a minimal polynomial with a
single root — any other root is a Galois conjugate (`minpoly.exists_algEquiv_of_root`, using that
an algebraic closure is normal) — hence lies in the perfect closure; conversely a purely
inseparable element is fixed because the Frobenius is injective.  The Witt-level statement is then
Proposition 1.2(b) for the integrally closed domain `κ`.
-/
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Perfect
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysWittFunctoriality
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysWittGaloisIntegrallyClosed

namespace RHTower

open Polynomial

variable (F E : Type*) [Field F] [Field E] [Algebra F E] [IsAlgClosure F E]

/-- **The fixed field of the full automorphism group of an algebraic closure is the perfect
closure.**  An element of an algebraic closure of `F` is fixed by every `F`-automorphism exactly
when it is purely inseparable over `F`. -/
theorem deningerMem_perfectClosure_iff_fixed (x : E) :
    x ∈ perfectClosure F E ↔ ∀ σ : E ≃ₐ[F] E, σ x = x := by
  classical
  haveI : Algebra.IsAlgebraic F E := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed E := IsAlgClosure.isAlgClosed F
  haveI hq : ExpChar F (ringExpChar F) := ringExpChar.expChar F
  haveI : ExpChar E (ringExpChar F) :=
    expChar_of_injective_ringHom (algebraMap F E).injective (ringExpChar F)
  constructor
  · intro hx σ
    obtain ⟨n, a, ha⟩ := (mem_perfectClosure_iff_pow_mem (ringExpChar F)).1 hx
    have hpow : (σ x) ^ (ringExpChar F) ^ n = x ^ (ringExpChar F) ^ n := by
      rw [← map_pow, ← ha, AlgEquiv.commutes]
    have hinj : Function.Injective (fun y : E => y ^ (ringExpChar F) ^ n) := by
      intro y z h
      refine (frobenius_inj E (ringExpChar F)).iterate n ?_
      simpa [iterate_frobenius] using h
    exact hinj hpow
  · intro hfix
    rw [mem_perfectClosure_iff_natSepDegree_eq_one, Polynomial.natSepDegree_eq_of_isAlgClosed E]
    have hne : minpoly F x ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)
    have hxmem : x ∈ (minpoly F x).aroots E := by
      rw [Polynomial.mem_aroots]
      exact ⟨hne, minpoly.aeval F x⟩
    have hall : ∀ y ∈ (minpoly F x).aroots E, y = x := by
      intro y hy
      have hy' : (Polynomial.aeval y) (minpoly F x) = 0 := (Polynomial.mem_aroots.1 hy).2
      obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (K := F) (L := E)
        (Algebra.IsAlgebraic.isAlgebraic x) hy'
      exact σ.injective (hσ.trans (hfix σ).symm)
    have hsingleton : ((minpoly F x).aroots E).toFinset = {x} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
      · simpa using hxmem
      · intro y hy
        exact hall y (Multiset.mem_toFinset.1 hy)
    rw [hsingleton, Finset.card_singleton]

/-- **Deninger, Proposition 1.3 (`t26n`), first input.**  For an algebraic closure `E` of `F`, the
fixed subring of the full automorphism group is the perfect closure of `F` in `E`. -/
theorem deningerFixedPoints_eq_perfectClosure :
    FixedPoints.subring E (E ≃ₐ[F] E) = (perfectClosure F E).toSubring := by
  ext x
  constructor
  · intro hx
    exact (deningerMem_perfectClosure_iff_fixed F E x).2 (fun σ => hx σ)
  · intro hx
    exact fun σ => (deningerMem_perfectClosure_iff_fixed F E x).1 hx σ

open scoped DeningerWittRing in
/-- **Deninger, Proposition 1.3 (`t26n`), top row.**  `W_rat (κ) ^ H = W_rat (κ₀^perf)` for
`κ` an algebraic closure of `κ₀` and `H = Aut_{κ₀} (κ)`:  every `H`-invariant rational Witt vector
over `κ` comes from a rational Witt vector over the perfect closure. -/
theorem deningerWittRing_fixed_eq_perfectClosure (w : DeningerCanonicalRationalWittRing E)
    (hw : ∀ σ : E ≃ₐ[F] E, σ • w = w) :
    ∃ w₀ : DeningerCanonicalRationalWittRing (perfectClosure F E),
      deningerCanonicalRationalWittMap
        (algebraMap (perfectClosure F E) E) w₀ = w := by
  obtain ⟨w₀, hw₀⟩ :=
    deningerWittRing_galoisDescent_integrallyClosed (G := E ≃ₐ[F] E) (A := E) w hw
  refine ⟨deningerCanonicalRationalWittMap
    (RingEquiv.subringCongr (deningerFixedPoints_eq_perfectClosure F E)).toRingHom w₀, ?_⟩
  rw [← deningerCanonicalRationalWittMap_comp]
  have hcomp : (algebraMap (perfectClosure F E) E).comp
      (RingEquiv.subringCongr (deningerFixedPoints_eq_perfectClosure F E)).toRingHom
      = algebraMap (FixedPoints.subring E (E ≃ₐ[F] E)) E := by
    ext y
    rfl
  rw [hcomp]
  exact hw₀

end RHTower
