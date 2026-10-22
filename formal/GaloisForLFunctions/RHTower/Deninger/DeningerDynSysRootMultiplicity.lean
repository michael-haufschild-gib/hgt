import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysInseparableIdentification

/-!
# The root multiplicities of a minimal polynomial

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §1, the paragraph
before Proposition 1.3.

Over an algebraic closure `E` of `F` the minimal polynomial of `x` factors as

`(minpoly F x).map = ∏_{r} (X - r) ^ d_x`

where `r` runs over the distinct conjugates of `x` and `d_x` is the degree of inseparability.
This is proved from `(minpoly F x).map = (minpoly F^perf x) ^ d_x` together with the separability
of minimal polynomials over the perfect field `F^perf`: every root of the separable factor is
simple, so every root of the minimal polynomial has multiplicity exactly `d_x`.
-/

namespace RHTower

open Polynomial

variable {F : Type*} [Field F]

/-- Root multiplicities are multiplicative in powers. -/
theorem deningerRootMultiplicity_pow {K : Type*} [Field K] {p : Polynomial K} (hp : p ≠ 0)
    (n : ℕ) (r : K) : (p ^ n).rootMultiplicity r = n * p.rootMultiplicity r := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hne : p ^ n * p ≠ 0 := mul_ne_zero (pow_ne_zero n hp) hp
      rw [pow_succ, rootMultiplicity_mul hne, ih]
      ring

/-- **Deninger, §1.**  Every root of the minimal polynomial of `x` over `F`, taken in an
algebraic closure, has multiplicity exactly the degree of inseparability of `x`. -/
theorem deningerRootMultiplicity_minpoly_map {E : Type*} [Field E] [Algebra F E]
    [IsAlgClosed E] (q : ℕ) [ExpChar F q] {x : E} (hx : IsIntegral F x) {r : E}
    (hr : ((minpoly F x).map (algebraMap F E)).IsRoot r) :
    ((minpoly F x).map (algebraMap F E)).rootMultiplicity r = deningerInsepDegree F E q x := by
  classical
  set L := perfectClosure F E with hL
  set d := deningerInsepDegree F E q x with hd
  have hdpos : 0 < d := by
    rw [hd, deningerInsepDegree]
    exact pow_pos (expChar_pos F q) _
  have hLE : (minpoly F x).map (algebraMap F E)
      = ((minpoly L x).map (algebraMap L E)) ^ d := by
    have h := deningerMinpoly_map_perfectClosure_pow_insepDegree (F := F) (E := E) q hx
    have h2 := congrArg (fun p : Polynomial L => p.map (algebraMap L E)) h
    simp only [Polynomial.map_pow] at h2
    rw [← h2, Polynomial.map_map, ← IsScalarTower.algebraMap_eq F L E]
  have hxL : IsIntegral L x := hx.tower_top
  have hirr : Irreducible (minpoly L x) := minpoly.irreducible hxL
  haveI : PerfectField E := IsAlgClosed.perfectField E
  have hsep : (minpoly L x).Separable := PerfectField.separable_of_irreducible hirr
  have hsepE : ((minpoly L x).map (algebraMap L E)).Separable := hsep.map
  have hne : (minpoly L x).map (algebraMap L E) ≠ 0 := by
    intro h0
    have := hsepE
    rw [h0] at this
    exact (Polynomial.not_separable_zero) this
  have hroot : ((minpoly L x).map (algebraMap L E)).IsRoot r := by
    have : ((minpoly L x).map (algebraMap L E) ^ d).IsRoot r := by rw [← hLE]; exact hr
    rw [Polynomial.IsRoot, Polynomial.eval_pow, pow_eq_zero_iff hdpos.ne'] at this
    exact this
  have hone : ((minpoly L x).map (algebraMap L E)).rootMultiplicity r = 1 := by
    have hle : ((minpoly L x).map (algebraMap L E)).rootMultiplicity r ≤ 1 :=
      rootMultiplicity_le_one_of_separable hsepE r
    have hpos : 0 < ((minpoly L x).map (algebraMap L E)).rootMultiplicity r :=
      (Polynomial.rootMultiplicity_pos hne).2 hroot
    omega
  rw [hLE, deningerRootMultiplicity_pow hne d r, hone, mul_one]

end RHTower
