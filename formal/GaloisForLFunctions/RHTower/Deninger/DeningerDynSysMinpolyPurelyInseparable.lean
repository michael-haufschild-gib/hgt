/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3
(`t26n`), the polynomial correspondence.

The lower isomorphism of Proposition 1.3 rests on matching the normalized irreducible polynomials
over `κ₀` with those over the perfect closure `κ₀^perf`.  The precise relation is

  `(minpoly κ₀ x).map = (minpoly κ₀^perf x) ^ d`,

which is proved here for an arbitrary purely inseparable extension `L / F`.  Neither divisor is
constructed by hand:  `minpoly L x` divides `minpoly F x` over `L`, and conversely a high enough
`q`-power of `minpoly L x` has coefficients in `F` — the identity

  `p ^ q ^ n = expand L (q ^ n) (p.map (iterateFrobenius L q n))`

turns the coefficients into `q ^ n`-th powers — so `minpoly F x` divides that power.  Unique
factorization in `L[t]` and monicity then force the two divisibilities into an equality of a power.
-/
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Expand

namespace RHTower

open Polynomial

/-- In characteristic `q`, a `q^n`-th power of a polynomial is the `q^n`-fold expansion of its
`n`-fold Frobenius twist. -/
theorem deningerPow_eq_expand {L : Type*} [Field L] (q : ℕ) [ExpChar L q] (n : ℕ)
    (p : Polynomial L) :
    p ^ q ^ n = Polynomial.expand L (q ^ n) (p.map (iterateFrobenius L q n)) := by
  induction n generalizing p with
  | zero =>
      have h0 : iterateFrobenius L q 0 = RingHom.id L := by
        ext x
        simp
      simp [h0]
  | succ n ih =>
      have hbase : ∀ r : Polynomial L,
          r ^ q = Polynomial.expand L q (r.map (frobenius L q)) := by
        intro r
        rw [← Polynomial.map_expand, Polynomial.map_frobenius_expand]
      have hcomp : (frobenius L q).comp (iterateFrobenius L q n) = iterateFrobenius L q (n + 1) := by
        ext x
        simp only [RingHom.coe_comp, Function.comp_apply, iterateFrobenius_def, frobenius_def]
        rw [← pow_mul, ← pow_succ]
      calc p ^ q ^ (n + 1) = (p ^ q ^ n) ^ q := by rw [← pow_mul, ← pow_succ]
        _ = Polynomial.expand L q ((p ^ q ^ n).map (frobenius L q)) := hbase _
        _ = Polynomial.expand L q
              ((Polynomial.expand L (q ^ n) (p.map (iterateFrobenius L q n))).map
                (frobenius L q)) := by rw [ih]
        _ = Polynomial.expand L q (Polynomial.expand L (q ^ n)
              ((p.map (iterateFrobenius L q n)).map (frobenius L q))) := by
              rw [Polynomial.map_expand]
        _ = Polynomial.expand L (q * q ^ n) (p.map ((frobenius L q).comp
              (iterateFrobenius L q n))) := by rw [Polynomial.expand_expand, Polynomial.map_map]
        _ = Polynomial.expand L (q ^ (n + 1)) (p.map (iterateFrobenius L q (n + 1))) := by
              rw [hcomp, ← pow_succ']

/-- **Deninger, Proposition 1.3 (`t26n`), the polynomial correspondence.**  Over a purely
inseparable extension `L / F`, the minimal polynomial over `F` of an element of an `L`-algebra is
a power of its minimal polynomial over `L`:  `α = α̃ ^ d`.  This is the relation between the
normalized irreducible polynomials over `κ₀` and over `κ₀^perf` used in the source. -/
theorem deningerMinpoly_map_eq_pow {F L E : Type*} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [IsPurelyInseparable F L] (q : ℕ) [ExpChar F q] (x : E) (hx : IsIntegral F x) :
    ∃ k : ℕ, 0 < k ∧ (minpoly F x).map (algebraMap F L) = (minpoly L x) ^ k := by
  classical
  haveI : ExpChar L q := expChar_of_injective_ringHom (algebraMap F L).injective q
  have hqpos : 0 < q := expChar_pos F q
  have hxL : IsIntegral L x := hx.tower_top
  have hpmonic : (minpoly L x).Monic := minpoly.monic hxL
  have hpirr : Irreducible (minpoly L x) := minpoly.irreducible hxL
  have hdvd1 : minpoly L x ∣ (minpoly F x).map (algebraMap F L) :=
    minpoly.dvd_map_of_isScalarTower F L x
  -- every element of `L` has a `q`-power in `F`
  have hpow : ∀ c : L, ∃ m : ℕ, c ^ q ^ m ∈ (algebraMap F L).range :=
    (isPurelyInseparable_iff_pow_mem F q).1 inferInstance
  choose m hm using hpow
  set n : ℕ := (minpoly L x).support.sup (fun i => m ((minpoly L x).coeff i)) with hn
  have hcoeff : ∀ i, (minpoly L x).coeff i ^ q ^ n ∈ (algebraMap F L).range := by
    intro i
    by_cases hi : i ∈ (minpoly L x).support
    · have hle : m ((minpoly L x).coeff i) ≤ n := by
        rw [hn]
        exact Finset.le_sup (f := fun i => m ((minpoly L x).coeff i)) hi
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      have := hm ((minpoly L x).coeff i)
      obtain ⟨a, ha⟩ := this
      refine ⟨a ^ q ^ d, ?_⟩
      rw [map_pow, ha, ← pow_mul, ← pow_add, ← hd]
    · rw [Polynomial.notMem_support_iff.1 hi, zero_pow (by positivity)]
      exact ⟨0, map_zero _⟩
  have hlift : (minpoly L x) ^ q ^ n ∈ Polynomial.lifts (algebraMap F L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro j
    rw [deningerPow_eq_expand q n, Polynomial.coeff_expand (pow_pos hqpos n)]
    by_cases hj : q ^ n ∣ j
    · rw [if_pos hj, Polynomial.coeff_map]
      simpa [iterateFrobenius_def] using hcoeff (j / q ^ n)
    · rw [if_neg hj]
      exact ⟨0, map_zero _⟩
  obtain ⟨R, hR⟩ := (Polynomial.mem_lifts _).1 hlift
  have hRmonic : R.Monic := by
    have hmap : (R.map (algebraMap F L)).Monic := by
      rw [hR]
      exact hpmonic.pow _
    have hdeg : (R.map (algebraMap F L)).natDegree = R.natDegree :=
      Polynomial.natDegree_map_eq_of_injective (algebraMap F L).injective R
    have hlead : (algebraMap F L) R.leadingCoeff = 1 := by
      have := hmap
      rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg, Polynomial.coeff_map] at this
      exact this
    have : (algebraMap F L) R.leadingCoeff = (algebraMap F L) 1 := by rw [hlead, map_one]
    exact (algebraMap F L).injective this
  have hRaeval : (Polynomial.aeval x) R = 0 := by
    have h1 : (Polynomial.aeval x) (R.map (algebraMap F L)) = 0 := by
      rw [hR, map_pow, minpoly.aeval, zero_pow (pow_pos hqpos n).ne']
    rwa [Polynomial.aeval_map_algebraMap] at h1
  have hdvd2 : (minpoly F x).map (algebraMap F L) ∣ (minpoly L x) ^ q ^ n := by
    rw [← hR]
    exact Polynomial.map_dvd _ (minpoly.dvd F x hRaeval)
  obtain ⟨k, -, hassoc⟩ := (dvd_prime_pow hpirr.prime (q ^ n)).1 hdvd2
  have heq : (minpoly F x).map (algebraMap F L) = (minpoly L x) ^ k :=
    Polynomial.eq_of_monic_of_associated
      ((minpoly.monic hx).map _) (hpmonic.pow _) hassoc
  refine ⟨k, ?_, heq⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk, pow_zero] at heq
    rw [heq] at hdvd1
    exact absurd (isUnit_of_dvd_one hdvd1) hpirr.not_isUnit
  · exact hk

/-- **Deninger, Proposition 1.3 (`t26n`), specialised to the perfect closure.**  For `x`
algebraic over `κ₀`, the minimal polynomial over `κ₀` is a power of the minimal polynomial over
the perfect closure `κ₀^perf`; this is the relation `α = α̃ ^ d` matching normalized irreducible
polynomials over `κ₀` with those over `κ₀^perf`. -/
theorem deningerMinpoly_map_perfectClosure_eq_pow {F E : Type*} [Field F] [Field E] [Algebra F E]
    (q : ℕ) [ExpChar F q] (x : E) (hx : IsIntegral F x) :
    ∃ k : ℕ, 0 < k ∧ (minpoly F x).map (algebraMap F (perfectClosure F E))
      = (minpoly (perfectClosure F E) x) ^ k :=
  deningerMinpoly_map_eq_pow q x hx

end RHTower
