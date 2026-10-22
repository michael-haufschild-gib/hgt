/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3
(`t26n`): the exponent of the correspondence **is** the degree of inseparability.

`DeningerDynSysInseparableExponent` writes `(minpoly κ₀ x).map = (minpoly κ₀^perf x) ^ q ^ m`,
where `expand κ₀ (q ^ m) g = minpoly κ₀ x` is the separable contraction.  Here `q ^ m` is
identified with `d_x = q ^ n_x`, the degree of inseparability of `DeningerDynSysInseparableDegree`:
contracting the expansion computes `minpoly κ₀ (x ^ q ^ j) = expand κ₀ (q ^ (m - j)) g` for
`j ≤ m`, which is separable exactly when `j = m` (`isUnit_or_eq_zero_of_separable_expand`), so `m`
is the least admissible exponent.  In characteristic zero both sides are `1`.
-/
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysInseparableExponent
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysInseparableDegree

namespace RHTower

open Polynomial

variable {F : Type*} [Field F]

/-- Contracting the expansion of a minimal polynomial computes the minimal polynomial of a
`q`-power. -/
theorem deningerMinpoly_pow_expand {E : Type*} [Field E] [Algebra F E] (q : ℕ) [ExpChar F q]
    {x : E} (hx : IsIntegral F x) {m : ℕ} {g : Polynomial F}
    (hgexp : Polynomial.expand F (q ^ m) g = minpoly F x) {n : ℕ} (hnm : n ≤ m) :
    minpoly F (x ^ q ^ n) = Polynomial.expand F (q ^ (m - n)) g := by
  have hqpos : 0 < q := expChar_pos F q
  have hsplit : Polynomial.expand F (q ^ n) (Polynomial.expand F (q ^ (m - n)) g)
      = minpoly F x := by
    rw [Polynomial.expand_expand, ← pow_add, show n + (m - n) = m by omega]
    exact hgexp
  have hirr : Irreducible (Polynomial.expand F (q ^ (m - n)) g) :=
    deningerIrreducible_of_expand (pow_pos hqpos n) (by rw [hsplit]; exact minpoly.irreducible hx)
  have hgmonic : g.Monic := by
    have hm := minpoly.monic hx
    rw [← hgexp, Polynomial.Monic, Polynomial.leadingCoeff_expand (pow_pos hqpos m)] at hm
    exact hm
  have hmonic : (Polynomial.expand F (q ^ (m - n)) g).Monic :=
    hgmonic.expand (pow_pos hqpos _)
  have haeval : (Polynomial.aeval (x ^ q ^ n)) (Polynomial.expand F (q ^ (m - n)) g) = 0 := by
    rw [Polynomial.expand_aeval, ← pow_mul, ← pow_add, show n + (m - n) = m by omega,
      ← Polynomial.expand_aeval, hgexp]
    exact minpoly.aeval F x
  have hint : IsIntegral F (x ^ q ^ n) := ⟨_, hmonic, haeval⟩
  exact Polynomial.eq_of_monic_of_associated (minpoly.monic hint) hmonic
    ((minpoly.irreducible hint).associated_of_dvd hirr (minpoly.dvd F _ haeval))

/-- In a field of prime exponential characteristic the characteristic equals it. -/
theorem deningerCharP_of_expChar_prime (F : Type*) [Field F] (q : ℕ) [hq : ExpChar F q]
    (hqp : q.Prime) : CharP F q := by
  obtain ⟨p, hp⟩ := CharP.exists F
  haveI := hp
  have hpp : p.Prime := by
    rcases CharP.char_is_prime_or_zero F p with h | h
    · exact h
    · subst h
      have h1 := expChar_one_of_char_zero F q
      exact absurd h1 hqp.ne_one
  have hpq : p = q := (char_eq_expChar_iff F p q).2 hpp
  exact hpq ▸ hp

/-- **Deninger, Proposition 1.3 (`t26n`): the exponent is the degree of inseparability.**  The
exponent in `(minpoly κ₀ x).map = (minpoly κ₀^perf x) ^ d` is exactly `d_x = q ^ n_x`, the degree
of inseparability of `x` over `κ₀`. -/
theorem deningerMinpoly_map_perfectClosure_pow_insepDegree {E : Type*} [Field E] [Algebra F E]
    [IsAlgClosed E] (q : ℕ) [ExpChar F q] {x : E} (hx : IsIntegral F x) :
    (minpoly F x).map (algebraMap F (perfectClosure F E))
      = (minpoly (perfectClosure F E) x) ^ deningerInsepDegree F E q x := by
  classical
  have hqpos : 0 < q := expChar_pos F q
  obtain ⟨m, g, hgsep, hgexp, heq⟩ :=
    deningerMinpoly_map_perfectClosure_eq_pow_expChar (F := F) (E := E) q hx
  rcases expChar_is_prime_or_one F q with hqp | hq1
  · haveI : CharP F q := deningerCharP_of_expChar_prime F q hqp
    have hgmonic : g.Monic := by
      have hm := minpoly.monic hx
      rw [← hgexp, Polynomial.Monic, Polynomial.leadingCoeff_expand (pow_pos hqpos m)] at hm
      exact hm
    have hgirr : Irreducible g :=
      deningerIrreducible_of_expand (pow_pos hqpos m)
        (by rw [hgexp]; exact minpoly.irreducible hx)
    have hmemm : m ∈ deningerInsepExpSet F E q x := by
      rw [deningerMem_insepExpSet_iff, mem_separableClosure_iff, IsSeparable,
        deningerMinpoly_pow_expand q hx hgexp (le_refl m), Nat.sub_self, pow_zero,
        Polynomial.expand_one]
      exact hgsep
    have hminimal : ∀ j ∈ deningerInsepExpSet F E q x, m ≤ j := by
      intro j hj
      by_contra hlt
      rw [Nat.not_le] at hlt
      rw [deningerMem_insepExpSet_iff, mem_separableClosure_iff, IsSeparable,
        deningerMinpoly_pow_expand q hx hgexp (le_of_lt hlt)] at hj
      rcases Polynomial.isUnit_or_eq_zero_of_separable_expand (p := q) (m - j) hqpos hj with
        hu | h0
      · exact hgirr.not_isUnit hu
      · omega
    have hexpeq : deningerInsepExp F E q x = m :=
      le_antisymm (deningerInsepExp_le hmemm) (hminimal _ (Nat.sInf_mem ⟨m, hmemm⟩))
    rw [deningerInsepDegree, hexpeq]
    exact heq
  · subst hq1
    rw [deningerInsepDegree, one_pow, pow_one, heq, one_pow, pow_one]

end RHTower
