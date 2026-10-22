import GaloisForLFunctions.RHTower.Sieve.VinogradovPowerSumRigidity
import Mathlib.Algebra.Field.ZMod

/-!
# Newton identities and Linnik lifting for power sums modulo p^k

If two families in a commutative ring have the same power sums of orders `1..b` and the integers
`1, ..., b` are units, Newton's identities force equal elementary symmetric functions, hence equal
monic polynomials `∏ (X - x_i)`. Over `ZMod (p^k)` with `k < p`, for `k`-tuples whose reductions
modulo `p` are distinct, this gives Linnik's lifting lemma: equal power sums of orders `1..k`
modulo `p^k` force the two tuples to be permutations of each other.

## Main results

- `esymm_eq_of_powerSums_eq_of_isUnit`: equal power sums of orders `1..b`, with `1, ..., b` units,
  give equal elementary symmetric polynomials `e_j` for `j ≤ b`.
- `polynomial_prod_eq_of_powerSums_eq_of_isUnit`: under the same hypotheses,
  `∏ (X - x_i) = ∏ (X - y_i)`.
- `zmod_multiset_eq_of_powerSums_eq`: for a prime `p` with `k < p`, `k`-tuples in `ZMod (p^k)` that
  are injective modulo `p` and have equal power sums of orders `1..k` agree as multisets.

## Hypotheses

Unconditional. The algebraic statements assume equal power sums and that `1, ..., b` are units; the
modular statement assumes `p` prime, `k < p`, and that both tuples are injective modulo `p`.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- Newton's identities: if `∑ x_i^j = ∑ y_i^j` for `1 ≤ j ≤ b` and each `j ≤ b` is a unit in `R`,
then `e_j(x) = e_j(y)` for all `j ≤ b`. -/
theorem esymm_eq_of_powerSums_eq_of_isUnit
    {R : Type*} [CommRing R] {b : ℕ} (x y : Fin b → R)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ b →
      ∑ i : Fin b, x i ^ j = ∑ i : Fin b, y i ^ j)
    (hunit : ∀ j : ℕ, 1 ≤ j → j ≤ b → IsUnit (j : R)) :
    ∀ j : ℕ, j ≤ b →
      (Finset.univ.val.map x).esymm j =
        (Finset.univ.val.map y).esymm j := by
  intro j hj
  induction j using Nat.strong_induction_on with
  | h j ih =>
      by_cases hj0 : j = 0
      · subst j
        simp [Multiset.esymm]
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hnewton := MvPolynomial.mul_esymm_eq_sum (Fin b) R j
      have hx := congrArg (MvPolynomial.aeval x) hnewton
      have hy := congrArg (MvPolynomial.aeval y) hnewton
      have hpsum (z : Fin b → R) (m : ℕ) :
          MvPolynomial.aeval z (MvPolynomial.psum (Fin b) R m) =
            ∑ i : Fin b, z i ^ m := by
        simp [MvPolynomial.psum]
      simp only [map_mul, map_natCast, MvPolynomial.aeval_esymm_eq_multiset_esymm,
        map_pow, map_neg, map_one, map_sum] at hx hy
      simp_rw [hpsum] at hx hy
      have hsum :
          (∑ a ∈ Finset.antidiagonal j with a.1 < j,
              (-1 : R) ^ a.1 * (Finset.univ.val.map x).esymm a.1 *
                (∑ i : Fin b, x i ^ a.2)) =
            ∑ a ∈ Finset.antidiagonal j with a.1 < j,
              (-1 : R) ^ a.1 * (Finset.univ.val.map y).esymm a.1 *
                (∑ i : Fin b, y i ^ a.2) := by
        apply Finset.sum_congr rfl
        intro a ha
        have ha' := Finset.mem_filter.mp ha
        have hadd := Finset.mem_antidiagonal.mp ha'.1
        have ha1 : a.1 < j := ha'.2
        have ha2pos : 1 ≤ a.2 := by omega
        have ha2le : a.2 ≤ b := by omega
        rw [ih a.1 ha1 (by omega), hpower a.2 ha2pos ha2le]
      rw [hsum] at hx
      have hmul : (j : R) * (Finset.univ.val.map x).esymm j =
          (j : R) * (Finset.univ.val.map y).esymm j := hx.trans hy.symm
      exact (hunit j hjpos hj).mul_left_cancel hmul

/-- If `∑ x_i^j = ∑ y_i^j` for `1 ≤ j ≤ b` and `1, ..., b` are units, then
`∏ (X - x_i) = ∏ (X - y_i)`. -/
theorem polynomial_prod_eq_of_powerSums_eq_of_isUnit
    {R : Type*} [CommRing R] {b : ℕ} (x y : Fin b → R)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ b →
      ∑ i : Fin b, x i ^ j = ∑ i : Fin b, y i ^ j)
    (hunit : ∀ j : ℕ, 1 ≤ j → j ≤ b → IsUnit (j : R)) :
    ((Finset.univ.val.map x).map fun a => Polynomial.X - Polynomial.C a).prod =
      ((Finset.univ.val.map y).map fun a => Polynomial.X - Polynomial.C a).prod := by
  rw [Multiset.prod_X_sub_X_eq_sum_esymm,
    Multiset.prod_X_sub_X_eq_sum_esymm]
  simp only [Multiset.card_map]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ b := by simpa using hj
  rw [esymm_eq_of_powerSums_eq_of_isUnit x y hpower hunit j hjle]

private theorem isUnit_finset_prod
    {R : Type*} [CommMonoid R] {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → R}
    (h : ∀ i ∈ s, IsUnit (f i)) : IsUnit (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Linnik lifting: for a prime `p` with `k < p`, two `k`-tuples in `ZMod (p^k)` with distinct
reductions modulo `p` and equal power sums of orders `1..k` are equal as multisets. -/
theorem zmod_multiset_eq_of_powerSums_eq
    {p k : ℕ} (hp : p.Prime) (hkp : k < p)
    (x y : Fin k → ZMod (p ^ k))
    (hx : Function.Injective fun i => ((x i).cast : ZMod p))
    (hy : Function.Injective fun i => ((y i).cast : ZMod p))
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i : Fin k, x i ^ j = ∑ i : Fin k, y i ^ j) :
    Finset.univ.val.map x = Finset.univ.val.map y := by
  by_cases hk0 : k = 0
  · subst k
    simp
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  have hp_dvd : p ∣ p ^ k := dvd_pow_self p hk0
  let castp : ZMod (p ^ k) →+* ZMod p := ZMod.castHom hp_dvd (ZMod p)
  have hunit : ∀ j : ℕ, 1 ≤ j → j ≤ k → IsUnit (j : ZMod (p ^ k)) := by
    intro j hjpos hjk
    rw [ZMod.isUnit_iff_coprime]
    have hjp : j < p := lt_of_le_of_lt hjk hkp
    have hnot : ¬ p ∣ j := Nat.not_dvd_of_pos_of_lt (by omega) hjp
    exact ((hp.coprime_iff_not_dvd.mpr hnot).symm).pow_right k
  have hpoly := polynomial_prod_eq_of_powerSums_eq_of_isUnit x y hpower hunit
  have hmatch : ∀ s : Fin k, ∃ i : Fin k, y s = x i := by
    intro s
    have hprod : ∏ i : Fin k, (y s - x i) = 0 := by
      calc
        ∏ i : Fin k, (y s - x i) =
            Polynomial.eval (y s)
              (((Finset.univ.val.map x).map fun a =>
                Polynomial.X - Polynomial.C a).prod) := by
              change (∏ i : Fin k, (y s - x i)) =
                (Polynomial.evalRingHom (y s))
                  (((Finset.univ.val.map x).map fun a =>
                    Polynomial.X - Polynomial.C a).prod)
              rw [map_multiset_prod]
              simp only [Multiset.map_map, Function.comp_apply,
                Polynomial.coe_evalRingHom, Polynomial.eval_sub,
                Polynomial.eval_X, Polynomial.eval_C]
              rw [Finset.prod_map_val]
        _ = Polynomial.eval (y s)
              (((Finset.univ.val.map y).map fun a =>
                Polynomial.X - Polynomial.C a).prod) :=
              congrArg (Polynomial.eval (y s)) hpoly
        _ = ∏ i : Fin k, (y s - y i) := by
              change (Polynomial.evalRingHom (y s))
                  (((Finset.univ.val.map y).map fun a =>
                    Polynomial.X - Polynomial.C a).prod) =
                ∏ i : Fin k, (y s - y i)
              rw [map_multiset_prod]
              simp only [Multiset.map_map, Function.comp_apply,
                Polynomial.coe_evalRingHom, Polynomial.eval_sub,
                Polynomial.eval_X, Polynomial.eval_C]
              rw [Finset.prod_map_val]
        _ = 0 := by
              apply Finset.prod_eq_zero (Finset.mem_univ s)
              simp
    have hprod_p : ∏ i : Fin k, (castp (y s) - castp (x i)) = 0 := by
      have := congrArg castp hprod
      simpa [map_prod] using this
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp (by simpa using hprod_p)
    have hmod : castp (y s) = castp (x i) := sub_eq_zero.mp hi
    have hother : ∀ j ∈ Finset.univ.erase i, IsUnit (y s - x j) := by
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hcast_ne : castp (y s - x j) ≠ 0 := by
        rw [map_sub]
        intro hz
        have hjmod : castp (x j) = castp (x i) := by
          exact (sub_eq_zero.mp hz).symm.trans hmod
        exact hji (hx hjmod)
      let z : ZMod (p ^ k) := y s - x j
      have hnotdvd : ¬ p ∣ z.val := by
        intro hdvd
        have hz0 : (z.val : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff z.val p).2 hdvd
        have hcastval : castp z = (z.val : ZMod p) := by
          simp [castp, ZMod.castHom_apply, ZMod.natCast_val]
        exact hcast_ne (hcastval.trans hz0)
      have hcop : z.val.Coprime (p ^ k) :=
        ((hp.coprime_iff_not_dvd.mpr hnotdvd).symm).pow_right k
      have hzu : IsUnit (z.val : ZMod (p ^ k)) :=
        (ZMod.isUnit_iff_coprime z.val (p ^ k)).2 hcop
      simpa [z, ZMod.natCast_zmod_val] using hzu
    have hrest : IsUnit (∏ j ∈ Finset.univ.erase i, (y s - x j)) :=
      isUnit_finset_prod hother
    have hfactor :
        (∏ j ∈ Finset.univ.erase i, (y s - x j)) * (y s - x i) = 0 := by
      rw [Finset.prod_erase_mul Finset.univ (fun j => y s - x j)
        (Finset.mem_univ i)]
      exact hprod
    have hzero : y s - x i = 0 := by
      apply hrest.mul_left_cancel
      simpa using hfactor
    exact ⟨i, sub_eq_zero.mp hzero⟩
  have hxinj : Function.Injective x := fun i j h => hx (congrArg castp h)
  have hyinj : Function.Injective y := fun i j h => hy (congrArg castp h)
  have hxn : (Finset.univ.val.map x).Nodup :=
    (Multiset.nodup_map_iff_of_injective hxinj).2 Finset.univ.nodup
  have hyn : (Finset.univ.val.map y).Nodup :=
    (Multiset.nodup_map_iff_of_injective hyinj).2 Finset.univ.nodup
  have hsubset : Finset.univ.val.map y ⊆ Finset.univ.val.map x := by
    intro a ha
    obtain ⟨s, -, rfl⟩ := Multiset.mem_map.mp ha
    obtain ⟨i, hi⟩ := hmatch s
    exact Multiset.mem_map.mpr ⟨i, by simp, hi.symm⟩
  have hle : Finset.univ.val.map y ≤ Finset.univ.val.map x :=
    (Multiset.le_iff_subset hyn).2 hsubset
  exact (Multiset.eq_of_le_of_card_le hle (by simp)).symm

end

end RHTower.Sieve
