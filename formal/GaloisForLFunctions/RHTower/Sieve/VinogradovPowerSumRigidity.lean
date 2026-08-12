import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Power-sum rigidity for Vinogradov's mean value theorem

The diagonal base case of the classical Vinogradov mean-value induction is
Newton--Girard rigidity: two `b`-tuples whose first `b` power sums agree have
the same multiset of entries.  This file proves the statement over `ℚ`, then
specializes it to natural-number tuples.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- Equality of the first `b` power sums over `ℚ` forces equality of every
elementary symmetric function. -/
theorem rational_esymm_eq_of_powerSums_eq
    {b : ℕ} (x y : Fin b → ℚ)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ b →
      ∑ i : Fin b, x i ^ j = ∑ i : Fin b, y i ^ j) :
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
      have hnewton := MvPolynomial.mul_esymm_eq_sum (Fin b) ℚ j
      have hx := congrArg (MvPolynomial.aeval x) hnewton
      have hy := congrArg (MvPolynomial.aeval y) hnewton
      have hpsum (z : Fin b → ℚ) (m : ℕ) :
          MvPolynomial.aeval z (MvPolynomial.psum (Fin b) ℚ m) =
            ∑ i : Fin b, z i ^ m := by
        simp [MvPolynomial.psum]
      simp only [map_mul, map_natCast, MvPolynomial.aeval_esymm_eq_multiset_esymm,
        map_pow, map_neg, map_one, map_sum] at hx hy
      simp_rw [hpsum] at hx hy
      have hsum :
          (∑ a ∈ Finset.antidiagonal j with a.1 < j,
              (-1 : ℚ) ^ a.1 * (Finset.univ.val.map x).esymm a.1 *
                (∑ i : Fin b, x i ^ a.2)) =
            ∑ a ∈ Finset.antidiagonal j with a.1 < j,
              (-1 : ℚ) ^ a.1 * (Finset.univ.val.map y).esymm a.1 *
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
      have hmul : (j : ℚ) * (Finset.univ.val.map x).esymm j =
          (j : ℚ) * (Finset.univ.val.map y).esymm j := hx.trans hy.symm
      exact mul_left_cancel₀ (by exact_mod_cast hjpos.ne') hmul

/-- Equality of the first `b` power sums determines a rational tuple up to
permutation, expressed as equality of its value multisets. -/
theorem rational_multiset_eq_of_powerSums_eq
    {b : ℕ} (x y : Fin b → ℚ)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ b →
      ∑ i : Fin b, x i ^ j = ∑ i : Fin b, y i ^ j) :
    Finset.univ.val.map x = Finset.univ.val.map y := by
  let sx : Multiset ℚ := Finset.univ.val.map x
  let sy : Multiset ℚ := Finset.univ.val.map y
  have hcardx : sx.card = b := by simp [sx]
  have hcardy : sy.card = b := by simp [sy]
  have hesymm : ∀ j : ℕ, j ≤ b → sx.esymm j = sy.esymm j := by
    simpa [sx, sy] using rational_esymm_eq_of_powerSums_eq x y hpower
  have hpoly :
      (sx.map fun a => Polynomial.X - Polynomial.C a).prod =
        (sy.map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm,
      Multiset.prod_X_sub_X_eq_sum_esymm, hcardx, hcardy]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hesymm j (by simpa using hj)]
  calc
    sx = ((sx.map fun a => Polynomial.X - Polynomial.C a).prod).roots := by
      rw [Polynomial.roots_multiset_prod_X_sub_C]
    _ = ((sy.map fun a => Polynomial.X - Polynomial.C a).prod).roots :=
      congrArg Polynomial.roots hpoly
    _ = sy := Polynomial.roots_multiset_prod_X_sub_C sy

/-- Natural-number form consumed by the diagonal Vinogradov moment bound. -/
theorem nat_multiset_eq_of_powerSums_eq
    {b : ℕ} (x y : Fin b → ℕ)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ b →
      ∑ i : Fin b, x i ^ j = ∑ i : Fin b, y i ^ j) :
    Finset.univ.val.map x = Finset.univ.val.map y := by
  let xq : Fin b → ℚ := fun i => x i
  let yq : Fin b → ℚ := fun i => y i
  have hpowerq : ∀ j : ℕ, 1 ≤ j → j ≤ b →
      ∑ i : Fin b, xq i ^ j = ∑ i : Fin b, yq i ^ j := by
    intro j hj1 hjb
    dsimp [xq, yq]
    exact_mod_cast hpower j hj1 hjb
  have hq := rational_multiset_eq_of_powerSums_eq xq yq hpowerq
  apply Multiset.map_injective
    (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℚ)))
  simpa [xq, yq, Multiset.map_map, Function.comp_def] using hq

end

end RHTower.Sieve
