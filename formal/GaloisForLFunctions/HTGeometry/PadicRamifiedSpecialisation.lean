/-
# The ramification obstruction at a specialised branch point

A `p`-adic number that is an `e`-th power has valuation divisible by `e`.  So if the specialisation
parameter is chosen with valuation coprime to the ramification index of a branch, the branch value
cannot lie in `ℚ_p`: it generates a ramified extension.  Any root of the specialised polynomial that
determines such an `e`-th root is therefore irrational.

This is the local half of the specialisation argument: the global side supplies the Puiseux branch
in `(t-b)^{1/e}` and the recovery of the branch parameter from the root, and this module supplies
the valuation bookkeeping that kills the rational root.

Main results:
* `not_pow_eq_of_not_dvd_valuation` — **no `e`-th root of a `p`-adic number of indivisible
  valuation**.
* `no_padic_root_of_ramified_branch` — the specialised polynomial has no `p`-adic root.
* `no_rational_root_of_ramified_branch` — hence no rational root.
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

open Polynomial

namespace GaloisForLFunctions.HTGeometry

section Ramification

variable {p : ℕ} [Fact p.Prime]

/-- **The valuation of an `e`-th power is divisible by `e`.** -/
theorem dvd_valuation_pow (z : ℚ_[p]) (e : ℕ) : (e : ℤ) ∣ (z ^ e).valuation := by
  rw [Padic.valuation_pow]
  exact Dvd.intro _ rfl

/-- **No `e`-th root of a `p`-adic number whose valuation is not divisible by `e`.** -/
theorem not_pow_eq_of_not_dvd_valuation {e : ℕ} {w : ℚ_[p]}
    (hnd : ¬ ((e : ℤ) ∣ w.valuation)) (z : ℚ_[p]) : z ^ e ≠ w := by
  intro hzw
  exact hnd (hzw ▸ dvd_valuation_pow z e)

/-- The valuation of `p ^ m` is `m`, so a power of the uniformizer has an `e`-th root only when `e`
divides the exponent. -/
theorem not_pow_eq_ppow {e m : ℕ} (hnd : ¬ ((e : ℤ) ∣ (m : ℤ))) (z : ℚ_[p]) :
    z ^ e ≠ (p : ℚ_[p]) ^ m := by
  refine not_pow_eq_of_not_dvd_valuation ?_ z
  rw [Padic.valuation_pow, Padic.valuation_natCast]
  simpa using hnd

/-- **The ramification step.**  Suppose every `p`-adic root of the specialised polynomial determines
an `e`-th root of the specialisation parameter, and the parameter's valuation is not divisible by
`e`.  Then the specialised polynomial has no root in `ℚ_p`. -/
theorem no_padic_root_of_ramified_branch {e : ℕ} {pi : ℚ_[p]}
    (hnd : ¬ ((e : ℤ) ∣ pi.valuation))
    {g : ℚ_[p][X]} (branchParameter : ℚ_[p] → ℚ_[p])
    (hbranch : ∀ y : ℚ_[p], g.eval y = 0 → (branchParameter y) ^ e = pi) :
    ∀ y : ℚ_[p], g.eval y ≠ 0 := by
  intro y hy
  exact not_pow_eq_of_not_dvd_valuation hnd (branchParameter y) (hbranch y hy)

/-- **Hence no rational root.**  A rational root of the rational specialised polynomial is a
`p`-adic root of its image, so the ramification obstruction rules it out. -/
theorem no_rational_root_of_ramified_branch {e : ℕ} {pi : ℚ_[p]}
    (hnd : ¬ ((e : ℤ) ∣ pi.valuation))
    {f : ℚ[X]} (branchParameter : ℚ_[p] → ℚ_[p])
    (hbranch : ∀ y : ℚ_[p], (f.map (Rat.castHom ℚ_[p])).eval y = 0 →
      (branchParameter y) ^ e = pi) :
    ∀ y : ℚ, f.eval y ≠ 0 := by
  intro y hy
  refine no_padic_root_of_ramified_branch hnd branchParameter hbranch ((y : ℚ_[p])) ?_
  rw [Polynomial.eval_map, show ((y : ℚ) : ℚ_[p]) = (Rat.castHom ℚ_[p]) y from rfl,
    Polynomial.eval₂_at_apply, hy, map_zero]

/-- Coprimality is the usable form of the indivisibility hypothesis. -/
theorem not_dvd_of_coprime {e m : ℕ} (he : 2 ≤ e) (hcop : Nat.Coprime m e) :
    ¬ ((e : ℤ) ∣ (m : ℤ)) := by
  intro hdvd
  have hnat : e ∣ m := by
    exact_mod_cast hdvd
  have hone : e ∣ Nat.gcd m e := Nat.dvd_gcd hnat dvd_rfl
  rw [hcop] at hone
  have := Nat.eq_one_of_dvd_one hone
  omega


/-! ## The obstruction through a normed extension -/

theorem valuation_eq_of_norm_pow_eq {e k : ℕ} (_he : 0 < e) {pi y : ℚ_[p]}
    (hpi : pi ≠ 0) (hy : y ≠ 0) (hnorm : ‖y‖ ^ e = ‖pi‖ ^ k) :
    (e : ℤ) * y.valuation = (k : ℤ) * pi.valuation := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    have := (Fact.out : p.Prime).one_lt
    exact_mod_cast this
  rw [Padic.norm_eq_zpow_neg_valuation hy, Padic.norm_eq_zpow_neg_valuation hpi,
    ← zpow_natCast ((p : ℝ) ^ (-y.valuation)) e, ← zpow_natCast ((p : ℝ) ^ (-pi.valuation)) k,
    ← zpow_mul, ← zpow_mul] at hnorm
  have hinj := zpow_right_injective₀ (by positivity : (0:ℝ) < (p:ℝ)) (ne_of_gt hp1) hnorm
  have hexp : -y.valuation * (e : ℤ) = -pi.valuation * (k : ℤ) := hinj
  linarith [hexp]

/-- **The ramification obstruction.**  A `p`-adic number whose norm is an `e`-th root of the `k`-th
power of the parameter norm has `e · v(y) = k · v(π)`; if `e` does not divide `k · v(π)` there is no
such number. -/
theorem not_norm_pow_eq {e k : ℕ} (he : 0 < e) {pi y : ℚ_[p]}
    (hpi : pi ≠ 0) (hy : y ≠ 0) (hnd : ¬ ((e : ℤ) ∣ (k : ℤ) * pi.valuation))
    (hnorm : ‖y‖ ^ e = ‖pi‖ ^ k) : False :=
  hnd ⟨y.valuation, (valuation_eq_of_norm_pow_eq he hpi hy hnorm).symm⟩

/-- **The branch value is irrational.**  A branch of ramification index `e` over a parameter of
valuation coprime to `e` takes its values in a ramified extension: if the leading coefficient and
the unit factor have norm one, no value of the branch lies in `ℚ_p`. -/
theorem not_padic_branch_value {L : Type*} [NormedField L] (i : ℚ_[p] →+* L)
    (hiso : ∀ x, ‖i x‖ = ‖x‖) {e k : ℕ} (he : 0 < e) {pi : ℚ_[p]} (hpi : pi ≠ 0)
    {s c u : L} (hs : s ^ e = i pi) (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    {y : ℚ_[p]} (hy0 : y ≠ 0) (hy : i y = c * s ^ k * u)
    (hnd : ¬ ((e : ℤ) ∣ (k : ℤ) * pi.valuation)) : False := by
  have hnormy : ‖y‖ = ‖s‖ ^ k := by
    rw [← hiso y, hy, norm_mul, norm_mul, hc, hu, norm_pow, one_mul, mul_one]
  have hnorms : ‖s‖ ^ e = ‖pi‖ := by
    rw [← norm_pow, hs, hiso]
  refine not_norm_pow_eq he hpi hy0 hnd ?_
  rw [hnormy, ← pow_mul, mul_comm k e, pow_mul, hnorms]


/-! ## The Dumas no-root criterion -/

open Finset in
/-- **The Dumas criterion, no-root form.**  If the constant term of a monic degree-`e` polynomial
dominates the intermediate coefficients in the Newton sense `‖a_i‖^e < ‖a_0‖^{e-i}`, and its
valuation is not divisible by `e`, then the polynomial has no root in `ℚ_p`.

The three cases are the three positions of `‖y‖^e` relative to `‖a_0‖`: above, the leading term is
strictly larger than everything it must cancel; below, the constant term is; and equality forces
`e · v(y) = v(a_0)`. -/
theorem no_padic_root_of_dumas {e : ℕ} (he : 2 ≤ e)
    (a : ℕ → ℚ_[p]) (ha0 : a 0 ≠ 0)
    (hcoef : ∀ i, 0 < i → i < e → ‖a i‖ ^ e < ‖a 0‖ ^ (e - i))
    (hval : ¬ ((e : ℤ) ∣ (a 0).valuation))
    (y : ℚ_[p]) (hroot : y ^ e + ∑ i ∈ range e, a i * y ^ i = 0) : False := by
  classical
  have hepos : 0 < e := by omega
  have hA : 0 < ‖a 0‖ := norm_pos_iff.mpr ha0
  have hzero : (0 : ℕ) ∈ range e := Finset.mem_range.mpr hepos
  have hy0 : y ≠ 0 := by
    intro hy
    subst hy
    rw [zero_pow (by omega), zero_add] at hroot
    rw [Finset.sum_eq_single 0] at hroot
    · rw [pow_zero, mul_one] at hroot
      exact ha0 hroot
    · intro i _ hi
      rw [zero_pow hi, mul_zero]
    · intro hcon
      exact absurd hzero hcon
  have hY : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hT0 : a 0 * y ^ 0 = a 0 := by rw [pow_zero, mul_one]
  rcases lt_trichotomy (‖a 0‖) (‖y‖ ^ e) with hlt | heq | hgt
  · -- the leading term is strictly larger than every term it must cancel
    have hsmall : ∀ i ∈ range e, ‖a i * y ^ i‖ < ‖y‖ ^ e := by
      intro i hi
      have hilt : i < e := Finset.mem_range.mp hi
      by_cases hi0 : i = 0
      · rw [hi0, hT0]
        exact hlt
      · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
        have hpow : ‖a i * y ^ i‖ ^ e < (‖y‖ ^ e) ^ e := by
          rw [norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm i e, pow_mul]
          calc ‖a i‖ ^ e * (‖y‖ ^ e) ^ i < ‖a 0‖ ^ (e - i) * (‖y‖ ^ e) ^ i :=
                mul_lt_mul_of_pos_right (hcoef i hipos hilt) (by positivity)
            _ ≤ (‖y‖ ^ e) ^ (e - i) * (‖y‖ ^ e) ^ i :=
                mul_le_mul_of_nonneg_right
                  (pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hlt) (e - i)) (by positivity)
            _ = (‖y‖ ^ e) ^ e := by rw [← pow_add]; congr 1; omega
        exact lt_of_pow_lt_pow_left₀ e (by positivity) hpow
    have hne : (range e).Nonempty := ⟨0, hzero⟩
    have hsup : (range e).sup' hne (fun i => ‖a i * y ^ i‖) < ‖y‖ ^ e :=
      (Finset.sup'_lt_iff hne).mpr hsmall
    have hsupnn : 0 ≤ (range e).sup' hne (fun i => ‖a i * y ^ i‖) :=
      le_trans (norm_nonneg _) (Finset.le_sup' (fun i => ‖a i * y ^ i‖) hzero)
    have hsum : ‖∑ i ∈ range e, a i * y ^ i‖
        ≤ (range e).sup' hne (fun i => ‖a i * y ^ i‖) :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hsupnn
        (fun i hi => Finset.le_sup' (fun i => ‖a i * y ^ i‖) hi)
    have hlead : y ^ e = -∑ i ∈ range e, a i * y ^ i := by linear_combination hroot
    have : ‖y‖ ^ e < ‖y‖ ^ e := by
      calc ‖y‖ ^ e = ‖y ^ e‖ := (norm_pow y e).symm
        _ = ‖∑ i ∈ range e, a i * y ^ i‖ := by rw [hlead, norm_neg]
        _ ≤ _ := hsum
        _ < ‖y‖ ^ e := hsup
    exact absurd this (lt_irrefl _)
  · -- equality forces the valuation of the constant term to be divisible by `e`
    refine hval ⟨y.valuation, ?_⟩
    have h := valuation_eq_of_norm_pow_eq (k := 1) hepos ha0 hy0
      (by rw [pow_one]; exact heq.symm)
    rw [Nat.cast_one, one_mul] at h
    exact h.symm
  · -- the constant term is strictly larger than every term it must cancel
    have hsmall : ∀ i ∈ (range e).erase 0, ‖a i * y ^ i‖ < ‖a 0‖ := by
      intro i hi
      have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
      have hilt : i < e := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
      have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      have hpow : ‖a i * y ^ i‖ ^ e < ‖a 0‖ ^ e := by
        rw [norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm i e, pow_mul]
        calc ‖a i‖ ^ e * (‖y‖ ^ e) ^ i < ‖a 0‖ ^ (e - i) * (‖y‖ ^ e) ^ i :=
              mul_lt_mul_of_pos_right (hcoef i hipos hilt) (by positivity)
          _ ≤ ‖a 0‖ ^ (e - i) * ‖a 0‖ ^ i :=
              mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (by positivity) (le_of_lt hgt) i) (by positivity)
          _ = ‖a 0‖ ^ e := by rw [← pow_add]; congr 1; omega
      exact lt_of_pow_lt_pow_left₀ e (norm_nonneg _) hpow
    have hne : ((range e).erase 0).Nonempty := ⟨1, Finset.mem_erase.mpr
      ⟨one_ne_zero, Finset.mem_range.mpr (by omega)⟩⟩
    have hsup : ((range e).erase 0).sup' hne (fun i => ‖a i * y ^ i‖) < ‖a 0‖ :=
      (Finset.sup'_lt_iff hne).mpr hsmall
    have hsupnn : 0 ≤ ((range e).erase 0).sup' hne (fun i => ‖a i * y ^ i‖) :=
      le_trans (norm_nonneg _) (Finset.le_sup' (fun i => ‖a i * y ^ i‖) hne.choose_spec)
    have hsum : ‖∑ i ∈ (range e).erase 0, a i * y ^ i‖
        ≤ ((range e).erase 0).sup' hne (fun i => ‖a i * y ^ i‖) :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hsupnn
        (fun i hi => Finset.le_sup' (fun i => ‖a i * y ^ i‖) hi)
    have hsplit : ∑ i ∈ (range e).erase 0, a i * y ^ i + a 0 * y ^ 0
        = ∑ i ∈ range e, a i * y ^ i := Finset.sum_erase_add _ _ hzero
    have hconst : a 0 = -(y ^ e + ∑ i ∈ (range e).erase 0, a i * y ^ i) := by
      have h2 : a 0 * y ^ 0 = -(y ^ e + ∑ i ∈ (range e).erase 0, a i * y ^ i) := by
        linear_combination hroot + hsplit
      rw [← hT0]
      exact h2
    have : ‖a 0‖ < ‖a 0‖ := by
      calc ‖a 0‖ = ‖y ^ e + ∑ i ∈ (range e).erase 0, a i * y ^ i‖ := by
            rw [hconst, norm_neg]
        _ ≤ max ‖y ^ e‖ ‖∑ i ∈ (range e).erase 0, a i * y ^ i‖ :=
            IsUltrametricDist.norm_add_le_max _ _
        _ < ‖a 0‖ := max_lt (by rw [norm_pow]; exact hgt) (lt_of_le_of_lt hsum hsup)
    exact absurd this (lt_irrefl _)


open Finset in
/-- The Dumas criterion for a monic polynomial: no root in `ℚ_p`. -/
theorem no_padic_root_of_dumas_poly {e : ℕ} (he : 2 ≤ e) {g : ℚ_[p][X]}
    (hmonic : g.Monic) (hdeg : g.natDegree = e) (ha0 : g.coeff 0 ≠ 0)
    (hcoef : ∀ i, 0 < i → i < e → ‖g.coeff i‖ ^ e < ‖g.coeff 0‖ ^ (e - i))
    (hval : ¬ ((e : ℤ) ∣ (g.coeff 0).valuation)) :
    ∀ y : ℚ_[p], g.eval y ≠ 0 := by
  intro y hy
  refine no_padic_root_of_dumas he (fun i => g.coeff i) ha0 hcoef hval y ?_
  have hsum : g.eval y = ∑ i ∈ range (e + 1), g.coeff i * y ^ i := by
    rw [Polynomial.eval_eq_sum_range, hdeg]
  rw [hsum, Finset.sum_range_succ] at hy
  have hlead : g.coeff e = 1 := by
    rw [← hdeg]
    exact hmonic
  rw [hlead, one_mul] at hy
  linear_combination hy

open Finset in
/-- **Hence no rational root.**  A monic rational polynomial whose `p`-adic image satisfies the
Dumas condition has no rational root. -/
theorem no_rational_root_of_dumas {e : ℕ} (he : 2 ≤ e) {f : ℚ[X]}
    (hmonic : (f.map (Rat.castHom ℚ_[p])).Monic)
    (hdeg : (f.map (Rat.castHom ℚ_[p])).natDegree = e)
    (ha0 : (f.map (Rat.castHom ℚ_[p])).coeff 0 ≠ 0)
    (hcoef : ∀ i, 0 < i → i < e →
      ‖(f.map (Rat.castHom ℚ_[p])).coeff i‖ ^ e
        < ‖(f.map (Rat.castHom ℚ_[p])).coeff 0‖ ^ (e - i))
    (hval : ¬ ((e : ℤ) ∣ ((f.map (Rat.castHom ℚ_[p])).coeff 0).valuation)) :
    ∀ y : ℚ, f.eval y ≠ 0 := by
  intro y hy
  refine no_padic_root_of_dumas_poly he hmonic hdeg ha0 hcoef hval ((y : ℚ_[p])) ?_
  rw [Polynomial.eval_map, show ((y : ℚ) : ℚ_[p]) = (Rat.castHom ℚ_[p]) y from rfl,
    Polynomial.eval₂_at_apply, hy, map_zero]

end Ramification

end GaloisForLFunctions.HTGeometry
