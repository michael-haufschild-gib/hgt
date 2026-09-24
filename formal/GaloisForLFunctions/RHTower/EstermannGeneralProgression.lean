import GaloisForLFunctions.RHTower.EstermannScaledTwist

/-!
# Every twist has a main term, at its reduced modulus

Writing `d = gcd(a, q)` and `q' = q/d`, the scaled-twist reduction turns an arbitrary residue twist
`a` mod `q` into a **unit** twist `a/d` mod `q'`, which is the hypothesis the Estermann smoothed sum
requires.  Hence every twist — not only the units — has an `O(x^{-1/2})` expansion, with main term
`(γ − log x − 2 log q')/(q' x)` belonging to the reduced modulus.

Averaging against `e(−ab/q)` then gives the smoothed divisor sum over the progression `N ≡ b (q)`
for an arbitrary modulus, with main term `∑_{a mod q} e(−ab/q) · main(q_a)`.  Grouping the residues
by their gcd collapses that to `∑_{d ∣ q} c_{q/d}(b) · main(q/d)` with Ramanujan sums `c`.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Every twist reduces to a unit twist of a divisor modulus.**  `a` mod `q` has the smoothed
expansion of the reduced modulus `q/gcd(a, q)`. -/
theorem exists_reducedMain (q : ℕ) [NeZero q] (a : ZMod q) :
    ∃ q' : ℕ, q' ∣ q ∧ 0 < q' ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖estermannSmoothedSum q a x - estermannSmoothedMain q' x‖ ≤ C * x ^ (-(1 / 2 : ℝ)) := by
  classical
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  set d : ℕ := Nat.gcd a.val q with hd
  have hdq : d ∣ q := Nat.gcd_dvd_right _ _
  have hdval : d ∣ a.val := Nat.gcd_dvd_left _ _
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right _ hq0
  set q' : ℕ := q / d with hq'
  have hq'dvd : q' ∣ q := Nat.div_dvd_of_dvd hdq
  have hq'0 : 0 < q' := Nat.div_pos (Nat.le_of_dvd hq0 hdq) hd0
  haveI : NeZero q' := ⟨hq'0.ne'⟩
  set m : ℕ := a.val / d with hm
  have hqfac : q = d * q' := (Nat.mul_div_cancel' hdq).symm
  have hcop : Nat.Coprime m q' := by
    rw [hm, hq', hd]
    exact Nat.coprime_div_gcd_div_gcd hd0
  set u : (ZMod q')ˣ := ZMod.unitOfCoprime m hcop with hu
  have hucoe : ((u : ZMod q')) = ((m : ℕ) : ZMod q') := ZMod.coe_unitOfCoprime m hcop
  have hareduce : a = (((d * m : ℤ)) : ZMod q) := by
    have hnat : d * m = a.val := Nat.mul_div_cancel' hdval
    have hcast : ((d * m : ℕ) : ZMod q) = (((d * m : ℤ)) : ZMod q) := by norm_cast
    have : (((d * m : ℤ)) : ZMod q) = ((a.val : ℕ) : ZMod q) := by
      rw [← hcast, hnat]
    rw [this, ZMod.natCast_val, ZMod.cast_id]
  refine ⟨q', hq'dvd, hq'0, ?_⟩
  obtain ⟨C, hC, hbound⟩ := exists_bound_norm_estermannSmoothedSum_sub_main q' u
  refine ⟨C, hC, fun x hx => ?_⟩
  have hred : estermannSmoothedSum q a x = estermannSmoothedSum q' ((u : ZMod q')) x := by
    rw [hareduce, estermannSmoothedSum_scale hqfac (m : ℤ) x, hucoe]
    norm_cast
  rw [hred]
  exact hbound x hx

/-- **The smoothed divisor sum in a progression, arbitrary modulus.**  Each residue twist
contributes the main term of its own reduced modulus. -/
theorem exists_bound_norm_estermann_general_progression (q : ℕ) [NeZero q] (b : ZMod q) :
    ∃ (mod : ZMod q → ℕ) (C : ℝ), 0 ≤ C ∧ (∀ a, mod a ∣ q) ∧
      ∀ x : ℝ, 0 < x →
        ‖(q : ℂ) * (∑' N : ℕ, (if (N : ZMod q) = b then ((N.divisors.card : ℂ)) else 0) *
              Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)))
            - ∑ a : ZMod q, ((ZMod.stdAddChar (-(a * b))) : ℂ) *
                estermannSmoothedMain (mod a) x‖
          ≤ C * x ^ (-(1 / 2 : ℝ)) := by
  classical
  choose mod hdvd hpos C hC hbound using fun a : ZMod q => exists_reducedMain q a
  refine ⟨mod, ∑ a : ZMod q, C a, Finset.sum_nonneg (fun a _ => hC a), hdvd, fun x hx => ?_⟩
  have horth := sum_twist_eq_progression q b hx
  have hchar : ∀ a : ZMod q, ‖((ZMod.stdAddChar (-(a * b))) : ℂ)‖ = 1 := by
    intro a
    rw [ZMod.stdAddChar_apply, Circle.norm_coe]
  have hrw : (q : ℂ) * (∑' N : ℕ, (if (N : ZMod q) = b then ((N.divisors.card : ℂ)) else 0) *
        Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)))
        - ∑ a : ZMod q, ((ZMod.stdAddChar (-(a * b))) : ℂ) * estermannSmoothedMain (mod a) x
      = ∑ a : ZMod q, ((ZMod.stdAddChar (-(a * b))) : ℂ) *
          (estermannSmoothedSum q a x - estermannSmoothedMain (mod a) x) := by
    rw [← horth]
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [hrw]
  calc ‖∑ a : ZMod q, ((ZMod.stdAddChar (-(a * b))) : ℂ) *
          (estermannSmoothedSum q a x - estermannSmoothedMain (mod a) x)‖
      ≤ ∑ a : ZMod q, ‖((ZMod.stdAddChar (-(a * b))) : ℂ) *
          (estermannSmoothedSum q a x - estermannSmoothedMain (mod a) x)‖ := norm_sum_le _ _
    _ ≤ ∑ a : ZMod q, C a * x ^ (-(1 / 2 : ℝ)) := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        rw [norm_mul, hchar a, one_mul]
        exact hbound a x hx
    _ = (∑ a : ZMod q, C a) * x ^ (-(1 / 2 : ℝ)) := by rw [← Finset.sum_mul]

end

end RHTower
