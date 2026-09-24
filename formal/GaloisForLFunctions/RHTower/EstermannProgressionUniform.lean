import GaloisForLFunctions.RHTower.EstermannSmoothedErrorExplicit
import GaloisForLFunctions.RHTower.EstermannGeneralProgression

/-!
# The divisor sum in a progression, with an absolute implied constant

Every ingredient is now uniform in the modulus.  A twist `a` mod `q` reduces, by
`d = gcd(a, q)`, to a unit twist of `q' = q/d`, and there the error is `C (q')^{3/2} x^{−1/2}` with
`C` absolute; since `q' ∣ q` this is at most `C q^{3/2} x^{−1/2}`.  Averaging the `q` twists against
`e(−ab/q)` costs a factor `q`, so

`‖q ∑_{N ≡ b (q)} d(N) e^{−Nx} − ∑_{a mod q} e(−ab/q) main(q/gcd(a,q))‖ ≤ C q^{5/2} x^{−1/2}`,

with `C` absolute.  This is the progression law with a rate, which is what summing over moduli in
`∑_n d(n) d(n+h) e^{−nx} = ∑_k ∑_{n ≡ −h (k)} d(n) e^{−nx}` requires.
-/

open Complex

namespace RHTower

noncomputable section

/-- The reduced modulus of a twist: `q / gcd(a, q)`. -/
def reducedModulus (q : ℕ) (a : ZMod q) : ℕ := q / Nat.gcd a.val q

theorem reducedModulus_dvd (q : ℕ) [NeZero q] (a : ZMod q) : reducedModulus q a ∣ q :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)

theorem reducedModulus_pos (q : ℕ) [NeZero q] (a : ZMod q) : 0 < reducedModulus q a := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  exact Nat.div_pos (Nat.le_of_dvd hq0 (Nat.gcd_dvd_right _ _))
    (Nat.gcd_pos_of_pos_right _ hq0)

/-- The explicit error at a unit twist. -/
theorem norm_estermannSmoothedSum_sub_main_le (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) {x : ℝ}
    (hx : 0 < x) :
    ‖estermannSmoothedSum q ((a : ZMod q)) x - estermannSmoothedMain q x‖
      ≤ estermannSmoothedErrorConstant * (q : ℝ) ^ ((3 : ℝ) / 2) * x ^ (-(1 / 2 : ℝ)) := by
  rw [estermannSmoothedSum_sub_main q a hx]
  exact norm_estermann_smoothed_error_le q a hx

/-- **The explicit error at an arbitrary twist.**  Reduction by the gcd, with `q' ∣ q` giving
`(q')^{3/2} ≤ q^{3/2}`. -/
theorem norm_estermannSmoothedSum_sub_reducedMain_le (q : ℕ) [NeZero q] (a : ZMod q) {x : ℝ}
    (hx : 0 < x) :
    ‖estermannSmoothedSum q a x - estermannSmoothedMain (reducedModulus q a) x‖
      ≤ estermannSmoothedErrorConstant * (q : ℝ) ^ ((3 : ℝ) / 2) * x ^ (-(1 / 2 : ℝ)) := by
  classical
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  set d : ℕ := Nat.gcd a.val q with hd
  have hdq : d ∣ q := Nat.gcd_dvd_right _ _
  have hdval : d ∣ a.val := Nat.gcd_dvd_left _ _
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right _ hq0
  set q' : ℕ := reducedModulus q a with hq'
  have hq'eq : q' = q / d := rfl
  have hq'0 : 0 < q' := reducedModulus_pos q a
  haveI : NeZero q' := ⟨hq'0.ne'⟩
  set m : ℕ := a.val / d with hm
  have hqfac : q = d * q' := by
    rw [hq'eq]
    exact (Nat.mul_div_cancel' hdq).symm
  have hcop : Nat.Coprime m q' := by
    rw [hm, hq'eq, hd]
    exact Nat.coprime_div_gcd_div_gcd hd0
  set u : (ZMod q')ˣ := ZMod.unitOfCoprime m hcop with hu
  have hucoe : ((u : ZMod q')) = ((m : ℕ) : ZMod q') := ZMod.coe_unitOfCoprime m hcop
  have hareduce : a = (((d * m : ℤ)) : ZMod q) := by
    have hnat : d * m = a.val := Nat.mul_div_cancel' hdval
    have hcast : ((d * m : ℕ) : ZMod q) = (((d * m : ℤ)) : ZMod q) := by norm_cast
    have hstep : (((d * m : ℤ)) : ZMod q) = ((a.val : ℕ) : ZMod q) := by
      rw [← hcast, hnat]
    rw [hstep, ZMod.natCast_val, ZMod.cast_id]
  have hred : estermannSmoothedSum q a x = estermannSmoothedSum q' ((u : ZMod q')) x := by
    rw [hareduce, estermannSmoothedSum_scale hqfac (m : ℤ) x, hucoe]
    norm_cast
  rw [hred]
  refine (norm_estermannSmoothedSum_sub_main_le q' u hx).trans ?_
  -- `q' ≤ q` gives `(q')^{3/2} ≤ q^{3/2}`
  have hle : (q' : ℝ) ≤ (q : ℝ) := by
    have := Nat.le_of_dvd hq0 (reducedModulus_dvd q a)
    exact_mod_cast this
  have hq'R : (0 : ℝ) ≤ (q' : ℝ) := Nat.cast_nonneg _
  have hmono : (q' : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hq'R hle (by norm_num)
  have hC0 : 0 ≤ estermannSmoothedErrorConstant := estermannSmoothedErrorConstant_nonneg
  have hxpow : (0 : ℝ) ≤ x ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hx _).le
  have h1 := mul_le_mul_of_nonneg_left hmono hC0
  exact mul_le_mul_of_nonneg_right h1 hxpow

/-- **The progression law with an absolute implied constant.** -/
theorem norm_progression_sub_main_le (q : ℕ) [NeZero q] (b : ZMod q) {x : ℝ} (hx : 0 < x) :
    ‖(q : ℂ) * (∑' N : ℕ, (if (N : ZMod q) = b then ((N.divisors.card : ℂ)) else 0) *
          Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)))
        - ∑ a : ZMod q, ((ZMod.stdAddChar (-(a * b))) : ℂ) *
            estermannSmoothedMain (reducedModulus q a) x‖
      ≤ estermannSmoothedErrorConstant * (q : ℝ) ^ ((5 : ℝ) / 2) * x ^ (-(1 / 2 : ℝ)) := by
  classical
  have horth := sum_twist_eq_progression q b hx
  have hchar : ∀ a : ZMod q, ‖((ZMod.stdAddChar (-(a * b))) : ℂ)‖ = 1 := by
    intro a
    rw [ZMod.stdAddChar_apply, Circle.norm_coe]
  have hrw : (q : ℂ) * (∑' N : ℕ, (if (N : ZMod q) = b then ((N.divisors.card : ℂ)) else 0) *
        Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)))
        - ∑ a : ZMod q, ((ZMod.stdAddChar (-(a * b))) : ℂ) *
            estermannSmoothedMain (reducedModulus q a) x
      = ∑ a : ZMod q, ((ZMod.stdAddChar (-(a * b))) : ℂ) *
          (estermannSmoothedSum q a x - estermannSmoothedMain (reducedModulus q a) x) := by
    rw [← horth]
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [hrw]
  set E : ℝ := estermannSmoothedErrorConstant * (q : ℝ) ^ ((3 : ℝ) / 2) * x ^ (-(1 / 2 : ℝ)) with hE
  have hE0 : 0 ≤ E := by
    rw [hE]
    have := estermannSmoothedErrorConstant_nonneg
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      have := Nat.pos_of_ne_zero (NeZero.ne q)
      exact_mod_cast this
    have h1 : (0 : ℝ) ≤ (q : ℝ) ^ ((3 : ℝ) / 2) := (Real.rpow_pos_of_pos hq0 _).le
    have h2 : (0 : ℝ) ≤ x ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hx _).le
    positivity
  have hterm : ∀ a : ZMod q,
      ‖((ZMod.stdAddChar (-(a * b))) : ℂ) *
        (estermannSmoothedSum q a x - estermannSmoothedMain (reducedModulus q a) x)‖ ≤ E := by
    intro a
    rw [norm_mul, hchar a, one_mul, hE]
    exact norm_estermannSmoothedSum_sub_reducedMain_le q a hx
  have hcard : (Finset.univ : Finset (ZMod q)).card = q := by
    rw [Finset.card_univ, ZMod.card]
  calc ‖∑ a : ZMod q, ((ZMod.stdAddChar (-(a * b))) : ℂ) *
          (estermannSmoothedSum q a x - estermannSmoothedMain (reducedModulus q a) x)‖
      ≤ ∑ a : ZMod q, ‖((ZMod.stdAddChar (-(a * b))) : ℂ) *
          (estermannSmoothedSum q a x - estermannSmoothedMain (reducedModulus q a) x)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _a : ZMod q, E := Finset.sum_le_sum (fun a _ => hterm a)
    _ = (q : ℝ) * E := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = estermannSmoothedErrorConstant * (q : ℝ) ^ ((5 : ℝ) / 2) * x ^ (-(1 / 2 : ℝ)) := by
        rw [hE]
        have hq0 : (0 : ℝ) < (q : ℝ) := by
          have := Nat.pos_of_ne_zero (NeZero.ne q)
          exact_mod_cast this
        have hsplit : (q : ℝ) ^ ((5 : ℝ) / 2) = (q : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) := by
          rw [show (5 : ℝ) / 2 = 1 + (3 : ℝ) / 2 by norm_num, Real.rpow_add hq0,
            Real.rpow_one]
        rw [hsplit]
        ring

end

end RHTower
