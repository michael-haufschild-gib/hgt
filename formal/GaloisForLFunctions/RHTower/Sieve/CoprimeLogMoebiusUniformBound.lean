import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusRecursion

/-!
# The uniform bound for the coprime logarithmic Möbius sum

The contraction recursion

`T_{pe}(Y) = T_e(Y) + (1/p) · T_{pe}(Y/p)`

is a genuine geometric recursion: unfolding it in the cutoff gives
`T_{pe}(Y) = ∑_{k ≥ 0} p^{-k} T_e(Y/p^k)`, so a uniform bound `C` for `T_e` produces the uniform
bound `C·(1 − 1/p)^{-1}` for `T_{pe}`.  Peeling the primes of a squarefree modulus one at a time
therefore multiplies the modulus-one constant by one Euler factor per prime, and the product of the
Euler factors is exactly `e/φ(e)`:

`|T_e(Y)| ≤ (6 + |γ|) · e/φ(e)`     uniformly in `e` squarefree and in `Y`.

The bound is proved without ever estimating the `d(e)` divisor terms separately, which is what makes
it lossless: summed against the diagonal weight `φ(e)/e²` it gives `∑_{e ≤ X} 1/φ(e)`, of order
`log X`, rather than a power of `log X` per divisor.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- The absolute constant of the modulus-one bound. -/
noncomputable def coprimeLogMoebiusConst : ℝ := 6 + |Real.eulerMascheroniConstant|

theorem coprimeLogMoebiusConst_nonneg : 0 ≤ coprimeLogMoebiusConst := by
  have := abs_nonneg (Real.eulerMascheroniConstant)
  unfold coprimeLogMoebiusConst
  linarith

/-- **The Euler-factor step.**  A uniform bound at modulus `e` produces a uniform bound at modulus
`p·e` multiplied by the single Euler factor `(1 − 1/p)^{-1}`. -/
theorem abs_coprimeLogMoebius_prime_step {p e : ℕ} (hp : p.Prime) (hpe : ¬ p ∣ e)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ Y : ℝ, |coprimeLogMoebius e Y| ≤ C) (Y : ℝ) :
    |coprimeLogMoebius (p * e) Y| ≤ C * ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hgoal_nonneg : (0 : ℝ) ≤ C * ((p : ℝ) / ((p : ℝ) - 1)) :=
    mul_nonneg hC (div_nonneg hp0.le hpos.le)
  have key : ∀ n : ℕ, ∀ Z : ℝ, ⌊Z⌋₊ ≤ n →
      |coprimeLogMoebius (p * e) Z| ≤ C * ((p : ℝ) / ((p : ℝ) - 1)) := by
    intro n
    induction n with
    | zero =>
        intro Z hZ
        have h0 : ⌊Z⌋₊ = 0 := Nat.le_zero.mp hZ
        rw [coprimeLogMoebius_of_lt_one _ (Nat.floor_eq_zero.mp h0), abs_zero]
        exact hgoal_nonneg
    | succ n ih =>
        intro Z hZ
        rcases lt_or_ge Z 1 with hZ1 | hZ1
        · rw [coprimeLogMoebius_of_lt_one _ hZ1, abs_zero]
          exact hgoal_nonneg
        · have hfl : ⌊Z / (p : ℝ)⌋₊ ≤ n := by
            rw [Nat.floor_div_natCast]
            have h1 : ⌊Z⌋₊ / p ≤ (n + 1) / p := Nat.div_le_div_right hZ
            have h2 : (n + 1) / p ≤ (n + 1) / 2 := Nat.div_le_div_left hp2 (by norm_num)
            have h3 : (n + 1) / 2 ≤ n := by omega
            exact le_trans h1 (le_trans h2 h3)
          have hih := ih (Z / (p : ℝ)) hfl
          have he := h Z
          have hrec := coprimeLogMoebius_recursion hp hpe Z
          have hsolve : coprimeLogMoebius (p * e) Z
              = coprimeLogMoebius e Z
                + (1 / (p : ℝ)) * coprimeLogMoebius (p * e) (Z / (p : ℝ)) := by
            linarith [hrec]
          have habs : |(1 / (p : ℝ)) * coprimeLogMoebius (p * e) (Z / (p : ℝ))|
              = (1 / (p : ℝ)) * |coprimeLogMoebius (p * e) (Z / (p : ℝ))| := by
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ))]
          have hscaled : (1 / (p : ℝ)) * |coprimeLogMoebius (p * e) (Z / (p : ℝ))|
              ≤ (1 / (p : ℝ)) * (C * ((p : ℝ) / ((p : ℝ) - 1))) :=
            mul_le_mul_of_nonneg_left hih (by positivity)
          have hfinal : C + (1 / (p : ℝ)) * (C * ((p : ℝ) / ((p : ℝ) - 1)))
              = C * ((p : ℝ) / ((p : ℝ) - 1)) := by
            field_simp
            ring
          rw [hsolve]
          calc |coprimeLogMoebius e Z + (1 / (p : ℝ)) * coprimeLogMoebius (p * e) (Z / (p : ℝ))|
              ≤ |coprimeLogMoebius e Z|
                + |(1 / (p : ℝ)) * coprimeLogMoebius (p * e) (Z / (p : ℝ))| := abs_add_le _ _
            _ ≤ C * ((p : ℝ) / ((p : ℝ) - 1)) := by
                rw [habs]
                linarith
  exact key ⌊Y⌋₊ Y le_rfl

/-- **The uniform bound.**  For every squarefree modulus `e` and every real cutoff `Y`,
`|T_e(Y)| ≤ (6 + |γ|) · e/φ(e)`. -/
theorem abs_coprimeLogMoebius_le : ∀ (e : ℕ), Squarefree e → ∀ (Y : ℝ),
    |coprimeLogMoebius e Y|
      ≤ coprimeLogMoebiusConst * ((e : ℝ) / (Nat.totient e : ℝ)) := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he Y
    rcases eq_or_ne e 1 with rfl | hne
    · have h1 : coprimeLogMoebiusConst * (((1 : ℕ) : ℝ) / ((Nat.totient 1 : ℕ) : ℝ))
          = coprimeLogMoebiusConst := by
        simp
      rw [h1]
      exact abs_coprimeLogMoebius_one_le Y
    · have he0 : e ≠ 0 := he.ne_zero
      have hpp : (e.minFac).Prime := Nat.minFac_prime hne
      have hpd : e.minFac ∣ e := Nat.minFac_dvd e
      have hmul : e.minFac * (e / e.minFac) = e := Nat.mul_div_cancel' hpd
      have hpe' : ¬ e.minFac ∣ (e / e.minFac) := by
        intro hdvd
        obtain ⟨k, hk⟩ := hdvd
        have hsq : e.minFac * e.minFac ∣ e := by
          refine ⟨k, ?_⟩
          calc e = e.minFac * (e / e.minFac) := hmul.symm
            _ = e.minFac * (e.minFac * k) := by rw [hk]
            _ = e.minFac * e.minFac * k := by ring
        have hunit := he _ hsq
        rw [Nat.isUnit_iff] at hunit
        exact hpp.ne_one hunit
      have he'sf : Squarefree (e / e.minFac) :=
        Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hpd) he
      have he'lt : e / e.minFac < e := Nat.div_lt_self (Nat.pos_of_ne_zero he0) hpp.one_lt
      have he'0 : e / e.minFac ≠ 0 := by
        intro h0
        rw [h0, Nat.mul_zero] at hmul
        exact he0 hmul.symm
      have hIH := ih (e / e.minFac) he'lt he'sf
      have hCnn : (0 : ℝ)
          ≤ coprimeLogMoebiusConst * ((e / e.minFac : ℕ) : ℝ) / ((Nat.totient (e / e.minFac) : ℕ) : ℝ) := by
        have h1 : (0 : ℝ) ≤ ((e / e.minFac : ℕ) : ℝ) := by positivity
        have h2 : (0 : ℝ) ≤ ((Nat.totient (e / e.minFac) : ℕ) : ℝ) := by positivity
        have := coprimeLogMoebiusConst_nonneg
        positivity
      have hCnn' : (0 : ℝ)
          ≤ coprimeLogMoebiusConst * (((e / e.minFac : ℕ) : ℝ) / ((Nat.totient (e / e.minFac) : ℕ) : ℝ)) := by
        rw [mul_div_assoc] at hCnn
        exact hCnn
      have hstep := abs_coprimeLogMoebius_prime_step hpp hpe' hCnn' hIH Y
      rw [hmul] at hstep
      refine le_trans hstep (le_of_eq ?_)
      -- the Euler factor identity
      have hcop : Nat.Coprime e.minFac (e / e.minFac) := (hpp.coprime_iff_not_dvd).mpr hpe'
      have htot : Nat.totient e = (e.minFac - 1) * Nat.totient (e / e.minFac) := by
        conv_lhs => rw [← hmul]
        rw [Nat.totient_mul hcop, Nat.totient_prime hpp]
      have hp1 : 1 ≤ e.minFac := hpp.one_lt.le
      have hcast : ((e.minFac - 1 : ℕ) : ℝ) = (e.minFac : ℝ) - 1 := by
        rw [Nat.cast_sub hp1, Nat.cast_one]
      have htotpos : (0 : ℝ) < (Nat.totient (e / e.minFac) : ℝ) := by
        have : 0 < Nat.totient (e / e.minFac) :=
          Nat.totient_pos.mpr (Nat.pos_of_ne_zero he'0)
        exact_mod_cast this
      have hppos : (0 : ℝ) < (e.minFac : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (e.minFac : ℝ) := by exact_mod_cast hpp.two_le
        linarith
      have hcastmul : (e : ℝ) = (e.minFac : ℝ) * ((e / e.minFac : ℕ) : ℝ) := by
        conv_lhs => rw [← hmul]
        push_cast
        ring
      have hcasttot : (Nat.totient e : ℝ)
          = ((e.minFac : ℝ) - 1) * (Nat.totient (e / e.minFac) : ℝ) := by
        rw [htot]
        push_cast [hcast]
        ring
      rw [hcastmul, hcasttot]
      field_simp

end RHTower.Sieve
