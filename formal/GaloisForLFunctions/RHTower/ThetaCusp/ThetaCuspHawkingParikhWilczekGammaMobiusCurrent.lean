import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekReflectedSourceForcing

/-!
# The actual half-density Gamma/Möbius current

The literal Gamma log source is outside the exponentially decreasing Schwartz
class. Its explicit positive-ray inverse-square bound nevertheless suffices for
Möbius reconstruction and the full von Mangoldt connection. The half-density
coefficients, convergence of both currents, and complete reflected forcing are
retained. No vanishing Ward law or Xi occurrence is assumed or asserted.
-/

set_option backward.isDefEq.respectTransparency false

namespace RHTower

open ArithmeticFunction

noncomputable section


private theorem pwExpLinear_bound {c : ℝ} (hc : 0 < c) (u : ℝ) :
    c * u - Real.exp u ≤ c * Real.log c - c := by
  have h := Real.add_one_le_exp (u - Real.log c)
  rw [Real.exp_sub, Real.exp_log hc] at h
  have hmul : c * (u - Real.log c + 1) ≤ Real.exp u := by
    calc
      _ ≤ c * (Real.exp u / c) := mul_le_mul_of_nonneg_left h hc.le
      _ = Real.exp u := by field_simp
  linarith

/-- The literal half-density Gamma source, pulled to the positive ray. -/
def pwGammaRaySource (y : ℝ) : ℂ :=
  (GaloisForLFunctions.expShift (1 / 2) 0 (Real.log y) : ℂ)

theorem pwGammaRaySource_eq {y : ℝ} (hy : 0 < y) :
    pwGammaRaySource y = (Real.sqrt y * Real.exp (-y) : ℝ) := by
  rw [pwGammaRaySource, GaloisForLFunctions.expShift]
  simp only [Nat.cast_zero, add_zero, Real.exp_log hy]
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy, ← Real.exp_add]
  congr 2
  ring

theorem pwGammaRaySource_ne_zero (y : ℝ) : pwGammaRaySource y ≠ 0 := by
  unfold pwGammaRaySource GaloisForLFunctions.expShift
  exact_mod_cast Real.exp_ne_zero _

/-- Explicit positive-ray decay; no two-sided Schwartz admission is assumed. -/
theorem pwGammaRaySource_norm_le_inv_sq {y : ℝ} (hy : 0 < y) :
    ‖pwGammaRaySource y‖ ≤
      Real.exp ((5 / 2) * Real.log (5 / 2) - 5 / 2) / y ^ 2 := by
  have h := Real.exp_le_exp.mpr (pwExpLinear_bound (c := 5 / 2) (by positivity)
    (Real.log y))
  have heq : y ^ 2 * Real.exp ((1 / 2) * Real.log y - y) =
      Real.exp ((5 / 2) * Real.log y - Real.exp (Real.log y)) := by
    rw [show (5 / 2) * Real.log y - Real.exp (Real.log y) =
        (Real.log y + Real.log y) + ((1 / 2) * Real.log y - y) by
      rw [Real.exp_log hy]; ring, Real.exp_add, Real.exp_add, Real.exp_log hy, pow_two]
  rw [pwGammaRaySource, GaloisForLFunctions.expShift, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  simp only [Nat.cast_zero, add_zero, Real.exp_log hy]
  apply (le_div_iff₀ (sq_pos_of_pos hy)).2
  rw [mul_comm, heq]
  exact h


/-- The canonical Möbius dilation of the actual half-density Gamma source. -/
def pwGammaMobiusPreimage (x : ℝ) : ℂ :=
  ∑' n : ℕ, ((moebius n : ℤ) : ℂ) * pwGammaRaySource ((n : ℝ) * x)

/-- The full Möbius-log source; its coefficients are not discarded. -/
def pwGammaMobiusLogCurrent (x : ℝ) : ℂ :=
  ∑' n : ℕ, ((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ) *
    pwGammaRaySource ((n : ℝ) * x)

private def pwGammaMobiusPair (b : ℕ → ℂ) (x : ℝ) (q : ℕ × ℕ) : ℂ :=
  b q.1 * (((moebius q.2 : ℤ) : ℂ) *
    pwGammaRaySource (((q.1 * q.2 : ℕ) : ℝ) * x))

private theorem pwGammaMobiusPair_zero (b : ℕ → ℂ) (hb0 : b 0 = 0) (x : ℝ)
    {q : ℕ × ℕ} (hq : q.1 * q.2 = 0) : pwGammaMobiusPair b x q = 0 := by
  rw [pwGammaMobiusPair]
  rcases Nat.mul_eq_zero.mp hq with h1 | h2
  · rw [h1, hb0, zero_mul]
  · simp [h2]

private theorem pwGammaMobiusPair_summable (b : ℕ → ℂ) (hb0 : b 0 = 0)
    (hb : Summable fun m : ℕ => ‖b m‖ / (m : ℝ) ^ 2) {x : ℝ} (hx : 0 < x) :
    Summable (pwGammaMobiusPair b x) := by
  let C : ℝ := Real.exp ((5 / 2) * Real.log (5 / 2) - 5 / 2)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hsq : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have hpair : Summable fun q : ℕ × ℕ =>
      (C / x ^ 2) * ((‖b q.1‖ / (q.1 : ℝ) ^ 2) * (1 / (q.2 : ℝ) ^ 2)) := by
    refine Summable.mul_left _ ?_
    exact Summable.mul_of_nonneg (f := fun m : ℕ => ‖b m‖ / (m : ℝ) ^ 2)
      (g := fun n : ℕ => 1 / (n : ℝ) ^ 2) hb hsq
      (fun n => div_nonneg (norm_nonneg _) (by positivity)) (fun n => by positivity)
  refine Summable.of_norm_bounded hpair fun q => ?_
  rcases Nat.eq_zero_or_pos (q.1 * q.2) with hq0 | hqpos
  · rw [pwGammaMobiusPair_zero b hb0 x hq0, norm_zero]
    positivity
  · have hprod : (0 : ℝ) < ((q.1 * q.2 : ℕ) : ℝ) * x := by
      have hcastpos : (0 : ℝ) < ((q.1 * q.2 : ℕ) : ℝ) := by exact_mod_cast hqpos
      exact mul_pos hcastpos hx
    have hterm := pwGammaRaySource_norm_le_inv_sq hprod
    have hmu : ‖((moebius q.2 : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (show |moebius q.2| ≤ 1 from abs_moebius_le_one)
    rw [pwGammaMobiusPair, norm_mul, norm_mul]
    have hinner : ‖((moebius q.2 : ℤ) : ℂ)‖ *
        ‖pwGammaRaySource (((q.1 * q.2 : ℕ) : ℝ) * x)‖
        ≤ C / (((q.1 : ℝ) * (q.2 : ℝ)) * x) ^ 2 := by
      calc
        _ ≤ 1 * ‖pwGammaRaySource (((q.1 * q.2 : ℕ) : ℝ) * x)‖ :=
          mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
        _ ≤ C / (((q.1 : ℝ) * (q.2 : ℝ)) * x) ^ 2 := by
          simpa only [one_mul, Nat.cast_mul] using hterm
    refine le_trans (mul_le_mul_of_nonneg_left hinner (norm_nonneg _)) (le_of_eq ?_)
    rw [mul_pow, mul_pow]
    field_simp

private theorem pwGammaMobiusPair_tsum_fst (b : ℕ → ℂ) (x : ℝ) (m : ℕ) :
    (∑' n : ℕ, pwGammaMobiusPair b x (m, n)) =
      b m * pwGammaMobiusPreimage ((m : ℝ) * x) := by
  rw [pwGammaMobiusPreimage, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [pwGammaMobiusPair]
  congr 2
  push_cast
  ring

private def pwGammaUnitWeight (m : ℕ) : ℂ := if m = 0 then 0 else 1

private theorem pwGammaUnitWeight_summable :
    Summable fun m : ℕ => ‖pwGammaUnitWeight m‖ / (m : ℝ) ^ 2 := by
  have hsq : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  refine hsq.congr fun n => ?_
  by_cases hn : n = 0 <;> simp [pwGammaUnitWeight, hn]

theorem pwGammaMobiusPreimage_summable {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => ((moebius n : ℤ) : ℂ) * pwGammaRaySource ((n : ℝ) * x) := by
  have h := (pwGammaMobiusPair_summable pwGammaUnitWeight (by simp [pwGammaUnitWeight])
    pwGammaUnitWeight_summable hx).prod_factor 1
  simpa [pwGammaMobiusPair, pwGammaUnitWeight] using h

theorem pwGammaMobiusPreimage_halfDensity {x : ℝ} (hx : 0 < x) :
    pwGammaMobiusPreimage x = (Real.sqrt x : ℂ) *
      ∑' n : ℕ, ((moebius n : ℤ) : ℂ) * (Real.sqrt (n : ℝ) : ℂ) *
        (Real.exp (-((n : ℝ) * x)) : ℂ) := by
  rw [pwGammaMobiusPreimage, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [pwGammaRaySource_eq (mul_pos hnr hx), Real.sqrt_mul hnr.le]
    push_cast
    ring

private theorem pwGammaVonMangoldt_weighted_summable :
    Summable fun m : ℕ => ‖(vonMangoldt m : ℂ)‖ / (m : ℝ) ^ 2 := by
  simpa only [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg] using
    deningerVonMangoldt_summable_div_sq

theorem pwGammaMobiusEulerCurrent_summable {x : ℝ} (hx : 0 < x) :
    Summable fun m : ℕ => (vonMangoldt m : ℂ) * pwGammaMobiusPreimage ((m : ℝ) * x) := by
  have h := (pwGammaMobiusPair_summable (fun m => (vonMangoldt m : ℂ)) (by simp)
    pwGammaVonMangoldt_weighted_summable hx).prod
  exact h.congr (pwGammaMobiusPair_tsum_fst _ x)

theorem pwGammaMobius_connection {x : ℝ} (hx : 0 < x) :
    (∑' m : ℕ, (vonMangoldt m : ℂ) * pwGammaMobiusPreimage ((m : ℝ) * x)) =
      pwGammaMobiusLogCurrent x := by
  classical
  let b : ℕ → ℂ := fun m => (vonMangoldt m : ℂ)
  have hb0 : b 0 = 0 := by simp [b]
  have hsum := pwGammaMobiusPair_summable b hb0 pwGammaVonMangoldt_weighted_summable hx
  have hleft : (∑' q : ℕ × ℕ, pwGammaMobiusPair b x q) =
      ∑' m : ℕ, (vonMangoldt m : ℂ) * pwGammaMobiusPreimage ((m : ℝ) * x) := by
    rw [hsum.tsum_prod]
    exact tsum_congr (pwGammaMobiusPair_tsum_fst b x)
  have hright := deningerProductFibre_tsum hsum
    (fun q hq => pwGammaMobiusPair_zero b hb0 x hq)
  have hfib : ∀ N : ℕ, (∑ d ∈ N.divisors, pwGammaMobiusPair b x (d, N / d)) =
      ((-(((moebius N : ℤ) : ℝ) * Real.log (N : ℝ)) : ℝ) : ℂ) *
        pwGammaRaySource ((N : ℝ) * x) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hterm : ∀ d ∈ N.divisors, pwGammaMobiusPair b x (d, N / d) =
          ((vonMangoldt d * ((moebius (N / d) : ℤ) : ℝ) : ℝ) : ℂ) *
            pwGammaRaySource ((N : ℝ) * x) := by
        intro d hd
        have hdvd : d * (N / d) = N := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
        rw [pwGammaMobiusPair,
          show (((d, N / d) : ℕ × ℕ).1 * ((d, N / d) : ℕ × ℕ).2 : ℕ) = N from hdvd]
        simp only [b]
        push_cast
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
      congr 1
      rw [← Complex.ofReal_sum, deningerVonMangoldtMoebiusDivisorSum]
  rw [← hleft, hright, tsum_congr hfib, pwGammaMobiusLogCurrent]

theorem pwGammaMobius_rightInverse {x : ℝ} (hx : 0 < x) :
    deningerRaySum pwGammaMobiusPreimage x = pwGammaRaySource x := by
  classical
  have hb0 : pwGammaUnitWeight 0 = 0 := by simp [pwGammaUnitWeight]
  have hsum := pwGammaMobiusPair_summable pwGammaUnitWeight hb0
    pwGammaUnitWeight_summable hx
  have hrows : Summable fun m : ℕ =>
      pwGammaUnitWeight m * pwGammaMobiusPreimage ((m : ℝ) * x) :=
    hsum.prod.congr (pwGammaMobiusPair_tsum_fst _ x)
  have hleft : (∑' q : ℕ × ℕ, pwGammaMobiusPair pwGammaUnitWeight x q) =
      deningerRaySum pwGammaMobiusPreimage x := by
    rw [hsum.tsum_prod, tsum_congr (pwGammaMobiusPair_tsum_fst _ x),
      hrows.tsum_eq_zero_add]
    simp [pwGammaUnitWeight, deningerRaySum]
  have hright := deningerProductFibre_tsum hsum
    (fun q hq => pwGammaMobiusPair_zero pwGammaUnitWeight hb0 x hq)
  have hfib : ∀ N : ℕ, (∑ d ∈ N.divisors, pwGammaMobiusPair pwGammaUnitWeight x (d, N / d)) =
      (if N = 1 then (1 : ℂ) else 0) * pwGammaRaySource ((N : ℝ) * x) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hterm : ∀ d ∈ N.divisors,
          pwGammaMobiusPair pwGammaUnitWeight x (d, N / d) =
            ((moebius (N / d) : ℤ) : ℂ) * pwGammaRaySource ((N : ℝ) * x) := by
        intro d hd
        have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
        have hdvd : d * (N / d) = N := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
        simp only [pwGammaMobiusPair, pwGammaUnitWeight, if_neg hd0, one_mul]
        rw [hdvd]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, deningerMobiusDivisorSum]
  rw [← hleft, hright, tsum_congr hfib,
    tsum_eq_single 1 (fun N hN => by rw [if_neg hN, zero_mul])]
  simp

/-- The actual arithmetic preimage is nonzero on the positive ray. -/
theorem pwGammaMobiusPreimage_nontrivial :
    ∃ x : ℝ, 0 < x ∧ pwGammaMobiusPreimage x ≠ 0 := by
  by_contra h
  have hzero : ∀ x : ℝ, 0 < x → pwGammaMobiusPreimage x = 0 := by
    intro x hx
    by_contra hnx
    exact h ⟨x, hx, hnx⟩
  have hsource := pwGammaMobius_rightInverse (x := 1) zero_lt_one
  have hsum : deningerRaySum pwGammaMobiusPreimage 1 = 0 := by
    calc
      _ = ∑' n : ℕ, (0 : ℂ) := tsum_congr fun n => hzero _ (by positivity)
      _ = 0 := by simp
  rw [hsum] at hsource
  exact pwGammaRaySource_ne_zero 1 hsource.symm


theorem pwGammaMobiusLogCurrent_summable {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ =>
      ((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ) *
        pwGammaRaySource ((n : ℝ) * x) := by
  let C : ℝ := Real.exp ((5 / 2) * Real.log (5 / 2) - 5 / 2)
  have hsum := Sieve.summable_log_div_sq.mul_left (C / x ^ 2)
  refine Summable.of_norm_bounded hsum fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hmu : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast (show |moebius n| ≤ 1 from abs_moebius_le_one)
    have hcoeff : ‖((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ)‖
        ≤ Real.log (n : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg hlog]
      simpa using mul_le_mul_of_nonneg_right hmu hlog
    rw [norm_mul]
    calc
      _ ≤ Real.log (n : ℝ) * (C / ((n : ℝ) * x) ^ 2) :=
        mul_le_mul hcoeff (pwGammaRaySource_norm_le_inv_sq (mul_pos hnr hx))
          (norm_nonneg _) hlog
      _ = (C / x ^ 2) * (Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
        rw [mul_pow]
        field_simp

/-- A closed source-level package: literal Möbius reconstruction and its complete,
convergent Euler current. It asserts no vanishing of the Möbius-log source. -/
theorem pwGammaMobius_source_current_closed :
    (∃ x : ℝ, 0 < x ∧ pwGammaMobiusPreimage x ≠ 0) ∧
      ∀ x : ℝ, 0 < x →
        deningerRaySum pwGammaMobiusPreimage x = pwGammaRaySource x ∧
        Summable (fun m : ℕ => (vonMangoldt m : ℂ) *
          pwGammaMobiusPreimage ((m : ℝ) * x)) ∧
        Summable (fun n : ℕ =>
          ((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ) *
            pwGammaRaySource ((n : ℝ) * x)) ∧
        (∑' m : ℕ, (vonMangoldt m : ℂ) * pwGammaMobiusPreimage ((m : ℝ) * x)) =
          pwGammaMobiusLogCurrent x := by
  refine ⟨pwGammaMobiusPreimage_nontrivial, fun x hx => ?_⟩
  exact ⟨pwGammaMobius_rightInverse hx, pwGammaMobiusEulerCurrent_summable hx,
    pwGammaMobiusLogCurrent_summable hx, pwGammaMobius_connection hx⟩


theorem pwGammaMobius_log_current_summable (t : ℝ) :
    Summable (pwArithmeticCurrentTerm (fun n => (vonMangoldt n : ℂ))
      (fun u => pwGammaMobiusPreimage (Real.exp u)) t) := by
  refine (pwGammaMobiusEulerCurrent_summable (Real.exp_pos t)).congr fun n => ?_
  exact (pwEulerCurrentTerm_logPull pwGammaMobiusPreimage t n).symm

theorem pwGammaMobius_log_connection (t : ℝ) :
    (∑' n : ℕ, pwArithmeticCurrentTerm (fun n => (vonMangoldt n : ℂ))
      (fun u => pwGammaMobiusPreimage (Real.exp u)) t n) =
        pwGammaMobiusLogCurrent (Real.exp t) := by
  rw [← pwGammaMobius_connection (Real.exp_pos t)]
  exact tsum_congr fun n => pwEulerCurrentTerm_logPull pwGammaMobiusPreimage t n

theorem pwGammaMobius_reflected_current_summable (t : ℝ) :
    Summable (pwReflectedArithmeticCurrentTerm (fun n => (vonMangoldt n : ℂ))
      (pwLogSingularComplexReflection (fun u => pwGammaMobiusPreimage (Real.exp u))) t) := by
  rw [pwReflectedArithmeticCurrent_summable_iff]
  exact pwGammaMobius_log_current_summable (-t)

/-- The transported connection for the actual Gamma/Möbius source. The complete
Möbius-log forcing remains present after reflection. -/
theorem pwGammaMobius_reflected_connection (t : ℝ) :
    (∑' n : ℕ, pwReflectedArithmeticCurrentTerm (fun n => (vonMangoldt n : ℂ))
      (pwLogSingularComplexReflection (fun u => pwGammaMobiusPreimage (Real.exp u))) t n) =
        (pwLogSingularGain t : ℂ) * pwGammaMobiusLogCurrent (Real.exp (-t)) := by
  rw [pwReflectedArithmeticCurrent_tsum_transport, pwLogSingularComplexReflection,
    pwGammaMobius_log_connection]

end

end RHTower
