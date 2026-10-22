import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaMobiusCurrent

/-!
# Positive reconstruction of the actual Gamma/Möbius forcing

A uniform inverse-square bound on the canonical Möbius preimage justifies
commuting its full dilation and von Mangoldt currents. The retained Möbius-log
forcing reconstructs to the positive Euler current of the original Gamma
source. Every prime gives a lower bound, and the forcing has positive real
values on every dilation ray and arbitrarily far out. No vanishing Ward law
or pointwise positivity of the forcing is asserted.
-/

set_option backward.isDefEq.respectTransparency false

namespace RHTower

open ArithmeticFunction

noncomputable section


/-- One constant controls the actual Möbius source on the whole positive ray. -/
theorem pwGammaMobiusPreimage_uniform_inv_sq :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, 0 < x → ‖pwGammaMobiusPreimage x‖ ≤ B / x ^ (2 : ℕ) := by
  let C : ℝ := Real.exp ((5 / 2) * Real.log (5 / 2) - 5 / 2)
  have hsq : Summable fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have hpos : 0 < ∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℕ) :=
    hsq.tsum_pos (fun n => by positivity) 1 (by simp)
  refine ⟨C * (∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℕ)), mul_pos (Real.exp_pos _) hpos, ?_⟩
  intro x hx
  have hmajorant := hsq.mul_left (C / x ^ (2 : ℕ))
  rw [pwGammaMobiusPreimage]
  calc
    _ ≤ ∑' n : ℕ, (C / x ^ (2 : ℕ)) * (1 / (n : ℝ) ^ (2 : ℕ)) := by
      refine tsum_of_norm_bounded hmajorant.hasSum fun n => ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hmu : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast (show |moebius n| ≤ 1 from abs_moebius_le_one)
        rw [norm_mul]
        calc
          _ ≤ 1 * ‖pwGammaRaySource ((n : ℝ) * x)‖ :=
            mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
          _ ≤ C / ((n : ℝ) * x) ^ (2 : ℕ) := by
            simpa using pwGammaRaySource_norm_le_inv_sq (mul_pos hnr hx)
          _ = (C / x ^ (2 : ℕ)) * (1 / (n : ℝ) ^ (2 : ℕ)) := by
            rw [mul_pow]
            field_simp
    _ = (C * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℕ)) / x ^ (2 : ℕ) := by
      rw [tsum_mul_left]
      ring

theorem pwGammaRaySource_re_pos (y : ℝ) : 0 < (pwGammaRaySource y).re := by
  exact Real.exp_pos _

/-- The complete positive Euler current of the original Gamma ray source. -/
def pwGammaSourceEulerCurrent (x : ℝ) : ℂ :=
  ∑' n : ℕ, (vonMangoldt n : ℂ) * pwGammaRaySource ((n : ℝ) * x)

theorem pwGammaSourceEulerCurrent_summable {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => (vonMangoldt n : ℂ) * pwGammaRaySource ((n : ℝ) * x) := by
  let C : ℝ := Real.exp ((5 / 2) * Real.log (5 / 2) - 5 / 2)
  have hmajorant := deningerVonMangoldt_summable_div_sq.mul_left (C / x ^ (2 : ℕ))
  refine Summable.of_norm_bounded hmajorant fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    calc
      _ ≤ vonMangoldt n * (C / ((n : ℝ) * x) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left (pwGammaRaySource_norm_le_inv_sq (mul_pos hnr hx))
          vonMangoldt_nonneg
      _ = (C / x ^ (2 : ℕ)) * (vonMangoldt n / (n : ℝ) ^ (2 : ℕ)) := by
        rw [mul_pow]
        field_simp

theorem pwGammaSourceEulerCurrent_re_pos {x : ℝ} (hx : 0 < x) :
    0 < (pwGammaSourceEulerCurrent x).re := by
  have hsum := pwGammaSourceEulerCurrent_summable hx
  rw [pwGammaSourceEulerCurrent, Complex.re_tsum hsum]
  have hpos : 0 < vonMangoldt 2 := by
    rw [vonMangoldt_apply_prime Nat.prime_two]
    exact Real.log_pos one_lt_two
  refine (Complex.reCLM.summable hsum).tsum_pos ?_ 2 ?_
  · intro n
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg vonMangoldt_nonneg (pwGammaRaySource_re_pos _).le
  · simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos hpos (pwGammaRaySource_re_pos _)


private def pwGammaEulerDilationPair (x : ℝ) (q : ℕ × ℕ) : ℂ :=
  (vonMangoldt q.2 : ℂ) *
    pwGammaMobiusPreimage ((q.2 : ℝ) * (((q.1 : ℝ) + 1) * x))

private theorem pwGammaEulerDilationPair_summable {x : ℝ} (hx : 0 < x) :
    Summable (pwGammaEulerDilationPair x) := by
  obtain ⟨B, hB, hbound⟩ := pwGammaMobiusPreimage_uniform_inv_sq
  have hsq : Summable fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have hshift : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 : ℕ) := by
    have hs : Summable fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) :=
      hsq.comp_injective (fun _ _ h => Nat.add_right_cancel h)
    simpa only [Nat.cast_add, Nat.cast_one] using hs
  have hmajorant : Summable fun q : ℕ × ℕ =>
      (B / x ^ (2 : ℕ)) * ((1 / ((q.1 : ℝ) + 1) ^ (2 : ℕ)) *
        (vonMangoldt q.2 / (q.2 : ℝ) ^ (2 : ℕ))) := by
    refine Summable.mul_left _ ?_
    exact Summable.mul_of_nonneg (f := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 : ℕ))
      (g := fun n : ℕ => vonMangoldt n / (n : ℝ) ^ (2 : ℕ))
      hshift deningerVonMangoldt_summable_div_sq (fun n => by positivity)
      (fun n => div_nonneg vonMangoldt_nonneg (by positivity))
  refine Summable.of_norm_bounded hmajorant fun q => ?_
  rcases Nat.eq_zero_or_pos q.2 with hn0 | hn
  · simp [pwGammaEulerDilationPair, hn0]
  · have hnr : (0 : ℝ) < (q.2 : ℝ) := by exact_mod_cast hn
    have harg : 0 < (q.2 : ℝ) * (((q.1 : ℝ) + 1) * x) := by positivity
    rw [pwGammaEulerDilationPair, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg vonMangoldt_nonneg]
    calc
      _ ≤ vonMangoldt q.2 * (B / ((q.2 : ℝ) * (((q.1 : ℝ) + 1) * x)) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left (hbound _ harg) vonMangoldt_nonneg
      _ = (B / x ^ (2 : ℕ)) * ((1 / ((q.1 : ℝ) + 1) ^ (2 : ℕ)) *
          (vonMangoldt q.2 / (q.2 : ℝ) ^ (2 : ℕ))) := by
        rw [mul_pow, mul_pow]
        field_simp

private theorem pwGammaEulerDilationPair_tsum_row {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (∑' n : ℕ, pwGammaEulerDilationPair x (m, n)) =
      pwGammaMobiusLogCurrent (((m : ℝ) + 1) * x) := by
  simpa only [pwGammaEulerDilationPair] using
    (pwGammaMobius_connection (x := ((m : ℝ) + 1) * x) (by positivity))

private theorem pwGammaEulerDilationPair_tsum_column {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (∑' m : ℕ, pwGammaEulerDilationPair x (m, n)) =
      (vonMangoldt n : ℂ) * pwGammaRaySource ((n : ℝ) * x) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaEulerDilationPair]
  · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    calc
      _ = (vonMangoldt n : ℂ) * deningerRaySum pwGammaMobiusPreimage ((n : ℝ) * x) := by
        rw [deningerRaySum, ← tsum_mul_left]
        refine tsum_congr fun m => ?_
        exact congrArg (fun y : ℝ => (vonMangoldt n : ℂ) * pwGammaMobiusPreimage y)
          (by ring)
      _ = _ := by rw [pwGammaMobius_rightInverse (mul_pos hnr hx)]

theorem pwGammaMobiusLogCurrent_dilation_summable {x : ℝ} (hx : 0 < x) :
    Summable fun m : ℕ => pwGammaMobiusLogCurrent (((m : ℝ) + 1) * x) := by
  exact (pwGammaEulerDilationPair_summable hx).prod.congr
    (pwGammaEulerDilationPair_tsum_row hx)

/-- The two full arithmetic currents commute on the actual source: `Z E = J Q`. -/
theorem pwGammaMobiusLogCurrent_reconstruction {x : ℝ} (hx : 0 < x) :
    deningerRaySum pwGammaMobiusLogCurrent x = pwGammaSourceEulerCurrent x := by
  have hsum := pwGammaEulerDilationPair_summable hx
  calc
    _ = ∑' m : ℕ, ∑' n : ℕ, pwGammaEulerDilationPair x (m, n) :=
      tsum_congr fun m => (pwGammaEulerDilationPair_tsum_row hx m).symm
    _ = ∑' n : ℕ, ∑' m : ℕ, pwGammaEulerDilationPair x (m, n) :=
      (Summable.tsum_comm (f := fun m n : ℕ => pwGammaEulerDilationPair x (m, n)) hsum).symm
    _ = _ := tsum_congr (pwGammaEulerDilationPair_tsum_column hx)

theorem pwGammaMobiusLogCurrent_reconstruction_re_pos {x : ℝ} (hx : 0 < x) :
    0 < (deningerRaySum pwGammaMobiusLogCurrent x).re := by
  rw [pwGammaMobiusLogCurrent_reconstruction hx]
  exact pwGammaSourceEulerCurrent_re_pos hx

/-- Every prime supplies an explicit lower bound for the reconstructed forcing. -/
theorem pwGammaMobiusLogCurrent_reconstruction_prime_floor {x : ℝ} (hx : 0 < x)
    {p : ℕ} (hp : p.Prime) :
    Real.log (p : ℝ) * (pwGammaRaySource ((p : ℝ) * x)).re ≤
      (deningerRaySum pwGammaMobiusLogCurrent x).re := by
  have hsum := pwGammaSourceEulerCurrent_summable hx
  rw [pwGammaMobiusLogCurrent_reconstruction hx, pwGammaSourceEulerCurrent,
    Complex.re_tsum hsum]
  have hterm := (Complex.reCLM.summable hsum).le_tsum p (fun n _ => by
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg vonMangoldt_nonneg (pwGammaRaySource_re_pos _).le)
  simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, vonMangoldt_apply_prime hp] using hterm

/-- The full forcing has a positive real value on every positive dilation ray. -/
theorem pwGammaMobiusLogCurrent_positive_on_dilation {x : ℝ} (hx : 0 < x) :
    ∃ n : ℕ, 0 < (pwGammaMobiusLogCurrent (((n : ℝ) + 1) * x)).re := by
  by_contra h
  push Not at h
  have hsum := pwGammaMobiusLogCurrent_dilation_summable hx
  have hpos := pwGammaMobiusLogCurrent_reconstruction_re_pos hx
  rw [deningerRaySum, Complex.re_tsum hsum] at hpos
  exact (not_le_of_gt hpos) (tsum_nonpos h)

/-- Nontriviality persists arbitrarily far out, with a positive real witness. -/
theorem pwGammaMobiusLogCurrent_positive_arbitrarily_far (A : ℝ) :
    ∃ y : ℝ, A < y ∧ 0 < y ∧ 0 < (pwGammaMobiusLogCurrent y).re := by
  let x : ℝ := max A 0 + 1
  have hx : 0 < x := by
    dsimp [x]
    have := le_max_right A 0
    linarith
  have hAx : A < x := by
    dsimp [x]
    have := le_max_left A 0
    linarith
  obtain ⟨n, hn⟩ := pwGammaMobiusLogCurrent_positive_on_dilation hx
  have hxy : x ≤ ((n : ℝ) + 1) * x := by
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)) hx.le]
  exact ⟨((n : ℝ) + 1) * x, hAx.trans_le hxy, hx.trans_le hxy, hn⟩

theorem pwGammaMobiusLogCurrent_ne_zero : pwGammaMobiusLogCurrent ≠ 0 := by
  intro h
  obtain ⟨y, _, _, hy⟩ := pwGammaMobiusLogCurrent_positive_arbitrarily_far 0
  have hz : pwGammaMobiusLogCurrent y = 0 := congrFun h y
  rw [hz, Complex.zero_re] at hy
  exact (lt_irrefl 0) hy

/-- Closed actual-source result, with convergence and the positive forcing retained. -/
theorem pwGammaMobiusForcing_positive_reconstruction :
    pwGammaMobiusLogCurrent ≠ 0 ∧
      ∀ x : ℝ, 0 < x →
        Summable (fun m : ℕ => pwGammaMobiusLogCurrent (((m : ℝ) + 1) * x)) ∧
        deningerRaySum pwGammaMobiusLogCurrent x = pwGammaSourceEulerCurrent x ∧
        0 < (deningerRaySum pwGammaMobiusLogCurrent x).re := by
  refine ⟨pwGammaMobiusLogCurrent_ne_zero, fun x hx => ?_⟩
  exact ⟨pwGammaMobiusLogCurrent_dilation_summable hx,
    pwGammaMobiusLogCurrent_reconstruction hx, pwGammaMobiusLogCurrent_reconstruction_re_pos hx⟩

end

end RHTower
