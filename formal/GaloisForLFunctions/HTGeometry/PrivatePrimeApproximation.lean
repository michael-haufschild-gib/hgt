import GaloisForLFunctions.HTGeometry.PrivatePrimeRealization

/-!
# Private-prime rational approximation of arbitrary positive profiles

Every positive real sequence admits pointwise rational approximants with strictly increasing
private denominator primes.  The construction internally caps the requested error by one; this
preserves superlinear growth even when the supplied tolerance is arbitrarily large.
-/

open Filter

namespace GaloisForLFunctions

noncomputable section

private noncomputable def primeAbove (N : ℕ) : ℕ :=
  Classical.choose (Nat.exists_infinite_primes (N + 1))

private theorem primeAbove_spec (N : ℕ) :
    N < primeAbove N ∧ (primeAbove N).Prime := by
  obtain ⟨hle, hp⟩ := Classical.choose_spec (Nat.exists_infinite_primes (N + 1))
  have hle' : N + 1 ≤ primeAbove N := by simpa [primeAbove] using hle
  have hp' : (primeAbove N).Prime := by simpa [primeAbove] using hp
  exact ⟨by omega, hp'⟩

private def cappedTolerance (ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  min (ε n) 1

private noncomputable def approximationPrimeBound (g ε : ℕ → ℝ) (n : ℕ) : ℕ :=
  max ⌈(cappedTolerance ε n)⁻¹⌉₊ ⌈(g n)⁻¹⌉₊

private noncomputable def approximationPrime (g ε : ℕ → ℝ) : ℕ → ℕ
  | 0 => primeAbove (approximationPrimeBound g ε 0)
  | n + 1 => primeAbove
      (max (approximationPrimeBound g ε (n + 1)) (approximationPrime g ε n))

private theorem approximationPrime_prime (g ε : ℕ → ℝ) :
    ∀ n, (approximationPrime g ε n).Prime := by
  intro n
  cases n with
  | zero => exact (primeAbove_spec _).2
  | succ n => exact (primeAbove_spec _).2

private theorem approximationPrime_bound_lt (g ε : ℕ → ℝ) :
    ∀ n, approximationPrimeBound g ε n < approximationPrime g ε n := by
  intro n
  cases n with
  | zero => exact (primeAbove_spec _).1
  | succ n =>
      exact (le_max_left _ _).trans_lt (primeAbove_spec _).1

private theorem approximationPrime_strictMono (g ε : ℕ → ℝ) :
    StrictMono (approximationPrime g ε) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (le_max_right _ _).trans_lt (primeAbove_spec _).1

private theorem approximationPrime_inv_lt_cappedTolerance
    {g ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (n : ℕ) :
    1 / (approximationPrime g ε n : ℝ) < cappedTolerance ε n := by
  have hδ : 0 < cappedTolerance ε n := by
    exact lt_min (hε n) zero_lt_one
  have hceil : ⌈(cappedTolerance ε n)⁻¹⌉₊ < approximationPrime g ε n :=
    (le_max_left _ _).trans_lt (approximationPrime_bound_lt g ε n)
  have hinv : (cappedTolerance ε n)⁻¹ < (approximationPrime g ε n : ℝ) :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast hceil)
  have hp : 0 < (approximationPrime g ε n : ℝ) := by
    exact_mod_cast (approximationPrime_prime g ε n).pos
  rw [div_lt_iff₀ hp]
  have hmul := mul_lt_mul_of_pos_left hinv hδ
  simpa [hδ.ne'] using hmul

private theorem one_lt_approximationPrime_mul
    {g ε : ℕ → ℝ} (hg : ∀ n, 0 < g n) (n : ℕ) :
    1 < (approximationPrime g ε n : ℝ) * g n := by
  have hceil : ⌈(g n)⁻¹⌉₊ < approximationPrime g ε n :=
    (le_max_right _ _).trans_lt (approximationPrime_bound_lt g ε n)
  have hinv : (g n)⁻¹ < (approximationPrime g ε n : ℝ) :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast hceil)
  have hmul := mul_lt_mul_of_pos_left hinv (hg n)
  simpa [mul_comm, (hg n).ne'] using hmul

private noncomputable def approximationNumerator (g ε : ℕ → ℝ) (n : ℕ) : ℕ :=
  let p := approximationPrime g ε n
  let q₀ := ⌊(p : ℝ) * g n⌋₊
  if p ∣ q₀ then q₀ + 1 else q₀

private theorem approximationPrime_not_dvd_numerator (g ε : ℕ → ℝ) (n : ℕ) :
    ¬ approximationPrime g ε n ∣ approximationNumerator g ε n := by
  let p := approximationPrime g ε n
  let q₀ := ⌊(p : ℝ) * g n⌋₊
  by_cases hdiv : p ∣ q₀
  · rw [approximationNumerator, if_pos hdiv]
    intro hsucc
    exact (approximationPrime_prime g ε n).not_dvd_one
      ((Nat.dvd_add_iff_right hdiv).2 hsucc)
  · simp [approximationNumerator, p, q₀, hdiv]

private theorem approximationNumerator_pos
    {g ε : ℕ → ℝ} (hg : ∀ n, 0 < g n) (n : ℕ) :
    0 < approximationNumerator g ε n := by
  let p := approximationPrime g ε n
  let q₀ := ⌊(p : ℝ) * g n⌋₊
  have hx : 1 < (p : ℝ) * g n := one_lt_approximationPrime_mul hg n
  have hq₀ : 0 < q₀ := Nat.floor_pos.mpr hx.le
  by_cases hdiv : p ∣ q₀
  · simp [approximationNumerator, p, q₀, hdiv]
  · simpa [approximationNumerator, p, q₀, hdiv] using hq₀

/-- The rational approximant with its selected private denominator prime. -/
noncomputable def privatePrimeApproximation (g ε : ℕ → ℝ) (n : ℕ) : ℚ :=
  (approximationNumerator g ε n : ℚ) / (approximationPrime g ε n : ℚ)

private theorem privatePrimeApproximation_pos
    {g ε : ℕ → ℝ} (hg : ∀ n, 0 < g n) (n : ℕ) :
    0 < (privatePrimeApproximation g ε n : ℝ) := by
  rw [privatePrimeApproximation]
  push_cast
  exact div_pos (by exact_mod_cast approximationNumerator_pos hg n)
    (by exact_mod_cast (approximationPrime_prime g ε n).pos)

private theorem privatePrimeApproximation_sub_lt
    {g ε : ℕ → ℝ} (hg : ∀ n, 0 < g n) (hε : ∀ n, 0 < ε n) (n : ℕ) :
    |(privatePrimeApproximation g ε n : ℝ) - g n| < cappedTolerance ε n := by
  let p := approximationPrime g ε n
  let q := approximationNumerator g ε n
  let x := (p : ℝ) * g n
  let q₀ := ⌊x⌋₊
  have hp : 0 < (p : ℝ) := by
    exact_mod_cast (approximationPrime_prime g ε n).pos
  have hx : 0 ≤ x := by
    exact (mul_pos hp (hg n)).le
  have hfloor : (q₀ : ℝ) ≤ x := Nat.floor_le hx
  have hfloorSucc : x < (q₀ : ℝ) + 1 := by
    simpa using Nat.lt_floor_add_one x
  have hq : q = q₀ ∨ q = q₀ + 1 := by
    by_cases hdiv : p ∣ q₀
    · exact Or.inr (by simp [q, q₀, x, p, approximationNumerator, hdiv])
    · exact Or.inl (by simp [q, q₀, x, p, approximationNumerator, hdiv])
  have hdist : |(q : ℝ) - x| ≤ 1 := by
    rcases hq with hq | hq
    · rw [hq, abs_of_nonpos (sub_nonpos.mpr hfloor)]
      linarith
    · rw [hq, Nat.cast_add, Nat.cast_one,
        abs_of_nonneg (sub_nonneg.mpr hfloorSucc.le)]
      linarith
  have hrewrite :
      (privatePrimeApproximation g ε n : ℝ) - g n = ((q : ℝ) - x) / p := by
    rw [privatePrimeApproximation]
    push_cast
    have hp0 : (approximationPrime g ε n : ℝ) ≠ 0 := hp.ne'
    calc
      (approximationNumerator g ε n : ℝ) / approximationPrime g ε n - g n =
          (approximationNumerator g ε n : ℝ) / approximationPrime g ε n -
            ((approximationPrime g ε n : ℝ) * g n) / approximationPrime g ε n := by
              rw [mul_div_cancel_left₀ (g n) hp0]
      _ = ((approximationNumerator g ε n : ℝ) -
          (approximationPrime g ε n : ℝ) * g n) / approximationPrime g ε n :=
            (sub_div _ _ _).symm
  rw [hrewrite, abs_div, abs_of_pos hp]
  exact ((div_le_div_iff_of_pos_right hp).2 hdist).trans_lt
    (approximationPrime_inv_lt_cappedTolerance hε n)

private theorem padicNorm_natCast_eq_one_of_not_dvd {p q : ℕ}
    (hp : p.Prime) (hnot : ¬ p ∣ q) :
    padicNorm p (q : ℚ) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnotZ : ¬ (p : ℤ) ∣ (q : ℤ) := by
    simpa only [Int.natCast_dvd_natCast] using hnot
  apply le_antisymm
  · simpa using (padicNorm.of_int (q : ℤ))
  · exact not_lt.mp fun hlt => hnotZ ((padicNorm.int_lt_one_iff (q : ℤ)).mp (by simpa using hlt))

private theorem privatePrimeApproximation_padic_self
    (g ε : ℕ → ℝ) (n : ℕ) :
    1 < padicNorm (approximationPrime g ε n) (privatePrimeApproximation g ε n) := by
  let p := approximationPrime g ε n
  have hp : p.Prime := approximationPrime_prime g ε n
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : padicNorm p (approximationNumerator g ε n : ℚ) = 1 :=
    padicNorm_natCast_eq_one_of_not_dvd hp (approximationPrime_not_dvd_numerator g ε n)
  rw [privatePrimeApproximation, div_eq_mul_inv, padicNorm.mul, hq,
    padicNorm_inv_self hp, one_mul]
  exact_mod_cast hp.one_lt

private theorem privatePrimeApproximation_padic_other
    (g ε : ℕ → ℝ) {n m : ℕ} (hmn : m ≠ n) :
    padicNorm (approximationPrime g ε n) (privatePrimeApproximation g ε m) ≤ 1 := by
  let pn := approximationPrime g ε n
  let pm := approximationPrime g ε m
  have hpn : pn.Prime := approximationPrime_prime g ε n
  have hpm : pm.Prime := approximationPrime_prime g ε m
  haveI : Fact pn.Prime := ⟨hpn⟩
  have hpne : pn ≠ pm := by
    intro heq
    exact hmn ((approximationPrime_strictMono g ε).injective heq).symm
  have hnum : padicNorm pn (approximationNumerator g ε m : ℚ) ≤ 1 := by
    simpa using (padicNorm.of_int (approximationNumerator g ε m : ℤ))
  have hden : padicNorm pn (pm : ℚ)⁻¹ = 1 :=
    padicNorm_inv_coprime hpn hpm hpne
  rw [privatePrimeApproximation, div_eq_mul_inv, padicNorm.mul, hden, mul_one]
  exact hnum

/-- Every positive real profile has positive rational approximants with strictly increasing
private denominator primes and error smaller than both the requested tolerance and one. -/
theorem exists_privatePrime_rational_approximation
    (g ε : ℕ → ℝ) (hg : ∀ n, 0 < g n) (hε : ∀ n, 0 < ε n) :
    ∃ (b : ℕ → ℚ) (p : ℕ → ℕ),
      (∀ n, (p n).Prime) ∧
      StrictMono p ∧
      (∀ n, 0 < (b n : ℝ)) ∧
      (∀ n, |(b n : ℝ) - g n| < min (ε n) 1) ∧
      (∀ n, 1 < padicNorm (p n) (b n)) ∧
      (∀ n m, m ≠ n → padicNorm (p n) (b m) ≤ 1) := by
  refine ⟨privatePrimeApproximation g ε, approximationPrime g ε,
    approximationPrime_prime g ε, approximationPrime_strictMono g ε,
    privatePrimeApproximation_pos hg, ?_,
    privatePrimeApproximation_padic_self g ε, ?_⟩
  · intro n
    exact privatePrimeApproximation_sub_lt hg hε n
  · intro n m hmn
    exact privatePrimeApproximation_padic_other g ε hmn

/-- Uniform error below one preserves superlinear growth after division by the index. -/
theorem tendsto_div_natCast_atTop_of_abs_sub_lt_one
    {g b : ℕ → ℝ}
    (hg : Tendsto (fun n => g n / (n : ℝ)) atTop atTop)
    (hclose : ∀ n, |b n - g n| < 1) :
    Tendsto (fun n => b n / (n : ℝ)) atTop atTop := by
  have hminor : Tendsto (fun n => g n / (n : ℝ) - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1) hg
  refine tendsto_atTop_mono' atTop ?_ hminor
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hb : g n - 1 < b n := by
    have := (abs_lt.mp (hclose n)).1
    linarith
  have hgn : g n - (n : ℝ) ≤ b n := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  calc
    g n / (n : ℝ) - 1 = (g n - (n : ℝ)) / n := by
      field_simp
    _ ≤ b n / n := (div_le_div_iff_of_pos_right hnpos).2 hgn

/-- The internally capped private-prime approximant preserves every superlinear input profile. -/
theorem tendsto_privatePrimeApproximation_div_natCast_atTop
    {g ε : ℕ → ℝ} (hgpos : ∀ n, 0 < g n) (hε : ∀ n, 0 < ε n)
    (hg : Tendsto (fun n => g n / (n : ℝ)) atTop atTop) :
    Tendsto (fun n => (privatePrimeApproximation g ε n : ℝ) / (n : ℝ))
      atTop atTop := by
  apply tendsto_div_natCast_atTop_of_abs_sub_lt_one hg
  intro n
  exact (privatePrimeApproximation_sub_lt hgpos hε n).trans_le (min_le_right _ _)

end


end GaloisForLFunctions
