import GaloisForLFunctions.RHTower.PrimeIrrationalRotationKZeroRH
import GaloisForLFunctions.HTGeometry.KroneckerFlow


/-!
# Integral intersections of prime rotation trace lattices

For a nonzero clock denominator, finite integer prime charges and the integer rank are uniquely
recoverable from `rank + sum(m_p * log p)/(2*pi*q)`. Gelfond--Schneider excludes nonzero integral
`2*pi` relations; unique factorization excludes the remaining prime-logarithm relations.

Two consequences address IRK's trace-integrality problem:

* the trace-coordinate lattices of two distinct primes meet exactly in the integers, even at
  different rational-imaginary clocks;
* a common finite-prime trace coordinate representable after deleting every finite set of primes
  is an integer.

These are arithmetic statements about explicit coordinate lattices. Constructing a Xi projective
class, proving its descent to the relevant rotation algebras, and identifying its canonical trace
and Chern pairing remain separate source problems. No all-prime `K0` trace-range theorem is assumed
or proved here.
-/

open Complex GaloisForLFunctions
open scoped BigOperators

namespace RHTower
noncomputable section

private theorem algebraic_zpow {z : ℂ} (hz : IsAlgebraic ℚ z) (n : ℤ) :
    IsAlgebraic ℚ (z ^ n) := by
  cases n with
  | ofNat n => simpa using hz.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hz.pow (n + 1)).inv

private theorem algebraic_exp_primeLogFrequency (m : Nat.Primes →₀ ℤ) :
    IsAlgebraic ℚ (Complex.exp (primeLogFrequency m : ℂ)) := by
  have hs (S : Finset Nat.Primes) :
      IsAlgebraic ℚ (Complex.exp ((∑ p ∈ S, (m p : ℝ) * Real.log p : ℝ) : ℂ)) := by
    classical
    induction S using Finset.induction_on with
    | empty => simpa using (isAlgebraic_int (R := ℚ) (A := ℂ) 1)
    | @insert p S hp ih =>
      rw [Finset.sum_insert hp, Complex.ofReal_add, Complex.exp_add]
      apply IsAlgebraic.mul _ ih
      rw [Complex.ofReal_mul, Complex.ofReal_intCast, Complex.exp_int_mul,
        Complex.natCast_log, Complex.exp_log (by exact_mod_cast p.2.ne_zero)]
      exact algebraic_zpow (isAlgebraic_nat (R := ℚ) (A := ℂ) p) (m p)
  exact hs m.support

/-- No nonzero integer multiple of `2*pi` has algebraic real exponential. -/
theorem transcendental_exp_two_pi_mul_int {k : ℤ} (hk : k ≠ 0) :
    Transcendental ℚ (Complex.exp ((2 * Real.pi * k : ℝ) : ℂ)) := by
  have hbase : IsAlgebraic ℚ (-1 : ℂ) :=
    (isAlgebraic_one (R := ℚ) (A := ℂ)).neg
  have htwo : IsAlgebraic ℚ (-2 : ℂ) :=
    (isAlgebraic_nat (R := ℚ) (A := ℂ) 2).neg
  have hexponent : IsAlgebraic ℚ (-2 * (k : ℂ) * Complex.I) :=
    (htwo.mul (isAlgebraic_int (R := ℚ) (A := ℂ) k)).mul
      GaloisForLFunctions.RHTower.isAlgebraic_I
  have hirr : ∀ i j : ℤ, (-2 * (k : ℂ) * Complex.I) ≠ i / j := by
    intro i j hij
    have him : -2 * (k : ℝ) = 0 := by
      simpa [div_eq_mul_inv] using congrArg Complex.im hij
    have hkR : (k : ℝ) = 0 := by linarith
    exact hk (Int.cast_eq_zero.mp hkR)
  have h := GaloisForLFunctions.RHTower.GelfondSchneiderProof.Setup.transcendental_cpow_of_isAlgebraic_of_irrational
    (-1 : ℂ) (-2 * (k : ℂ) * Complex.I) hbase hexponent (by norm_num) hirr
  convert h using 1
  rw [Complex.cpow_def_of_ne_zero (by norm_num), Complex.log_neg_one]
  congr 1
  push_cast
  calc
    (2 : ℂ) * Real.pi * k = (Real.pi : ℂ) * Complex.I * (-2 * k * Complex.I) := by
      calc
        _ = -2 * Real.pi * k * (Complex.I * Complex.I) := by rw [Complex.I_mul_I]; ring
        _ = _ := by ring

/-- The prime logarithm lattice has no nonzero intersection with `2*pi*Z`. -/
theorem primeLogFrequency_eq_two_pi_mul_int_iff (m : Nat.Primes →₀ ℤ) (k : ℤ) :
    primeLogFrequency m = 2 * Real.pi * k ↔ m = 0 ∧ k = 0 := by
  constructor
  · intro h
    have hk : k = 0 := by
      by_contra hk
      apply transcendental_exp_two_pi_mul_int hk
      rw [← h]
      exact algebraic_exp_primeLogFrequency m
    refine ⟨(primeLogFrequency_eq_zero_iff m).mp ?_, hk⟩
    simpa [hk] using h
  · rintro ⟨rfl, rfl⟩
    simp [primeLogFrequency]


private theorem primeLogFrequency_sub (a b : Nat.Primes →₀ ℤ) :
    primeLogFrequency (a - b) = primeLogFrequency a - primeLogFrequency b := by
  unfold primeLogFrequency
  rw [Finsupp.sum_sub_index]
  · intro p x y
    simp [sub_mul]

/-- The finite-prime trace coordinate at the common rational-imaginary clock. -/
def primeRotationTraceCoordinate (q : ℕ) (rank : ℤ) (m : Nat.Primes →₀ ℤ) : ℝ :=
  rank + primeLogFrequency m / (2 * Real.pi * q)

/-- Integer rank and all finite prime charges are uniquely determined by the trace. -/
theorem primeRotationTraceCoordinate_eq_iff {q : ℕ} (hq : q ≠ 0)
    (r s : ℤ) (a b : Nat.Primes →₀ ℤ) :
    primeRotationTraceCoordinate q r a = primeRotationTraceCoordinate q s b ↔
      r = s ∧ a = b := by
  constructor
  · intro h
    have hD : (2 * Real.pi * q : ℝ) ≠ 0 := by positivity
    have hmul := congrArg (fun x : ℝ => x * (2 * Real.pi * q)) h
    simp only [primeRotationTraceCoordinate, add_mul, div_mul_cancel₀ _ hD] at hmul
    have hrel : primeLogFrequency (a - b) = 2 * Real.pi * (((q : ℤ) * (s - r) : ℤ) : ℝ) := by
      rw [primeLogFrequency_sub]
      push_cast
      linear_combination hmul
    obtain ⟨hab, hrs⟩ := (primeLogFrequency_eq_two_pi_mul_int_iff _ _).mp hrel
    have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq
    exact ⟨(sub_eq_zero.mp ((mul_eq_zero.mp hrs).resolve_left hqZ)).symm,
      sub_eq_zero.mp hab⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A trace representable after deleting every finite prime set is exactly an integer.
This is an arithmetic trace-lattice theorem, not a source descent hypothesis discharge. -/
theorem primeRotationTrace_tail_iff_integer {q : ℕ} (hq : q ≠ 0) (T : ℝ) :
    (∀ F : Finset Nat.Primes, ∃ r : ℤ, ∃ m : Nat.Primes →₀ ℤ,
      T = primeRotationTraceCoordinate q r m ∧ ∀ p ∈ F, m p = 0) ↔
      ∃ r : ℤ, T = (r : ℝ) := by
  classical
  constructor
  · intro h
    obtain ⟨r, m, hr, _⟩ := h ∅
    obtain ⟨s, n, hs, hn⟩ := h m.support
    have hmn := ((primeRotationTraceCoordinate_eq_iff hq r s m n).mp
      (hr.symm.trans hs)).2
    have hm : m = 0 := by
      ext p
      by_cases hp : p ∈ m.support
      · simpa [hmn] using hn p hp
      · exact Finsupp.notMem_support_iff.mp hp
    refine ⟨r, ?_⟩
    simpa [hm, primeRotationTraceCoordinate, primeLogFrequency] using hr
  · rintro ⟨r, rfl⟩ F
    exact ⟨r, 0, by simp [primeRotationTraceCoordinate, primeLogFrequency], by simp⟩

/-- The finite-prime coordinate extends the existing single-prime rotation coordinate. -/
theorem primeRotationTraceCoordinate_single (p : Nat.Primes) (q : ℕ) (r c : ℤ) :
    primeRotationTraceCoordinate q r (Finsupp.single p c) =
      irrationalRotationKZeroTrace (primeRotationParameter p q) r c := by
  simp only [primeRotationTraceCoordinate, primeLogFrequency_single,
    irrationalRotationKZeroTrace, primeRotationParameter]
  ring

/-- Equal traces at two distinct primes have zero Chern coordinates, at a common clock. -/
theorem primeRotationTrace_two_prime_eq_iff (p r : Nat.Primes) (hpr : p ≠ r)
    {q : ℕ} (hq : q ≠ 0) (a b c d : ℤ) :
    irrationalRotationKZeroTrace (primeRotationParameter p q) a c =
      irrationalRotationKZeroTrace (primeRotationParameter r q) b d ↔
      a = b ∧ c = 0 ∧ d = 0 := by
  rw [← primeRotationTraceCoordinate_single, ← primeRotationTraceCoordinate_single,
    primeRotationTraceCoordinate_eq_iff hq]
  constructor
  · rintro ⟨hab, hcd⟩
    have hc := congrArg (fun m : Nat.Primes →₀ ℤ => m p) hcd
    have hd := congrArg (fun m : Nat.Primes →₀ ℤ => m r) hcd
    exact ⟨hab, by simpa [hpr, Ne.symm hpr] using hc,
      by simpa [hpr, Ne.symm hpr] using hd.symm⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp

private theorem primeRotationTrace_change_clock (p : Nat.Primes)
    {q s : ℕ} (hq : q ≠ 0) (hs : s ≠ 0) (r c : ℤ) :
    irrationalRotationKZeroTrace (primeRotationParameter p (q * s)) r (c * s) =
      irrationalRotationKZeroTrace (primeRotationParameter p q) r c := by
  unfold irrationalRotationKZeroTrace primeRotationParameter
  push_cast
  field_simp [Real.pi_ne_zero, hq, hs]

/-- Two distinct prime trace lattices meet only on the integer axis, even with different clocks. -/
theorem primeRotationTrace_two_prime_clocks_eq_iff (p r : Nat.Primes) (hpr : p ≠ r)
    {q s : ℕ} (hq : q ≠ 0) (hs : s ≠ 0) (a b c d : ℤ) :
    irrationalRotationKZeroTrace (primeRotationParameter p q) a c =
      irrationalRotationKZeroTrace (primeRotationParameter r s) b d ↔
      a = b ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    have hcommon :
        irrationalRotationKZeroTrace (primeRotationParameter p (q * s)) a (c * s) =
          irrationalRotationKZeroTrace (primeRotationParameter r (q * s)) b (d * q) := by
      rw [primeRotationTrace_change_clock p hq hs]
      have hr := primeRotationTrace_change_clock r hs hq b d
      rw [Nat.mul_comm s q] at hr
      rw [hr]
      exact h
    obtain ⟨hab, hc, hd⟩ :=
      (primeRotationTrace_two_prime_eq_iff p r hpr (mul_ne_zero hq hs) _ _ _ _).mp hcommon
    have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq
    have hsZ : (s : ℤ) ≠ 0 := by exact_mod_cast hs
    exact ⟨hab, (mul_eq_zero.mp hc).resolve_right hsZ,
      (mul_eq_zero.mp hd).resolve_right hqZ⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp [irrationalRotationKZeroTrace]

/-- A common trace in two distinct prime coordinate ranges is exactly an integer. -/
theorem primeRotationTrace_two_prime_ranges_iff_integer
    (p r : Nat.Primes) (hpr : p ≠ r) {q s : ℕ} (hq : q ≠ 0) (hs : s ≠ 0) (T : ℝ) :
    ((∃ a c : ℤ, T = irrationalRotationKZeroTrace (primeRotationParameter p q) a c) ∧
      (∃ b d : ℤ, T = irrationalRotationKZeroTrace (primeRotationParameter r s) b d)) ↔
      ∃ a : ℤ, T = (a : ℝ) := by
  constructor
  · rintro ⟨⟨a, c, ha⟩, ⟨b, d, hb⟩⟩
    have hc := ((primeRotationTrace_two_prime_clocks_eq_iff p r hpr hq hs a b c d).mp
      (ha.symm.trans hb)).2.1
    exact ⟨a, by simpa [hc, irrationalRotationKZeroTrace] using ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, 0, by simp [irrationalRotationKZeroTrace]⟩,
      ⟨a, 0, by simp [irrationalRotationKZeroTrace]⟩⟩

end
end RHTower
