import GaloisForLFunctions.RHTower.CausalMobiusThetaTail
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDivisorProduct
import Mathlib.NumberTheory.Primorial

/-!
# The finite-prime moving-cusp form of the causal theta criterion

Let `k = thetaCuspFullSource` and `P_Y = ∏_{p ≤ Y} p`.  The finite Euler-deleted source
`k_Y(x) = ∏_{p ≤ Y} (1 − p^{−1/2} T_{log p}) k(x)` is the squarefree Möbius sum
`∑_{d ∣ P_Y} μ(d) d^{−1/2} k(x + log d)`.  Its directed positive-ray port at `x = −log N` keeps the
terms whose shifted arguments are positive,

`B_Y(N) = ∑_{d ∣ P_Y, d > N} μ(d) d^{−1/2} k(log(d/N))`.

With the moving horizon `Y_N = N log N`, every integer present in the causal tail `B(N)` but
missing from the port has a prime factor above `Y_N`; the Gaussian atom bound
`|k(log u)| + |k'(log u)| ≤ C (1+u)^C e^{−π u²}` makes their total `O_A(N^{−A})` for every `A`.
The causal tail moves by `O(N^{−1/2})` across each unit interval, so the criterion
`RH ⟺ B(t) = O(t^ε)` becomes the entirely finite `RH ⟺ B_{Y_N}(N) = O(N^ε)`.  An off-line zero
`ρ` forces `limsup N^{−(Re ρ − 1/2)+δ} |B_{Y_N}(N)| = ∞` for every `0 < δ < Re ρ − 1/2`.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics Polynomial

namespace RHTower

noncomputable section

/-! ### The Gaussian atom bound -/

/-- **Gaussian decay of every source derivative.**  For `x ≥ 0`,
`|k^{(m)}(x)| ≤ C e^{Dx} e^{−π e^{2x}}`. -/
theorem exists_abs_iteratedDeriv_thetaCuspFullSource_le_gaussian (m : ℕ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ x : ℝ, 0 ≤ x →
      |iteratedDeriv m thetaCuspFullSource x| ≤
        C * Real.exp (D * x) * Real.exp (-Real.pi * Real.exp (2 * x)) := by
  set P : ℝ[X] := thetaCuspLogDerivativePolynomial m with hP
  set S : ℝ := thetaCuspCoeffMass P with hS
  set Dn : ℕ := P.natDegree with hDn
  have hS0 : 0 ≤ S := thetaCuspCoeffMass_nonneg P
  set G : ℝ := ∑' n : ℕ, (n : ℝ) ^ Dn * Real.exp (-Real.pi * (n : ℝ) ^ 2) with hG
  have hGs : Summable (fun n : ℕ => (n : ℝ) ^ Dn * Real.exp (-Real.pi * (n : ℝ) ^ 2)) :=
    summable_pow_mul_exp_neg_nat_sq Dn Real.pi_pos
  have hG0 : 0 ≤ G := tsum_nonneg (fun n => by positivity)
  refine ⟨S * Real.exp Real.pi * G, Dn + 1 / 2, by positivity, by positivity, fun x hx => ?_⟩
  have hu1 : 1 ≤ Real.exp x := Real.one_le_exp hx
  have ha : Summable (fun n : ℕ => thetaCuspPolynomialAtom P n x) := by
    have h := summable_iteratedDeriv_thetaCuspSourceTerm m x
    simpa only [hP, iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom] using h
  have hatom : ∀ n : ℕ, |thetaCuspPolynomialAtom P n x| ≤
      S * Real.exp Real.pi * ((n : ℝ) ^ Dn * Real.exp (-Real.pi * (n : ℝ) ^ 2)) *
        (Real.exp ((Dn + 1 / 2) * x) * Real.exp (-Real.pi * Real.exp (2 * x))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [show thetaCuspPolynomialAtom P 0 x = 0 from thetaCuspPolynomialAtom_derivative_zero m x,
        abs_zero]
      positivity
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hv : 1 ≤ (n : ℝ) * Real.exp x := one_le_mul_of_one_le_of_one_le hn1 hu1
    unfold thetaCuspPolynomialAtom
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have hpoly := abs_eval_le_coeffMass_mul_pow P hv
    have hexp : Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ (2 : ℕ)) ≤
        Real.exp Real.pi * Real.exp (-Real.pi * (n : ℝ) ^ 2) *
          Real.exp (-Real.pi * Real.exp (2 * x)) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have he2 : Real.exp (2 * x) = Real.exp x ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [he2]
      have h1 : (1 : ℝ) ≤ Real.exp x ^ 2 := one_le_pow₀ hu1
      have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
      have key : (n : ℝ) ^ 2 + Real.exp x ^ 2 - 1 ≤ ((n : ℝ) * Real.exp x) ^ 2 := by
        rw [mul_pow]
        nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h1)]
      nlinarith [mul_le_mul_of_nonneg_left key Real.pi_pos.le]
    have hpow : ((n : ℝ) * Real.exp x) ^ Dn = (n : ℝ) ^ Dn * Real.exp (Dn * x) := by
      rw [mul_pow, ← Real.exp_nat_mul]
    have hsplit : Real.exp (x / 2) * Real.exp (Dn * x) = Real.exp ((Dn + 1 / 2) * x) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (x / 2) * |P.eval ((n : ℝ) * Real.exp x)| *
          Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ (2 : ℕ))
        ≤ Real.exp (x / 2) * (S * ((n : ℝ) ^ Dn * Real.exp (Dn * x))) *
          (Real.exp Real.pi * Real.exp (-Real.pi * (n : ℝ) ^ 2) *
            Real.exp (-Real.pi * Real.exp (2 * x))) := by
          rw [← hpow]; gcongr
      _ = S * Real.exp Real.pi * ((n : ℝ) ^ Dn * Real.exp (-Real.pi * (n : ℝ) ^ 2)) *
          ((Real.exp (x / 2) * Real.exp (Dn * x)) * Real.exp (-Real.pi * Real.exp (2 * x))) := by
          ring
      _ = _ := by rw [hsplit]
  rw [iteratedDeriv_thetaCuspFullSource, thetaCuspFullDerivative]
  simp_rw [iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom]
  rw [← hP]
  calc |∑' n, thetaCuspPolynomialAtom P n x| ≤ ∑' n, |thetaCuspPolynomialAtom P n x| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm ha.norm
    _ ≤ ∑' n : ℕ, S * Real.exp Real.pi * ((n : ℝ) ^ Dn * Real.exp (-Real.pi * (n : ℝ) ^ 2)) *
          (Real.exp ((Dn + 1 / 2) * x) * Real.exp (-Real.pi * Real.exp (2 * x))) :=
        ha.abs.tsum_le_tsum hatom ((hGs.mul_left _).mul_right _)
    _ = S * Real.exp Real.pi * G * Real.exp ((Dn + 1 / 2) * x) *
          Real.exp (-Real.pi * Real.exp (2 * x)) := by
        rw [tsum_mul_right, tsum_mul_left, hG]; ring

/-- **The Gaussian atom bound (4).**  There are `C, c > 0` with
`|k(log u)| + |k'(log u)| ≤ C (1 + u)^C e^{−c u²}` for every `u ≥ 1`. -/
theorem exists_thetaCuspFullSource_log_gaussian_bound :
    ∃ C c : ℝ, 0 < c ∧ ∀ u : ℝ, 1 ≤ u →
      |thetaCuspFullSource (Real.log u)| + |deriv thetaCuspFullSource (Real.log u)| ≤
        C * (1 + u) ^ C * Real.exp (-c * u ^ 2) := by
  obtain ⟨C₀, D₀, hC₀, hD₀, h₀⟩ := exists_abs_iteratedDeriv_thetaCuspFullSource_le_gaussian 0
  obtain ⟨C₁, D₁, hC₁, hD₁, h₁⟩ := exists_abs_iteratedDeriv_thetaCuspFullSource_le_gaussian 1
  set C : ℝ := C₀ + C₁ + D₀ + D₁ + 1 with hC
  refine ⟨C, Real.pi, Real.pi_pos, fun u hu => ?_⟩
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hx : 0 ≤ Real.log u := Real.log_nonneg hu
  have hexp2 : Real.exp (2 * Real.log u) = u ^ 2 := by
    rw [show 2 * Real.log u = ((2 : ℕ) : ℝ) * Real.log u by norm_num, Real.exp_nat_mul,
      Real.exp_log hu0]
  have hpowD : ∀ D : ℝ, 0 ≤ D → D ≤ C → Real.exp (D * Real.log u) ≤ (1 + u) ^ C := by
    intro D hD hDC
    rw [mul_comm, ← Real.rpow_def_of_pos hu0]
    calc u ^ D ≤ (1 + u) ^ D := Real.rpow_le_rpow hu0.le (by linarith) hD
      _ ≤ (1 + u) ^ C := Real.rpow_le_rpow_of_exponent_le (by linarith) hDC
  have hk0 := h₀ (Real.log u) hx
  have hk1 := h₁ (Real.log u) hx
  simp only [iteratedDeriv_zero] at hk0
  rw [iteratedDeriv_one] at hk1
  rw [hexp2] at hk0 hk1
  have hg : 0 ≤ Real.exp (-Real.pi * u ^ 2) := (Real.exp_pos _).le
  have hP : 0 ≤ (1 + u) ^ C := Real.rpow_nonneg (by linarith) _
  have e0 := hpowD D₀ hD₀ (by linarith)
  have e1 := hpowD D₁ hD₁ (by linarith)
  calc |thetaCuspFullSource (Real.log u)| + |deriv thetaCuspFullSource (Real.log u)|
      ≤ C₀ * Real.exp (D₀ * Real.log u) * Real.exp (-Real.pi * u ^ 2) +
          C₁ * Real.exp (D₁ * Real.log u) * Real.exp (-Real.pi * u ^ 2) := add_le_add hk0 hk1
    _ ≤ C₀ * (1 + u) ^ C * Real.exp (-Real.pi * u ^ 2) +
          C₁ * (1 + u) ^ C * Real.exp (-Real.pi * u ^ 2) := by gcongr
    _ ≤ C * (1 + u) ^ C * Real.exp (-Real.pi * u ^ 2) := by
        have : C₀ + C₁ ≤ C := by linarith
        nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hP hg)]

/-! ### The finite source and its directed port -/

/-- The primes up to `Y`. -/
def primesAtMost (Y : ℕ) : Finset ℕ := (Finset.range (Y + 1)).filter Nat.Prime

theorem primorial_eq_prod_primesAtMost (Y : ℕ) : primorial Y = ∏ p ∈ primesAtMost Y, p := rfl

theorem prime_of_mem_primesAtMost {Y p : ℕ} (hp : p ∈ primesAtMost Y) : p.Prime :=
  (Finset.mem_filter.mp hp).2

theorem moebius_prod_of_primes {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) :
    ArithmeticFunction.moebius (∏ p ∈ T, p) = (-1) ^ T.card := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_prod_of_prime T hT]
  rw [Finset.prod_congr rfl (fun p hp => ArithmeticFunction.moebius_apply_prime (hT p hp))]
  simp

/-- **The squarefree Möbius identity.**  The finite prime deletion is the divisor sum
`∑_{d ∣ ∏S} μ(d) d^{−1/2} f(x + log d)`. -/
theorem thetaPrimeDeletion_eq_sum_divisors (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (f : ℝ → ℝ) (x : ℝ) :
    thetaPrimeDeletion S f x = ∑ d ∈ (∏ p ∈ S, p).divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 / 2 : ℝ)) *
        f (x + Real.log d) := by
  rw [Sieve.sum_divisors_prod_primes_eq hS, thetaPrimeDeletion]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  have hTS : ∀ p ∈ T, p.Prime := fun p hp => hS p (Finset.mem_powerset.mp hT hp)
  rw [moebius_prod_of_primes hTS]
  push_cast
  ring

/-- The moving prime horizon `Y_N = ⌊N log N⌋`. -/
def movingCuspHorizon (N : ℕ) : ℕ := ⌊(N : ℝ) * Real.log N⌋₊

/-- **The directed positive-ray port (1).**
`B_Y(x) = ∑_{d ∣ P_Y, d > x} μ(d) d^{−1/2} k(log(d/x))`. -/
def finitePrimeCausalPort (Y : ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ (primorial Y).divisors, causalMobiusThetaTerm x d

/-- The moving-cusp port `B_{Y_N}(N)`. -/
def movingCuspPort (N : ℕ) : ℝ := finitePrimeCausalPort (movingCuspHorizon N) N

/-- **The port is the positive-ray part of the Euler-deleted source at `−log x`.**  The unsplit
value `k_Y(−log x)` also carries the terms `d ≤ x`. -/
theorem thetaPrimeDeletion_neg_log_eq_add_port (Y : ℕ) {x : ℝ} (hx : 0 < x) :
    thetaPrimeDeletion (primesAtMost Y) thetaCuspFullSource (-Real.log x) =
      (∑ d ∈ (primorial Y).divisors.filter (fun d : ℕ => (d : ℝ) ≤ x),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-(1 / 2 : ℝ)) *
          thetaCuspFullSource (Real.log (d / x))) +
        finitePrimeCausalPort Y x := by
  classical
  rw [thetaPrimeDeletion_eq_sum_divisors _ (fun p hp => prime_of_mem_primesAtMost hp),
    ← primorial_eq_prod_primesAtMost, finitePrimeCausalPort,
    ← Finset.sum_filter_add_sum_filter_not _ (fun d : ℕ => (d : ℝ) ≤ x)]
  congr 1
  · refine Finset.sum_congr rfl (fun d hd => ?_)
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
    rw [Real.log_div hd0.ne' hx.ne']; ring_nf
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    by_cases hdx : (d : ℝ) ≤ x
    · rw [if_neg (not_not.mpr hdx)]
      simp only [causalMobiusThetaTerm]
      exact (Set.indicator_of_notMem (fun h => not_lt.mpr hdx h.2) _).symm
    · rw [if_pos hdx]
      simp only [causalMobiusThetaTerm]
      rw [Set.indicator_of_mem (show x ∈ Ioo 0 (d : ℝ) from ⟨hx, lt_of_not_ge hdx⟩),
        Real.log_div hd0.ne' hx.ne']
      ring_nf


/-! ### Gaussian truncation of the missing integers -/

/-- An integer missing from the port but present in the causal tail exceeds the prime horizon. -/
theorem lt_of_causalMobiusThetaTerm_ne_zero_of_notMem_divisors {Y n : ℕ} {x : ℝ}
    (hn : n ∉ (primorial Y).divisors) (hterm : causalMobiusThetaTerm x n ≠ 0) : Y < n := by
  by_contra hle
  push Not at hle
  apply hn
  have hmu : ArithmeticFunction.moebius n ≠ 0 := by
    intro h0
    apply hterm
    simp [causalMobiusThetaTerm, h0]
  have hsq : Squarefree n := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
  have hn0 : n ≠ 0 := hsq.ne_zero
  refine Nat.mem_divisors.mpr ⟨?_, (primorial_pos Y).ne'⟩
  rw [← Nat.prod_primeFactors_of_squarefree hsq, primorial_eq_prod_primesAtMost]
  refine Finset.prod_dvd_prod_of_subset _ _ id (fun p hp => ?_)
  have hpn : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_primeFactors hp)
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_of_mem_primeFactors hp⟩

theorem finitePrimeCausalPort_eq_tsum (Y : ℕ) (x : ℝ) :
    finitePrimeCausalPort Y x = ∑' n : ℕ,
      Set.indicator (↑(primorial Y).divisors) (fun n => causalMobiusThetaTerm x n) n := by
  rw [finitePrimeCausalPort, tsum_eq_sum (s := (primorial Y).divisors)
    (fun n hn => Set.indicator_of_notMem hn _)]
  exact Finset.sum_congr rfl (fun n hn => (Set.indicator_of_mem hn _).symm)

/-- **The missing integers.**  `|B(x) − B_Y(x)| ≤ ∑_{n > Y} |μ(n) n^{−1/2} k(log(n/x))|`. -/
theorem abs_causalMobiusThetaTail_sub_port_le (Y : ℕ) (x : ℝ) :
    |causalMobiusThetaTail x - finitePrimeCausalPort Y x| ≤
      ∑' n : ℕ, if Y < n then |causalMobiusThetaTerm x n| else 0 := by
  classical
  have hsum := summable_causalMobiusThetaTerm x
  have hind : Summable (fun n : ℕ =>
      Set.indicator (↑(primorial Y).divisors) (fun n => causalMobiusThetaTerm x n) n) :=
    summable_of_ne_finset_zero (s := (primorial Y).divisors)
      (fun n hn => Set.indicator_of_notMem hn _)
  have hbound : Summable (fun n : ℕ => if Y < n then |causalMobiusThetaTerm x n| else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> simp [abs_nonneg]) hsum.abs
  rw [finitePrimeCausalPort_eq_tsum, causalMobiusThetaTail, ← hsum.tsum_sub hind]
  have hdiff : Summable (fun n : ℕ => causalMobiusThetaTerm x n -
      Set.indicator (↑(primorial Y).divisors) (fun n => causalMobiusThetaTerm x n) n) :=
    hsum.sub hind
  have hnorm : |∑' n : ℕ, (causalMobiusThetaTerm x n -
      Set.indicator (↑(primorial Y).divisors) (fun n => causalMobiusThetaTerm x n) n)| ≤
      ∑' n : ℕ, |causalMobiusThetaTerm x n -
        Set.indicator (↑(primorial Y).divisors) (fun n => causalMobiusThetaTerm x n) n| := by
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hdiff.norm
  refine hnorm.trans (hdiff.abs.tsum_le_tsum (fun n => ?_) hbound)
  by_cases hmem : n ∈ (primorial Y).divisors
  · rw [Set.indicator_of_mem (show n ∈ (↑(primorial Y).divisors : Set ℕ) from hmem), sub_self,
      abs_zero]
    split_ifs <;> positivity
  · rw [Set.indicator_of_notMem (show n ∉ (↑(primorial Y).divisors : Set ℕ) from hmem), sub_zero]
    by_cases hterm : causalMobiusThetaTerm x n = 0
    · rw [hterm, abs_zero]; split_ifs <;> positivity
    · rw [if_pos (lt_of_causalMobiusThetaTerm_ne_zero_of_notMem_divisors hmem hterm)]

theorem three_lt_exp_one_lt : Real.exp 1 < 3 := by
  have := Real.exp_one_lt_d9; norm_num at this; linarith

theorem one_lt_log_of_three_le {N : ℝ} (hN : 3 ≤ N) : 1 < Real.log N := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  linarith [three_lt_exp_one_lt]

/-- `u^6 e^{−πu²/4} ≤ 384/π³`. -/
theorem pow_six_mul_exp_neg_quarter_le (u : ℝ) :
    u ^ 6 * Real.exp (-(Real.pi * u ^ 2 / 4)) ≤ 384 / Real.pi ^ 3 := by
  have h := Real.pow_div_factorial_le_exp (Real.pi * u ^ 2 / 4) (by positivity) 3
  have hfac : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfac] at h
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  have : (Real.pi * u ^ 2 / 4) ^ 3 = Real.pi ^ 3 * u ^ 6 / 64 := by ring
  rw [this] at h
  nlinarith [h]

/-- **The Gaussian tail of the missing integers.**  For `N ≥ 3`,
`∑_{n > Y_N} |μ(n) n^{−1/2} k(log(n/N))| ≤ K N² e^{−(π/2)(log N)²}`. -/
theorem exists_tsum_missing_le_gaussian :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 3 ≤ N →
      (∑' n : ℕ, if movingCuspHorizon N < n then |causalMobiusThetaTerm N n| else 0) ≤
        K * (N : ℝ) ^ 2 * Real.exp (-(Real.pi / 2 * Real.log N ^ 2)) := by
  set E : ℝ := HedenmalmThetaSource.thetaEnvelopeUpper with hE
  have hE0 : 0 ≤ E := HedenmalmThetaSource.thetaEnvelopeUpper_pos.le
  refine ⟨E * (384 / Real.pi ^ 3) * (8 / Real.pi), by positivity, fun N hN => ?_⟩
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set L : ℝ := Real.log N with hL
  have hL1 : 1 < L := one_lt_log_of_three_le hNR
  set a : ℝ := Real.pi / (4 * (N : ℝ) ^ 2) with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one (by positivity)]; nlinarith [Real.pi_lt_four]
  set r : ℝ := Real.exp (-a) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : ∑' n : ℕ, r ^ n ≤ 8 * (N : ℝ) ^ 2 / Real.pi := by
    rw [tsum_geometric_of_lt_one hr0 hr1]
    have h1 : a / 2 ≤ 1 - r := by
      have := Real.add_one_le_exp a
      have hr' : r = (Real.exp a)⁻¹ := by rw [hr, Real.exp_neg]
      rw [hr']
      have hea : 0 < Real.exp a := Real.exp_pos a
      rw [le_sub_iff_add_le, ← le_sub_iff_add_le', inv_le_comm₀ hea (by linarith)]
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
      nlinarith
    have h2 : 0 < 1 - r := by linarith
    rw [inv_le_comm₀ h2 (by positivity)]
    calc (8 * (N : ℝ) ^ 2 / Real.pi)⁻¹ = a / 2 := by rw [ha]; field_simp; ring
      _ ≤ 1 - r := h1
  have hterm : ∀ n : ℕ, (if movingCuspHorizon N < n then |causalMobiusThetaTerm N n| else 0) ≤
      E * (384 / Real.pi ^ 3) * Real.exp (-(Real.pi / 2 * L ^ 2)) * r ^ n := by
    intro n
    split_ifs with hY
    swap
    · positivity
    have hnlog : (N : ℝ) * L < n := by
      rw [movingCuspHorizon, Nat.floor_lt (by positivity)] at hY
      exact hY
    have hn1 : (1 : ℝ) ≤ n := by
      have : (N : ℝ) * L ≥ 1 := by nlinarith
      linarith
    have hn0 : (0 : ℝ) < n := by linarith
    set u : ℝ := n / N with hu
    have huL : L < u := by rw [hu, lt_div_iff₀ hN0]; linarith
    have hu1 : 1 ≤ u := by linarith
    have hu0 : 0 < u := by linarith
    have hx0 : 0 ≤ Real.log u := Real.log_nonneg hu1
    simp only [causalMobiusThetaTerm]
    by_cases hmem : (N : ℝ) ∈ Ioo 0 (n : ℝ)
    swap
    · rw [Set.indicator_of_notMem hmem, abs_zero]; positivity
    rw [Set.indicator_of_mem hmem, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn0 _),
      abs_of_pos (thetaCuspFullSource_pos_all _)]
    have hk := HedenmalmThetaSource.thetaCuspFullSource_le_envelope hx0
    rw [← hE] at hk
    have henv : HedenmalmThetaSource.thetaEnvelope (Real.log u) ≤ u ^ 6 * Real.exp (-(Real.pi * u ^ 2)) := by
      unfold HedenmalmThetaSource.thetaEnvelope
      rw [show 2 * Real.log u = ((2 : ℕ) : ℝ) * Real.log u by norm_num, Real.exp_nat_mul,
        Real.exp_log hu0, neg_mul]
      gcongr
      rw [show 9 * Real.log u / 2 = Real.log u * (9 / 2) by ring, ← Real.rpow_def_of_pos hu0,
        show (u ^ 6 : ℝ) = u ^ (6 : ℝ) by norm_num]
      exact Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
    have hsplit : u ^ 6 * Real.exp (-(Real.pi * u ^ 2)) ≤
        (384 / Real.pi ^ 3) * Real.exp (-(Real.pi / 2 * L ^ 2)) * r ^ n := by
      have e1 : Real.exp (-(Real.pi * u ^ 2)) = Real.exp (-(Real.pi * u ^ 2 / 4)) *
          Real.exp (-(Real.pi * u ^ 2 / 4)) * Real.exp (-(Real.pi * u ^ 2 / 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      have e2 : Real.exp (-(Real.pi * u ^ 2 / 2)) ≤ Real.exp (-(Real.pi / 2 * L ^ 2)) := by
        rw [Real.exp_le_exp]
        have : L ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by linarith) huL.le 2
        nlinarith [Real.pi_pos]
      have e3 : Real.exp (-(Real.pi * u ^ 2 / 4)) ≤ r ^ n := by
        rw [hr, ← Real.exp_nat_mul, Real.exp_le_exp, ha]
        have hun : (n : ℝ) / (N : ℝ) ^ 2 ≤ u ^ 2 := by
          rw [hu, div_pow, div_le_div_iff_of_pos_right (by positivity)]
          nlinarith
        have : (n : ℝ) * -(Real.pi / (4 * (N : ℝ) ^ 2)) = -(Real.pi * ((n : ℝ) / (N : ℝ) ^ 2) / 4) := by
          field_simp
        rw [this]
        nlinarith [Real.pi_pos]
      rw [e1]
      have h6 := pow_six_mul_exp_neg_quarter_le u
      calc u ^ 6 * (Real.exp (-(Real.pi * u ^ 2 / 4)) * Real.exp (-(Real.pi * u ^ 2 / 4)) *
            Real.exp (-(Real.pi * u ^ 2 / 2)))
          = (u ^ 6 * Real.exp (-(Real.pi * u ^ 2 / 4))) * Real.exp (-(Real.pi * u ^ 2 / 2)) *
              Real.exp (-(Real.pi * u ^ 2 / 4)) := by ring
        _ ≤ (384 / Real.pi ^ 3) * Real.exp (-(Real.pi / 2 * L ^ 2)) * r ^ n := by
            gcongr
    have hlogu : Real.log ((n : ℝ) / N) = Real.log u := rfl
    have hmu := Sieve.abs_moebius_real_le_one n
    have hrp : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
    calc |((ArithmeticFunction.moebius n : ℤ) : ℝ)| * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          thetaCuspFullSource (Real.log ((n : ℝ) / N))
        ≤ 1 * 1 * (E * HedenmalmThetaSource.thetaEnvelope (Real.log u)) := by
          rw [hlogu]
          exact mul_le_mul (mul_le_mul hmu hrp (by positivity) zero_le_one) hk
            (thetaCuspFullSource_pos_all _).le (by norm_num)
      _ ≤ 1 * 1 * (E * (u ^ 6 * Real.exp (-(Real.pi * u ^ 2)))) := by gcongr
      _ ≤ 1 * 1 * (E * ((384 / Real.pi ^ 3) * Real.exp (-(Real.pi / 2 * L ^ 2)) * r ^ n)) := by
          gcongr
      _ = E * (384 / Real.pi ^ 3) * Real.exp (-(Real.pi / 2 * L ^ 2)) * r ^ n := by ring
  have hsumr : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  calc (∑' n : ℕ, if movingCuspHorizon N < n then |causalMobiusThetaTerm N n| else 0)
      ≤ ∑' n : ℕ, E * (384 / Real.pi ^ 3) * Real.exp (-(Real.pi / 2 * L ^ 2)) * r ^ n :=
        (Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hterm
          (hsumr.mul_left _)).tsum_le_tsum hterm (hsumr.mul_left _)
    _ = E * (384 / Real.pi ^ 3) * Real.exp (-(Real.pi / 2 * L ^ 2)) * ∑' n : ℕ, r ^ n :=
        tsum_mul_left
    _ ≤ E * (384 / Real.pi ^ 3) * Real.exp (-(Real.pi / 2 * L ^ 2)) *
          (8 * (N : ℝ) ^ 2 / Real.pi) := by gcongr
    _ = E * (384 / Real.pi ^ 3) * (8 / Real.pi) * (N : ℝ) ^ 2 *
          Real.exp (-(Real.pi / 2 * L ^ 2)) := by ring

/-- `N² e^{−(π/2)(log N)²} ≤ e^{(A+2)²/(2π)} N^{−A}`. -/
theorem sq_mul_exp_neg_log_sq_le {N A : ℝ} (hN : 0 < N) :
    N ^ 2 * Real.exp (-(Real.pi / 2 * Real.log N ^ 2)) ≤
      Real.exp ((A + 2) ^ 2 / (2 * Real.pi)) * N ^ (-A) := by
  have hN2 : N ^ 2 = Real.exp (2 * Real.log N) := by
    rw [show 2 * Real.log N = ((2 : ℕ) : ℝ) * Real.log N by norm_num, Real.exp_nat_mul,
      Real.exp_log hN]
  rw [hN2, Real.rpow_def_of_pos hN, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hpi := Real.pi_pos
  have key : 0 ≤ Real.pi / 2 * (Real.log N - (A + 2) / Real.pi) ^ 2 := by positivity
  have : Real.pi / 2 * (Real.log N - (A + 2) / Real.pi) ^ 2 =
      Real.pi / 2 * Real.log N ^ 2 - (A + 2) * Real.log N + (A + 2) ^ 2 / (2 * Real.pi) := by
    field_simp; ring
  nlinarith

/-- **The superpolynomial truncation (2).**  For every `A > 0`,
`B_{Y_N}(N) = B(N) + O_A(N^{−A})` on integers `N ≥ 3`. -/
theorem exists_abs_movingCuspPort_sub_le (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 3 ≤ N →
      |movingCuspPort N - causalMobiusThetaTail N| ≤ C * (N : ℝ) ^ (-A) := by
  obtain ⟨K, hK0, hK⟩ := exists_tsum_missing_le_gaussian
  refine ⟨K * Real.exp ((A + 2) ^ 2 / (2 * Real.pi)), by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [abs_sub_comm]
  calc |causalMobiusThetaTail N - movingCuspPort N|
      ≤ ∑' n : ℕ, if movingCuspHorizon N < n then |causalMobiusThetaTerm N n| else 0 :=
        abs_causalMobiusThetaTail_sub_port_le _ _
    _ ≤ K * (N : ℝ) ^ 2 * Real.exp (-(Real.pi / 2 * Real.log N ^ 2)) := hK N hN
    _ = K * ((N : ℝ) ^ 2 * Real.exp (-(Real.pi / 2 * Real.log N ^ 2))) := by ring
    _ ≤ K * (Real.exp ((A + 2) ^ 2 / (2 * Real.pi)) * (N : ℝ) ^ (-A)) :=
        mul_le_mul_of_nonneg_left (sq_mul_exp_neg_log_sq_le hN0) hK0
    _ = K * Real.exp ((A + 2) ^ 2 / (2 * Real.pi)) * (N : ℝ) ^ (-A) := by ring

/-- **The Gaussian tail estimate (5)**, in the card's shape:
`|B(N) − B_{Y_N}(N)| ≤ C √N (1 + log N)^C e^{−c'(log N)²}` for `N ≥ 3`. -/
theorem exists_abs_causalTail_sub_movingCuspPort_le_gaussian :
    ∃ C c : ℝ, 0 < c ∧ ∀ N : ℕ, 3 ≤ N →
      |causalMobiusThetaTail N - movingCuspPort N| ≤
        C * Real.sqrt N * (1 + Real.log N) ^ C * Real.exp (-(c * Real.log N ^ 2)) := by
  obtain ⟨K, hK0, hK⟩ := exists_tsum_missing_le_gaussian
  set C : ℝ := K * Real.exp (9 / (4 * Real.pi)) with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, Real.pi / 4, by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hpow : 1 ≤ (1 + Real.log N) ^ C := Real.one_le_rpow (by linarith) hC0
  have hkey : (N : ℝ) ^ 2 * Real.exp (-(Real.pi / 2 * Real.log N ^ 2)) ≤
      Real.exp (9 / (4 * Real.pi)) * Real.sqrt N * Real.exp (-(Real.pi / 4 * Real.log N ^ 2)) := by
    have hsq : Real.sqrt N = Real.exp (Real.log N / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hN0]; ring_nf
    have hN2 : (N : ℝ) ^ 2 = Real.exp (2 * Real.log N) := by
      rw [show 2 * Real.log N = ((2 : ℕ) : ℝ) * Real.log N by norm_num, Real.exp_nat_mul,
        Real.exp_log hN0]
    rw [hsq, hN2, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have hpi := Real.pi_pos
    have key : 0 ≤ Real.pi / 4 * (Real.log N - 3 / Real.pi) ^ 2 := by positivity
    have : Real.pi / 4 * (Real.log N - 3 / Real.pi) ^ 2 =
        Real.pi / 4 * Real.log N ^ 2 - 3 / 2 * Real.log N + 9 / (4 * Real.pi) := by
      field_simp; ring
    nlinarith
  calc |causalMobiusThetaTail N - movingCuspPort N|
      ≤ ∑' n : ℕ, if movingCuspHorizon N < n then |causalMobiusThetaTerm N n| else 0 :=
        abs_causalMobiusThetaTail_sub_port_le _ _
    _ ≤ K * (N : ℝ) ^ 2 * Real.exp (-(Real.pi / 2 * Real.log N ^ 2)) := hK N hN
    _ ≤ K * (Real.exp (9 / (4 * Real.pi)) * Real.sqrt N *
          Real.exp (-(Real.pi / 4 * Real.log N ^ 2))) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hkey hK0
    _ = C * Real.sqrt N * 1 * Real.exp (-(Real.pi / 4 * Real.log N ^ 2)) := by rw [hC]; ring
    _ ≤ C * Real.sqrt N * (1 + Real.log N) ^ C * Real.exp (-(Real.pi / 4 * Real.log N ^ 2)) := by
        gcongr


/-! ### Regularity across a unit interval -/

/-- The tail over the fixed indices `n ≥ N + 1`, read at the cusp `t`. -/
def causalTailFrom (N : ℕ) (t : ℝ) : ℝ :=
  ∑' j : ℕ, ((ArithmeticFunction.moebius (j + N + 1) : ℤ) : ℝ) *
    causalProfile t ((j + N + 1 : ℕ) : ℝ)

theorem summable_causalTailFrom {N : ℕ} {t : ℝ} (ht : 0 < t) (htN : t ≤ N + 1) :
    Summable (fun j : ℕ => ((ArithmeticFunction.moebius (j + N + 1) : ℤ) : ℝ) *
      causalProfile t ((j + N + 1 : ℕ) : ℝ)) := by
  obtain ⟨D, _, hD⟩ := exists_causalProfile_bounds
  have hs := (summable_nat_add_iff (N + 1)).mpr summable_natCast_rpow_neg_five_halves
  refine Summable.of_norm_bounded (hs.mul_left (D * t ^ 2)) (fun j => ?_)
  have htj : t ≤ ((j + N + 1 : ℕ) : ℝ) := by
    push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  rw [Real.norm_eq_abs, abs_mul]
  calc |((ArithmeticFunction.moebius (j + N + 1) : ℤ) : ℝ)| *
        |causalProfile t ((j + N + 1 : ℕ) : ℝ)|
      ≤ 1 * (D * t ^ 2 * ((j + N + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul (Sieve.abs_moebius_real_le_one _) (hD t _ ht htj).1 (abs_nonneg _) zero_le_one
    _ = D * t ^ 2 * (((j + (N + 1) : ℕ) : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) := by
        rw [one_mul, show j + N + 1 = j + (N + 1) by ring]

theorem causalMobiusThetaTail_eq_causalTailFrom {N : ℕ} {t : ℝ} (hNt : (N : ℝ) ≤ t)
    (htN : t < N + 1) (ht : 0 < t) : causalMobiusThetaTail t = causalTailFrom N t := by
  have hfl : ⌊t⌋₊ = N := (Nat.floor_eq_iff ht.le).mpr ⟨hNt, htN⟩
  rw [causalMobiusThetaTail_eq_tsum_shift ht, hfl, causalTailFrom]

theorem causalMobiusThetaTail_succ_eq {N : ℕ} :
    causalMobiusThetaTail ((N : ℝ) + 1) = causalTailFrom N ((N : ℝ) + 1) -
      ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℝ) *
        causalProfile ((N : ℝ) + 1) ((N + 1 : ℕ) : ℝ) := by
  have ht : (0 : ℝ) < N + 1 := by positivity
  have hfl : ⌊(N : ℝ) + 1⌋₊ = N + 1 := by
    rw [show (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  rw [causalMobiusThetaTail_eq_tsum_shift ht, hfl, causalTailFrom,
    (summable_causalTailFrom (N := N) ht le_rfl).tsum_eq_zero_add]
  simp only [zero_add]
  have : ∀ j : ℕ, j + 1 + N + 1 = j + (N + 1) + 1 := fun j => by ring
  simp_rw [this]
  ring

/-- **The unit-interval regularity (7).**  `sup_{N ≤ t ≤ N+1} |B(t) − B(N)| = O(N^{−1/2})`. -/
theorem exists_abs_causalMobiusThetaTail_sub_le_unitInterval :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, (N : ℝ) ≤ t → t ≤ N + 1 →
      |causalMobiusThetaTail t - causalMobiusThetaTail N| ≤ C * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨D₁, hD₁, hk'⟩ := exists_abs_deriv_thetaCuspFullSource_le 2
  have hk0 := thetaCuspFullSource_pos_all 0
  refine ⟨8 / 3 * D₁ + thetaCuspFullSource 0, by positivity, fun N hN t hNt htN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have ht0 : 0 < t := hN0.trans_le hNt
  -- the moving part over the fixed indices
  have hmove : |causalTailFrom N t - causalTailFrom N N| ≤ 8 / 3 * D₁ * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hs1 := summable_causalTailFrom (N := N) ht0 htN
    have hs2 := summable_causalTailFrom (N := N) hN0 (by linarith)
    rw [causalTailFrom, causalTailFrom, ← hs1.tsum_sub hs2]
    have hpt : ∀ j : ℕ, |((ArithmeticFunction.moebius (j + N + 1) : ℤ) : ℝ) *
        causalProfile t ((j + N + 1 : ℕ) : ℝ) - ((ArithmeticFunction.moebius (j + N + 1) : ℤ) : ℝ) *
        causalProfile N ((j + N + 1 : ℕ) : ℝ)| ≤
        4 * D₁ * N * ((j + N + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) := by
      intro j
      set n : ℝ := ((j + N + 1 : ℕ) : ℝ) with hn
      have hn0 : 0 < n := by rw [hn]; positivity
      have htn : t ≤ n := by rw [hn]; push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      rw [← mul_sub, abs_mul]
      refine le_trans (mul_le_of_le_one_left (abs_nonneg _) (Sieve.abs_moebius_real_le_one _)) ?_
      unfold causalProfile
      rw [← mul_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
      set y₁ := Real.log n - Real.log t with hy₁
      set y₂ := Real.log n - Real.log N with hy₂
      have hy₁0 : 0 ≤ y₁ := sub_nonneg.mpr (Real.log_le_log ht0 htn)
      have hy12 : y₁ ≤ y₂ := by rw [hy₁, hy₂]; linarith [Real.log_le_log hN0 hNt]
      have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := thetaCuspFullSource)
        (a := y₁) (b := y₂) (f' := deriv thetaCuspFullSource)
        (C := D₁ * Real.exp (-(2 * y₁)))
        (fun ξ _ => (differentiable_thetaCuspFullSource ξ).hasDerivAt.hasDerivWithinAt)
        (fun ξ hξ => by
          rw [Real.norm_eq_abs]
          refine (hk' ξ).trans ?_
          have hξ0 : 0 ≤ ξ := hy₁0.trans hξ.1
          rw [abs_of_nonneg hξ0]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hξ.1])) hD₁)
        y₂ ⟨hy12, le_rfl⟩
      rw [Real.norm_eq_abs] at hmvt
      have hexp : Real.exp (-(2 * y₁)) = t ^ 2 * (n ^ 2)⁻¹ := exp_neg_two_log_sub ht0 hn0
      have hdy : y₂ - y₁ ≤ 1 / N := by
        rw [hy₁, hy₂, show Real.log n - Real.log N - (Real.log n - Real.log t) =
          Real.log (t / N) by rw [Real.log_div ht0.ne' hN0.ne']; ring]
        refine (Real.log_le_sub_one_of_pos (div_pos ht0 hN0)).trans ?_
        rw [div_sub_one hN0.ne', div_le_div_iff_of_pos_right hN0]
        linarith
      have ht2 : t ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
      have hdiff : |thetaCuspFullSource y₁ - thetaCuspFullSource y₂| ≤
          D₁ * (4 * (N : ℝ) ^ 2 * (n ^ 2)⁻¹) * (1 / N) := by
        rw [abs_sub_comm]
        refine hmvt.trans ?_
        rw [hexp]
        gcongr
      have hr5 : n ^ (-(1 / 2 : ℝ)) * (n ^ 2)⁻¹ = n ^ (-(5 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]; norm_num
      calc n ^ (-(1 / 2 : ℝ)) * |thetaCuspFullSource y₁ - thetaCuspFullSource y₂|
          ≤ n ^ (-(1 / 2 : ℝ)) * (D₁ * (4 * (N : ℝ) ^ 2 * (n ^ 2)⁻¹) * (1 / N)) :=
            mul_le_mul_of_nonneg_left hdiff (Real.rpow_pos_of_pos hn0 _).le
        _ = 4 * D₁ * ((N : ℝ) ^ 2 / N) * (n ^ (-(1 / 2 : ℝ)) * (n ^ 2)⁻¹) := by ring
        _ = 4 * D₁ * N * n ^ (-(5 / 2 : ℝ)) := by
            rw [hr5, pow_two, mul_div_assoc, div_self hN0.ne', mul_one]
    have hsum5 : Summable (fun j : ℕ => ((j + N + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) := by
      have h := (summable_nat_add_iff (N + 1)).mpr summable_natCast_rpow_neg_five_halves
      exact h.congr (fun j => by rw [show j + (N + 1) = j + N + 1 by ring])
    have htail := Sieve.tsum_tail_rpow_neg_le (show (1 : ℝ) < 5 / 2 by norm_num) hN
    have habs := (hs1.sub hs2).abs
    calc |∑' j : ℕ, (((ArithmeticFunction.moebius (j + N + 1) : ℤ) : ℝ) *
          causalProfile t ((j + N + 1 : ℕ) : ℝ) - ((ArithmeticFunction.moebius (j + N + 1) : ℤ) : ℝ) *
          causalProfile N ((j + N + 1 : ℕ) : ℝ))|
        ≤ ∑' j : ℕ, |((ArithmeticFunction.moebius (j + N + 1) : ℤ) : ℝ) *
          causalProfile t ((j + N + 1 : ℕ) : ℝ) - ((ArithmeticFunction.moebius (j + N + 1) : ℤ) : ℝ) *
          causalProfile N ((j + N + 1 : ℕ) : ℝ)| := by
          simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (hs1.sub hs2).norm
      _ ≤ ∑' j : ℕ, 4 * D₁ * N * ((j + N + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) :=
          habs.tsum_le_tsum hpt (hsum5.mul_left _)
      _ = 4 * D₁ * N * ∑' j : ℕ, ((j + N + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) := tsum_mul_left
      _ ≤ 4 * D₁ * N * ((N : ℝ) ^ (1 - 5 / 2 : ℝ) / (5 / 2 - 1)) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
      _ = 8 / 3 * D₁ * ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(3 / 2 : ℝ))) := by
          rw [Real.rpow_one]; norm_num; ring
      _ = 8 / 3 * D₁ * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_add hN0]; norm_num
  -- the jump at the right endpoint
  have hjump : |((ArithmeticFunction.moebius (N + 1) : ℤ) : ℝ) *
      causalProfile ((N : ℝ) + 1) ((N + 1 : ℕ) : ℝ)| ≤
        thetaCuspFullSource 0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [abs_mul]
    refine le_trans (mul_le_of_le_one_left (abs_nonneg _) (Sieve.abs_moebius_real_le_one _)) ?_
    unfold causalProfile
    rw [show (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 by push_cast; ring, sub_self, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos (by positivity) _),
      abs_of_pos (thetaCuspFullSource_pos_all _), mul_comm]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hN0 (by linarith) (by norm_num)) hk0.le
  have hNfrom : causalMobiusThetaTail N = causalTailFrom N N :=
    causalMobiusThetaTail_eq_causalTailFrom le_rfl (by linarith) hN0
  rcases lt_or_eq_of_le htN with hlt | heq
  · rw [causalMobiusThetaTail_eq_causalTailFrom hNt hlt ht0, hNfrom]
    refine hmove.trans ?_
    have : 0 ≤ thetaCuspFullSource 0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    nlinarith
  · rw [heq, causalMobiusThetaTail_succ_eq, hNfrom]
    rw [heq] at hmove
    calc |causalTailFrom N ((N : ℝ) + 1) - ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℝ) *
          causalProfile ((N : ℝ) + 1) ((N + 1 : ℕ) : ℝ) - causalTailFrom N N|
        = |(causalTailFrom N ((N : ℝ) + 1) - causalTailFrom N N) -
            ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℝ) *
              causalProfile ((N : ℝ) + 1) ((N + 1 : ℕ) : ℝ)| := by ring_nf
      _ ≤ |causalTailFrom N ((N : ℝ) + 1) - causalTailFrom N N| +
            |((ArithmeticFunction.moebius (N + 1) : ℤ) : ℝ) *
              causalProfile ((N : ℝ) + 1) ((N + 1 : ℕ) : ℝ)| := abs_sub _ _
      _ ≤ 8 / 3 * D₁ * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
            thetaCuspFullSource 0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := add_le_add hmove hjump
      _ = (8 / 3 * D₁ + thetaCuspFullSource 0) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by ring

/-! ### The finite moving-cusp criterion -/

/-- A power bound on the moving-cusp port from some point on gives the same power bound on the
causal tail for every real `t ≥ 1`. -/
theorem exists_causalTail_bound_of_port_bound {a C : ℝ} (ha : 0 ≤ a) {N₀ : ℕ}
    (hport : ∀ N : ℕ, N₀ ≤ N → |movingCuspPort N| ≤ C * (N : ℝ) ^ a) :
    ∃ C' : ℝ, ∀ t : ℝ, 1 ≤ t → |causalMobiusThetaTail t| ≤ C' * t ^ a := by
  obtain ⟨CT, hCT0, hCT⟩ := exists_abs_movingCuspPort_sub_le 1
  obtain ⟨CI, hCI0, hCI⟩ := exists_abs_causalMobiusThetaTail_sub_le_unitInterval
  obtain ⟨C0, hC00, hC0⟩ := exists_abs_causalMobiusThetaTail_le_sq
  set N₁ : ℕ := max N₀ 3 with hN₁
  set Cp : ℝ := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  refine ⟨Cp + CT + CI + C0 * (N₁ : ℝ) ^ 2 + C0 * 4, fun t ht => ?_⟩
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hta : 1 ≤ t ^ a := Real.one_le_rpow ht ha
  rcases lt_or_ge t (N₁ : ℝ) with hsmall | hbig
  · -- a bounded range: the crude bound
    refine (hC0 t ht0).trans ?_
    have h1 : t ^ 2 ≤ (N₁ : ℝ) ^ 2 := pow_le_pow_left₀ ht0.le hsmall.le 2
    have hnn : 0 ≤ Cp + CT + CI + C0 * 4 := by positivity
    calc C0 * t ^ 2 ≤ C0 * (N₁ : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h1 hC00
      _ ≤ C0 * (N₁ : ℝ) ^ 2 * t ^ a := le_mul_of_one_le_right (by positivity) hta
      _ ≤ (Cp + CT + CI + C0 * (N₁ : ℝ) ^ 2 + C0 * 4) * t ^ a := by
          nlinarith [mul_nonneg hnn (le_trans zero_le_one hta)]
  · set N : ℕ := ⌊t⌋₊ with hNdef
    have hNt : (N : ℝ) ≤ t := Nat.floor_le ht0.le
    have htN : t < N + 1 := Nat.lt_floor_add_one t
    have hN₁N : N₁ ≤ N := Nat.le_floor hbig
    have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN₁N
    have hN0N : N₀ ≤ N := le_trans (le_max_left _ _) hN₁N
    have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    have hN0 : (0 : ℝ) < N := by linarith
    have hNa : 1 ≤ (N : ℝ) ^ a := Real.one_le_rpow (by linarith) ha
    have hNat : (N : ℝ) ^ a ≤ t ^ a := Real.rpow_le_rpow hN0.le hNt ha
    have hinv1 : (N : ℝ) ^ (-(1 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have hinvh : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h1 := hCI N (by omega) t hNt htN.le
    have h2 := hCT N hN3
    have h3 := hport N hN0N
    have h3' : |movingCuspPort N| ≤ Cp * (N : ℝ) ^ a :=
      h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    calc |causalMobiusThetaTail t|
        ≤ |causalMobiusThetaTail t - causalMobiusThetaTail N| + |causalMobiusThetaTail N| := by
          have := abs_sub_abs_le_abs_sub (causalMobiusThetaTail t) (causalMobiusThetaTail N)
          linarith
      _ ≤ CI * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
            (|movingCuspPort N| + |movingCuspPort N - causalMobiusThetaTail N|) := by
          gcongr
          have := abs_sub_abs_le_abs_sub (causalMobiusThetaTail N) (movingCuspPort N)
          rw [abs_sub_comm (causalMobiusThetaTail N)] at this
          linarith
      _ ≤ CI * 1 + (Cp * (N : ℝ) ^ a + CT * 1) := by
          gcongr
          exact h2.trans (mul_le_mul_of_nonneg_left hinv1 hCT0)
      _ ≤ (Cp + CT + CI) * (N : ℝ) ^ a := by nlinarith
      _ ≤ (Cp + CT + CI) * t ^ a := mul_le_mul_of_nonneg_left hNat (by positivity)
      _ ≤ (Cp + CT + CI + C0 * (N₁ : ℝ) ^ 2 + C0 * 4) * t ^ a := by
          have : 0 ≤ C0 * (N₁ : ℝ) ^ 2 + C0 * 4 := by positivity
          nlinarith [mul_nonneg this (le_trans zero_le_one hta)]

/-- **The finite moving-cusp criterion (3).**
`RH ⟺ ∀ ε > 0, B_{Y_N}(N) = O_ε(N^ε)` on the integers `N ≥ 3`. -/
theorem riemannHypothesis_iff_movingCuspPort_subpower :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N → |movingCuspPort N| ≤ C * (N : ℝ) ^ ε := by
  constructor
  · intro hRH ε hε
    obtain ⟨C, hC⟩ := causalMobiusThetaTail_subpower_of_riemannHypothesis hRH ε hε
    obtain ⟨CT, hCT0, hCT⟩ := exists_abs_movingCuspPort_sub_le 1
    refine ⟨max C 0 + CT, fun N hN => ?_⟩
    have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hN1 : (1 : ℝ) ≤ N := by linarith
    have hNe : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
    have hinv : (N : ℝ) ^ (-(1 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
    have hB := (hC N hN1).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity))
    calc |movingCuspPort N| ≤ |movingCuspPort N - causalMobiusThetaTail N| +
          |causalMobiusThetaTail N| := by
          have := abs_sub_abs_le_abs_sub (movingCuspPort N) (causalMobiusThetaTail N)
          linarith
      _ ≤ CT * 1 + max C 0 * (N : ℝ) ^ ε := by
          gcongr
          exact (hCT N hN).trans (mul_le_mul_of_nonneg_left hinv hCT0)
      _ ≤ (max C 0 + CT) * (N : ℝ) ^ ε := by
          have := le_max_right C 0
          nlinarith
  · intro h
    refine riemannHypothesis_of_causalMobiusThetaTail_subpower (fun ε hε => ?_)
    obtain ⟨C, hC⟩ := h ε hε
    exact exists_causalTail_bound_of_port_bound hε.le (N₀ := 3) hC

/-- **The quantitative off-line witness (8).**  If `ζ(ρ) = 0` with `1/2 < Re ρ < 1` and
`v = Re ρ − 1/2`, then for every `0 < δ < v` the port is not eventually `O(N^{v−δ})`. -/
theorem not_eventually_movingCuspPort_le_of_riemannZeta_eq_zero {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (h2 : ρ.re < 1) {δ : ℝ} (hδ : 0 < δ) (hδv : δ < ρ.re - 1 / 2) :
    ¬ ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      |movingCuspPort N| ≤ C * (N : ℝ) ^ (ρ.re - 1 / 2 - δ) := by
  rintro ⟨C, hC⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hC
  obtain ⟨C', hC'⟩ := exists_causalTail_bound_of_port_bound (a := ρ.re - 1 / 2 - δ)
    (by linarith) (N₀ := N₀) hN₀
  exact causalMobiusThetaTail_growth_excludes_zero (by linarith) hC' hρ (by linarith) h2

/-- The witness in `limsup` form: `N^{−(v−δ)} |B_{Y_N}(N)|` exceeds every constant infinitely
often. -/
theorem frequently_lt_abs_movingCuspPort_of_riemannZeta_eq_zero {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (h2 : ρ.re < 1) {δ : ℝ} (hδ : 0 < δ) (hδv : δ < ρ.re - 1 / 2)
    (C : ℝ) : ∃ᶠ N : ℕ in atTop,
      C < (N : ℝ) ^ (-(ρ.re - 1 / 2 - δ)) * |movingCuspPort N| := by
  by_contra hfreq
  rw [not_frequently] at hfreq
  refine not_eventually_movingCuspPort_le_of_riemannZeta_eq_zero hρ h2 hδ hδv ⟨C, ?_⟩
  filter_upwards [hfreq, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpos : 0 < (N : ℝ) ^ (ρ.re - 1 / 2 - δ) := Real.rpow_pos_of_pos hN0 _
  push Not at hN
  rw [Real.rpow_neg hN0.le, inv_mul_le_iff₀ hpos] at hN
  linarith

end

end RHTower
