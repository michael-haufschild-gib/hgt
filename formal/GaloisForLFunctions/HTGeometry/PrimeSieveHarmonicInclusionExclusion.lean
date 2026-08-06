import GaloisForLFunctions.HTGeometry.PrimeSieveEulerTrace
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The sieved harmonic sum: inclusion--exclusion and its logarithmic asymptotic

The first trace of a commuting prime sieve truncated at height `N` is the
harmonic sum restricted to the integers coprime to the primorial of the sieve.
Möbius inversion of the coprimality indicator turns that restricted sum into a
finite alternating sum of full harmonic sums at the decimated heights `N / d`,
one for each divisor `d` of the primorial.

Because the primorial is squarefree, the Möbius weights `μ(d)/d` sum over its
divisors to the Euler product of the sieve, so the decimated expansion has
leading coefficient exactly the sieve density.  Feeding in the Euler--Mascheroni
asymptotic of the harmonic numbers gives the exact affine law

`T_P(N) = a_P log N + κ_P + o(1)`,

with `a_P` the sieve density and `κ_P` the finite Möbius average of
`γ - log d` over the divisors of the primorial.
-/

open ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- The harmonic number as a sum over `Icc 1 N`. -/
theorem sum_Icc_one_div_eq_harmonic (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / j = (harmonic N : ℝ) := by
  induction N with
  | zero => simp [harmonic_zero]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
      push_cast
      ring

/-- The primorial of a finite set of primes is nonzero. -/
theorem sievePrimorial_ne_zero (P : Finset Nat.Primes) : sievePrimorial P ≠ 0 := by
  rw [sievePrimorial]
  exact Finset.prod_ne_zero_iff.mpr fun p _ => p.2.pos.ne'

/-- The divisors of a greatest common divisor are the divisors of one argument
that divide the other. -/
theorem divisors_gcd_eq_filter (n : ℕ) {M : ℕ} (hM : M ≠ 0) :
    (Nat.gcd n M).divisors = M.divisors.filter (fun d => d ∣ n) := by
  classical
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter]
  constructor
  · rintro ⟨hdvd, -⟩
    exact ⟨⟨hdvd.trans (Nat.gcd_dvd_right n M), hM⟩, hdvd.trans (Nat.gcd_dvd_left n M)⟩
  · rintro ⟨⟨hdM, -⟩, hdn⟩
    refine ⟨Nat.dvd_gcd hdn hdM, fun h => hM ?_⟩
    exact Nat.eq_zero_of_gcd_eq_zero_right h

/-- The Möbius function sums to the unit arithmetic function over divisors. -/
theorem sum_divisors_moebius_real (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : ℝ) = if n = 1 then 1 else 0 := by
  have h : ∑ d ∈ n.divisors, (μ d : ℤ) = if n = 1 then 1 else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply (f := (μ : ArithmeticFunction ℤ)) (x := n),
      moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  calc ∑ d ∈ n.divisors, (μ d : ℝ)
      = ((∑ d ∈ n.divisors, (μ d : ℤ) : ℤ) : ℝ) := by push_cast; ring
    _ = _ := by rw [h]; split <;> norm_num

/-- The multiples of `d` in `Icc 1 N` are the scalings of `Icc 1 (N / d)`. -/
theorem multiples_Icc {d : ℕ} (hd : 0 < d) (N : ℕ) :
    (Finset.Icc 1 N).filter (fun n => d ∣ n)
      = (Finset.Icc 1 (N / d)).image (fun j => d * j) := by
  classical
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, j, rfl⟩
    refine ⟨j, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · omega
      · exact hj
    · rw [Nat.le_div_iff_mul_le hd, mul_comm]
      exact h2
  · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
    have hle := (Nat.le_div_iff_mul_le hd).mp hj2
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩, j, rfl⟩
    rw [mul_comm]
    exact hle

/-- The first sieved trace truncated at height `N`: the harmonic sum over the
integers coprime to the primorial of the sieve. -/
noncomputable def sievedHarmonic (P : Finset Nat.Primes) (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n (sievePrimorial P)),
    (1 : ℝ) / n

/-- **Inclusion--exclusion for the sieved harmonic sum.**  Möbius inversion of
the coprimality indicator decimates the height by each divisor of the
primorial. -/
theorem sievedHarmonic_eq_sum_divisors (P : Finset Nat.Primes) (N : ℕ) :
    sievedHarmonic P N
      = ∑ d ∈ (sievePrimorial P).divisors,
          (μ d : ℝ) / d * (harmonic (N / d) : ℝ) := by
  classical
  have hM : sievePrimorial P ≠ 0 := sievePrimorial_ne_zero P
  have h1 : sievedHarmonic P N
      = ∑ n ∈ Finset.Icc 1 N,
          (∑ d ∈ (sievePrimorial P).divisors.filter (fun d => d ∣ n), (μ d : ℝ))
            * ((1 : ℝ) / n) := by
    rw [sievedHarmonic, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← divisors_gcd_eq_filter n hM, sum_divisors_moebius_real]
    by_cases h : Nat.gcd n (sievePrimorial P) = 1
    · rw [if_pos h, if_pos (show Nat.Coprime n (sievePrimorial P) from h), one_mul]
    · rw [if_neg h, if_neg (show ¬ Nat.Coprime n (sievePrimorial P) from h), zero_mul]
  have h2 : ∀ n : ℕ,
      (∑ d ∈ (sievePrimorial P).divisors.filter (fun d => d ∣ n), (μ d : ℝ))
          * ((1 : ℝ) / n)
        = ∑ d ∈ (sievePrimorial P).divisors,
            (if d ∣ n then (μ d : ℝ) * ((1 : ℝ) / n) else 0) := by
    intro n
    rw [Finset.sum_filter, Finset.sum_mul]
    exact Finset.sum_congr rfl fun d _ => by split <;> ring
  rw [h1]
  simp_rw [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  rw [← Finset.sum_filter, multiples_Icc hd0 N,
    Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hd0 hab),
    ← sum_Icc_one_div_eq_harmonic, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 : 0 < j := (Finset.mem_Icc.mp hj).1
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj0
  push_cast
  field_simp

section EulerProduct

/-- The Möbius function divided by its argument, as an arithmetic function. -/
noncomputable def moebiusDiv : ArithmeticFunction ℝ :=
  ⟨fun d => (μ d : ℝ) / d, by simp⟩

@[simp] theorem moebiusDiv_apply (d : ℕ) : moebiusDiv d = (μ d : ℝ) / d := rfl

/-- `μ(d)/d` is multiplicative. -/
theorem isMultiplicative_moebiusDiv : moebiusDiv.IsMultiplicative := by
  constructor
  · simp
  · intro m n hmn
    simp only [moebiusDiv_apply, isMultiplicative_moebius.map_mul_of_coprime hmn]
    push_cast
    rw [div_mul_div_comm]

/-- The divisor sum of `μ(d)/d` as an arithmetic function value. -/
theorem sum_divisors_moebiusDiv_eq (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : ℝ) / d
      = (moebiusDiv * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  exact Finset.sum_congr rfl fun d _ => rfl

/-- The divisor sum of `μ(d)/d` is multiplicative. -/
theorem isMultiplicative_moebiusDivSum :
    (moebiusDiv * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ)).IsMultiplicative :=
  isMultiplicative_moebiusDiv.mul isMultiplicative_zeta.natCast

/-- At a prime the divisor sum of `μ(d)/d` is the local Euler factor. -/
theorem sum_divisors_moebiusDiv_prime (p : Nat.Primes) :
    ∑ d ∈ ((p : ℕ)).divisors, (μ d : ℝ) / d = 1 - ((p : ℕ) : ℝ)⁻¹ := by
  have hne : (1 : ℕ) ≠ (p : ℕ) := p.2.one_lt.ne
  rw [p.2.divisors, Finset.sum_pair hne]
  rw [moebius_apply_one, ArithmeticFunction.moebius_apply_prime p.2]
  push_cast
  ring

/-- **The Möbius divisor sum of the primorial is the sieve density.** -/
theorem sum_divisors_moebiusDiv_sievePrimorial (P : Finset Nat.Primes) :
    ∑ d ∈ (sievePrimorial P).divisors, (μ d : ℝ) / d = sieveDensity P := by
  classical
  induction P using Finset.induction with
  | empty => simp [sievePrimorial_empty, sieveDensity]
  | insert p P hp ih =>
      have hcop : Nat.Coprime (p : ℕ) (sievePrimorial P) := coprime_sievePrimorial hp
      have key := isMultiplicative_moebiusDivSum.map_mul_of_coprime hcop
      rw [sievePrimorial_insert hp, sieveDensity_insert hp, ← ih,
        sum_divisors_moebiusDiv_eq, key, ← sum_divisors_moebiusDiv_eq,
        ← sum_divisors_moebiusDiv_eq, sum_divisors_moebiusDiv_prime, mul_comm]

end EulerProduct

section Asymptotic

/-- Decimation of the height by a positive integer is cofinal. -/
theorem tendsto_natDiv_atTop {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => N / d) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun K => ⟨K * d, fun N hN => ?_⟩
  exact (Nat.le_div_iff_mul_le hd).mpr hN

/-- The decimated height has relative density the reciprocal of the decimation. -/
theorem tendsto_natDiv_div_self {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / N) atTop (𝓝 (1 / d)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hg : Tendsto (fun N : ℕ => ((N % d : ℕ) : ℝ) / N) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => by positivity) (fun N => ?_)
      (tendsto_const_div_atTop_nhds_zero_nat (d : ℝ))
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      have hmod : ((N % d : ℕ) : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast (Nat.mod_lt N hd).le
      gcongr
  have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).sub hg).div_const (d : ℝ)
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdm : (d : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast Nat.div_add_mod N d
  field_simp
  nlinarith [hdm]

/-- The logarithm of the decimated height is the logarithm of the height shifted
by the logarithm of the decimation. -/
theorem tendsto_log_natDiv_sub_log {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => Real.log ((N / d : ℕ) : ℝ) - Real.log N) atTop
      (𝓝 (-Real.log d)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : Real.log (1 / (d : ℝ)) = -Real.log d := by
    rw [one_div, Real.log_inv]
  have h1 : Tendsto (fun N : ℕ => Real.log (((N / d : ℕ) : ℝ) / N)) atTop
      (𝓝 (Real.log (1 / (d : ℝ)))) :=
    (Real.continuousAt_log (by positivity)).tendsto.comp (tendsto_natDiv_div_self hd)
  rw [hlog] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop d, eventually_gt_atTop 0] with N hNd hN0
  have hdiv : 0 < N / d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
  have h2 : ((N / d : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hdiv.ne'
  have h3 : (N : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
  rw [Real.log_div h2 h3]

/-- The decimated harmonic number, measured against the undecimated logarithm,
converges to the Euler--Mascheroni constant shifted by the logarithm of the
decimation. -/
theorem tendsto_harmonic_natDiv_sub_log {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => (harmonic (N / d) : ℝ) - Real.log N) atTop
      (𝓝 (Real.eulerMascheroniConstant - Real.log d)) := by
  have h1 : Tendsto
      (fun N : ℕ => (harmonic (N / d) : ℝ) - Real.log ((N / d : ℕ) : ℝ)) atTop
      (𝓝 Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log.comp (tendsto_natDiv_atTop hd)
  have h2 := h1.add (tendsto_log_natDiv_sub_log hd)
  rw [← sub_eq_add_neg] at h2
  exact h2.congr fun N => by ring

/-- The constant term of the sieved harmonic law: the Möbius average of
`γ - log d` over the divisors of the primorial. -/
noncomputable def sieveHarmonicConstant (P : Finset Nat.Primes) : ℝ :=
  ∑ d ∈ (sievePrimorial P).divisors,
    (μ d : ℝ) / d * (Real.eulerMascheroniConstant - Real.log d)

/-- **The affine law of the sieved harmonic sum.**  The first sieved trace at
height `N` is the sieve density times `log N`, plus an explicit finite constant,
plus a vanishing remainder. -/
theorem tendsto_sievedHarmonic_sub (P : Finset Nat.Primes) :
    Tendsto (fun N : ℕ => sievedHarmonic P N - sieveDensity P * Real.log N) atTop
      (𝓝 (sieveHarmonicConstant P)) := by
  have hsum : ∀ N : ℕ, sievedHarmonic P N - sieveDensity P * Real.log N
      = ∑ d ∈ (sievePrimorial P).divisors,
          (μ d : ℝ) / d * ((harmonic (N / d) : ℝ) - Real.log N) := by
    intro N
    rw [sievedHarmonic_eq_sum_divisors, ← sum_divisors_moebiusDiv_sievePrimorial P,
      Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  refine Tendsto.congr (fun N => (hsum N).symm) ?_
  rw [sieveHarmonicConstant]
  refine tendsto_finsetSum _ fun d hd => ?_
  exact (tendsto_harmonic_natDiv_sub_log (Nat.pos_of_mem_divisors hd)).const_mul _

end Asymptotic

end GaloisForLFunctions.HTGeometry
