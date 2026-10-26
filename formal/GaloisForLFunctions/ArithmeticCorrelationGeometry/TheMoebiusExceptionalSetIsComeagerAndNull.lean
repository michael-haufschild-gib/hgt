import GaloisForLFunctions.ArithmeticCorrelationGeometry.AlmostEveryGaugePointCancelsToTheSquareRoot
import GaloisForLFunctions.BezoutValuationIncidence.CoprimeSquarefreeDensityAndMobiusDilationMeans

/-!
# The Möbius exceptional set is comeager and null

The half-power law `Σ_{n ≤ N} μ(n) χ_x(n) = O(N^{1/2+δ})` holds at Haar-almost every gauge point
(`ae_gaugeHalfPowerLaw`), and at the gauge point `0` it is the Riemann hypothesis. This module
shows that the exceptional set is nevertheless **topologically generic**.

* **Twin tails** (`twinTail`). Given finitely many coordinates of a gauge point, put the phase `½`
  on every other prime. On squarefree `n` the twisted Möbius function becomes
  `ψ(gcd(n, Q))`, `ψ(d) = ∏_{p | d} (−e(x_p))`, `Q` the product of the kept primes
  (`moebius_mul_twist_twinTail`), so the twisted Mertens sum is
  `Σ_{d | Q} ψ(d) · #{m ≤ N/d squarefree, (m, Q) = 1}` (`moebiusGaugeSum_twinTail`).
* **Linear growth** (`tendsto_moebiusGaugeSum_twinTail_div`). By the coprime squarefree density,
  `N⁻¹ Σ_{n≤N} μ(n)χ_x(n) → (6/π²)∏_{p | Q} p/(p+1) · ∏_{p | Q} (1 − e(x_p)/p) ≠ 0`: every twin tail
  carries the pole of `ζ(s)/ζ(2s)` and violates the half-power law.
* **Comeager and null** (`moebius_exceptional_residual_and_null`). The points whose partial sums
  beat every multiple of `(N+1)^{3/4}` form a `G_δ` set containing a twin tail in every open set;
  so the exceptional set of the half-power law is residual, while its Haar measure is zero. In
  particular every neighbourhood of the gauge point `0` contains exceptional points
  (`zero_mem_closure_exceptional`).

Gauge status: RH asks whether `0` lies in a meager set of full Haar measure. No property of the
gauge point that is stable under small perturbations in the product topology — equivalently, that
is decided by finitely many prime phases up to finite precision — can decide it: twin tails share
any finite amount of that information with `0` and violate the law.
-/

open MeasureTheory Finset Filter Topology
open scoped ComplexConjugate ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

/-! ### The twisted Mertens sums -/

/-- The twisted Mertens sum `Σ_{1 ≤ n ≤ N} μ(n) χ_x(n)`. -/
def moebiusGaugeSum (N : ℕ) (x : GaugeTorus) : ℂ := ∑ n ∈ Icc 1 N, ((μ n : ℤ) : ℂ) * twist x n

theorem continuous_moebiusGaugeSum (N : ℕ) : Continuous (moebiusGaugeSum N) :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_twist n)

/-- The strongly exceptional points: partial sums beating every multiple of `(N+1)^{3/4}`. -/
def strongExceptional : Set GaugeTorus :=
  {x | ∀ K : ℕ, ∃ N : ℕ, (K : ℝ) * ((N : ℝ) + 1) ^ (3 / 4 : ℝ) < ‖moebiusGaugeSum N x‖}

theorem isGδ_strongExceptional : IsGδ strongExceptional := by
  have : strongExceptional = ⋂ K : ℕ, ⋃ N : ℕ,
      {x | (K : ℝ) * ((N : ℝ) + 1) ^ (3 / 4 : ℝ) < ‖moebiusGaugeSum N x‖} := by
    ext x; simp [strongExceptional]
  rw [this]
  refine IsGδ.iInter_of_isOpen fun K => isOpen_iUnion fun N => ?_
  exact isOpen_lt continuous_const (continuous_moebiusGaugeSum N).norm

/-- The Möbius sum over `range (N+1)` is the sum over `[1, N]`. -/
theorem sum_range_moebius_twist (N : ℕ) (x : GaugeTorus) :
    ∑ n ∈ range (N + 1), ((μ n : ℤ) : ℂ) * twist x n = moebiusGaugeSum N x := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos N), moebiusGaugeSum]
  have hIcc : Icc 1 N = Ico 1 (N + 1) := by ext n; simp only [mem_Icc, mem_Ico]; omega
  rw [hIcc]
  simp

/-- Strongly exceptional points violate the half-power law. -/
theorem not_gaugeHalfPowerLaw_of_mem_strongExceptional {x : GaugeTorus}
    (hx : x ∈ strongExceptional) : ¬ GaugeHalfPowerLaw (fun n => ((μ n : ℤ) : ℂ)) x := by
  intro h
  obtain ⟨C, hC, hb⟩ := h (1 / 4) (by norm_num)
  obtain ⟨N, hN⟩ := hx ⌈C⌉₊
  have h1 := hb N
  rw [sum_range_moebius_twist, show (1 / 2 : ℝ) + 1 / 4 = 3 / 4 by norm_num] at h1
  have hpow : 0 ≤ ((N : ℝ) + 1) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
  have : C * ((N : ℝ) + 1) ^ (3 / 4 : ℝ) ≤ (⌈C⌉₊ : ℝ) * ((N : ℝ) + 1) ^ (3 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil C) hpow
  linarith

/-! ### Twin tails -/

/-- The twin tail of `x₀` beyond the coordinates `I`: keep `x₀` on `I`, put `½` on every other
prime and `0` elsewhere. -/
def twinTail (I : Finset ℕ) (x₀ : GaugeTorus) : GaugeTorus :=
  fun i => if i ∈ I then x₀ i else if i.Prime then ((1 / 2 : ℝ) : UnitAddCircle) else 0

/-- The product of the primes of `I`. -/
def tailModulus (I : Finset ℕ) : ℕ := ∏ p ∈ I.filter Nat.Prime, p

theorem fourier_one_half : fourier 1 (((1 / 2 : ℝ)) : UnitAddCircle) = -1 := by
  rw [fourier_coe_apply]
  have : 2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * (((1 / 2 : ℝ)) : ℂ) / ((1 : ℝ) : ℂ) =
      Real.pi * Complex.I := by push_cast; ring
  rw [this, Complex.exp_pi_mul_I]

/-- At a prime the twist is the first Fourier mode of the prime coordinate. -/
theorem twist_prime (x : GaugeTorus) {p : ℕ} (hp : p.Prime) : twist x p = fourier 1 (x p) := by
  rw [twist, HTGeometry.torusCharacter_apply]
  have hsupp : (expVec p).support = {p} := by
    rw [support_expVec, Nat.support_factorization, hp.primeFactors]
  rw [hsupp, prod_singleton, expVec_apply, hp.factorization_self]
  rfl


/-- The local factor `−e(x_p)` of the twisted Möbius function at a prime. -/
def tailFactor (x₀ : GaugeTorus) (p : ℕ) : ℂ := -fourier 1 (x₀ p)

/-- The twisted Möbius weight on the kept primes: `ψ(d) = ∏_{p | d} (−e(x_p))`. -/
def tailWeight (x₀ : GaugeTorus) (d : ℕ) : ℂ := ∏ p ∈ d.primeFactors, tailFactor x₀ p

theorem primeFactors_tailModulus (I : Finset ℕ) :
    (tailModulus I).primeFactors = I.filter Nat.Prime :=
  Nat.primeFactors_prod fun _ hp => (mem_filter.mp hp).2

theorem tailModulus_ne_zero (I : Finset ℕ) : tailModulus I ≠ 0 :=
  prod_ne_zero_iff.mpr fun _ hp => (mem_filter.mp hp).2.ne_zero

theorem squarefree_tailModulus (I : Finset ℕ) : Squarefree (tailModulus I) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (mem_filter.mp hp).2.squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (mem_filter.mp hp).2 (mem_filter.mp hq).2).mpr hpq

/-- On squarefree `n` the twisted Möbius function at a twin tail is `ψ(gcd(n, Q))`. -/
theorem moebius_mul_twist_twinTail (I : Finset ℕ) (x₀ : GaugeTorus) {n : ℕ} (hn : Squarefree n) :
    ((μ n : ℤ) : ℂ) * twist (twinTail I x₀) n = tailWeight x₀ (Nat.gcd n (tailModulus I)) := by
  classical
  have hn0 : n ≠ 0 := hn.ne_zero
  have hprimes : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hμ : ((μ n : ℤ) : ℂ) = ∏ p ∈ n.primeFactors, ((μ p : ℤ) : ℂ) := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hn]
    rw [ArithmeticFunction.IsMultiplicative.map_prod_of_prime
      ArithmeticFunction.isMultiplicative_moebius _ hprimes, Int.cast_prod]
  have htw : twist (twinTail I x₀) n = ∏ p ∈ n.primeFactors, twist (twinTail I x₀) p := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hn]
    exact twist_prod _ _ _ fun p hp => (hprimes p hp).ne_zero
  rw [hμ, htw, ← prod_mul_distrib, tailWeight,
    Nat.primeFactors_gcd hn0 (tailModulus_ne_zero I), primeFactors_tailModulus]
  have hfilter : n.primeFactors ∩ I.filter Nat.Prime = n.primeFactors.filter (· ∈ I) := by
    ext p
    simp only [mem_inter, mem_filter]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, hprimes p h1⟩
  rw [hfilter, prod_filter]
  refine prod_congr rfl fun p hp => ?_
  have hpr := hprimes p hp
  rw [ArithmeticFunction.moebius_apply_prime hpr, twist_prime _ hpr]
  by_cases hI : p ∈ I
  · simp only [twinTail, if_pos hI, tailFactor]; push_cast; ring
  · simp only [twinTail, if_neg hI, if_pos hpr, fourier_one_half]; push_cast; ring

/-- The coprime squarefree count is a cardinality. -/
theorem coprimeSquarefreeCount_eq_card (Q M : ℕ) :
    BezoutValuationIncidence.coprimeSquarefreeCount Q M =
      #{m ∈ Icc 1 M | Nat.Coprime Q m ∧ Squarefree m} := by
  classical
  rw [BezoutValuationIncidence.coprimeSquarefreeCount, card_filter]
  push_cast
  refine sum_congr rfl fun m _ => ?_
  rw [BezoutValuationIncidence.coprimeSquarefreeIndicator]
  by_cases hc : Nat.Coprime Q m
  · by_cases hs : Squarefree m
    · rw [if_pos hc, if_pos ⟨hc, hs⟩, ArithmeticFunction.moebius_apply_of_squarefree hs]
      push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
    · rw [if_pos hc, if_neg (fun h => hs h.2), ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
      simp
  · rw [if_neg hc, if_neg (fun h => hc h.1)]

/-- **Divisors with a prescribed gcd.** The squarefree `n ≤ N` with `gcd(n, Q) = d` are `d·m` with
`m ≤ N/d` squarefree and coprime to `Q`. -/
theorem card_gcd_eq (N : ℕ) {Q d : ℕ} (hQ : Squarefree Q) (hd : d ∈ Q.divisors) :
    #{n ∈ Icc 1 N | Nat.gcd n Q = d ∧ Squarefree n} =
      #{m ∈ Icc 1 (N / d) | Nat.Coprime Q m ∧ Squarefree m} := by
  classical
  have hdQ : d ∣ Q := Nat.dvd_of_mem_divisors hd
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hdsq : Squarefree d := hQ.squarefree_of_dvd hdQ
  symm
  refine card_nbij' (fun m => d * m) (fun n => n / d) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at hm ⊢
    obtain ⟨⟨hm1, hmN⟩, hcop, hsq⟩ := hm
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hd0.ne' (by omega)),
      by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd0).mp hmN⟩, ?_, ?_⟩
    · rw [Nat.Coprime.gcd_mul_right_cancel d hcop.symm, Nat.gcd_eq_left hdQ]
    · exact Nat.squarefree_mul_iff.mpr ⟨Nat.Coprime.coprime_dvd_left hdQ hcop, hdsq, hsq⟩
  · intro n hn
    simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at hn ⊢
    obtain ⟨⟨hn1, hnN⟩, hg, hsq⟩ := hn
    have hdn : d ∣ n := hg ▸ Nat.gcd_dvd_left n Q
    refine ⟨⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdn) hd0, Nat.div_le_div_right hnN⟩, ?_,
      hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdn)⟩
    -- a common prime of `Q` and `n/d` would divide `n` twice
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpQ : p ∣ Q := hpg.trans (Nat.gcd_dvd_left _ _)
    have hpm : p ∣ n / d := hpg.trans (Nat.gcd_dvd_right _ _)
    have hpn : p ∣ n := hpm.trans (Nat.div_dvd_of_dvd hdn)
    have hpd : p ∣ d := hg ▸ Nat.dvd_gcd hpn hpQ
    have : p * p ∣ n := by
      have := Nat.mul_dvd_mul hpd hpm
      rwa [Nat.mul_div_cancel' hdn] at this
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p this))
  · intro m _
    exact Nat.mul_div_cancel_left m hd0
  · intro n hn
    simp only [coe_filter, Set.mem_setOf_eq] at hn
    exact Nat.mul_div_cancel' (hn.2.1 ▸ Nat.gcd_dvd_left n Q)

/-- **The twisted Mertens sum of a twin tail.** -/
theorem moebiusGaugeSum_twinTail (I : Finset ℕ) (x₀ : GaugeTorus) (N : ℕ) :
    moebiusGaugeSum N (twinTail I x₀) = ∑ d ∈ (tailModulus I).divisors,
      tailWeight x₀ d * (BezoutValuationIncidence.coprimeSquarefreeCount (tailModulus I) (N / d) : ℂ) := by
  classical
  set Q := tailModulus I
  have hQ := squarefree_tailModulus I
  have hterm : ∀ n ∈ Icc 1 N, ((μ n : ℤ) : ℂ) * twist (twinTail I x₀) n =
      if Squarefree n then tailWeight x₀ (Nat.gcd n Q) else 0 := by
    intro n _
    split_ifs with hs
    · exact moebius_mul_twist_twinTail I x₀ hs
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]; simp
  rw [moebiusGaugeSum, sum_congr rfl hterm,
    ← sum_fiberwise_of_maps_to (g := fun n => Nat.gcd n Q) (t := Q.divisors)
      (fun n _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n Q, hQ.ne_zero⟩)]
  refine sum_congr rfl fun d hd => ?_
  rw [coprimeSquarefreeCount_eq_card, ← card_gcd_eq N hQ hd, ← sum_filter]
  rw [sum_filter, sum_filter]
  have : ∀ n ∈ Icc 1 N, (if Nat.gcd n Q = d then (if Squarefree n then tailWeight x₀ (Nat.gcd n Q)
      else 0) else 0) = if Nat.gcd n Q = d ∧ Squarefree n then tailWeight x₀ d else 0 := by
    intro n _
    by_cases h1 : Nat.gcd n Q = d <;> by_cases h2 : Squarefree n <;> simp [h1, h2]
  rw [sum_congr rfl this, ← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  norm_cast

/-! ### Linear growth of twin tails -/

/-- Divisor sums over a squarefree modulus are sums over subsets of its primes. -/
theorem sum_divisors_eq_sum_powerset {M : Type*} [AddCommMonoid M] {Q : ℕ} (hQ : Squarefree Q)
    (f : ℕ → M) : ∑ d ∈ Q.divisors, f d = ∑ t ∈ Q.primeFactors.powerset, f (∏ p ∈ t, p) := by
  classical
  have hinj : Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) (Q.primeFactors.powerset : Set _) := by
    intro t ht t' ht' h
    have hpt : ∀ p ∈ t, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (mem_powerset.mp (mem_coe.mp ht) hp)
    have hpt' : ∀ p ∈ t', p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (mem_powerset.mp (mem_coe.mp ht') hp)
    rw [← Nat.primeFactors_prod hpt, ← Nat.primeFactors_prod hpt']
    exact congrArg Nat.primeFactors h
  rw [← sum_image hinj]
  congr 1
  ext d
  rw [mem_image, Nat.mem_divisors]
  constructor
  · intro hd
    refine ⟨d.primeFactors, mem_powerset.mpr (Nat.primeFactors_mono hd.1 hQ.ne_zero),
      Nat.prod_primeFactors_of_squarefree (hQ.squarefree_of_dvd hd.1)⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, hQ.ne_zero⟩
    calc ∏ p ∈ t, p ∣ ∏ p ∈ Q.primeFactors, p := prod_dvd_prod_of_subset _ _ _ (mem_powerset.mp ht)
      _ = Q := Nat.prod_primeFactors_of_squarefree hQ

/-- The limit constant `Σ_{d | Q} ψ(d)/d = ∏_{p | Q} (1 − e(x_p)/p)` is nonzero. -/
theorem sum_tailWeight_div_ne_zero (I : Finset ℕ) (x₀ : GaugeTorus) :
    ∑ d ∈ (tailModulus I).divisors, tailWeight x₀ d / (d : ℂ) ≠ 0 := by
  classical
  rw [sum_divisors_eq_sum_powerset (squarefree_tailModulus I)]
  have hterm : ∀ t ∈ (tailModulus I).primeFactors.powerset,
      tailWeight x₀ (∏ p ∈ t, p) / ((∏ p ∈ t, p : ℕ) : ℂ) =
        ∏ p ∈ t, tailFactor x₀ p / (p : ℂ) := by
    intro t ht
    have hpt : ∀ p ∈ t, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (mem_powerset.mp ht hp)
    rw [tailWeight, Nat.primeFactors_prod hpt, prod_div_distrib]
    push_cast; rfl
  rw [sum_congr rfl hterm, ← prod_one_add]
  refine prod_ne_zero_iff.mpr fun p hp => ?_
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
  intro h0
  have hnorm : ‖tailFactor x₀ p / (p : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_div, tailFactor, norm_neg, ← twist_prime _ hpr, norm_twist, Complex.norm_natCast,
      div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have : tailFactor x₀ p / (p : ℂ) = -1 := by linear_combination h0
  rw [this, norm_neg, norm_one] at hnorm
  norm_num at hnorm


/-- **Twin tails grow linearly**: `N⁻¹ Σ_{n ≤ N} μ(n)χ_x(n)` converges to
`δ_Q Σ_{d | Q} ψ(d)/d`, `δ_Q` the density of squarefree integers coprime to `Q`. -/
theorem tendsto_moebiusGaugeSum_twinTail_div (I : Finset ℕ) (x₀ : GaugeTorus) :
    Tendsto (fun N : ℕ => moebiusGaugeSum N (twinTail I x₀) / (N : ℂ)) atTop
      (𝓝 ((BezoutValuationIncidence.coprimeSquarefreeDensity (tailModulus I) : ℂ) *
        ∑ d ∈ (tailModulus I).divisors, tailWeight x₀ d / (d : ℂ))) := by
  set Q := tailModulus I
  have hQ := squarefree_tailModulus I
  have hd : ∀ d ∈ Q.divisors, Tendsto (fun N : ℕ =>
      BezoutValuationIncidence.coprimeSquarefreeCount Q (N / d) / (N : ℝ)) atTop
      (𝓝 (BezoutValuationIncidence.coprimeSquarefreeDensity Q / d)) := by
    intro d hdm
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hdm
    have hx : Tendsto (fun N : ℕ => (N : ℝ) / d) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const hd0
    have hlim := ((BezoutValuationIncidence.tendsto_coprimeSquarefreeMean_of_squarefree Q hQ).comp
      hx).div_const (d : ℝ)
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    simp only [Function.comp_apply, BezoutValuationIncidence.coprimeSquarefreeMean,
      Nat.floor_div_eq_div]
    field_simp
  have hsum := tendsto_finsetSum (s := Q.divisors) fun d hdm =>
    (Complex.continuous_ofReal.tendsto _).comp (hd d hdm) |>.const_mul (tailWeight x₀ d)
  have heq : ∀ N : ℕ, moebiusGaugeSum N (twinTail I x₀) / (N : ℂ) = ∑ d ∈ Q.divisors,
      tailWeight x₀ d * (((BezoutValuationIncidence.coprimeSquarefreeCount Q (N / d) / (N : ℝ) :
        ℝ)) : ℂ) := by
    intro N
    rw [moebiusGaugeSum_twinTail, sum_div]
    refine sum_congr rfl fun d _ => ?_
    push_cast
    ring
  have hval : (BezoutValuationIncidence.coprimeSquarefreeDensity Q : ℂ) *
      ∑ d ∈ Q.divisors, tailWeight x₀ d / (d : ℂ) = ∑ d ∈ Q.divisors,
        tailWeight x₀ d * (((BezoutValuationIncidence.coprimeSquarefreeDensity Q / d : ℝ)) : ℂ) := by
    rw [mul_sum]
    refine sum_congr rfl fun d _ => ?_
    push_cast
    ring
  rw [hval]
  simp_rw [heq]
  exact hsum

/-- Eventually `K (N+1)^{3/4} < c N` for every `K` and `c > 0`. -/
theorem eventually_mul_rpow_lt (K : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, K * ((N : ℝ) + 1) ^ (3 / 4 : ℝ) < c * N := by
  have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  filter_upwards [h1.eventually_gt_atTop (2 * |K| / c), eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hsplit : ((N : ℝ) + 1) ^ (3 / 4 : ℝ) * ((N : ℝ) + 1) ^ (1 / 4 : ℝ) = (N : ℝ) + 1 := by
    rw [← Real.rpow_add hpos]; norm_num
  have h34 : 0 < ((N : ℝ) + 1) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hpos _
  have hK : |K| < c * ((N : ℝ) + 1) ^ (1 / 4 : ℝ) / 2 := by
    rw [div_lt_iff₀ hc] at hN
    linarith
  calc K * ((N : ℝ) + 1) ^ (3 / 4 : ℝ) ≤ |K| * ((N : ℝ) + 1) ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) h34.le
    _ < c * ((N : ℝ) + 1) ^ (1 / 4 : ℝ) / 2 * ((N : ℝ) + 1) ^ (3 / 4 : ℝ) :=
        mul_lt_mul_of_pos_right hK h34
    _ = c / 2 * (((N : ℝ) + 1) ^ (3 / 4 : ℝ) * ((N : ℝ) + 1) ^ (1 / 4 : ℝ)) := by ring
    _ = c * ((N : ℝ) + 1) / 2 := by rw [hsplit]; ring
    _ ≤ c * N := by nlinarith

/-- **Every twin tail is strongly exceptional.** -/
theorem twinTail_mem_strongExceptional (I : Finset ℕ) (x₀ : GaugeTorus) :
    twinTail I x₀ ∈ strongExceptional := by
  set L := (BezoutValuationIncidence.coprimeSquarefreeDensity (tailModulus I) : ℂ) *
    ∑ d ∈ (tailModulus I).divisors, tailWeight x₀ d / (d : ℂ)
  have hdens : 0 < BezoutValuationIncidence.coprimeSquarefreeDensity (tailModulus I) := by
    rw [BezoutValuationIncidence.coprimeSquarefreeDensity]
    refine mul_pos (by rw [RHTower.Sieve.squarefreeDensity_eq]; positivity)
      (prod_pos fun p hp => div_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
        (by positivity))
  have hL : L ≠ 0 := mul_ne_zero (by exact_mod_cast hdens.ne') (sum_tailWeight_div_ne_zero I x₀)
  have hLpos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hlim := tendsto_moebiusGaugeSum_twinTail_div I x₀
  intro K
  obtain ⟨N, hN1, hN2, hN3⟩ := ((hlim.eventually (Metric.ball_mem_nhds L (half_pos hLpos))).and
    ((eventually_mul_rpow_lt (K : ℝ) (half_pos hLpos)).and (eventually_ge_atTop 1))).exists
  refine ⟨N, hN2.trans_le ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN3
  rw [dist_eq_norm] at hN1
  have hq : ‖moebiusGaugeSum N (twinTail I x₀) / (N : ℂ)‖ ≥ ‖L‖ / 2 := by
    have h := norm_sub_norm_le L (moebiusGaugeSum N (twinTail I x₀) / (N : ℂ))
    rw [norm_sub_rev] at h
    linarith
  rw [norm_div, Complex.norm_natCast, ge_iff_le, le_div_iff₀ hN0] at hq
  linarith

/-- **Strongly exceptional points are dense**: every open set contains a twin tail. -/
theorem dense_strongExceptional : Dense strongExceptional := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨x₀, hx₀⟩
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU x₀ hx₀
  refine ⟨twinTail I x₀, hsub fun i hi => ?_, twinTail_mem_strongExceptional I x₀⟩
  simp only [twinTail, if_pos (mem_coe.mp hi)]
  exact (hu i (mem_coe.mp hi)).2

/-- **The Möbius exceptional set is comeager and Haar-null.** The gauge points where the
half-power law fails form a residual set — it contains the dense `G_δ` of strongly exceptional
points — while their Haar measure is zero. -/
theorem moebius_exceptional_residual_and_null :
    {x : GaugeTorus | ¬ GaugeHalfPowerLaw (fun n => ((μ n : ℤ) : ℂ)) x} ∈ residual GaugeTorus ∧
      gaugeHaar {x : GaugeTorus | ¬ GaugeHalfPowerLaw (fun n => ((μ n : ℤ) : ℂ)) x} = 0 := by
  refine ⟨mem_of_superset (residual_of_dense_Gδ isGδ_strongExceptional dense_strongExceptional)
    fun x hx => not_gaugeHalfPowerLaw_of_mem_strongExceptional hx, ?_⟩
  have h := ae_gaugeHalfPowerLaw (fun n => ((μ n : ℤ) : ℂ)) fun n => by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rwa [ae_iff] at h

/-- **Every neighbourhood of the gauge point `0` contains exceptional points.** -/
theorem zero_mem_closure_exceptional :
    (0 : GaugeTorus) ∈ closure {x : GaugeTorus | ¬ GaugeHalfPowerLaw (fun n => ((μ n : ℤ) : ℂ)) x} := by
  have hd : Dense {x : GaugeTorus | ¬ GaugeHalfPowerLaw (fun n => ((μ n : ℤ) : ℂ)) x} :=
    dense_strongExceptional.mono fun x hx => not_gaugeHalfPowerLaw_of_mem_strongExceptional hx
  rw [hd.closure_eq]
  trivial
end GaloisForLFunctions.ArithmeticCorrelationGeometry
