import GaloisForLFunctions.RHTower.DivisorSecondCenteredHyperbola
import GaloisForLFunctions.RHTower.MobiusDivisorClippedHomothety
import GaloisForLFunctions.RHTower.MobiusDivisorPrimePairEnergy
import GaloisForLFunctions.RHTower.Sieve.CoprimeSquarefreeDyadic
import GaloisForLFunctions.RHTower.MobiusDivisorTwoPrimeLocalCriterion
import GaloisForLFunctions.RHTower.GibbsMoebiusAnchor

/-!
# A quadratic reserve from the first prime merger

The unsigned divisor channel has a uniform square-root lower bound once
its quotient scale is large. A coprime squarefree counting estimate then
forces a positive quadratic release in every first prime pairing. The
pairing sum is identified exactly with the literal retained-state energy.

The constants are independent of the prime and cutoff. No bound for the
defect of subsequent mergers, exhaustive selection order, or signed Abel
sum is assumed or established here.
-/

noncomputable section
open Finset Filter Topology
open scoped ArithmeticFunction.Moebius
namespace RHTower

/-- A single quotient threshold gives a square-root lower bound for every
positive dilation channel, including the clipped endpoint. -/
theorem exists_divisorUnsignedDilationChannel_quotient_lower :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ M d : ℕ, 0 < d → A ≤ M/d →
      (1/32:ℝ)*Real.sqrt M ≤ divisorUnsignedDilationChannel M d := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    (eventually_divisorUnsignedDilationChannel_one_ge_sqrt_coefficient (1/32) (by norm_num))
  norm_num at hA
  refine ⟨max A 1, le_max_right _ _, ?_⟩
  intro M d hd hMd
  have hN : A ≤ M/d := (le_max_left _ _).trans hMd
  have hw0 := divisorPrimeClipWeight_nonneg M d hd
  have hw1 : 0 ≤ 1-divisorPrimeClipWeight M d := by
    have h := divisorPrimeClipWeight_lt_one M d hd
    linarith
  have h0 := mul_le_mul_of_nonneg_left (hA (M/d) hN) hw1
  have h1 := mul_le_mul_of_nonneg_left (hA (M/d+1) (by omega)) hw0
  have hs := mul_le_mul_of_nonneg_left (add_le_add h0 h1) (Real.sqrt_nonneg (d:ℝ))
  have hc := divisorUnsignedDilationChannel_prime_interpolation M d 1 hd
  simp only [Nat.mul_one] at hc
  have hclock := divisorPrimeClipWeight_mul_step M d hd
  push_cast at hclock
  rw [Real.sqrt_mul (Nat.cast_nonneg d)] at hclock
  rw [hc]
  push_cast at hs ⊢
  nlinarith only [hs, hclock]

private lemma coprime_squarefree_density_ge_quarter {p : ℕ} (hp : p.Prime) :
    (1/4:ℝ) ≤ (1-1/(p:ℝ))*Sieve.coprimeSquarefreeSum p := by
  rw [Sieve.coprime_density_eq hp, Sieve.squarefreeDensity_eq]
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpp : (0:ℝ) < (p:ℝ)+1 := by positivity
  have hpi : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have hpi16 : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  apply (le_div_iff₀ hpp).mpr
  rw [show (6/Real.pi^2)*(p:ℝ) = 6*(p:ℝ)/Real.pi^2 by ring]
  apply (le_div_iff₀ hpi).mpr
  have hmul := mul_le_mul_of_nonneg_left hpi16
    (show (0:ℝ) ≤ (1/4)*((p:ℝ)+1) by positivity)
  nlinarith only [hmul, hp2]

private lemma coprime_squarefree_prefix_ge_eighth {p N : ℕ}
    (hp : p.Prime) (hN : 1024 ≤ N) :
    (N:ℝ)/8 ≤ ∑ n ∈ Ioc 0 N, if p ∣ n then 0 else ((μ n : ℤ):ℝ)^2 := by
  let R := N/32+1
  have hR32 : 32 ≤ R := by dsimp [R]; omega
  have hNR : N ≤ 32*R := by dsimp [R]; omega
  have hNRsq : N ≤ R^2 := by
    calc
      N ≤ 32*R := hNR
      _ ≤ R*R := Nat.mul_le_mul_right R hR32
      _ = R^2 := by ring
  have hcount := Sieve.abs_window_coprime_squarefree_sub_le
    (t:=0) (L:=N) (R:=R) hp (by omega) (by simpa using hNRsq)
  simp only [Nat.zero_add] at hcount
  have hRpos : (0:ℝ) < R := by exact_mod_cast (show 0<R by omega)
  have hRupper : (R:ℝ) ≤ (N:ℝ)/32+1 := by
    have hdiv : ((N/32:ℕ):ℝ)*32 ≤ N := by exact_mod_cast Nat.div_mul_le_self N 32
    dsimp [R]
    push_cast
    linarith
  have hquot : (N:ℝ)/(R:ℝ) ≤ 32 := by
    apply (div_le_iff₀ hRpos).mpr
    exact_mod_cast hNR
  have herror : 2*(R:ℝ)+(N:ℝ)/(R:ℝ) ≤ (N:ℝ)/8 := by
    have hNreal : (1024:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hdensity := mul_le_mul_of_nonneg_left (coprime_squarefree_density_ge_quarter hp)
    (Nat.cast_nonneg (α:=ℝ) N)
  have hlower := (abs_le.mp hcount).1
  nlinarith only [hlower, herror, hdensity]

/-- Uniform positive quadratic energy release in the complete first-prime
pairing. The threshold applies to the quotient `M / p`. -/
theorem exists_mobiusDivisorFirstPrime_quadratic_release :
    ∃ c : ℝ, 0 < c ∧ ∃ T : ℕ, 1 ≤ T ∧ ∀ M p : ℕ, p.Prime → T ≤ M/p →
      c*(M:ℝ)^2/(p:ℝ) ≤
        (∑ d ∈ Icc 1 M, (mobiusDivisorDilationChannel M d)^2) -
          ∑ d ∈ (Icc 1 M).filter (fun d => ¬p ∣ d), (mobiusDivisorPrimePair M p d)^2 := by
  obtain ⟨A, hA, hchannel⟩ := exists_divisorUnsignedDilationChannel_quotient_lower
  have hApos : 0 < A := by omega
  have hAreal : (0:ℝ) < A := by exact_mod_cast hApos
  refine ⟨1/(8192*(A:ℝ)), by positivity, 1024*A, by omega, ?_⟩
  intro M p hp hMp
  let N := M/(p*A)
  have hden : 0 < p*A := Nat.mul_pos hp.pos hApos
  have hbound : 1024*(p*A) ≤ M := by
    have h := (Nat.le_div_iff_mul_le hp.pos).mp hMp
    nlinarith only [h]
  have hN : 1024 ≤ N := (Nat.le_div_iff_mul_le hden).mpr hbound
  have hNM : N ≤ M := Nat.div_le_self _ _
  let F : ℕ → ℝ := fun d => ((μ d : ℤ):ℝ)^2 *
    divisorUnsignedDilationChannel M d * divisorUnsignedDilationChannel M (p*d)
  have hF (d : ℕ) : 0 ≤ F d := mul_nonneg
    (mul_nonneg (sq_nonneg _) (divisorUnsignedDilationChannel_nonneg M d))
    (divisorUnsignedDilationChannel_nonneg M (p*d))
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 N) : ((μ d : ℤ):ℝ)^2*((M:ℝ)/1024) ≤ F d := by
    obtain ⟨hd1, hdN⟩ := mem_Icc.mp hd
    have hdpos : 0 < d := by omega
    have hprod : d*(p*A) ≤ M := (Nat.le_div_iff_mul_le hden).mp hdN
    have hpdA : A ≤ M/(p*d) := (Nat.le_div_iff_mul_le (Nat.mul_pos hp.pos hdpos)).mpr (by
      nlinarith only [hprod])
    have hdA : A ≤ M/d := (Nat.le_div_iff_mul_le hdpos).mpr (by
      have hdp : d ≤ p*d := by simpa using Nat.mul_le_mul_right d hp.one_le
      have h := Nat.mul_le_mul_left A hdp
      nlinarith only [hprod, h])
    have hl := hchannel M d hdpos hdA
    have hr := hchannel M (p*d) (Nat.mul_pos hp.pos hdpos) hpdA
    have hmul := mul_le_mul hl hr (by positivity) (divisorUnsignedDilationChannel_nonneg M d)
    have hsqrt := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) M)
    have hlower : (M:ℝ)/1024 ≤ divisorUnsignedDilationChannel M d *
        divisorUnsignedDilationChannel M (p*d) := by nlinarith only [hmul, hsqrt]
    have h := mul_le_mul_of_nonneg_left hlower (sq_nonneg (((μ d : ℤ):ℝ)))
    dsimp only [F]
    nlinarith only [h]
  have hI : Ioc 0 N = Icc 1 N := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  have hcount := coprime_squarefree_prefix_ge_eighth hp hN
  rw [hI] at hcount
  have hweighted : (M:ℝ)/1024 *
      (∑ d ∈ Icc 1 N, if p ∣ d then 0 else ((μ d : ℤ):ℝ)^2) ≤
        ∑ d ∈ (Icc 1 N).filter (fun d => ¬p ∣ d), F d := by
    rw [mul_sum, sum_filter]
    apply sum_le_sum
    intro d hd
    by_cases hpdiv : p ∣ d
    · simp [hpdiv]
    · simp only [hpdiv, if_false, not_false_eq_true, if_true]
      simpa only [mul_comm] using hpoint d hd
  have hsub : (Icc 1 N).filter (fun d => ¬p ∣ d) ⊆ (Icc 1 M).filter (fun d => ¬p ∣ d) := by
    intro d hd
    obtain ⟨hd, hpd⟩ := mem_filter.mp hd
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hd).2.trans hNM⟩, hpd⟩
  have hsum := sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hF d)
  have hoverlap : (M:ℝ)*(N:ℝ)/8192 ≤ ∑ d ∈ (Icc 1 M).filter (fun d => ¬p ∣ d), F d := by
    have hc := mul_le_mul_of_nonneg_left hcount (show (0:ℝ) ≤ (M:ℝ)/1024 by positivity)
    nlinarith only [hc, hweighted, hsum]
  have hMscale : (M:ℝ) ≤ 2*(p:ℝ)*(A:ℝ)*(N:ℝ) := by
    have hlt : M < (N+1)*(p*A) := (Nat.div_lt_iff_lt_mul hden).mp (by dsimp [N]; omega)
    have htwo : N+1 ≤ 2*N := by omega
    have h := hlt.le.trans (Nat.mul_le_mul_right (p*A) htwo)
    exact_mod_cast (show M ≤ 2*p*A*N by nlinarith only [h])
  have hpReal : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hscale : (1/(8192*(A:ℝ)))*(M:ℝ)^2/(p:ℝ) ≤ (M:ℝ)*(N:ℝ)/4096 := by
    apply (div_le_iff₀ hpReal).mpr
    rw [show (1/(8192*(A:ℝ)))*(M:ℝ)^2 = (M:ℝ)^2/(8192*(A:ℝ)) by ring]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 8192*(A:ℝ))).mpr
    have h := mul_le_mul_of_nonneg_left hMscale (Nat.cast_nonneg (α:=ℝ) M)
    nlinarith only [h]
  rw [sum_mobiusDivisorPrimePair_sq_eq hp]
  change _ ≤ _ - (_ - 2*(∑ d ∈ (Icc 1 M).filter (fun d => ¬p ∣ d), F d))
  nlinarith only [hscale, hoverlap]

private lemma unsigned_channel_zero_of_le {M d : ℕ} (hd : 0<d) (hM : M≤d) :
    divisorUnsignedDilationChannel M d = 0 := by
  simp [divisorUnsignedDilationChannel, Icc_eq_empty_of_lt (by omega : M-1<d)]

/-- The complete retained-state energy after selecting one prime is exactly
the coprime cofactor pairing sum, also when the prime is outside the cutoff. -/
theorem mobiusDivisorSelectionEnergy_singleton_eq_primePair (M : ℕ) {p : ℕ} (hp : p.Prime) :
    mobiusDivisorSelectionEnergy M {p} =
      ∑ d ∈ (Icc 1 M).filter (fun d => ¬p ∣ d), (mobiusDivisorPrimePair M p d)^2 := by
  let U := (mobiusDivisorSelectionPrimes M).erase p
  have hprimes (R : Finset ℕ) (hR : R ∈ U.powerset) : ∀ r ∈ R, r.Prime := by
    intro r hr
    exact (mem_filter.mp (mem_erase.mp (mem_powerset.mp hR hr)).2).2
  have hnot (R : Finset ℕ) (hR : R ∈ U.powerset) : p ∉ R := by
    intro hpR
    exact (mem_erase.mp (mem_powerset.mp hR hpR)).1 rfl
  have henergy : mobiusDivisorSelectionEnergy M {p} =
      ∑ R ∈ U.powerset,
        (divisorUnsignedDilationChannel M (∏ r ∈ R, r) -
          divisorUnsignedDilationChannel M (p*(∏ r ∈ R, r)))^2 := by
    unfold mobiusDivisorSelectionEnergy
    rw [subsetLabelEnergy_remaining]
    have hset : mobiusDivisorSelectionPrimes M \ {p} = U := by
      ext r
      simp [U, and_comm]
    rw [hset]
    apply sum_congr rfl
    intro R hR
    change (mobiusDivisorSelectionFibre M {p} R)^2 = _
    rw [← mobiusDivisorOrientedFibre_sq]
    change (mobiusDivisorOrientedFibre M (insert p ∅) R)^2 = _
    rw [mobiusDivisorOrientedFibre_insert M ∅ R p (hnot R hR),
      mobiusDivisorOrientedFibre_empty_eq_unsigned_product R (hprimes R hR) M,
      mobiusDivisorOrientedFibre_empty_eq_unsigned_product (insert p R) (by
        intro r hr
        rcases mem_insert.mp hr with rfl | hr
        · exact hp
        · exact hprimes R hR r hr) M,
      prod_insert (hnot R hR)]
  rw [henergy]
  apply sum_bij_ne_zero (fun R _ _ => ∏ r ∈ R, r)
  · intro R hR hne
    have hrpos : 0 < ∏ r ∈ R, r := prod_pos (fun r hr => (hprimes R hR r hr).pos)
    have hrle : (∏ r ∈ R, r) ≤ p*(∏ r ∈ R, r) := by
      simpa using Nat.mul_le_mul_right (∏ r ∈ R, r) hp.one_le
    have hrlt : (∏ r ∈ R, r) < M := by
      by_contra hn
      have hz := unsigned_channel_zero_of_le hrpos (not_lt.mp hn)
      have hzp := unsigned_channel_zero_of_le (Nat.mul_pos hp.pos hrpos) ((not_lt.mp hn).trans hrle)
      simp only [hz, hzp, sub_self, zero_pow (by omega : 2≠0), ne_eq, not_true_eq_false] at hne
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    intro hpd
    have hf := Nat.mem_primeFactors.mpr ⟨hp, hpd, hrpos.ne'⟩
    rw [Nat.primeFactors_prod (hprimes R hR)] at hf
    exact hnot R hR hf
  · intro R hR _ S hS _ he
    have hr := Nat.primeFactors_prod (hprimes R hR)
    have hs := Nat.primeFactors_prod (hprimes S hS)
    rw [← hr, ← hs, he]
  · intro d hd hne
    obtain ⟨hd, hpd⟩ := mem_filter.mp hd
    obtain ⟨hd1, hdM⟩ := mem_Icc.mp hd
    have hdpos : 0<d := by omega
    have hsf : Squarefree d := by
      by_contra hn
      simp [mobiusDivisorPrimePair, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn] at hne
    have hdlt : d<M := by
      by_contra hn
      have hz := unsigned_channel_zero_of_le hdpos (not_lt.mp hn)
      have hdp : d ≤ p*d := by simpa using Nat.mul_le_mul_right d hp.one_le
      have hzp := unsigned_channel_zero_of_le (Nat.mul_pos hp.pos hdpos) ((not_lt.mp hn).trans hdp)
      simp [mobiusDivisorPrimePair, hz, hzp] at hne
    have hR : d.primeFactors ∈ U.powerset := by
      apply mem_powerset.mpr
      intro r hr
      obtain ⟨hrprime, hrd, _⟩ := Nat.mem_primeFactors.mp hr
      apply mem_erase.mpr
      refine ⟨?_, mem_filter.mpr ⟨mem_range.mpr ?_, hrprime⟩⟩
      · intro he
        exact hpd (he ▸ hrd)
      · exact (Nat.le_of_mem_primeFactors hr).trans_lt hdlt
    have hNZ : (divisorUnsignedDilationChannel M (∏ r ∈ d.primeFactors, r) -
        divisorUnsignedDilationChannel M (p*(∏ r ∈ d.primeFactors, r)))^2 ≠ 0 := by
      rw [Nat.prod_primeFactors_of_squarefree hsf]
      intro hz
      apply hne
      rw [mobiusDivisorPrimePair, mul_pow, hz, mul_zero]
    exact ⟨d.primeFactors, hR, hNZ, Nat.prod_primeFactors_of_squarefree hsf⟩
  · intro R hR _
    have hsf := GibbsGas.squarefree_prod_primes (hprimes R hR)
    have hmu : (((μ (∏ r ∈ R, r) : ℤ):ℝ))^2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
    rw [mobiusDivisorPrimePair, mul_pow, hmu, one_mul]

/-- The literal source supplies a universal first-prime reserve of order
`M² / p` at all sufficiently large quotient scales. -/
theorem exists_mobiusDivisorSelectionEnergy_first_prime_reserve :
    ∃ c : ℝ, 0 < c ∧ ∃ T : ℕ, 1 ≤ T ∧ ∀ M p : ℕ, p.Prime → T ≤ M/p →
      c*(M:ℝ)^2/(p:ℝ) ≤ mobiusDivisorSelectionEnergy M ∅ - mobiusDivisorSelectionEnergy M {p} := by
  obtain ⟨c, hc, T, hT, h⟩ := exists_mobiusDivisorFirstPrime_quadratic_release
  refine ⟨c, hc, T, hT, ?_⟩
  intro M p hp hMp
  rw [mobiusDivisorSelectionEnergy_empty, mobiusDivisorSelectionEnergy_singleton_eq_primePair M hp]
  exact h M p hp hMp

end RHTower
