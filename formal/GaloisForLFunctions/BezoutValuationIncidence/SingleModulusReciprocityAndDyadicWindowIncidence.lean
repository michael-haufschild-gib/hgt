import GaloisForLFunctions.BezoutValuationIncidence.ReciprocityFormOfTheBernoulliKernel
import GaloisForLFunctions.BezoutValuationIncidence.CrossScaleCouplingOfPrimePacketsWithThePrimeBlock
import GaloisForLFunctions.ArithmeticIncidencePositivity.DyadicWindowIncidence

/-!
# Single-Modulus Kloosterman Reciprocity, Omitted-Class Compensation, and Additive Dyadic Window Incidence

This module resolves Topics 1 and 3 of the Research Topics (§7.8) for the Bézout–Valuation
Incidence programme:

1. **Witness-free Kloosterman reciprocity of the Bernoulli kernel and single-modulus sums (§1):**
   By Euler's totient theorem (`Nat.ModEq.pow_totient`) and Fermat's little theorem, the explicit
   modular inverses
   $$\bar n_d = n^{\varphi(d)-1} \bmod d, \qquad \bar n_p = n^{p-2} \bmod p$$
   (`modInvTotient`, `modInvNat`) satisfy $n \bar n_d \equiv 1 \pmod d$ for all $\gcd(n, d) = 1$
   ($d \ge 2$) and $n \bar n_p \equiv 1 \pmod p$ for all $p \nmid n$ ($p$ prime). Substituting these
   into the reciprocity law eliminates the external witness `nbar` from
   `bernoulliKernel_eq_reciprocity` and `abs_pmRamanujanEnergyCenteredGram_sub_reciprocity_le`
   (`bernoulliKernel_eq_reciprocity_totient`, `bernoulliKernel_eq_reciprocity_fermat`,
   `abs_pmRamanujanEnergyCenteredGram_sub_reciprocity_fermat_le`) and decomposes the single-modulus
   Bernoulli sum of any row $c'$ at prime $p$ into its divisible multiple sum $p \mid n$ and a
   finite cosecant–Bernoulli linear combination of Kloosterman-fraction sums over $p \nmid n$
   (`sum_bernoulliKernel_eq_divisible_add_kloosterman`).

2. **Constant centering versus omitted-class compensation of the prime row (§2):**
   - For the flat window row $\mathbf 1_{(Q, 2Q]}$ (`windowIndicatorRow Q`), periodicity and zero
     period mean of $\mathfrak B(p, \cdot) - m_p$ force $Q \cdot \Lambda_p(\mathbf 1_{(Q, 2Q]}) \to 0$
     (`tendsto_mul_kernelStatistic_windowIndicatorRow`).
   - Consequently, subtracting the global mean $1$ (`centredPrimeWindowRow Q = (\Lambda - 1)\mathbf 1_{(Q, 2Q]}`)
     cancels the rank-two readouts $\mathcal R'$ and $H'$ but **leaves the single-modulus kernel
     statistic unchanged at scale $1/Q$**:
     $$Q \cdot \Lambda_p\bigl((\Lambda - 1)\mathbf 1_{(Q, 2Q]}\bigr)
       \longrightarrow -\frac{\pi^2(p^2 - 1)^2}{144 p^2(p - 1)}$$
     (`tendsto_mul_kernelStatistic_centredPrimeWindowRow`).
   - Subtracting the finite omitted-class main term
     $\mathrm{omittedClassMainTerm}(p, Q) = -\frac{\mathfrak B(p, 0) - m_p}{p - 1} W(Q)$
     cancels the $1/Q$ anomaly of $\Lambda_p(\Lambda\mathbf 1_{(Q, 2Q]})$ identically
     (`tendsto_mul_kernelStatistic_primeWindowRow_sub_omittedClassMainTerm`).
   - At the row level, restoring the omitted divisible class via $\frac{p}{p-1}\mathbf 1_{p \mid n}$
     (`restoredPrimeWindowRow p Q`) or subtracting the coprime sieve weight
     $\frac{p}{p-1}\mathbf 1_{p \nmid n}$ (`coprimeCentredPrimeWindowRow p Q`) equidistributes all
     $p$ residue classes (including $0 \bmod p$) and forces
     $$Q \cdot \Lambda_p(\mathrm{restoredPrimeWindowRow}\, p\, Q) \longrightarrow 0, \qquad
       Q \cdot \Lambda_p(\mathrm{coprimeCentredPrimeWindowRow}\, p\, Q) \longrightarrow 0$$
     (`tendsto_mul_kernelStatistic_restoredPrimeWindowRow`,
     `tendsto_mul_kernelStatistic_coprimeCentredPrimeWindowRow`).

3. **Additive Bézout incidence inside a dyadic window $(X/2, 2X)$ (§3):**
   Inside `ArithmeticIncidencePositivity.InDyadicWindow X`:
   - Every pair of window elements $p, N \in (X/2, 2X)$ satisfies $\lfloor N/p \rfloor \in \{0, 1, 2, 3\}$
     (`div_mem_zero_one_two_three_of_inDyadicWindow`), partitioning the sawtooth $\{N/p\}$ into at
     most four affine shells $\{N/p\} = (N - kp)/p$ ($k \in \{0, 1, 2, 3\}$), with
     $\lfloor q/p \rfloor \in \{1, 2, 3\}$ whenever $p < q$ (`div_mem_one_two_three_of_lt_inDyadicWindow`).
   - Two proper divisor edges $(a_1, b_1)$ and $(a_2, b_2)$ inside $(X/2, 2X)$ land on consecutive
     integers $b_2 = b_1 + 1$ if and only if one is a doubling edge and the other is a tripling edge
     solving $3 a_2 - 2 a_1 = \pm 1$ (`divisor_edges_consecutive_iff`), which occurs if and only if
     $(a_1, a_2) = (3t + 1, 2t + 1)$ with endpoints $(6t + 2, 6t + 3)$ or $(a_1, a_2) = (2t + 1, 3t + 2)$
     with endpoints $(6t + 3, 6t + 4)$ (`bezout_two_three_iff_param`, `bezout_three_two_iff_param`),
     forcing $\gcd(a_1, a_2) = 1$ and fixing the exact sawtooth phases $\{N/a_i\} \in \{0, 1/a_1, 1 - 1/a_2\}$
     at the tripling endpoint $N = 6t + 3$ (`sawtooth_phases_at_bezout_tripling_endpoint_left`,
     `sawtooth_phases_at_bezout_tripling_endpoint_right`).
-/

open Finset Filter Topology RHTower RHTower.Sieve
open ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.ArithmeticIncidencePositivity
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Witness-Free Kloosterman Reciprocity of the Bernoulli Kernel -/

/-- The canonical Euler-totient modular inverse `n^{φ(d) - 1} mod d` of `n` modulo `d`. -/
def modInvTotient (d n : ℕ) : ℕ := n ^ (Nat.totient d - 1) % d

/-- The canonical Fermat modular inverse `n^{p - 2} mod p` of `n` modulo a prime `p`. -/
def modInvNat (p n : ℕ) : ℕ := n ^ (p - 2) % p

theorem modInvNat_eq_modInvTotient {p : ℕ} (hp : p.Prime) (n : ℕ) :
    modInvNat p n = modInvTotient p n := by
  rw [modInvNat, modInvTotient, Nat.totient_prime hp, Nat.sub_sub]

/-- **Euler's totient inverse identity.** For `d ≥ 2` and `gcd(n, d) = 1`,
`n * modInvTotient d n ≡ 1 (mod d)`. -/
theorem mul_modInvTotient_mod_eq_one {d n : ℕ} (hd : 2 ≤ d) (hcop : Nat.Coprime n d) :
    n * modInvTotient d n % d = 1 := by
  have hphi : 1 ≤ Nat.totient d := Nat.totient_pos.mpr (by omega)
  have hpow : n * n ^ (Nat.totient d - 1) = n ^ Nat.totient d := by
    rw [← pow_succ', Nat.sub_add_cancel hphi]
  have hmod := Nat.ModEq.pow_totient hcop
  rw [modInvTotient, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, hpow, hmod,
    Nat.mod_eq_of_lt (by omega : 1 < d)]

/-- **Fermat's modular inverse identity.** For a prime `p` and `p ∤ n`,
`n * modInvNat p n ≡ 1 (mod p)`. -/
theorem mul_modInvNat_mod_eq_one {p n : ℕ} (hp : p.Prime) (hnd : ¬ p ∣ n) :
    n * modInvNat p n % p = 1 := by
  rw [modInvNat_eq_modInvTotient hp]
  exact mul_modInvTotient_mod_eq_one hp.two_le (Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hnd))

/-- **Witness-free reciprocity form of the Bernoulli kernel at general modulus.**
For `d ≥ 2` and `gcd(n, d) = 1`,
`𝔅(d, n) = (π²/4) Σ_{k=1}^{d-1} B₂(k/d) / sin²(π k n̄_d / d)`. -/
theorem bernoulliKernel_eq_reciprocity_totient {d n : ℕ} (hd : 2 ≤ d) (hcop : Nat.Coprime n d) :
    bernoulliKernel d n = Real.pi ^ 2 / 4 *
      ∑ k ∈ Ico 1 d,
        bernoulliTwo ((k : ℝ) / d) / Real.sin (Real.pi * (k * modInvTotient d n : ℕ) / d) ^ 2 :=
  bernoulliKernel_eq_reciprocity hd (mul_modInvTotient_mod_eq_one hd hcop)

/-- **Witness-free Fermat reciprocity form of the Bernoulli kernel at a prime.**
For a prime `p` and `p ∤ n`,
`𝔅(p, n) = (π²/4) Σ_{k=1}^{p-1} B₂(k/p) / sin²(π k n̄_p / p)`. -/
theorem bernoulliKernel_eq_reciprocity_fermat {p n : ℕ} (hp : p.Prime) (hnd : ¬ p ∣ n) :
    bernoulliKernel p n = Real.pi ^ 2 / 4 *
      ∑ k ∈ Ico 1 p,
        bernoulliTwo ((k : ℝ) / p) / Real.sin (Real.pi * (k * modInvNat p n : ℕ) / p) ^ 2 :=
  bernoulliKernel_eq_reciprocity hp.two_le (mul_modInvNat_mod_eq_one hp hnd)

/-- **Witness-free reciprocity approximation for the pronic Gram of two distinct primes.** -/
theorem abs_pmRamanujanEnergyCenteredGram_sub_reciprocity_fermat_le {N p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpN : p ≤ N) (hqN : q ≤ N) :
    |pmRamanujanEnergyCenteredGram p q - (((p : ℝ) - 1) / 2 - Real.log p) * Real.log q +
        p * rowBeta N (unitRow p) - Real.pi ^ 2 / (4 * q) *
          ∑ k ∈ Ico 1 p,
            bernoulliTwo ((k : ℝ) / p) / Real.sin (Real.pi * (k * modInvNat p q : ℕ) / p) ^ 2| ≤
      3 / 4 * (p : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
  have hnd : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  exact abs_pmRamanujanEnergyCenteredGram_sub_reciprocity_le hp hq hpN hqN
    (mul_modInvNat_mod_eq_one hp hnd)

/-- **Exact Kloosterman-fraction decomposition of the single-modulus Bernoulli sum.**
For any prime `p`, cutoff `N`, and large-scale row `c'`, the quadratic Bernoulli sum splits into the
divisible multiple sum `p ∣ n` (weighted by `𝔅(p, 0) = π²(p² - 1)/72`) plus the `B₂(k/p)`-weighted
Kloosterman-fraction cosecant sums over `p ∤ n`. -/
theorem sum_bernoulliKernel_eq_divisible_add_kloosterman {p : ℕ} (hp : p.Prime)
    (N : ℕ) (c' : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * bernoulliKernel p n =
      Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 72 *
        (∑ n ∈ (Icc 1 N).filter (fun n => p ∣ n), c' n / (n : ℝ) ^ 2) +
      Real.pi ^ 2 / 4 * ∑ k ∈ Ico 1 p, bernoulliTwo ((k : ℝ) / p) *
        ∑ n ∈ (Icc 1 N).filter (fun n => ¬ p ∣ n),
          (c' n / (n : ℝ) ^ 2) / Real.sin (Real.pi * (k * modInvNat p n : ℕ) / p) ^ 2 := by
  rw [← sum_filter_add_sum_filter_not (Icc 1 N) (fun n => p ∣ n)]
  congr 1
  · rw [mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have hdvd : p ∣ n := (mem_filter.mp hn).2
    rw [bernoulliKernel_mod, Nat.mod_eq_zero_of_dvd hdvd, bernoulliKernel_zero hp.pos]
    ring
  · have hcop : ∑ n ∈ (Icc 1 N).filter (fun n => ¬ p ∣ n),
        c' n / (n : ℝ) ^ 2 * bernoulliKernel p n =
      ∑ n ∈ (Icc 1 N).filter (fun n => ¬ p ∣ n),
        ∑ k ∈ Ico 1 p, Real.pi ^ 2 / 4 * bernoulliTwo ((k : ℝ) / p) *
          ((c' n / (n : ℝ) ^ 2) / Real.sin (Real.pi * (k * modInvNat p n : ℕ) / p) ^ 2) := by
      refine sum_congr rfl fun n hn => ?_
      have hnd : ¬ p ∣ n := (mem_filter.mp hn).2
      rw [bernoulliKernel_eq_reciprocity_fermat hp hnd, ← mul_assoc, mul_sum]
      refine sum_congr rfl fun k _ => by ring
    rw [hcop, sum_comm, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, mul_sum]

/-! ## §2. Constant Centering versus Omitted-Class Compensation of the Prime Row -/

/-- The flat indicator row `1_{(Q, 2Q]}` on the dyadic window. -/
def windowIndicatorRow (Q : ℕ) (n : ℕ) : ℝ :=
  if Q < n ∧ n ≤ 2 * Q then 1 else 0

/-- The constant-centred prime row `(Λ - 1) · 1_{(Q, 2Q]}` on the dyadic window. -/
def centredPrimeWindowRow (Q : ℕ) (n : ℕ) : ℝ :=
  if Q < n ∧ n ≤ 2 * Q then vonMangoldt n - 1 else 0

/-- The finite omitted-class main term `-(𝔅(p, 0) - m_p)/(p - 1) · W(Q)` of the prime row at `p`. -/
def omittedClassMainTerm (p Q : ℕ) : ℝ :=
  -((bernoulliKernel p 0 - primeKernelMean p) / ((p : ℝ) - 1)) * dyadicInverseSquareMass Q

/-- The divisible-multiple compensating row `(p/(p - 1)) 1_{p ∣ n} · 1_{(Q, 2Q]}`. -/
def multipleCompensatingRow (p Q : ℕ) (n : ℕ) : ℝ :=
  if Q < n ∧ n ≤ 2 * Q then (if n % p = 0 then (p : ℝ) / ((p : ℝ) - 1) else 0) else 0

/-- The omitted-class-restored prime row `(Λ(n) + (p/(p - 1)) 1_{p ∣ n}) · 1_{(Q, 2Q]}`. -/
def restoredPrimeWindowRow (p Q : ℕ) (n : ℕ) : ℝ :=
  primeWindowRow Q n + multipleCompensatingRow p Q n

/-- The coprime-sieved centred prime row `(Λ(n) - (p/(p - 1)) 1_{p ∤ n}) · 1_{(Q, 2Q]}`. -/
def coprimeCentredPrimeWindowRow (p Q : ℕ) (n : ℕ) : ℝ :=
  if Q < n ∧ n ≤ 2 * Q then
    vonMangoldt n - (if n % p = 0 then 0 else (p : ℝ) / ((p : ℝ) - 1))
  else 0

theorem centredPrimeWindowRow_eq_sub (Q n : ℕ) :
    centredPrimeWindowRow Q n = primeWindowRow Q n - windowIndicatorRow Q n := by
  unfold centredPrimeWindowRow primeWindowRow windowIndicatorRow
  split_ifs <;> ring

theorem coprimeCentredPrimeWindowRow_eq_restored_sub_indicator (p Q n : ℕ) :
    coprimeCentredPrimeWindowRow p Q n =
      restoredPrimeWindowRow p Q n - ((p : ℝ) / ((p : ℝ) - 1)) * windowIndicatorRow Q n := by
  unfold coprimeCentredPrimeWindowRow restoredPrimeWindowRow primeWindowRow
    multipleCompensatingRow windowIndicatorRow
  split_ifs <;> ring

theorem kernelStatistic_add (N : ℕ) (c₁ c₂ : ℕ → ℝ) (p : ℕ) :
    kernelStatistic N (fun n => c₁ n + c₂ n) p =
      kernelStatistic N c₁ p + kernelStatistic N c₂ p := by
  simp only [kernelStatistic, ← sum_add_distrib]
  exact sum_congr rfl fun n _ => by ring

theorem kernelStatistic_sub (N : ℕ) (c₁ c₂ : ℕ → ℝ) (p : ℕ) :
    kernelStatistic N (fun n => c₁ n - c₂ n) p =
      kernelStatistic N c₁ p - kernelStatistic N c₂ p := by
  simp only [kernelStatistic, ← sum_sub_distrib]
  exact sum_congr rfl fun n _ => by ring

theorem kernelStatistic_const_mul (N : ℕ) (a : ℝ) (c : ℕ → ℝ) (p : ℕ) :
    kernelStatistic N (fun n => a * c n) p = a * kernelStatistic N c p := by
  simp only [kernelStatistic, mul_sum]
  exact sum_congr rfl fun n _ => by ring

/-- Explicit closed form of `omittedClassMainTerm p Q`. -/
theorem omittedClassMainTerm_eq {p : ℕ} (hp : p.Prime) (Q : ℕ) :
    omittedClassMainTerm p Q =
      -(Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (72 * (p : ℝ) ^ 2 * ((p : ℝ) - 1))) *
        dyadicInverseSquareMass Q := by
  unfold omittedClassMainTerm
  rw [bernoulliKernel_zero hp.pos, primeKernelMean]
  have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  field_simp

/-- **Exact finite omitted-class decomposition.** At every scale `Q`, the difference between
`Λ_p(Λ 1_{(Q, 2Q]})` and `omittedClassMainTerm p Q` is the sum of the centred coprime class
defects, the prime-power residue-`0` mass, and the cubic remainder. -/
theorem kernelStatistic_primeWindowRow_sub_omittedClassMainTerm_eq {p : ℕ} (hp : p.Prime) (Q : ℕ) :
    kernelStatistic (2 * Q) (primeWindowRow Q) p - omittedClassMainTerm p Q =
      ∑ r ∈ (range p).erase 0,
        (bernoulliKernel p r - primeKernelMean p) *
          (primeClassMass p r Q - dyadicInverseSquareMass Q / ((p : ℝ) - 1)) +
      (bernoulliKernel p 0 - primeKernelMean p) * primeClassMass p 0 Q +
      ∑ n ∈ Ioc Q (2 * Q), vonMangoldt n / (n : ℝ) ^ 3 * cubicKernel p n := by
  set b : ℕ → ℝ := fun r => bernoulliKernel p r - primeKernelMean p
  have hsum0 : ∑ r ∈ (range p).erase 0, b r = -(b 0) := by
    have h := sum_range_bernoulliKernel_sub_mean hp
    rw [← add_sum_erase _ _ (mem_range.mpr hp.pos)] at h
    linarith
  rw [kernelStatistic_primeWindowRow_eq hp Q, ← add_sum_erase _ _ (mem_range.mpr hp.pos),
    omittedClassMainTerm]
  have hsplit : ∑ r ∈ (range p).erase 0,
      b r * (primeClassMass p r Q - dyadicInverseSquareMass Q / ((p : ℝ) - 1)) =
      ∑ r ∈ (range p).erase 0, b r * primeClassMass p r Q -
        dyadicInverseSquareMass Q / ((p : ℝ) - 1) * ∑ r ∈ (range p).erase 0, b r := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun r _ => by ring
  rw [hsplit, hsum0]
  simp only [b]
  ring

/-- **Subtracting the omitted-class main term cancels the `1/Q` anomaly.**
`Q · (Λ_p(Λ 1_{(Q, 2Q]}) - omittedClassMainTerm p Q) → 0`. -/
theorem tendsto_mul_kernelStatistic_primeWindowRow_sub_omittedClassMainTerm {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ =>
      (Q : ℝ) * (kernelStatistic (2 * Q) (primeWindowRow Q) p - omittedClassMainTerm p Q))
      atTop (𝓝 0) := by
  have h1 := tendsto_mul_kernelStatistic_primeWindowRow hp
  set c72 := -(Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (72 * (p : ℝ) ^ 2 * ((p : ℝ) - 1)))
  have h2 : Tendsto (fun Q : ℕ => (Q : ℝ) * omittedClassMainTerm p Q) atTop
      (𝓝 (-(Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (144 * (p : ℝ) ^ 2 * ((p : ℝ) - 1))))) := by
    have h := tendsto_mul_dyadicInverseSquareMass.const_mul c72
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hp1 : (p : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      linarith
    have hval : c72 * (1 / 2) =
        -(Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (144 * (p : ℝ) ^ 2 * ((p : ℝ) - 1))) := by
      simp only [c72]; field_simp; ring
    rw [hval] at h
    refine h.congr fun Q => ?_
    rw [omittedClassMainTerm_eq hp Q]; simp only [c72]; ring
  have hsub := h1.sub h2
  rw [sub_self] at hsub
  exact hsub.congr fun Q => by ring

/-- Any `p`-periodic sequence `g` with zero period sum has `Q Σ_{Q < n ≤ 2Q} g(n)/n² → 0`. -/
theorem tendsto_mul_sum_Ioc_div_sq_of_periodic_zero_sum {g : ℕ → ℝ} {p : ℕ} (hp : 0 < p)
    (hper : ∀ n, g (n + p) = g n) (h0 : ∑ r ∈ range p, g r = 0)
    {B : ℝ} (_ : 0 ≤ B) (hbound : ∀ n, |g n| ≤ B) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * ∑ n ∈ Ioc Q (2 * Q), g n / (n : ℝ) ^ 2) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have hpart : ∀ x : ℕ, |∑ n ∈ Icc 1 x, g n| ≤ p * B := by
    intro x
    have hIcc : Icc 1 x = Ico 1 (1 + x) := by
      ext n; simp only [mem_Icc, mem_Ico]; omega
    rw [hIcc]
    exact abs_sum_Ico_le_of_periodic hp hper h0 hbound 1 x
  set x₀ := ⌈4 * (p * B) / η⌉₊ + 1
  refine ⟨x₀, fun Q hQ => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hlin : ∀ x, Q ≤ x → x ≤ 2 * Q → |∑ n ∈ Icc 1 x, g n| ≤ (η / 4) * x := by
    intro x hxQ _
    have hx0 : (4 * (p * B) / η : ℝ) ≤ x := by
      have h1 : (⌈4 * (p * B) / η⌉₊ : ℝ) ≤ Q := by exact_mod_cast (by omega : ⌈4 * (p * B) / η⌉₊ ≤ Q)
      have h2 : (Q : ℝ) ≤ x := by exact_mod_cast hxQ
      linarith [Nat.le_ceil (4 * (p * B) / η)]
    have hmul : p * B ≤ (η / 4) * x := by
      have h := mul_le_mul_of_nonneg_left hx0 (show (0 : ℝ) ≤ η / 4 by positivity)
      have hne : η ≠ 0 := hη.ne'
      have hsimp : (η / 4) * (4 * (p * B) / η) = p * B := by field_simp
      linarith
    exact (hpart x).trans hmul
  have hab := abs_sum_Ioc_mul_le_of_linear (s := g)
    (w := fun n : ℕ => 1 / (n : ℝ) ^ 2) (L := η / 4) (D := Q) (X := 2 * Q) (by omega)
    hlin (fun n => by positivity)
    (fun n hn => one_div_le_one_div_of_le (by
        have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        positivity) (pow_le_pow_left₀ (Nat.cast_nonneg _) (by push_cast; linarith) 2))
  have hhead : 2 * (Q : ℝ) * (1 / ((Q + 1 : ℕ) : ℝ) ^ 2) ≤ 2 / (Q : ℝ) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hQ0]; push_cast; nlinarith
  have htail : ∑ n ∈ Ioc Q (2 * Q), 1 / (n : ℝ) ^ 2 ≤ 1 / (Q : ℝ) :=
    (dyadicInverseSquareMass_le Q).trans (one_div_le_one_div_of_le hQ0 (by linarith))
  have hrw : (∑ n ∈ Ioc Q (2 * Q), g n / (n : ℝ) ^ 2) =
      ∑ n ∈ Ioc Q (2 * Q), g n * (1 / (n : ℝ) ^ 2) :=
    sum_congr rfl fun n _ => by ring
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hQ0, hrw]
  calc (Q : ℝ) * |∑ n ∈ Ioc Q (2 * Q), g n * (1 / (n : ℝ) ^ 2)|
      ≤ (Q : ℝ) * (η / 4 * (2 / (Q : ℝ) + 1 / (Q : ℝ))) :=
        mul_le_mul_of_nonneg_left (hab.trans (mul_le_mul_of_nonneg_left
          (add_le_add hhead htail) (by positivity))) hQ0.le
    _ = 3 * η / 4 := by field_simp; ring
    _ < η := by linarith

/-- **The flat window indicator row has `o(1/Q)` single-modulus kernel statistic.** -/
theorem tendsto_mul_kernelStatistic_windowIndicatorRow {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * kernelStatistic (2 * Q) (windowIndicatorRow Q) p) atTop (𝓝 0) := by
  have hquad : Tendsto (fun Q : ℕ => (Q : ℝ) * ∑ n ∈ Ioc Q (2 * Q),
      (bernoulliKernel p n - primeKernelMean p) / (n : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_mul_sum_Ioc_div_sq_of_periodic_zero_sum hp.pos
      (fun n => by rw [bernoulliKernel_add_period])
      (sum_range_bernoulliKernel_sub_mean hp) (by positivity)
      (abs_bernoulliKernel_sub_mean_le hp)
  have hcub : Tendsto (fun Q : ℕ => (Q : ℝ) * ∑ n ∈ Ioc Q (2 * Q),
      1 / (n : ℝ) ^ 3 * cubicKernel p n) atTop (𝓝 0) := by
    have hbound : ∀ Q : ℕ, 1 ≤ Q → |(Q : ℝ) * ∑ n ∈ Ioc Q (2 * Q),
        1 / (n : ℝ) ^ 3 * cubicKernel p n| ≤ (p : ℝ) ^ 3 * (1 / (Q : ℝ)) := by
      intro Q hQ
      have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
      have hterm : ∀ n ∈ Ioc Q (2 * Q), |1 / (n : ℝ) ^ 3 * cubicKernel p n| ≤
          1 / (Q : ℝ) ^ 3 * (p : ℝ) ^ 3 := by
        intro n hn
        rw [mem_Ioc] at hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hQn : (Q : ℝ) ≤ n := by exact_mod_cast hn.1.le
        rw [abs_mul, abs_of_pos (by positivity)]
        exact mul_le_mul (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hQ0.le hQn 3))
          (abs_cubicKernel_le hp.pos n) (abs_nonneg _) (by positivity)
      rw [abs_mul, abs_of_pos hQ0]
      calc (Q : ℝ) * |∑ n ∈ Ioc Q (2 * Q), 1 / (n : ℝ) ^ 3 * cubicKernel p n|
          ≤ (Q : ℝ) * ∑ _n ∈ Ioc Q (2 * Q), 1 / (Q : ℝ) ^ 3 * (p : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)) hQ0.le
        _ = (p : ℝ) ^ 3 * (1 / (Q : ℝ)) := by
            rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, show 2 * Q - Q = Q by omega]; field_simp
    have hlim : Tendsto (fun Q : ℕ => (p : ℝ) ^ 3 * (1 / (Q : ℝ))) atTop (𝓝 0) := by
      have h := tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat (a := (p : ℝ) ^ 3)
      simpa only [mul_zero] using h
    refine squeeze_zero_norm' (eventually_ge_atTop 1 |>.mono fun Q hQ => ?_) hlim
    rw [Real.norm_eq_abs]; exact hbound Q hQ
  have hsum := hquad.add hcub
  rw [add_zero] at hsum
  refine hsum.congr fun Q => ?_
  have hsub : Ioc Q (2 * Q) ⊆ Icc 1 (2 * Q) := fun n hn => by
    rw [mem_Ioc] at hn; rw [mem_Icc]; omega
  have hrestrict : kernelStatistic (2 * Q) (windowIndicatorRow Q) p =
      ∑ n ∈ Ioc Q (2 * Q), ((bernoulliKernel p n - primeKernelMean p) / (n : ℝ) ^ 2 +
        1 / (n : ℝ) ^ 3 * cubicKernel p n) := by
    rw [kernelStatistic, ← sum_subset hsub fun n _ hn' => by
      have : ¬ (Q < n ∧ n ≤ 2 * Q) := fun h => hn' (mem_Ioc.mpr h)
      simp [windowIndicatorRow, this]]
    refine sum_congr rfl fun n hn => ?_
    rw [mem_Ioc] at hn
    simp [windowIndicatorRow, hn.1, hn.2]
    ring
  rw [hrestrict, sum_add_distrib, mul_add]

/-- **Constant centering does not cancel the omitted residue class.**
Subtracting the global constant `1` on `(Q, 2Q]` leaves the `1/Q` single-modulus kernel statistic
identical to that of the uncentred prime row:
`Q · Λ_p((Λ - 1) 1_{(Q, 2Q]}) → -π²(p² - 1)²/(144 p² (p - 1))`. -/
theorem tendsto_mul_kernelStatistic_centredPrimeWindowRow {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * kernelStatistic (2 * Q) (centredPrimeWindowRow Q) p) atTop
      (𝓝 (-(Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (144 * (p : ℝ) ^ 2 * ((p : ℝ) - 1))))) := by
  have h := (tendsto_mul_kernelStatistic_primeWindowRow hp).sub
    (tendsto_mul_kernelStatistic_windowIndicatorRow hp)
  rw [sub_zero] at h
  refine h.congr fun Q => ?_
  have heq : centredPrimeWindowRow Q = fun n => primeWindowRow Q n - windowIndicatorRow Q n :=
    funext (centredPrimeWindowRow_eq_sub Q)
  rw [heq, kernelStatistic_sub, mul_sub]

/-- The cubic Bernoulli kernel vanishes at `0` modulo `d`. -/
theorem cubicKernel_zero {d : ℕ} (hd : 0 < d) : cubicKernel d 0 = 0 := by
  have h := hasSum_cubicKernel hd 0
  have hzero : (fun j : ℕ => (2 * cubicPotential d ((j + 1) * 0) -
      residuePotential d ((j + 1) * 0)) / ((j : ℝ) + 1) ^ 3) = fun _ => 0 := by
    funext j
    rw [mul_zero, two_mul_cubicPotential_sub_eq_poly hd, Nat.zero_mod, Nat.cast_zero,
      cubicDiffPoly_zero, zero_div]
  rw [hzero] at h
  exact h.unique hasSum_zero

/-- **The divisible-multiple compensating row supplies the exact opposite of the omitted-class anomaly.**
`Q · Λ_p((p/(p-1)) 1_{p ∣ n} 1_{(Q, 2Q]}) → +π²(p² - 1)²/(144 p² (p - 1))`. -/
theorem tendsto_mul_kernelStatistic_multipleCompensatingRow {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * kernelStatistic (2 * Q) (multipleCompensatingRow p Q) p) atTop
      (𝓝 (Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (144 * (p : ℝ) ^ 2 * ((p : ℝ) - 1)))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set g : ℕ → ℝ := fun n => (if n % p = 0 then (p : ℝ) else 0) - 1
  have hg_per : ∀ n, g (n + p) = g n := fun n => by simp only [g, Nat.add_mod_right]
  have hg_sum : ∑ r ∈ range p, g r = 0 := by
    simp only [g, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    rw [← add_sum_erase _ _ (mem_range.mpr hp.pos)]
    simp only [Nat.zero_mod, ↓reduceIte]
    have hrest : ∑ x ∈ (range p).erase 0, (if x % p = 0 then (p : ℝ) else 0) = 0 := by
      refine sum_eq_zero fun x hx => ?_
      rw [Nat.mod_eq_of_lt (mem_range.mp (mem_of_mem_erase hx)), if_neg (ne_of_mem_erase hx)]
    rw [hrest]; ring
  have hg_bound : ∀ n, |g n| ≤ p := fun n => by
    simp only [g]
    split_ifs
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [zero_sub, abs_neg, abs_one]; linarith
  have h_mult_mass : Tendsto (fun Q : ℕ =>
      (Q : ℝ) * ∑ n ∈ Ioc Q (2 * Q), ((if n % p = 0 then (p : ℝ) else 0) - 1) / (n : ℝ) ^ 2)
      atTop (𝓝 0) :=
    tendsto_mul_sum_Ioc_div_sq_of_periodic_zero_sum hp.pos hg_per hg_sum (by positivity) hg_bound
  set b0 := bernoulliKernel p 0 - primeKernelMean p
  have hquad : Tendsto (fun Q : ℕ =>
      (Q : ℝ) * ∑ n ∈ Ioc Q (2 * Q),
        (if n % p = 0 then (p : ℝ) / ((p : ℝ) - 1) else 0) / (n : ℝ) ^ 2 *
          (bernoulliKernel p n - primeKernelMean p))
      atTop (𝓝 (b0 / ((p : ℝ) - 1) * (1 / 2))) := by
    have h1 := (h_mult_mass.add tendsto_mul_dyadicInverseSquareMass).const_mul (b0 / ((p : ℝ) - 1))
    rw [zero_add] at h1
    refine h1.congr fun Q => ?_
    rw [dyadicInverseSquareMass, ← mul_add, ← sum_add_distrib, mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    split_ifs with h0
    · rw [bernoulliKernel_mod, h0]
      simp only [b0]
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp; ring
    · ring
  have hcub : Tendsto (fun Q : ℕ =>
      (Q : ℝ) * ∑ n ∈ Ioc Q (2 * Q),
        (if n % p = 0 then (p : ℝ) / ((p : ℝ) - 1) else 0) / (n : ℝ) ^ 3 * cubicKernel p n)
      atTop (𝓝 0) := by
    refine Tendsto.congr (fun Q => ?_) tendsto_const_nhds
    have h0 : ∑ n ∈ Ioc Q (2 * Q),
        (if n % p = 0 then (p : ℝ) / ((p : ℝ) - 1) else 0) / (n : ℝ) ^ 3 * cubicKernel p n = 0 := by
      refine sum_eq_zero fun n _ => ?_
      split_ifs with hmod
      · rw [cubicKernel_mod, hmod, cubicKernel_zero hp.pos, mul_zero]
      · simp
    rw [h0, mul_zero]
  have htot := hquad.add hcub
  have hb0 : b0 / ((p : ℝ) - 1) * (1 / 2) + 0 =
      Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (144 * (p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by
    simp only [b0, bernoulliKernel_zero hp.pos, primeKernelMean]
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    have : (p : ℝ) ≠ 0 := by positivity
    field_simp; ring
  rw [hb0] at htot
  refine htot.congr fun Q => ?_
  have hsub : Ioc Q (2 * Q) ⊆ Icc 1 (2 * Q) := fun n hn => by
    rw [mem_Ioc] at hn; rw [mem_Icc]; omega
  have hrestrict : kernelStatistic (2 * Q) (multipleCompensatingRow p Q) p =
      ∑ n ∈ Ioc Q (2 * Q),
        ((if n % p = 0 then (p : ℝ) / ((p : ℝ) - 1) else 0) / (n : ℝ) ^ 2 *
          (bernoulliKernel p n - primeKernelMean p) +
        (if n % p = 0 then (p : ℝ) / ((p : ℝ) - 1) else 0) / (n : ℝ) ^ 3 * cubicKernel p n) := by
    rw [kernelStatistic, ← sum_subset hsub fun n _ hn' => by
      have : ¬ (Q < n ∧ n ≤ 2 * Q) := fun h => hn' (mem_Ioc.mpr h)
      simp [multipleCompensatingRow, this]]
    refine sum_congr rfl fun n hn => ?_
    rw [mem_Ioc] at hn
    simp [multipleCompensatingRow, hn.1, hn.2]
  rw [hrestrict, sum_add_distrib, mul_add]

/-- **Omitted-class restoration cancels the single-modulus kernel statistic.**
For every prime `p`, `Q · Λ_p((Λ + (p/(p-1)) 1_{p ∣ n}) 1_{(Q, 2Q]}) → 0`. -/
theorem tendsto_mul_kernelStatistic_restoredPrimeWindowRow {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * kernelStatistic (2 * Q) (restoredPrimeWindowRow p Q) p)
      atTop (𝓝 0) := by
  have h := (tendsto_mul_kernelStatistic_primeWindowRow hp).add
    (tendsto_mul_kernelStatistic_multipleCompensatingRow hp)
  rw [neg_add_cancel] at h
  refine h.congr fun Q => ?_
  have heq : restoredPrimeWindowRow p Q =
      fun n => primeWindowRow Q n + multipleCompensatingRow p Q n := rfl
  rw [heq, kernelStatistic_add, mul_add]

/-- **Coprime-sieved centering cancels the single-modulus kernel statistic.**
For every prime `p`, subtracting `(p/(p - 1)) 1_{p ∤ n}` on `(Q, 2Q]` yields
`Q · Λ_p((Λ - (p/(p-1)) 1_{p ∤ n}) 1_{(Q, 2Q]}) → 0`. -/
theorem tendsto_mul_kernelStatistic_coprimeCentredPrimeWindowRow {p : ℕ} (hp : p.Prime) :
    Tendsto (fun Q : ℕ => (Q : ℝ) * kernelStatistic (2 * Q) (coprimeCentredPrimeWindowRow p Q) p)
      atTop (𝓝 0) := by
  have h := (tendsto_mul_kernelStatistic_restoredPrimeWindowRow hp).sub
    ((tendsto_mul_kernelStatistic_windowIndicatorRow hp).const_mul ((p : ℝ) / ((p : ℝ) - 1)))
  simp only [mul_zero, sub_self] at h
  refine h.congr fun Q => ?_
  have heq : coprimeCentredPrimeWindowRow p Q = fun n =>
      restoredPrimeWindowRow p Q n - ((p : ℝ) / ((p : ℝ) - 1)) * windowIndicatorRow Q n :=
    funext (coprimeCentredPrimeWindowRow_eq_restored_sub_indicator p Q)
  rw [heq, kernelStatistic_sub, kernelStatistic_const_mul]
  ring

/-! ## §3. Additive Window Structure for the Incidence Face inside `(X/2, 2X)` -/

/-- **Four-shell jump partition inside a dyadic window.**
For any modulus `p` and cutoff `N` inside the open dyadic window `(X/2, 2X)`, the jump count
`⌊N/p⌋` belongs to `{0, 1, 2, 3}`. -/
theorem div_mem_zero_one_two_three_of_inDyadicWindow {X : ℝ} {p N : ℕ}
    (hp : InDyadicWindow X p) (hN : InDyadicWindow X N) :
    N / p = 0 ∨ N / p = 1 ∨ N / p = 2 ∨ N / p = 3 := by
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with rfl | h
    · have h1 := hp.1; have h2 := hN.2
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    · exact h
  have hlt4 : N < 4 * p := by
    have h := lt_four_mul_of_inDyadicWindow hp hN
    have h' : ((N : ℕ) : ℝ) < ((4 * p : ℕ) : ℝ) := by push_cast; exact h
    exact Nat.cast_lt.mp h'
  have hdiv : N / p < 4 := (Nat.div_lt_iff_lt_mul hp0).mpr hlt4
  rcases hq : N / p with _ | _ | _ | _ | k <;> omega

/-- **Three-branch Euclidean quotient for ordered moduli in a dyadic window.**
For `p < q` inside `(X/2, 2X)`, the Euclidean quotient `⌊q/p⌋` belongs to `{1, 2, 3}`. -/
theorem div_mem_one_two_three_of_lt_inDyadicWindow {X : ℝ} {p q : ℕ}
    (hp : InDyadicWindow X p) (hq : InDyadicWindow X q) (hpq : p < q) :
    q / p = 1 ∨ q / p = 2 ∨ q / p = 3 := by
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with rfl | h
    · have h1 := hp.1; have h2 := hq.2
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      linarith
    · exact h
  have h1 : 1 ≤ q / p := (Nat.le_div_iff_mul_le hp0).mpr (by omega)
  rcases div_mem_zero_one_two_three_of_inDyadicWindow hp hq with h0 | h1' | h2 | h3
  · omega
  · left; exact h1'
  · right; left; exact h2
  · right; right; exact h3

/-- **Piecewise affine sawtooth representation on the four dyadic shells.**
For `p, N ∈ (X/2, 2X)`, there is `k ∈ {0, 1, 2, 3}` with `k p ≤ N < (k + 1) p` and
`{N/p} = (N - k p)/p`. -/
theorem fract_div_eq_sub_of_inDyadicWindow {X : ℝ} {p N : ℕ}
    (hp : InDyadicWindow X p) (hN : InDyadicWindow X N) :
    ∃ k ∈ ({0, 1, 2, 3} : Finset ℕ),
      k * p ≤ N ∧ N < (k + 1) * p ∧
      Int.fract ((N : ℝ) / p) = ((N - k * p : ℕ) : ℝ) / p := by
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with rfl | h
    · have h1 := hp.1; have h2 := hN.2
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    · exact h
  refine ⟨N / p, ?_, Nat.div_mul_le_self N p, ?_, ?_⟩
  · rcases div_mem_zero_one_two_three_of_inDyadicWindow hp hN with h | h | h | h <;> simp [h]
  · rw [add_mul, one_mul]
    exact Nat.lt_div_mul_add hp0
  · have hle : N / p * p ≤ N := Nat.div_mul_le_self N p
    have hlt : N - N / p * p < p := by
      have := Nat.lt_div_mul_add (a := N) hp0
      omega
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
    set q : ℕ := N / p
    have hrw : (N : ℝ) / p = ((N - q * p : ℕ) : ℝ) / p + ((q : ℤ) : ℝ) := by
      rw [Nat.cast_sub hle]
      push_cast
      field_simp
      ring
    rw [hrw, Int.fract_add_intCast, Int.fract_eq_self.mpr]
    exact ⟨by positivity, (div_lt_one hpR).mpr (by exact_mod_cast hlt)⟩

/-- **Additive Bézout classification of consecutive divisor edges in a dyadic window.**
Two proper divisor edges `(a₁, b₁)` and `(a₂, b₂)` inside `(X/2, 2X)` land on consecutive integers
`b₂ = b₁ + 1` if and only if one is a doubling edge and the other is a tripling edge satisfying
`3 a₂ = 2 a₁ + 1` or `2 a₂ = 3 a₁ + 1`. -/
theorem divisor_edges_consecutive_iff {X : ℝ} {a₁ b₁ a₂ b₂ : ℕ}
    (ha₁ : InDyadicWindow X a₁) (hb₁ : InDyadicWindow X b₁) (hab₁ : a₁ < b₁) (hd₁ : a₁ ∣ b₁)
    (ha₂ : InDyadicWindow X a₂) (hb₂ : InDyadicWindow X b₂) (hab₂ : a₂ < b₂) (hd₂ : a₂ ∣ b₂) :
    b₂ = b₁ + 1 ↔
      (b₁ = 2 * a₁ ∧ b₂ = 3 * a₂ ∧ 3 * a₂ = 2 * a₁ + 1) ∨
      (b₁ = 3 * a₁ ∧ b₂ = 2 * a₂ ∧ 2 * a₂ = 3 * a₁ + 1) := by
  constructor
  · intro hcon
    rcases eq_two_mul_or_three_mul_of_dvd ha₁ hb₁ hab₁ hd₁ with h1 | h1 <;>
    rcases eq_two_mul_or_three_mul_of_dvd ha₂ hb₂ hab₂ hd₂ with h2 | h2
    · omega
    · left; exact ⟨h1, h2, by omega⟩
    · right; exact ⟨h1, h2, by omega⟩
    · omega
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> omega

/-- **Modulo-6 parameterization of `3 a₂ = 2 a₁ + 1`.**
`3 a₂ = 2 a₁ + 1` holds if and only if `a₁ = 3 t + 1` and `a₂ = 2 t + 1` for `t = a₁ / 3`, with
consecutive edge endpoints `(2 a₁, 3 a₂) = (6 t + 2, 6 t + 3)`. -/
theorem bezout_two_three_iff_param {a₁ a₂ : ℕ} :
    3 * a₂ = 2 * a₁ + 1 ↔
      ∃ t : ℕ, a₁ = 3 * t + 1 ∧ a₂ = 2 * t + 1 ∧ 2 * a₁ = 6 * t + 2 ∧ 3 * a₂ = 6 * t + 3 := by
  constructor
  · intro h
    refine ⟨a₁ / 3, by omega, by omega, by omega, by omega⟩
  · rintro ⟨t, rfl, rfl, -, -⟩
    ring

/-- **Modulo-6 parameterization of `2 a₂ = 3 a₁ + 1`.**
`2 a₂ = 3 a₁ + 1` holds if and only if `a₁ = 2 t + 1` and `a₂ = 3 t + 2` for `t = a₁ / 2`, with
consecutive edge endpoints `(3 a₁, 2 a₂) = (6 t + 3, 6 t + 4)`. -/
theorem bezout_three_two_iff_param {a₁ a₂ : ℕ} :
    2 * a₂ = 3 * a₁ + 1 ↔
      ∃ t : ℕ, a₁ = 2 * t + 1 ∧ a₂ = 3 * t + 2 ∧ 3 * a₁ = 6 * t + 3 ∧ 2 * a₂ = 6 * t + 4 := by
  constructor
  · intro h
    refine ⟨a₁ / 2, by omega, by omega, by omega, by omega⟩
  · rintro ⟨t, rfl, rfl, -, -⟩
    ring

/-- Any pair `(a₁, a₂)` coupled by `3 a₂ = 2 a₁ + 1` or `2 a₂ = 3 a₁ + 1` is coprime. -/
theorem coprime_of_bezout_two_three {a₁ a₂ : ℕ}
    (h : 3 * a₂ = 2 * a₁ + 1 ∨ 2 * a₂ = 3 * a₁ + 1) :
    Nat.Coprime a₁ a₂ := by
  rw [Nat.coprime_iff_gcd_eq_one]
  refine Nat.eq_one_of_dvd_one ?_
  have hd₁ : Nat.gcd a₁ a₂ ∣ a₁ := Nat.gcd_dvd_left a₁ a₂
  have hd₂ : Nat.gcd a₁ a₂ ∣ a₂ := Nat.gcd_dvd_right a₁ a₂
  rcases h with h1 | h2
  · have hsub : 3 * a₂ - 2 * a₁ = 1 := by omega
    rw [← hsub]
    exact Nat.dvd_sub (dvd_mul_of_dvd_right hd₂ 3) (dvd_mul_of_dvd_right hd₁ 2)
  · have hsub : 2 * a₂ - 3 * a₁ = 1 := by omega
    rw [← hsub]
    exact Nat.dvd_sub (dvd_mul_of_dvd_right hd₂ 2) (dvd_mul_of_dvd_right hd₁ 3)

/-- **Exact sawtooth phases at the Bézout tripling endpoint `N = 6t + 3` (`3 a₂ = 2 a₁ + 1`).**
At `N = 3 a₂ = 2 a₁ + 1` (`a₁ = 3t + 1`, `a₂ = 2t + 1`), `a₂` is at an exact integer jump
(`{N/a₂} = 0`), while for `t ≥ 1`, `a₁` has quotient `2`, remainder `1`, and fractional part `1/a₁`. -/
theorem sawtooth_phases_at_bezout_tripling_endpoint_left (t : ℕ) :
    let a₁ := 3 * t + 1
    let a₂ := 2 * t + 1
    let N := 6 * t + 3
    N % a₂ = 0 ∧ Int.fract ((N : ℝ) / a₂) = 0 ∧
    (1 ≤ t → N / a₁ = 2 ∧ N % a₁ = 1 ∧ Int.fract ((N : ℝ) / a₁) = 1 / (a₁ : ℝ)) := by
  dsimp only
  refine ⟨?_, ?_, fun ht => ⟨?_, ?_, ?_⟩⟩
  · rw [show 6 * t + 3 = 3 * (2 * t + 1) by ring, Nat.mul_mod_left]
  · have hmul : ((6 * t + 3 : ℕ) : ℝ) / (2 * t + 1 : ℕ) = ((3 : ℤ) : ℝ) := by
      have : (0 : ℝ) < (2 * t + 1 : ℕ) := by positivity
      push_cast; field_simp; ring
    exact Int.fract_eq_zero_iff.mpr ⟨3, hmul.symm⟩
  · rw [show 6 * t + 3 = 1 + (3 * t + 1) * 2 by ring,
      Nat.add_mul_div_left 1 2 (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  · rw [show 6 * t + 3 = 1 + (3 * t + 1) * 2 by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · have ha₁ : (1 : ℝ) < (3 * t + 1 : ℕ) := by exact_mod_cast (by omega : 1 < 3 * t + 1)
    have hrw : ((6 * t + 3 : ℕ) : ℝ) / (3 * t + 1 : ℕ) =
        1 / ((3 * t + 1 : ℕ) : ℝ) + ((2 : ℤ) : ℝ) := by
      push_cast; field_simp; ring
    rw [hrw, Int.fract_add_intCast, Int.fract_eq_self.mpr]
    exact ⟨by positivity, (div_lt_one (by linarith)).mpr ha₁⟩

/-- **Exact sawtooth phases at the Bézout tripling endpoint `N = 6t + 3` (`2 a₂ = 3 a₁ + 1`).**
At `N = 3 a₁ = 2 a₂ - 1` (`a₁ = 2t + 1`, `a₂ = 3t + 2`), `a₁` is at an exact integer jump
(`{N/a₁} = 0`), while `a₂` has quotient `1`, remainder `a₂ - 1`, and fractional part `(a₂ - 1)/a₂`. -/
theorem sawtooth_phases_at_bezout_tripling_endpoint_right (t : ℕ) :
    let a₁ := 2 * t + 1
    let a₂ := 3 * t + 2
    let N := 6 * t + 3
    N % a₁ = 0 ∧ Int.fract ((N : ℝ) / a₁) = 0 ∧
    N / a₂ = 1 ∧ N % a₂ = a₂ - 1 ∧
    Int.fract ((N : ℝ) / a₂) = ((a₂ - 1 : ℕ) : ℝ) / (a₂ : ℝ) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show 6 * t + 3 = 3 * (2 * t + 1) by ring, Nat.mul_mod_left]
  · have hmul : ((6 * t + 3 : ℕ) : ℝ) / (2 * t + 1 : ℕ) = ((3 : ℤ) : ℝ) := by
      have : (0 : ℝ) < (2 * t + 1 : ℕ) := by positivity
      push_cast; field_simp; ring
    exact Int.fract_eq_zero_iff.mpr ⟨3, hmul.symm⟩
  · rw [show 6 * t + 3 = (3 * t + 1) + (3 * t + 2) * 1 by ring,
      Nat.add_mul_div_left (3 * t + 1) 1 (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  · rw [show 6 * t + 3 = (3 * t + 1) + (3 * t + 2) * 1 by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega
  · have ha₂ : (0 : ℝ) < (3 * t + 2 : ℕ) := by positivity
    have hlt : ((3 * t + 2 - 1 : ℕ) : ℝ) < (3 * t + 2 : ℕ) := by exact_mod_cast (by omega)
    have hrw : ((6 * t + 3 : ℕ) : ℝ) / (3 * t + 2 : ℕ) =
        ((3 * t + 2 - 1 : ℕ) : ℝ) / (3 * t + 2 : ℕ) + ((1 : ℤ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ 3 * t + 2)]
      push_cast; field_simp; ring
    rw [hrw, Int.fract_add_intCast, Int.fract_eq_self.mpr]
    exact ⟨by positivity, (div_lt_one ha₂).mpr hlt⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
