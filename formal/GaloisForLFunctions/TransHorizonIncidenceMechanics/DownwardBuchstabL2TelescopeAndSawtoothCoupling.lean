import GaloisForLFunctions.TransHorizonIncidenceMechanics.TransHorizonGramMatrixAndRadicalProjection
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TransHorizonRoughAbsorptionAndReset
import GaloisForLFunctions.BezoutValuationIncidence.ExactFinitePrefixDiscrepancyDualityAndReturnTimes

/-!
# Pillar XXIV: Downward Buchstab `L²` Telescope, Sawtooth Fractional-Part Coupling, and Scale-Halving Energy Subadditivity (`DownwardBuchstabL2TelescopeAndSawtoothCoupling`)

## 1. Classical Baseline & Honest Classification (`README.md` §2)

- **Closest existing results:**
  - Buchstab's identity for truncated divisor sums $s_{N_2,c}(k) - s_{N_1,c}(k) = \sum_{d \mid k,\, N_1 < d \le N_2} c(d)$;
  - Dirichlet hyperbola / floor-sum identity $\sum_{j=1}^Q s_{N,c}(j) = \sum_{d=1}^N c(d) \lfloor Q / d \rfloor = Q \sum_{d=1}^N \frac{c(d)}{d} - \sum_{d=1}^N c(d) \{Q / d\}$ (Báez-Duarte / Nyman–Beurling sawtooth representation);
  - Finite Cauchy–Schwarz inequality on $[1, Q]$.
- **What classical theories leave unresolved:**
  Dirichlet polarization of $\widetilde{\mathcal{D}}_N(M; c) = \sum_{k=1}^M (s_{N,c}(k)s_{N,c}(k+1) - s_{N,c}(k)^2)$ only shows that unit-shift correlation is bounded by $L^2$ energy $\mathcal{E}_N(M; c) = \sum_{k=1}^M s_{N,c}(k)^2$; it does **not** bound $\mathcal{E}_N(M; c)$ itself in the trans-horizon regime $M > N$.
- **New content in this module (`Candidate new theorem` & `Corollary`):**
  1. **Exact Sub-Horizon Top Closure (`sieveL2PrefixEnergy_moebiusReal_eq_one_of_le`):**
     For every $1 \le M \le N_2$, Möbius inversion forces $s_{N_2,\mu}(k) = \mathbf{1}_{k=1}$ on $[1, M]$, so the top-horizon $L^2$ energy is identically $\mathcal{E}_{N_2}(M; \mu) = 1$ (in particular $\mathcal{E}_M(M; \mu) = 1$).
  2. **Downward Buchstab $L^2$ Telescope (`sieveL2PrefixEnergy_sub_eq_sum_Ico_filter_squarefree`, `sieveL2PrefixEnergy_moebiusReal_eq_one_sub_sum_Ico`):**
     Telescoping downward from the exact sub-horizon value $\mathcal{E}_M(M; \mu) = 1$ at horizon $M$ down to horizon $N \le M$ expresses the trans-horizon $L^2$ energy $\mathcal{E}_N(M; \mu)$ purely in terms of the squarefree horizon steps $n + 1 \in (N, M]$:
     $$\mathcal{E}_N(M; \mu) = 1 - \sum_{\substack{n \in [N, M - 1] \\ \operatorname{Squarefree}(n + 1)}} \bigl(\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu)\bigr).$$
  3. **Prime-Horizon Buchstab–Sawtooth Energy Identity (`sieveL2PrefixEnergy_prime_horizon_sub_eq_sawtooth`, `sieveL2PrefixEnergy_prime_horizon_sub_eq_discrepancy`):**
     At every prime step $p = N + 1$, rough absorption reduces the cross-band inner product to the linear prefix sum $\sum_{j=1}^{\lfloor M/p \rfloor} s_{N,c}(j)$, which equals $\lfloor M/p \rfloor \operatorname{finiteHarmonicSum}(N, c) - \operatorname{sievedFractSum}(N, c, \lfloor M/p \rfloor)$. This couples the $L^2$ energy step directly to the Báez-Duarte fractional-part sum:
     $$\mathcal{E}_{N+1}(M; c) - \mathcal{E}_N(M; c) =
       \left\lfloor \frac{M}{N + 1} \right\rfloor \Bigl(c(N + 1)^2 + 2 c(N + 1) \operatorname{finiteHarmonicSum}(N, c)\Bigr) -
         2 c(N + 1) \operatorname{sievedFractSum}\bigl(N, c, \lfloor M / (N + 1) \rfloor\bigr).$$
  4. **Universal Scale-Halving $L^2$ Energy Subadditivity (`mul_quotient_prime_horizon_step_add_subscale_eq`, `sieveL2PrefixEnergy_le_prime_succ_add_div`, `sieveL2PrefixEnergy_prime_succ_le_add_two_mul_band_add_div`):**
     By an exact division-free completion of the square + finite prefix variance identity on $Q = \lfloor M / (N + 1) \rfloor$,
     $$(Q : \mathbb{R}) \cdot \bigl(\mathcal{E}_{N+1}(M; c) - \mathcal{E}_N(M; c) + \mathcal{E}_N(Q; c)\bigr) =
       \Bigl(c(N + 1) Q + \sum_{j=1}^Q s_{N,c}(j)\Bigr)^2 + \Bigl(Q \cdot \mathcal{E}_N(Q; c) - \Bigl(\sum_{j=1}^Q s_{N,c}(j)\Bigr)^2\Bigr) \ge 0,$$
     yielding the unconditional **Downward Prime-Horizon Subadditivity Inequality**
     $$\mathcal{E}_N(M; c) \le \mathcal{E}_{N+1}(M; c) + \mathcal{E}_N\bigl(\lfloor M / (N + 1) \rfloor; c\bigr)$$
     for **every** prime $p = N + 1$, **every** $M \in \mathbb{N}$, and **every** weight $c : \mathbb{N} \to \mathbb{R}$.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Linear Prefix Sums of `sieveSeq` and Exact Báez-Duarte Sawtooth Coupling -/

/-- Agreement of the linear prefix sum of `sieveSeq N c` on `Finset.Icc 1 Q` with the linear
prefix sum of `sievedDivisorSum N c`. -/
theorem sum_Icc_sieveSeq_eq_sum_sievedDivisorSum (N Q : ℕ) (c : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 Q, sieveSeq N c j) =
      ∑ j ∈ Finset.Icc 1 Q, sievedDivisorSum N c j := by
  refine Finset.sum_congr rfl fun j hj => ?_
  exact sieveSeq_eq_sievedDivisorSum N c (Finset.mem_Icc.mp hj).1

/-- **Linear Prefix Sum Decomposition into Harmonic Drift and Discrepancy
(`sum_Icc_sieveSeq_eq_drift_add_discrepancy`):**
For every horizon $N$, prefix $Q \in \mathbb{N}$, and weight $c : \mathbb{N} \to \mathbb{R}$:
$$\sum_{j=1}^Q s_{N,c}(j) = Q \cdot \operatorname{finiteHarmonicSum}(N, c) + \operatorname{sievePrefixDiscrepancy}(N, Q, c).$$ -/
theorem sum_Icc_sieveSeq_eq_drift_add_discrepancy (N Q : ℕ) (c : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 Q, sieveSeq N c j) =
      (Q : ℝ) * finiteHarmonicSum N c + sievePrefixDiscrepancy N Q c := by
  rw [sum_Icc_sieveSeq_eq_sum_sievedDivisorSum, sievePrefixDiscrepancy_eq_sum_sub_drift]
  ring

/-- **Linear Prefix Sum Decomposition into Harmonic Drift and Báez-Duarte Fractional Sum
(`sum_Icc_sieveSeq_eq_drift_sub_sievedFractSum`):**
For every horizon $N$, prefix $Q \in \mathbb{N}$, and weight $c : \mathbb{N} \to \mathbb{R}$:
$$\sum_{j=1}^Q s_{N,c}(j) = Q \cdot \operatorname{finiteHarmonicSum}(N, c) - \operatorname{sievedFractSum}(N, c, Q).$$ -/
theorem sum_Icc_sieveSeq_eq_drift_sub_sievedFractSum (N Q : ℕ) (c : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 Q, sieveSeq N c j) =
      (Q : ℝ) * finiteHarmonicSum N c - sievedFractSum N c Q := by
  rw [sum_Icc_sieveSeq_eq_drift_add_discrepancy, sievePrefixDiscrepancy_eq_neg_sievedFractSum]
  ring

/-- **Ramanujan Dual Energy Bound on the Báez-Duarte Fractional Sum
(`sievedFractSum_sq_le_variance_mul_dualEnergy`):**
For every horizon $N$, prefix $Q \in \mathbb{N}$, and weight $c : \mathbb{N} \to \mathbb{R}$:
$$\bigl(\operatorname{sievedFractSum}(N, c, Q)\bigr)^2 \le
  \operatorname{sieveVariance}(N, c) \cdot \operatorname{sievePrefixDualEnergy}(N, Q).$$ -/
theorem sievedFractSum_sq_le_variance_mul_dualEnergy (N Q : ℕ) (c : ℕ → ℝ) :
    sievedFractSum N c Q ^ (2 : ℕ) ≤ sieveVariance N c * sievePrefixDualEnergy N Q := by
  have h := sievePrefixDiscrepancy_sq_le_variance_mul_dualEnergy N Q c
  rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum, neg_sq] at h
  exact h

/-! ## §2. Prime-Horizon Buchstab–Sawtooth $L^2$ Energy Step Law -/

/-- Private helper: pointwise single-horizon step of `sieveBandSeq`. -/
private theorem sieveBandSeq_succ_eq_ite' (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    sieveBandSeq N (N + 1) c k = if N + 1 ∣ k then c (N + 1) else 0 := by
  unfold sieveBandSeq sieveSeq
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
  ring

/-- Private helper: quotient bijection for multiples of `d > 0` in `Finset.Icc 1 M`. -/
private theorem sum_Icc_filter_dvd_eq_sum_Icc_div' {d : ℕ} (hd : 0 < d) (M : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ (Finset.Icc 1 M).filter (fun k => d ∣ k), f k) =
      ∑ j ∈ Finset.Icc 1 (M / d), f (d * j) := by
  have hbij : (Finset.Icc 1 M).filter (fun k => d ∣ k) =
      (Finset.Icc 1 (M / d)).image (fun j => d * j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hk1, hkM⟩, ⟨j, rfl⟩⟩
      have hj1 : 1 ≤ j := by
        by_contra h
        have hj0 : j = 0 := by omega
        subst hj0; omega
      exact ⟨j, ⟨hj1, (Nat.le_div_iff_mul_le hd).mpr (by linarith)⟩, rfl⟩
    · rintro ⟨j, ⟨hj1, hjM⟩, rfl⟩
      have hle := (Nat.le_div_iff_mul_le hd).mp hjM
      exact ⟨⟨Nat.mul_pos hd hj1, by linarith⟩, dvd_mul_right d j⟩
  rw [hbij, Finset.sum_image]
  intro j₁ _ j₂ _ hmul
  exact Nat.eq_of_mul_eq_mul_left hd hmul

/-- Private helper: single-horizon $L^2$ step identity. -/
private theorem sieveL2PrefixEnergy_succ_sub_eq' (N M : ℕ) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy (N + 1) M c - sieveL2PrefixEnergy N M c =
      c (N + 1) ^ (2 : ℕ) * ((M / (N + 1) : ℕ) : ℝ) +
        2 * c (N + 1) * ∑ j ∈ Finset.Icc 1 (M / (N + 1)), sieveSeq N c ((N + 1) * j) := by
  have hsq : (∑ k ∈ Finset.Icc 1 M, sieveBandSeq N (N + 1) c k ^ (2 : ℕ)) =
      c (N + 1) ^ (2 : ℕ) * ((M / (N + 1) : ℕ) : ℝ) := by
    have hpt : ∀ k ∈ Finset.Icc 1 M,
        sieveBandSeq N (N + 1) c k ^ (2 : ℕ) =
          if N + 1 ∣ k then c (N + 1) ^ (2 : ℕ) else 0 := by
      intro k _
      rw [sieveBandSeq_succ_eq_ite']
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter,
      sum_Icc_filter_dvd_eq_sum_Icc_div' (Nat.succ_pos N) M (fun _ => c (N + 1) ^ (2 : ℕ)),
      Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_comm]
  have hcov : (∑ k ∈ Finset.Icc 1 M, sieveSeq N c k * sieveBandSeq N (N + 1) c k) =
      c (N + 1) * ∑ j ∈ Finset.Icc 1 (M / (N + 1)), sieveSeq N c ((N + 1) * j) := by
    have hpt : ∀ k ∈ Finset.Icc 1 M,
        sieveSeq N c k * sieveBandSeq N (N + 1) c k =
          if N + 1 ∣ k then c (N + 1) * sieveSeq N c k else 0 := by
      intro k _
      rw [sieveBandSeq_succ_eq_ite']
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter,
      sum_Icc_filter_dvd_eq_sum_Icc_div' (Nat.succ_pos N) M (fun k => c (N + 1) * sieveSeq N c k),
      ← Finset.mul_sum]
  rw [sieveL2PrefixEnergy_horizon_band_sub N (N + 1) M c, hsq, hcov]
  ring

/-- Private helper: prime-horizon $L^2$ step identity. -/
private theorem sieveL2PrefixEnergy_prime_succ_sub_eq' {N : ℕ} (hp : (N + 1).Prime)
    (M : ℕ) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy (N + 1) M c - sieveL2PrefixEnergy N M c =
      c (N + 1) ^ (2 : ℕ) * ((M / (N + 1) : ℕ) : ℝ) +
        2 * c (N + 1) * ∑ j ∈ Finset.Icc 1 (M / (N + 1)), sieveSeq N c j := by
  have hrough : IsTransHorizonRough N (N + 1) :=
    isTransHorizonRough_of_prime_gt hp (Nat.lt_succ_self N)
  rw [sieveL2PrefixEnergy_succ_sub_eq']
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, sieveSeq_mul_of_isTransHorizonRough hrough c j]

/-- **Prime-Horizon Buchstab–Sawtooth $L^2$ Energy Step Identity
(`sieveL2PrefixEnergy_prime_horizon_sub_eq_sawtooth`):**
Whenever $p = N + 1$ is prime, for every prefix $M \in \mathbb{N}$ and weight $c : \mathbb{N} \to \mathbb{R}$,
the $L^2$ energy step across $p = N + 1$ decomposes into the harmonic drift term and the
Báez-Duarte fractional-part sum at the quotient scale $Q = \lfloor M / (N + 1) \rfloor$:
$$\mathcal{E}_{N+1}(M; c) - \mathcal{E}_N(M; c) =
  \left\lfloor \frac{M}{N + 1} \right\rfloor \Bigl(c(N + 1)^2 + 2 c(N + 1) \operatorname{finiteHarmonicSum}(N, c)\Bigr) -
    2 c(N + 1) \operatorname{sievedFractSum}\bigl(N, c, \lfloor M / (N + 1) \rfloor\bigr).$$ -/
theorem sieveL2PrefixEnergy_prime_horizon_sub_eq_sawtooth {N : ℕ} (hp : (N + 1).Prime)
    (M : ℕ) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy (N + 1) M c - sieveL2PrefixEnergy N M c =
      ((M / (N + 1) : ℕ) : ℝ) * (c (N + 1) ^ (2 : ℕ) + 2 * c (N + 1) * finiteHarmonicSum N c) -
        2 * c (N + 1) * sievedFractSum N c (M / (N + 1)) := by
  rw [sieveL2PrefixEnergy_prime_succ_sub_eq' hp M c,
    sum_Icc_sieveSeq_eq_drift_sub_sievedFractSum N (M / (N + 1)) c]
  ring

/-- **Prime-Horizon Buchstab–Discrepancy $L^2$ Energy Step Identity
(`sieveL2PrefixEnergy_prime_horizon_sub_eq_discrepancy`):**
Whenever $p = N + 1$ is prime, for every prefix $M \in \mathbb{N}$ and weight $c : \mathbb{N} \to \mathbb{R}$:
$$\mathcal{E}_{N+1}(M; c) - \mathcal{E}_N(M; c) =
  \left\lfloor \frac{M}{N + 1} \right\rfloor \Bigl(c(N + 1)^2 + 2 c(N + 1) \operatorname{finiteHarmonicSum}(N, c)\Bigr) +
    2 c(N + 1) \operatorname{sievePrefixDiscrepancy}\bigl(N, \lfloor M / (N + 1) \rfloor, c\bigr).$$ -/
theorem sieveL2PrefixEnergy_prime_horizon_sub_eq_discrepancy {N : ℕ} (hp : (N + 1).Prime)
    (M : ℕ) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy (N + 1) M c - sieveL2PrefixEnergy N M c =
      ((M / (N + 1) : ℕ) : ℝ) * (c (N + 1) ^ (2 : ℕ) + 2 * c (N + 1) * finiteHarmonicSum N c) +
        2 * c (N + 1) * sievePrefixDiscrepancy N (M / (N + 1)) c := by
  rw [sieveL2PrefixEnergy_prime_succ_sub_eq' hp M c,
    sum_Icc_sieveSeq_eq_drift_add_discrepancy N (M / (N + 1)) c]
  ring

/-! ## §3. Scale-Halving Cauchy–Schwarz Variance Identity & Universal Prime-Horizon Subadditivity -/

/-- **Division-Free Finite Prefix Cauchy–Schwarz Variance Identity
(`sum_Icc_mul_sub_sum_sq_eq`):**
For every $Q \in \mathbb{N}$ and function $f : \mathbb{N} \to \mathbb{R}$:
$$\sum_{j=1}^Q \Bigl((Q : \mathbb{R}) \cdot f(j) - \sum_{i=1}^Q f(i)\Bigr)^2 =
  (Q : \mathbb{R}) \cdot \Bigl((Q : \mathbb{R}) \cdot \sum_{j=1}^Q f(j)^2 - \Bigl(\sum_{j=1}^Q f(j)\Bigr)^2\Bigr).$$ -/
theorem sum_Icc_mul_sub_sum_sq_eq (Q : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 Q,
        ((Q : ℝ) * f j - ∑ i ∈ Finset.Icc 1 Q, f i) ^ (2 : ℕ)) =
      (Q : ℝ) * ((Q : ℝ) * (∑ j ∈ Finset.Icc 1 Q, f j ^ (2 : ℕ)) -
        (∑ j ∈ Finset.Icc 1 Q, f j) ^ (2 : ℕ)) := by
  set S : ℝ := ∑ i ∈ Finset.Icc 1 Q, f i
  have hpt : ∀ j ∈ Finset.Icc 1 Q,
      ((Q : ℝ) * f j - S) ^ (2 : ℕ) =
        (Q : ℝ) ^ (2 : ℕ) * f j ^ (2 : ℕ) - (2 * (Q : ℝ) * S) * f j + S ^ (2 : ℕ) := by
    intro j _
    ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul]
  change (Q : ℝ) ^ (2 : ℕ) * (∑ j ∈ Finset.Icc 1 Q, f j ^ (2 : ℕ)) -
    2 * (Q : ℝ) * S * S + (Q : ℝ) * S ^ (2 : ℕ) =
    (Q : ℝ) * ((Q : ℝ) * (∑ j ∈ Finset.Icc 1 Q, f j ^ (2 : ℕ)) - S ^ (2 : ℕ))
  ring

/-- **Finite Prefix Cauchy–Schwarz Inequality for `sieveSeq`
(`sq_sum_Icc_sieveSeq_le_mul_sieveL2PrefixEnergy`):**
For every horizon $N$, prefix $Q \in \mathbb{N}$, and weight $c : \mathbb{N} \to \mathbb{R}$:
$$\Bigl(\sum_{j=1}^Q s_{N,c}(j)\Bigr)^2 \le (Q : \mathbb{R}) \cdot \mathcal{E}_N(Q; c).$$ -/
theorem sq_sum_Icc_sieveSeq_le_mul_sieveL2PrefixEnergy (N Q : ℕ) (c : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 Q, sieveSeq N c j) ^ (2 : ℕ) ≤
      (Q : ℝ) * sieveL2PrefixEnergy N Q c := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp [sieveL2PrefixEnergy]
  · have hQ_pos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
    have hnonneg : 0 ≤ ∑ j ∈ Finset.Icc 1 Q,
        ((Q : ℝ) * sieveSeq N c j - ∑ i ∈ Finset.Icc 1 Q, sieveSeq N c i) ^ (2 : ℕ) :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [sum_Icc_mul_sub_sum_sq_eq Q (sieveSeq N c)] at hnonneg
    unfold sieveL2PrefixEnergy
    have hpos_diff : 0 ≤ (Q : ℝ) * (∑ j ∈ Finset.Icc 1 Q, sieveSeq N c j ^ (2 : ℕ)) -
        (∑ j ∈ Finset.Icc 1 Q, sieveSeq N c j) ^ (2 : ℕ) :=
      nonneg_of_mul_nonneg_right hnonneg hQ_pos
    linarith

/-- **Exact Square-Completion Identity for the Prime-Horizon $L^2$ Energy Step
(`mul_quotient_prime_horizon_step_add_subscale_eq`):**
For every prime $p = N + 1$, prefix $M \in \mathbb{N}$ with quotient $Q = \lfloor M / (N + 1) \rfloor$,
and weight $c : \mathbb{N} \to \mathbb{R}$:
$$(Q : \mathbb{R}) \cdot \bigl(\mathcal{E}_{N+1}(M; c) - \mathcal{E}_N(M; c) + \mathcal{E}_N(Q; c)\bigr) =
  \Bigl(c(N + 1) \cdot (Q : \mathbb{R}) + \sum_{j=1}^Q s_{N,c}(j)\Bigr)^2 +
    \Bigl((Q : \mathbb{R}) \cdot \mathcal{E}_N(Q; c) - \Bigl(\sum_{j=1}^Q s_{N,c}(j)\Bigr)^2\Bigr).$$ -/
theorem mul_quotient_prime_horizon_step_add_subscale_eq {N : ℕ} (hp : (N + 1).Prime)
    (M : ℕ) (c : ℕ → ℝ) :
    ((M / (N + 1) : ℕ) : ℝ) *
        (sieveL2PrefixEnergy (N + 1) M c - sieveL2PrefixEnergy N M c +
          sieveL2PrefixEnergy N (M / (N + 1)) c) =
      (c (N + 1) * ((M / (N + 1) : ℕ) : ℝ) +
          ∑ j ∈ Finset.Icc 1 (M / (N + 1)), sieveSeq N c j) ^ (2 : ℕ) +
        (((M / (N + 1) : ℕ) : ℝ) * sieveL2PrefixEnergy N (M / (N + 1)) c -
          (∑ j ∈ Finset.Icc 1 (M / (N + 1)), sieveSeq N c j) ^ (2 : ℕ)) := by
  rw [sieveL2PrefixEnergy_prime_succ_sub_eq' hp M c]
  ring

/-- **Universal Downward Prime-Horizon $L^2$ Energy Subadditivity
(`sieveL2PrefixEnergy_le_prime_succ_add_div`):**
For **every** prime $p = N + 1$, **every** prefix $M \in \mathbb{N}$, and **every** weight
$c : \mathbb{N} \to \mathbb{R}$:
$$\mathcal{E}_N(M; c) \le \mathcal{E}_{N+1}(M; c) + \mathcal{E}_N\bigl(\lfloor M / (N + 1) \rfloor; c\bigr).$$ -/
theorem sieveL2PrefixEnergy_le_prime_succ_add_div {N : ℕ} (hp : (N + 1).Prime)
    (M : ℕ) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy N M c ≤
      sieveL2PrefixEnergy (N + 1) M c + sieveL2PrefixEnergy N (M / (N + 1)) c := by
  rcases Nat.eq_zero_or_pos (M / (N + 1)) with hQ0 | hQpos
  · have hstep := sieveL2PrefixEnergy_prime_succ_sub_eq' hp M c
    rw [hQ0] at hstep ⊢
    simp [sieveL2PrefixEnergy] at hstep ⊢
    linarith
  · have hQ_real : (0 : ℝ) < ((M / (N + 1) : ℕ) : ℝ) := Nat.cast_pos.mpr hQpos
    have hid := mul_quotient_prime_horizon_step_add_subscale_eq hp M c
    have hcs := sq_sum_Icc_sieveSeq_le_mul_sieveL2PrefixEnergy N (M / (N + 1)) c
    have hsq : 0 ≤ (c (N + 1) * ((M / (N + 1) : ℕ) : ℝ) +
        ∑ j ∈ Finset.Icc 1 (M / (N + 1)), sieveSeq N c j) ^ (2 : ℕ) := sq_nonneg _
    have hprod_nonneg : 0 ≤ ((M / (N + 1) : ℕ) : ℝ) *
        (sieveL2PrefixEnergy (N + 1) M c - sieveL2PrefixEnergy N M c +
          sieveL2PrefixEnergy N (M / (N + 1)) c) := by linarith
    have hnonneg := nonneg_of_mul_nonneg_right hprod_nonneg hQ_real
    linarith

/-- **Universal Upward Prime-Horizon $L^2$ Energy Step Bound
(`sieveL2PrefixEnergy_prime_succ_le_add_two_mul_band_add_div`):**
For **every** prime $p = N + 1$, **every** prefix $M \in \mathbb{N}$, and **every** weight
$c : \mathbb{N} \to \mathbb{R}$:
$$\mathcal{E}_{N+1}(M; c) \le \mathcal{E}_N(M; c) +
  2 c(N + 1)^2 \left\lfloor \frac{M}{N + 1} \right\rfloor +
    \mathcal{E}_N\bigl(\lfloor M / (N + 1) \rfloor; c\bigr).$$ -/
theorem sieveL2PrefixEnergy_prime_succ_le_add_two_mul_band_add_div {N : ℕ} (hp : (N + 1).Prime)
    (M : ℕ) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy (N + 1) M c ≤
      sieveL2PrefixEnergy N M c +
        2 * c (N + 1) ^ (2 : ℕ) * ((M / (N + 1) : ℕ) : ℝ) +
          sieveL2PrefixEnergy N (M / (N + 1)) c := by
  rcases Nat.eq_zero_or_pos (M / (N + 1)) with hQ0 | hQpos
  · have hstep := sieveL2PrefixEnergy_prime_succ_sub_eq' hp M c
    rw [hQ0] at hstep ⊢
    simp [sieveL2PrefixEnergy] at hstep ⊢
    linarith
  · have hQ_real : (0 : ℝ) < ((M / (N + 1) : ℕ) : ℝ) := Nat.cast_pos.mpr hQpos
    have hid : ((M / (N + 1) : ℕ) : ℝ) *
        (2 * c (N + 1) ^ (2 : ℕ) * ((M / (N + 1) : ℕ) : ℝ) +
          sieveL2PrefixEnergy N (M / (N + 1)) c -
          (sieveL2PrefixEnergy (N + 1) M c - sieveL2PrefixEnergy N M c)) =
      (c (N + 1) * ((M / (N + 1) : ℕ) : ℝ) -
          ∑ j ∈ Finset.Icc 1 (M / (N + 1)), sieveSeq N c j) ^ (2 : ℕ) +
        (((M / (N + 1) : ℕ) : ℝ) * sieveL2PrefixEnergy N (M / (N + 1)) c -
          (∑ j ∈ Finset.Icc 1 (M / (N + 1)), sieveSeq N c j) ^ (2 : ℕ)) := by
      rw [sieveL2PrefixEnergy_prime_succ_sub_eq' hp M c]
      ring
    have hcs := sq_sum_Icc_sieveSeq_le_mul_sieveL2PrefixEnergy N (M / (N + 1)) c
    have hsq : 0 ≤ (c (N + 1) * ((M / (N + 1) : ℕ) : ℝ) -
        ∑ j ∈ Finset.Icc 1 (M / (N + 1)), sieveSeq N c j) ^ (2 : ℕ) := sq_nonneg _
    have hprod_nonneg : 0 ≤ ((M / (N + 1) : ℕ) : ℝ) *
        (2 * c (N + 1) ^ (2 : ℕ) * ((M / (N + 1) : ℕ) : ℝ) +
          sieveL2PrefixEnergy N (M / (N + 1)) c -
          (sieveL2PrefixEnergy (N + 1) M c - sieveL2PrefixEnergy N M c)) := by linarith
    have hnonneg := nonneg_of_mul_nonneg_right hprod_nonneg hQ_real
    linarith

/-! ## §4. Downward Buchstab $L^2$ Telescope from the Sub-Horizon Top ($N_2 = M \to N_1 = N$) -/

/-- **Horizon-Band $L^2$ Energy Telescope (`sieveL2PrefixEnergy_sub_eq_sum_Ico_succ_sub`):**
For every $N_1 \le N_2$, prefix $M \in \mathbb{N}$, and weight $c : \mathbb{N} \to \mathbb{R}$:
$$\mathcal{E}_{N_2}(M; c) - \mathcal{E}_{N_1}(M; c) =
  \sum_{n \in \operatorname{Ico} N_1 N_2} \bigl(\mathcal{E}_{n+1}(M; c) - \mathcal{E}_n(M; c)\bigr).$$ -/
theorem sieveL2PrefixEnergy_sub_eq_sum_Ico_succ_sub {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂)
    (M : ℕ) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy N₂ M c - sieveL2PrefixEnergy N₁ M c =
      ∑ n ∈ Finset.Ico N₁ N₂,
        (sieveL2PrefixEnergy (n + 1) M c - sieveL2PrefixEnergy n M c) := by
  induction N₂, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ← ih]
    ring

/-- **Squarefree-Filtered Horizon-Band $L^2$ Energy Telescope
(`sieveL2PrefixEnergy_sub_eq_sum_Ico_filter_squarefree`):**
For every squarefree-supported weight $c : \mathbb{N} \to \mathbb{R}$ and $N_1 \le N_2$,
non-squarefree horizon steps $n + 1$ contribute zero to the $L^2$ energy telescope:
$$\mathcal{E}_{N_2}(M; c) - \mathcal{E}_{N_1}(M; c) =
  \sum_{n \in (\operatorname{Ico} N_1 N_2).\text{filter}(\text{fun } n \Rightarrow \operatorname{Squarefree}(n + 1))}
    \bigl(\mathcal{E}_{n+1}(M; c) - \mathcal{E}_n(M; c)\bigr).$$ -/
theorem sieveL2PrefixEnergy_sub_eq_sum_Ico_filter_squarefree {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂)
    (M : ℕ) {c : ℕ → ℝ} (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) :
    sieveL2PrefixEnergy N₂ M c - sieveL2PrefixEnergy N₁ M c =
      ∑ n ∈ (Finset.Ico N₁ N₂).filter (fun n => Squarefree (n + 1)),
        (sieveL2PrefixEnergy (n + 1) M c - sieveL2PrefixEnergy n M c) := by
  rw [sieveL2PrefixEnergy_sub_eq_sum_Ico_succ_sub hN M c, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hsq : Squarefree (n + 1)
  · simp [hsq]
  · simp only [hsq, if_false]
    rw [sieveL2PrefixEnergy_succ_sub_eq', hc (n + 1) hsq]
    ring

/-- **Sub-Horizon Top Closure for `moebiusReal` (`sieveL2PrefixEnergy_moebiusReal_eq_one_of_le`):**
Whenever $1 \le M \le N_2$, Möbius inversion annihilates $s_{N_2,\mu}(k)$ for all $2 \le k \le M$
and sets $s_{N_2,\mu}(1) = 1$, so the prefix $L^2$ energy is identically $1$:
$$\mathcal{E}_{N_2}(M; \mu) = 1.$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_eq_one_of_le {N₂ M : ℕ}
    (hM1 : 1 ≤ M) (hMN : M ≤ N₂) :
    sieveL2PrefixEnergy N₂ M moebiusReal = 1 := by
  unfold sieveL2PrefixEnergy
  have hpt : ∀ k ∈ Finset.Icc 1 M,
      sieveSeq N₂ moebiusReal k ^ (2 : ℕ) = sieveSeq N₂ moebiusReal k := by
    intro k hk
    obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
    rw [sieveSeq_moebiusReal_eq_ite_of_le hk1 (hkM.trans hMN)]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hpt]
  exact sum_sieveSeq_moebiusReal_eq_one_of_le hM1 hMN

/-- **Exact Trans-Horizon Downward Buchstab $L^2$ Formula for `moebiusReal`
(`sieveL2PrefixEnergy_moebiusReal_eq_one_sub_sum_Ico`):**
For every trans-horizon pair $N \le M$ with $1 \le M$, the trans-horizon $L^2$ energy
$\mathcal{E}_N(M; \mu) = \sum_{k=1}^M s_{N,\mu}(k)^2$ equals $1$ minus the sum of squarefree
horizon steps from $N$ up to $M$:
$$\mathcal{E}_N(M; \mu) = 1 -
  \sum_{n \in (\operatorname{Ico} N M).\text{filter}(\text{fun } n \Rightarrow \operatorname{Squarefree}(n + 1))}
    \bigl(\mathcal{E}_{n+1}(M; \mu) - \mathcal{E}_n(M; \mu)\bigr).$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_eq_one_sub_sum_Ico {N M : ℕ}
    (hM1 : 1 ≤ M) (hNM : N ≤ M) :
    sieveL2PrefixEnergy N M moebiusReal =
      1 - ∑ n ∈ (Finset.Ico N M).filter (fun n => Squarefree (n + 1)),
        (sieveL2PrefixEnergy (n + 1) M moebiusReal - sieveL2PrefixEnergy n M moebiusReal) := by
  have htele := sieveL2PrefixEnergy_sub_eq_sum_Ico_filter_squarefree
    hNM M moebiusReal_eq_zero_of_not_squarefree
  rw [sieveL2PrefixEnergy_moebiusReal_eq_one_of_le hM1 le_rfl] at htele
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
