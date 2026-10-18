import GaloisForLFunctions.RHTower.CHMDPrimeChainVariance
import GaloisForLFunctions.BezoutValuationIncidence.PowerDampedRenormalizedDefectAndPronicCeiling

/-!
# Pillar XII: All-Horizon Prime-Chain Renormalization, Excited-Shell Collapse, and `CHMDPrimeChain` Spectral Cutoff (`PrimeChainSieveBridgeAndSpectralCutoff`)

To unify the discrete trans-horizon sieve mechanics on `ℕ` with the continuous/bipartite
prime-chain variance operator `RHTower.CHMDPrimeChain.varianceEnergy` on the Hilbert-space graph,
this twelfth foundational pillar of **Trans-Horizon Arithmetic–Archimedean Incidence Mechanics**
evaluates the action of `CHMDPrimeChain` directly on the truncated sieve profile
`m ↦ sieveSeq H c m` across all scales `N, m ≫ H`:

## Core Main Theorems (100% Unconditional)

1. **All-Horizon Prime-Chain Renormalization Identity
   (`sieveSeq_prime_mul_sub_eq_sieveSeq_div`)**:
   For **every** sieve horizon `H : ℕ`, weight `c : ℕ → ℝ`, prime `p`, and chain base `b : ℕ`
   coprime to `p` (`Nat.Coprime p b`, in particular `b = ordCompl[p] m` for any `m ≠ 0`), stepping
   from the chain ground state `b` to `p * b` at horizon `H` equals the dilated-weight sieve at the
   rescaled horizon `H / p`:
   $$\operatorname{sieveSeq}(H, c, p \cdot b) - \operatorname{sieveSeq}(H, c, b) =
     \operatorname{sieveSeq}\bigl(H / p,\, (\text{fun } d \Rightarrow c(p \cdot d)),\, b\bigr).$$
   This identity holds unconditionally at **every** trans-horizon scale `b ≫ H`.

2. **Exact Spectral Low-Pass Cutoff of `CHMDPrimeChain` for Primes `p > H`
   (`sieveSeq_eq_ordCompl_of_prime_gt`,
   `sieveSeq_eq_of_same_chain_of_prime_gt`,
   `bipartiteEnergy_chain_sieveSeq_eq_zero_of_prime_gt`,
   `varianceEnergy_chain_sieveSeq_eq_zero_of_prime_gt`)**:
   Whenever a prime `p` exceeds the sieve horizon (`H < p`), `H / p = 0`, so every node `m` on a
   `p`-adic chain satisfies `sieveSeq H c m = sieveSeq H c (ordCompl[p] m)`. Consequently, for
   **every** product index `N : ℕ`, chain base `b : ℕ`, logarithmic cut `u : ℝ`, and weight
   `c : ℕ → ℝ`, the complete bipartite prime-chain variance of `sieveSeq H c` vanishes identically
   for all primes `p > H`:
   $$\operatorname{bipartiteEnergy}\bigl(\operatorname{chainLeft}(N, p, b, u),\,
       \operatorname{chainRight}(N, p, b, u),\, \operatorname{sieveSeq}(H, c)\bigr) = 0,$$
   $$\operatorname{varianceEnergy}\bigl(\operatorname{chainLeft}(N, p, b, u),\,
       \operatorname{chainRight}(N, p, b, u),\, \operatorname{sieveSeq}(H, c)\bigr) = 0.$$

3. **All-Horizon Two-Level Excited-Shell Collapse on Sub-Horizon Prime Chains (`p ≤ H`)
   (`sieveSeq_eq_prime_mul_ordCompl_of_dvd_of_squarefree_support`,
   `sieveSeq_eq_of_same_chain_of_dvd_of_squarefree_support`,
   `sieveSeq_sub_ordCompl_eq_sieveSeq_div_of_dvd_of_squarefree_support`)**:
   For **every** squarefree-supported weight `c : ℕ → ℝ` (including `moebiusReal` and
   `pmPowerDampedRealWeight ε`), **every** horizon `H : ℕ`, and **every** prime `p`:
   - Every excited node `m ≠ 0` on the `p`-chain (`p ∣ m`) collapses to the first excited level
     `p * ordCompl[p] m`:
     $$\operatorname{sieveSeq}(H, c, m) = \operatorname{sieveSeq}\bigl(H, c, p \cdot \operatorname{ordCompl}_p(m)\bigr).$$
   - Therefore, all excited-to-excited jumps `p^r b ↔ p^s b` (`r, s ≥ 1`) along the `p`-chain vanish
     identically at every horizon `H`, and every ground-to-excited jump `b ↔ p^r b` (`r ≥ 1`) equals
     the exact renormalized `(H / p)`-sieve value:
     $$\operatorname{sieveSeq}(H, c, m) - \operatorname{sieveSeq}\bigl(H, c, \operatorname{ordCompl}_p(m)\bigr) =
       \operatorname{sieveSeq}\bigl(H / p,\, (\text{fun } d \Rightarrow c(p \cdot d)),\, \operatorname{ordCompl}_p(m)\bigr).$$
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve RHTower.CHMDPrimeChain
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. All-Horizon Prime-Chain Renormalization Identity (`H ↦ H / p`) -/

/-- For a prime `p` and `b` with `Nat.Coprime p b`, the sub-horizon divisors of `p * b` not
divisible by `p` coincide with the sub-horizon divisors of `b`. -/
theorem filter_dvd_prime_mul_not_dvd_eq {H p b : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p b) :
    ((Finset.Icc 1 H).filter (fun s => s ∣ p * b)).filter (fun s => ¬ p ∣ s) =
      (Finset.Icc 1 H).filter (fun s => s ∣ b) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hs1, hsH⟩, hspb⟩, hnp⟩
    have hcop_sp : Nat.Coprime s p := (hp.coprime_iff_not_dvd.mpr hnp).symm
    exact ⟨⟨hs1, hsH⟩, hcop_sp.dvd_of_dvd_mul_left hspb⟩
  · rintro ⟨⟨hs1, hsH⟩, hsb⟩
    have hnp : ¬ p ∣ s := by
      intro hps
      exact (hp.coprime_iff_not_dvd.mp hcop) (hps.trans hsb)
    exact ⟨⟨⟨hs1, hsH⟩, dvd_mul_of_dvd_right hsb p⟩, hnp⟩

/-- For a prime `p`, summing `c s` over sub-horizon divisors `s ∈ [1, H]` of `p * b` divisible by `p`
equals `sieveSeq (H / p) (fun d => c (p * d)) b`. -/
theorem sum_filter_dvd_prime_mul_dvd_eq_sieveSeq_div (H : ℕ) {p b : ℕ} (hp : p.Prime)
    (c : ℕ → ℝ) :
    (∑ s ∈ ((Finset.Icc 1 H).filter (fun s => s ∣ p * b)).filter (fun s => p ∣ s), c s) =
      sieveSeq (H / p) (fun d => c (p * d)) b := by
  unfold sieveSeq
  symm
  refine Finset.sum_bij (fun d _ => p * d) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
    obtain ⟨⟨hd1, hdH⟩, hdb⟩ := hd
    have hp_pos : 0 < p := hp.pos
    have hpd_le : p * d ≤ H := by
      rw [mul_comm]
      exact (Nat.le_div_iff_mul_le hp_pos).mp hdH
    exact ⟨⟨⟨Nat.mul_pos hp_pos hd1, hpd_le⟩, mul_dvd_mul_left p hdb⟩, dvd_mul_right p d⟩
  · intro d₁ _ d₂ _ heq
    exact Nat.eq_of_mul_eq_mul_left hp.pos heq
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_Icc] at hs
    obtain ⟨⟨⟨hs1, hsH⟩, hspb⟩, hps⟩ := hs
    refine ⟨s / p, ?_, Nat.mul_div_cancel' hps⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hp_pos : 0 < p := hp.pos
    have hps_eq : p * (s / p) = s := Nat.mul_div_cancel' hps
    have hd_pos : 1 ≤ s / p := by
      rcases Nat.eq_zero_or_pos (s / p) with h0 | hpos
      · rw [h0, mul_zero] at hps_eq
        omega
      · exact hpos
    have hd_le : s / p ≤ H / p := Nat.div_le_div_right hsH
    have hd_dvd : s / p ∣ b := by
      rw [← hps_eq] at hspb
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp hspb
    exact ⟨⟨hd_pos, hd_le⟩, hd_dvd⟩
  · intro d _
    rfl

/-- **All-Horizon Prime-Chain Renormalization Identity (`sieveSeq_prime_mul_sub_eq_sieveSeq_div`):**
For every sieve horizon `H : ℕ`, weight `c : ℕ → ℝ`, prime `p`, and `b : ℕ` coprime to `p`:
`sieveSeq H c (p * b) - sieveSeq H c b = sieveSeq (H / p) (fun d => c (p * d)) b`. -/
theorem sieveSeq_prime_mul_sub_eq_sieveSeq_div (H : ℕ) {p b : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p b) (c : ℕ → ℝ) :
    sieveSeq H c (p * b) - sieveSeq H c b =
      sieveSeq (H / p) (fun d => c (p * d)) b := by
  have hsplit := (Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 H).filter (fun s => s ∣ p * b)) (fun s => p ∣ s) c).symm
  rw [filter_dvd_prime_mul_not_dvd_eq hp hcop,
    sum_filter_dvd_prime_mul_dvd_eq_sieveSeq_div H hp c] at hsplit
  change sieveSeq H c (p * b) - sieveSeq H c b = _
  unfold sieveSeq at hsplit ⊢
  linarith

/-! ## §2. Exact Spectral Low-Pass Cutoff of `CHMDPrimeChain` Above the Sieve Horizon (`p > H`) -/

/-- When `H < p` for a prime `p`, `sieveSeq H c (p ^ r * b) = sieveSeq H c b` for all `r, b : ℕ`. -/
theorem sieveSeq_prime_pow_mul_eq_of_prime_gt {H p : ℕ} (hp : p.Prime) (hpH : H < p)
    (c : ℕ → ℝ) (r b : ℕ) :
    sieveSeq H c (p ^ r * b) = sieveSeq H c b := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hrew : p ^ (r + 1) * b = (p ^ r * b) * p := by
      rw [pow_succ, mul_right_comm]
    rw [hrew]
    have hfilt : (Finset.Icc 1 H).filter (fun d => d ∣ (p ^ r * b) * p) =
        (Finset.Icc 1 H).filter (fun d => d ∣ p ^ r * b) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hd1, hdH⟩, hdvd⟩
        have hnp : ¬ p ∣ d := fun hpd => by
          have := Nat.le_of_dvd hd1 hpd
          omega
        exact ⟨⟨hd1, hdH⟩, (hp.coprime_iff_not_dvd.mpr hnp).symm.dvd_of_dvd_mul_right hdvd⟩
      · rintro ⟨⟨hd1, hdH⟩, hdvd⟩
        exact ⟨⟨hd1, hdH⟩, dvd_mul_of_dvd_left hdvd p⟩
    unfold sieveSeq at ih ⊢
    rw [hfilt, ih]

/-- **Trans-Horizon Prime-Chain Constancy (`sieveSeq_eq_ordCompl_of_prime_gt`):**
For every prime `p > H`, weight `c : ℕ → ℝ`, and `m : ℕ`:
`sieveSeq H c m = sieveSeq H c (ordCompl[p] m)`. -/
theorem sieveSeq_eq_ordCompl_of_prime_gt {H p : ℕ} (hp : p.Prime) (hpH : H < p)
    (c : ℕ → ℝ) (m : ℕ) :
    sieveSeq H c m = sieveSeq H c (ordCompl[p] m) := by
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self m p]
  exact sieveSeq_prime_pow_mul_eq_of_prime_gt hp hpH c (m.factorization p) (ordCompl[p] m)

/-- Any two integers `m, k` on the same `p`-adic chain (`ordCompl[p] m = ordCompl[p] k`) for a prime
`p > H` have identical `H`-sieve values: `sieveSeq H c m = sieveSeq H c k`. -/
theorem sieveSeq_eq_of_same_chain_of_prime_gt {H p m k : ℕ} (hp : p.Prime) (hpH : H < p)
    (hchain : ordCompl[p] m = ordCompl[p] k) (c : ℕ → ℝ) :
    sieveSeq H c m = sieveSeq H c k := by
  rw [sieveSeq_eq_ordCompl_of_prime_gt hp hpH c m,
    sieveSeq_eq_ordCompl_of_prime_gt hp hpH c k, hchain]

/-- **Exact Spectral Low-Pass Cutoff of `CHMDPrimeChain.bipartiteEnergy` (`p > H`)
(`bipartiteEnergy_chain_sieveSeq_eq_zero_of_prime_gt`):**
For every horizon `H : ℕ`, prime `p > H`, product index `N : ℕ`, chain base `b : ℕ`, cut `u : ℝ`,
and weight `c : ℕ → ℝ`, the bipartite prime-chain energy of `sieveSeq H c` vanishes identically:
`bipartiteEnergy (chainLeft N p b u) (chainRight N p b u) (sieveSeq H c) = 0`. -/
theorem bipartiteEnergy_chain_sieveSeq_eq_zero_of_prime_gt {H p : ℕ} (hp : p.Prime)
    (hpH : H < p) (N b : ℕ) (u : ℝ) (c : ℕ → ℝ) :
    bipartiteEnergy (chainLeft N p b u) (chainRight N p b u) (sieveSeq H c) = 0 := by
  unfold bipartiteEnergy
  refine Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun k hk => ?_
  unfold chainLeft at hm
  unfold chainRight at hk
  simp only [Finset.mem_filter] at hm hk
  have hchain : ordCompl[p] m = ordCompl[p] k := hm.2.1.trans hk.2.1.symm
  rw [sieveSeq_eq_of_same_chain_of_prime_gt hp hpH hchain c, sub_self, sq, mul_zero]

/-- **Exact Spectral Low-Pass Cutoff of `CHMDPrimeChain.varianceEnergy` (`p > H`)
(`varianceEnergy_chain_sieveSeq_eq_zero_of_prime_gt`):**
For every horizon `H : ℕ`, prime `p > H`, product index `N : ℕ`, chain base `b : ℕ`, cut `u : ℝ`,
and weight `c : ℕ → ℝ`:
`varianceEnergy (chainLeft N p b u) (chainRight N p b u) (sieveSeq H c) = 0`. -/
theorem varianceEnergy_chain_sieveSeq_eq_zero_of_prime_gt {H p : ℕ} (hp : p.Prime)
    (hpH : H < p) (N b : ℕ) (u : ℝ) (c : ℕ → ℝ) :
    varianceEnergy (chainLeft N p b u) (chainRight N p b u) (sieveSeq H c) = 0 := by
  rw [← bipartiteEnergy_eq_variance]
  exact bipartiteEnergy_chain_sieveSeq_eq_zero_of_prime_gt hp hpH N b u c

/-! ## §3. All-Horizon Two-Level Excited-Shell Collapse on Sub-Horizon Prime Chains (`p ≤ H`) -/

/-- Local helper: if `s` is squarefree and `d ∣ k`, then `s ∣ d * k ↔ s ∣ k`. -/
private theorem dvd_mul_iff_of_squarefree {s d k : ℕ} (hs : Squarefree s) (hdk : d ∣ k) :
    s ∣ d * k ↔ s ∣ k := by
  constructor
  · intro hsd
    by_cases hk0 : k = 0
    · subst hk0; exact dvd_zero s
    · have hs_pos : 0 < s := hs.ne_zero.bot_lt
      let g := Nat.gcd s k
      have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left k hs_pos
      have hgd_s : g ∣ s := Nat.gcd_dvd_left s k
      have hgd_k : g ∣ k := Nat.gcd_dvd_right s k
      have hs_eq : g * (s / g) = s := Nat.mul_div_cancel' hgd_s
      have hk_eq : g * (k / g) = k := Nat.mul_div_cancel' hgd_k
      have hsq_mul : Squarefree (g * (s / g)) := by rw [hs_eq]; exact hs
      have hcop_g : Nat.Coprime (s / g) g := (Nat.coprime_of_squarefree_mul hsq_mul).symm
      have hcop_kg : Nat.Coprime (s / g) (k / g) := Nat.coprime_div_gcd_div_gcd hg_pos
      have hcop_k : Nat.Coprime (s / g) k := by rw [← hk_eq]; exact hcop_g.mul_right hcop_kg
      have hcop_kk : Nat.Coprime (s / g) (k * k) := hcop_k.mul_right hcop_k
      have hdiv_kk : (s / g) ∣ k * k :=
        (Nat.div_dvd_of_dvd hgd_s).trans (hsd.trans (Nat.mul_dvd_mul_right hdk k))
      have hsg_one : s / g = 1 := Nat.eq_one_of_dvd_coprimes hcop_kk (dvd_refl (s / g)) hdiv_kk
      rw [← hs_eq, hsg_one, mul_one]
      exact hgd_k
  · intro hsk
    exact dvd_mul_of_dvd_right hsk d

/-- Local helper: for any squarefree-supported weight `c`, `sieveSeq H c (p ^ (a + 1) * u) = sieveSeq H c (p * u)`. -/
private theorem sieveSeq_prime_pow_succ_mul_eq (H : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) (p u a : ℕ) :
    sieveSeq H c (p ^ (a + 1) * u) = sieveSeq H c (p * u) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hrew : p ^ (a + 1 + 1) * u = p * (p ^ (a + 1) * u) := by
      rw [pow_succ', mul_assoc]
    have hdvd : p ∣ p ^ (a + 1) * u :=
      dvd_mul_of_dvd_left (dvd_pow_self p (by omega : a + 1 ≠ 0)) u
    have hstep : sieveSeq H c (p * (p ^ (a + 1) * u)) = sieveSeq H c (p ^ (a + 1) * u) := by
      unfold sieveSeq
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hsq : Squarefree s
      · simp only [dvd_mul_iff_of_squarefree hsq hdvd]
      · rw [hc s hsq]; split_ifs <;> rfl
    rw [hrew, hstep, ih]

/-- **Excited-Shell Collapse on Prime Chains (`sieveSeq_eq_prime_mul_ordCompl_of_dvd_of_squarefree_support`):**
For every horizon `H : ℕ`, squarefree-supported weight `c : ℕ → ℝ`, prime `p`, and nonzero `m ≠ 0`
divisible by `p` (`p ∣ m`), `sieveSeq H c m` collapses to the first excited level `p * ordCompl[p] m`:
`sieveSeq H c m = sieveSeq H c (p * ordCompl[p] m)`. -/
theorem sieveSeq_eq_prime_mul_ordCompl_of_dvd_of_squarefree_support (H : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) {p m : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) (hpm : p ∣ m) :
    sieveSeq H c m = sieveSeq H c (p * ordCompl[p] m) := by
  have hfac_pos : 0 < m.factorization p := hp.factorization_pos_of_dvd hm hpm
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hfac_pos.ne'
  have hdecomp : m = p ^ (a + 1) * ordCompl[p] m :=
    (Nat.ordProj_mul_ordCompl_eq_self m p).symm.trans
      (congrArg (· * ordCompl[p] m) (congrArg (p ^ ·) ha))
  exact (congrArg (sieveSeq H c) hdecomp).trans
    (sieveSeq_prime_pow_succ_mul_eq H hc p (ordCompl[p] m) a)

/-- **Zero Jump Between Any Two Excited Nodes on the Same Prime Chain
(`sieveSeq_eq_of_same_chain_of_dvd_of_squarefree_support`):**
For every `H : ℕ`, squarefree-supported weight `c : ℕ → ℝ`, prime `p`, and nonzero `m, k ≠ 0` on
the same `p`-chain (`ordCompl[p] m = ordCompl[p] k`) with `p ∣ m` and `p ∣ k`:
`sieveSeq H c m = sieveSeq H c k`. -/
theorem sieveSeq_eq_of_same_chain_of_dvd_of_squarefree_support (H : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) {p m k : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) (hk : k ≠ 0) (hpm : p ∣ m) (hpk : p ∣ k)
    (hchain : ordCompl[p] m = ordCompl[p] k) :
    sieveSeq H c m = sieveSeq H c k := by
  rw [sieveSeq_eq_prime_mul_ordCompl_of_dvd_of_squarefree_support H hc hp hm hpm,
    sieveSeq_eq_prime_mul_ordCompl_of_dvd_of_squarefree_support H hc hp hk hpk, hchain]

/-- **Universal Ground-to-Excited Prime-Chain Jump Law
(`sieveSeq_sub_ordCompl_eq_sieveSeq_div_of_dvd_of_squarefree_support`):**
For every `H : ℕ`, squarefree-supported weight `c : ℕ → ℝ`, prime `p`, and nonzero `m ≠ 0` with
`p ∣ m`, the prime-chain jump from the chain ground state `ordCompl[p] m` to `m` (regardless of
how large the prime-power valuation `v_p(m) ≥ 1` is) equals the renormalized `(H / p)`-sieve at
`ordCompl[p] m`:
`sieveSeq H c m - sieveSeq H c (ordCompl[p] m) = sieveSeq (H / p) (fun d => c (p * d)) (ordCompl[p] m)`. -/
theorem sieveSeq_sub_ordCompl_eq_sieveSeq_div_of_dvd_of_squarefree_support (H : ℕ)
    {c : ℕ → ℝ} (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) {p m : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) (hpm : p ∣ m) :
    sieveSeq H c m - sieveSeq H c (ordCompl[p] m) =
      sieveSeq (H / p) (fun d => c (p * d)) (ordCompl[p] m) := by
  rw [sieveSeq_eq_prime_mul_ordCompl_of_dvd_of_squarefree_support H hc hp hm hpm]
  have hcop : Nat.Coprime p (ordCompl[p] m) :=
    hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hp hm)
  exact sieveSeq_prime_mul_sub_eq_sieveSeq_div H hp hcop c

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
