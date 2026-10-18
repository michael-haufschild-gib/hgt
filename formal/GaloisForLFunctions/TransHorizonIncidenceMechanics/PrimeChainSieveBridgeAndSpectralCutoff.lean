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

/-! ## §4. Exact Sub-Horizon Rank-1 Ground-State Factorization of `bipartiteEnergy` and `varianceEnergy` -/

/-- Every node `m ∈ chainLeft N p b u` and `k ∈ chainRight N p b u` satisfies `0 < m`, `0 < k`,
`m < k`, `ordCompl[p] m = b`, `ordCompl[p] k = b`, and (when `p` is prime) `p ∣ k`. -/
theorem dvd_of_mem_chainRight_of_mem_chainLeft {N p b m k : ℕ} {u : ℝ} (hp : p.Prime)
    (hm : m ∈ chainLeft N p b u) (hk : k ∈ chainRight N p b u) :
    0 < m ∧ 0 < k ∧ m < k ∧ ordCompl[p] m = b ∧ ordCompl[p] k = b ∧ p ∣ k := by
  unfold chainLeft at hm
  unfold chainRight at hk
  simp only [Finset.mem_filter] at hm hk
  obtain ⟨hm_div, hm_ord, hm_log⟩ := hm
  obtain ⟨hk_div, hk_ord, hk_log⟩ := hk
  have hm_pos : 0 < m := Nat.pos_of_mem_divisors hm_div
  have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk_div
  have hmk : m < k := by
    by_contra hle
    have hlog : Real.log (k : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by exact_mod_cast hk_pos) (by exact_mod_cast Nat.le_of_not_gt hle)
    linarith
  obtain ⟨r, hr_pos, hkr⟩ :=
    exists_pow_mul_of_same_chain hp hm_pos hmk (hm_ord.trans hk_ord.symm)
  have hpk : p ∣ k := by
    rw [hkr]
    exact dvd_mul_of_dvd_right (dvd_pow_self p hr_pos.ne') m
  exact ⟨hm_pos, hk_pos, hmk, hm_ord, hk_ord, hpk⟩

/-- Every node `m ∈ chainLeft N p b u` different from the chain base `b` (`m ≠ b`) is divisible
by `p`. -/
theorem dvd_of_mem_chainLeft_of_ne_base {N p b m : ℕ} {u : ℝ} (_hp : p.Prime)
    (hm : m ∈ chainLeft N p b u) (hne : m ≠ b) :
    0 < m ∧ ordCompl[p] m = b ∧ p ∣ m := by
  unfold chainLeft at hm
  simp only [Finset.mem_filter] at hm
  obtain ⟨hm_div, hm_ord, _⟩ := hm
  have hm_pos : 0 < m := Nat.pos_of_mem_divisors hm_div
  have hdecomp := Nat.ordProj_mul_ordCompl_eq_self m p
  have hfac_ne : m.factorization p ≠ 0 := by
    intro h0
    have hmb : m = b := by
      rw [← hm_ord, h0, pow_zero, Nat.div_one]
    exact hne hmb
  refine ⟨hm_pos, hm_ord, ?_⟩
  rw [← hdecomp]
  exact dvd_mul_of_dvd_left (dvd_pow_self p hfac_ne) (ordCompl[p] m)

/-- Whenever `chainLeft N p b u` is nonempty, `sieveSeq H c` is identically equal to
`sieveSeq H c (p * b)` on `chainRight N p b u` for any squarefree-supported weight `c`. -/
theorem sieveSeq_eq_prime_mul_base_on_chainRight (H : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) {N p b m k : ℕ} {u : ℝ} (hp : p.Prime)
    (hm : m ∈ chainLeft N p b u) (hk : k ∈ chainRight N p b u) :
    sieveSeq H c k = sieveSeq H c (p * b) := by
  obtain ⟨_, hk_pos, _, _, hk_ord, hpk⟩ := dvd_of_mem_chainRight_of_mem_chainLeft hp hm hk
  rw [sieveSeq_eq_prime_mul_ordCompl_of_dvd_of_squarefree_support H hc hp hk_pos.ne' hpk, hk_ord]

/-- **Exact Vanishing of Right-Chain Internal Scatter (`scatter_chainRight_sieveSeq_eq_zero_of_mem_chainLeft`):**
Whenever `chainLeft N p b u` contains at least one element `m`, `sieveSeq H c` is constant across
`chainRight N p b u`, so `scatter (chainRight N p b u) (sieveSeq H c) = 0`. -/
theorem scatter_chainRight_sieveSeq_eq_zero_of_mem_chainLeft (H : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) {N p b m : ℕ} {u : ℝ} (hp : p.Prime)
    (hm : m ∈ chainLeft N p b u) :
    scatter (chainRight N p b u) (sieveSeq H c) = 0 := by
  by_cases hR : (chainRight N p b u) = ∅
  · simp [hR, scatter]
  · have hmean : mean (chainRight N p b u) (sieveSeq H c) = sieveSeq H c (p * b) := by
      unfold mean
      have hsum : (∑ k ∈ chainRight N p b u, sieveSeq H c k) =
          (chainRight N p b u).card * sieveSeq H c (p * b) := by
        rw [Finset.sum_congr rfl (fun k hk =>
          sieveSeq_eq_prime_mul_base_on_chainRight H hc hp hm hk),
          Finset.sum_const, nsmul_eq_mul]
      have hcard_ne : ((chainRight N p b u).card : ℝ) ≠ 0 := by
        exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hR)
      rw [hsum, mul_div_cancel_left₀ _ hcard_ne]
    unfold scatter
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [sieveSeq_eq_prime_mul_base_on_chainRight H hc hp hm hk, hmean, sub_self, sq, mul_zero]

/-- When the chain base `b` does not lie in `chainLeft N p b u`, every node `m ∈ chainLeft N p b u`
is an excited node (`p ∣ m`), so all jumps to `chainRight N p b u` vanish and
`bipartiteEnergy (chainLeft N p b u) (chainRight N p b u) (sieveSeq H c) = 0`. -/
theorem bipartiteEnergy_chain_sieveSeq_of_not_mem_chainLeft (H : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) {N p b : ℕ} {u : ℝ} (hp : p.Prime)
    (hb : b ∉ chainLeft N p b u) :
    bipartiteEnergy (chainLeft N p b u) (chainRight N p b u) (sieveSeq H c) = 0 := by
  unfold bipartiteEnergy
  refine Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun k hk => ?_
  have hne : m ≠ b := fun h => hb (h ▸ hm)
  obtain ⟨hm_pos, hm_ord, hpm⟩ := dvd_of_mem_chainLeft_of_ne_base hp hm hne
  obtain ⟨_, hk_pos, _, _, hk_ord, hpk⟩ := dvd_of_mem_chainRight_of_mem_chainLeft hp hm hk
  rw [sieveSeq_eq_of_same_chain_of_dvd_of_squarefree_support H hc hp hm_pos.ne' hk_pos.ne' hpm hpk
    (hm_ord.trans hk_ord.symm), sub_self, sq, mul_zero]

/-- When the chain base `b` lies in `chainLeft N p b u`, all excited nodes `m ∈ chainLeft \ {b}`
contribute `0` to `bipartiteEnergy`, while the ground node `m = b` contributes
`sieveSeq (H / p) (fun d => c (p * d)) b ^ 2` for each `k ∈ chainRight N p b u`. -/
theorem bipartiteEnergy_chain_sieveSeq_of_mem_chainLeft (H : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) {N p b : ℕ} {u : ℝ} (hp : p.Prime)
    (hb : b ∈ chainLeft N p b u) :
    bipartiteEnergy (chainLeft N p b u) (chainRight N p b u) (sieveSeq H c) =
      ((chainRight N p b u).card : ℝ) *
        sieveSeq (H / p) (fun d => c (p * d)) b ^ (2 : ℕ) := by
  unfold bipartiteEnergy
  rw [Finset.sum_eq_single b]
  · have hconst : ∀ k ∈ chainRight N p b u,
        (sieveSeq H c b - sieveSeq H c k) ^ (2 : ℕ) =
          sieveSeq (H / p) (fun d => c (p * d)) b ^ (2 : ℕ) := by
      intro k hk
      obtain ⟨_, hk_pos, _, _, hk_ord, hpk⟩ := dvd_of_mem_chainRight_of_mem_chainLeft hp hb hk
      have hjump :=
        sieveSeq_sub_ordCompl_eq_sieveSeq_div_of_dvd_of_squarefree_support H hc hp hk_pos.ne' hpk
      rw [hk_ord] at hjump
      have hneg : sieveSeq H c b - sieveSeq H c k =
          -sieveSeq (H / p) (fun d => c (p * d)) b := by linarith
      rw [hneg, neg_sq]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  · intro m hm hne
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hm_pos, hm_ord, hpm⟩ := dvd_of_mem_chainLeft_of_ne_base hp hm hne
    obtain ⟨_, hk_pos, _, _, hk_ord, hpk⟩ := dvd_of_mem_chainRight_of_mem_chainLeft hp hm hk
    rw [sieveSeq_eq_of_same_chain_of_dvd_of_squarefree_support H hc hp hm_pos.ne' hk_pos.ne'
      hpm hpk (hm_ord.trans hk_ord.symm), sub_self, sq, mul_zero]
  · intro hnot
    exact (hnot hb).elim

/-- **Universal Sub-Horizon Rank-1 Ground-State Factorization of `bipartiteEnergy`
(`bipartiteEnergy_chain_sieveSeq_eq_ite`):**
For every horizon `H : ℕ`, squarefree-supported weight `c : ℕ → ℝ`, prime `p`, product index `N : ℕ`,
chain base `b : ℕ`, and logarithmic cut `u : ℝ`:
`bipartiteEnergy (chainLeft N p b u) (chainRight N p b u) (sieveSeq H c) =
  if b ∈ chainLeft N p b u then (chainRight N p b u).card * sieveSeq (H / p) (fun d => c (p * d)) b ^ 2 else 0`. -/
theorem bipartiteEnergy_chain_sieveSeq_eq_ite (H : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) (N : ℕ) {p : ℕ} (hp : p.Prime)
    (b : ℕ) (u : ℝ) :
    bipartiteEnergy (chainLeft N p b u) (chainRight N p b u) (sieveSeq H c) =
      if b ∈ chainLeft N p b u then
        ((chainRight N p b u).card : ℝ) *
          sieveSeq (H / p) (fun d => c (p * d)) b ^ (2 : ℕ)
      else 0 := by
  split_ifs with hb
  · exact bipartiteEnergy_chain_sieveSeq_of_mem_chainLeft H hc hp hb
  · exact bipartiteEnergy_chain_sieveSeq_of_not_mem_chainLeft H hc hp hb

/-- **Universal Sub-Horizon Rank-1 Ground-State Factorization of `varianceEnergy`
(`varianceEnergy_chain_sieveSeq_eq_ite`):**
For every horizon `H : ℕ`, squarefree-supported weight `c : ℕ → ℝ`, prime `p`, product index `N : ℕ`,
chain base `b : ℕ`, and logarithmic cut `u : ℝ`:
`varianceEnergy (chainLeft N p b u) (chainRight N p b u) (sieveSeq H c) =
  if b ∈ chainLeft N p b u then (chainRight N p b u).card * sieveSeq (H / p) (fun d => c (p * d)) b ^ 2 else 0`. -/
theorem varianceEnergy_chain_sieveSeq_eq_ite (H : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) (N : ℕ) {p : ℕ} (hp : p.Prime)
    (b : ℕ) (u : ℝ) :
    varianceEnergy (chainLeft N p b u) (chainRight N p b u) (sieveSeq H c) =
      if b ∈ chainLeft N p b u then
        ((chainRight N p b u).card : ℝ) *
          sieveSeq (H / p) (fun d => c (p * d)) b ^ (2 : ℕ)
      else 0 := by
  rw [← bipartiteEnergy_eq_variance]
  exact bipartiteEnergy_chain_sieveSeq_eq_ite H hc N hp b u

/-! ## §5. Multiplicative Renormalization Fixed-Point Law & Terminal-Octave Quantization -/

/-- Whenever a weight `c : ℕ → ℝ` factors as `c (p * d) = c p * c d` on all divisors `d ∣ b`,
the dilated-weight sieve `sieveSeq K (fun d => c (p * d)) b` equals `c p * sieveSeq K c b`. -/
theorem sieveSeq_div_mul_weight_eq_mul_sieveSeq (K p b : ℕ) (c : ℕ → ℝ)
    (hfac : ∀ d : ℕ, d ∣ b → c (p * d) = c p * c d) :
    sieveSeq K (fun d => c (p * d)) b = c p * sieveSeq K c b := by
  unfold sieveSeq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  exact hfac d (Finset.mem_filter.mp hd).2

/-- **Multiplicative Renormalization Fixed-Point Law for `varianceEnergy`
(`varianceEnergy_chain_sieveSeq_eq_mul_sq_of_factor_on_divisors`):**
Whenever `c` is squarefree-supported and `c (p * d) = c p * c d` for all `d ∣ b` (which holds
for all multiplicative weights when `b ∈ chainLeft N p b u`, since `p ∤ b`), the prime-chain
variance at horizon `H` equals `|R| * c(p)^2 * (sieveSeq (H / p) c b)^2` if `b ∈ L` and `0` otherwise. -/
theorem varianceEnergy_chain_sieveSeq_eq_mul_sq_of_factor_on_divisors (H : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) (N : ℕ) {p : ℕ} (hp : p.Prime)
    (b : ℕ) (u : ℝ) (hfac : ∀ d : ℕ, d ∣ b → c (p * d) = c p * c d) :
    varianceEnergy (chainLeft N p b u) (chainRight N p b u) (sieveSeq H c) =
      if b ∈ chainLeft N p b u then
        ((chainRight N p b u).card : ℝ) * c p ^ (2 : ℕ) *
          sieveSeq (H / p) c b ^ (2 : ℕ)
      else 0 := by
  rw [varianceEnergy_chain_sieveSeq_eq_ite H hc N hp b u,
    sieveSeq_div_mul_weight_eq_mul_sieveSeq (H / p) p b c hfac]
  split_ifs <;> ring

/-- For any integer `H` and prime `p` in the terminal band `p ≤ H < 2 * p`, integer division gives
`H / p = 1`, so `sieveSeq (H / p) (fun d => c (p * d)) b = c p` for **every** `b : ℕ` (with no
multiplicativity assumption on `c`!). -/
theorem sieveSeq_div_eq_apply_prime_of_le_of_lt_two_mul {H p : ℕ} (hp : p.Prime)
    (hle : p ≤ H) (hlt : H < 2 * p) (c : ℕ → ℝ) (b : ℕ) :
    sieveSeq (H / p) (fun d => c (p * d)) b = c p := by
  have hp_pos : 0 < p := hp.pos
  have hdiv : H / p = 1 := by
    apply le_antisymm
    · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp_pos).mpr (by omega))
    · exact (Nat.le_div_iff_mul_le hp_pos).mpr (by omega)
  rw [hdiv]
  unfold sieveSeq
  have hset : (Finset.Icc 1 1).filter (fun d => d ∣ b) = {1} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd1, hd1'⟩, _⟩
      omega
    · rintro rfl
      exact ⟨⟨le_rfl, le_rfl⟩, one_dvd b⟩
  rw [hset, Finset.sum_singleton, mul_one]

/-- **Universal Terminal-Octave Prime-Chain Step Law (`sieveSeq_prime_mul_sub_eq_of_mem_sievePrimeTail`):**
For every terminal prime `p ∈ sievePrimeTail H` (`H / 2 < p ≤ H`), every weight `c : ℕ → ℝ`, and
every `b : ℕ` coprime to `p`, stepping from `b` to `p * b` changes `sieveSeq H c` by `c p`
universally across all trans-horizon scales `b ≫ H`:
`sieveSeq H c (p * b) - sieveSeq H c b = c p`. -/
theorem sieveSeq_prime_mul_sub_eq_of_mem_sievePrimeTail {H p b : ℕ}
    (hp_tail : p ∈ sievePrimeTail H) (hcop : Nat.Coprime p b) (c : ℕ → ℝ) :
    sieveSeq H c (p * b) - sieveSeq H c b = c p := by
  unfold sievePrimeTail at hp_tail
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp_tail
  obtain ⟨⟨_, hpH⟩, hp, hlt⟩ := hp_tail
  rw [sieveSeq_prime_mul_sub_eq_sieveSeq_div H hp hcop c,
    sieveSeq_div_eq_apply_prime_of_le_of_lt_two_mul hp hpH hlt c b]

/-- **Universal Terminal-Octave Quantization of `varianceEnergy`
(`varianceEnergy_chain_sieveSeq_eq_of_mem_sievePrimeTail`):**
For every horizon `H : ℕ`, squarefree-supported weight `c : ℕ → ℝ`, terminal prime
`p ∈ sievePrimeTail H` (`H / 2 < p ≤ H`), product index `N : ℕ`, chain base `b : ℕ`, and cut `u : ℝ`,
the `CHMDPrimeChain` variance energy is universally quantized to `|chainRight N p b u| * c(p)^2`:
`varianceEnergy (chainLeft N p b u) (chainRight N p b u) (sieveSeq H c) =
  if b ∈ chainLeft N p b u then (chainRight N p b u).card * c p ^ 2 else 0`. -/
theorem varianceEnergy_chain_sieveSeq_eq_of_mem_sievePrimeTail (H : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) (N : ℕ) {p : ℕ}
    (hp_tail : p ∈ sievePrimeTail H) (b : ℕ) (u : ℝ) :
    varianceEnergy (chainLeft N p b u) (chainRight N p b u) (sieveSeq H c) =
      if b ∈ chainLeft N p b u then
        ((chainRight N p b u).card : ℝ) * c p ^ (2 : ℕ)
      else 0 := by
  unfold sievePrimeTail at hp_tail
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp_tail
  obtain ⟨⟨_, hpH⟩, hp, hlt⟩ := hp_tail
  rw [varianceEnergy_chain_sieveSeq_eq_ite H hc N hp b u,
    sieveSeq_div_eq_apply_prime_of_le_of_lt_two_mul hp hpH hlt c b]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
