import GaloisForLFunctions.TransHorizonIncidenceMechanics.SuccessorStateObstructionAndPhaseRefinement
import GaloisForLFunctions.TransHorizonIncidenceMechanics.HorizonRadicalStateAndDefectNormalForm

/-!
# Exact Totient Observability Thresholds and Valuation-Clock Fiber Collisions (`TotientObservabilityThresholdAndValuationFiberCollision`)

## 1. Central Problem & Classical Baseline

In the classical theory of $L_N$-even arithmetic functions (Cohen 1955; McCarthy 1986;
Tóth–Haukkanen 2010), a truncated divisor sum
$$s_{N,c}(k) = \sum_{\substack{d \mid k \\ d \le N}} c(d)$$
depends on $k$ only through its multiplicative observation state
$\sigma_N(k) = \operatorname{lcm}\{d \le N : d \mid k\} = \gcd(k, L_N)$, where
$L_N = \operatorname{lcm}(1, \dots, N)$. Because the map
$$\bar{\sigma}_N : \mathbb{Z}/L_N\mathbb{Z} \longrightarrow \mathcal{D}_N, \qquad
  k \bmod L_N \longmapsto \gcd(k, L_N)$$
has fiber size $\varphi(L_N / g)$ over each divisor state $g \mid L_N$, a single observation
$\sigma_N(k)$ does not determine $\sigma_N(k + 1)$ whenever $N \ge 3$
(`horizonObservationState_successor_congr_iff`).

In `SuccessorStateObstructionAndPhaseRefinement`, it was shown that observing $\sigma_N(k + t)$
for $0 \le t < N$ suffices to recover the full additive residue phase $k \bmod L_N$
(`horizonObservationPhase_eq_iff_finite_trace`), with the explicit caveat:
> *"No optimality of the observation length $N$ is asserted."*

**Central Question:** *What is the exact minimum number of consecutive multiplicative observations
$\sigma_N(k + t)$ ($0 \le t < W$)—or squarefree observations $\operatorname{rad}_N(k + t) = \gcd(k + t, N\#)$—required
to resolve all fiber ambiguities and uniquely reconstruct the additive phase $k \bmod L_N$ (resp.
$k \bmod N\#$)?*

## 2. Organizing Principle: Valuation-Clock Shift Collisions vs. Tail Uniqueness

For a prime power $p^a$ ($a \ge 1$), Pillar I (`ValuationClockChainBridge`) identified the
**valuation visibility clock** $\tau_{\mathrm{vis}}(p^a) = p^a / \operatorname{rad}(p^a) = p^{a-1}$
as the exact lag at which the Ramanujan sum $c_{p^a}(L)$ switches on. In the additive time domain,
shifting an integer by $\tau_{\mathrm{vis}}(p^a) = p^{a-1}$ preserves all lower $p$-adic valuations
$v_p(k + t) < a - 1$. Consequently:
- **Sharp Collision Below $\varphi(p^a) = p^a - \tau_{\mathrm{vis}}(p^a)$:**
  The pair $k = 1$ and $\ell = 1 + p^{a-1}$ satisfies $k \not\equiv \ell \pmod{p^a}$, yet neither
  $1 + t$ nor $1 + p^{a-1} + t$ reaches $p^a$ during the first $\varphi(p^a) - 1 = p^a - p^{a-1} - 1$
  steps, so their $p$-adic gcd traces coincide identically for all $0 \le t < \varphi(p^a) - 1$.
- **Exact Resolution at $\varphi(p^a)$:**
  Once $k \equiv \ell \pmod{p^{a-1}}$ is known by induction on $a$, the unique return time
  $t_k \in [0, p^a - 1]$ with $p^a \mid k + t_k$ is already determined modulo $p^{a-1}$. If $t_k$
  and $t_\ell$ both avoid the inspected prefix $[0, \varphi(p^a) - 1]$, both are forced into the
  uninspected tail $[p^a - p^{a-1}, p^a - 1]$ of length exactly $p^{a-1} = \tau_{\mathrm{vis}}(p^a)$,
  where each residue class modulo $p^{a-1}$ has a unique representative, forcing $t_k = t_\ell$.

## 3. Main Theorems (Labelled Against the Classical Baseline)

1. **Exact Prime-Power Totient Observability Theorem — `[Candidate new theorem]`
   (`gcd_prime_pow_collision_below_totient`, `modEq_prime_pow_of_gcd_eq_below_totient`,
   `prime_pow_trace_injective_iff_totient_le`):**
   For every prime $p$ and exponent $a \ge 1$, a window of length $W$ of $p$-adic gcd observations
   $t \mapsto \gcd(k + t, p^a)$ ($0 \le t < W$) uniquely determines $k \bmod p^a$ for all
   $k, \ell \in \mathbb{N}$ **if and only if**
   $$W \ge \varphi(p^a) = p^a - \tau_{\mathrm{vis}}(p^a).$$

2. **Horizon Totient Observability Theorem — `[Candidate new theorem]`
   (`horizonTotientThreshold`, `horizonTotientThreshold_lt_self`,
   `horizonObservationPhase_eq_iff_totient_trace`):**
   Define $\Phi_{\max}(N) = \max_{p^a \le N} \varphi(p^a)$. For every $N \ge 1$,
   $\Phi_{\max}(N) < N$, strictly improving the $W = N$ bound of
   `horizonObservationPhase_eq_iff_finite_trace`. For every $W \ge \Phi_{\max}(N)$ and all
   $k, \ell \in \mathbb{N}$:
   $$\operatorname{horizonObservationPhase}(N, k) = \operatorname{horizonObservationPhase}(N, \ell)
     \iff \forall t < W,\; \forall c : \mathbb{N} \to \mathbb{R},\;
       s_{N,c}(k + t) = s_{N,c}(\ell + t).$$

3. **Squarefree / Primorial Radical Observability Theorem — `[Candidate new theorem]`
   (`horizonPrimeTotientThreshold`, `horizonRadicalPhase`,
   `horizonRadicalPhase_eq_iff_prime_totient_trace`, `radical_prime_collision_below_totient`):**
   For squarefree-supported weights, observing $\operatorname{horizonRadicalState}(N, k + t)$
   for $0 \le t < W$ recovers the primorial phase $k \bmod N\#$ whenever
   $W \ge \max_{p \le N \text{ prime}} (p - 1)$, and for every prime $p \le N$, window length
   $W = p - 2$ fails on $k = 1, \ell = 2$.
-/

open Finset
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Prime-Power Valuation-Clock Collisions and the Exact $\varphi(p^a)$ Threshold -/

/-- **Sub-Ceiling $p$-Adic GCD Reduction (`gcd_prime_pow_eq_gcd_pred_of_not_dvd`):**
If $p$ is prime, $a \ge 1$, and $p^a \nmid x$, then every common divisor of $x$ and $p^a$ already
divides $p^{a-1}$, so $\gcd(x, p^a) = \gcd(x, p^{a-1})$. -/
theorem gcd_prime_pow_eq_gcd_pred_of_not_dvd {p a x : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hndvd : ¬ p ^ a ∣ x) :
    Nat.gcd x (p ^ a) = Nat.gcd x (p ^ (a - 1)) := by
  apply Nat.dvd_antisymm
  · refine Nat.dvd_gcd (Nat.gcd_dvd_left x (p ^ a)) ?_
    obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right x (p ^ a))
    have hk_lt : k < a := by
      by_contra hge
      have hka : k = a := by omega
      apply hndvd
      rw [← hka, ← hk_eq]
      exact Nat.gcd_dvd_left x (p ^ a)
    rw [hk_eq]
    exact pow_dvd_pow p (by omega : k ≤ a - 1)
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left x (p ^ (a - 1)))
      ((Nat.gcd_dvd_right x (p ^ (a - 1))).trans (pow_dvd_pow p (by omega : a - 1 ≤ a)))

/-- For any prime $p$ and $a \ge 1$, $\varphi(p^a) + p^{a-1} = p^a$. -/
theorem totient_prime_pow_add_pred (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) :
    (p ^ a).totient + p ^ (a - 1) = p ^ a := by
  rw [Nat.totient_prime_pow hp (by omega : 0 < a)]
  have hpow : p ^ a = p ^ (a - 1) * p := by
    conv_lhs => rw [← Nat.sub_add_cancel ha, pow_succ]
  have hp1 : 1 ≤ p := hp.one_le
  rw [hpow, Nat.mul_sub_left_distrib, mul_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hp.pos)]

/-- **Sharp Valuation-Clock Collision Below $\varphi(p^a)$
(`gcd_prime_pow_collision_below_totient`):**
For every prime $p$ and $a \ge 1$, the states $k = 1$ and $\ell = 1 + p^{a-1}$ (shifted by the
valuation visibility clock $\tau_{\mathrm{vis}}(p^a) = p^{a-1}$) are incongruent modulo $p^a$, yet
have identical $p$-adic gcd observations $\gcd(1 + t, p^a) = \gcd(1 + p^{a-1} + t, p^a)$ for every
$t$ with $t + 1 < \varphi(p^a)$. -/
theorem gcd_prime_pow_collision_below_totient {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    ¬ Nat.ModEq (p ^ a) 1 (1 + p ^ (a - 1)) ∧
      ∀ t : ℕ, t + 1 < (p ^ a).totient →
        Nat.gcd (1 + t) (p ^ a) = Nat.gcd (1 + p ^ (a - 1) + t) (p ^ a) := by
  have hsum := totient_prime_pow_add_pred p a hp ha
  have hlt_pow : p ^ (a - 1) < p ^ a :=
    Nat.pow_lt_pow_right hp.one_lt (by omega : a - 1 < a)
  refine ⟨?_, fun t ht => ?_⟩
  · intro hmod
    have hdvd : p ^ a ∣ (1 + p ^ (a - 1)) - 1 :=
      (Nat.modEq_iff_dvd' (by omega : 1 ≤ 1 + p ^ (a - 1))).mp hmod
    simp only [Nat.add_sub_cancel_left] at hdvd
    have hle := Nat.le_of_dvd (pow_pos hp.pos (a - 1)) hdvd
    omega
  · have hndvd1 : ¬ p ^ a ∣ 1 + t := by
      intro hdvd
      have hle := Nat.le_of_dvd (by omega : 0 < 1 + t) hdvd
      omega
    have hndvd2 : ¬ p ^ a ∣ 1 + p ^ (a - 1) + t := by
      intro hdvd
      have hle := Nat.le_of_dvd (by omega : 0 < 1 + p ^ (a - 1) + t) hdvd
      omega
    rw [gcd_prime_pow_eq_gcd_pred_of_not_dvd hp ha hndvd1,
      gcd_prime_pow_eq_gcd_pred_of_not_dvd hp ha hndvd2]
    have hrew : 1 + p ^ (a - 1) + t = (1 + t) + 1 * p ^ (a - 1) := by ring
    rw [hrew, Nat.gcd_add_mul_right_left]

/-- For any $d > 0$ and $k \in \mathbb{N}$, there exists $t < d$ such that $d \mid k + t$. -/
theorem exists_divisibility_return (d k : ℕ) (hd : 0 < d) :
    ∃ t, t < d ∧ d ∣ k + t := by
  refine ⟨(d - k % d) % d, Nat.mod_lt _ hd, ?_⟩
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod_mod, ← Nat.mod_add_mod k d (d - k % d),
    Nat.add_sub_of_le (Nat.mod_lt k hd).le, Nat.mod_self]

/-- **Sufficiency of $\varphi(p^a)$ Observations for Prime-Power Phase Reconstruction
(`modEq_prime_pow_of_gcd_eq_below_totient`):**
For every prime $p$, exponent $a \in \mathbb{N}$, and $k, \ell \in \mathbb{N}$, if
$\gcd(k + t, p^a) = \gcd(\ell + t, p^a)$ for all $t < \varphi(p^a)$, then
$k \equiv \ell \pmod{p^a}$. -/
theorem modEq_prime_pow_of_gcd_eq_below_totient {p : ℕ} (hp : p.Prime)
    (a k l : ℕ)
    (h : ∀ t < (p ^ a).totient, Nat.gcd (k + t) (p ^ a) = Nat.gcd (l + t) (p ^ a)) :
    Nat.ModEq (p ^ a) k l := by
  induction a with
  | zero =>
    rw [pow_zero]
    exact Nat.modEq_one
  | succ a ih =>
    have hmod_a : Nat.ModEq (p ^ a) k l := by
      by_cases ha0 : a = 0
      · subst ha0
        rw [pow_zero]
        exact Nat.modEq_one
      · apply ih
        intro t ht
        have htot_le : (p ^ a).totient ≤ (p ^ (a + 1)).totient := by
          rw [Nat.totient_prime_pow hp (by omega : 0 < a),
            Nat.totient_prime_pow hp (by omega : 0 < a + 1)]
          exact Nat.mul_le_mul_right (p - 1) (Nat.pow_le_pow_right hp.pos (by omega))
        have hstep := h t (ht.trans_le htot_le)
        have hdvd : p ^ a ∣ p ^ (a + 1) := pow_dvd_pow p (by omega)
        have h1 : Nat.gcd (Nat.gcd (k + t) (p ^ (a + 1))) (p ^ a) =
            Nat.gcd (k + t) (p ^ a) := by
          rw [Nat.gcd_assoc, Nat.gcd_eq_right hdvd]
        have h2 : Nat.gcd (Nat.gcd (l + t) (p ^ (a + 1))) (p ^ a) =
            Nat.gcd (l + t) (p ^ a) := by
          rw [Nat.gcd_assoc, Nat.gcd_eq_right hdvd]
        rw [← h1, ← h2, hstep]
    let P := p ^ (a + 1)
    let Q := p ^ a
    have hP_pos : 0 < P := pow_pos hp.pos (a + 1)
    have hQ_pos : 0 < Q := pow_pos hp.pos a
    have hQP : Q ∣ P := pow_dvd_pow p (by omega : a ≤ a + 1)
    have hsum : P.totient + Q = P := totient_prime_pow_add_pred p (a + 1) hp (by omega)
    obtain ⟨tk, htk_lt, htk_dvd⟩ := exists_divisibility_return P k hP_pos
    obtain ⟨tl, htl_lt, htl_dvd⟩ := exists_divisibility_return P l hP_pos
    by_cases htk_tot : tk < P.totient
    · have hgcd := h tk htk_tot
      rw [Nat.gcd_eq_right htk_dvd] at hgcd
      have htl_k : P ∣ l + tk := by
        rw [hgcd]
        exact Nat.gcd_dvd_left (l + tk) P
      exact Nat.ModEq.add_right_cancel' tk
        ((Nat.modEq_zero_iff_dvd.mpr htk_dvd).trans (Nat.modEq_zero_iff_dvd.mpr htl_k).symm)
    · by_cases htl_tot : tl < P.totient
      · have hgcd := h tl htl_tot
        rw [Nat.gcd_eq_right htl_dvd] at hgcd
        have htk_l : P ∣ k + tl := by
          rw [← hgcd]
          exact Nat.gcd_dvd_left (k + tl) P
        exact Nat.ModEq.add_right_cancel' tl
          ((Nat.modEq_zero_iff_dvd.mpr htk_l).trans (Nat.modEq_zero_iff_dvd.mpr htl_dvd).symm)
      · have hQ_tk : Q ∣ k + tk := hQP.trans htk_dvd
        have hQ_tl : Q ∣ l + tl := hQP.trans htl_dvd
        have hmod_tk_tl : Nat.ModEq Q tk tl := by
          have h1 : Nat.ModEq Q (k + tk) (l + tl) :=
            (Nat.modEq_zero_iff_dvd.mpr hQ_tk).trans (Nat.modEq_zero_iff_dvd.mpr hQ_tl).symm
          have h2 : Nat.ModEq Q (k + tk) (k + tl) :=
            h1.trans (hmod_a.symm.add_right tl)
          exact Nat.ModEq.add_left_cancel' k h2
        have htk_eq_tl : tk = tl := by
          rcases le_total tk tl with hle | hle
          · have hdvd_sub : Q ∣ tl - tk := (Nat.modEq_iff_dvd' hle).mp hmod_tk_tl
            have hlt_sub : tl - tk < Q := by omega
            have hzero : tl - tk = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_sub hlt_sub
            omega
          · have hdvd_sub : Q ∣ tk - tl := (Nat.modEq_iff_dvd' hle).mp hmod_tk_tl.symm
            have hlt_sub : tk - tl < Q := by omega
            have hzero : tk - tl = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_sub hlt_sub
            omega
        subst htk_eq_tl
        exact Nat.ModEq.add_right_cancel' tk
          ((Nat.modEq_zero_iff_dvd.mpr htk_dvd).trans (Nat.modEq_zero_iff_dvd.mpr htl_dvd).symm)

/-- **Exact Prime-Power Totient Observability Classification
(`prime_pow_trace_injective_iff_totient_le`):**
For every prime $p$, exponent $a \ge 1$, and window length $W : \mathbb{N}$, observing
$\gcd(k + t, p^a)$ for $0 \le t < W$ uniquely determines $k \bmod p^a$ for all $k, \ell \in \mathbb{N}$
**if and only if** $\varphi(p^a) \le W$. -/
theorem prime_pow_trace_injective_iff_totient_le {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (W : ℕ) :
    (∀ k l : ℕ,
      (∀ t < W, Nat.gcd (k + t) (p ^ a) = Nat.gcd (l + t) (p ^ a)) →
      Nat.ModEq (p ^ a) k l) ↔
      (p ^ a).totient ≤ W := by
  constructor
  · intro hinj
    by_contra hlt
    obtain ⟨hne, hcol⟩ := gcd_prime_pow_collision_below_totient hp ha
    apply hne
    apply hinj 1 (1 + p ^ (a - 1))
    intro t ht
    exact hcol t (by omega)
  · intro hle k l htrace
    exact modEq_prime_pow_of_gcd_eq_below_totient hp a k l fun t ht =>
      htrace t (ht.trans_le hle)

/-! ## §2. The Horizon Totient Observability Threshold $\Phi_{\max}(N)$ -/

/-- **Horizon Totient Observability Threshold (`horizonTotientThreshold`):**
The maximum of $\varphi(d)$ over all prime powers $d = p^a \in [1, N]$. -/
def horizonTotientThreshold (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter IsPrimePow).sup Nat.totient

/-- Every prime power $p^a \le N$ ($a \ge 1$) has $\varphi(p^a) \le \operatorname{horizonTotientThreshold}(N)$. -/
theorem totient_prime_pow_le_horizonTotientThreshold {N p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hle : p ^ a ≤ N) :
    (p ^ a).totient ≤ horizonTotientThreshold N := by
  unfold horizonTotientThreshold
  apply Finset.le_sup (f := Nat.totient)
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨pow_pos hp.pos a, hle⟩, hp.isPrimePow.pow (by omega : a ≠ 0)⟩

/-- **Strict Sub-Horizon Bound (`horizonTotientThreshold_lt_self`):**
For every $N \ge 1$, $\operatorname{horizonTotientThreshold}(N) < N$, strictly improving the
$N$-step bound of `horizonObservationPhase_eq_iff_finite_trace`. -/
theorem horizonTotientThreshold_lt_self {N : ℕ} (hN : 1 ≤ N) :
    horizonTotientThreshold N < N := by
  unfold horizonTotientThreshold
  rw [Finset.sup_lt_iff (by omega : 0 < N)]
  intro d hd
  obtain ⟨hdI, hpp⟩ := Finset.mem_filter.mp hd
  obtain ⟨_, hdN⟩ := Finset.mem_Icc.mp hdI
  exact (Nat.totient_lt d hpp.one_lt).trans_le hdN

/-- Equality of multiplicative observation states $\sigma_N(k) = \sigma_N(\ell)$ implies
$\gcd(k, d) = \gcd(\ell, d)$ for every active divisor $d \in [1, N]$. -/
theorem gcd_eq_of_horizonObservationState_eq {N k l d : ℕ} (hd : d ∈ Finset.Icc 1 N)
    (hstate : horizonObservationState N k = horizonObservationState N l) :
    Nat.gcd k d = Nat.gcd l d := by
  obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
  have htests := (horizonObservationState_eq_iff_tests N k l).mp hstate
  apply Nat.dvd_antisymm
  · refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right k d)
    have hmem : Nat.gcd k d ∈ Finset.Icc 1 N := by
      rw [Finset.mem_Icc]
      exact ⟨Nat.gcd_pos_of_pos_right k (by omega),
        (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right k d)).trans hdN⟩
    exact (htests (Nat.gcd k d) hmem).mp (Nat.gcd_dvd_left k d)
  · refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right l d)
    have hmem : Nat.gcd l d ∈ Finset.Icc 1 N := by
      rw [Finset.mem_Icc]
      exact ⟨Nat.gcd_pos_of_pos_right l (by omega),
        (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right l d)).trans hdN⟩
    exact (htests (Nat.gcd l d) hmem).mpr (Nat.gcd_dvd_left l d)

/-- If every prime power $p^a \mid d$ divides $m$, then $d \mid m$. -/
theorem dvd_of_forall_prime_pow_dvd {d m : ℕ} (hd : 0 < d)
    (h : ∀ p a : ℕ, p.Prime → 1 ≤ a → p ^ a ∣ d → p ^ a ∣ m) :
    d ∣ m := by
  by_cases hm0 : m = 0
  · subst hm0
    exact dvd_zero d
  · rw [← Nat.factorization_le_iff_dvd (by omega : d ≠ 0) hm0]
    intro p
    by_cases hp : p.Prime
    · by_cases ha : 1 ≤ d.factorization p
      · have hdvd_d : p ^ (d.factorization p) ∣ d := Nat.ordProj_dvd d p
        have hdvd_m : p ^ (d.factorization p) ∣ m := h p (d.factorization p) hp ha hdvd_d
        exact (hp.pow_dvd_iff_le_factorization hm0).mp hdvd_m
      · have h0 : d.factorization p = 0 := by omega
        rw [h0]
        exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime d hp]
      exact Nat.zero_le _

/-- If $k \equiv \ell \pmod{p^a}$ for every prime power $p^a \mid d$, then $k \equiv \ell \pmod d$. -/
theorem modEq_of_forall_prime_pow_dvd {d k l : ℕ} (hd : 0 < d)
    (h : ∀ p a : ℕ, p.Prime → 1 ≤ a → p ^ a ∣ d → Nat.ModEq (p ^ a) k l) :
    Nat.ModEq d k l := by
  rcases le_total k l with hkl | hlk
  · rw [Nat.modEq_iff_dvd' hkl]
    exact dvd_of_forall_prime_pow_dvd hd fun p a hp ha hpad =>
      (Nat.modEq_iff_dvd' hkl).mp (h p a hp ha hpad)
  · apply Nat.ModEq.symm
    rw [Nat.modEq_iff_dvd' hlk]
    exact dvd_of_forall_prime_pow_dvd hd fun p a hp ha hpad =>
      (Nat.modEq_iff_dvd' hlk).mp (h p a hp ha hpad).symm

/-- **Horizon Totient Observability Theorem (`horizonObservationPhase_eq_iff_totient_trace`):**
For every horizon $N : \mathbb{N}$, window length $W \ge \operatorname{horizonTotientThreshold}(N)$,
and $k, \ell \in \mathbb{N}$, the complete residue phase $\operatorname{horizonObservationPhase}(N, k)$
equals $\operatorname{horizonObservationPhase}(N, \ell)$ **if and only if** the first $W$ sieve
observations coincide:
$$\operatorname{horizonObservationPhase}(N, k) = \operatorname{horizonObservationPhase}(N, \ell)
  \iff \forall t < W,\; \forall c : \mathbb{N} \to \mathbb{R},\;
    s_{N,c}(k + t) = s_{N,c}(\ell + t).$$ -/
theorem horizonObservationPhase_eq_iff_totient_trace (N : ℕ) {W : ℕ}
    (hW : horizonTotientThreshold N ≤ W) (k l : ℕ) :
    horizonObservationPhase N k = horizonObservationPhase N l ↔
      ∀ t < W, ∀ c : ℕ → ℝ, sieveSeq N c (k + t) = sieveSeq N c (l + t) := by
  constructor
  · intro h t _
    exact (horizonObservationPhase_eq_iff_all_future N k l).mp h t
  · intro h
    apply (horizonObservationPhase_eq_iff_residues N k l).mpr
    intro d hd
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
    apply modEq_of_forall_prime_pow_dvd hd1
    intro p a hp ha hpad
    have hpaN : p ^ a ≤ N := (Nat.le_of_dvd hd1 hpad).trans hdN
    have hpaI : p ^ a ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨pow_pos hp.pos a, hpaN⟩
    have htot : (p ^ a).totient ≤ W :=
      (totient_prime_pow_le_horizonTotientThreshold hp ha hpaN).trans hW
    apply modEq_prime_pow_of_gcd_eq_below_totient hp a k l
    intro t ht
    have hstate : horizonObservationState N (k + t) = horizonObservationState N (l + t) :=
      (horizonObservationState_eq_iff_all_sieveSeq N (k + t) (l + t)).mpr (h t (ht.trans_le htot))
    exact gcd_eq_of_horizonObservationState_eq hpaI hstate

/-! ## §3. Squarefree / Primorial Radical Observability Threshold -/

/-- **Primorial Radical Phase (`horizonRadicalPhase`):**
The residue class $k \bmod N\#$ (`primorial N`), which governs all future squarefree-supported
sieve observations. -/
def horizonRadicalPhase (N k : ℕ) : ℕ := k % primorial N

/-- **Horizon Prime Totient Threshold (`horizonPrimeTotientThreshold`):**
The maximum of $\varphi(p) = p - 1$ over all primes $p \le N$. -/
def horizonPrimeTotientThreshold (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter Nat.Prime).sup Nat.totient

/-- Equality of primorial radical phases is equivalent to congruence modulo every prime $p \le N$. -/
theorem horizonRadicalPhase_eq_iff_prime_modEq (N k l : ℕ) :
    horizonRadicalPhase N k = horizonRadicalPhase N l ↔
      ∀ p : ℕ, p.Prime → p ≤ N → Nat.ModEq p k l := by
  constructor
  · intro h p hp hpN
    have hdvd : p ∣ primorial N := hp.dvd_primorial_iff.mpr hpN
    exact Nat.ModEq.of_dvd hdvd h
  · intro h
    change Nat.ModEq (primorial N) k l
    apply modEq_of_forall_prime_pow_dvd (primorial_pos N)
    intro p a hp ha hpad
    have ha1 : a = 1 := by
      by_contra hne
      have ha2 : 2 ≤ a := by omega
      have hsq : p * p ∣ primorial N :=
        (sq p ▸ pow_dvd_pow p ha2).trans hpad
      have hu : p = 1 := Nat.isUnit_iff.mp (squarefree_primorial N p hsq)
      exact hp.ne_one hu
    subst ha1
    rw [pow_one] at hpad ⊢
    exact h p hp (hp.dvd_primorial_iff.mp hpad)

/-- **Primorial Radical Observability Theorem (`horizonRadicalPhase_eq_iff_prime_totient_trace`):**
For every $N : \mathbb{N}$, window length $W \ge \operatorname{horizonPrimeTotientThreshold}(N)$,
and $k, \ell \in \mathbb{N}$:
$$\operatorname{horizonRadicalPhase}(N, k) = \operatorname{horizonRadicalPhase}(N, \ell)
  \iff \forall t < W,\; \operatorname{horizonRadicalState}(N, k + t) =
    \operatorname{horizonRadicalState}(N, \ell + t).$$ -/
theorem horizonRadicalPhase_eq_iff_prime_totient_trace (N : ℕ) {W : ℕ}
    (hW : horizonPrimeTotientThreshold N ≤ W) (k l : ℕ) :
    horizonRadicalPhase N k = horizonRadicalPhase N l ↔
      ∀ t < W, horizonRadicalState N (k + t) = horizonRadicalState N (l + t) := by
  constructor
  · intro h t _
    apply (Nat.Squarefree.ext_iff (horizonRadicalState_squarefree N (k + t))
      (horizonRadicalState_squarefree N (l + t))).mpr
    intro p hp
    rw [prime_dvd_horizonRadicalState_iff N (k + t) hp,
      prime_dvd_horizonRadicalState_iff N (l + t) hp]
    by_cases hpN : p ≤ N
    · have hmod := ((horizonRadicalPhase_eq_iff_prime_modEq N k l).mp h p hp hpN).add_right t
      exact and_congr_left fun _ => hmod.dvd_iff dvd_rfl
    · simp [hpN]
  · intro h
    apply (horizonRadicalPhase_eq_iff_prime_modEq N k l).mpr
    intro p hp hpN
    have htot : (p ^ 1).totient ≤ W := by
      rw [pow_one]
      refine (Finset.le_sup (f := Nat.totient) ?_).trans hW
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hp.one_le, hpN⟩, hp⟩
    simpa only [pow_one] using modEq_prime_pow_of_gcd_eq_below_totient hp 1 k l fun t ht => by
      have hst := h t (ht.trans_le htot)
      have hdvd_iff : p ∣ k + t ↔ p ∣ l + t := by
        have h1 := prime_dvd_horizonRadicalState_iff N (k + t) hp
        have h2 := prime_dvd_horizonRadicalState_iff N (l + t) hp
        rw [hst] at h1
        exact ⟨fun hkt => (h2.mp (h1.mpr ⟨hkt, hpN⟩)).1,
          fun hlt => (h1.mp (h2.mpr ⟨hlt, hpN⟩)).1⟩
      rw [pow_one]
      by_cases hkt : p ∣ k + t
      · rw [Nat.gcd_eq_right hkt, Nat.gcd_eq_right (hdvd_iff.mp hkt)]
      · have hlt : ¬ p ∣ l + t := fun hc => hkt (hdvd_iff.mpr hc)
        rw [(hp.coprime_iff_not_dvd.mpr hkt).symm.gcd_eq_one,
          (hp.coprime_iff_not_dvd.mpr hlt).symm.gcd_eq_one]

/-- **Sharp Prime Radical Collision Below $p - 1$ (`radical_prime_collision_below_totient`):**
For every prime $p$, $k = 1$ and $\ell = 2$ are incongruent modulo $p$, yet have
$\gcd(1 + t, p) = \gcd(2 + t, p) = 1$ for every $t$ with $t + 1 < p - 1 = \varphi(p)$. -/
theorem radical_prime_collision_below_totient {p : ℕ} (hp : p.Prime) :
    ¬ Nat.ModEq p 1 2 ∧
      ∀ t : ℕ, t + 1 < p.totient → Nat.gcd (1 + t) p = Nat.gcd (2 + t) p := by
  have h := gcd_prime_pow_collision_below_totient hp (a := 1) le_rfl
  simp only [pow_one, Nat.sub_self, pow_zero] at h
  exact h

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
