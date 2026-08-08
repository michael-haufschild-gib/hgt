import GaloisForLFunctions.HTGeometry.FactorialCompositionBound
import GaloisForLFunctions.HTGeometry.PowerSeriesEndpointExpansion

/-!
# The remainder of an endpoint expansion

The remainder term of an endpoint expansion is `[X^N] P(S)`, where every jet has been truncated at
degree `K = N − R`.  Every convolution index occurring in it is at most `K`, so the factorial
envelope loses the binomial factor `C(N, N−K) = C(N,R)`.

The bound is carried by the predicate

`TruncDom r a K B c G  :  ∀ n, ‖[X^n]G‖ · C(n, n−K)^r ≤ c (n+1)^B · (n!)^r a^n`,

which is stable under sums and under multiplying by a jet truncated at `K`.  The multiplication step
is exactly `choose_sub_le_mul_choose` together with the factorial identity
`(p!)^r (q!)^r C(n,q)^r = (n!)^r` for `p + q = n`.  Induction along constants, sums, and
multiplication by a variable therefore bounds the whole remainder, with a constant and a polynomial
weight independent of `K`.
-/

open MvPolynomial PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The factorial envelope -/

/-- The factorial envelope with exponent `r` and geometric ratio `a`. -/
def facEnv (r a : ℝ) (n : ℕ) : ℝ := ((n.factorial : ℕ) : ℝ) ^ r * a ^ n

theorem facEnv_pos {r a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < facEnv r a n := by
  have hf : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  rw [facEnv]
  positivity

@[simp]
theorem facEnv_zero (r a : ℝ) : facEnv r a 0 = 1 := by
  rw [facEnv]
  simp

/-- **The envelope splits along a convolution, at the cost of a binomial.** -/
theorem facEnv_mul_choose_rpow {r a : ℝ} {p q n : ℕ} (hpq : p + q = n) :
    facEnv r a p * facEnv r a q * (((n.choose q : ℕ) : ℝ)) ^ r = facEnv r a n := by
  have hq : q ≤ n := by omega
  have hnat : n.choose q * (q.factorial * p.factorial) = n.factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial hq
    have hp : n - q = p := by omega
    rw [hp] at h
    calc n.choose q * (q.factorial * p.factorial)
        = n.choose q * q.factorial * p.factorial := by ring
      _ = n.factorial := h
  have hcast : (((n.choose q : ℕ) : ℝ)) * ((((q.factorial : ℕ) : ℝ)) * (((p.factorial : ℕ) : ℝ)))
      = (((n.factorial : ℕ) : ℝ)) := by exact_mod_cast hnat
  have hpf : (0 : ℝ) ≤ ((p.factorial : ℕ) : ℝ) := by positivity
  have hqf : (0 : ℝ) ≤ ((q.factorial : ℕ) : ℝ) := by positivity
  have hcf : (0 : ℝ) ≤ ((n.choose q : ℕ) : ℝ) := by positivity
  have hrpow : (((p.factorial : ℕ) : ℝ)) ^ r * (((q.factorial : ℕ) : ℝ)) ^ r
      * (((n.choose q : ℕ) : ℝ)) ^ r = (((n.factorial : ℕ) : ℝ)) ^ r := by
    rw [← Real.mul_rpow hpf hqf, ← Real.mul_rpow (by positivity) hcf]
    congr 1
    rw [← hcast]
    ring
  have hpow : a ^ p * a ^ q = a ^ n := by
    rw [← pow_add, hpq]
  rw [facEnv, facEnv, facEnv]
  calc (((p.factorial : ℕ) : ℝ)) ^ r * a ^ p * ((((q.factorial : ℕ) : ℝ)) ^ r * a ^ q)
        * (((n.choose q : ℕ) : ℝ)) ^ r
      = ((((p.factorial : ℕ) : ℝ)) ^ r * (((q.factorial : ℕ) : ℝ)) ^ r
          * (((n.choose q : ℕ) : ℝ)) ^ r) * (a ^ p * a ^ q) := by ring
    _ = (((n.factorial : ℕ) : ℝ)) ^ r * a ^ n := by rw [hrpow, hpow]

/-! ## The truncated domination predicate -/

/-- `G` is dominated by the factorial envelope with polynomial weight `B` and constant `c`,
carrying the binomial saving of a truncation at height `K`. -/
def TruncDom (r a : ℝ) (K B : ℕ) (c : ℝ) (G : PowerSeries ℂ) : Prop :=
  ∀ n : ℕ, ‖PowerSeries.coeff n G‖ * (((n.choose (n - K) : ℕ) : ℝ)) ^ r
    ≤ c * ((n : ℝ) + 1) ^ B * facEnv r a n

theorem TruncDom.mono_const {r a : ℝ} {K B : ℕ} {c c' : ℝ} (hcc : c ≤ c') {G : PowerSeries ℂ}
    (h : TruncDom r a K B c G) (ha : 0 < a) : TruncDom r a K B c' G := by
  intro n
  refine le_trans (h n) ?_
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ B * facEnv r a n := by
    have := facEnv_pos (r := r) ha n
    positivity
  nlinarith

theorem TruncDom.mono_weight {r a : ℝ} {K B B' : ℕ} {c : ℝ} (hBB : B ≤ B') {G : PowerSeries ℂ}
    (h : TruncDom r a K B c G) (ha : 0 < a) (hc : 0 ≤ c) : TruncDom r a K B' c G := by
  intro n
  refine le_trans (h n) ?_
  have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hpow : ((n : ℝ) + 1) ^ B ≤ ((n : ℝ) + 1) ^ B' := pow_le_pow_right₀ hbase hBB
  have hfac : 0 < facEnv r a n := facEnv_pos (r := r) ha n
  have := mul_le_mul_of_nonneg_left hpow hc
  nlinarith

theorem truncDom_add {r a : ℝ} {K B : ℕ} {c₁ c₂ : ℝ} {G H : PowerSeries ℂ}
    (h₁ : TruncDom r a K B c₁ G) (h₂ : TruncDom r a K B c₂ H) :
    TruncDom r a K B (c₁ + c₂) (G + H) := by
  intro n
  have hnorm : ‖PowerSeries.coeff n (G + H)‖
      ≤ ‖PowerSeries.coeff n G‖ + ‖PowerSeries.coeff n H‖ := by
    rw [map_add]
    exact norm_add_le _ _
  have hbin : (0 : ℝ) ≤ (((n.choose (n - K) : ℕ) : ℝ)) ^ r := by positivity
  have := mul_le_mul_of_nonneg_right hnorm hbin
  have h1 := h₁ n
  have h2 := h₂ n
  nlinarith

/-! ## The multiplication step -/

theorem truncDom_mul_lowPart {r a : ℝ} (hr : 0 ≤ r) (ha : 0 < a) {K B₁ B₂ : ℕ} {c₁ c₂ : ℝ}
    (hc₂ : 0 ≤ c₂) {G : PowerSeries ℂ} (hG : TruncDom r a K B₁ c₁ G) {F : PowerSeries ℂ}
    (hF : ∀ n : ℕ, ‖PowerSeries.coeff n F‖ ≤ c₂ * ((n : ℝ) + 1) ^ B₂ * facEnv r a n) :
    TruncDom r a K (B₁ + B₂ + 1) (c₁ * c₂) (G * lowPart K F) := by
  have hc₁ : (0 : ℝ) ≤ c₁ := by
    have h0 := hG 0
    have hlhs : (0 : ℝ) ≤ ‖PowerSeries.coeff 0 G‖ * (((Nat.choose 0 (0 - K) : ℕ) : ℝ)) ^ r := by
      positivity
    have hnn := le_trans hlhs h0
    simpa using hnn
  intro n
  classical
  have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  -- the termwise estimate
  have hterm : ∀ p ∈ Finset.range (n + 1),
      ‖PowerSeries.coeff p G * PowerSeries.coeff (n - p) (lowPart K F)‖
          * (((n.choose (n - K) : ℕ) : ℝ)) ^ r
        ≤ c₁ * c₂ * ((n : ℝ) + 1) ^ (B₁ + B₂) * facEnv r a n := by
    intro p hp
    have hpn : p ≤ n := by
      have := Finset.mem_range.mp hp
      omega
    by_cases hq : n - p ≤ K
    · -- the truncation survives
      have hsplit : n.choose (n - K) ≤ n.choose (n - p) * p.choose (p - K) := by
        have h := choose_sub_le_mul_choose (n := n) (q := n - p) (K := K) (by omega) hq
        have hpq : n - (n - p) = p := by omega
        rwa [hpq] at h
      have hbincast : (((n.choose (n - K) : ℕ) : ℝ)) ^ r
          ≤ (((n.choose (n - p) : ℕ) : ℝ)) ^ r * (((p.choose (p - K) : ℕ) : ℝ)) ^ r := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        refine Real.rpow_le_rpow (by positivity) ?_ hr
        exact_mod_cast hsplit
      have hGp := hG p
      have hFq : ‖PowerSeries.coeff (n - p) (lowPart K F)‖
          ≤ c₂ * (((n - p : ℕ) : ℝ) + 1) ^ B₂ * facEnv r a (n - p) := by
        rw [coeff_lowPart, if_pos hq]
        exact hF (n - p)
      have hGnn : (0 : ℝ) ≤ ‖PowerSeries.coeff p G‖ := norm_nonneg _
      have hFnn : (0 : ℝ) ≤ ‖PowerSeries.coeff (n - p) (lowPart K F)‖ := norm_nonneg _
      have hkey := facEnv_mul_choose_rpow (r := r) (a := a)
        (p := p) (q := n - p) (n := n) (by omega)
      -- weights are monotone
      have hw1 : (((p : ℕ) : ℝ) + 1) ^ B₁ ≤ ((n : ℝ) + 1) ^ B₁ := by
        refine pow_le_pow_left₀ (by positivity) ?_ B₁
        have : ((p : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpn
        linarith
      have hw2 : (((n - p : ℕ) : ℝ) + 1) ^ B₂ ≤ ((n : ℝ) + 1) ^ B₂ := by
        refine pow_le_pow_left₀ (by positivity) ?_ B₂
        have : ((n - p : ℕ) : ℝ) ≤ (n : ℝ) := by
          have : (n - p : ℕ) ≤ n := by omega
          exact_mod_cast this
        linarith
      -- assemble
      have hprod : ‖PowerSeries.coeff p G * PowerSeries.coeff (n - p) (lowPart K F)‖
          * (((n.choose (n - K) : ℕ) : ℝ)) ^ r
          ≤ (‖PowerSeries.coeff p G‖ * (((p.choose (p - K) : ℕ) : ℝ)) ^ r)
            * (‖PowerSeries.coeff (n - p) (lowPart K F)‖)
            * (((n.choose (n - p) : ℕ) : ℝ)) ^ r := by
        rw [norm_mul]
        have hnn : (0 : ℝ) ≤ ‖PowerSeries.coeff p G‖
            * ‖PowerSeries.coeff (n - p) (lowPart K F)‖ := by positivity
        calc ‖PowerSeries.coeff p G‖ * ‖PowerSeries.coeff (n - p) (lowPart K F)‖
              * (((n.choose (n - K) : ℕ) : ℝ)) ^ r
            ≤ ‖PowerSeries.coeff p G‖ * ‖PowerSeries.coeff (n - p) (lowPart K F)‖
              * ((((n.choose (n - p) : ℕ) : ℝ)) ^ r * (((p.choose (p - K) : ℕ) : ℝ)) ^ r) :=
              mul_le_mul_of_nonneg_left hbincast hnn
          _ = (‖PowerSeries.coeff p G‖ * (((p.choose (p - K) : ℕ) : ℝ)) ^ r)
              * (‖PowerSeries.coeff (n - p) (lowPart K F)‖)
              * (((n.choose (n - p) : ℕ) : ℝ)) ^ r := by ring
      refine le_trans hprod ?_
      have hbinnn : (0 : ℝ) ≤ (((n.choose (n - p) : ℕ) : ℝ)) ^ r := by positivity
      have hAnn : (0 : ℝ) ≤ c₁ * ((p : ℝ) + 1) ^ B₁ * facEnv r a p := by
        have := facEnv_pos (r := r) ha p
        positivity
      have hstep1 : (‖PowerSeries.coeff p G‖ * (((p.choose (p - K) : ℕ) : ℝ)) ^ r)
          * (‖PowerSeries.coeff (n - p) (lowPart K F)‖)
          * (((n.choose (n - p) : ℕ) : ℝ)) ^ r
          ≤ (c₁ * ((p : ℝ) + 1) ^ B₁ * facEnv r a p)
            * (c₂ * (((n - p : ℕ) : ℝ) + 1) ^ B₂ * facEnv r a (n - p))
            * (((n.choose (n - p) : ℕ) : ℝ)) ^ r := by
        refine mul_le_mul_of_nonneg_right ?_ hbinnn
        calc (‖PowerSeries.coeff p G‖ * (((p.choose (p - K) : ℕ) : ℝ)) ^ r)
              * ‖PowerSeries.coeff (n - p) (lowPart K F)‖
            ≤ (c₁ * ((p : ℝ) + 1) ^ B₁ * facEnv r a p)
              * ‖PowerSeries.coeff (n - p) (lowPart K F)‖ :=
              mul_le_mul_of_nonneg_right hGp hFnn
          _ ≤ (c₁ * ((p : ℝ) + 1) ^ B₁ * facEnv r a p)
              * (c₂ * (((n - p : ℕ) : ℝ) + 1) ^ B₂ * facEnv r a (n - p)) :=
              mul_le_mul_of_nonneg_left hFq hAnn
      refine le_trans hstep1 ?_
      have hfinal : (c₁ * ((p : ℝ) + 1) ^ B₁ * facEnv r a p)
          * (c₂ * (((n - p : ℕ) : ℝ) + 1) ^ B₂ * facEnv r a (n - p))
          * (((n.choose (n - p) : ℕ) : ℝ)) ^ r
          = c₁ * c₂ * (((p : ℝ) + 1) ^ B₁ * (((n - p : ℕ) : ℝ) + 1) ^ B₂)
            * (facEnv r a p * facEnv r a (n - p) * (((n.choose (n - p) : ℕ) : ℝ)) ^ r) := by
        ring
      rw [hfinal, hkey]
      have hwprod : ((p : ℝ) + 1) ^ B₁ * (((n - p : ℕ) : ℝ) + 1) ^ B₂
          ≤ ((n : ℝ) + 1) ^ B₁ * ((n : ℝ) + 1) ^ B₂ :=
        mul_le_mul hw1 hw2 (by positivity) (by positivity)
      have hfacn : 0 < facEnv r a n := facEnv_pos (r := r) ha n
      have hmul := mul_le_mul_of_nonneg_left hwprod (mul_nonneg hc₁ hc₂)
      calc c₁ * c₂ * (((p : ℝ) + 1) ^ B₁ * (((n - p : ℕ) : ℝ) + 1) ^ B₂) * facEnv r a n
          = (c₁ * c₂ * (((p : ℝ) + 1) ^ B₁ * (((n - p : ℕ) : ℝ) + 1) ^ B₂)) * facEnv r a n := by
            ring
        _ ≤ (c₁ * c₂ * (((n : ℝ) + 1) ^ B₁ * ((n : ℝ) + 1) ^ B₂)) * facEnv r a n :=
            mul_le_mul_of_nonneg_right hmul (le_of_lt hfacn)
        _ = c₁ * c₂ * ((n : ℝ) + 1) ^ (B₁ + B₂) * facEnv r a n := by
            rw [← pow_add]
    · -- the truncation kills the term
      rw [coeff_lowPart, if_neg hq, mul_zero, norm_zero, zero_mul]
      have hfacn : 0 < facEnv r a n := facEnv_pos (r := r) ha n
      positivity
  -- sum the estimate
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hbin : (0 : ℝ) ≤ (((n.choose (n - K) : ℕ) : ℝ)) ^ r := by positivity
  have hsum : ‖∑ p ∈ Finset.range (n + 1),
      PowerSeries.coeff p G * PowerSeries.coeff (n - p) (lowPart K F)‖
      ≤ ∑ p ∈ Finset.range (n + 1),
        ‖PowerSeries.coeff p G * PowerSeries.coeff (n - p) (lowPart K F)‖ :=
    norm_sum_le _ _
  calc ‖∑ p ∈ Finset.range (n + 1),
          PowerSeries.coeff p G * PowerSeries.coeff (n - p) (lowPart K F)‖
        * (((n.choose (n - K) : ℕ) : ℝ)) ^ r
      ≤ (∑ p ∈ Finset.range (n + 1),
          ‖PowerSeries.coeff p G * PowerSeries.coeff (n - p) (lowPart K F)‖)
        * (((n.choose (n - K) : ℕ) : ℝ)) ^ r := mul_le_mul_of_nonneg_right hsum hbin
    _ = ∑ p ∈ Finset.range (n + 1),
          ‖PowerSeries.coeff p G * PowerSeries.coeff (n - p) (lowPart K F)‖
            * (((n.choose (n - K) : ℕ) : ℝ)) ^ r := by rw [Finset.sum_mul]
    _ ≤ ∑ _p ∈ Finset.range (n + 1), c₁ * c₂ * ((n : ℝ) + 1) ^ (B₁ + B₂) * facEnv r a n :=
        Finset.sum_le_sum hterm
    _ = ((n : ℝ) + 1) * (c₁ * c₂ * ((n : ℝ) + 1) ^ (B₁ + B₂) * facEnv r a n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = c₁ * c₂ * ((n : ℝ) + 1) ^ (B₁ + B₂ + 1) * facEnv r a n := by
        rw [pow_succ]
        ring

/-! ## The remainder bound -/

/-- **The remainder of an endpoint expansion is dominated with the full binomial saving.**
The constant and the polynomial weight depend only on the differential polynomial and on the jet
bounds, not on the truncation height. -/
theorem exists_truncDom_aeval {σ : Type*} [Fintype σ] [DecidableEq σ] {r a : ℝ} (hr : 0 ≤ r)
    (ha : 0 < a) (jets : σ → PowerSeries ℂ) {B : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hjet : ∀ (i : σ) (n : ℕ),
      ‖PowerSeries.coeff n (jets i)‖ ≤ c * ((n : ℝ) + 1) ^ B * facEnv r a n)
    (P : MvPolynomial σ ℂ) :
    ∃ (B' : ℕ) (c' : ℝ), 0 ≤ c' ∧ ∀ K : ℕ,
      TruncDom r a K B' c' (aeval (fun i => lowPart K (jets i)) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C z =>
      refine ⟨0, ‖z‖, norm_nonneg z, fun K n => ?_⟩
      rw [MvPolynomial.aeval_C]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have hc0 : (Nat.choose 0 (0 - K) : ℕ) = 1 := by simp
        rw [hc0]
        simp
      · have hzero : PowerSeries.coeff n
            ((algebraMap ℂ (PowerSeries ℂ)) z) = 0 := by
          simp [PowerSeries.coeff_C, Nat.ne_of_gt hn]
        rw [hzero, norm_zero, zero_mul]
        have := facEnv_pos (r := r) ha n
        positivity
  | add p q hp hq =>
      obtain ⟨B₁, c₁, hc₁, h₁⟩ := hp
      obtain ⟨B₂, c₂, hc₂, h₂⟩ := hq
      refine ⟨max B₁ B₂, c₁ + c₂, by linarith, fun K => ?_⟩
      rw [map_add]
      exact truncDom_add ((h₁ K).mono_weight (le_max_left _ _) ha hc₁)
        ((h₂ K).mono_weight (le_max_right _ _) ha hc₂)
  | mul_X p i hp =>
      obtain ⟨B₁, c₁, hc₁, h₁⟩ := hp
      refine ⟨B₁ + B + 1, c₁ * c, by positivity, fun K => ?_⟩
      rw [map_mul, MvPolynomial.aeval_X]
      exact truncDom_mul_lowPart hr ha hc (h₁ K) (hjet i)

end

end GaloisForLFunctions.HTGeometry
