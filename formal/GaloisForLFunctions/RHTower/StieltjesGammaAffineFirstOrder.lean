import GaloisForLFunctions.RHTower.RegularizedDivisorHarmonicLimit

/-!
# The γ-affine structure of the first-order Stieltjes prime lane

For a prime `p` the first-order generalized Stieltjes structure constant is the regularized limit

```text
A_{1,p} = reg-lim_{x → ∞} ( ∑_{k ≤ x} v_p(k)/k − (log x)/(p−1) ).
```

This file proves that limit exists and computes it exactly:

```text
A_{1,p} = γ/(p−1) − (log p)·p/(p−1)² .
```

So the individual finite-support Stieltjes structure constant is `ℚ`-linear in `{γ, log p}` — the
banked elementary content of the γ-affine structure card, at first order, with the exact rational
coefficients `1/(p−1)` and `−p/(p−1)²`.

The mechanism is the prime-power ladder.  Because `v_p(k)` counts the powers of `p` dividing `k`,

```text
∑_{k ≤ N} v_p(k)/k = ∑_{i ≥ 1} p^{-i} H_{⌊N/p^i⌋}    (`sum_padicValNat_div_eq_ladder`),
```

a finite sum.  Each rung is compared with its two-lane model value
`p^{-i}(log N + γ − i log p)`, whose full ladder sums in closed form to
`(log N + γ)/(p−1) − (log p) p/(p−1)²` (`tsum_modelTerm`).  The comparison error splits at
`I = ⌊log_p N⌋`: below `I` every rung is within `4/N` of its model, and above `I` the ladder rung
vanishes while the model tail is `O((log N)/N)` (`abs_tsum_ladderSubModel_le`).  Both go to zero,
which gives the limit.

Nothing here is an RH statement.  The regularization calculation is elementary; the content is the
exact `γ`/`log p` decomposition with rational coefficients, which is what makes the individual
`A_β` lanes γ-affine — and which, by
`RHTower.StieltjesLaneCutoffDivergence`, is exactly what fails to survive the infinite prime
assembly into `γ₁`.
-/

open Finset Filter Topology

namespace RHTower
namespace StieltjesGammaAffine

noncomputable section

/-! ### The prime-power ladder identity -/

/-- The reciprocal sum over the multiples of `d` in `[1, N]` is the shifted harmonic number. -/
theorem sum_inv_multiples_eq_harmonic (N d : ℕ) (hd : 1 ≤ d) :
    (∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·), (n : ℚ)⁻¹) =
      (d : ℚ)⁻¹ * harmonic (N / d) := by
  rw [harmonic_eq_sum_Icc, Finset.mul_sum]
  refine (Finset.sum_bij' (fun k _ => d * k) (fun n _ => n / d) ?_ ?_ ?_ ?_ ?_).symm
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_filter] at hk ⊢
    refine ⟨⟨?_, ?_⟩, ⟨k, rfl⟩⟩
    · exact Nat.mul_pos (by omega) (by omega)
    · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hk.2
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    rcases hn with ⟨⟨hn1, hnN⟩, hdn⟩
    exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdn) (by omega), Nat.div_le_div_right hnN⟩
  · intro k _hk
    exact Nat.mul_div_cancel_left k (by omega)
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro k _hk
    simp [Nat.cast_mul]
    ring

/-- The `p`-adic valuation counts the powers of `p` dividing `k`, cut at any bound above it. -/
theorem card_filter_pow_dvd {p k M : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (hM : padicValNat p k ≤ M) :
    ((Finset.Icc 1 M).filter (fun i => p ^ i ∣ k)).card = padicValNat p k := by
  have hmem : ∀ i, i ∈ (Finset.Icc 1 M).filter (fun i => p ^ i ∣ k)
      ↔ i ∈ Finset.Icc 1 (padicValNat p k) := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [hp.pow_dvd_iff_le_factorization hk, Nat.factorization_def _ hp]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, le_trans h.2 hM⟩, h.2⟩
  rw [Finset.filter_congr_decidable]
  rw [show (Finset.Icc 1 M).filter (fun i => p ^ i ∣ k) = Finset.Icc 1 (padicValNat p k) from
    Finset.ext hmem]
  simp

/-- **Valuation-weighted harmonic sum as a prime-power ladder.**
`∑_{k ≤ N} v_p(k)/k = ∑_{i=1}^{N} p^{-i} H_{⌊N/p^i⌋}`. -/
theorem sum_padicValNat_div_eq_ladder {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (padicValNat p k : ℚ) / k)
      = ∑ i ∈ Finset.Icc 1 N, ((p : ℚ) ^ i)⁻¹ * harmonic (N / p ^ i) := by
  have hstep : ∀ k ∈ Finset.Icc 1 N, (padicValNat p k : ℚ) / k
      = ∑ i ∈ Finset.Icc 1 N, (if p ^ i ∣ k then (1 : ℚ) else 0) / k := by
    intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    have hk0 : k ≠ 0 := by omega
    have hval : padicValNat p k ≤ N := by
      have hdvd : p ^ (padicValNat p k) ∣ k := pow_padicValNat_dvd
      have hle : p ^ (padicValNat p k) ≤ k := Nat.le_of_dvd (by omega) hdvd
      have h2 : 2 ^ (padicValNat p k) ≤ p ^ (padicValNat p k) :=
        Nat.pow_le_pow_left hp.two_le _
      have h3 : padicValNat p k < 2 ^ (padicValNat p k) := Nat.lt_two_pow_self
      omega
    rw [← Finset.sum_div, Finset.sum_boole, card_filter_pow_dvd hp hk0 hval]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hppos : 1 ≤ p ^ i := Nat.one_le_pow _ _ hp.pos
  have hkey := sum_inv_multiples_eq_harmonic N (p ^ i) hppos
  rw [Finset.sum_filter] at hkey
  push_cast at hkey
  rw [← hkey]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : p ^ i ∣ k
  · rw [if_pos h, if_pos h, one_div]
  · rw [if_neg h, if_neg h, zero_div]




/-! ### The ladder and its two-lane model -/

variable {p : ℕ}

/-- The `i+1`-st rung of the prime-power ladder `p^{-(i+1)} H_{⌊N/p^{i+1}⌋}`. -/
def ladderTerm (p N i : ℕ) : ℝ :=
  ((p : ℝ)⁻¹) ^ (i + 1) * (harmonic (N / p ^ (i + 1)) : ℝ)

/-- The `i+1`-st rung of the two-lane model `p^{-(i+1)}(log N + γ − (i+1) log p)`. -/
def modelTerm (p N i : ℕ) : ℝ :=
  ((p : ℝ)⁻¹) ^ (i + 1) *
    (Real.log N + Real.eulerMascheroniConstant - ((i : ℝ) + 1) * Real.log p)

lemma ratio_lt_one (hp : p.Prime) : ‖((p : ℝ)⁻¹)‖ < 1 := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [inv_lt_one_iff₀]
  right; linarith

lemma ratio_nonneg : (0 : ℝ) ≤ ((p : ℝ)⁻¹) := by positivity

lemma summable_modelTerm (hp : p.Prime) (N : ℕ) : Summable (modelTerm p N) := by
  have hr := ratio_lt_one hp
  have h1 : Summable (fun i : ℕ => ((p : ℝ)⁻¹) ^ i) := by
    refine summable_geometric_of_lt_one ratio_nonneg ?_
    have := hr
    rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((p:ℝ)⁻¹))] at this
  have h2 : Summable (fun i : ℕ => (i : ℝ) ^ 1 * ((p : ℝ)⁻¹) ^ i) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hrep : ∀ i : ℕ, modelTerm p N i
      = (Real.log N + Real.eulerMascheroniConstant - Real.log p) *
          (((p : ℝ)⁻¹) * ((p : ℝ)⁻¹) ^ i)
        - Real.log p * (((p : ℝ)⁻¹) * ((i : ℝ) ^ 1 * ((p : ℝ)⁻¹) ^ i)) := by
    intro i
    rw [modelTerm, pow_succ]
    ring
  rw [show modelTerm p N = fun i : ℕ =>
      (Real.log N + Real.eulerMascheroniConstant - Real.log p) *
        (((p : ℝ)⁻¹) * ((p : ℝ)⁻¹) ^ i)
      - Real.log p * (((p : ℝ)⁻¹) * ((i : ℝ) ^ 1 * ((p : ℝ)⁻¹) ^ i)) from funext hrep]
  exact ((h1.mul_left _).mul_left _).sub ((h2.mul_left _).mul_left _)

lemma tsum_modelTerm (hp : p.Prime) (N : ℕ) :
    ∑' i, modelTerm p N i
      = (Real.log N + Real.eulerMascheroniConstant) / ((p : ℝ) - 1)
        - Real.log p * (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  have hr := ratio_lt_one hp
  have hrabs : ((p : ℝ)⁻¹) < 1 := by
    have := hr
    rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((p:ℝ)⁻¹))] at this
  have h1 : Summable (fun i : ℕ => ((p : ℝ)⁻¹) ^ i) :=
    summable_geometric_of_lt_one ratio_nonneg hrabs
  have h2 : Summable (fun i : ℕ => (i : ℝ) ^ 1 * ((p : ℝ)⁻¹) ^ i) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpne : (p : ℝ) ≠ 0 := by positivity
  have hpm : (p : ℝ) - 1 ≠ 0 := by intro h; nlinarith
  have hgeo : ∑' i : ℕ, ((p : ℝ)⁻¹) ^ i = (1 - (p : ℝ)⁻¹)⁻¹ :=
    tsum_geometric_of_lt_one ratio_nonneg hrabs
  have hlin : ∑' i : ℕ, (i : ℝ) * ((p : ℝ)⁻¹) ^ i
      = ((p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hr
  have hrep : ∀ i : ℕ, modelTerm p N i
      = (Real.log N + Real.eulerMascheroniConstant - Real.log p) *
          (((p : ℝ)⁻¹) * ((p : ℝ)⁻¹) ^ i)
        - Real.log p * (((p : ℝ)⁻¹) * ((i : ℝ) * ((p : ℝ)⁻¹) ^ i)) := by
    intro i
    rw [modelTerm, pow_succ]
    ring
  have h2' : Summable (fun i : ℕ => (i : ℝ) * ((p : ℝ)⁻¹) ^ i) := by
    simpa using h2
  rw [show modelTerm p N = fun i : ℕ =>
      (Real.log N + Real.eulerMascheroniConstant - Real.log p) *
        (((p : ℝ)⁻¹) * ((p : ℝ)⁻¹) ^ i)
      - Real.log p * (((p : ℝ)⁻¹) * ((i : ℝ) * ((p : ℝ)⁻¹) ^ i)) from funext hrep]
  rw [Summable.tsum_sub ((h1.mul_left _).mul_left _) ((h2'.mul_left _).mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left, hgeo, hlin]
  have hone : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / (p : ℝ) := by
    field_simp
  rw [hone]
  field_simp
  ring

/-- Exact value of a shifted arithmetico-geometric tail. -/
lemma tsum_shifted_linear_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (C L : ℝ) (k : ℕ) :
    ∑' i : ℕ, r ^ (i + k) * (C + (i : ℝ) * L)
      = r ^ k * (C * (1 - r)⁻¹ + L * (r / (1 - r) ^ 2)) := by
  have hrn : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have h1 : Summable (fun i : ℕ => r ^ i) := summable_geometric_of_lt_one hr0 hr1
  have h2 : Summable (fun i : ℕ => (i : ℝ) * r ^ i) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hrn
  have hgeo : ∑' i : ℕ, r ^ i = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
  have hlin : ∑' i : ℕ, (i : ℝ) * r ^ i = r / (1 - r) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hrn
  have hrep : ∀ i : ℕ, r ^ (i + k) * (C + (i : ℝ) * L)
      = (r ^ k * C) * r ^ i + (r ^ k * L) * ((i : ℝ) * r ^ i) := by
    intro i
    rw [pow_add]
    ring
  rw [show (fun i : ℕ => r ^ (i + k) * (C + (i : ℝ) * L))
      = fun i : ℕ => (r ^ k * C) * r ^ i + (r ^ k * L) * ((i : ℝ) * r ^ i) from funext hrep]
  rw [Summable.tsum_add (h1.mul_left _) (h2.mul_left _), tsum_mul_left, tsum_mul_left,
    hgeo, hlin]
  ring

/-! ### The ladder as a convergent series -/

lemma ladderTerm_eq_zero_of_lt {N i : ℕ} (hlt : N < p ^ (i + 1)) : ladderTerm p N i = 0 := by
  rw [ladderTerm, Nat.div_eq_of_lt hlt]
  simp

lemma ladderTerm_eq_zero_of_le {N i : ℕ} (hp : p.Prime) (hi : N ≤ i) : ladderTerm p N i = 0 := by
  refine ladderTerm_eq_zero_of_lt ?_
  have h1 : i + 1 < 2 ^ (i + 1) := Nat.lt_two_pow_self
  have h2 : (2 : ℕ) ^ (i + 1) ≤ p ^ (i + 1) := Nat.pow_le_pow_left hp.two_le _
  omega

lemma summable_ladderTerm (hp : p.Prime) (N : ℕ) : Summable (ladderTerm p N) :=
  summable_of_ne_finset_zero (s := Finset.range N)
    fun i hi => ladderTerm_eq_zero_of_le hp (by simpa using hi)



/-- **The valuation-weighted harmonic sum is the ladder series.** -/
theorem sum_padicValNat_div_real_eq_tsum (hp : p.Prime) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (padicValNat p k : ℝ) / k) = ∑' i, ladderTerm p N i := by
  have hzero : ∀ i ∉ Finset.range N, ladderTerm p N i = 0 :=
    fun i hi => ladderTerm_eq_zero_of_le hp (by simpa using hi)
  rw [tsum_eq_sum hzero]
  have hcast : (∑ k ∈ Finset.Icc 1 N, (padicValNat p k : ℝ) / k)
      = ((∑ k ∈ Finset.Icc 1 N, (padicValNat p k : ℚ) / (k : ℚ) : ℚ) : ℝ) := by
    push_cast
    ring
  rw [hcast, sum_padicValNat_div_eq_ladder hp N,
    RegularizedDivisorHarmonic.sum_Icc_one_eq_sum_range
      (fun i => ((p : ℚ) ^ i)⁻¹ * harmonic (N / p ^ i)) N]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ladderTerm, inv_pow]

/-! ### The comparison error -/

lemma abs_ladderTerm_sub_modelTerm_le_of_pow_le {N i : ℕ} (hp : p.Prime)
    (hpi : p ^ (i + 1) ≤ N) : |ladderTerm p N i - modelTerm p N i| ≤ 4 / N := by
  have hd1 : 1 ≤ p ^ (i + 1) := Nat.one_le_pow _ _ hp.pos
  have hN1 : 1 ≤ N := le_trans hd1 hpi
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := hN1
    exact_mod_cast this
  have hdR : (0 : ℝ) < ((p ^ (i + 1) : ℕ) : ℝ) := by
    have : (0 : ℕ) < p ^ (i + 1) := hd1
    exact_mod_cast this
  have hlogd : Real.log ((p ^ (i + 1) : ℕ) : ℝ) = ((i : ℝ) + 1) * Real.log p := by
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  have hfac : ((p : ℝ)⁻¹) ^ (i + 1) = (((p ^ (i + 1) : ℕ)) : ℝ)⁻¹ := by
    rw [inv_pow]
    congr 1
    push_cast
    ring
  have hdiff : ladderTerm p N i - modelTerm p N i
      = (((p ^ (i + 1) : ℕ)) : ℝ)⁻¹ *
        ((harmonic (N / p ^ (i + 1)) : ℝ) - Real.log ((N : ℝ) / ((p ^ (i + 1) : ℕ) : ℝ))
          - Real.eulerMascheroniConstant) := by
    rw [ladderTerm, modelTerm, hfac, Real.log_div (ne_of_gt hNR) (ne_of_gt hdR), hlogd]
    ring
  have hkey := RegularizedDivisorHarmonic.abs_harmonic_sub_log_div_le hd1 hpi
  rw [hdiff, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((p ^ (i + 1) : ℕ)) : ℝ)⁻¹)]
  calc (((p ^ (i + 1) : ℕ)) : ℝ)⁻¹ *
        |(harmonic (N / p ^ (i + 1)) : ℝ) - Real.log ((N : ℝ) / ((p ^ (i + 1) : ℕ) : ℝ))
          - Real.eulerMascheroniConstant|
      ≤ (((p ^ (i + 1) : ℕ)) : ℝ)⁻¹ * (4 * ((p ^ (i + 1) : ℕ) : ℝ) / N) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 4 / N := by field_simp

lemma abs_modelTerm_le (N i : ℕ) (hp : p.Prime) (hN : 1 ≤ N) :
    |modelTerm p N i| ≤ ((p : ℝ)⁻¹) ^ (i + 1) *
      ((Real.log N + |Real.eulerMascheroniConstant|) + ((i : ℝ) + 1) * Real.log p) := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  rw [modelTerm, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((p : ℝ)⁻¹) ^ (i + 1))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : |Real.log N + Real.eulerMascheroniConstant - ((i : ℝ) + 1) * Real.log p|
      ≤ |Real.log N + Real.eulerMascheroniConstant| + |((i : ℝ) + 1) * Real.log p| :=
    abs_sub _ _
  have h2 : |Real.log N + Real.eulerMascheroniConstant|
      ≤ Real.log N + |Real.eulerMascheroniConstant| := by
    calc |Real.log N + Real.eulerMascheroniConstant|
        ≤ |Real.log N| + |Real.eulerMascheroniConstant| := abs_add_le _ _
      _ = Real.log N + |Real.eulerMascheroniConstant| := by rw [abs_of_nonneg hlogN]
  have h3 : |((i : ℝ) + 1) * Real.log p| = ((i : ℝ) + 1) * Real.log p :=
    abs_of_nonneg (by positivity)
  linarith

/-- The explicit comparison-error majorant. -/
def errorMajorant (p N : ℕ) : ℝ :=
  4 * Real.log N / (Real.log p * N)
    + (4 * Real.log N + 2 * |Real.eulerMascheroniConstant| + 4 * Real.log p) / N

set_option maxHeartbeats 2000000 in
theorem abs_tsum_ladderSubModel_le (hp : p.Prime) {N : ℕ} (hN : 1 ≤ N) :
    |∑' i, (ladderTerm p N i - modelTerm p N i)| ≤ errorMajorant p N := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := hN
    exact_mod_cast this
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hrabs : ((p : ℝ)⁻¹) < 1 := by
    have h := ratio_lt_one (p := p) hp
    rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((p : ℝ)⁻¹))] at h
  set I := Nat.log p N with hIdef
  set f : ℕ → ℝ := fun i => ladderTerm p N i - modelTerm p N i with hfdef
  have hsumf : Summable f := (summable_ladderTerm hp N).sub (summable_modelTerm hp N)
  have hpowI : p ^ I ≤ N := Nat.pow_log_le_self p (by omega)
  have hpowI1 : N < p ^ (I + 1) := Nat.lt_pow_succ_log_self hp.one_lt N
  have hIlog : (I : ℝ) * Real.log p ≤ Real.log N := by
    have h1 : Real.log (((p ^ I : ℕ)) : ℝ) ≤ Real.log N := by
      refine Real.log_le_log ?_ (by exact_mod_cast hpowI)
      have : (0 : ℕ) < p ^ I := Nat.one_le_pow _ _ hp.pos
      exact_mod_cast this
    rw [show (((p ^ I : ℕ)) : ℝ) = (p : ℝ) ^ I from by push_cast; ring, Real.log_pow] at h1
    exact h1
  -- head bound
  have hhead : |∑ i ∈ Finset.range I, f i| ≤ 4 * Real.log N / (Real.log p * N) := by
    have hterm : ∀ i ∈ Finset.range I, |f i| ≤ 4 / N := by
      intro i hi
      have hle : p ^ (i + 1) ≤ p ^ I :=
        Nat.pow_le_pow_right hp.pos (by simpa using Finset.mem_range.mp hi)
      exact abs_ladderTerm_sub_modelTerm_le_of_pow_le hp (le_trans hle hpowI)
    have hstep : |∑ i ∈ Finset.range I, f i| ≤ (I : ℝ) * (4 / N) := by
      calc |∑ i ∈ Finset.range I, f i| ≤ ∑ i ∈ Finset.range I, |f i| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ Finset.range I, (4 / (N : ℝ)) := Finset.sum_le_sum hterm
        _ = (I : ℝ) * (4 / N) := by rw [Finset.sum_const, Finset.card_range]; ring
    refine le_trans hstep ?_
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < Real.log p * (N : ℝ))]
    calc (I : ℝ) * (4 / N) * (Real.log p * N) = ((I : ℝ) * Real.log p) * 4 := by
          field_simp
      _ ≤ Real.log N * 4 := by nlinarith
      _ = 4 * Real.log N := by ring
  -- tail bound
  have htailzero : ∀ i : ℕ, ladderTerm p N (i + I) = 0 := by
    intro i
    refine ladderTerm_eq_zero_of_lt ?_
    have h1 : p ^ (I + 1) ≤ p ^ (i + I + 1) :=
      Nat.pow_le_pow_right hp.pos (by omega)
    omega
  set C : ℝ := (Real.log N + |Real.eulerMascheroniConstant|) + ((I : ℝ) + 1) * Real.log p with hC
  have hCnn : 0 ≤ C := by
    have : (0 : ℝ) ≤ ((I : ℝ) + 1) * Real.log p := by positivity
    have h2 : (0 : ℝ) ≤ |Real.eulerMascheroniConstant| := abs_nonneg _
    simp only [hC]
    linarith
  have htailterm : ∀ i : ℕ,
      |f (i + I)| ≤ ((p : ℝ)⁻¹) ^ (i + (I + 1)) * (C + (i : ℝ) * Real.log p) := by
    intro i
    have h0 : f (i + I) = -modelTerm p N (i + I) := by
      simp only [hfdef, htailzero i]
      ring
    rw [h0, abs_neg]
    refine le_trans (abs_modelTerm_le N (i + I) hp hN) ?_
    have hexp : ((i : ℕ) + I + 1) = i + (I + 1) := by omega
    rw [hexp]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : (((i + I : ℕ) : ℝ) + 1) * Real.log p
        = ((I : ℝ) + 1) * Real.log p + (i : ℝ) * Real.log p := by push_cast; ring
    simp only [hC]
    rw [this]
    ring_nf
    linarith
  have hsummableTail : Summable (fun i : ℕ => |f (i + I)|) :=
    ((summable_nat_add_iff I).mpr hsumf).abs
  have hsummableBound : Summable
      (fun i : ℕ => ((p : ℝ)⁻¹) ^ (i + (I + 1)) * (C + (i : ℝ) * Real.log p)) := by
    have hrn : ‖((p : ℝ)⁻¹)‖ < 1 := ratio_lt_one hp
    have h1 : Summable (fun i : ℕ => ((p : ℝ)⁻¹) ^ i) :=
      summable_geometric_of_lt_one ratio_nonneg hrabs
    have h2 : Summable (fun i : ℕ => (i : ℝ) * ((p : ℝ)⁻¹) ^ i) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hrn
    have hrep : ∀ i : ℕ, ((p : ℝ)⁻¹) ^ (i + (I + 1)) * (C + (i : ℝ) * Real.log p)
        = (((p : ℝ)⁻¹) ^ (I + 1) * C) * ((p : ℝ)⁻¹) ^ i
          + (((p : ℝ)⁻¹) ^ (I + 1) * Real.log p) * ((i : ℝ) * ((p : ℝ)⁻¹) ^ i) := by
      intro i
      rw [pow_add]
      ring
    rw [show (fun i : ℕ => ((p : ℝ)⁻¹) ^ (i + (I + 1)) * (C + (i : ℝ) * Real.log p))
        = fun i : ℕ => (((p : ℝ)⁻¹) ^ (I + 1) * C) * ((p : ℝ)⁻¹) ^ i
          + (((p : ℝ)⁻¹) ^ (I + 1) * Real.log p) * ((i : ℝ) * ((p : ℝ)⁻¹) ^ i)
        from funext hrep]
    exact (h1.mul_left _).add (h2.mul_left _)
  have htail : |∑' i, f (i + I)|
      ≤ (4 * Real.log N + 2 * |Real.eulerMascheroniConstant| + 4 * Real.log p) / N := by
    have hstep1 : |∑' i, f (i + I)| ≤ ∑' i, |f (i + I)| := by
      have h := norm_tsum_le_tsum_norm (f := fun i : ℕ => f (i + I))
        (by simpa [Real.norm_eq_abs] using hsummableTail)
      simpa [Real.norm_eq_abs] using h
    have hstep2 : ∑' i, |f (i + I)|
        ≤ ∑' i, ((p : ℝ)⁻¹) ^ (i + (I + 1)) * (C + (i : ℝ) * Real.log p) :=
      Summable.tsum_le_tsum htailterm hsummableTail hsummableBound
    have hval := tsum_shifted_linear_geometric (r := (p : ℝ)⁻¹) ratio_nonneg hrabs C
      (Real.log p) (I + 1)
    rw [hval] at hstep2
    -- numeric bound
    have hone : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / (p : ℝ) := by field_simp
    have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hA : (1 - (p : ℝ)⁻¹)⁻¹ ≤ 2 := by
      rw [hone, inv_div]
      rw [div_le_iff₀ hpm]
      linarith
    have hpne : (p : ℝ) ≠ 0 := by positivity
    have hp1ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hpm
    have hB : ((p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2 ≤ 2 := by
      have hval : ((p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2 = (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
        rw [hone]
        field_simp
      rw [hval, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (p : ℝ) - 1)
        (by linarith : (0 : ℝ) ≤ (p : ℝ) - 2)]
    have hQnn : (0 : ℝ) ≤ C * (1 - (p : ℝ)⁻¹)⁻¹ + Real.log p * (((p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2) := by
      have h1 : (0 : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
        rw [hone]; positivity
      have h2 : (0 : ℝ) ≤ ((p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2 := by
        rw [hone]; positivity
      have := hlogp.le
      positivity
    have hQ : C * (1 - (p : ℝ)⁻¹)⁻¹ + Real.log p * (((p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2)
        ≤ 2 * C + 2 * Real.log p := by
      have h1 : C * (1 - (p : ℝ)⁻¹)⁻¹ ≤ C * 2 := by
        exact mul_le_mul_of_nonneg_left hA hCnn
      have h2 : Real.log p * (((p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2) ≤ Real.log p * 2 :=
        mul_le_mul_of_nonneg_left hB hlogp.le
      linarith
    have hrpow : ((p : ℝ)⁻¹) ^ (I + 1) ≤ 1 / N := by
      have hlt : (N : ℝ) ≤ (p : ℝ) ^ (I + 1) := by
        have h := hpowI1
        have hcast : ((N : ℕ) : ℝ) < ((p ^ (I + 1) : ℕ) : ℝ) := by exact_mod_cast h
        rw [show (((p ^ (I + 1) : ℕ)) : ℝ) = (p : ℝ) ^ (I + 1) from by push_cast; ring] at hcast
        exact hcast.le
      rw [inv_pow, one_div]
      exact (inv_le_inv₀ (by positivity) hNR).mpr hlt
    have hCbound : 2 * C + 2 * Real.log p
        ≤ 4 * Real.log N + 2 * |Real.eulerMascheroniConstant| + 4 * Real.log p := by
      simp only [hC]
      nlinarith [hIlog, hlogp.le]
    calc |∑' i, f (i + I)| ≤ ((p : ℝ)⁻¹) ^ (I + 1) *
            (C * (1 - (p : ℝ)⁻¹)⁻¹ + Real.log p * (((p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2)) :=
          le_trans hstep1 hstep2
      _ ≤ (1 / (N : ℝ)) * (2 * C + 2 * Real.log p) := by
          refine mul_le_mul hrpow hQ hQnn (by positivity)
      _ ≤ (1 / (N : ℝ)) * (4 * Real.log N + 2 * |Real.eulerMascheroniConstant|
            + 4 * Real.log p) := by
          refine mul_le_mul_of_nonneg_left hCbound (by positivity)
      _ = (4 * Real.log N + 2 * |Real.eulerMascheroniConstant| + 4 * Real.log p) / N := by
          rw [one_div, inv_mul_eq_div]
  rw [← hsumf.sum_add_tsum_nat_add I]
  refine le_trans (abs_add_le _ _) ?_
  exact add_le_add hhead htail

/-! ### The first-order γ-affine law -/

/-- The first-order generalized Stieltjes structure constant
`A_{1,p} = γ/(p−1) − (log p)·p/(p−1)²`. -/
def firstOrderStieltjes (p : ℕ) : ℝ :=
  Real.eulerMascheroniConstant / ((p : ℝ) - 1) - Real.log p * (p : ℝ) / ((p : ℝ) - 1) ^ 2

lemma tendsto_errorMajorant (hp : p.Prime) :
    Tendsto (fun N : ℕ => errorMajorant p N) atTop (𝓝 0) := by
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlogdiv : Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) atTop (𝓝 0) := by
    have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    exact h.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hrep : ∀ N : ℕ, errorMajorant p N
      = (4 / Real.log p) * (Real.log N / N) + 4 * (Real.log N / N)
        + (2 * |Real.eulerMascheroniConstant| + 4 * Real.log p) * (1 / N) := by
    intro N
    rw [errorMajorant]
    by_cases hN : (N : ℝ) = 0
    · rw [hN]
      simp
    · field_simp
      ring
  rw [show (fun N : ℕ => errorMajorant p N) = fun N : ℕ =>
      (4 / Real.log p) * (Real.log N / N) + 4 * (Real.log N / N)
        + (2 * |Real.eulerMascheroniConstant| + 4 * Real.log p) * (1 / N) from funext hrep]
  have h1 : Tendsto (fun N : ℕ => (4 / Real.log p) * (Real.log N / N)) atTop (𝓝 0) := by
    simpa using hlogdiv.const_mul (4 / Real.log p)
  have h2 : Tendsto (fun N : ℕ => (4 : ℝ) * (Real.log N / N)) atTop (𝓝 0) := by
    simpa using hlogdiv.const_mul (4 : ℝ)
  have h3 : Tendsto (fun N : ℕ =>
      (2 * |Real.eulerMascheroniConstant| + 4 * Real.log p) * (1 / (N : ℝ))) atTop (𝓝 0) := by
    simpa using hinv.const_mul (2 * |Real.eulerMascheroniConstant| + 4 * Real.log p)
  simpa using (h1.add h2).add h3

/-- **γ-affine structure of the first-order Stieltjes prime lane.**  The regularized limit
`A_{1,p} = reg-lim (∑_{k ≤ N} v_p(k)/k − (log N)/(p−1))` exists and equals
`γ/(p−1) − (log p)·p/(p−1)²`. -/
theorem tendsto_stieltjesFirstOrderCutoff (hp : p.Prime) :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, (padicValNat p k : ℝ) / k)
        - Real.log N / ((p : ℝ) - 1))
      atTop (𝓝 (firstOrderStieltjes p)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpm : (p : ℝ) - 1 ≠ 0 := by intro h; nlinarith
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ (tendsto_errorMajorant hp)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hkey : (∑ k ∈ Finset.Icc 1 N, (padicValNat p k : ℝ) / k)
      - Real.log N / ((p : ℝ) - 1) - firstOrderStieltjes p
      = ∑' i, (ladderTerm p N i - modelTerm p N i) := by
    rw [Summable.tsum_sub (summable_ladderTerm hp N) (summable_modelTerm hp N),
      ← sum_padicValNat_div_real_eq_tsum hp N, tsum_modelTerm hp N, firstOrderStieltjes]
    field_simp
    ring
  rw [Real.norm_eq_abs, hkey]
  exact abs_tsum_ladderSubModel_le hp hN

/-- **The first-order lane is `ℚ`-linear in `{γ, log p}`.**  Explicit rational coefficients
`1/(p−1)` for `γ` and `−p/(p−1)²` for `log p`. -/
theorem firstOrderStieltjes_eq_rat_combination (hp : p.Prime) :
    firstOrderStieltjes p
      = ((1 / ((p : ℚ) - 1) : ℚ) : ℝ) * Real.eulerMascheroniConstant
        + ((-(p : ℚ) / ((p : ℚ) - 1) ^ 2 : ℚ) : ℝ) * Real.log p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpm : (p : ℝ) - 1 ≠ 0 := by intro h; nlinarith
  rw [firstOrderStieltjes]
  push_cast
  field_simp
  ring

end

end StieltjesGammaAffine
end RHTower
