import Mathlib
import GaloisForLFunctions.HTGeometry.EntireLogarithm

/-!
# Quadratic-subtype growth and sublogarithmic canonical divisors

This module carries the *converse* half of the quadratic-subtype / sublogarithmic-divisor
equivalence: a divisor whose counting function is `o(log r)` has a convergent genus-zero canonical
product `P(z) = ∏_k (1 - z/a_k)` with `log M_P(r) = o((log r)²)`.

The divisor is presented as a sequence `a : ℕ → ℂ` of nonzero points of nondecreasing modulus
tending to infinity — the standard presentation of a canonical product — and `divisorSeqCount a r`
is `#{k : ‖a k‖ ≤ r}` (`Set.ncard`).  Under `SublogDensity a` the counting bound converts into the
per-index bound `C·k ≤ log ‖a k‖` for every `C` (`eventually_mul_le_log_norm`), which makes all the
estimates plain series manipulations instead of Stieltjes integrals:

* `summable_rpow_neg` — the exponent of convergence is zero: `∑ ‖a k‖^{-α} < ∞` for every `α > 0`
  (the card's step 3);
* `multipliable_genusZero` — hence the genus-zero product converges at every point;
* `logSum_le` — the card's estimate (8)–(10): `∑_k log(1 + r/‖a k‖) ≤ ε (log r)²` eventually, for
  every `ε > 0`.  Splitting the sum at `K = ⌈2 log r / C⌉` puts a `(2/C)(log r)²` head against a
  geometric tail, and `C` is chosen after `ε`;
* `logNorm_genusZeroProduct_le_of_sublogDensity` — the card's `(4) ⟹ (5)`.

The maximum-modulus step avoids any `log ∏' = ∑' log` lemma: the finite partial products are
bounded by `exp` of the partial sums, which are bounded by the total sum, and the bound passes to
the limit.
-/

noncomputable section

open Complex Filter Topology Set Asymptotics Metric
open GaloisForLFunctions.HTGeometry (iteratedDeriv_eq_zero_of_growth)

namespace GaloisForLFunctions.QuadraticSubtypeDivisor


/-! ## Divisors and their counting function -/

/-- The number of divisor points, with multiplicity, in the closed disc of radius `r`. -/
def divisorSeqCount (a : ℕ → ℂ) (r : ℝ) : ℕ := {k : ℕ | ‖a k‖ ≤ r}.ncard

theorem finite_normLe {a : ℕ → ℂ} (htend : Tendsto (fun k => ‖a k‖) atTop atTop) (r : ℝ) :
    {k : ℕ | ‖a k‖ ≤ r}.Finite := by
  have h : ∀ᶠ k in atTop, r < ‖a k‖ := htend.eventually_gt_atTop r
  rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at h
  refine h.subset (fun k hk => ?_)
  simp only [mem_setOf_eq, not_lt] at hk ⊢
  exact hk

theorem succ_le_divisorSeqCount {a : ℕ → ℂ} (hmono : Monotone (fun k => ‖a k‖))
    (htend : Tendsto (fun k => ‖a k‖) atTop atTop) (k : ℕ) :
    k + 1 ≤ divisorSeqCount a (‖a k‖) := by
  have hsub : (Set.Iic k) ⊆ {j : ℕ | ‖a j‖ ≤ ‖a k‖} := fun j hj => hmono hj
  have hfin := finite_normLe htend (‖a k‖)
  have h1 : (Set.Iic k).ncard ≤ divisorSeqCount a (‖a k‖) := Set.ncard_le_ncard hsub hfin
  have h2 : (Set.Iic k : Set ℕ).ncard = k + 1 := Set.ncard_Iic_nat k
  omega

/-- The card's condition `(4)`: the divisor has sublogarithmic density, `n(r) = o(log r)`. -/
def SublogDensity (a : ℕ → ℂ) : Prop :=
  Tendsto (fun r : ℝ => (divisorSeqCount a r : ℝ) / Real.log r) atTop (𝓝 0)

/-- Sublogarithmic density forces every linear lower bound on `log ‖a k‖`. -/
theorem eventually_mul_le_log_norm {a : ℕ → ℂ} (hmono : Monotone (fun k => ‖a k‖))
    (htend : Tendsto (fun k => ‖a k‖) atTop atTop) (hden : SublogDensity a) {C : ℝ}
    (hC : 0 < C) : ∀ᶠ k : ℕ in atTop, C * (k : ℝ) ≤ Real.log ‖a k‖ := by
  have hεpos : (0 : ℝ) < 1 / (2 * C) := by positivity
  have hev : ∀ᶠ r : ℝ in atTop, (divisorSeqCount a r : ℝ) / Real.log r < 1 / (2 * C) :=
    hden (Iio_mem_nhds hεpos)
  obtain ⟨R₀, hR₀⟩ := (hev.and (eventually_gt_atTop (1 : ℝ))).exists_forall_of_atTop
  have hnorm : ∀ᶠ k in atTop, R₀ ≤ ‖a k‖ := htend.eventually_ge_atTop R₀
  have hR₀' : ∀ᶠ k in atTop, max R₀ 2 ≤ ‖a k‖ := htend.eventually_ge_atTop (max R₀ 2)
  filter_upwards [hR₀'] with k hk
  have hk1 : R₀ ≤ ‖a k‖ := le_trans (le_max_left _ _) hk
  have hk2 : (2 : ℝ) ≤ ‖a k‖ := le_trans (le_max_right _ _) hk
  obtain ⟨hlt, hgt⟩ := hR₀ (‖a k‖) hk1
  have hlogpos : (0 : ℝ) < Real.log ‖a k‖ := Real.log_pos hgt
  have hcount : ((k : ℝ) + 1) ≤ (divisorSeqCount a (‖a k‖) : ℝ) := by
    have := succ_le_divisorSeqCount hmono htend k
    exact_mod_cast this
  have hdiv : (divisorSeqCount a (‖a k‖) : ℝ) < (1 / (2 * C)) * Real.log ‖a k‖ := by
    rw [div_lt_iff₀ hlogpos] at hlt
    linarith
  have : ((k : ℝ) + 1) < (1 / (2 * C)) * Real.log ‖a k‖ := lt_of_le_of_lt hcount hdiv
  have hCpos : (0 : ℝ) < 2 * C := by linarith
  rw [one_div, inv_mul_eq_div, lt_div_iff₀ hCpos] at this
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- The exponent of convergence of a sublogarithmic divisor is zero:
`∑ ‖a k‖^{-α} < ∞` for every `α > 0`. -/
theorem summable_rpow_neg {a : ℕ → ℂ} (hane : ∀ k, a k ≠ 0)
    (hmono : Monotone (fun k => ‖a k‖))
    (htend : Tendsto (fun k => ‖a k‖) atTop atTop) (hden : SublogDensity a) {α : ℝ}
    (hα : 0 < α) : Summable (fun k => ‖a k‖ ^ (-α)) := by
  have hC : (0 : ℝ) < 2 / α := by positivity
  obtain ⟨N, hN⟩ := (eventually_mul_le_log_norm hmono htend hden hC).exists_forall_of_atTop
  have hgeo : Summable (fun k : ℕ => Real.exp (-(2 : ℝ) * k)) := by
    have hpow : ∀ k : ℕ, Real.exp (-(2 : ℝ) * k) = (Real.exp (-2)) ^ k := by
      intro k
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [funext hpow]
    refine summable_geometric_of_lt_one (by positivity) ?_
    rw [Real.exp_lt_one_iff]
    norm_num
  rw [← summable_nat_add_iff N]
  refine Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (norm_nonneg _) _) (fun k => ?_)
    ((summable_nat_add_iff N).mpr hgeo)
  have h1 : (2 / α) * ((k + N : ℕ) : ℝ) ≤ Real.log ‖a (k + N)‖ := hN (k + N) (by omega)
  have hpos : 0 < ‖a (k + N)‖ := norm_pos_iff.mpr (hane _)
  rw [Real.rpow_def_of_pos hpos]
  refine Real.exp_le_exp.mpr ?_
  have h2 : (2 : ℝ) * ((k + N : ℕ) : ℝ) ≤ α * Real.log ‖a (k + N)‖ := by
    have := mul_le_mul_of_nonneg_left h1 hα.le
    rw [← mul_assoc] at this
    have hαα : α * (2 / α) = 2 := by field_simp
    rw [hαα] at this
    exact this
  nlinarith


theorem summable_inv_norm {a : ℕ → ℂ} (hane : ∀ k, a k ≠ 0)
    (hmono : Monotone (fun k => ‖a k‖))
    (htend : Tendsto (fun k => ‖a k‖) atTop atTop) (hden : SublogDensity a) :
    Summable (fun k => ‖a k‖⁻¹) := by
  have h := summable_rpow_neg hane hmono htend hden (α := 1) one_pos
  refine h.congr (fun k => ?_)
  rw [Real.rpow_neg_one]

/-! ## The genus-zero canonical product -/

/-- The genus-zero canonical product `∏_k (1 - z / a k)`. -/
def genusZeroProduct (a : ℕ → ℂ) (z : ℂ) : ℂ := ∏' k : ℕ, (1 - z / a k)

theorem multipliable_genusZero {a : ℕ → ℂ} (hinv : Summable (fun k => ‖a k‖⁻¹)) (z : ℂ) :
    Multipliable (fun k : ℕ => 1 - z / a k) := by
  have h : Summable (fun k : ℕ => ‖-(z / a k)‖) := by
    have : ∀ k : ℕ, ‖-(z / a k)‖ = ‖z‖ * ‖a k‖⁻¹ := by
      intro k
      rw [norm_neg, norm_div, div_eq_mul_inv]
    rw [funext this]
    exact hinv.mul_left ‖z‖
  have hm := multipliable_one_add_of_summable h
  refine hm.congr (fun k => ?_)
  ring

theorem summable_logOnePlus {a : ℕ → ℂ} (hane : ∀ k, a k ≠ 0)
    (hinv : Summable (fun k => ‖a k‖⁻¹)) {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun k : ℕ => Real.log (1 + r / ‖a k‖)) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (hinv.mul_left r)
  · refine Real.log_nonneg ?_
    have : 0 ≤ r / ‖a k‖ := by positivity
    linarith
  · have hpos : (0 : ℝ) < ‖a k‖ := norm_pos_iff.mpr (hane k)
    have h1 : Real.log (1 + r / ‖a k‖) ≤ r / ‖a k‖ := by
      have := Real.log_le_sub_one_of_pos (x := 1 + r / ‖a k‖) (by positivity)
      linarith
    rw [div_eq_mul_inv] at h1
    exact h1

/-- The maximum modulus of the genus-zero product is controlled by the logarithmic sum. -/
theorem log_norm_genusZeroProduct_le {a : ℕ → ℂ} (hane : ∀ k, a k ≠ 0)
    (hinv : Summable (fun k => ‖a k‖⁻¹)) (z : ℂ) :
    Real.log ‖genusZeroProduct a z‖ ≤ ∑' k : ℕ, Real.log (1 + ‖z‖ / ‖a k‖) := by
  set S : ℝ := ∑' k : ℕ, Real.log (1 + ‖z‖ / ‖a k‖) with hS
  have hsum := summable_logOnePlus hane hinv (r := ‖z‖) (norm_nonneg z)
  have hfin : ∀ n : ℕ, ‖∏ k ∈ Finset.range n, (1 - z / a k)‖ ≤ Real.exp S := by
    intro n
    have h1 : ‖∏ k ∈ Finset.range n, (1 - z / a k)‖
        ≤ ∏ k ∈ Finset.range n, (1 + ‖z‖ / ‖a k‖) := by
      rw [norm_prod]
      refine Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => ?_)
      calc ‖1 - z / a k‖ ≤ ‖(1 : ℂ)‖ + ‖z / a k‖ := norm_sub_le _ _
        _ = 1 + ‖z‖ / ‖a k‖ := by rw [norm_one, norm_div]
    refine le_trans h1 ?_
    have h2 : ∏ k ∈ Finset.range n, (1 + ‖z‖ / ‖a k‖)
        = Real.exp (∑ k ∈ Finset.range n, Real.log (1 + ‖z‖ / ‖a k‖)) := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl (fun k _ => ?_)
      refine (Real.exp_log ?_).symm
      have hpos : (0 : ℝ) < ‖a k‖ := norm_pos_iff.mpr (hane k)
      positivity
    rw [h2]
    refine Real.exp_le_exp.mpr ?_
    refine hsum.sum_le_tsum _ (fun k _ => ?_)
    refine Real.log_nonneg ?_
    have hpos : (0 : ℝ) < ‖a k‖ := norm_pos_iff.mpr (hane k)
    have : 0 ≤ ‖z‖ / ‖a k‖ := by positivity
    linarith
  have hlim : Filter.Tendsto (fun n : ℕ => ‖∏ k ∈ Finset.range n, (1 - z / a k)‖)
      atTop (𝓝 ‖genusZeroProduct a z‖) := by
    have := (multipliable_genusZero hinv z).hasProd.tendsto_prod_nat
    exact (continuous_norm.tendsto _).comp this
  have hle : ‖genusZeroProduct a z‖ ≤ Real.exp S := le_of_tendsto hlim (.of_forall hfin)
  rcases eq_or_lt_of_le (norm_nonneg (genusZeroProduct a z)) with h0 | h0
  · rw [← h0, Real.log_zero]
    refine tsum_nonneg (fun k => ?_)
    refine Real.log_nonneg ?_
    have hpos : (0 : ℝ) < ‖a k‖ := norm_pos_iff.mpr (hane k)
    have hq : 0 ≤ ‖z‖ / ‖a k‖ := by positivity
    linarith
  · rw [← Real.log_exp S]
    exact Real.log_le_log h0 hle


/-! ## The quadratic-subtype growth estimate -/

set_option maxHeartbeats 1000000 in
/-- **The card's estimate (8)–(10).**  A sublogarithmic divisor makes the logarithmic sum
`∑_k log(1 + r/‖a k‖)` of quadratic subtype zero. -/
theorem logSum_le {a : ℕ → ℂ} (hane : ∀ k, a k ≠ 0) (hmono : Monotone (fun k => ‖a k‖))
    (htend : Tendsto (fun k => ‖a k‖) atTop atTop) (hden : SublogDensity a)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, ∑' k : ℕ, Real.log (1 + r / ‖a k‖) ≤ ε * (Real.log r) ^ 2 := by
  have hinv := summable_inv_norm hane hmono htend hden
  set C : ℝ := 8 / ε with hCdef
  have hCpos : (0 : ℝ) < C := by positivity
  obtain ⟨N, hN⟩ := (eventually_mul_le_log_norm hmono htend hden hCpos).exists_forall_of_atTop
  set A₀ : ℝ := ‖a 0‖ with hA₀def
  have hA₀pos : (0 : ℝ) < A₀ := norm_pos_iff.mpr (hane 0)
  set B₀ : ℝ := Real.log (1 + 1 / A₀) with hB₀def
  have hB₀nn : (0 : ℝ) ≤ B₀ := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) < 1 / A₀ := by positivity
    linarith
  have hgeoSum : Summable (fun k : ℕ => Real.exp (-(C * k))) := by
    have hpow : ∀ k : ℕ, Real.exp (-(C * k)) = (Real.exp (-C)) ^ k := by
      intro k
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [funext hpow]
    refine summable_geometric_of_lt_one (by positivity) ?_
    rw [Real.exp_lt_one_iff]
    linarith
  set B₁ : ℝ := ∑' k : ℕ, Real.exp (-(C * k)) with hB₁def
  have hB₁nn : (0 : ℝ) ≤ B₁ := tsum_nonneg (fun k => (Real.exp_pos _).le)
  set D : ℝ := 2 * B₀ / C + 1 + B₀ + B₁ with hDdef
  have hDnn : (0 : ℝ) ≤ D := by
    have : (0 : ℝ) ≤ 2 * B₀ / C := by positivity
    linarith
  set L₀ : ℝ := max (max 1 (4 * D / (3 * ε))) ((N : ℝ) * C / 2) with hL₀def
  filter_upwards [eventually_ge_atTop (Real.exp L₀), eventually_gt_atTop (0 : ℝ)]
    with r hrexp hrpos
  set L : ℝ := Real.log r with hLdef
  have hLge : L₀ ≤ L := by
    rw [hLdef, ← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos _) hrexp
  have hL1 : (1 : ℝ) ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLge
  have hLD : 4 * D / (3 * ε) ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLge
  have hLN : (N : ℝ) * C / 2 ≤ L := le_trans (le_max_right _ _) hLge
  have hr1 : (1 : ℝ) ≤ r := by
    have := Real.exp_le_exp.mpr hL1
    rw [Real.exp_log hrpos] at this
    calc (1 : ℝ) = Real.exp 0 := by simp
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ r := this
  have hsum := summable_logOnePlus hane hinv (r := r) (le_of_lt hrpos)
  set K : ℕ := ⌈2 * L / C⌉₊ with hKdef
  have hKge : 2 * L / C ≤ (K : ℝ) := Nat.le_ceil _
  have hKle : (K : ℝ) ≤ 2 * L / C + 1 := by
    have h := Nat.ceil_lt_add_one (a := 2 * L / C) (by positivity)
    linarith
  have hKN : N ≤ K := by
    have h1 : (N : ℝ) ≤ 2 * L / C := by
      rw [le_div_iff₀ hCpos]
      linarith
    have := le_trans h1 hKge
    exact_mod_cast this
  -- head
  have hhead : ∑ k ∈ Finset.range K, Real.log (1 + r / ‖a k‖) ≤ (K : ℝ) * (L + B₀) := by
    have hterm : ∀ k ∈ Finset.range K, Real.log (1 + r / ‖a k‖) ≤ L + B₀ := by
      intro k _
      have hak : A₀ ≤ ‖a k‖ := hmono (Nat.zero_le k)
      have hakpos : (0 : ℝ) < ‖a k‖ := lt_of_lt_of_le hA₀pos hak
      have h1 : 1 + r / ‖a k‖ ≤ 1 + r / A₀ := by
        have : r / ‖a k‖ ≤ r / A₀ := by
          refine div_le_div_of_nonneg_left (le_of_lt hrpos) hA₀pos hak
        linarith
      have h2 : (1 : ℝ) + r / A₀ ≤ r * (1 + 1 / A₀) := by
        have : r / A₀ = r * (1 / A₀) := by ring
        rw [this]
        nlinarith
      have h3 : Real.log (1 + r / ‖a k‖) ≤ Real.log (r * (1 + 1 / A₀)) := by
        refine Real.log_le_log (by positivity) (le_trans h1 h2)
      rw [Real.log_mul (ne_of_gt hrpos) (by positivity)] at h3
      exact h3
    calc ∑ k ∈ Finset.range K, Real.log (1 + r / ‖a k‖)
        ≤ ∑ _k ∈ Finset.range K, (L + B₀) := Finset.sum_le_sum hterm
      _ = (K : ℝ) * (L + B₀) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- tail
  have hmono2 : ∀ k : ℕ, Real.log (1 + r / ‖a (k + K)‖) ≤ Real.exp (-(C * k)) := by
    intro k
    have hakpos : (0 : ℝ) < ‖a (k + K)‖ := norm_pos_iff.mpr (hane _)
    have h1 : Real.log (1 + r / ‖a (k + K)‖) ≤ r / ‖a (k + K)‖ := by
      have := Real.log_le_sub_one_of_pos (x := 1 + r / ‖a (k + K)‖) (by positivity)
      linarith
    have h2 : r / ‖a (k + K)‖ = Real.exp (L - Real.log ‖a (k + K)‖) := by
      rw [Real.exp_sub, hLdef, Real.exp_log hrpos, Real.exp_log hakpos]
    have h3 : C * ((k + K : ℕ) : ℝ) ≤ Real.log ‖a (k + K)‖ := hN (k + K) (by omega)
    have h4 : L - Real.log ‖a (k + K)‖ ≤ -(C * k) := by
      have hCK : 2 * L ≤ C * (K : ℝ) := by
        have := hKge
        rw [div_le_iff₀ hCpos] at this
        linarith
      have hcast : ((k + K : ℕ) : ℝ) = (k : ℝ) + (K : ℝ) := by push_cast; ring
      rw [hcast] at h3
      nlinarith
    calc Real.log (1 + r / ‖a (k + K)‖) ≤ r / ‖a (k + K)‖ := h1
      _ = Real.exp (L - Real.log ‖a (k + K)‖) := h2
      _ ≤ Real.exp (-(C * k)) := Real.exp_le_exp.mpr h4
  have htail : ∑' k : ℕ, Real.log (1 + r / ‖a (k + K)‖) ≤ B₁ :=
    Summable.tsum_mono ((summable_nat_add_iff K).mpr hsum) hgeoSum hmono2
  -- assemble
  have hsplit : ∑' k : ℕ, Real.log (1 + r / ‖a k‖)
      = (∑ k ∈ Finset.range K, Real.log (1 + r / ‖a k‖))
        + ∑' k : ℕ, Real.log (1 + r / ‖a (k + K)‖) := (Summable.sum_add_tsum_nat_add K hsum).symm
  rw [hsplit]
  have hLB : (0 : ℝ) ≤ L + B₀ := by linarith
  have hstep1 : (K : ℝ) * (L + B₀) ≤ (2 * L / C + 1) * (L + B₀) :=
    mul_le_mul_of_nonneg_right hKle hLB
  have hCval : 2 / C = ε / 4 := by
    rw [hCdef]
    field_simp
    norm_num
  have hstep2 : (2 * L / C + 1) * (L + B₀) = (2 / C) * L ^ 2 + (2 * B₀ / C) * L + L + B₀ := by
    field_simp
    ring
  have hfinal : (2 / C) * L ^ 2 + (2 * B₀ / C) * L + L + B₀ + B₁ ≤ ε * L ^ 2 := by
    rw [hCval]
    have hlow : (2 * B₀ / C) * L + L + B₀ + B₁ ≤ D * L := by
      rw [hDdef]
      nlinarith
    have hDL : D * L ≤ (3 * ε / 4) * L ^ 2 := by
      have hεpos : (0 : ℝ) < 3 * ε := by linarith
      rw [div_le_iff₀ hεpos] at hLD
      nlinarith
    nlinarith
  linarith [hhead, htail, hstep1, hstep2]


/-! ## The converse direction of the card -/

/-- **Converse direction, `(4) ⟹ (5)`.**  If the divisor has sublogarithmic density then the
genus-zero canonical product converges and its maximum modulus has quadratic subtype zero:
`log M_P(r) = o((log r)²)`. -/
theorem logNorm_genusZeroProduct_le_of_sublogDensity {a : ℕ → ℂ} (hane : ∀ k, a k ≠ 0)
    (hmono : Monotone (fun k => ‖a k‖)) (htend : Tendsto (fun k => ‖a k‖) atTop atTop)
    (hden : SublogDensity a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ r →
      Real.log ‖genusZeroProduct a z‖ ≤ ε * (Real.log r) ^ 2 := by
  have hinv := summable_inv_norm hane hmono htend hden
  filter_upwards [logSum_le hane hmono htend hden hε, eventually_gt_atTop (0 : ℝ)]
    with r hr hrpos z hz
  refine le_trans (log_norm_genusZeroProduct_le hane hinv z) (le_trans ?_ hr)
  refine Summable.tsum_mono (summable_logOnePlus hane hinv (norm_nonneg z))
    (summable_logOnePlus hane hinv (le_of_lt hrpos)) (fun k => ?_)
  have hakpos : (0 : ℝ) < ‖a k‖ := norm_pos_iff.mpr (hane k)
  refine Real.log_le_log (by positivity) ?_
  have hdiv : ‖z‖ / ‖a k‖ ≤ r / ‖a k‖ := by gcongr
  linarith

/-- **Convergence of the genus-zero product.**  This is the "`P(z)` converges" half of the
card's converse direction. -/
theorem multipliable_genusZero_of_sublogDensity {a : ℕ → ℂ} (hane : ∀ k, a k ≠ 0)
    (hmono : Monotone (fun k => ‖a k‖)) (htend : Tendsto (fun k => ‖a k‖) atTop atTop)
    (hden : SublogDensity a) (z : ℂ) :
    Multipliable (fun k : ℕ => 1 - z / a k) :=
  multipliable_genusZero (summable_inv_norm hane hmono htend hden) z


/-! ## The forward direction: growth controls the divisor -/

/-- The card's growth class `(1)`: `log M_f(r) = o((log r)²)`. -/
def QuadraticSubtypeZero (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ r → Real.log ‖f z‖ ≤ ε * (Real.log r) ^ 2

/-- Quadratic subtype zero implies ordinary order zero: the log-modulus is eventually below
`r ^ δ` for every `δ > 0`. -/
theorem orderZero_of_quadraticSubtypeZero {f : ℂ → ℂ} (hq : QuadraticSubtypeZero f)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ r → Real.log ‖f z‖ ≤ r ^ δ := by
  have hlog : Filter.Tendsto (fun r : ℝ => (Real.log r) ^ 2 / r ^ δ) atTop (𝓝 0) := by
    have h1 : (fun r : ℝ => Real.log r) =o[atTop] fun r : ℝ => r ^ (δ / 2) :=
      isLittleO_log_rpow_atTop (by positivity)
    have h2 : (fun r : ℝ => (Real.log r) ^ 2) =o[atTop] fun r : ℝ => r ^ δ := by
      have := h1.mul h1
      refine this.congr' ?_ ?_
      · filter_upwards with r
        ring
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
        rw [← Real.rpow_add hr]
        congr 1
        ring
    have h3 := h2.tendsto_div_nhds_zero
    exact h3
  have hev : ∀ᶠ r : ℝ in atTop, (Real.log r) ^ 2 / r ^ δ < 1 := by
    have := hlog (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))
    exact this
  filter_upwards [hq 1 one_pos, hev, eventually_gt_atTop (0 : ℝ)] with r hr hr1 hrpos z hz
  have h1 := hr z hz
  rw [one_mul] at h1
  have hrδ : (0 : ℝ) < r ^ δ := Real.rpow_pos_of_pos hrpos _
  rw [div_lt_one hrδ] at hr1
  linarith

/-- **Forward direction, step 2 (Jensen).**  An entire function of quadratic subtype zero has
sublogarithmic zero density: `n_f(r) = o(log r)`. -/
theorem divisorCount_le_of_quadraticSubtypeZero {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0) (hq : QuadraticSubtypeZero f)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop,
      ((∑ᶠ u : ℂ, (MeromorphicOn.divisor f (Metric.closedBall 0 r)) u : ℤ) : ℝ)
        ≤ ε * Real.log r := by
  have hε8 : (0 : ℝ) < ε / 8 := by positivity
  obtain ⟨R₀, hR₀⟩ := ((hq (ε / 8) hε8).and (eventually_gt_atTop (1 : ℝ))).exists_forall_of_atTop
  have hkey : ∀ᶠ r : ℝ in atTop, (-Real.log ‖f 0‖) / Real.log r ≤ (ε / 2) * Real.log r := by
    have htend : Filter.Tendsto (fun r : ℝ => (-Real.log ‖f 0‖) / Real.log r) atTop (𝓝 0) := by
      refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
      exact Real.tendsto_log_atTop
    have h1 : ∀ᶠ r : ℝ in atTop, (-Real.log ‖f 0‖) / Real.log r < 1 :=
      htend (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))
    have h2 : ∀ᶠ r : ℝ in atTop, (1 : ℝ) ≤ (ε / 2) * Real.log r := by
      have : Filter.Tendsto (fun r : ℝ => (ε / 2) * Real.log r) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (by positivity) Real.tendsto_log_atTop
      exact this.eventually_ge_atTop 1
    filter_upwards [h1, h2] with r hr1 hr2
    linarith
  filter_upwards [eventually_ge_atTop (max R₀ 2), eventually_ge_atTop (Real.sqrt R₀), hkey]
    with r hr hrsq hkr
  have hr2 : (2 : ℝ) ≤ r := le_trans (le_max_right _ _) hr
  have hrpos : (0 : ℝ) < r := by linarith
  have hR₀le : R₀ ≤ r := le_trans (le_max_left _ _) hr
  have hRsq : R₀ ≤ r ^ 2 := by nlinarith
  obtain ⟨hgrow, hgt1⟩ := hR₀ (r ^ 2) hRsq
  set M : ℝ := max 1 (Real.exp ((ε / 8) * (Real.log (r ^ 2)) ^ 2)) with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hMsphere : ∀ z ∈ Metric.sphere (0 : ℂ) |r ^ 2|, ‖f z‖ ≤ M := by
    intro z hz
    have hzn : ‖z‖ = r ^ 2 := by
      have := Metric.mem_sphere.mp hz
      rw [dist_zero_right] at this
      rw [this, abs_of_pos (by positivity)]
    have hzle : ‖z‖ ≤ r ^ 2 := le_of_eq hzn
    rcases eq_or_lt_of_le (norm_nonneg (f z)) with h0 | h0
    · rw [← h0]
      linarith
    · have h1 := hgrow z hzle
      have h2 : ‖f z‖ ≤ Real.exp ((ε / 8) * (Real.log (r ^ 2)) ^ 2) := by
        rw [← Real.exp_log h0]
        exact Real.exp_le_exp.mpr h1
      exact le_trans h2 (le_max_right _ _)
  have hjensen := hf.mono (Set.subset_univ _) |>.sum_divisor_le
    (r := r) (R := r ^ 2) (M := M) (by rwa [abs_of_pos hrpos])
    (by rw [abs_of_pos hrpos, abs_of_pos (by positivity : (0:ℝ) < r ^ 2)]; nlinarith)
    hM1 hf0 hMsphere
  rw [abs_of_pos hrpos] at hjensen
  have hlogM : Real.log M = (ε / 8) * (Real.log (r ^ 2)) ^ 2 := by
    rw [hMdef, max_eq_right, Real.log_exp]
    refine Real.one_le_exp ?_
    positivity
  have hlogRr : Real.log (r ^ 2 / r) = Real.log r := by
    congr 1
    field_simp
  have hlogr2 : Real.log (r ^ 2) = 2 * Real.log r := by
    rw [Real.log_pow]
    push_cast
    ring
  have hlogrpos : (0 : ℝ) < Real.log r := Real.log_pos (by linarith)
  have hfin : Real.log (M / ‖f 0‖) / Real.log (r ^ 2 / r) ≤ ε * Real.log r := by
    rw [hlogRr, Real.log_div (by positivity) (norm_ne_zero_iff.mpr hf0), hlogM, hlogr2]
    rw [div_le_iff₀ hlogrpos]
    have hexp : (ε / 8) * (2 * Real.log r) ^ 2 = (ε / 2) * (Real.log r) ^ 2 := by ring
    rw [hexp]
    have hk : (-Real.log ‖f 0‖) ≤ (ε / 2) * Real.log r * Real.log r := by
      rw [div_le_iff₀ hlogrpos] at hkr
      linarith
    nlinarith
  exact le_trans hjensen hfin


/-! ## Zero-free rigidity: quadratic subtype zero forces constancy

This is the "constraint reformulation" lemma of the card: a zero-free entire function in the
growth class `(1)` is constant.  Borel–Carathéodory upgrades the one-sided real-part bound
`Re g ≤ B (log (2+‖z‖))²` into a modulus bound, `log x ≤ 8 x^{1/8}` turns that into a genuine
sub-linear polynomial envelope `‖g z‖ ≤ C (1+‖z‖)^{1/4}`, and the corpus Cauchy estimate
`iteratedDeriv_eq_zero_of_growth` then kills the first derivative. -/


theorem log_le_eight_rpow {x : ℝ} (hx : 0 < x) : Real.log x ≤ 8 * x ^ (1 / 8 : ℝ) := by
  have hxp : (0 : ℝ) < x ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hx _
  have h1 : Real.log (x ^ (1 / 8 : ℝ)) ≤ x ^ (1 / 8 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hxp
  have h2 : Real.log (x ^ (1 / 8 : ℝ)) = (1 / 8 : ℝ) * Real.log x := Real.log_rpow hx _
  rw [h2] at h1
  linarith

/-- **A one-sided squared-logarithmic growth bound forces an entire function to be constant.**
If the real part of an entire `g` is at most `B (log (2 + ‖z‖))²`, then `g` is constant. -/
theorem entire_reBound_sq_imp_const (g : ℂ → ℂ) (hg : Differentiable ℂ g) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z : ℂ, (g z).re ≤ B * (Real.log (2 + ‖z‖)) ^ 2) :
    ∀ z : ℂ, g z = g 0 := by
  set B' : ℝ := B + 1 with hB'def
  have hB'pos : (0 : ℝ) < B' := by rw [hB'def]; linarith
  have hBB' : B ≤ B' := by rw [hB'def]; linarith
  -- Step 1: Borel–Carathéodory envelope
  have hmod : ∀ z : ℂ,
      ‖g z‖ ≤ 2 * B' * (Real.log (4 + 2 * ‖z‖)) ^ 2 + 3 * ‖g 0‖ := by
    intro z
    have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    set R : ℝ := 2 * (1 + ‖z‖) with hRdef
    have hRpos : (0 : ℝ) < R := by rw [hRdef]; positivity
    set M : ℝ := B' * (Real.log (2 + R)) ^ 2 with hMdef
    have hlogRpos : (0 : ℝ) < Real.log (2 + R) := Real.log_pos (by rw [hRdef]; nlinarith)
    have hMpos : (0 : ℝ) < M := by rw [hMdef]; positivity
    have hzball : z ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff, hRdef]; nlinarith
    have hmaps : MapsTo g (ball (0 : ℂ) R) {w : ℂ | w.re ≤ M} := by
      intro w hw
      rw [mem_ball_zero_iff] at hw
      have hwR : ‖w‖ ≤ R := le_of_lt hw
      simp only [mem_setOf_eq]
      have h1 := hbound w
      have hlw : Real.log (2 + ‖w‖) ≤ Real.log (2 + R) :=
        Real.log_le_log (by have := norm_nonneg w; linarith) (by linarith)
      have hlwnn : (0 : ℝ) ≤ Real.log (2 + ‖w‖) :=
        Real.log_nonneg (by have := norm_nonneg w; linarith)
      have hsq : (Real.log (2 + ‖w‖)) ^ 2 ≤ (Real.log (2 + R)) ^ 2 := by nlinarith
      have hsqnn : (0 : ℝ) ≤ (Real.log (2 + ‖w‖)) ^ 2 := sq_nonneg _
      calc (g w).re ≤ B * (Real.log (2 + ‖w‖)) ^ 2 := h1
        _ ≤ B' * (Real.log (2 + ‖w‖)) ^ 2 := mul_le_mul_of_nonneg_right hBB' hsqnn
        _ ≤ B' * (Real.log (2 + R)) ^ 2 := mul_le_mul_of_nonneg_left hsq hB'pos.le
        _ = M := by rw [hMdef]
    have hbc := Complex.borelCaratheodory hMpos hg.differentiableOn hmaps hRpos hzball
    have hRz : R - ‖z‖ = 2 + ‖z‖ := by rw [hRdef]; ring
    have ht1 : 2 * M * ‖z‖ / (R - ‖z‖) ≤ 2 * M := by
      rw [hRz, mul_div_assoc]
      apply mul_le_of_le_one_right (by positivity)
      rw [div_le_one (by positivity)]
      linarith
    have ht2 : ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖) ≤ 3 * ‖g 0‖ := by
      rw [hRz, hRdef, mul_div_assoc]
      have hfrac : (2 * (1 + ‖z‖) + ‖z‖) / (2 + ‖z‖) ≤ 3 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      calc ‖g 0‖ * ((2 * (1 + ‖z‖) + ‖z‖) / (2 + ‖z‖)) ≤ ‖g 0‖ * 3 :=
            mul_le_mul_of_nonneg_left hfrac (norm_nonneg _)
        _ = 3 * ‖g 0‖ := by ring
    have hlogeq : Real.log (2 + R) = Real.log (4 + 2 * ‖z‖) := by rw [hRdef]; congr 1; ring
    have h2M : 2 * M = 2 * B' * (Real.log (4 + 2 * ‖z‖)) ^ 2 := by
      rw [hMdef, hlogeq]; ring
    calc ‖g z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖) := hbc
      _ ≤ 2 * M + 3 * ‖g 0‖ := by linarith
      _ = 2 * B' * (Real.log (4 + 2 * ‖z‖)) ^ 2 + 3 * ‖g 0‖ := by rw [h2M]
  -- Step 2: a genuine sub-linear polynomial envelope
  set C : ℝ := 2 * B' * (64 * (4 : ℝ) ^ (1 / 4 : ℝ)) + 3 * ‖g 0‖ with hCdef
  have hCnn : (0 : ℝ) ≤ C := by
    have h4 : (0 : ℝ) < (4 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    rw [hCdef]
    positivity
  have hpoly : ∀ z : ℂ, ‖g z‖ ≤ C * (1 + ‖z‖) ^ (1 / 4 : ℝ) := by
    intro z
    have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    have hbase : (0 : ℝ) < 4 + 2 * ‖z‖ := by linarith
    have hlognn : (0 : ℝ) ≤ Real.log (4 + 2 * ‖z‖) :=
      Real.log_nonneg (by linarith)
    have hlog8 : Real.log (4 + 2 * ‖z‖) ≤ 8 * (4 + 2 * ‖z‖) ^ (1 / 8 : ℝ) :=
      log_le_eight_rpow hbase
    have hpow8 : (0 : ℝ) ≤ (4 + 2 * ‖z‖) ^ (1 / 8 : ℝ) := (Real.rpow_pos_of_pos hbase _).le
    have hsq : (Real.log (4 + 2 * ‖z‖)) ^ 2 ≤ 64 * ((4 + 2 * ‖z‖) ^ (1 / 8 : ℝ)) ^ 2 := by
      nlinarith
    have hcollapse : ((4 + 2 * ‖z‖) ^ (1 / 8 : ℝ)) ^ 2 = (4 + 2 * ‖z‖) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_natCast ((4 + 2 * ‖z‖) ^ (1 / 8 : ℝ)) 2, ← Real.rpow_mul hbase.le]
      norm_num
    have hle4 : (4 : ℝ) + 2 * ‖z‖ ≤ 4 * (1 + ‖z‖) := by linarith
    have hmono4 : (4 + 2 * ‖z‖) ^ (1 / 4 : ℝ) ≤ (4 * (1 + ‖z‖)) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hbase.le hle4 (by norm_num)
    have hsplit : (4 * (1 + ‖z‖)) ^ (1 / 4 : ℝ)
        = (4 : ℝ) ^ (1 / 4 : ℝ) * (1 + ‖z‖) ^ (1 / 4 : ℝ) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have hone : (1 : ℝ) ≤ (1 + ‖z‖) ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    have hB'nn : (0 : ℝ) ≤ 2 * B' := by linarith
    calc ‖g z‖ ≤ 2 * B' * (Real.log (4 + 2 * ‖z‖)) ^ 2 + 3 * ‖g 0‖ := hmod z
      _ ≤ 2 * B' * (64 * ((4 + 2 * ‖z‖) ^ (1 / 8 : ℝ)) ^ 2) + 3 * ‖g 0‖ := by
          have := mul_le_mul_of_nonneg_left hsq hB'nn
          linarith
      _ = 2 * B' * (64 * (4 + 2 * ‖z‖) ^ (1 / 4 : ℝ)) + 3 * ‖g 0‖ := by rw [hcollapse]
      _ ≤ 2 * B' * (64 * ((4 : ℝ) ^ (1 / 4 : ℝ) * (1 + ‖z‖) ^ (1 / 4 : ℝ))) + 3 * ‖g 0‖ := by
          have h1 : (4 + 2 * ‖z‖) ^ (1 / 4 : ℝ)
              ≤ (4 : ℝ) ^ (1 / 4 : ℝ) * (1 + ‖z‖) ^ (1 / 4 : ℝ) := by
            rw [← hsplit]; exact hmono4
          nlinarith
      _ = (2 * B' * (64 * (4 : ℝ) ^ (1 / 4 : ℝ))) * (1 + ‖z‖) ^ (1 / 4 : ℝ) + 3 * ‖g 0‖ := by
          ring
      _ ≤ (2 * B' * (64 * (4 : ℝ) ^ (1 / 4 : ℝ))) * (1 + ‖z‖) ^ (1 / 4 : ℝ)
            + 3 * ‖g 0‖ * (1 + ‖z‖) ^ (1 / 4 : ℝ) := by nlinarith [norm_nonneg (g 0)]
      _ = C * (1 + ‖z‖) ^ (1 / 4 : ℝ) := by rw [hCdef]; ring
  -- Step 3: the first derivative vanishes, so `g` is constant
  have hderiv : ∀ c : ℂ, deriv g c = 0 := by
    intro c
    have h := iteratedDeriv_eq_zero_of_growth hg (C := C) (a := 1 / 4) (n := 1)
      (by norm_num) (by norm_num) hCnn hpoly c
    rwa [iteratedDeriv_one] at h
  intro z
  exact is_const_of_deriv_eq_zero hg hderiv z 0


end GaloisForLFunctions.QuadraticSubtypeDivisor

end
