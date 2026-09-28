import GaloisForLFunctions.RHTower.Sieve.HarmanDiscardPrimePairSum
import GaloisForLFunctions.RHTower.Sieve.HarmanDiscardTwoPrimeStripBoundsUpper

/-!
# The two-prime-cofactor discarded sum over prime triples

`∑_{q₂} (1/q₂) ∑_{q₁} (1/q₁) ∑_{p₃} 1/(p₃ (1 - α₁ - α₂ - α₃))` over the discarded region is compared
with the section `harmanDiscardTwoPrimeSection` layer by layer: the innermost prime sum is the
integral `harmanDiscardTwoPrimeInner` up to `η` (uniform Mertens–Riemann), the middle sum is the
section up to `η` (the closed form of the inner integral is Lipschitz in `α₁`), and the outer sum
is bounded on strips by the strip envelopes.
-/

namespace RHTower.Sieve

open Real Filter Topology Finset

noncomputable section

/-- The innermost prime sum over the smaller cofactor prime. -/
def harmanTwoPrimeInnerSum (y κ α₁ α₂ : ℝ) : ℝ :=
  primeScaleSum y α₂ ((1 + κ - α₁ - α₂) / 2) (fun α₃ => 1 / (1 - α₁ - α₂ - α₃))

theorem eventually_abs_harmanTwoPrimeInnerSum_sub_le {κ η : ℝ} (hκ1 : κ ≤ 1 / 1000)
    (hη : 0 < η) :
    ∀ᶠ y : ℝ in atTop, ∀ α₂ ∈ Set.Icc (2 / 11 : ℝ) ((1 + κ) / 4), ∀ α₁, α₂ ≤ α₁ →
      α₁ ≤ 1 + κ - 3 * α₂ →
      |harmanTwoPrimeInnerSum y κ α₁ α₂ - harmanDiscardTwoPrimeInner κ α₁ α₂| ≤ η := by
  filter_upwards [eventually_abs_primeScaleSum_sub_integral_le (a₀ := 1 / 6) (b₀ := 1) (M := 6)
    (L := 36) (by norm_num) hη (by norm_num)] with y hy
  intro α₂ hα α₁ h1 h2
  have hup : α₂ ≤ (1 + κ - α₁ - α₂) / 2 := by linarith
  have hden : ∀ x ∈ Set.Icc α₂ ((1 + κ - α₁ - α₂) / 2), 1 / 6 ≤ (1 - α₁ - α₂) + (-1) * x := by
    intro x hx; linarith [hx.2, hα.1]
  have hLip := lipschitzBound_inv_affine (p := 1 - α₁ - α₂) (q := -1) (m := 1 / 6) (by norm_num)
    hden
  have hform : (fun x => 1 / ((1 - α₁ - α₂) + (-1) * x)) = fun α₃ => 1 / (1 - α₁ - α₂ - α₃) := by
    funext x; congr 1; ring
  rw [hform] at hLip
  have hM : ∀ x ∈ Set.Icc α₂ ((1 + κ - α₁ - α₂) / 2), |1 / (1 - α₁ - α₂ - x)| ≤ 6 := by
    intro x hx
    have h6 : 1 / 6 ≤ 1 - α₁ - α₂ - x := by have := hden x hx; linarith
    rw [abs_of_pos (by positivity)]
    calc 1 / (1 - α₁ - α₂ - x) ≤ 1 / (1 / 6) := one_div_le_one_div_of_le (by norm_num) h6
      _ = 6 := by norm_num
  have h := hy _ _ (by linarith [hα.1]) hup (by linarith [hα.1]) _ hM
    (hLip.mono_const (by norm_num))
  unfold harmanTwoPrimeInnerSum harmanDiscardTwoPrimeInner
  have e : (∫ α₃ in α₂..(1 + κ - α₁ - α₂) / 2, 1 / (1 - α₁ - α₂ - α₃) / α₃)
      = ∫ α₃ in α₂..(1 + κ - α₁ - α₂) / 2, 1 / (α₃ * (1 - α₁ - α₂ - α₃)) := by
    congr 1; funext x; rw [div_div, mul_comm]
  rw [← e]
  exact h

/-- The closed-form inner integral is bounded and Lipschitz in `α₁`. -/
theorem harmanDiscardTwoPrimeInner_lipschitz {κ α₂ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000)
    (hα : α₂ ∈ Set.Icc (2 / 11 : ℝ) ((1 + κ) / 4)) :
    (∀ x ∈ Set.Icc α₂ (1 + κ - 3 * α₂), |harmanDiscardTwoPrimeInner κ x α₂| ≤ 40) ∧
      LipschitzBound (fun x => harmanDiscardTwoPrimeInner κ x α₂)
        (Set.Icc α₂ (1 + κ - 3 * α₂)) 150 := by
  set s := Set.Icc α₂ (1 + κ - 3 * α₂) with hs
  have hα0 : 0 < α₂ := by linarith [hα.1]
  -- the closed form on `s`
  have hcl : ∀ x ∈ s, harmanDiscardTwoPrimeInner κ x α₂ =
      (log ((1 - α₂ + κ) + (-1) * x) - log ((1 - α₂ - κ) + (-1) * x)
        + log ((1 - 2 * α₂) + (-1) * x) - log α₂) * (1 / ((1 - α₂) + (-1) * x)) := by
    intro x hx
    rw [harmanDiscardTwoPrimeInner_eq hκ hκ1 hα.1 hx.2]
    have h1 : 0 < 1 - x - α₂ - κ := by linarith [hx.2, hα.1]
    have h2 : 0 < 1 - x - α₂ - α₂ := by linarith [hx.2, hα.1]
    rw [Real.log_div (by linarith) h1.ne', Real.log_div h2.ne' hα0.ne']
    rw [show (1 - α₂ + κ) + (-1) * x = 1 - x - α₂ + κ by ring,
      show (1 - α₂ - κ) + (-1) * x = 1 - x - α₂ - κ by ring,
      show (1 - 2 * α₂) + (-1) * x = 1 - x - α₂ - α₂ by ring,
      show (1 - α₂) + (-1) * x = 1 - x - α₂ by ring]
    ring
  have b1 : ∀ x ∈ s, 1 / 3 ≤ (1 - α₂ + κ) + (-1) * x := fun x hx => by linarith [hx.2, hα.1]
  have b2 : ∀ x ∈ s, 1 / 3 ≤ (1 - α₂ - κ) + (-1) * x := fun x hx => by linarith [hx.2, hα.1]
  have b3 : ∀ x ∈ s, 1 / 6 ≤ (1 - 2 * α₂) + (-1) * x := fun x hx => by linarith [hx.2, hα.1]
  have b4 : ∀ x ∈ s, 1 / 3 ≤ (1 - α₂) + (-1) * x := fun x hx => by linarith [hx.2, hα.1]
  have u1 : ∀ x ∈ s, (1 - α₂ + κ) + (-1) * x ≤ 1 := fun x hx => by linarith [hx.1, hα.1]
  have u2 : ∀ x ∈ s, (1 - α₂ - κ) + (-1) * x ≤ 1 := fun x hx => by linarith [hx.1, hα.1]
  have u3 : ∀ x ∈ s, (1 - 2 * α₂) + (-1) * x ≤ 1 := fun x hx => by linarith [hx.1, hα.1]
  have L1 := lipschitzBound_log_affine (p := 1 - α₂ + κ) (q := -1) (m := 1 / 3) (by norm_num) b1
  have L2 := lipschitzBound_log_affine (p := 1 - α₂ - κ) (q := -1) (m := 1 / 3) (by norm_num) b2
  have L3 := lipschitzBound_log_affine (p := 1 - 2 * α₂) (q := -1) (m := 1 / 6) (by norm_num) b3
  have L4 := lipschitzBound_const (log α₂) s
  have LB := ((L1.sub L2).add L3).sub L4
  have LI := lipschitzBound_inv_affine (p := 1 - α₂) (q := -1) (m := 1 / 3) (by norm_num) b4
  have hlogb : ∀ v, 1 / 6 ≤ v → v ≤ 1 → |log v| ≤ 3 := by
    intro v hv1 hv2
    have h := abs_log_le_of_mem (by norm_num : (0 : ℝ) < 1 / 6) hv1 hv2
    have hl1 : log 1 = 0 := Real.log_one
    have hl6 : -log (1 / 6 : ℝ) ≤ 3 := by
      rw [one_div, Real.log_inv, neg_neg]
      have h6 : (6 : ℝ) ≤ Real.exp 3 := by
        have h1 := Real.add_one_le_exp (1 : ℝ)
        have e3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add, ← Real.exp_add]; norm_num
        rw [e3]
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith
        nlinarith
      calc log 6 ≤ log (Real.exp 3) := Real.log_le_log (by norm_num) h6
        _ = 3 := Real.log_exp 3
    rw [hl1] at h
    exact h.trans (max_le (by norm_num) hl6)
  have MB : ∀ x ∈ s, |log ((1 - α₂ + κ) + (-1) * x) - log ((1 - α₂ - κ) + (-1) * x)
      + log ((1 - 2 * α₂) + (-1) * x) - log α₂| ≤ 12 := by
    intro x hx
    have e1 := hlogb _ (by linarith [b1 x hx]) (u1 x hx)
    have e2 := hlogb _ (by linarith [b2 x hx]) (u2 x hx)
    have e3 := hlogb _ (b3 x hx) (u3 x hx)
    have e4 := hlogb α₂ (by linarith [hα.1]) (by linarith [hα.2])
    calc _ ≤ |log ((1 - α₂ + κ) + (-1) * x)| + |log ((1 - α₂ - κ) + (-1) * x)|
          + |log ((1 - 2 * α₂) + (-1) * x)| + |log α₂| := by
          have := abs_sub (log ((1 - α₂ + κ) + (-1) * x) - log ((1 - α₂ - κ) + (-1) * x)
            + log ((1 - 2 * α₂) + (-1) * x)) (log α₂)
          have := abs_add_le (log ((1 - α₂ + κ) + (-1) * x) - log ((1 - α₂ - κ) + (-1) * x))
            (log ((1 - 2 * α₂) + (-1) * x))
          have := abs_sub (log ((1 - α₂ + κ) + (-1) * x)) (log ((1 - α₂ - κ) + (-1) * x))
          linarith
      _ ≤ 12 := by linarith
  have MI : ∀ x ∈ s, |1 / ((1 - α₂) + (-1) * x)| ≤ 3 := by
    intro x hx
    have h := b4 x hx
    rw [abs_of_pos (by positivity)]
    calc 1 / ((1 - α₂) + (-1) * x) ≤ 1 / (1 / 3) := one_div_le_one_div_of_le (by norm_num) h
      _ = 3 := by norm_num
  have LP := LB.mul LI MB MI
  constructor
  · intro x hx
    rw [hcl x hx, abs_mul]
    calc _ ≤ 12 * 3 := mul_le_mul (MB x hx) (MI x hx) (abs_nonneg _) (by norm_num)
      _ ≤ 40 := by norm_num
  · intro x hx z hz
    simp only
    rw [hcl x hx, hcl z hz]
    refine (LP x hx z hz).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    norm_num

/-- The middle prime sum over `q₁`. -/
def harmanTwoPrimeMiddleSum (y κ α₂ : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊y ^ harmanDiscardLow κ α₂⌋₊ ⌊y ^ harmanDiscardHighTwo κ α₂⌋₊).filter
      Nat.Prime, 1 / (p : ℝ) * harmanTwoPrimeInnerSum y κ (log p / log y) α₂

theorem eventually_harmanTwoPrimeMiddleSum_le {κ η : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000)
    (hη : 0 < η) :
    ∀ᶠ y : ℝ in atTop, ∀ α₂ ∈ Set.Icc (2 / 11 : ℝ) ((1 + κ) / 4),
      harmanTwoPrimeMiddleSum y κ α₂ ≤ harmanDiscardTwoPrimeSection κ α₂ + η := by
  have hη6 : 0 < η / 6 := by positivity
  have hη2 : 0 < η / 2 := by positivity
  filter_upwards [eventually_abs_harmanTwoPrimeInnerSum_sub_le hκ1 hη6,
    eventually_abs_primeScaleSum_sub_integral_le (a₀ := 1 / 6) (b₀ := 1) (M := 40) (L := 150)
      (by norm_num) hη2 (by norm_num),
    eventually_sum_prime_inv_rpow_le_uniform (a₀ := 1 / 6) (by norm_num),
    eventually_gt_atTop (1 : ℝ)] with y hin hB1 hmert hy1
  intro α₂ hα
  set lo := harmanDiscardLow κ α₂ with hlo
  set hi := harmanDiscardHighTwo κ α₂ with hhi
  have hlh : lo ≤ hi := harmanDiscardLow_le_highTwo hκ (by linarith [hα.1]) hα.2
  have hlo1 : α₂ ≤ lo := le_max_left _ _
  have hhi1 : hi ≤ 1 + κ - 3 * α₂ := min_le_right _ _
  have hhi2 : hi ≤ 1 / 2 + κ := min_le_left _ _
  -- the inner sums are the inner integrals up to `η/6`
  have hstep : harmanTwoPrimeMiddleSum y κ α₂ ≤
      primeScaleSum y lo hi (fun x => harmanDiscardTwoPrimeInner κ x α₂)
        + η / 6 * ∑ p ∈ (Finset.Ioc ⌊y ^ lo⌋₊ ⌊y ^ hi⌋₊).filter Nat.Prime, 1 / (p : ℝ) := by
    unfold harmanTwoPrimeMiddleSum primeScaleSum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun p hp => ?_)
    obtain ⟨h1, h2⟩ := logScale_mem_of_mem_Ioc_floor hy1 (Finset.mem_filter.1 hp).1
    have hi' := (abs_le.mp (hin α₂ hα (log p / log y) (hlo1.trans h1.le) (h2.trans hhi1))).2
    have hq : 0 ≤ 1 / (p : ℝ) := by positivity
    calc 1 / (p : ℝ) * harmanTwoPrimeInnerSum y κ (log p / log y) α₂
        ≤ 1 / (p : ℝ) * (harmanDiscardTwoPrimeInner κ (log p / log y) α₂ + η / 6) :=
          mul_le_mul_of_nonneg_left (by linarith) hq
      _ = harmanDiscardTwoPrimeInner κ (log p / log y) α₂ / p + η / 6 * (1 / p) := by ring
  -- the prime sum against the inner integral is the section up to `η/2`
  obtain ⟨hM, hL⟩ := harmanDiscardTwoPrimeInner_lipschitz hκ hκ1 hα
  have hsub : Set.Icc lo hi ⊆ Set.Icc α₂ (1 + κ - 3 * α₂) := Set.Icc_subset_Icc hlo1 hhi1
  have hsec := hB1 lo hi (by linarith [hα.1]) hlh (by linarith) _
    (fun x hx => hM x (hsub hx)) (hL.mono_set hsub)
  have hsec' : primeScaleSum y lo hi (fun x => harmanDiscardTwoPrimeInner κ x α₂)
      ≤ harmanDiscardTwoPrimeSection κ α₂ + η / 2 := by
    unfold harmanDiscardTwoPrimeSection
    linarith [(abs_le.mp hsec).2]
  -- Mertens' sum over `q₁`
  have hm := hmert lo hi (by linarith [hα.1]) hlh
  have hlogq : log (hi / lo) ≤ 2 := by
    have hlo0 : 0 < lo := by linarith [hα.1]
    have := Real.log_le_sub_one_of_pos (div_pos (hlo0.trans_le hlh) hlo0)
    have hq : hi / lo ≤ 3 := by rw [div_le_iff₀ hlo0]; linarith [hα.1]
    linarith
  have hmert3 : η / 6 * ∑ p ∈ (Finset.Ioc ⌊y ^ lo⌋₊ ⌊y ^ hi⌋₊).filter Nat.Prime, 1 / (p : ℝ)
      ≤ η / 6 * 3 := mul_le_mul_of_nonneg_left (by linarith) hη6.le
  linarith

/-- One strip of the outer sum: primes `q₂ ∈ (y^c, y^d]` against an envelope of the section. -/
theorem sum_strip_harmanTwoPrimeMiddleSum_le {y κ c d η₁ : ℝ} {P : ℝ → ℝ} (hy : 1 < y)
    (hc : 2 / 11 ≤ c) (hd : d ≤ (1 + κ) / 4)
    (hmid : ∀ α₂ ∈ Set.Icc (2 / 11 : ℝ) ((1 + κ) / 4),
      harmanTwoPrimeMiddleSum y κ α₂ ≤ harmanDiscardTwoPrimeSection κ α₂ + η₁)
    (hstrip : ∀ x ∈ Set.Icc c d, harmanDiscardTwoPrimeSection κ x ≤ P x) :
    ∑ p ∈ (Finset.Ioc ⌊y ^ c⌋₊ ⌊y ^ d⌋₊).filter Nat.Prime,
        1 / (p : ℝ) * harmanTwoPrimeMiddleSum y κ (log p / log y)
      ≤ primeScaleSum y c d P
        + η₁ * ∑ p ∈ (Finset.Ioc ⌊y ^ c⌋₊ ⌊y ^ d⌋₊).filter Nat.Prime, 1 / (p : ℝ) := by
  unfold primeScaleSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun p hp => ?_)
  obtain ⟨h1, h2⟩ := logScale_mem_of_mem_Ioc_floor hy (Finset.mem_filter.1 hp).1
  have hm := hmid _ ⟨hc.trans h1.le, h2.trans hd⟩
  have hP := hstrip _ ⟨h1.le, h2⟩
  have hq : 0 ≤ 1 / (p : ℝ) := by positivity
  calc 1 / (p : ℝ) * harmanTwoPrimeMiddleSum y κ (log p / log y)
      ≤ 1 / (p : ℝ) * (P (log p / log y) + η₁) := mul_le_mul_of_nonneg_left (by linarith) hq
    _ = P (log p / log y) / p + η₁ * (1 / p) := by ring

/-- **The two-prime-cofactor discarded sum over prime triples** is eventually at most
`0.0960 + η`. -/
theorem eventually_harmanTwoPrimeTripleSum_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ y : ℝ in atTop, ∑ p ∈ (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ ((1 + 1 / 1000000) / 4 : ℝ)⌋₊).filter Nat.Prime,
        1 / (p : ℝ) * harmanTwoPrimeMiddleSum y (1 / 1000000) (log p / log y) ≤ 960 / 10000 + η := by
  have hη4 : 0 < η / 4 := by positivity
  have hc : 0 < η / 26 := by positivity
  filter_upwards [eventually_harmanTwoPrimeMiddleSum_le (κ := (1 / 1000000)) (by norm_num) (by norm_num) hη4,
    eventually_sum_prime_inv_rpow_le_uniform (a₀ := 2 / 11) (by norm_num),
    eventually_primeScaleSum_le_of_affine (a := (2 / 11 : ℝ)) (b := (65 / 352))
      (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (2 / 11) (65 / 352) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (3 / 4 + 1 / 1000000) (123351807 / 250000000) (127567017 / 250000000) (logUpper 1 ((3 / 4 + 1 / 1000000) / (65 / 352) - 2 + (3 / 4 + 1 / 1000000) * (1 / (2 / 11) - 1 / (65 / 352)))) x) (by norm_num) (by norm_num) hc
      ⟨_, _, harmanTwoPrimeStripEnvelope_affine (by norm_num)⟩ harmanTwoPrimeStripEnvelope_integral_0,
    eventually_primeScaleSum_le_of_affine (a := (65 / 352 : ℝ)) (b := (3 / 16))
      (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (65 / 352) (3 / 16) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (3 / 4 + 1 / 1000000) (56746977 / 125000000) (5868031 / 12500000) (logUpper 1 ((3 / 4 + 1 / 1000000) / (3 / 16) - 2 + (3 / 4 + 1 / 1000000) * (1 / (65 / 352) - 1 / (3 / 16)))) x) (by norm_num) (by norm_num) hc
      ⟨_, _, harmanTwoPrimeStripEnvelope_affine (by norm_num)⟩ harmanTwoPrimeStripEnvelope_integral_1,
    eventually_primeScaleSum_le_of_affine (a := (3 / 16 : ℝ)) (b := (999999 / 5000000))
      (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (3 / 16) (999999 / 5000000) (2 + 1 / 1000000 / (999999 / 5000000)) (1 / 1000000) (469442171 / 1000000000) (276528509 / 500000000) (logUpper 1 (2 + 1 / 1000000 / (999999 / 5000000) + (1 / 1000000) * (1 / (3 / 16) - 1 / (999999 / 5000000)))) x) (by norm_num) (by norm_num) hc
      ⟨_, _, harmanTwoPrimeStripEnvelope_affine (by norm_num)⟩ harmanTwoPrimeStripEnvelope_integral_2,
    eventually_primeScaleSum_le_of_affine (a := (999999 / 5000000 : ℝ)) (b := (41 / 200))
      (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (999999 / 5000000) (41 / 200) (1 / (41 / 200) - 3) (1) (21156277 / 50000000) (452718967 / 1000000000) (logUpper 1 (1 / (41 / 200) - 3 + (1) * (1 / (999999 / 5000000) - 1 / (41 / 200)))) x) (by norm_num) (by norm_num) hc
      ⟨_, _, harmanTwoPrimeStripEnvelope_affine (by norm_num)⟩ harmanTwoPrimeStripEnvelope_integral_3,
    eventually_primeScaleSum_le_of_affine (a := (41 / 200 : ℝ)) (b := (21 / 100))
      (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (41 / 200) (21 / 100) (1 / (21 / 100) - 3) (1) (338674089 / 1000000000) (2826951 / 7812500) (logUpper 0 (1 / (21 / 100) - 3 + (1) * (1 / (41 / 200) - 1 / (21 / 100)))) x) (by norm_num) (by norm_num) hc
      ⟨_, _, harmanTwoPrimeStripEnvelope_affine (by norm_num)⟩ harmanTwoPrimeStripEnvelope_integral_4,
    eventually_primeScaleSum_le_of_affine (a := (21 / 100 : ℝ)) (b := (43 / 200))
      (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (21 / 100) (43 / 200) (1 / (43 / 200) - 3) (1) (131449023 / 500000000) (35065553 / 125000000) (logUpper 0 (1 / (43 / 200) - 3 + (1) * (1 / (21 / 100) - 1 / (43 / 200)))) x) (by norm_num) (by norm_num) hc
      ⟨_, _, harmanTwoPrimeStripEnvelope_affine (by norm_num)⟩ harmanTwoPrimeStripEnvelope_integral_5,
    eventually_primeScaleSum_le_of_affine (a := (43 / 200 : ℝ)) (b := (11 / 50))
      (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (43 / 200) (11 / 50) (1 / (11 / 50) - 3) (1) (19600349 / 100000000) (208895229 / 1000000000) (logUpper 0 (1 / (11 / 50) - 3 + (1) * (1 / (43 / 200) - 1 / (11 / 50)))) x) (by norm_num) (by norm_num) hc
      ⟨_, _, harmanTwoPrimeStripEnvelope_affine (by norm_num)⟩ harmanTwoPrimeStripEnvelope_integral_6,
    eventually_primeScaleSum_le_of_affine (a := (11 / 50 : ℝ)) (b := (9 / 40))
      (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (11 / 50) (9 / 40) (1 / (9 / 40) - 3) (1) (138250973 / 1000000000) (18397767 / 125000000) (logUpper 0 (1 / (9 / 40) - 3 + (1) * (1 / (11 / 50) - 1 / (9 / 40)))) x) (by norm_num) (by norm_num) hc
      ⟨_, _, harmanTwoPrimeStripEnvelope_affine (by norm_num)⟩ harmanTwoPrimeStripEnvelope_integral_7,
    eventually_primeScaleSum_le_of_affine (a := (9 / 40 : ℝ)) (b := (23 / 100))
      (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (9 / 40) (23 / 100) (1 / (23 / 100) - 3) (1) (89957999 / 1000000000) (47836231 / 500000000) (logUpper 0 (1 / (23 / 100) - 3 + (1) * (1 / (9 / 40) - 1 / (23 / 100)))) x) (by norm_num) (by norm_num) hc
      ⟨_, _, harmanTwoPrimeStripEnvelope_affine (by norm_num)⟩ harmanTwoPrimeStripEnvelope_integral_8,
    eventually_primeScaleSum_le_of_affine (a := (23 / 100 : ℝ)) (b := (47 / 200))
      (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (23 / 100) (47 / 200) (1 / (47 / 200) - 3) (1) (3218937 / 62500000) (54723779 / 1000000000) (logUpper 0 (1 / (47 / 200) - 3 + (1) * (1 / (23 / 100) - 1 / (47 / 200)))) x) (by norm_num) (by norm_num) hc
      ⟨_, _, harmanTwoPrimeStripEnvelope_affine (by norm_num)⟩ harmanTwoPrimeStripEnvelope_integral_9,
    eventually_primeScaleSum_le_of_affine (a := (47 / 200 : ℝ)) (b := (6 / 25))
      (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (47 / 200) (6 / 25) (1 / (6 / 25) - 3) (1) (23331247 / 1000000000) (12384673 / 500000000) (logUpper 0 (1 / (6 / 25) - 3 + (1) * (1 / (47 / 200) - 1 / (6 / 25)))) x) (by norm_num) (by norm_num) hc
      ⟨_, _, harmanTwoPrimeStripEnvelope_affine (by norm_num)⟩ harmanTwoPrimeStripEnvelope_integral_10,
    eventually_primeScaleSum_le_of_affine (a := (6 / 25 : ℝ)) (b := (49 / 200))
      (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (6 / 25) (49 / 200) (1 / (49 / 200) - 3) (1) (74531 / 12500000) (3162681 / 500000000) (logUpper 0 (1 / (49 / 200) - 3 + (1) * (1 / (6 / 25) - 1 / (49 / 200)))) x) (by norm_num) (by norm_num) hc
      ⟨_, _, harmanTwoPrimeStripEnvelope_affine (by norm_num)⟩ harmanTwoPrimeStripEnvelope_integral_11,
    eventually_primeScaleSum_le_of_affine (a := (49 / 200 : ℝ)) (b := (1 / 4))
      (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (49 / 200) (1 / 4) (1 / (1 / 4) - 3) (1) (0) (0) (logUpper 0 (1 / (1 / 4) - 3 + (1) * (1 / (49 / 200) - 1 / (1 / 4)))) x) (by norm_num) (by norm_num) hc
      ⟨_, _, harmanTwoPrimeStripEnvelope_affine (by norm_num)⟩ harmanTwoPrimeStripEnvelope_integral_12,
    eventually_gt_atTop (1 : ℝ)] with y hmid hmert h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 hy1
  have hmono : ∀ c d : ℝ, c ≤ d → ⌊y ^ c⌋₊ ≤ ⌊y ^ d⌋₊ := fun c d h =>
    Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hy1.le h)
  have split : ∀ f : ℕ → ℝ,
      ∑ p ∈ (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ ((1 + 1 / 1000000) / 4 : ℝ)⌋₊).filter Nat.Prime, f p =
        (∑ p ∈ (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ (65 / 352 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (65 / 352 : ℝ)⌋₊ ⌊y ^ (3 / 16 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (3 / 16 : ℝ)⌋₊ ⌊y ^ (999999 / 5000000 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (999999 / 5000000 : ℝ)⌋₊ ⌊y ^ (41 / 200 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (41 / 200 : ℝ)⌋₊ ⌊y ^ (21 / 100 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (21 / 100 : ℝ)⌋₊ ⌊y ^ (43 / 200 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (43 / 200 : ℝ)⌋₊ ⌊y ^ (11 / 50 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (11 / 50 : ℝ)⌋₊ ⌊y ^ (9 / 40 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (9 / 40 : ℝ)⌋₊ ⌊y ^ (23 / 100 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (23 / 100 : ℝ)⌋₊ ⌊y ^ (47 / 200 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (47 / 200 : ℝ)⌋₊ ⌊y ^ (6 / 25 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (6 / 25 : ℝ)⌋₊ ⌊y ^ (49 / 200 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (49 / 200 : ℝ)⌋₊ ⌊y ^ ((1 / 4) : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ ((1 / 4) : ℝ)⌋₊ ⌊y ^ ((1 + 1 / 1000000) / 4 : ℝ)⌋₊).filter Nat.Prime, f p) := by
    intro f
    simp only [Finset.sum_filter]
    rw [← Finset.sum_Ioc_consecutive _ (hmono (2 / 11 : ℝ) (65 / 352 : ℝ) (by norm_num))
        (hmono (65 / 352 : ℝ) ((1 + 1 / 1000000) / 4 : ℝ) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (65 / 352 : ℝ) (3 / 16 : ℝ) (by norm_num))
        (hmono (3 / 16 : ℝ) ((1 + 1 / 1000000) / 4 : ℝ) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (3 / 16 : ℝ) (999999 / 5000000 : ℝ) (by norm_num))
        (hmono (999999 / 5000000 : ℝ) ((1 + 1 / 1000000) / 4 : ℝ) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (999999 / 5000000 : ℝ) (41 / 200 : ℝ) (by norm_num))
        (hmono (41 / 200 : ℝ) ((1 + 1 / 1000000) / 4 : ℝ) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (41 / 200 : ℝ) (21 / 100 : ℝ) (by norm_num))
        (hmono (21 / 100 : ℝ) ((1 + 1 / 1000000) / 4 : ℝ) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (21 / 100 : ℝ) (43 / 200 : ℝ) (by norm_num))
        (hmono (43 / 200 : ℝ) ((1 + 1 / 1000000) / 4 : ℝ) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (43 / 200 : ℝ) (11 / 50 : ℝ) (by norm_num))
        (hmono (11 / 50 : ℝ) ((1 + 1 / 1000000) / 4 : ℝ) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (11 / 50 : ℝ) (9 / 40 : ℝ) (by norm_num))
        (hmono (9 / 40 : ℝ) ((1 + 1 / 1000000) / 4 : ℝ) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (9 / 40 : ℝ) (23 / 100 : ℝ) (by norm_num))
        (hmono (23 / 100 : ℝ) ((1 + 1 / 1000000) / 4 : ℝ) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (23 / 100 : ℝ) (47 / 200 : ℝ) (by norm_num))
        (hmono (47 / 200 : ℝ) ((1 + 1 / 1000000) / 4 : ℝ) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (47 / 200 : ℝ) (6 / 25 : ℝ) (by norm_num))
        (hmono (6 / 25 : ℝ) ((1 + 1 / 1000000) / 4 : ℝ) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (6 / 25 : ℝ) (49 / 200 : ℝ) (by norm_num))
        (hmono (49 / 200 : ℝ) ((1 + 1 / 1000000) / 4 : ℝ) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (49 / 200 : ℝ) ((1 / 4) : ℝ) (by norm_num))
        (hmono ((1 / 4) : ℝ) ((1 + 1 / 1000000) / 4 : ℝ) (by norm_num))]
    ring
  have c0 := sum_strip_harmanTwoPrimeMiddleSum_le (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (2 / 11) (65 / 352) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (3 / 4 + 1 / 1000000) (123351807 / 250000000) (127567017 / 250000000) (logUpper 1 ((3 / 4 + 1 / 1000000) / (65 / 352) - 2 + (3 / 4 + 1 / 1000000) * (1 / (2 / 11) - 1 / (65 / 352)))) x)
    (c := (2 / 11 : ℝ)) (d := (65 / 352)) hy1 (by norm_num) (by norm_num) hmid harmanDiscardTwoPrimeSection_le_strip_0
  have c1 := sum_strip_harmanTwoPrimeMiddleSum_le (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (65 / 352) (3 / 16) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (3 / 4 + 1 / 1000000) (56746977 / 125000000) (5868031 / 12500000) (logUpper 1 ((3 / 4 + 1 / 1000000) / (3 / 16) - 2 + (3 / 4 + 1 / 1000000) * (1 / (65 / 352) - 1 / (3 / 16)))) x)
    (c := (65 / 352 : ℝ)) (d := (3 / 16)) hy1 (by norm_num) (by norm_num) hmid harmanDiscardTwoPrimeSection_le_strip_1
  have c2 := sum_strip_harmanTwoPrimeMiddleSum_le (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (3 / 16) (999999 / 5000000) (2 + 1 / 1000000 / (999999 / 5000000)) (1 / 1000000) (469442171 / 1000000000) (276528509 / 500000000) (logUpper 1 (2 + 1 / 1000000 / (999999 / 5000000) + (1 / 1000000) * (1 / (3 / 16) - 1 / (999999 / 5000000)))) x)
    (c := (3 / 16 : ℝ)) (d := (999999 / 5000000)) hy1 (by norm_num) (by norm_num) hmid harmanDiscardTwoPrimeSection_le_strip_2
  have c3 := sum_strip_harmanTwoPrimeMiddleSum_le (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (999999 / 5000000) (41 / 200) (1 / (41 / 200) - 3) (1) (21156277 / 50000000) (452718967 / 1000000000) (logUpper 1 (1 / (41 / 200) - 3 + (1) * (1 / (999999 / 5000000) - 1 / (41 / 200)))) x)
    (c := (999999 / 5000000 : ℝ)) (d := (41 / 200)) hy1 (by norm_num) (by norm_num) hmid harmanDiscardTwoPrimeSection_le_strip_3
  have c4 := sum_strip_harmanTwoPrimeMiddleSum_le (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (41 / 200) (21 / 100) (1 / (21 / 100) - 3) (1) (338674089 / 1000000000) (2826951 / 7812500) (logUpper 0 (1 / (21 / 100) - 3 + (1) * (1 / (41 / 200) - 1 / (21 / 100)))) x)
    (c := (41 / 200 : ℝ)) (d := (21 / 100)) hy1 (by norm_num) (by norm_num) hmid harmanDiscardTwoPrimeSection_le_strip_4
  have c5 := sum_strip_harmanTwoPrimeMiddleSum_le (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (21 / 100) (43 / 200) (1 / (43 / 200) - 3) (1) (131449023 / 500000000) (35065553 / 125000000) (logUpper 0 (1 / (43 / 200) - 3 + (1) * (1 / (21 / 100) - 1 / (43 / 200)))) x)
    (c := (21 / 100 : ℝ)) (d := (43 / 200)) hy1 (by norm_num) (by norm_num) hmid harmanDiscardTwoPrimeSection_le_strip_5
  have c6 := sum_strip_harmanTwoPrimeMiddleSum_le (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (43 / 200) (11 / 50) (1 / (11 / 50) - 3) (1) (19600349 / 100000000) (208895229 / 1000000000) (logUpper 0 (1 / (11 / 50) - 3 + (1) * (1 / (43 / 200) - 1 / (11 / 50)))) x)
    (c := (43 / 200 : ℝ)) (d := (11 / 50)) hy1 (by norm_num) (by norm_num) hmid harmanDiscardTwoPrimeSection_le_strip_6
  have c7 := sum_strip_harmanTwoPrimeMiddleSum_le (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (11 / 50) (9 / 40) (1 / (9 / 40) - 3) (1) (138250973 / 1000000000) (18397767 / 125000000) (logUpper 0 (1 / (9 / 40) - 3 + (1) * (1 / (11 / 50) - 1 / (9 / 40)))) x)
    (c := (11 / 50 : ℝ)) (d := (9 / 40)) hy1 (by norm_num) (by norm_num) hmid harmanDiscardTwoPrimeSection_le_strip_7
  have c8 := sum_strip_harmanTwoPrimeMiddleSum_le (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (9 / 40) (23 / 100) (1 / (23 / 100) - 3) (1) (89957999 / 1000000000) (47836231 / 500000000) (logUpper 0 (1 / (23 / 100) - 3 + (1) * (1 / (9 / 40) - 1 / (23 / 100)))) x)
    (c := (9 / 40 : ℝ)) (d := (23 / 100)) hy1 (by norm_num) (by norm_num) hmid harmanDiscardTwoPrimeSection_le_strip_8
  have c9 := sum_strip_harmanTwoPrimeMiddleSum_le (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (23 / 100) (47 / 200) (1 / (47 / 200) - 3) (1) (3218937 / 62500000) (54723779 / 1000000000) (logUpper 0 (1 / (47 / 200) - 3 + (1) * (1 / (23 / 100) - 1 / (47 / 200)))) x)
    (c := (23 / 100 : ℝ)) (d := (47 / 200)) hy1 (by norm_num) (by norm_num) hmid harmanDiscardTwoPrimeSection_le_strip_9
  have c10 := sum_strip_harmanTwoPrimeMiddleSum_le (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (47 / 200) (6 / 25) (1 / (6 / 25) - 3) (1) (23331247 / 1000000000) (12384673 / 500000000) (logUpper 0 (1 / (6 / 25) - 3 + (1) * (1 / (47 / 200) - 1 / (6 / 25)))) x)
    (c := (47 / 200 : ℝ)) (d := (6 / 25)) hy1 (by norm_num) (by norm_num) hmid harmanDiscardTwoPrimeSection_le_strip_10
  have c11 := sum_strip_harmanTwoPrimeMiddleSum_le (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (6 / 25) (49 / 200) (1 / (49 / 200) - 3) (1) (74531 / 12500000) (3162681 / 500000000) (logUpper 0 (1 / (49 / 200) - 3 + (1) * (1 / (6 / 25) - 1 / (49 / 200)))) x)
    (c := (6 / 25 : ℝ)) (d := (49 / 200)) hy1 (by norm_num) (by norm_num) hmid harmanDiscardTwoPrimeSection_le_strip_11
  have c12 := sum_strip_harmanTwoPrimeMiddleSum_le (P := fun x => harmanTwoPrimeStripEnvelope (1 / 1000000) (49 / 200) (1 / 4) (1 / (1 / 4) - 3) (1) (0) (0) (logUpper 0 (1 / (1 / 4) - 3 + (1) * (1 / (49 / 200) - 1 / (1 / 4)))) x)
    (c := (49 / 200 : ℝ)) (d := (1 / 4)) hy1 (by norm_num) (by norm_num) hmid harmanDiscardTwoPrimeSection_le_strip_12
  have ct := sum_strip_harmanTwoPrimeMiddleSum_le (P := fun _ => 30 * (1 / 1000000))
    (c := 1 / 4) (d := (1 + 1 / 1000000) / 4) hy1 (by norm_num) le_rfl hmid
    (fun x hx => harmanDiscardTwoPrimeSection_le_tail (by norm_num) (by norm_num) hx.1 hx.2)
  have htailc : primeScaleSum y (1 / 4) ((1 + 1 / 1000000) / 4) (fun _ => 30 * (1 / 1000000)) =
      30 * (1 / 1000000) * ∑ p ∈ (Finset.Ioc ⌊y ^ ((1 / 4) : ℝ)⌋₊ ⌊y ^ ((1 + 1 / 1000000) / 4 : ℝ)⌋₊).filter Nat.Prime, 1 / (p : ℝ) := by
    unfold primeScaleSum; rw [Finset.mul_sum]; congr 1; funext p; ring
  have htailm := hmert (1 / 4) ((1 + 1 / 1000000) / 4) (by norm_num) (by norm_num)
  have htotm := hmert (2 / 11) ((1 + 1 / 1000000) / 4) (by norm_num) (by norm_num)
  have hl1 : log (((1 + 1 / 1000000) / 4) / (1 / 4)) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((1 + 1 / 1000000) / 4) / (1 / 4) by norm_num)
    norm_num at this ⊢; linarith
  have hl2 : log (((1 + 1 / 1000000) / 4) / (2 / 11)) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((1 + 1 / 1000000) / 4) / (2 / 11) by norm_num)
    norm_num at this ⊢; linarith
  have hs1 := split (fun p => 1 / (p : ℝ) * harmanTwoPrimeMiddleSum y (1 / 1000000) (log p / log y))
  have hs2 := split (fun p => 1 / (p : ℝ))
  have hmert' : η / 4 * ∑ p ∈ (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ ((1 + 1 / 1000000) / 4 : ℝ)⌋₊).filter Nat.Prime,
      1 / (p : ℝ) ≤ η / 4 * 2 := mul_le_mul_of_nonneg_left (by linarith) hη4.le
  have htail' : 30 * (1 / 1000000) * ∑ p ∈ (Finset.Ioc ⌊y ^ ((1 / 4) : ℝ)⌋₊ ⌊y ^ ((1 + 1 / 1000000) / 4 : ℝ)⌋₊).filter Nat.Prime,
      1 / (p : ℝ) ≤ 30 * (1 / 1000000) * 2 := mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
  rw [htailc] at ct
  rw [hs1]
  rw [hs2] at hmert'
  linarith

end

end RHTower.Sieve
