import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaRoutePGeometricKLBurnolHolonomyVirial

/-!
# Route P dyadic information and binary Möbius rigidity

The full geometric-valuation information chirality is exactly the infinite sum of its binary
valuation-bit chiralities.  Every bit has the same strict orientation off the critical wall; the
hidden residual tends to zero, so no cancelling tail is lost.

Coefficientwise this is binary Möbius inversion.  For exponent `2^v m`, `m` odd, alternating
Gamma contributions from all visible dyadic levels are `-1,-2,...,-2^(v-1),2^v`; their signed
sum is exactly `1`.  Thus the full dyadic Gamma tower reconstructs the positive Bose coefficient
instead of reversing it.
-/

open Real Set Filter Topology BigOperators

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Bernoulli information chirality carried by binary valuation digit `j`. -/
def sourceHorizontalDyadicBitKLChirality (c s : ℝ) (j : ℕ) : ℝ :=
  RHTower.sourceHorizontalCenteredBernoulliKLChirality
    ((2 : ℝ) ^ j * c) ((2 : ℝ) ^ j * s)

/-- Exact finite binary-digit decomposition, with unresolved higher-valuation fibre retained. -/
theorem sourceHorizontalGeometricKLChirality_finiteDyadic_decomposition
    {c s : ℝ} (hplus : c + s < 0) (hminus : c - s < 0) (N : ℕ) :
    sourceHorizontalCenteredGeometricKLChirality c s =
      (∑ j ∈ Finset.range N, sourceHorizontalDyadicBitKLChirality c s j) +
        sourceHorizontalCenteredGeometricKLChirality
          ((2 : ℝ) ^ N * c) ((2 : ℝ) ^ N * s) := by
  induction N with
  | zero => simp [sourceHorizontalDyadicBitKLChirality]
  | succ N ih =>
      have hpow : 0 < (2 : ℝ) ^ N := by positivity
      have hpN : (2 : ℝ) ^ N * c + (2 : ℝ) ^ N * s < 0 := by
        nlinarith
      have hmN : (2 : ℝ) ^ N * c - (2 : ℝ) ^ N * s < 0 := by
        nlinarith
      rw [ih, sourceHorizontalCenteredGeometricKLChirality_dyadic_split hpN hmN,
        Finset.sum_range_succ]
      unfold sourceHorizontalDyadicBitKLChirality
      rw [pow_succ]
      ring

/-- Every visible binary digit has same strict orientation off critical wall. -/
theorem sourceHorizontalDyadicBitKLChirality_pos
    {c s : ℝ} (hc : c < 0) (hs : 0 < s) (hsc : s < -c) (j : ℕ) :
    0 < sourceHorizontalDyadicBitKLChirality c s j := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have hcj : (2 : ℝ) ^ j * c < 0 := mul_neg_of_pos_of_neg hpow hc
  have hsj : |(2 : ℝ) ^ j * s| < -((2 : ℝ) ^ j * c) := by
    rw [abs_mul, abs_of_pos hpow, abs_of_pos hs]
    nlinarith
  have hne := (RHTower.sourceHorizontalCenteredBernoulliKLChirality_eq_zero_iff hcj hsj).not
  have hnonzero : RHTower.sourceHorizontalCenteredBernoulliKLChirality
      ((2 : ℝ) ^ j * c) ((2 : ℝ) ^ j * s) ≠ 0 := hne.mpr (by positivity)
  have hmono := RHTower.sourceHorizontalCenteredBernoulliKLChirality_strictMonoOn_nonneg
    ((2 : ℝ) ^ j * c)
    (by constructor <;> nlinarith : (0 : ℝ) ∈ Set.Icc 0 (-((2 : ℝ) ^ j * c)))
    (by constructor <;> nlinarith : (2 : ℝ) ^ j * s ∈ Set.Icc 0 (-((2 : ℝ) ^ j * c)))
    (by positivity)
  rw [RHTower.sourceHorizontalCenteredBernoulliKLChirality_zero] at hmono
  exact hmono

private theorem tendsto_sourceHorizontalBoseLogPartition_neg_mul_atTop
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => sourceHorizontalBoseLogPartition (-a * x))
      atTop (𝓝 0) := by
  have hscale : Tendsto (fun x : ℝ => a * x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop ha tendsto_id
  have hexp0 := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have hexp : Tendsto (fun x : ℝ => Real.exp (-a * x)) atTop (𝓝 0) := by
    apply hexp0.congr'
    filter_upwards with x
    change Real.exp (-(a * x)) = Real.exp (-a * x)
    congr 1
    ring
  have hden : Tendsto (fun x : ℝ => 1 - Real.exp (-a * x)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hexp
  have hlog := hden.log one_ne_zero
  simpa [sourceHorizontalBoseLogPartition] using hlog.neg

private theorem tendsto_mul_sourceHorizontalBoseMean_neg_mul_atTop
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => x * sourceHorizontalBoseMean (-a * x))
      atTop (𝓝 0) := by
  have hscale : Tendsto (fun x : ℝ => a * x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop ha tendsto_id
  have hexp0 := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have hexp : Tendsto (fun x : ℝ => Real.exp (-a * x)) atTop (𝓝 0) := by
    apply hexp0.congr'
    filter_upwards with x
    change Real.exp (-(a * x)) = Real.exp (-a * x)
    congr 1
    ring
  have hden : Tendsto (fun x : ℝ => 1 - Real.exp (-a * x)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hexp
  have hnum0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) a ha
  have hnum : Tendsto (fun x : ℝ => x * Real.exp (-a * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using hnum0
  have hquot := hnum.div hden one_ne_zero
  have hquot' : Tendsto
      (fun x : ℝ => x * sourceHorizontalBoseMean (-a * x))
      atTop (𝓝 (0 / 1)) := by
    apply hquot.congr'
    filter_upwards with x
    simp only [Pi.div_apply]
    rw [sourceHorizontalBoseMean]
    ring
  simpa using hquot'

/-- Hidden geometric fibre disappears at infinite binary depth. -/
theorem tendsto_sourceHorizontalGeometricKLChirality_dyadicResidual
    {c s : ℝ} (hplus : c + s < 0) (hminus : c - s < 0) :
    Tendsto (fun N : ℕ => sourceHorizontalCenteredGeometricKLChirality
      ((2 : ℝ) ^ N * c) ((2 : ℝ) ^ N * s)) atTop (𝓝 0) := by
  let R : ℕ → ℝ := fun N => (2 : ℝ) ^ N
  have hR : Tendsto R atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hap : 0 < -(c + s) := by linarith
  have ham : 0 < -(c - s) := by linarith
  have hmp0 := (tendsto_mul_sourceHorizontalBoseMean_neg_mul_atTop hap).comp hR
  have hmm0 := (tendsto_mul_sourceHorizontalBoseMean_neg_mul_atTop ham).comp hR
  have hlp0 := (tendsto_sourceHorizontalBoseLogPartition_neg_mul_atTop hap).comp hR
  have hlm0 := (tendsto_sourceHorizontalBoseLogPartition_neg_mul_atTop ham).comp hR
  have hmp : Tendsto (fun N : ℕ => R N *
      sourceHorizontalBoseMean (R N * c + R N * s)) atTop (𝓝 0) := by
    apply hmp0.congr'
    filter_upwards with N
    apply congrArg (fun z => R N * sourceHorizontalBoseMean z)
    ring
  have hmm : Tendsto (fun N : ℕ => R N *
      sourceHorizontalBoseMean (R N * c - R N * s)) atTop (𝓝 0) := by
    apply hmm0.congr'
    filter_upwards with N
    apply congrArg (fun z => R N * sourceHorizontalBoseMean z)
    ring
  have hlp : Tendsto (fun N : ℕ =>
      sourceHorizontalBoseLogPartition (R N * c + R N * s)) atTop (𝓝 0) := by
    apply hlp0.congr'
    filter_upwards with N
    apply congrArg sourceHorizontalBoseLogPartition
    ring
  have hlm : Tendsto (fun N : ℕ =>
      sourceHorizontalBoseLogPartition (R N * c - R N * s)) atTop (𝓝 0) := by
    apply hlm0.congr'
    filter_upwards with N
    apply congrArg sourceHorizontalBoseLogPartition
    ring
  have h := ((hmp.add hmm).const_mul (2 * s)).sub ((hlp.sub hlm).const_mul 2)
  convert h using 1
  · ext N
    rw [sourceHorizontalCenteredGeometricKLChirality]
    dsimp only [R]
    ring
  · ring

/-- Full geometric information chirality is exactly sum of all binary valuation digits. -/
theorem hasSum_sourceHorizontalDyadicBitKLChirality
    {c s : ℝ} (hc : c < 0) (hs : 0 < s) (hsc : s < -c) :
    HasSum (sourceHorizontalDyadicBitKLChirality c s)
      (sourceHorizontalCenteredGeometricKLChirality c s) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun j => (sourceHorizontalDyadicBitKLChirality_pos hc hs hsc j).le)]
  have hplus : c + s < 0 := by linarith
  have hminus : c - s < 0 := by linarith
  have hres := tendsto_sourceHorizontalGeometricKLChirality_dyadicResidual hplus hminus
  have hfinite := sourceHorizontalGeometricKLChirality_finiteDyadic_decomposition
    hplus hminus
  have heq : (fun N : ℕ => ∑ j ∈ Finset.range N,
      sourceHorizontalDyadicBitKLChirality c s j) =
      fun N : ℕ => sourceHorizontalCenteredGeometricKLChirality c s -
        sourceHorizontalCenteredGeometricKLChirality
          ((2 : ℝ) ^ N * c) ((2 : ℝ) ^ N * s) := by
    funext N
    linarith [hfinite N]
  rw [heq]
  simpa using tendsto_const_nhds.sub hres

/-- Signed alternating-Gamma contribution to exponent `2^v m` from binary level `j≤v`. -/
def sourceHorizontalDyadicGammaExponentContribution
    (v m j : ℕ) : ℤ :=
  (-1 : ℤ) ^ ((2 ^ (v - j)) * m + 1) * (2 : ℤ) ^ j

private theorem sourceHorizontalDyadicGammaExponentContribution_of_lt
    {v m j : ℕ} (hj : j < v) :
    sourceHorizontalDyadicGammaExponentContribution v m j = -(2 : ℤ) ^ j := by
  unfold sourceHorizontalDyadicGammaExponentContribution
  have hd : 0 < v - j := Nat.sub_pos_of_lt hj
  have heven : Even ((2 ^ (v - j)) * m) := by
    have hpow : Even (2 ^ (v - j)) := by
      exact Nat.even_pow.mpr ⟨even_two, ne_of_gt hd⟩
    exact hpow.mul_right m
  have hodd : Odd ((2 ^ (v - j)) * m + 1) := heven.add_one
  rw [hodd.neg_one_pow]
  ring

private theorem sourceHorizontalDyadicGammaExponentContribution_last
    {v m : ℕ} (hm : Odd m) :
    sourceHorizontalDyadicGammaExponentContribution v m v = (2 : ℤ) ^ v := by
  unfold sourceHorizontalDyadicGammaExponentContribution
  have heven : Even (2 ^ (v - v) * m + 1) := by
    simpa using hm.add_one
  rw [heven.neg_one_pow]
  simp

/-- **Binary Möbius coefficient law.**  All alternating primitive contributions to exponent
`2^v m`, with `m` odd, collapse to one positive unit. -/
theorem sourceHorizontal_dyadicGammaExponentCoefficient_eq_one
    (v m : ℕ) (hm : Odd m) :
    (∑ j ∈ Finset.range (v + 1),
      sourceHorizontalDyadicGammaExponentContribution v m j) = 1 := by
  rw [Finset.sum_range_succ]
  rw [sourceHorizontalDyadicGammaExponentContribution_last hm]
  have hhead : (∑ j ∈ Finset.range v,
      sourceHorizontalDyadicGammaExponentContribution v m j) =
      -(∑ j ∈ Finset.range v, (2 : ℤ) ^ j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    exact sourceHorizontalDyadicGammaExponentContribution_of_lt hj
  rw [hhead]
  have hgeom : (∑ j ∈ Finset.range v, (2 : ℤ) ^ j) = (2 : ℤ) ^ v - 1 := by
    have h := geom_sum_mul (2 : ℤ) v
    nlinarith
  rw [hgeom]
  ring

end

end RHTower.HedenmalmThetaSource
