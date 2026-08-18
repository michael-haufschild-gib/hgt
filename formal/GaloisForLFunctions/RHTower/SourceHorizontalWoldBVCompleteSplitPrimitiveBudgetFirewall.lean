import GaloisForLFunctions.RHTower.SourceHorizontalWoldBVKreinSelectedResidueThirdJetDescent
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedSignedControlProducer

/-!
# Complete BV split versus the primitive Euler budget

The selected endpoint residue cannot be studied in isolation if descent is required to preserve
the proved finite Green--Stokes conservation law.  Its omitted interior channel is the normalized
positive Wold cubic moment.  This module proves the exact finite identity

`interiorThirdJet N + endpointThirdJet N = 1`.

Consequently, coefficient-faithful positivity of both channels fixes their total energy at
`8 * normSq c`, at every finite prime clock.  The literal primitive Euler source budget is
strictly smaller for every nonzero coefficient.  Thus no complete positive descent preserving
both Green--Stokes channels can be primitive-budget contractive.  This is a finite arithmetic
firewall, not an asymptotic or RH-dependent statement.

The result leaves one structurally different survivor: retain the interior channel with its Krein
sign and prove an independent signed arithmetic comparison.  It does not manufacture that law.
-/

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Literal interior third jet: normalized positive cubic Wold moment at finite prime clock. -/
def sourceHorizontalWoldBVGreenStokesInteriorThirdJet (N : ℕ) : ℝ :=
  sourceHorizontalWoldOrderedNormalizedMoment N 2

/-- Every finite interior third jet is strictly positive, not merely nonnegative. -/
theorem sourceHorizontalWoldBVGreenStokesInteriorThirdJet_pos (N : ℕ) :
    0 < sourceHorizontalWoldBVGreenStokesInteriorThirdJet N := by
  rw [sourceHorizontalWoldBVGreenStokesInteriorThirdJet,
    sourceHorizontalWoldOrderedNormalizedMoment]
  apply div_pos
  · apply Finset.sum_pos'
    · intro n hn
      exact mul_nonneg (woldCoeff_nonneg 1 _) (sq_nonneg _)
    · refine ⟨0, by simp, ?_⟩
      exact mul_pos (woldCoeff_pos 1 _)
        (sq_pos_of_pos (xiMassNthPrimeLogHeight_pos 0))
  · exact pow_pos (xiMassNthPrimeLogHeight_pos N) 3

/-- Finite Green--Stokes conservation at third order: interior plus endpoint is exactly one. -/
theorem sourceHorizontalWoldBVGreenStokesInteriorThirdJet_add_endpointThirdJet
    (N : ℕ) :
    sourceHorizontalWoldBVGreenStokesInteriorThirdJet N +
        sourceHorizontalWoldBVGreenStokesEndpointThirdJet N = 1 := by
  rw [sourceHorizontalWoldBVGreenStokesInteriorThirdJet,
    sourceHorizontalWoldOrderedNormalizedMoment,
    sourceHorizontalWoldBVGreenStokesEndpointThirdJet,
    sourceHorizontalWoldResidualPrimitiveCubicCoefficient,
    sourceHorizontalWoldNaturalCubicMoment_nthPrime_eq_ordered]
  have hH : xiMassNthPrimeLogHeight N ≠ 0 :=
    (xiMassNthPrimeLogHeight_pos N).ne'
  norm_num only [Nat.reduceAdd]
  field_simp [hH]
  ring

/-- Interior third jet converges to its complementary universal value `1/3`. -/
theorem tendsto_sourceHorizontalWoldBVGreenStokesInteriorThirdJet :
    Tendsto sourceHorizontalWoldBVGreenStokesInteriorThirdJet atTop
      (nhds (1 / 3 : ℝ)) := by
  change Tendsto
    (fun N : ℕ => sourceHorizontalWoldOrderedNormalizedMoment N 2) atTop
      (nhds (1 / 3 : ℝ))
  simpa using tendsto_sourceHorizontalWoldOrderedNormalizedMoment 2

private theorem sourceBudget_nthPrimeSubtype_zero_eq :
    (nthPrimeSubtype 0 : ℕ) = 2 := by
  simp [nthPrimeSubtype]

private theorem sourceBudget_nthPrimeSubtype_one_eq :
    (nthPrimeSubtype 1 : ℕ) = 3 := by
  change ((nthPrimeEquiv 1 : Nat.Primes) : ℕ) = 3
  have h : nthPrimeEquiv 1 = (⟨3, Nat.prime_three⟩ : Nat.Primes) := by
    apply nthPrimeEquiv.symm.injective
    rw [nthPrimeEquiv.symm_apply_apply]
    change 1 = Nat.count Nat.Prime 3
    decide
  exact congrArg Subtype.val h

private theorem sourceBudget_nthPrimeSubtype_two_eq :
    (nthPrimeSubtype 2 : ℕ) = 5 := by
  change ((nthPrimeEquiv 2 : Nat.Primes) : ℕ) = 5
  have h : nthPrimeEquiv 2 = (⟨5, by norm_num⟩ : Nat.Primes) := by
    apply nthPrimeEquiv.symm.injective
    rw [nthPrimeEquiv.symm_apply_apply]
    change 2 = Nat.count Nat.Prime 5
    decide
  exact congrArg Subtype.val h

private theorem sourceBudget_nthPrimeSubtype_three_eq :
    (nthPrimeSubtype 3 : ℕ) = 7 := by
  change ((nthPrimeEquiv 3 : Nat.Primes) : ℕ) = 7
  have h : nthPrimeEquiv 3 = (⟨7, by norm_num⟩ : Nat.Primes) := by
    apply nthPrimeEquiv.symm.injective
    rw [nthPrimeEquiv.symm_apply_apply]
    change 3 = Nat.count Nat.Prime 7
    decide
  exact congrArg Subtype.val h

/-- Ordered-prime logarithmic tail after `2,3,5` is bounded by the continuous integer tail
starting at `7`, and hence by `1 / log 6`. -/
theorem tsum_nthPrime_invNatLogSq_tail_le :
    (∑' n : ℕ, invNatLogSq (nthPrimeSubtype (n + 3))) ≤
      (Real.log 6)⁻¹ := by
  have hIntegral :
      (∑' n : ℕ, routePInvLogSqContinuous (n + 6 + 1 : ℕ)) ≤
        (Real.log 6)⁻¹ := by
    have hanti : AntitoneOn routePInvLogSqContinuous (Ici 6) :=
      routePInvLogSqContinuous_antitoneOn.mono (by
        intro x hx
        change 6 ≤ x at hx
        change 2 ≤ x
        linarith)
    simpa [routePInvLogSqContinuous] using
      hanti.tsum_comp_add_le_integral 6
        (integrableOn_inv_div_log_sq_Ioi (by norm_num : (1 : ℝ) < 6))
        (fun t ht => by
          change 6 < t at ht
          exact div_nonneg (inv_nonneg.mpr (by linarith))
            (sq_nonneg (Real.log t)))
  have hMajor : ∀ n : ℕ,
      invNatLogSq (nthPrimeSubtype (n + 3)) ≤ invNatLogSq (n + 7) := by
    intro n
    have hp7 : n + 7 ≤ (nthPrimeSubtype (n + 3) : ℕ) := by
      have h := nthPrimeSubtype_strictMono.add_le_nat n 3
      rw [sourceBudget_nthPrimeSubtype_three_eq] at h
      simpa [Nat.add_comm] using h
    have hcont := routePInvLogSqContinuous_antitoneOn
      (show (n + 7 : ℝ) ∈ Ici 2 by
        change (2 : ℝ) ≤ n + 7
        exact_mod_cast (by omega : 2 ≤ n + 7))
      (show (nthPrimeSubtype (n + 3) : ℝ) ∈ Ici 2 by
        change (2 : ℝ) ≤ (nthPrimeSubtype (n + 3) : ℝ)
        exact_mod_cast le_trans (by omega : 2 ≤ n + 7) hp7)
      (by exact_mod_cast hp7)
    simpa [invNatLogSq, routePInvLogSqContinuous, div_eq_mul_inv,
      mul_comm] using hcont
  have hleft : Summable
      (fun n : ℕ => invNatLogSq (nthPrimeSubtype (n + 3))) := by
    apply summable_prime_invNatLogSq.comp_injective
    intro a b h
    exact Nat.add_right_cancel (nthPrimeSubtype_injective h)
  have hright : Summable (fun n : ℕ => invNatLogSq (n + 7)) := by
    exact summable_invNatLogSq.comp_injective (by
      intro a b h
      exact Nat.add_right_cancel h)
  calc
    (∑' n : ℕ, invNatLogSq (nthPrimeSubtype (n + 3))) ≤
        ∑' n : ℕ, invNatLogSq (n + 7) :=
      Summable.tsum_le_tsum hMajor hleft hright
    _ ≤ (Real.log 6)⁻¹ := by
      convert hIntegral using 1
      apply tsum_congr
      intro n
      rw [invNatLogSq, routePInvLogSqContinuous]
      norm_cast
      ring_nf

/-- Prime logarithmic inverse-square mass is strictly below `2`.  The proof is symbolic: isolate
`2,3,5`, dominate every later prime by the integer tail from `7`, then integrate from `6`. -/
theorem tsum_prime_invNatLogSq_lt_two :
    (∑' p : Nat.Primes, invNatLogSq p) < 2 := by
  have hsplit :
      (∑' p : Nat.Primes, invNatLogSq p) =
        invNatLogSq 2 + invNatLogSq 3 + invNatLogSq 5 +
          ∑' n : ℕ, invNatLogSq (nthPrimeSubtype (n + 3)) := by
    rw [← nthPrimeEquiv.tsum_eq]
    have hs : Summable (fun n : ℕ => invNatLogSq (nthPrimeEquiv n)) :=
      nthPrimeEquiv.summable_iff.mpr summable_prime_invNatLogSq
    rw [← hs.sum_add_tsum_nat_add 3]
    simp only [nthPrimeEquiv_apply]
    simp [sourceBudget_nthPrimeSubtype_zero_eq,
      sourceBudget_nthPrimeSubtype_one_eq,
      sourceBudget_nthPrimeSubtype_two_eq, Finset.sum_range_succ]
  have hlog2 := Real.log_two_gt_d9
  have hlog3 := Real.log_three_gt_d9
  have hlog5 := Real.log_five_gt_d9
  have hl2p : 0 < Real.log 2 := by linarith
  have hl3p : 0 < Real.log 3 := by linarith
  have hl5p : 0 < Real.log 5 := by linarith
  have hs2 : (0.6931471803 : ℝ) ^ 2 < Real.log 2 ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hl2p.le).2 hlog2
  have hs3 : (1.0986122885 : ℝ) ^ 2 < Real.log 3 ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hl3p.le).2 hlog3
  have hs5 : (1.6094379123 : ℝ) ^ 2 < Real.log 5 ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hl5p.le).2 hlog5
  have hf2 : invNatLogSq 2 < (21 / 20 : ℝ) := by
    rw [invNatLogSq]
    apply (div_lt_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hl2p))).2
    norm_num at hs2 ⊢
    nlinarith
  have hf3 : invNatLogSq 3 < (7 / 25 : ℝ) := by
    rw [invNatLogSq]
    apply (div_lt_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hl3p))).2
    norm_num at hs3 ⊢
    nlinarith
  have hf5 : invNatLogSq 5 < (2 / 25 : ℝ) := by
    rw [invNatLogSq]
    apply (div_lt_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hl5p))).2
    norm_num at hs5 ⊢
    nlinarith
  have hlog6eq : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have hl6 : (25 / 14 : ℝ) < Real.log 6 := by
    rw [hlog6eq]
    nlinarith
  have hl6p : 0 < Real.log 6 := by linarith
  have hinv6 : (Real.log 6)⁻¹ < (14 / 25 : ℝ) := by
    apply (inv_lt_iff_one_lt_mul₀' hl6p).2
    nlinarith
  rw [hsplit]
  have ht := tsum_nthPrime_invNatLogSq_tail_le
  linarith

/-- Primitive collision budget is bounded by its coefficient-faithful prime logarithmic major. -/
theorem routePPrimitiveCollisionCubicTraceBudget_le_primeInvLogSq :
    routePPrimitiveCollisionCubicTraceBudget ≤
      (115 / 432 : ℝ) * ∑' p : Nat.Primes, invNatLogSq p := by
  let major : Nat.Primes × ℕ → ℝ := fun pe =>
    (115 / 864 : ℝ) * invNatLogSq pe.1 * (1 / 2 : ℝ) ^ pe.2
  have hmajorNonneg : 0 ≤ major := by
    intro pe
    dsimp only [major]
    rw [invNatLogSq]
    positivity
  have hmajor : Summable major := by
    rw [summable_prod_of_nonneg hmajorNonneg]
    constructor
    · intro p
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left
        ((115 / 864 : ℝ) * invNatLogSq p)
    · have hprime := summable_prime_invNatLogSq.mul_left (115 / 432 : ℝ)
      apply hprime.congr
      intro p
      dsimp only [major]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
  have hbudgetMajor :
      routePPrimitiveCollisionCubicTraceBudget ≤ ∑' pe, major pe := by
    rw [routePPrimitiveCollisionCubicTraceBudget]
    exact Summable.tsum_le_tsum xiGammaEulerPrimitiveCubicLogMomentWeight_le
      summable_xiGammaEulerPrimitiveCubicLogMomentWeight hmajor
  have hmajorEq :
      (∑' pe, major pe) =
        (115 / 432 : ℝ) * ∑' p : Nat.Primes, invNatLogSq p := by
    rw [hmajor.tsum_prod, ← tsum_mul_left]
    apply tsum_congr
    intro p
    dsimp only [major]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    ring
  rwa [hmajorEq] at hbudgetMajor

/-- Sharpened arithmetic comparison needed by the signed-source audit: primitive base budget is
strictly below `1`, twice sharper than the earlier one-zero-quantum estimate. -/
theorem routePPrimitiveBaseCauchyCubicTraceBudget_lt_one :
    routePPrimitiveBaseCauchyCubicTraceBudget < 1 := by
  rw [routePPrimitiveBaseCauchyCubicTraceBudget_eq]
  have hmajor := routePPrimitiveCollisionCubicTraceBudget_le_primeInvLogSq
  have hprime := tsum_prime_invNatLogSq_lt_two
  nlinarith

/-- Coefficient energy carried by the positive interior channel. -/
def sourceHorizontalWoldBVInteriorEnergy (c : ℂ) (N : ℕ) : ℝ :=
  8 * Complex.normSq c * sourceHorizontalWoldBVGreenStokesInteriorThirdJet N

/-- Complete positive Green--Stokes split has fixed finite energy `8 * normSq c`. -/
theorem sourceHorizontalWoldBVInteriorEnergy_add_endpointEnergy
    (c : ℂ) (N : ℕ) :
    sourceHorizontalWoldBVInteriorEnergy c N +
        sourceHorizontalWoldBVKreinGhostEnergy c N =
      8 * Complex.normSq c := by
  rw [sourceHorizontalWoldBVInteriorEnergy,
    sourceHorizontalWoldBVKreinGhostEnergy]
  calc
    8 * Complex.normSq c * sourceHorizontalWoldBVGreenStokesInteriorThirdJet N +
          8 * Complex.normSq c * sourceHorizontalWoldBVGreenStokesEndpointThirdJet N =
        8 * Complex.normSq c *
          (sourceHorizontalWoldBVGreenStokesInteriorThirdJet N +
            sourceHorizontalWoldBVGreenStokesEndpointThirdJet N) := by ring
    _ = 8 * Complex.normSq c := by
      rw [sourceHorizontalWoldBVGreenStokesInteriorThirdJet_add_endpointThirdJet]
      ring

/-- Sharp finite-clock firewall: complete positive source-conservation energy strictly exceeds
the literal primitive Euler budget for every nonzero coefficient and every clock. -/
theorem sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_lt_completePositiveSplit
    {c : ℂ} (hc : c ≠ 0) (N : ℕ) :
    sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c <
      sourceHorizontalWoldBVInteriorEnergy c N +
        sourceHorizontalWoldBVKreinGhostEnergy c N := by
  rw [sourceHorizontalWoldBVInteriorEnergy_add_endpointEnergy]
  have hnorm : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc
  have hbudget :=
    sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_lt_quantum hc
  nlinarith

/-- Canonical Krein conservation trace: endpoint channel positive, interior channel negative. -/
def sourceHorizontalWoldBVKreinSignedSplitEnergy (c : ℂ) (N : ℕ) : ℝ :=
  sourceHorizontalWoldBVKreinGhostEnergy c N -
    sourceHorizontalWoldBVInteriorEnergy c N

/-- Exact finite signed split.  No budget term is inserted by definition. -/
theorem sourceHorizontalWoldBVKreinSignedSplitEnergy_eq
    (c : ℂ) (N : ℕ) :
    sourceHorizontalWoldBVKreinSignedSplitEnergy c N =
      8 * Complex.normSq c *
        (2 * sourceHorizontalWoldBVGreenStokesEndpointThirdJet N - 1) := by
  have hinterior : sourceHorizontalWoldBVGreenStokesInteriorThirdJet N =
      1 - sourceHorizontalWoldBVGreenStokesEndpointThirdJet N := by
    linarith [sourceHorizontalWoldBVGreenStokesInteriorThirdJet_add_endpointThirdJet N]
  rw [sourceHorizontalWoldBVKreinSignedSplitEnergy,
    sourceHorizontalWoldBVKreinGhostEnergy,
    sourceHorizontalWoldBVInteriorEnergy, hinterior]
  ring

/-- Canonical signed conservation trace converges to `8/3 * normSq c`. -/
theorem tendsto_sourceHorizontalWoldBVKreinSignedSplitEnergy (c : ℂ) :
    Tendsto (sourceHorizontalWoldBVKreinSignedSplitEnergy c) atTop
      (nhds ((8 / 3 : ℝ) * Complex.normSq c)) := by
  have h :=
    (tendsto_sourceHorizontalWoldBVGreenStokesEndpointThirdJet.const_mul
      (16 * Complex.normSq c)).sub_const (8 * Complex.normSq c)
  convert h using 1
  · funext N
    rw [sourceHorizontalWoldBVKreinSignedSplitEnergy_eq]
    ring_nf
  · ring_nf

/-- Even the canonical Krein-signed limiting trace strictly exceeds the literal primitive budget
for every nonzero coefficient. -/
theorem sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_lt_signedSplitLimit
    {c : ℂ} (hc : c ≠ 0) :
    sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c <
      (8 / 3 : ℝ) * Complex.normSq c := by
  have hnorm : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc
  have hbudget := routePPrimitiveBaseCauchyCubicTraceBudget_lt_one
  rw [sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget]
  nlinarith

/-- Cofinal signed firewall: assigning the natural negative sign to the interior channel still
fails primitive-budget control eventually. -/
theorem eventually_sourceBudget_lt_sourceHorizontalWoldBVKreinSignedSplitEnergy
    {c : ℂ} (hc : c ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c <
        sourceHorizontalWoldBVKreinSignedSplitEnergy c N := by
  exact (tendsto_sourceHorizontalWoldBVKreinSignedSplitEnergy c).eventually_const_lt
    (sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_lt_signedSplitLimit hc)

/-- Route-O's exact matched Suzuki current, with every natural/prime-power label below the open
`N`th-prime cutoff retained. -/
def ccmActualHeadMatchedSuzukiOpenPrimeClockCurrent
    (N : ℕ) (f : SoninL2) : ℝ :=
  ∑ n ∈ Finset.range (nthPrimeSubtype N : ℕ),
    ccmActualHeadMatchedSuzukiCurrent n f

/-- The prime-clock matched Suzuki current converges to its absolutely summable source total. -/
theorem tendsto_ccmActualHeadMatchedSuzukiOpenPrimeClockCurrent
    (f : SoninL2) :
    Tendsto (fun N : ℕ => ccmActualHeadMatchedSuzukiOpenPrimeClockCurrent N f)
      atTop (nhds (∑' n : ℕ, ccmActualHeadMatchedSuzukiCurrent n f)) := by
  have hsum := (summable_ccmActualHeadMatchedSuzukiCurrent f).hasSum.tendsto_sum_nat
  have hcut : Tendsto (fun N : ℕ => (nthPrimeSubtype N : ℕ)) atTop atTop :=
    nthPrimeSubtype_strictMono.tendsto_atTop
  simpa [ccmActualHeadMatchedSuzukiOpenPrimeClockCurrent,
    Function.comp_def] using hsum.comp hcut

/-- Route-O's exact signed matched current is cubic-scale null after source-horizontal prime-clock
normalization.  This uses its proved absolute summability, not a coefficientwise surrogate. -/
theorem tendsto_ccmActualHeadMatchedSuzukiOpenPrimeClockCurrent_div_logHeightCube_zero
    (f : SoninL2) :
    Tendsto (fun N : ℕ =>
      ccmActualHeadMatchedSuzukiOpenPrimeClockCurrent N f /
        xiMassNthPrimeLogHeight N ^ 3) atTop (nhds 0) := by
  have hnum := tendsto_ccmActualHeadMatchedSuzukiOpenPrimeClockCurrent f
  have hden : Tendsto (fun N : ℕ => xiMassNthPrimeLogHeight N ^ 3)
      atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop _
      tendsto_xiMassNthPrimeLogHeight_atTop
    filter_upwards
      [tendsto_xiMassNthPrimeLogHeight_atTop.eventually_ge_atTop (1 : ℝ)]
      with N hN
    have hnonneg : 0 ≤ xiMassNthPrimeLogHeight N := by linarith
    nlinarith [mul_nonneg
      (mul_nonneg hnonneg (sub_nonneg.mpr hN)) (by linarith :
        0 ≤ xiMassNthPrimeLogHeight N + 1)]
  exact hnum.div_atTop hden

/-- Most general fixed coefficient-faithful Route-O matched-current compensation of the canonical
signed BV split.  Scaling may depend on the selected source data, but not on the cofinal clock. -/
def sourceHorizontalWoldBVKreinRouteOMatchedCompensatedEnergy
    (c : ℂ) (f : SoninL2) (k : ℝ) (N : ℕ) : ℝ :=
  sourceHorizontalWoldBVKreinSignedSplitEnergy c N -
    k * (ccmActualHeadMatchedSuzukiOpenPrimeClockCurrent N f /
      xiMassNthPrimeLogHeight N ^ 3)

/-- Absolute summability makes every fixed Route-O matched-current compensation invisible at the
cubic Wold horizon; the obstructing `8/3` signed limit is unchanged. -/
theorem tendsto_sourceHorizontalWoldBVKreinRouteOMatchedCompensatedEnergy
    (c : ℂ) (f : SoninL2) (k : ℝ) :
    Tendsto (sourceHorizontalWoldBVKreinRouteOMatchedCompensatedEnergy c f k)
      atTop (nhds ((8 / 3 : ℝ) * Complex.normSq c)) := by
  have hzero :=
    (tendsto_ccmActualHeadMatchedSuzukiOpenPrimeClockCurrent_div_logHeightCube_zero f).const_mul k
  change Tendsto (fun N : ℕ =>
    sourceHorizontalWoldBVKreinSignedSplitEnergy c N -
      k * (ccmActualHeadMatchedSuzukiOpenPrimeClockCurrent N f /
        xiMassNthPrimeLogHeight N ^ 3)) atTop
    (nhds ((8 / 3 : ℝ) * Complex.normSq c))
  simpa using (tendsto_sourceHorizontalWoldBVKreinSignedSplitEnergy c).sub hzero

/-- Cross-route firewall: Route O's strongest coefficient-retaining, absolutely summable matched
Suzuki current cannot repair primitive-budget control of the selected BV corner at any fixed
source scaling. -/
theorem eventually_sourceBudget_lt_sourceHorizontalWoldBVKreinRouteOMatchedCompensatedEnergy
    {c : ℂ} (hc : c ≠ 0) (f : SoninL2) (k : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c <
        sourceHorizontalWoldBVKreinRouteOMatchedCompensatedEnergy c f k N := by
  exact
    (tendsto_sourceHorizontalWoldBVKreinRouteOMatchedCompensatedEnergy c f k).eventually_const_lt
      (sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_lt_signedSplitLimit hc)

/-- A universal complete-positive primitive-budget control law is unconditionally false. -/
def SourceHorizontalWoldBVCompletePositivePrimitiveBudgetLaw : Prop :=
  ∀ (c : ℂ), c ≠ 0 → ∀ N : ℕ,
    sourceHorizontalWoldBVInteriorEnergy c N +
        sourceHorizontalWoldBVKreinGhostEnergy c N ≤
      sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c

theorem not_sourceHorizontalWoldBVCompletePositivePrimitiveBudgetLaw :
    ¬ SourceHorizontalWoldBVCompletePositivePrimitiveBudgetLaw := by
  intro hlaw
  have hle := hlaw 1 one_ne_zero 0
  have hlt :=
    sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_lt_completePositiveSplit
      one_ne_zero 0
  linarith

end

end RHTower
