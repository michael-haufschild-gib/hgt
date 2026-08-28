import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureSourcePlemeljTrace
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureThreeCenterSharpQuantum
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.Sieve.GhsSizeBounds

/-!
# Canonical height windows for the HCF Plemelj covariance

This module removes the abstract `card K = o(N)` premise from the source-only HCF covariance
reduction.  At natural height `n`, the integer feature window `[-n-1,n+1]` has `2n+3` sites,
whereas the unconditional Riemann--von Mangoldt theorem gives `N(n) ~ n log n / (2π)`.
Consequently the von Mangoldt lattice channel is genuinely `o(N(n))` on this canonical window.

The final equivalence states the remaining three-quarter target without hidden lower-order terms:
the corrected-budget ceiling and source-only Plemelj-covariance ceiling at `1452/4225` are the same
asymptotic assertion.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Integer critical-feature centers covering the natural height window with one-site padding. -/
def criticalFeatureCanonicalLatticeWindow (n : ℕ) : Finset ℤ :=
  Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1)

/-- Riemann zero count at the same natural height, cast to the budget scalar field. -/
def criticalFeatureCanonicalZeroCount (n : ℕ) : ℝ :=
  (xiZeroCount (n : ℝ) : ℝ)

theorem card_criticalFeatureCanonicalLatticeWindow (n : ℕ) :
    (criticalFeatureCanonicalLatticeWindow n).card = 2 * n + 3 := by
  simp [criticalFeatureCanonicalLatticeWindow]
  omega

/-- The canonical zero-count normalizer is eventually strictly positive. -/
theorem eventually_criticalFeatureCanonicalZeroCount_pos :
    ∀ᶠ n : ℕ in atTop, 0 < criticalFeatureCanonicalZeroCount n := by
  obtain ⟨T₀, hT₀, hclose⟩ :=
    exists_xiZeroCount_close (1 / (4 * Real.pi)) (by positivity)
  filter_upwards [eventually_ge_atTop ⌈T₀⌉₊] with n hn
  have hT : T₀ ≤ (n : ℝ) :=
    (Nat.le_ceil T₀).trans (by exact_mod_cast hn)
  have hn4 : (4 : ℝ) ≤ n := hT₀.trans hT
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have h := hclose (n : ℝ) hT
  rw [abs_le] at h
  dsimp [criticalFeatureCanonicalZeroCount]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcoeff : (1 / (2 * Real.pi) : ℝ) = 2 * (1 / (4 * Real.pi)) := by
    field_simp
    ring
  rw [hcoeff] at h
  have hmainPos : 0 < (1 / (4 * Real.pi)) * ((n : ℝ) * Real.log n) := by
    positivity
  nlinarith

/-- The padded feature lattice is sublinear relative to the actual Riemann zero count. -/
theorem tendsto_card_criticalFeatureCanonicalLatticeWindow_div_zeroCount :
    Tendsto
      (fun n : ℕ =>
        ((criticalFeatureCanonicalLatticeWindow n).card : ℝ) /
          criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  obtain ⟨T₀, hT₀, hclose⟩ :=
    exists_xiZeroCount_close (1 / (4 * Real.pi)) (by positivity)
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    RHTower.Sieve.tendsto_log_natCast_atTop
  have hmajor : Tendsto
      (fun n : ℕ => (20 * Real.pi) / Real.log (n : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hlog
  refine squeeze_zero'
    (eventually_criticalFeatureCanonicalZeroCount_pos.mono fun n hn => by positivity)
    ?_ hmajor
  filter_upwards [eventually_ge_atTop ⌈T₀⌉₊, eventually_ge_atTop 4,
    eventually_criticalFeatureCanonicalZeroCount_pos] with n hnT hn4 hcount
  have hT : T₀ ≤ (n : ℝ) :=
    (Nat.le_ceil T₀).trans (by exact_mod_cast hnT)
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hcloseN := hclose (n : ℝ) hT
  rw [abs_le] at hcloseN
  have hlower :
      (1 / (4 * Real.pi)) * ((n : ℝ) * Real.log n) ≤
        criticalFeatureCanonicalZeroCount n := by
    dsimp [criticalFeatureCanonicalZeroCount]
    have hcoeff : (1 / (2 * Real.pi) : ℝ) = 2 * (1 / (4 * Real.pi)) := by
      field_simp
      ring
    rw [hcoeff] at hcloseN
    nlinarith
  rw [card_criticalFeatureCanonicalLatticeWindow]
  push_cast
  rw [div_le_iff₀ hcount]
  have hscaled : 5 * ((n : ℝ) * Real.log n) ≤
      20 * Real.pi * criticalFeatureCanonicalZeroCount n := by
    have hmul := mul_le_mul_of_nonneg_left hlower (by positivity : 0 ≤ 20 * Real.pi)
    field_simp at hmul
    nlinarith
  have hcardLog : (2 * (n : ℝ) + 3) * Real.log n ≤
      20 * Real.pi * criticalFeatureCanonicalZeroCount n := by
    have hcard : 2 * (n : ℝ) + 3 ≤ 5 * n := by nlinarith
    have := mul_le_mul_of_nonneg_right hcard hlogpos.le
    nlinarith
  rw [show (20 * Real.pi / Real.log n) * criticalFeatureCanonicalZeroCount n =
      (20 * Real.pi * criticalFeatureCanonicalZeroCount n) / Real.log n by ring]
  exact (le_div_iff₀ hlogpos).2 hcardLog

/-- On the canonical height window, corrected HCF budget and source-only covariance differ by
`o(N(n))` unconditionally. -/
theorem tendsto_canonical_correctedBudget_sub_plemeljCovariance_div :
    Tendsto
      (fun n : ℕ =>
        (criticalFeaturePrimeGammaOffLineLatticeBudget
              (criticalFeatureCanonicalLatticeWindow n) -
            criticalFeaturePoleGammaPlemeljCovariance
              (criticalFeatureCanonicalLatticeWindow n)) /
          criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) :=
  tendsto_correctedBudget_sub_plemeljCovariance_div
    criticalFeatureCanonicalLatticeWindow criticalFeatureCanonicalZeroCount
    eventually_criticalFeatureCanonicalZeroCount_pos
    tendsto_card_criticalFeatureCanonicalLatticeWindow_div_zeroCount

/-- `B(n) ≤ c N(n) + o(N(n))`, encoded without choosing a remainder sequence. -/
def CriticalFeatureCanonicalAsymptoticUpper (B : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    B n ≤ (c + ε) * criticalFeatureCanonicalZeroCount n

private theorem canonicalAsymptoticUpper_iff_of_sub_div_tendsto_zero
    {B C : ℕ → ℝ} {c : ℝ}
    (hdiff : Tendsto
      (fun n => (B n - C n) / criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0)) :
    CriticalFeatureCanonicalAsymptoticUpper B c ↔
      CriticalFeatureCanonicalAsymptoticUpper C c := by
  have htransfer (X Y : ℕ → ℝ)
      (hXY : Tendsto
        (fun n => (X n - Y n) / criticalFeatureCanonicalZeroCount n)
        atTop (𝓝 0))
      (hY : CriticalFeatureCanonicalAsymptoticUpper Y c) :
      CriticalFeatureCanonicalAsymptoticUpper X c := by
    intro ε hε
    have hY' := hY (ε / 2) (by linarith)
    have herr : ∀ᶠ n : ℕ in atTop,
        (X n - Y n) / criticalFeatureCanonicalZeroCount n < ε / 2 :=
      (tendsto_order.1 hXY).2 _ (by linarith)
    filter_upwards [hY', herr, eventually_criticalFeatureCanonicalZeroCount_pos]
      with n hYn heren hN
    have hdiffn : X n - Y n <
        (ε / 2) * criticalFeatureCanonicalZeroCount n :=
      (div_lt_iff₀ hN).mp heren
    nlinarith
  constructor
  · intro hB
    apply htransfer C B
    · have hneg := hdiff.neg
      simp only [neg_zero] at hneg
      convert hneg using 1
      funext n
      ring
    · exact hB
  · exact htransfer B C hdiff

/-- **Exact canonical source gate.**  At the sharp three-center constant, proving the requested
source-only pole--Gamma Plemelj ceiling is equivalent to proving the corrected HCF budget ceiling;
the von Mangoldt and lattice-cardinality channels introduce no hidden loss. -/
theorem canonical_correctedBudget_ceiling_iff_plemeljCovariance_ceiling :
    CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
          (criticalFeatureCanonicalLatticeWindow n))
        (1452 / 4225) ↔
      CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePoleGammaPlemeljCovariance
          (criticalFeatureCanonicalLatticeWindow n))
        (1452 / 4225) :=
  canonicalAsymptoticUpper_iff_of_sub_div_tendsto_zero
    tendsto_canonical_correctedBudget_sub_plemeljCovariance_div

end

end RHTower
