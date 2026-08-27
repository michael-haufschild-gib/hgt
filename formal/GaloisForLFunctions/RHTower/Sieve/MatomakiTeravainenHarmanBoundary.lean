import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanCells
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedSchedule
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowRelaxedDilationPaperScale
import GaloisForLFunctions.RHTower.Sieve.PrimePairDivisorWeightedMean

/-!
# Threshold-boundary fibres in the fourth Harman term

A threshold-crossing aligned cell forces `q₁` into one fixed multiplicative prime window after
`q₂` is fixed.  Six source-width dilations enlarge by at most `63δ_A`, so uniform Mertens bounds
give the required linear paper-width saving.
-/

namespace RHTower.Sieve

open Filter Topology Finset

noncomputable section

/-- On `[0,1]`, six successive `1+δ` dilations fit inside `1+63δ`. -/
theorem one_add_pow_six_le_one_add_sixtyThree_mul
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (1 + δ) ^ 6 ≤ 1 + 63 * δ := by
  have hpow : ∀ n : ℕ, 1 ≤ n → δ ^ n ≤ δ := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    calc
      δ ^ (k + 1) = δ ^ k * δ := by rw [pow_succ]
      _ ≤ 1 * δ := mul_le_mul_of_nonneg_right (pow_le_one₀ hδ0 hδ1) hδ0
      _ = δ := one_mul δ
  have h₂ := hpow 2 (by norm_num)
  have h₃ := hpow 3 (by norm_num)
  have h₄ := hpow 4 (by norm_num)
  have h₅ := hpow 5 (by norm_num)
  have h₆ := hpow 6 (by norm_num)
  ring_nf at ⊢
  nlinarith

/-- For fixed `q₂`, exact prime fibre containing every pair in a threshold-crossing cell. -/
def mtHarmanThresholdBoundaryFibre
    (S : Finset ℕ) (δ E : ℝ) (q₂ : ℕ) : Finset ℕ :=
  S.filter fun q₁ =>
    E < (1 + δ) ^ 5 * ((q₁ : ℝ) * (q₂ : ℝ) ^ 4) ∧
      (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E

theorem mem_mtHarmanThresholdBoundaryFibre
    {S : Finset ℕ} {δ E : ℝ} {q₁ q₂ : ℕ} :
    q₁ ∈ mtHarmanThresholdBoundaryFibre S δ E q₂ ↔
      q₁ ∈ S ∧
        E < (1 + δ) ^ 5 * ((q₁ : ℝ) * (q₂ : ℝ) ^ 4) ∧
          (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E := by
  simp [mtHarmanThresholdBoundaryFibre]

/-- Every actual pair in a threshold-crossing aligned cell belongs to the boundary fibre. -/
theorem adjacentBlock_thresholdBoundary_mem_harmanFibre
    {t : ℕ} {endpoint : ℕ → ℕ} (hendpoint : ∀ i, 1 ≤ endpoint i)
    {S : Finset ℕ} {i₁ i₂ : Fin t} {q₁ q₂ : ℕ} {δ E : ℝ}
    (hδ : 0 ≤ δ)
    (hband : ∀ i : Fin t,
      mtAdjacentBlockUpperScale endpoint i ≤
        (1 + δ) * mtAdjacentBlockLowerScale endpoint i)
    (hq₁S : q₁ ∈ S)
    (hq₁ : q₁ ∈ mtAdjacentPrimeBlock endpoint i₁)
    (hq₂ : q₂ ∈ mtAdjacentPrimeBlock endpoint i₂)
    (hgeometry : (q₁ : ℝ) * (q₂ : ℝ) ^ 4 < E)
    (hboundary : E ≤ mtAdjacentBlockUpperScale endpoint i₁ *
      mtAdjacentBlockUpperScale endpoint i₂ ^ 4) :
    q₁ ∈ mtHarmanThresholdBoundaryFibre S δ E q₂ := by
  rw [mem_mtHarmanThresholdBoundaryFibre]
  exact ⟨hq₁S, adjacentBlock_thresholdBoundary_implies_harmanWindow
    hendpoint hδ hband hq₁ hq₂ hgeometry hboundary⟩

/-- The threshold-boundary fibre has reciprocal mass at most `64δ_A`, uniformly in its second
prime and threshold. -/
theorem eventually_sum_inv_mtHarmanThresholdBoundaryFibre_le
    (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (S : Finset ℕ) (q₂ : ℕ) (E : ℝ),
      (∀ q ∈ S, q.Prime) →
      (∀ q ∈ S, mtLowerCutoffNat X ≤ q) →
      q₂.Prime →
      ∑ q₁ ∈ mtHarmanThresholdBoundaryFibre S (mtPaperWidth A X) E q₂,
          1 / (q₁ : ℝ) ≤ 64 * mtPaperWidth A X := by
  filter_upwards [
    eventually_sum_inv_primesIco_relaxedPaperCutoff_fixedDilation A 63 (by norm_num),
    eventually_one_le_mtPaperWidth_mul_mtLowerCutoffNat_sub_one A,
    Filter.eventually_ge_atTop (Real.exp 1)] with X hwindowX hprogressX hX
  intro S q₂ E hprime hlowerNat hq₂Prime
  let δ : ℝ := mtPaperWidth A X
  let T : Finset ℕ := mtHarmanThresholdBoundaryFibre S δ E q₂
  change ∑ q₁ ∈ T, 1 / (q₁ : ℝ) ≤ 64 * δ
  have hlogX : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hδ0 : 0 ≤ δ := by
    dsimp [δ, mtPaperWidth]
    exact Real.rpow_nonneg (zero_le_one.trans hlogX) _
  have hδ1 : δ ≤ 1 := by
    dsimp [δ, mtPaperWidth]
    rw [Real.rpow_neg (zero_le_one.trans hlogX)]
    exact inv_le_one_of_one_le₀
      (Real.one_le_rpow hlogX (by positivity : (0 : ℝ) ≤ ((10 * A : ℕ) : ℝ)))
  by_cases hT : T.Nonempty
  · let a : ℕ := T.min' hT
    let b : ℕ := T.max' hT + 1
    have haMem : a ∈ T := Finset.min'_mem T hT
    have hbPredMem : b - 1 ∈ T := by
      simpa [b] using Finset.max'_mem T hT
    have haSource : a ∈ S := (mem_mtHarmanThresholdBoundaryFibre.mp haMem).1
    have hbSource : b - 1 ∈ S :=
      (mem_mtHarmanThresholdBoundaryFibre.mp hbPredMem).1
    have hza : mtLowerCutoffNat X ≤ a := hlowerNat a haSource
    have hδProgressA : 1 ≤ δ * ((a - 1 : ℕ) : ℝ) := by
      have hsub : mtLowerCutoffNat X - 1 ≤ a - 1 := Nat.sub_le_sub_right hza 1
      have hsubR : ((mtLowerCutoffNat X - 1 : ℕ) : ℝ) ≤ ((a - 1 : ℕ) : ℝ) := by
        exact_mod_cast hsub
      have hbaseProgress : 1 ≤ δ * ((mtLowerCutoffNat X - 1 : ℕ) : ℝ) := by
        simpa only [δ] using hprogressX
      exact hbaseProgress.trans (mul_le_mul_of_nonneg_left hsubR hδ0)
    have hzSubPos : 0 < mtLowerCutoffNat X - 1 := by
      by_contra hnot
      have hzero : mtLowerCutoffNat X - 1 = 0 := Nat.eq_zero_of_not_pos hnot
      have hfalse : (1 : ℝ) ≤ 0 := by simpa [hzero] using hprogressX
      norm_num at hfalse
    have hzOne : 1 ≤ mtLowerCutoffNat X := by omega
    have hcutCeil : mtLowerCutoff X ≤ (mtLowerCutoffNat X : ℝ) := Nat.le_ceil _
    have hzCast : (mtLowerCutoffNat X : ℝ) =
        ((mtLowerCutoffNat X - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hzOne]
      push_cast
      ring
    have hden : 0 < 1 + δ := by linarith
    have hcutBase : mtLowerCutoff X / (1 + δ) ≤
        ((mtLowerCutoffNat X - 1 : ℕ) : ℝ) := by
      apply (div_le_iff₀ hden).2
      calc
        mtLowerCutoff X ≤ (mtLowerCutoffNat X : ℝ) := hcutCeil
        _ = ((mtLowerCutoffNat X - 1 : ℕ) : ℝ) + 1 := hzCast
        _ ≤ ((mtLowerCutoffNat X - 1 : ℕ) : ℝ) +
            δ * ((mtLowerCutoffNat X - 1 : ℕ) : ℝ) := by
          simpa only [δ, add_le_add_iff_left] using hprogressX
        _ = ((mtLowerCutoffNat X - 1 : ℕ) : ℝ) * (1 + δ) := by ring
    have hcutA : mtLowerCutoff X / (1 + δ) ≤ ((a - 1 : ℕ) : ℝ) := by
      exact hcutBase.trans (by
        exact_mod_cast Nat.sub_le_sub_right hza 1)
    have hab : a ≤ b := by
      dsimp [a, b]
      exact (Finset.min'_le T (T.max' hT) (Finset.max'_mem T hT)).trans
        (Nat.le_add_right _ _)
    have hq₂PowPos : 0 < (q₂ : ℝ) ^ 4 := pow_pos (by exact_mod_cast hq₂Prime.pos) 4
    have hmaxGeometry := (mem_mtHarmanThresholdBoundaryFibre.mp hbPredMem).2.2
    have hminGeometry := (mem_mtHarmanThresholdBoundaryFibre.mp haMem).2.1
    have hmaxMinMul :
        ((b - 1 : ℕ) : ℝ) * (q₂ : ℝ) ^ 4 <
          ((1 + δ) ^ 5 * (a : ℝ)) * (q₂ : ℝ) ^ 4 := by
      calc
        ((b - 1 : ℕ) : ℝ) * (q₂ : ℝ) ^ 4 < E := hmaxGeometry
        _ < (1 + δ) ^ 5 * ((a : ℝ) * (q₂ : ℝ) ^ 4) := hminGeometry
        _ = ((1 + δ) ^ 5 * (a : ℝ)) * (q₂ : ℝ) ^ 4 := by ring
    have hmaxMin : ((b - 1 : ℕ) : ℝ) < (1 + δ) ^ 5 * (a : ℝ) :=
      lt_of_mul_lt_mul_right hmaxMinMul hq₂PowPos.le
    have haCast : (a : ℝ) = ((a - 1 : ℕ) : ℝ) + 1 := by
      have haOne : 1 ≤ a := hzOne.trans hza
      rw [Nat.cast_sub haOne]
      push_cast
      ring
    have haDilated : (a : ℝ) ≤ (1 + δ) * ((a - 1 : ℕ) : ℝ) := by
      rw [haCast]
      nlinarith
    have hsixBand : ((b - 1 : ℕ) : ℝ) ≤
        (1 + δ) ^ 6 * ((a - 1 : ℕ) : ℝ) := by
      calc
        ((b - 1 : ℕ) : ℝ) ≤ (1 + δ) ^ 5 * (a : ℝ) := hmaxMin.le
        _ ≤ (1 + δ) ^ 5 * ((1 + δ) * ((a - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left haDilated (by positivity)
        _ = (1 + δ) ^ 6 * ((a - 1 : ℕ) : ℝ) := by ring
    have hfixedBand : ((b - 1 : ℕ) : ℝ) ≤
        (1 + 63 * δ) * ((a - 1 : ℕ) : ℝ) := by
      exact hsixBand.trans (mul_le_mul_of_nonneg_right
        (one_add_pow_six_le_one_add_sixtyThree_mul hδ0 hδ1)
        (Nat.cast_nonneg _))
    have hsubset : T ⊆ primesIco a b := by
      intro q hq
      have hqPrime := hprime q (mem_mtHarmanThresholdBoundaryFibre.mp hq).1
      exact mem_primesIco.mpr ⟨Finset.min'_le T q hq,
        (Finset.le_max' T q hq).trans_lt (Nat.lt_add_one _), hqPrime⟩
    calc
      ∑ q₁ ∈ T, 1 / (q₁ : ℝ) ≤ ∑ q₁ ∈ primesIco a b, 1 / (q₁ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro q hq hqT
          exact one_div_nonneg.mpr (by
            exact_mod_cast (mem_primesIco.mp hq).2.2.pos.le))
      _ ≤ 64 * δ := by
        simpa only [δ, show (63 : ℝ) + 1 = 64 by norm_num] using
          hwindowX hcutA hab (by simpa only [δ] using hfixedBand)
  · have hEmpty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp [hEmpty, hδ0]

/-- Divisor-weighted count of Harman threshold-boundary prime pairs dividing `n`. -/
def weightedMTHarmanThresholdBoundaryCount
    (K : ℕ) (S₁ S₂ : Finset ℕ) (δ E : ℝ) (n : ℕ) : ℝ :=
  weightedPrimePairDivisorCount K S₂
    (fun q₂ => mtHarmanThresholdBoundaryFibre S₁ δ E q₂) n

/-- Uniform divisor-weighted mean for all threshold-crossing cells.  The outer `q₂` reciprocal
mass remains exposed for the later source-range estimate. -/
theorem eventually_sum_weightedMTHarmanThresholdBoundaryCount_le
    (A K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (S₁ S₂ : Finset ℕ) (E : ℝ) (Y : ℕ),
      1 ≤ Y →
      (∀ q ∈ S₁, q.Prime) →
      (∀ q ∈ S₁, mtLowerCutoffNat X ≤ q) →
      (∀ q ∈ S₂, q.Prime) →
      ∑ n ∈ Finset.Icc 1 Y,
          weightedMTHarmanThresholdBoundaryCount
            K S₁ S₂ (mtPaperWidth A X) E n ≤
        (4 : ℝ) ^ K * (Y : ℝ) *
          (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
            (64 * mtPaperWidth A X) * ∑ q₂ ∈ S₂, 1 / (q₂ : ℝ) := by
  filter_upwards [eventually_sum_inv_mtHarmanThresholdBoundaryFibre_le A]
    with X hmassX
  intro S₁ S₂ E Y hY hprime₁ hlower₁ hprime₂
  have hprimeFibre : ∀ q₂ ∈ S₂,
      ∀ q₁ ∈ mtHarmanThresholdBoundaryFibre S₁ (mtPaperWidth A X) E q₂,
        q₁.Prime := by
    intro q₂ hq₂ q₁ hq₁
    exact hprime₁ q₁ (mem_mtHarmanThresholdBoundaryFibre.mp hq₁).1
  exact sum_weightedPrimePairDivisorCount_le_of_fibreMass
    K Y hY S₂
      (fun q₂ => mtHarmanThresholdBoundaryFibre S₁ (mtPaperWidth A X) E q₂)
      hprime₂ hprimeFibre
      (fun q₂ hq₂ => hmassX S₁ q₂ E hprime₁ hlower₁ (hprime₂ q₂ hq₂))

end

end RHTower.Sieve
