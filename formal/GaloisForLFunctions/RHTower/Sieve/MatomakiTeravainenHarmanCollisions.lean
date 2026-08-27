import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanRectangles
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowRelaxedPaperScale
import GaloisForLFunctions.RHTower.Sieve.PrimePairDivisorWeightedMean

/-!
# Same-cell collisions in Harman rectangles

The source order predicates fail to rectangularize only when two consecutive primes occupy one
aligned cell.  This file counts exactly those strict-order pairs and proves their divisor-weighted
paper-scale mean without introducing a block-selection function.
-/

namespace RHTower.Sieve

open Filter Topology Finset

noncomputable section

/-- Larger primes in the same adjacent cell as the fixed outer prime. -/
def mtHarmanSameCellFibre {t : ℕ} (endpoint : ℕ → ℕ) (i : Fin t) (q₂ : ℕ) :
    Finset ℕ :=
  (mtAdjacentPrimeBlock endpoint i).filter fun q₁ => q₂ < q₁

theorem mem_mtHarmanSameCellFibre
    {t : ℕ} {endpoint : ℕ → ℕ} {i : Fin t} {q₁ q₂ : ℕ} :
    q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ ↔
      q₁ ∈ mtAdjacentPrimeBlock endpoint i ∧ q₂ < q₁ := by
  simp [mtHarmanSameCellFibre]

/-- Exact divisor-weighted count of strict-order prime pairs occupying one aligned cell. -/
def weightedMTHarmanSameCellCollisionCount
    (K : ℕ) {t : ℕ} (endpoint : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ i : Fin t, weightedPrimePairDivisorCount K
    (mtAdjacentPrimeBlock endpoint i) (mtHarmanSameCellFibre endpoint i) n

/-- Every same-cell ordered pair is counted by the exact collision fibre. -/
theorem sameCell_pair_mem_collisionFibre
    {t : ℕ} {endpoint : ℕ → ℕ} {i : Fin t} {q₁ q₂ : ℕ}
    (hq₁ : q₁ ∈ mtAdjacentPrimeBlock endpoint i) (horder : q₂ < q₁) :
    q₁ ∈ mtHarmanSameCellFibre endpoint i q₂ := by
  exact mem_mtHarmanSameCellFibre.mpr ⟨hq₁, horder⟩

/-- Adjacent-block reciprocal masses telescope exactly to the complete prime interval. -/
theorem sum_mtAdjacentPrimeBlock_eq_sum_primesIco
    {t : ℕ} (endpoint : ℕ → ℕ) (hmono : Monotone endpoint) (f : ℕ → ℝ) :
    ∑ i : Fin t, ∑ q ∈ mtAdjacentPrimeBlock endpoint i, f q =
      ∑ q ∈ primesIco (endpoint 0) (endpoint t), f q := by
  have hpair : (↑(Finset.univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint
      (mtAdjacentPrimeBlock endpoint) := by
    intro i hi k hk hik
    exact mtAdjacentPrimeBlock_disjoint endpoint hmono i k hik
  have hunion : (Finset.univ : Finset (Fin t)).biUnion
      (mtAdjacentPrimeBlock endpoint) = primesIco (endpoint 0) (endpoint t) := by
    calc
      (Finset.univ : Finset (Fin t)).biUnion (mtAdjacentPrimeBlock endpoint) =
          (mtBlockPrefix (Fin.last t)).biUnion (mtAdjacentPrimeBlock endpoint) := by
        congr 1
        ext i
        simp [mem_mtBlockPrefix]
      _ = primesIco (endpoint 0) (endpoint t) := by
        simpa using mtAdjacentPrimeBlock_prefix_biUnion endpoint hmono (Fin.last t)
  rw [← hunion]
  exact (Finset.sum_biUnion hpair).symm

/-- Uniform weighted mean for all strict-order same-cell collisions.  Total outer reciprocal mass
of the aligned blocks remains exposed. -/
theorem eventually_sum_weightedMTHarmanSameCellCollisionCount_le
    (A K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (t : ℕ) (endpoint : ℕ → ℕ) (Y : ℕ),
      1 ≤ Y →
      Monotone endpoint →
      (∀ i : Fin t,
        mtLowerCutoff X / (1 + mtPaperWidth A X) ≤
          mtAdjacentBlockLowerScale endpoint i) →
      (∀ i : Fin t,
        mtAdjacentBlockUpperScale endpoint i ≤
          (1 + mtPaperWidth A X) * mtAdjacentBlockLowerScale endpoint i) →
      ∑ n ∈ Finset.Icc 1 Y,
          weightedMTHarmanSameCellCollisionCount K (t := t) endpoint n ≤
        (4 : ℝ) ^ K * (Y : ℝ) *
          (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
            (2 * mtPaperWidth A X) *
              ∑ i : Fin t, ∑ q₂ ∈ mtAdjacentPrimeBlock endpoint i, 1 / (q₂ : ℝ) := by
  filter_upwards [eventually_sum_inv_primesIco_relaxedPaperCutoff A] with X hwindowX
  intro t endpoint Y hY hmono hlower hband
  let C : ℝ := (4 : ℝ) ^ K * (Y : ℝ) *
    (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1)
  have hblockMass : ∀ i : Fin t,
      ∑ q ∈ mtAdjacentPrimeBlock endpoint i, 1 / (q : ℝ) ≤
        2 * mtPaperWidth A X := by
    intro i
    exact hwindowX (by simpa [mtAdjacentBlockLowerScale] using hlower i)
      (hmono (Nat.le_succ i.1))
      (by simpa [mtAdjacentBlockUpperScale, mtAdjacentBlockLowerScale] using hband i)
  have hfibreMass : ∀ i : Fin t, ∀ q₂ ∈ mtAdjacentPrimeBlock endpoint i,
      ∑ q₁ ∈ mtHarmanSameCellFibre endpoint i q₂, 1 / (q₁ : ℝ) ≤
        2 * mtPaperWidth A X := by
    intro i q₂ hq₂
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (by
        intro q hq hnot
        exact one_div_nonneg.mpr (by
          exact_mod_cast (mem_primesIco.mp hq).2.2.pos.le))).trans (hblockMass i)
  have hcellMean : ∀ i : Fin t,
      ∑ n ∈ Finset.Icc 1 Y,
          weightedPrimePairDivisorCount K (mtAdjacentPrimeBlock endpoint i)
            (mtHarmanSameCellFibre endpoint i) n ≤
        C * (2 * mtPaperWidth A X) *
          ∑ q₂ ∈ mtAdjacentPrimeBlock endpoint i, 1 / (q₂ : ℝ) := by
    intro i
    have hprimeOuter : ∀ q ∈ mtAdjacentPrimeBlock endpoint i, q.Prime := by
      intro q hq
      exact (mem_primesIco.mp hq).2.2
    have hprimeFibre : ∀ q₂ ∈ mtAdjacentPrimeBlock endpoint i,
        ∀ q₁ ∈ mtHarmanSameCellFibre endpoint i q₂, q₁.Prime := by
      intro q₂ hq₂ q₁ hq₁
      exact (mem_primesIco.mp (mem_mtHarmanSameCellFibre.mp hq₁).1).2.2
    simpa only [C] using sum_weightedPrimePairDivisorCount_le_of_fibreMass
      K Y hY (mtAdjacentPrimeBlock endpoint i) (mtHarmanSameCellFibre endpoint i)
        hprimeOuter hprimeFibre (hfibreMass i)
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        weightedMTHarmanSameCellCollisionCount K (t := t) endpoint n =
      ∑ i : Fin t, ∑ n ∈ Finset.Icc 1 Y,
        weightedPrimePairDivisorCount K (mtAdjacentPrimeBlock endpoint i)
          (mtHarmanSameCellFibre endpoint i) n := by
      unfold weightedMTHarmanSameCellCollisionCount
      rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin t, C * (2 * mtPaperWidth A X) *
        ∑ q₂ ∈ mtAdjacentPrimeBlock endpoint i, 1 / (q₂ : ℝ) :=
      Finset.sum_le_sum fun i _ => hcellMean i
    _ = (4 : ℝ) ^ K * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
          (2 * mtPaperWidth A X) *
            ∑ i : Fin t, ∑ q₂ ∈ mtAdjacentPrimeBlock endpoint i, 1 / (q₂ : ℝ) := by
      dsimp [C]
      rw [Finset.mul_sum]

/-- Paper-aligned specialization of the complete same-cell collision estimate. -/
theorem eventually_sum_weightedMTHarmanSameCellCollisionCount_paperAligned_le
    (A K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (z₁ Y : ℕ),
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X → 1 ≤ Y →
      ∑ n ∈ Finset.Icc 1 Y,
          weightedMTHarmanSameCellCollisionCount K
            (t := z₁ - mtLowerCutoffNat X)
            (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)) n ≤
        (4 : ℝ) ^ K * (Y : ℝ) *
          (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
            (2 * mtPaperWidth A X) *
              ∑ i : Fin (z₁ - mtLowerCutoffNat X),
                ∑ q₂ ∈ mtAdjacentPrimeBlock
                  (mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)) i,
                    1 / (q₂ : ℝ) := by
  filter_upwards [eventually_sum_weightedMTHarmanSameCellCollisionCount_le A K,
    eventually_one_le_mtPaperWidth_mul_mtLowerCutoffNat_sub_one A,
    Filter.eventually_ge_atTop (Real.exp 1)] with X hmeanX hprogressX hX
  intro z₁ Y hz hzX hY
  let z₀ := mtLowerCutoffNat X
  let δ := mtPaperWidth A X
  have hlogX : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hδ0 : 0 ≤ δ := by
    dsimp [δ, mtPaperWidth]
    exact Real.rpow_nonneg (zero_le_one.trans hlogX) _
  have hzSubPos : 0 < z₀ - 1 := by
    by_contra hnot
    have hzero : z₀ - 1 = 0 := Nat.eq_zero_of_not_pos hnot
    have hfalse : (1 : ℝ) ≤ 0 := by
      simpa only [z₀, δ, hzero, Nat.cast_zero, mul_zero] using hprogressX
    norm_num at hfalse
  have hzOne : 1 ≤ z₀ := by omega
  have hmonoEndpoint : Monotone (mtPaperAlignedEndpoint z₀ z₁ δ) :=
    mtPaperAlignedEndpoint_monotone hzOne (by simpa only [z₀] using hz) hδ0
      (by simpa only [z₀, δ] using hprogressX)
  have hcutCeil : mtLowerCutoff X ≤ (z₀ : ℝ) := by
    dsimp [z₀, mtLowerCutoffNat]
    exact Nat.le_ceil _
  have hzCast : (z₀ : ℝ) = ((z₀ - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hzOne]
    push_cast
    ring
  have hden : 0 < 1 + δ := by linarith
  have hcutBase : mtLowerCutoff X / (1 + δ) ≤ ((z₀ - 1 : ℕ) : ℝ) := by
    apply (div_le_iff₀ hden).2
    calc
      mtLowerCutoff X ≤ (z₀ : ℝ) := hcutCeil
      _ = ((z₀ - 1 : ℕ) : ℝ) + 1 := hzCast
      _ ≤ ((z₀ - 1 : ℕ) : ℝ) + δ * ((z₀ - 1 : ℕ) : ℝ) := by
        simpa only [z₀, δ, add_le_add_iff_left] using hprogressX
      _ = ((z₀ - 1 : ℕ) : ℝ) * (1 + δ) := by ring
  have hlower : ∀ i : Fin (z₁ - z₀),
      mtLowerCutoff X / (1 + δ) ≤
        mtAdjacentBlockLowerScale (mtPaperAlignedEndpoint z₀ z₁ δ) i := by
    intro i
    have hendpointLower :=
      (mtPaperAlignedEndpoint_mem_Icc hzOne (by simpa only [z₀] using hz) hδ0
        (by simpa only [z₀, δ] using hprogressX) i.1).1
    exact hcutBase.trans (by
      dsimp [mtAdjacentBlockLowerScale]
      exact_mod_cast Nat.sub_le_sub_right hendpointLower 1)
  have hband : ∀ i : Fin (z₁ - z₀),
      mtAdjacentBlockUpperScale (mtPaperAlignedEndpoint z₀ z₁ δ) i ≤
        (1 + δ) * mtAdjacentBlockLowerScale (mtPaperAlignedEndpoint z₀ z₁ δ) i := by
    intro i
    exact mtPaperAlignedEndpoint_band hδ0 i.1
  simpa only [z₀, δ] using hmeanX (z₁ - z₀)
    (mtPaperAlignedEndpoint z₀ z₁ δ) Y hY hmonoEndpoint hlower hband

end

end RHTower.Sieve
