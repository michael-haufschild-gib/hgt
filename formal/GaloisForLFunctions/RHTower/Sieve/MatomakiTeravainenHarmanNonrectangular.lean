import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanBoundary
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanCollisions

/-!
# Complete nonrectangular support of the fourth Harman term

This combines the two exact obstructions to rectangularization: strict-order pairs in one aligned
cell and pair-product threshold crossings.  Their divisor-weighted mean costs `66δ_A` times the
outer reciprocal prime mass.
-/

namespace RHTower.Sieve

open Filter Topology Finset

noncomputable section

/-- Complete divisor-weighted nonrectangular majorant for one paper-aligned Harman schedule. -/
def weightedMTHarmanNonrectangularCount
    (K : ℕ) {t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (δ E : ℝ) (n : ℕ) : ℝ :=
  weightedMTHarmanSameCellCollisionCount K (t := t) endpoint n +
    weightedMTHarmanThresholdBoundaryCount K P P δ E n

/-- Same-cell collisions and threshold-crossing pairs together have the exact source-scale
`66δ_A` weighted mean. -/
theorem eventually_sum_weightedMTHarmanNonrectangularCount_paperAligned_le
    (A K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (z₁ Y : ℕ) (E : ℝ),
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X → 1 ≤ Y →
      let endpoint :=
        mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)
      let P := primesIco (mtLowerCutoffNat X) z₁
      ∑ n ∈ Finset.Icc 1 Y,
          weightedMTHarmanNonrectangularCount K
            (t := z₁ - mtLowerCutoffNat X) endpoint P
            (mtPaperWidth A X) E n ≤
        (4 : ℝ) ^ K * (Y : ℝ) *
          (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
            (66 * mtPaperWidth A X) * ∑ q ∈ P, 1 / (q : ℝ) := by
  filter_upwards [
    eventually_sum_weightedMTHarmanSameCellCollisionCount_paperAligned_le A K,
    eventually_sum_weightedMTHarmanThresholdBoundaryCount_le A K,
    eventually_one_le_mtPaperWidth_mul_mtLowerCutoffNat_sub_one A,
    Filter.eventually_ge_atTop (Real.exp 1)] with
      X hcollisionX hboundaryX hprogressX hX
  intro z₁ Y E hz hzX hY
  dsimp only
  let z₀ := mtLowerCutoffNat X
  let δ := mtPaperWidth A X
  let endpoint := mtPaperAlignedEndpoint z₀ z₁ δ
  let P := primesIco z₀ z₁
  let C : ℝ := (4 : ℝ) ^ K * (Y : ℝ) *
    (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1)
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
  have hmonoEndpoint : Monotone endpoint := by
    dsimp [endpoint]
    exact mtPaperAlignedEndpoint_monotone hzOne (by simpa only [z₀] using hz) hδ0
      (by simpa only [z₀, δ] using hprogressX)
  have hterminal : endpoint (z₁ - z₀) = z₁ := by
    dsimp [endpoint]
    exact mtPaperAlignedEndpoint_sub_eq hzOne (by simpa only [z₀] using hz) hδ0
      (by simpa only [z₀, δ] using hprogressX)
  have hmassEq :
      (∑ i : Fin (z₁ - z₀), ∑ q ∈ mtAdjacentPrimeBlock endpoint i, 1 / (q : ℝ)) =
        ∑ q ∈ P, 1 / (q : ℝ) := by
    have hsum := sum_mtAdjacentPrimeBlock_eq_sum_primesIco
      (t := z₁ - z₀) endpoint hmonoEndpoint (fun q => 1 / (q : ℝ))
    simpa only [P, endpoint, mtPaperAlignedEndpoint_zero, hterminal] using hsum
  have hprime : ∀ q ∈ P, q.Prime := by
    intro q hq
    exact (mem_primesIco.mp hq).2.2
  have hlower : ∀ q ∈ P, z₀ ≤ q := by
    intro q hq
    exact (mem_primesIco.mp hq).1
  have hcollision :
      ∑ n ∈ Finset.Icc 1 Y,
          weightedMTHarmanSameCellCollisionCount K
            (t := z₁ - z₀) endpoint n ≤
        C * (2 * δ) * ∑ q ∈ P, 1 / (q : ℝ) := by
    have h := hcollisionX z₁ Y hz hzX hY
    rw [show (∑ i : Fin (z₁ - z₀),
        ∑ q ∈ mtAdjacentPrimeBlock endpoint i, 1 / (q : ℝ)) =
          ∑ q ∈ P, 1 / (q : ℝ) from hmassEq] at h
    simpa only [C, z₀, δ, endpoint, P] using h
  have hboundary :
      ∑ n ∈ Finset.Icc 1 Y,
          weightedMTHarmanThresholdBoundaryCount K P P δ E n ≤
        C * (64 * δ) * ∑ q ∈ P, 1 / (q : ℝ) := by
    simpa only [C, z₀, δ, P] using
      hboundaryX P P E Y hY hprime hlower hprime
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        weightedMTHarmanNonrectangularCount K (t := z₁ - z₀) endpoint P δ E n =
      (∑ n ∈ Finset.Icc 1 Y,
        weightedMTHarmanSameCellCollisionCount K (t := z₁ - z₀) endpoint n) +
      ∑ n ∈ Finset.Icc 1 Y,
        weightedMTHarmanThresholdBoundaryCount K P P δ E n := by
      simp only [weightedMTHarmanNonrectangularCount, Finset.sum_add_distrib]
    _ ≤ C * (2 * δ) * ∑ q ∈ P, 1 / (q : ℝ) +
        C * (64 * δ) * ∑ q ∈ P, 1 / (q : ℝ) :=
      add_le_add hcollision hboundary
    _ = (4 : ℝ) ^ K * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
          (66 * δ) * ∑ q ∈ P, 1 / (q : ℝ) := by
      dsimp [C]
      ring

/-- Complete triple-term majorant: the pair obstruction plus the second same-cell order
collision `q₃<q₂`. -/
def weightedMTHarmanTripleNonrectangularCount
    (K : ℕ) {t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (δ E : ℝ) (n : ℕ) : ℝ :=
  weightedMTHarmanNonrectangularCount K (t := t) endpoint P δ E n +
    weightedMTHarmanSameCellCollisionCount K (t := t) endpoint n

/-- Triple-term nonrectangular support has weighted mean at most `68δ_A` times outer reciprocal
prime mass. -/
theorem eventually_sum_weightedMTHarmanTripleNonrectangularCount_paperAligned_le
    (A K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (z₁ Y : ℕ) (E : ℝ),
      mtLowerCutoffNat X ≤ z₁ → (z₁ : ℝ) ≤ X → 1 ≤ Y →
      let endpoint :=
        mtPaperAlignedEndpoint (mtLowerCutoffNat X) z₁ (mtPaperWidth A X)
      let P := primesIco (mtLowerCutoffNat X) z₁
      ∑ n ∈ Finset.Icc 1 Y,
          weightedMTHarmanTripleNonrectangularCount K
            (t := z₁ - mtLowerCutoffNat X) endpoint P
            (mtPaperWidth A X) E n ≤
        (4 : ℝ) ^ K * (Y : ℝ) *
          (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
            (68 * mtPaperWidth A X) * ∑ q ∈ P, 1 / (q : ℝ) := by
  filter_upwards [
    eventually_sum_weightedMTHarmanNonrectangularCount_paperAligned_le A K,
    eventually_sum_weightedMTHarmanSameCellCollisionCount_paperAligned_le A K,
    eventually_one_le_mtPaperWidth_mul_mtLowerCutoffNat_sub_one A,
    Filter.eventually_ge_atTop (Real.exp 1)] with
      X hpairX hcollisionX hprogressX hX
  intro z₁ Y E hz hzX hY
  dsimp only
  let z₀ := mtLowerCutoffNat X
  let δ := mtPaperWidth A X
  let endpoint := mtPaperAlignedEndpoint z₀ z₁ δ
  let P := primesIco z₀ z₁
  let C : ℝ := (4 : ℝ) ^ K * (Y : ℝ) *
    (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1)
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
  have hmonoEndpoint : Monotone endpoint := by
    dsimp [endpoint]
    exact mtPaperAlignedEndpoint_monotone hzOne (by simpa only [z₀] using hz) hδ0
      (by simpa only [z₀, δ] using hprogressX)
  have hterminal : endpoint (z₁ - z₀) = z₁ := by
    dsimp [endpoint]
    exact mtPaperAlignedEndpoint_sub_eq hzOne (by simpa only [z₀] using hz) hδ0
      (by simpa only [z₀, δ] using hprogressX)
  have hmassEq :
      (∑ i : Fin (z₁ - z₀), ∑ q ∈ mtAdjacentPrimeBlock endpoint i, 1 / (q : ℝ)) =
        ∑ q ∈ P, 1 / (q : ℝ) := by
    have hsum := sum_mtAdjacentPrimeBlock_eq_sum_primesIco
      (t := z₁ - z₀) endpoint hmonoEndpoint (fun q => 1 / (q : ℝ))
    simpa only [P, endpoint, mtPaperAlignedEndpoint_zero, hterminal] using hsum
  have hpair :
      ∑ n ∈ Finset.Icc 1 Y,
          weightedMTHarmanNonrectangularCount K (t := z₁ - z₀) endpoint P δ E n ≤
        C * (66 * δ) * ∑ q ∈ P, 1 / (q : ℝ) := by
    simpa only [C, z₀, δ, endpoint, P] using hpairX z₁ Y E hz hzX hY
  have hcollision :
      ∑ n ∈ Finset.Icc 1 Y,
          weightedMTHarmanSameCellCollisionCount K (t := z₁ - z₀) endpoint n ≤
        C * (2 * δ) * ∑ q ∈ P, 1 / (q : ℝ) := by
    have h := hcollisionX z₁ Y hz hzX hY
    rw [show (∑ i : Fin (z₁ - z₀),
        ∑ q ∈ mtAdjacentPrimeBlock endpoint i, 1 / (q : ℝ)) =
          ∑ q ∈ P, 1 / (q : ℝ) from hmassEq] at h
    simpa only [C, z₀, δ, endpoint, P] using h
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        weightedMTHarmanTripleNonrectangularCount K
          (t := z₁ - z₀) endpoint P δ E n =
      (∑ n ∈ Finset.Icc 1 Y,
        weightedMTHarmanNonrectangularCount K endpoint P δ E n) +
      ∑ n ∈ Finset.Icc 1 Y,
        weightedMTHarmanSameCellCollisionCount K endpoint n := by
      simp only [weightedMTHarmanTripleNonrectangularCount, Finset.sum_add_distrib]
    _ ≤ C * (66 * δ) * ∑ q ∈ P, 1 / (q : ℝ) +
        C * (2 * δ) * ∑ q ∈ P, 1 / (q : ℝ) :=
      add_le_add hpair hcollision
    _ = (4 : ℝ) ^ K * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
          (68 * δ) * ∑ q ∈ P, 1 / (q : ℝ) := by
      dsimp [C]
      ring

end

end RHTower.Sieve
