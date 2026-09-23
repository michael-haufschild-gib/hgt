import GaloisForLFunctions.RHTower.Sieve.LadderStepAffine
import GaloisForLFunctions.RHTower.Sieve.SpectralHeadBound
import GaloisForLFunctions.RHTower.Sieve.AffineMajorantFromHeight

/-!
# The affine majorant of the weighted polynomial, from the ladder

Gallagher's dyadic tail divides the *constant* of the affine majorant by the square of the cut, so a
constant of the trivial size `B₀·Ec` reproduces the trivial bound.  The constant must come from the
ladder, where the mean value theorem is applied to each cofactor polynomial — of length `B₀/Q_j`,
not `B₀`.  Above the height at which the ladder's analytic input expires the trivial majorant is
used, and the two regimes combine into one affine majorant by absorbing the trivial constant into
the slope.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The ladder defect's shape factor. -/
def ladderDefectSum (L B₀ : ℕ) (Q η : ℝ) : ℝ :=
  Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q
    * ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
        * ((1 + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5
          + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ (2 : ℕ))

/-- The slope of the ladder's affine majorant. -/
def ladderAffineSlope (L B₀ : ℕ) (Q η ρ : ℝ) : ℝ :=
  4 * (5 * Real.pi / 2) * ρ ^ (2 : ℕ)
      * (∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
          * Real.sqrt ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)) ^ (2 : ℕ)
    + 2 * (5 * Real.pi / 2) * ladderDefectSum L B₀ Q η

/-- The constant of the ladder's affine majorant. -/
def ladderAffineConst (z₀ z L B₀ : ℕ) (Q η ρ s w₀ : ℝ) : ℝ :=
  4 * (5 * Real.exp 1 / 2) * ρ ^ (2 : ℕ)
      * (∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
          * Real.sqrt (((B₀ : ℝ) / (Q * (1 + η) ^ j))
              * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))) ^ (2 : ℕ)
    + 2 * (∑ j ∈ Finset.range L, discMajorant (primesRange z₀ z) B₀ Q η s w₀ j) ^ (2 : ℕ)
    + 2 * (5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ)) * ladderDefectSum L B₀ Q η

/-- **The ladder's affine majorant at a height where its analytic input holds.** -/
theorem integral_normSq_omegaWeighted_affine_le {z₀ z L B₀ : ℕ} {Q η w₀ T ρ s : ℝ}
    (hQ : Q = (z₀ : ℝ)) (hQ1 : 1 < Q) (hη : 0 < η) (hT : 1 ≤ T) (hw₀ : 0 ≤ w₀) (hwT : w₀ ≤ T)
    (hL : 1 ≤ L) (hρ : 0 < ρ) (hs : 0 ≤ s) (hz : z = ⌊Q * (1 + η) ^ L⌋₊) (hB : 0 < (B₀ : ℝ))
    (hV : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-T) T \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock (primesRange z₀ z) Q (1 + η) j) w‖ ≤ ρ * (Q * (1 + η) ^ j))
    (hU : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly moebiusCoeff (geomCofactorBlockAt 1 B₀ Q η j) w‖
        ≤ s * ((B₀ : ℝ) / (Q * (1 + η) ^ j))) :
    (∫ w in Set.Icc (-T) T,
        ‖omegaWeightedMoebiusPoly (primesRange z₀ z) (Finset.Icc 1 B₀) w‖ ^ (2 : ℕ))
      ≤ ladderAffineSlope L B₀ Q η ρ * T + ladderAffineConst z₀ z L B₀ Q η ρ s w₀ := by
  classical
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ1
  have hη0 : (0 : ℝ) ≤ η := hη.le
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hPprime : ∀ q ∈ primesRange z₀ z, q.Prime := fun q hq => (mem_primesRange.1 hq).1
  have hPbd := primesRange_ladder_bounds (z := z) (L := L) hQ hη0 hQ0.le hz
  have hPge : ∀ p ∈ primesRange z₀ z, Q ≤ (p : ℝ) := fun p hp => (hPbd p hp).1.le
  set V : ℕ → ℝ := fun j => ρ * (Q * (1 + η) ^ j) with hV'
  set U : ℕ → ℝ := fun j => s * ((B₀ : ℝ) / (Q * (1 + η) ^ j)) with hU'
  set Vlow : ℕ → ℝ := fun j => ((geomBlock (primesRange z₀ z) Q (1 + η) j).card : ℝ) with hVlow
  have hVpos : ∀ j, 0 ≤ V j := by
    intro j
    have : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    rw [hV']
    positivity
  have hUpos : ∀ j, 0 ≤ U j := by
    intro j
    have : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    rw [hU']
    positivity
  have hVlowpos : ∀ j, 0 ≤ Vlow j := fun j => Nat.cast_nonneg _
  have hcpos : ∀ j ∈ Finset.range L, 0 < stepAffineMajorant B₀ Q η ρ T j := fun j _ =>
    stepAffineMajorant_pos hQ0 hη0 hρ hB j
  have hdpos : ∀ j ∈ Finset.range L, 0 < discMajorant (primesRange z₀ z) B₀ Q η s w₀ j :=
    fun j _ => discMajorant_pos hQ0 hη0 hs j
  have hcT : ∀ j ∈ Finset.range L,
      V j ^ (2 : ℕ) * ladderStepMVT B₀ Q η T j ≤ (stepAffineMajorant B₀ Q η ρ T j) ^ (2 : ℕ) := fun j _ =>
    stepAffineMajorant_sq_ge hQ0 hη0 hρ.le hT0.le j (hVpos j) le_rfl
  have hdT : ∀ j ∈ Finset.range L,
      Vlow j ^ (2 : ℕ) * U j ^ (2 : ℕ) * (2 * w₀)
        ≤ (discMajorant (primesRange z₀ z) B₀ Q η s w₀ j) ^ (2 : ℕ) := fun j _ =>
    discMajorant_sq_ge hQ0 hη0 hs hw₀ j (hUpos j) (hVlowpos j) le_rfl le_rfl
  have hlowP : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock (primesRange z₀ z) Q (1 + η) j) w‖ ≤ Vlow j := by
    intro j _ w _
    exact norm_primeBlockPoly_le_card _ w
  have hmain := integral_normSq_omegaWeighted_annulus_optimal_two_le (P := primesRange z₀ z)
    (A₀ := 1) (B₀ := B₀) (by omega) hQ1 hη0 hT hw₀ hwT hL hPprime hPge hPbd
    (fun j => stepAffineMajorant B₀ Q η ρ T j)
    (fun j => discMajorant (primesRange z₀ z) B₀ Q η s w₀ j)
    V U Vlow hcpos hdpos hVpos hUpos hVlowpos hcT hdT hV hlowP hU
  have hcsum := sum_stepAffineMajorant_sq_le (B₀ := B₀) (Q := Q) (η := η) (ρ := ρ) (T := T)
    hQ0 hη0 hT0.le L
  refine hmain.trans ?_
  rw [ladderAffineSlope, ladderAffineConst, ladderDefectSum]
  have hone : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
  rw [hone]
  nlinarith [hcsum, sq_nonneg (∑ j ∈ Finset.range L,
    discMajorant (primesRange z₀ z) B₀ Q η s w₀ j)]

/-- **Two regimes, one affine majorant.**  Below the height at which the ladder's input expires the
ladder majorant is used; above it the mean value theorem is, and its constant is absorbed into the
slope. -/
theorem affineMajorant_two_regime {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : (0 : ℕ) ∉ s) {M : ℕ}
    (hsM : ∀ n ∈ s, n ≤ M) {G T₀ α₁ β₁ : ℝ} (hG : 1 ≤ G) (hGT₀ : G ≤ T₀)
    (hα₁ : 0 ≤ α₁) (hβ₁ : 0 ≤ β₁)
    (hmid : ∀ T : ℝ, G ≤ T → T ≤ T₀ →
      (∫ w in Set.Icc (-T) T, ‖logPoly a s w‖ ^ (2 : ℕ)) ≤ α₁ * T + β₁) :
    ∀ T : ℝ, G ≤ T →
      (∫ w in Set.Icc (-T) T, ‖logPoly a s w‖ ^ (2 : ℕ))
        ≤ (α₁ + 5 * Real.pi / 2 * (∑ n ∈ s, ‖a n‖ ^ (2 : ℕ))
            + 5 * Real.exp 1 / 2 * (M : ℝ) * (∑ n ∈ s, ‖a n‖ ^ (2 : ℕ)) / T₀) * T + β₁ := by
  intro T hT
  have hT1 : (1 : ℝ) ≤ T := le_trans hG hT
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT1
  have hT₀0 : (0 : ℝ) < T₀ := lt_of_lt_of_le zero_lt_one (le_trans hG hGT₀)
  have hE0 : (0 : ℝ) ≤ ∑ n ∈ s, ‖a n‖ ^ (2 : ℕ) := Finset.sum_nonneg fun n _ => by positivity
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hextra : (0 : ℝ) ≤ 5 * Real.pi / 2 * (∑ n ∈ s, ‖a n‖ ^ (2 : ℕ))
      + 5 * Real.exp 1 / 2 * (M : ℝ) * (∑ n ∈ s, ‖a n‖ ^ (2 : ℕ)) / T₀ := by positivity
  rcases le_or_gt T T₀ with hle | hgt
  · have h := hmid T hT hle
    nlinarith [h, hextra, hT0]
  · have hmvt := integral_Icc_normSq_logPoly_le_energy a hs0 hsM hT1
    have habs : 5 * Real.exp 1 / 2 * (M : ℝ) * (∑ n ∈ s, ‖a n‖ ^ (2 : ℕ))
        ≤ 5 * Real.exp 1 / 2 * (M : ℝ) * (∑ n ∈ s, ‖a n‖ ^ (2 : ℕ)) / T₀ * T := by
      have hbase : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 * (M : ℝ) * (∑ n ∈ s, ‖a n‖ ^ (2 : ℕ)) := by positivity
      have hid : 5 * Real.exp 1 / 2 * (M : ℝ) * (∑ n ∈ s, ‖a n‖ ^ (2 : ℕ)) / T₀ * T
          = (5 * Real.exp 1 / 2 * (M : ℝ) * (∑ n ∈ s, ‖a n‖ ^ (2 : ℕ))) * (T / T₀) := by
        field_simp
      rw [hid]
      have hTT : (1 : ℝ) ≤ T / T₀ := (one_le_div hT₀0).2 hgt.le
      nlinarith [hbase, hTT]
    nlinarith [hmvt, habs, hα₁, hβ₁, hT0, hE0]

end

end RHTower.Sieve
