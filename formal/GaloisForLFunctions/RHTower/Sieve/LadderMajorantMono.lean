import GaloisForLFunctions.RHTower.Sieve.LadderAffineMajorant
import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetLadderTail

/-!
# The ladder majorants are monotone

Both halves of the ladder's affine majorant increase with the length of the fibre index range and
with the annulus constant.  This is what lets the spectral estimate at a shrunk window be compared
with the corpus's estimate at the full one instead of being re-derived: the shrunk window has a
shorter index range and a smaller annulus constant, so every majorant is inherited.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

theorem ladderDefectSum_mono {L B₀ B₁ : ℕ} {Q η : ℝ} (hQ1 : 1 < Q) (hη : 0 ≤ η)
    (hB0 : 1 ≤ B₀) (hB : B₀ ≤ B₁) :
    ladderDefectSum L B₀ Q η ≤ ladderDefectSum L B₁ Q η := by
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ1
  have hlogQ : (0 : ℝ) < Real.log Q := Real.log_pos hQ1
  have hr : (0 : ℝ) < 1 + η := by linarith
  have hBR : ((B₀ : ℕ) : ℝ) ≤ ((B₁ : ℕ) : ℝ) := Nat.cast_le.2 hB
  have hB0R : (1 : ℝ) ≤ ((B₀ : ℕ) : ℝ) := by exact_mod_cast hB0
  have hfl : (⌊((B₀ : ℕ) : ℝ) * (1 + η)⌋₊ : ℕ) ≤ (⌊((B₁ : ℕ) : ℝ) * (1 + η)⌋₊ : ℕ) :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right hBR hr.le)
  have hfl1 : 1 ≤ (⌊((B₀ : ℕ) : ℝ) * (1 + η)⌋₊ : ℕ) := by
    refine Nat.le_floor ?_
    push_cast
    nlinarith [hB0R, hη]
  have hlog : Real.log ((⌊((B₀ : ℕ) : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ)
      ≤ Real.log ((⌊((B₁ : ℕ) : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) := by
    refine Real.log_le_log ?_ (Nat.cast_le.2 hfl)
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hfl1
  have hlog0 : (0 : ℝ) ≤ Real.log ((⌊((B₀ : ℕ) : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast hfl1
  have hsum : ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
        * ((1 + ((B₀ : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 5
          + ((B₀ : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ (2 : ℕ))
      ≤ ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
        * ((1 + ((B₁ : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 5
          + ((B₁ : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ (2 : ℕ)) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    have hfac : (0 : ℝ) ≤ Q * (1 + η) ^ j * η + 1 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hfac
    gcongr
  have hsum0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
      * ((1 + ((B₀ : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 5
        + ((B₀ : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ (2 : ℕ)) := by
    refine Finset.sum_nonneg fun j _ => ?_
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    positivity
  rw [ladderDefectSum, ladderDefectSum]
  gcongr

theorem ladderAffineSlope_mono {L B₀ B₁ : ℕ} {Q η ρ₀ ρ₁ : ℝ} (hQ1 : 1 < Q) (hη : 0 ≤ η)
    (hB0 : 1 ≤ B₀) (hB : B₀ ≤ B₁) (hρ0 : 0 ≤ ρ₀) (hρ : ρ₀ ≤ ρ₁) :
    ladderAffineSlope L B₀ Q η ρ₀ ≤ ladderAffineSlope L B₁ Q η ρ₁ := by
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ1
  have hr : (0 : ℝ) < 1 + η := by linarith
  have hBR : ((B₀ : ℕ) : ℝ) ≤ ((B₁ : ℕ) : ℝ) := Nat.cast_le.2 hB
  have hpi := Real.pi_pos
  have hsum : ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
        * Real.sqrt (((B₀ : ℕ) : ℝ) / (Q * (1 + η) ^ j) + 1)
      ≤ ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
        * Real.sqrt (((B₁ : ℕ) : ℝ) / (Q * (1 + η) ^ j) + 1) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    gcongr
  have hsum0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
      * Real.sqrt (((B₀ : ℕ) : ℝ) / (Q * (1 + η) ^ j) + 1) := by
    refine Finset.sum_nonneg fun j _ => ?_
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    positivity
  have hdef := ladderDefectSum_mono (L := L) hQ1 hη hB0 hB
  rw [ladderAffineSlope, ladderAffineSlope]
  gcongr

theorem ladderAffineConst_mono {z₀ z L B₀ B₁ : ℕ} {Q η ρ₀ ρ₁ s w₀ : ℝ} (hQ1 : 1 < Q)
    (hη : 0 ≤ η) (hB0 : 1 ≤ B₀) (hB : B₀ ≤ B₁) (hρ0 : 0 ≤ ρ₀) (hρ : ρ₀ ≤ ρ₁) (hs : 0 ≤ s) :
    ladderAffineConst z₀ z L B₀ Q η ρ₀ s w₀ ≤ ladderAffineConst z₀ z L B₁ Q η ρ₁ s w₀ := by
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ1
  have hr : (0 : ℝ) < 1 + η := by linarith
  have hBR : ((B₀ : ℕ) : ℝ) ≤ ((B₁ : ℕ) : ℝ) := Nat.cast_le.2 hB
  have he := Real.exp_pos (1 : ℝ)
  have hsum : ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
        * Real.sqrt ((((B₀ : ℕ) : ℝ) / (Q * (1 + η) ^ j))
            * (((B₀ : ℕ) : ℝ) / (Q * (1 + η) ^ j) + 1))
      ≤ ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
        * Real.sqrt ((((B₁ : ℕ) : ℝ) / (Q * (1 + η) ^ j))
            * (((B₁ : ℕ) : ℝ) / (Q * (1 + η) ^ j) + 1)) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    gcongr
  have hsum0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
      * Real.sqrt ((((B₀ : ℕ) : ℝ) / (Q * (1 + η) ^ j))
          * (((B₀ : ℕ) : ℝ) / (Q * (1 + η) ^ j) + 1)) := by
    refine Finset.sum_nonneg fun j _ => ?_
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    positivity
  have hdisc : ∑ j ∈ Finset.range L, discMajorant (primesRange z₀ z) B₀ Q η s w₀ j
      ≤ ∑ j ∈ Finset.range L, discMajorant (primesRange z₀ z) B₁ Q η s w₀ j := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    rw [discMajorant, discMajorant]
    have hc0 : (0 : ℝ) ≤ ((geomBlock (primesRange z₀ z) Q (1 + η) j).card : ℝ) + 1 := by
      positivity
    have hw : (0 : ℝ) ≤ Real.sqrt (2 * w₀) + 1 := by positivity
    gcongr
  have hdisc0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range L,
      discMajorant (primesRange z₀ z) B₀ Q η s w₀ j := by
    refine Finset.sum_nonneg fun j _ => (discMajorant_pos hQ0 hη hs j).le
  have hdef := ladderDefectSum_mono (L := L) hQ1 hη hB0 hB
  have hdef0 : (0 : ℝ) ≤ ladderDefectSum L B₀ Q η := ladderDefectSum_nonneg hQ1 hη
  have hflmono : ((⌊((B₀ : ℕ) : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ)
      ≤ ((⌊((B₁ : ℕ) : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) :=
    Nat.cast_le.2 (Nat.floor_mono (mul_le_mul_of_nonneg_right hBR hr.le))
  rw [ladderAffineConst, ladderAffineConst]
  gcongr

/-- The slope majorant increases with the index range, at a fixed annulus constant. -/
theorem ladderAffineSlope_mono_index {L B₀ B₁ : ℕ} {Q η ρ : ℝ} (hQ1 : 1 < Q) (hη : 0 ≤ η)
    (hB0 : 1 ≤ B₀) (hB : B₀ ≤ B₁) :
    ladderAffineSlope L B₀ Q η ρ ≤ ladderAffineSlope L B₁ Q η ρ := by
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ1
  have hr : (0 : ℝ) < 1 + η := by linarith
  have hBR : ((B₀ : ℕ) : ℝ) ≤ ((B₁ : ℕ) : ℝ) := Nat.cast_le.2 hB
  have hpi := Real.pi_pos
  have hsum : ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
        * Real.sqrt (((B₀ : ℕ) : ℝ) / (Q * (1 + η) ^ j) + 1)
      ≤ ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
        * Real.sqrt (((B₁ : ℕ) : ℝ) / (Q * (1 + η) ^ j) + 1) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    gcongr
  have hsum0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
      * Real.sqrt (((B₀ : ℕ) : ℝ) / (Q * (1 + η) ^ j) + 1) := by
    refine Finset.sum_nonneg fun j _ => ?_
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    positivity
  have hdef := ladderDefectSum_mono (L := L) hQ1 hη hB0 hB
  rw [ladderAffineSlope, ladderAffineSlope]
  gcongr

/-- The constant majorant increases with the index range, at a fixed annulus constant. -/
theorem ladderAffineConst_mono_index {z₀ z L B₀ B₁ : ℕ} {Q η ρ s w₀ : ℝ} (hQ1 : 1 < Q)
    (hη : 0 ≤ η) (hB0 : 1 ≤ B₀) (hB : B₀ ≤ B₁) (hs : 0 ≤ s) :
    ladderAffineConst z₀ z L B₀ Q η ρ s w₀ ≤ ladderAffineConst z₀ z L B₁ Q η ρ s w₀ := by
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ1
  have hr : (0 : ℝ) < 1 + η := by linarith
  have hBR : ((B₀ : ℕ) : ℝ) ≤ ((B₁ : ℕ) : ℝ) := Nat.cast_le.2 hB
  have he := Real.exp_pos (1 : ℝ)
  have hsum : ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
        * Real.sqrt ((((B₀ : ℕ) : ℝ) / (Q * (1 + η) ^ j))
            * (((B₀ : ℕ) : ℝ) / (Q * (1 + η) ^ j) + 1))
      ≤ ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
        * Real.sqrt ((((B₁ : ℕ) : ℝ) / (Q * (1 + η) ^ j))
            * (((B₁ : ℕ) : ℝ) / (Q * (1 + η) ^ j) + 1)) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    gcongr
  have hsum0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
      * Real.sqrt ((((B₀ : ℕ) : ℝ) / (Q * (1 + η) ^ j))
          * (((B₀ : ℕ) : ℝ) / (Q * (1 + η) ^ j) + 1)) := by
    refine Finset.sum_nonneg fun j _ => ?_
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    positivity
  have hdisc : ∑ j ∈ Finset.range L, discMajorant (primesRange z₀ z) B₀ Q η s w₀ j
      ≤ ∑ j ∈ Finset.range L, discMajorant (primesRange z₀ z) B₁ Q η s w₀ j := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    rw [discMajorant, discMajorant]
    have hc0 : (0 : ℝ) ≤ ((geomBlock (primesRange z₀ z) Q (1 + η) j).card : ℝ) + 1 := by
      positivity
    have hw : (0 : ℝ) ≤ Real.sqrt (2 * w₀) + 1 := by positivity
    gcongr
  have hdisc0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range L,
      discMajorant (primesRange z₀ z) B₀ Q η s w₀ j :=
    Finset.sum_nonneg fun j _ => (discMajorant_pos hQ0 hη hs j).le
  have hdef := ladderDefectSum_mono (L := L) hQ1 hη hB0 hB
  have hdef0 : (0 : ℝ) ≤ ladderDefectSum L B₀ Q η := ladderDefectSum_nonneg hQ1 hη
  have hflmono : ((⌊((B₀ : ℕ) : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ)
      ≤ ((⌊((B₁ : ℕ) : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) :=
    Nat.cast_le.2 (Nat.floor_mono (mul_le_mul_of_nonneg_right hBR hr.le))
  rw [ladderAffineConst, ladderAffineConst]
  gcongr

end

end RHTower.Sieve
