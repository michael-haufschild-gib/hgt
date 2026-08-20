import GaloisForLFunctions.HTGeometry.TwistedDiagonal

/-!
# Diagonal and off-diagonal of a twisted mean value

Splitting the exact double sum of `twisted_meanValue` along the diagonal `nk = mh` gives the
classical shape: a main term of length `U` supported on the diagonal, plus an oscillatory remainder
whose every entry is at most `2·max(nk, mh)` in modulus.  Both statements are exact; the second is
the only estimate, and it is the trivial one coming from `|log(nk/mh)| ≥ 1/max(nk,mh)`.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The coefficient attached to the pair `(m,n)` in a twisted mean value. -/
def twistedCoeff (a b : ℕ → ℂ) (σ : ℝ) (m n : ℕ) : ℂ :=
  a m * (starRingEnd ℂ) (b n) * ((((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ)) : ℂ)

/-- **Diagonal/off-diagonal split of the twisted mean value.** -/
theorem twisted_meanValue_split (a b : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) {h k : ℕ}
    (hh : 1 ≤ h) (hk : 1 ≤ k) (hs : ∀ n ∈ s, 1 ≤ n) (T U : ℝ) :
    (∫ t in T..(T + U), cdpoly a s σ t * (starRingEnd ℂ) (cdpoly b s σ t)
        * Complex.exp ((((Real.log k - Real.log h) * t : ℝ)) * I))
      = (U : ℂ) * (∑ m ∈ s, ∑ n ∈ s.filter (fun n => n * k = m * h),
            twistedCoeff a b σ m n)
        + ∑ m ∈ s, ∑ n ∈ s.filter (fun n => ¬ (n * k = m * h)),
            twistedCoeff a b σ m n
              * expInt (Real.log n - Real.log m + (Real.log k - Real.log h)) T U := by
  classical
  rw [twisted_meanValue a b s σ (Real.log k - Real.log h) T U]
  simp only [twistedCoeff]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : 1 ≤ m := hs m hm
  have hdiag : (∑ n ∈ s.filter (fun n => n * k = m * h),
        a m * (starRingEnd ℂ) (b n) * ((((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ)) : ℂ)
          * expInt (Real.log n - Real.log m + (Real.log k - Real.log h)) T U)
      = ∑ n ∈ s.filter (fun n => n * k = m * h),
          (U : ℂ) * (a m * (starRingEnd ℂ) (b n)
            * ((((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ)) : ℂ)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hns, hneq⟩ := Finset.mem_filter.mp hn
    rw [expInt_twisted_diag hm1 (hs n hns) hh hk hneq]
    ring
  rw [← Finset.sum_filter_add_sum_filter_not s (fun n => n * k = m * h), hdiag,
    ← Finset.mul_sum]

/-- **The off-diagonal is trivially bounded** by `2·max(nk, mh)` per entry. -/
theorem norm_twisted_offDiagonal_le (a b : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) {h k : ℕ}
    (hh : 1 ≤ h) (hk : 1 ≤ k) (hs : ∀ n ∈ s, 1 ≤ n) (T U : ℝ) :
    ‖∑ m ∈ s, ∑ n ∈ s.filter (fun n => ¬ (n * k = m * h)),
        twistedCoeff a b σ m n
          * expInt (Real.log n - Real.log m + (Real.log k - Real.log h)) T U‖
      ≤ ∑ m ∈ s, ∑ n ∈ s.filter (fun n => ¬ (n * k = m * h)),
          ‖twistedCoeff a b σ m n‖ * (2 * max ((n * k : ℕ) : ℝ) ((m * h : ℕ) : ℝ)) := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun m hm => ?_
  have hm1 : 1 ≤ m := hs m hm
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun n hn => ?_
  obtain ⟨hns, hneq⟩ := Finset.mem_filter.mp hn
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact norm_expInt_twisted_offdiag hm1 (hs n hns) hh hk hneq T U

end GaloisForLFunctions.HTGeometry

end
