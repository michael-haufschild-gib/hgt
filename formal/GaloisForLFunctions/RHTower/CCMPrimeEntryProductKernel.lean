import GaloisForLFunctions.RHTower.CCMPrimeEntryOverlapKernel

/-!
# Product and ratio coordinates for finite prime-entry energy

On the product layer R = nm, the two entry times are reconstructed from
log R and log(n/m). The finite-time overlap supplies its own ratio cutoff:
it vanishes when either entry reaches the terminal time. Its closed form
retains the boundary subtraction that a limiting overlap would lose.
-/

noncomputable section
open MeasureTheory Set

namespace RHTower

theorem ccmPrimeEntryOverlap_eq_zero_of_left_ge {T a : ℝ} (hT : 0 ≤ T)
    (ha : T ≤ a) (b : ℝ) : ccmPrimeEntryOverlap T a b = 0 := by
  unfold ccmPrimeEntryOverlap
  calc
    _ = ∫ _t in (0 : ℝ)..T, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hta := ((uIcc_of_le hT ▸ ht).2).trans ha
      simp only [ccmPrimeEntryTent, max_eq_right (sub_nonpos.mpr hta), mul_zero, zero_mul]
    _ = 0 := intervalIntegral.integral_zero

theorem ccmPrimeEntryOverlap_eq_zero_of_right_ge {T b : ℝ} (hT : 0 ≤ T)
    (hb : T ≤ b) (a : ℝ) : ccmPrimeEntryOverlap T a b = 0 := by
  rw [ccmPrimeEntryOverlap_comm]
  exact ccmPrimeEntryOverlap_eq_zero_of_left_ge hT hb a

def ccmPrimeEntryProductKernel (T : ℝ) (R : ℕ) (s : ℝ) : ℝ :=
  ccmPrimeEntryOverlap T ((Real.log R + s) / 2) ((Real.log R - s) / 2)

theorem ccmPrimeEntryProductKernel_even (T : ℝ) (R : ℕ) (s : ℝ) :
    ccmPrimeEntryProductKernel T R (-s) = ccmPrimeEntryProductKernel T R s := by
  unfold ccmPrimeEntryProductKernel
  simp only [sub_eq_add_neg, neg_neg]
  exact ccmPrimeEntryOverlap_comm _ _ _

theorem ccmPrimeEntryProductKernel_nonneg {T : ℝ} (hT : 0 ≤ T) (R : ℕ) (s : ℝ) :
    0 ≤ ccmPrimeEntryProductKernel T R s := ccmPrimeEntryOverlap_nonneg hT _ _

/-- The product-layer kernel is the literal original finite overlap. -/
theorem ccmPrimeEntryProductKernel_log_ratio (T : ℝ) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) :
    ccmPrimeEntryProductKernel T (n * m) (Real.log n - Real.log m) =
      ccmPrimeEntryOverlap T (Real.log n) (Real.log m) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hm)
  unfold ccmPrimeEntryProductKernel
  rw [Nat.cast_mul, Real.log_mul hnR hmR]
  congr 1 <;> ring

/-- The terminal cutoff is a product-dependent interval in log ratio.
It is not permissible to replace this kernel by an untruncated ratio weight. -/
theorem ccmPrimeEntryProductKernel_eq_zero_of_ratio_ge {T s : ℝ} {R : ℕ}
    (hT : 0 ≤ T) (hs : 2 * T - Real.log R ≤ |s|) :
    ccmPrimeEntryProductKernel T R s = 0 := by
  unfold ccmPrimeEntryProductKernel
  rcases le_or_gt 0 s with hs0 | hs0
  · rw [abs_of_nonneg hs0] at hs
    exact ccmPrimeEntryOverlap_eq_zero_of_left_ge hT (by linarith) _
  · rw [abs_of_neg hs0] at hs
    exact ccmPrimeEntryOverlap_eq_zero_of_right_ge hT (by linarith) _

/-- The full product/ratio formula inside the terminal interval includes
the polynomial boundary counterterm. -/
theorem ccmPrimeEntryProductKernel_eq {T s : ℝ} {R : ℕ} (hR : 0 < R)
    (hs : |s| ≤ 2 * T - Real.log R) :
    ccmPrimeEntryProductKernel T R s =
      Real.exp (-Real.log R / 2) * ccmPrimeEntryRatioKernel s -
        Real.exp (-T) * ((T - Real.log R / 2) ^ 2 - s ^ 2 / 4 +
          2 * (T - Real.log R / 2) + 2) := by
  have hlog : 0 ≤ Real.log R := Real.log_nonneg (by exact_mod_cast hR)
  have hmax : 0 ≤ max ((Real.log R + s) / 2) ((Real.log R - s) / 2) := by
    have h1 := le_max_left ((Real.log R + s) / 2) ((Real.log R - s) / 2)
    have h2 := le_max_right ((Real.log R + s) / 2) ((Real.log R - s) / 2)
    linarith only [hlog, h1, h2]
  obtain ⟨hslo, hshi⟩ := abs_le.mp hs
  rw [ccmPrimeEntryProductKernel,
    ccmPrimeEntryOverlap_eq hmax (by linarith) (by linarith),
    ccmPrimeEntryOverlapLimit_eq_ratio]
  rw [show -(((Real.log R + s) / 2) + (Real.log R - s) / 2) / 2 =
      -Real.log R / 2 by ring,
    show (Real.log R + s) / 2 - (Real.log R - s) / 2 = s by ring]
  ring

end RHTower
