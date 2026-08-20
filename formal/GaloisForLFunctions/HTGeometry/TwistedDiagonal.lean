import GaloisForLFunctions.HTGeometry.TwistedDirichletMeanValue

/-!
# The diagonal of a twisted mean value

For a twist by `(h/k)^{-it}` the frequency attached to the pair `(m,n)` is
`log n − log m + log k − log h = log(nk) − log(mh)`.  It vanishes exactly on the classical diagonal
`nk = mh`, where the exponential window integral is the full length `U`; off it, the integral is at
most `2/|log(nk/mh)|`, and for distinct positive integers that logarithm is at least the reciprocal
of the larger one.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A concavity bound: `log A − log B ≥ (A−B)/A` for `0 < B ≤ A`. -/
theorem sub_div_le_log_sub_log {A B : ℝ} (hB : 0 < B) (hBA : B ≤ A) :
    (A - B) / A ≤ Real.log A - Real.log B := by
  have hA : 0 < A := lt_of_lt_of_le hB hBA
  have hquot : (0 : ℝ) < B / A := by positivity
  have h := Real.log_le_sub_one_of_pos hquot
  rw [Real.log_div hB.ne' hA.ne'] at h
  have hBA' : B / A = B / A := rfl
  have hkey : (A - B) / A = 1 - B / A := by field_simp
  rw [hkey]
  linarith

/-- For distinct positive naturals the logarithms differ by at least the reciprocal of the
larger one. -/
theorem inv_le_abs_log_sub_log {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hne : A ≠ B) :
    1 / (max (A : ℝ) (B : ℝ)) ≤ |Real.log A - Real.log B| := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  rcases lt_or_gt_of_ne (show (A : ℝ) ≠ (B : ℝ) by exact_mod_cast hne) with hlt | hgt
  · have hmax : max (A : ℝ) (B : ℝ) = (B : ℝ) := max_eq_right hlt.le
    have hstep := sub_div_le_log_sub_log hA0 hlt.le
    have hone : (1 : ℝ) ≤ (B : ℝ) - (A : ℝ) := by
      have : (A : ℝ) + 1 ≤ (B : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast hlt)
      linarith
    have hle : 1 / (B : ℝ) ≤ Real.log B - Real.log A := by
      refine le_trans ?_ hstep
      rw [div_le_div_iff₀ hB0 hB0]
      nlinarith
    rw [hmax]
    rw [abs_sub_comm]
    exact le_trans hle (le_abs_self _)
  · have hmax : max (A : ℝ) (B : ℝ) = (A : ℝ) := max_eq_left hgt.le
    have hstep := sub_div_le_log_sub_log hB0 hgt.le
    have hone : (1 : ℝ) ≤ (A : ℝ) - (B : ℝ) := by
      have : (B : ℝ) + 1 ≤ (A : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast hgt)
      linarith
    have hle : 1 / (A : ℝ) ≤ Real.log A - Real.log B := by
      refine le_trans ?_ hstep
      rw [div_le_div_iff₀ hA0 hA0]
      nlinarith
    rw [hmax]
    exact le_trans hle (le_abs_self _)

/-- The twisted frequency of the pair `(m,n)` is `log(nk) − log(mh)`. -/
theorem twistedFreq_eq {m n h k : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hh : 1 ≤ h) (hk : 1 ≤ k) :
    Real.log n - Real.log m + (Real.log k - Real.log h)
      = Real.log ((n * k : ℕ) : ℝ) - Real.log ((m * h : ℕ) : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  push_cast
  rw [Real.log_mul hn0.ne' hk0.ne', Real.log_mul hm0.ne' hh0.ne']
  ring

/-- On the twisted diagonal the window integral is the full length. -/
theorem expInt_twisted_diag {m n h k : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hh : 1 ≤ h) (hk : 1 ≤ k)
    (heq : n * k = m * h) (T U : ℝ) :
    expInt (Real.log n - Real.log m + (Real.log k - Real.log h)) T U = (U : ℂ) := by
  rw [twistedFreq_eq hm hn hh hk, heq, sub_self, expInt_zero]

/-- Off the twisted diagonal the window integral is at most `2·max(nk, mh)`. -/
theorem norm_expInt_twisted_offdiag {m n h k : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hk : 1 ≤ k) (hne : n * k ≠ m * h) (T U : ℝ) :
    ‖expInt (Real.log n - Real.log m + (Real.log k - Real.log h)) T U‖
      ≤ 2 * max ((n * k : ℕ) : ℝ) ((m * h : ℕ) : ℝ) := by
  have hnk : 1 ≤ n * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmh : 1 ≤ m * h := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hlow := inv_le_abs_log_sub_log hnk hmh hne
  have hmaxpos : (0 : ℝ) < max ((n * k : ℕ) : ℝ) ((m * h : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((n * k : ℕ) : ℝ) := by exact_mod_cast hnk
    exact lt_of_lt_of_le zero_lt_one (le_max_of_le_left this)
  have hfreq : Real.log n - Real.log m + (Real.log k - Real.log h)
      = Real.log ((n * k : ℕ) : ℝ) - Real.log ((m * h : ℕ) : ℝ) := twistedFreq_eq hm hn hh hk
  have habs : (0 : ℝ) < |Real.log ((n * k : ℕ) : ℝ) - Real.log ((m * h : ℕ) : ℝ)| := by
    refine lt_of_lt_of_le ?_ hlow
    positivity
  have hne' : Real.log n - Real.log m + (Real.log k - Real.log h) ≠ 0 := by
    rw [hfreq]
    intro hzero
    rw [hzero, abs_zero] at habs
    exact lt_irrefl 0 habs
  refine le_trans (norm_expInt_le hne' T U) ?_
  rw [hfreq, div_le_iff₀ habs]
  have hkey : 1 / (max ((n * k : ℕ) : ℝ) ((m * h : ℕ) : ℝ))
      ≤ |Real.log ((n * k : ℕ) : ℝ) - Real.log ((m * h : ℕ) : ℝ)| := hlow
  rw [div_le_iff₀ hmaxpos] at hkey
  nlinarith [hkey, hmaxpos, habs]

end GaloisForLFunctions.HTGeometry

end
