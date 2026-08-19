import GaloisForLFunctions.RHTower.Sieve.ScaledBadStart

/-!
# The fibre length, two-sided, from the start alone

The outer factor realising a prescribed start is only determined to within the interval
`[y/(t+1), y/t)`, so the length of its fibre is determined only to within one unit at each end.
Both bounds are what a marker needs: the upper one so that the fibre fits inside the marker's cell,
the lower one so that the fibre fills a definite proportion of it.
-/

namespace RHTower.Sieve

open Finset

/-- **The fibre length is `hy·t/√y` up to one unit at each end.** -/
theorem fibreLen_bounds {y hy : ℝ} {a t : ℕ} (hy4 : 4 ≤ y) (hy0 : 0 ≤ hy) (ht1 : 1 ≤ t)
    (ha1 : 1 ≤ a) (hstart : fibreStartIdx y a = t)
    (halow : y / ((t : ℝ) + 1) ≤ (a : ℝ)) (hahigh : (a : ℝ) < y / (t : ℝ)) :
    hy * (t : ℝ) / Real.sqrt y - 1 ≤ (fibreLen y hy a : ℝ)
      ∧ (fibreLen y hy a : ℝ) ≤ hy * ((t : ℝ) + 1) / Real.sqrt y + 1 := by
  have hy0' : (0 : ℝ) < y := by linarith
  have hsy : (0 : ℝ) < Real.sqrt y := Real.sqrt_pos.2 hy0'
  have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
  have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
  have ha0 : (0 : ℝ) < (a : ℝ) := by linarith
  have htop0 : (0 : ℝ) ≤ y + hy * Real.sqrt y := by positivity
  set T : ℝ := (y + hy * Real.sqrt y) / (a : ℝ) with hT
  have hyoversqrt : y / Real.sqrt y = Real.sqrt y := by
    rw [eq_comm, eq_div_iff (ne_of_gt hsy)]
    linarith [hsq]
  -- the lower bound for `T`
  have hTlow : (t : ℝ) + hy * (t : ℝ) / Real.sqrt y ≤ T := by
    rw [hT, le_div_iff₀ ha0]
    have hat : (a : ℝ) * (t : ℝ) < y := by
      rw [lt_div_iff₀ (by linarith : (0:ℝ) < (t:ℝ))] at hahigh
      linarith
    have hexp : ((t : ℝ) + hy * (t : ℝ) / Real.sqrt y) * (a : ℝ)
        = ((a : ℝ) * (t : ℝ)) * (1 + hy / Real.sqrt y) := by
      field_simp
    rw [hexp]
    have hfac : (0 : ℝ) ≤ 1 + hy / Real.sqrt y := by positivity
    have hkey : ((a : ℝ) * (t : ℝ)) * (1 + hy / Real.sqrt y)
        ≤ y * (1 + hy / Real.sqrt y) := mul_le_mul_of_nonneg_right hat.le hfac
    have hval : y * (1 + hy / Real.sqrt y) = y + hy * Real.sqrt y := by
      field_simp
      nlinarith [hsq]
    linarith [hkey, hval]
  -- the upper bound for `T`
  have hThigh : T ≤ ((t : ℝ) + 1) + hy * ((t : ℝ) + 1) / Real.sqrt y := by
    rw [hT, div_le_iff₀ ha0]
    have hat : y ≤ (a : ℝ) * ((t : ℝ) + 1) := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < (t:ℝ) + 1)] at halow
      linarith
    have hexp : (((t : ℝ) + 1) + hy * ((t : ℝ) + 1) / Real.sqrt y) * (a : ℝ)
        = ((a : ℝ) * ((t : ℝ) + 1)) * (1 + hy / Real.sqrt y) := by
      field_simp
    rw [hexp]
    have hfac : (0 : ℝ) ≤ 1 + hy / Real.sqrt y := by positivity
    have hkey : y * (1 + hy / Real.sqrt y)
        ≤ ((a : ℝ) * ((t : ℝ) + 1)) * (1 + hy / Real.sqrt y) :=
      mul_le_mul_of_nonneg_right hat hfac
    have hval : y * (1 + hy / Real.sqrt y) = y + hy * Real.sqrt y := by
      field_simp
      nlinarith [hsq]
    linarith [hkey, hval]
  -- transfer to the floor
  have hfl1 : T - 1 < ((⌊T⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one T
    linarith
  have hfl2 : ((⌊T⌋₊ : ℕ) : ℝ) ≤ T :=
    Nat.floor_le (by rw [hT]; positivity)
  have hquot : (0 : ℝ) ≤ hy * (t : ℝ) / Real.sqrt y := by positivity
  have htle : t ≤ ⌊T⌋₊ := by
    have : ((t : ℕ) : ℝ) < ((⌊T⌋₊ : ℕ) : ℝ) + 1 := by linarith [hTlow, hfl1, hquot]
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  have hfin : (fibreLen y hy a : ℝ) = ((⌊T⌋₊ : ℕ) : ℝ) - (t : ℝ) := by
    rw [fibreLen, hstart, hT] at *
    rw [Nat.cast_sub htle]
  constructor
  · rw [hfin]
    linarith [hTlow, hfl1]
  · rw [hfin]
    linarith [hThigh, hfl2]

end RHTower.Sieve
