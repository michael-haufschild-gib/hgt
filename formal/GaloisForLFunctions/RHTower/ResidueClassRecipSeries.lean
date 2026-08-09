import GaloisForLFunctions.RHTower.DigammaDifferenceSeries
import GaloisForLFunctions.RHTower.DigammaQuarter

/-!
# Reciprocal sums over an arithmetic progression

`DigammaDifferenceSeries.hasSum_digamma_sub` gives `ψ(b) − ψ(a) = ∑ₙ (1/(a+n) − 1/(b+n))`.  Taking
`a = j/q`, `b = (j+1)/q` and dividing by `q` turns it into a closed form for the sum of `1/(m(m+1))` over an
arithmetic progression:

**`hasSum_residueClass_recip` — `∑_{k≥0} 1/((qk+j)(qk+j+1)) = (ψ((j+1)/q) − ψ(j/q))/q`  (`q, j ≥ 1`).**

Two instances, from mathlib's `digamma_one`, `digamma_one_half` and the corpus's `digamma_quarter`
(`ψ(1/4) = −γ − π/2 − 3log 2`):

* `hasSum_odd_recip` — `∑_{k≥0} 1/((2k+1)(2k+2)) = log 2`.  This re-derives `hasSum_mod_div_mul_succ` at
  `m = 2` by a different route — digamma rather than the Mellin pairing — so two independent computations of
  the same constant agree.
* **`hasSum_quarter_recip_one` — `∑_{k≥0} 1/((4k+1)(4k+2)) = (log 2 + π/2)/4`.**

The second is the first value in this development that needs `π`, and it is the ingredient the `q = 4`
Báez-Duarte Gram entries were missing.  Assembling those entries additionally needs the decomposition of `ℕ`
into residue classes as a `HasSum`, which is not done here.
-/

open Complex

noncomputable section

namespace RHTower

/-- **Reciprocal sums over an arithmetic progression, in closed form.** -/
theorem hasSum_residueClass_recip {q j : ℕ} (hq : 1 ≤ q) (hj : 1 ≤ j) :
    HasSum (fun k : ℕ => 1 / ((((q * k + j : ℕ)) : ℂ) * (((q * k + j + 1 : ℕ)) : ℂ)))
      ((Complex.digamma (((j : ℂ) + 1) / (q : ℂ)) - Complex.digamma ((j : ℂ) / (q : ℂ)))
        / (q : ℂ)) := by
  have hqne : ((q : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqre : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hjre : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have ha : 0 < (((j : ℂ) / (q : ℂ))).re := by
    rw [show ((j : ℂ) / (q : ℂ)) = (((j : ℝ) / (q : ℝ) : ℝ) : ℂ) from by push_cast; ring,
      Complex.ofReal_re]
    positivity
  have hb : 0 < ((((j : ℂ) + 1) / (q : ℂ))).re := by
    rw [show (((j : ℂ) + 1) / (q : ℂ)) = ((((j : ℝ) + 1) / (q : ℝ) : ℝ) : ℂ) from by
      push_cast; ring, Complex.ofReal_re]
    positivity
  have hbase := (hasSum_digamma_sub ha hb).div_const ((q : ℕ) : ℂ)
  refine hbase.congr_fun ?_
  intro k
  have h1 : (((q * k + j : ℕ)) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : (((q * k + j + 1 : ℕ)) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc1 : (((q * k + j : ℕ)) : ℂ) = (q : ℂ) * (k : ℂ) + (j : ℂ) := by push_cast; ring
  have hc2 : (((q * k + j + 1 : ℕ)) : ℂ) = (q : ℂ) * (k : ℂ) + (j : ℂ) + 1 := by push_cast; ring
  rw [hc1] at h1
  rw [hc2] at h2
  have eA : (j : ℂ) / (q : ℂ) + (k : ℂ) = ((q : ℂ) * (k : ℂ) + (j : ℂ)) / (q : ℂ) := by
    field_simp
    ring
  have eB : ((j : ℂ) + 1) / (q : ℂ) + (k : ℂ)
      = ((q : ℂ) * (k : ℂ) + (j : ℂ) + 1) / (q : ℂ) := by
    field_simp
    ring
  rw [hc1, hc2, eA, eB, one_div_div, one_div_div]
  field_simp
  ring

/-- `∑_{k≥0} 1/((2k+1)(2k+2)) = log 2`, from `ψ(1) − ψ(1/2) = 2 log 2`. -/
theorem hasSum_odd_recip :
    HasSum (fun k : ℕ => 1 / ((((2 * k + 1 : ℕ)) : ℂ) * (((2 * k + 1 + 1 : ℕ)) : ℂ)))
      ((Real.log 2 : ℂ)) := by
  have h := hasSum_residueClass_recip (q := 2) (j := 1) (by norm_num) (by norm_num)
  have harg1 : (((1 : ℕ) : ℂ) + 1) / ((2 : ℕ) : ℂ) = 1 := by norm_num
  have harg2 : (((1 : ℕ) : ℂ)) / ((2 : ℕ) : ℂ) = 1 / 2 := by norm_num
  rw [harg1, harg2, Complex.digamma_one, Complex.digamma_one_half] at h
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num]
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog] at h
  convert h using 1
  push_cast
  ring

/-- **`∑_{k≥0} 1/((4k+1)(4k+2)) = (log 2 + π/2)/4`**, from `ψ(1/2) − ψ(1/4) = log 2 + π/2`. -/
theorem hasSum_quarter_recip_one :
    HasSum (fun k : ℕ => 1 / ((((4 * k + 1 : ℕ)) : ℂ) * (((4 * k + 1 + 1 : ℕ)) : ℂ)))
      ((((Real.log 2 + Real.pi / 2) / 4 : ℝ)) : ℂ) := by
  have h := hasSum_residueClass_recip (q := 4) (j := 1) (by norm_num) (by norm_num)
  have harg1 : (((1 : ℕ) : ℂ) + 1) / ((4 : ℕ) : ℂ) = 1 / 2 := by norm_num
  have harg2 : (((1 : ℕ) : ℂ)) / ((4 : ℕ) : ℂ) = 1 / 4 := by norm_num
  rw [harg1, harg2, Complex.digamma_one_half,
    GaloisForLFunctions.RHTower.digamma_quarter] at h
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num]
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog] at h
  convert h using 1
  push_cast
  ring

end RHTower

end
