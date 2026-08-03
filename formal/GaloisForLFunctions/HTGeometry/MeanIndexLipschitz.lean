import GaloisForLFunctions.HTGeometry.MeanIndexComparison

/-!
# Mean and mode under a Lipschitz central index

The mean-minus-mode gap is controlled by the spread of the central index over a sampling window plus
two logarithmic corrections whose size is inverse in the window width.  If the central index rises at
most linearly on the window — the regularity a growth lemma supplies off an exceptional set — the
two effects are in competition: a wide window makes the spread large, a narrow one makes the
logarithmic corrections large.

Balancing them at width `h` gives

`|Lambda(r) - nu(r)| <= 2 L h + 2 log(nu(r) + 2 L h + 1 + 1/(e^h - 1)) / h`,

which at `h` of order `sqrt(log nu / L)` is of order `sqrt(L log nu)` — square-root small in the
Lipschitz constant, where the crude window bound is linear in it.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

variable {a : ℕ → ℂ}

/-- The ratio correction of a logarithmic step. -/
private theorem exp_ratio_correction {h : ℝ} (hh : 0 < h) (y : ℝ) :
    (Real.exp y / Real.exp (y + h)) / (1 - Real.exp y / Real.exp (y + h))
      = 1 / (Real.exp h - 1) := by
  have hq : Real.exp y / Real.exp (y + h) = Real.exp (-h) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hpos : (0 : ℝ) < Real.exp h := Real.exp_pos h
  have hgt : (1 : ℝ) < Real.exp h := by simpa using Real.exp_lt_exp.mpr hh
  have hne : Real.exp h - 1 ≠ 0 := by linarith
  rw [hq, Real.exp_neg]
  rw [div_eq_div_iff (by
    have : (Real.exp h)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      exact Or.inr hgt
    linarith) hne]
  field_simp

/-- **Mean and mode under a Lipschitz central index.**  Sampling at logarithmic width `h` inside a
window of width `H` on which the central index rises at most linearly, the mean-minus-mode gap is at
most the spread `2 L h` plus two logarithmic corrections of size `log(nu)/h`. -/
theorem abs_meanIndex_sub_centralIndex_le_lipschitz
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H L h v₀ : ℝ} (hL : 0 < L)
    (hh : 0 < h) (hhH : 2 * h ≤ H) (hv₀h : v₀ ≤ h)
    (hlipA : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp (x + v)) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) + L * v)
    (hlipB : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp x) : ℝ) - L * v ≤ (centralIndex a (Real.exp (x - v)) : ℝ)) :
    |meanIndex a (Real.exp x) - (centralIndex a (Real.exp x) : ℝ)|
      ≤ 2 * L * h
        + 2 * Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
              + 1 / (Real.exp h - 1)) / h := by
  have hhH1 : h ≤ H := by linarith
  have hexp : StrictMono Real.exp := Real.exp_strictMono
  have ht : (0 : ℝ) < Real.exp (x - h) := Real.exp_pos _
  have htr : Real.exp (x - h) < Real.exp x := hexp (by linarith)
  have hrs : Real.exp x < Real.exp (x + h) := hexp (by linarith)
  have hss' : Real.exp (x + h) < Real.exp (x + 2 * h) := hexp (by linarith)
  have hbase := abs_meanIndex_sub_centralIndex_le (a := a) ha ht htr hrs hss' hn₀
  -- the two logarithmic step lengths
  have hlog1 : Real.log (Real.exp (x + h) / Real.exp x) = h := by
    rw [← Real.exp_sub, Real.log_exp]; ring
  have hlog2 : Real.log (Real.exp x / Real.exp (x - h)) = h := by
    rw [← Real.exp_sub, Real.log_exp]; ring
  have hcorr1 : (Real.exp (x + h) / Real.exp (x + 2 * h))
      / (1 - Real.exp (x + h) / Real.exp (x + 2 * h)) = 1 / (Real.exp h - 1) := by
    have h2 : x + 2 * h = (x + h) + h := by ring
    rw [h2]
    exact exp_ratio_correction hh (x + h)
  have hcorr2 : (Real.exp (x - h) / Real.exp x) / (1 - Real.exp (x - h) / Real.exp x)
      = 1 / (Real.exp h - 1) := by
    have h2 : Real.exp x = Real.exp (x - h + h) := by rw [show x - h + h = x from by ring]
    rw [h2]
    exact exp_ratio_correction hh (x - h)
  rw [hlog1, hlog2, hcorr1, hcorr2] at hbase
  refine le_trans hbase ?_
  -- the spread
  have hup := hlipA h hv₀h hhH1
  have hdown := hlipB h hv₀h hhH1
  have hspread : (centralIndex a (Real.exp (x + h)) : ℝ)
      - (centralIndex a (Real.exp (x - h)) : ℝ) ≤ 2 * L * h := by
    linarith
  -- the two logarithms
  have hcpos : (0 : ℝ) < Real.exp h - 1 := by
    have : (1 : ℝ) < Real.exp h := by simpa using Real.exp_lt_exp.mpr hh
    linarith
  have hAnn : (0 : ℝ) < (centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
      + 1 / (Real.exp h - 1) := by
    have h1 : (0 : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ 2 * L * h := by positivity
    have h3 : (0 : ℝ) < 1 / (Real.exp h - 1) := by positivity
    linarith
  have hup2 := hlipA (2 * h) (by linarith) hhH
  have hlogA : Real.log (((centralIndex a (Real.exp (x + 2 * h)) : ℝ) + 1)
        + 1 / (Real.exp h - 1))
      ≤ Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
        + 1 / (Real.exp h - 1)) := by
    refine Real.log_le_log ?_ ?_
    · have h1 : (0 : ℝ) ≤ (centralIndex a (Real.exp (x + 2 * h)) : ℝ) := Nat.cast_nonneg _
      have h3 : (0 : ℝ) < 1 / (Real.exp h - 1) := by positivity
      linarith
    · have : (centralIndex a (Real.exp (x + 2 * h)) : ℝ)
          ≤ (centralIndex a (Real.exp x) : ℝ) + L * (2 * h) := hup2
      linarith
  have hlogB : Real.log (((centralIndex a (Real.exp x) : ℝ) + 1) + 1 / (Real.exp h - 1))
      ≤ Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
        + 1 / (Real.exp h - 1)) := by
    refine Real.log_le_log ?_ ?_
    · have h1 : (0 : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) := Nat.cast_nonneg _
      have h3 : (0 : ℝ) < 1 / (Real.exp h - 1) := by positivity
      linarith
    · have : (0 : ℝ) ≤ 2 * L * h := by positivity
      linarith
  have hdiv1 : Real.log (((centralIndex a (Real.exp (x + 2 * h)) : ℝ) + 1)
        + 1 / (Real.exp h - 1)) / h
      ≤ Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
        + 1 / (Real.exp h - 1)) / h :=
    div_le_div_of_nonneg_right hlogA hh.le
  have hdiv2 : Real.log (((centralIndex a (Real.exp x) : ℝ) + 1) + 1 / (Real.exp h - 1)) / h
      ≤ Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
        + 1 / (Real.exp h - 1)) / h :=
    div_le_div_of_nonneg_right hlogB hh.le
  have hdouble : 2 * Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
        + 1 / (Real.exp h - 1)) / h
      = Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
          + 1 / (Real.exp h - 1)) / h
        + Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
            + 1 / (Real.exp h - 1)) / h := by
    ring
  linarith

end GaloisForLFunctions.HTGeometry
