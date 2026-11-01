import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheMetzlerThresholdOfTheOverlapRatioIsOne
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.StarsAreLowerHorizons

/-!
# The sign gauge on deep stars

Lorentzian theory derives one positive square from three inputs: local signature, a sign
hypothesis (nonnegative or Metzler entries), and connectivity (ALG). For Weil's atomic intersection
Gram the sign hypothesis holds exactly below the atomic spacing: separated atoms meet nonpositively
(`markovPair_atom_nonpos`). The Metzler threshold of the overlap ratio is `1`
(`metzlerThreshold_overlapRatio`).

On the star of `d` the atoms sit at `log d + log a`, `a ≤ ⌊N/d⌋`. Their gaps are the gaps of the
lower horizon, so they are at least `atomSpacing ⌊N/d⌋ ≥ 1/(⌊N/d⌋ + 1)`, about `d/N`. Hence:

* **the sign gauge holds on deep stars** (`markovPair_star_nonpos`, `markovPair_star_nonpos_of_lt`):
  for a nonnegative atom of width `w`, distinct atoms of the star of `d` meet nonpositively as soon
  as `w < atomSpacing ⌊N/d⌋`. At width `c/N` this holds whenever `c(⌊N/d⌋ + 1) < N`, roughly
  `d > c`.
* **the pole rows are nonnegative on every star** (`starPoleRow_nonneg`).

So the Lorentzian sign hypothesis is local in the same way as Hodge–Riemann. It holds on the stars
of depth beyond the overlap, which sink into the separated regime, and fails across the shallow
stars, where the overlap ratio exceeds `1` and ALG proves that no nonnegative gauge exists. Local
signature and local sign are available exactly where local positivity already holds. The
Brändén–Huh mechanism meets the same gluing problem as the Kähler package.
-/

noncomputable section

open Finset
open GaloisForLFunctions.ArithmeticLorentzianGeometry GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.SpacingScaleHarmonicAnalysis

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

variable {g : ℝ → ℝ} {w : ℝ}

/-- Gaps on a star are gaps of the lower horizon. -/
theorem logGap_star {d a b : ℕ} (hd : 0 < d) (ha : 0 < a) (hb : 0 < b) :
    Real.log ((d * b : ℕ) : ℝ) - Real.log ((d * a : ℕ) : ℝ) = Real.log b - Real.log a := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  push_cast
  rw [Real.log_mul hd' hb', Real.log_mul hd' ha']
  ring

/-- **The sign gauge on a star.** Distinct atoms of the star of `d` meet nonpositively when the
atom width is below the spacing of the lower horizon `⌊N/d⌋`. -/
theorem markovPair_star_nonpos (hg0 : ∀ u, 0 ≤ g u) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {d N : ℕ} (hd : 0 < d) {a b : ℕ} (ha : a ∈ Icc 1 (N / d)) (hb : b ∈ Icc 1 (N / d))
    (hab : a ≠ b) (hw : w < atomSpacing (N / d)) :
    markovPair (atom g (d * a)) (atom g (d * b)) ≤ 0 := by
  refine markovPair_atom_nonpos hg0 hgsupp ?_
  have hgap := atomSpacing_le_abs_logGap ha hb hab
  rw [logGap] at hgap
  rw [logGap_star hd (mem_Icc.mp ha).1 (mem_Icc.mp hb).1]
  linarith

/-- **Deep stars carry the sign gauge.** At width `c/N`, distinct atoms of the star of `d` meet
nonpositively whenever `c(⌊N/d⌋ + 1) < N`. -/
theorem markovPair_star_nonpos_of_lt (hg0 : ∀ u, 0 ≤ g u)
    {c : ℝ} (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {d N : ℕ} (hd : 0 < d) (hdN : d ≤ N)
    (hwc : w = c / N) (hc : c * (((N / d : ℕ) : ℝ) + 1) < N) {a b : ℕ} (ha : a ∈ Icc 1 (N / d))
    (hb : b ∈ Icc 1 (N / d)) (hab : a ≠ b) :
    markovPair (atom g (d * a)) (atom g (d * b)) ≤ 0 := by
  refine markovPair_star_nonpos hg0 hgsupp hd ha hb hab ?_
  have hM : 1 ≤ N / d := Nat.div_pos hdN hd
  have hspace := inv_succ_le_atomSpacing hM
  have hN : (0 : ℝ) < N := by exact_mod_cast hd.trans_le hdN
  have hM1 : (0 : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by positivity
  rw [hwc]
  calc c / N < 1 / (((N / d : ℕ) : ℝ) + 1) := by
        rw [div_lt_div_iff₀ hN hM1]; linarith
    _ ≤ atomSpacing (N / d) := hspace

/-- **The pole rows are nonnegative on every star.** -/
theorem starPoleRow_nonneg (hg0 : ∀ u, 0 ≤ g u) (n : ℕ) (s : ℝ) :
    0 ≤ ∫ u, atom g n u * Real.exp (s * u) :=
  MeasureTheory.integral_nonneg fun _ => mul_nonneg (hg0 _) (Real.exp_pos _).le

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
