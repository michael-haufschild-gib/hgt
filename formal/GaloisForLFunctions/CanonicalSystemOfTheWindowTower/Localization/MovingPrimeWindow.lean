import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheTrivialDivisorCouplesOrderedTests

/-!+# Moving prime windows of two restricted sources

Restricting the sources to `[0,w]` and `[L-w,L]` restricts their correlation
to `[L-2w,L]`. Consequently the arithmetic interaction is a finite sum over
integers in `[exp(L-2w), exp L]`, even without regularity assumptions on the
sources. The same support argument removes every prime shift from a diagonal
source whose width is less than `log 2`.

These are the support and arithmetic mechanisms in Section 5 of
arXiv:2611.10726, expressed using the existing ordered correlation.
-/

noncomputable section
open MeasureTheory Set Filter
open RHTower
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

/-- A source restricted to its actual physical interval. -/
def intervalSource (a b : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := (Icc a b).indicator f

/-- Difference intervals control correlation without smoothness or integrability assumptions. -/
theorem crossCorr_intervalSource_eq_zero (a b c d u : ℝ) (f g : ℝ → ℝ)
    (hu : u ∉ Icc (c - b) (d - a)) :
    crossCorr (intervalSource a b f) (intervalSource c d g) u = 0 := by
  unfold crossCorr
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Icc a b
  · have hy : x + u ∉ Icc c d := by
      intro hy
      exact hu ⟨by linarith only [hx.2, hy.1], by linarith only [hx.1, hy.2]⟩
    simp only [intervalSource, indicator_of_notMem hy, mul_zero, Pi.zero_apply]
  · simp only [intervalSource, indicator_of_notMem hx, zero_mul, Pi.zero_apply]

/-- The separated pair has precisely the allowable lag window from the two-interval geometry. -/
theorem crossCorr_twoWindow_eq_zero (L w u : ℝ) (f g : ℝ → ℝ)
    (hu : u ∉ Icc (L - 2 * w) L) :
    crossCorr (intervalSource 0 w f) (intervalSource (L - w) L g) u = 0 := by
  apply crossCorr_intervalSource_eq_zero
  simpa only [sub_zero, show L - w - w = L - 2 * w by ring] using hu

/-- Every nonzero prime interaction lies in the moving multiplicative interval. -/
theorem twoWindow_prime_interaction_support (L w : ℝ) (f g : ℝ → ℝ) (n : ℕ) :
    RHTower.vonMangoldtAtom n *
      crossCorr (intervalSource 0 w f) (intervalSource (L - w) L g) (Real.log n) ≠ 0 →
      2 ≤ n ∧ Real.exp (L - 2 * w) ≤ n ∧ (n : ℝ) ≤ Real.exp L := by
  intro hn
  have hn2 : 2 ≤ n := by
    by_contra h
    exact hn (by rw [vonMangoldtAtom_eq_zero_of_lt_two (by omega), zero_mul])
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlag : Real.log n ∈ Icc (L - 2 * w) L := by
    by_contra h
    exact hn (by rw [crossCorr_twoWindow_eq_zero L w (Real.log n) f g h, mul_zero])
  refine ⟨hn2, ?_, ?_⟩
  · simpa only [Real.exp_log hnpos] using Real.exp_le_exp.mpr hlag.1
  · simpa only [Real.exp_log hnpos] using Real.exp_le_exp.mpr hlag.2

/-- Exact finite arithmetic interaction; no tail or error term remains. -/
theorem twoWindow_prime_interaction_eq_sum (L w : ℝ) (f g : ℝ → ℝ) :
    (∑' n : ℕ, RHTower.vonMangoldtAtom n *
      crossCorr (intervalSource 0 w f) (intervalSource (L - w) L g) (Real.log n)) =
    ∑ n ∈ Finset.Icc ⌈Real.exp (L - 2 * w)⌉₊ ⌊Real.exp L⌋₊,
      RHTower.vonMangoldtAtom n *
        crossCorr (intervalSource 0 w f) (intervalSource (L - w) L g) (Real.log n) := by
  apply tsum_eq_sum
  intro n hn
  by_contra hne
  obtain ⟨_, hlo, hhi⟩ := twoWindow_prime_interaction_support L w f g n hne
  apply hn
  exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo, Nat.le_floor hhi⟩

/-- Diagonal prime shifts vanish below the first prime aperture. -/
theorem diagonal_interval_prime_interaction_eq_zero (a w : ℝ) (f : ℝ → ℝ)
    (hw : w < Real.log 2) :
    (∑' n : ℕ, RHTower.vonMangoldtAtom n *
      crossCorr (intervalSource a (a + w) f) (intervalSource a (a + w) f) (Real.log n)) = 0 := by
  have hterm (n : ℕ) : RHTower.vonMangoldtAtom n *
      crossCorr (intervalSource a (a + w) f) (intervalSource a (a + w) f) (Real.log n) = 0 := by
    by_cases hn : 2 ≤ n
    · have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnreal
      rw [crossCorr_intervalSource_eq_zero]
      · exact mul_zero _
      · intro h
        linarith only [h.2, hw, hlog]
    · rw [vonMangoldtAtom_eq_zero_of_lt_two (by omega), zero_mul]
  simp only [hterm, tsum_zero]

/-- The existing ordered coupling has exactly the finite prime window. -/
theorem orderedCoupling_twoWindow (L w : ℝ) (f g : ℝ → ℝ) :
    orderedCoupling (intervalSource 0 w f) (intervalSource (L - w) L g) =
      (∫ u in Ioi (0 : ℝ), collarKernel u *
        crossCorr (intervalSource 0 w f) (intervalSource (L - w) L g) u) -
      ∑ n ∈ Finset.Icc ⌈Real.exp (L - 2 * w)⌉₊ ⌊Real.exp L⌋₊,
        RHTower.vonMangoldtAtom n *
          crossCorr (intervalSource 0 w f) (intervalSource (L - w) L g) (Real.log n) := by
  rw [orderedCoupling, twoWindow_prime_interaction_eq_sum]

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower

#print axioms GaloisForLFunctions.CanonicalSystemOfTheWindowTower.orderedCoupling_twoWindow
#print axioms GaloisForLFunctions.CanonicalSystemOfTheWindowTower.diagonal_interval_prime_interaction_eq_zero
