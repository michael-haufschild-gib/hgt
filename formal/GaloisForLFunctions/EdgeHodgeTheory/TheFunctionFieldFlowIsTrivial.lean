import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanDefectCountsTheOuterEigenvalues

/-!
# Calibration over `𝔽_q`: the resolution flow of a curve is trivial

For a curve datum the resolution is the length `n` of the window `Γ₀, …, Γ_{n−1}` of Frobenius
graphs, and the form is the Toeplitz span defect `G_{kl} = Re Σᵢ βᵢ^{|k−l|}`
(`ArithmeticCastelnuovoSeveri.CurveDatum.spanGram`). The **window edge** is the first window with
a negative square (`windowEdge`).

* **Positivity holds exactly below the edge** (`hermNegIndex_spanGram_eq_zero_iff_lt_windowEdge`):
  the windows are nested, so the defect is nondecreasing.
* **The edge is infinite iff Weil's bound holds** (`windowEdge_eq_top_iff`).
* **Detection within the genus** (`windowEdge_le_card`, `hermNegIndex_spanGram_stable`): a datum
  violating the bound is seen at a window of length at most `2g`, and the defect is constant from
  window `2g` on. The flow degenerates nowhere: there is no edge window between a universal regime
  and an RH regime.
* **Short windows are always positive** (`two_le_windowEdge`); **the golden datum is seen at the
  first possible window** (`windowEdge_goldenDatum`).

Over `ℤ` the edge of the tilted spline tends to `∞` with the horizon, unconditionally
(`TheEdgeIsAThresholdCurve.edge_bounded_over_curves_and_unbounded_over_integers`): an off-line
zero would be seen only at resolutions that grow without bound.
-/

noncomputable section

open Filter Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.EdgeHodgeTheory

open ArithmeticCastelnuovoSeveri

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- **The window edge** of a curve datum: the first window length at which the Frobenius-span
defect has a negative square. -/
def windowEdge : ℕ∞ := ⨅ (n : ℕ) (_ : hermNegIndex (D.spanGram n) ≠ 0), (n : ℕ∞)

/-- Positivity holds exactly below the window edge. -/
theorem hermNegIndex_spanGram_eq_zero_iff_lt_windowEdge (n : ℕ) :
    hermNegIndex (D.spanGram n) = 0 ↔ (n : ℕ∞) < windowEdge D := by
  constructor
  · intro h0
    by_contra hge
    push Not at hge
    have hlt : windowEdge D < (n + 1 : ℕ) := lt_of_le_of_lt hge (by exact_mod_cast n.lt_succ_self)
    obtain ⟨m, hm⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hm0, hmlt⟩ := iInf_lt_iff.mp hm
    have hmn : m ≤ n := by exact_mod_cast Order.le_of_lt_add_one (by exact_mod_cast hmlt)
    exact hm0 (Nat.eq_zero_of_le_zero (h0 ▸ D.negIndex_spanGram_mono hmn))
  · intro hlt
    by_contra h0
    exact absurd (iInf₂_le n h0) (not_le.mpr hlt)

/-- From window `2g` on the defect is the number of outer eigenvalues. -/
theorem hermNegIndex_spanGram_stable {n : ℕ} (hn : Fintype.card ι ≤ n) :
    hermNegIndex (D.spanGram n) = hermNegIndex (D.spanGram (Fintype.card ι)) := by
  rw [D.pontryagin_law_curve.2 n hn, D.pontryagin_law_curve.2 _ le_rfl]

/-- **The window edge is infinite iff the datum satisfies Weil's bound.** -/
theorem windowEdge_eq_top_iff : windowEdge D = ⊤ ↔ ∀ i, ‖D.β i‖ = 1 := by
  rw [D.unitary_iff_negIndex_spanGram_eq_zero]
  constructor
  · intro h
    have := (hermNegIndex_spanGram_eq_zero_iff_lt_windowEdge D (Fintype.card ι)).mpr
    rw [h] at this
    exact this (ENat.coe_lt_top _)
  · intro h
    simp only [windowEdge, iInf_eq_top, ENat.coe_ne_top, imp_false, not_not]
    intro n
    rcases le_total n (Fintype.card ι) with hn | hn
    · exact Nat.eq_zero_of_le_zero (h ▸ D.negIndex_spanGram_mono hn)
    · rw [hermNegIndex_spanGram_stable D hn, h]

/-- **Detection within the genus.** A datum violating Weil's bound is seen at a window of length
at most `2g`. -/
theorem windowEdge_le_card (h : ¬ ∀ i, ‖D.β i‖ = 1) : windowEdge D ≤ Fintype.card ι := by
  rw [D.unitary_iff_negIndex_spanGram_eq_zero] at h
  exact iInf₂_le (Fintype.card ι) h

theorem hermNegIndex_spanGram_one : hermNegIndex (D.spanGram 1) = 0 := by
  refine negIndex_eq_zero_of_hermQuad_nonneg fun x => ?_
  have h0 : D.trace 0 = Fintype.card ι := by
    simp [CurveDatum.trace, CurveDatum.powerSum]
  simp only [hermQuad, dotProduct, Matrix.mulVec, Fin.sum_univ_one, CurveDatum.spanGram,
    Nat.dist_self, h0]
  have hx : star x 0 * ((((Fintype.card ι : ℕ) : ℝ) : ℂ) * x 0) =
      ((((Fintype.card ι : ℕ) : ℝ) * Complex.normSq (x 0) : ℝ) : ℂ) := by
    rw [Pi.star_apply, Complex.star_def]
    apply Complex.ext <;> simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring
  rw [hx, Complex.ofReal_re]
  positivity

/-- **Short windows are positive**: every datum has window edge at least `2`. -/
theorem two_le_windowEdge : 2 ≤ windowEdge D := by
  refine le_iInf₂ fun n hn => ?_
  by_contra hlt
  push Not at hlt
  have hn1 : n ≤ 1 := by exact_mod_cast Order.le_of_lt_add_one (by simpa using hlt)
  exact hn (Nat.eq_zero_of_le_zero ((hermNegIndex_spanGram_one D) ▸ D.negIndex_spanGram_mono hn1))

/-- **The golden datum is seen at the first possible window.** -/
theorem windowEdge_goldenDatum : windowEdge goldenDatum = 2 :=
  le_antisymm (iInf₂_le 2 (by rw [goldenDatum_negIndex_spanGram le_rfl]; exact one_ne_zero))
    (two_le_windowEdge _)

end GaloisForLFunctions.EdgeHodgeTheory
