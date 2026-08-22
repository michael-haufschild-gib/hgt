import GaloisForLFunctions.RHTower.ConnesCutoffCommutator
import GaloisForLFunctions.RHTower.ConnesFracConvSwap

/-!
# §VII (45)–(46) in the paper's own cut-off convention

§VII (45)-(46) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

`ConnesLogShiftKernel` proved (45) with the cut-off written as `Ψ(ε/x)`, which makes the scaling
substitution exact.  Connes' operator (39) instead cuts off with `ψ(|ε|)`, and (46) is stated with
the *local* supremum `Sup_{|ε| ≤ 1} |η(x+ε)|` rather than a global bound.  Both discrepancies are
removed here, so that (46) can feed the assembly of (42).

Two observations do the work.  First, the *uncut* logarithmic-difference integral already
converges — at `0` because `α < 1`, at `∞` because `α > 0` — so the `Ψ ≡ 1` instance of the
existing scaling identity evaluates it, and any cut-off `0 ≤ ψ ≤ 1` can only decrease it.  Second,
because `ψ` is supported in `[-1,1]` the integrand of (46) is *identically zero* for `|ε| > 1`, so
a bound valid only on `|ε| ≤ 1` suffices.

The last theorem records where the commutator lives: `ε_Λ` and its translate both vanish once
`|x| ≤ Λ − 1`, so the commutator is supported in Connes' thickened tail `X_Λ`.
-/

open MeasureTheory Real Set Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-! ## (45) with the paper's cut-off -/

theorem connes_logShift_integrable_full {x : ℝ} (hx : x ≠ 0) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    Integrable (fun ε : ℝ =>
      abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹) volume := by
  have h := connes_integrable_logShift hx hα0 hα1 (Ψ := fun _ : ℝ => (1 : ℝ))
    continuous_const (fun _ => zero_le_one) (fun _ => le_refl 1)
  exact h.congr (Filter.Eventually.of_forall fun ε => by simp only [one_mul])

theorem connes_logShift_value_full {x : ℝ} (hx : x ≠ 0) (α : ℝ) :
    (∫ ε : ℝ, abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹)
      = (|x| ^ (-α)) * ∫ y : ℝ, connesLogShiftKernel α y := by
  have h := connes_logShift_substitution hx α (fun _ : ℝ => (1 : ℝ))
  simpa using h

/-- **§VII (45), in Connes' cut-off convention.**  With the cut-off written as `ψ(|ε|)` — the form
used by the operator (39) — the logarithmic-difference integral is still at most `c'_α |x|^{-α}`. -/
theorem connes_logShift_bound_abs {x : ℝ} (hx : x ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ t, 0 ≤ ψ t) (hψ1 : ∀ t, ψ t ≤ 1) :
    (∫ ε : ℝ, ψ |ε| * (abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹))
      ≤ (|x| ^ (-α)) * ∫ y : ℝ, connesLogShiftKernel α y := by
  set G : ℝ → ℝ := fun ε => abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹ with hG
  have hGnn : ∀ ε : ℝ, 0 ≤ G ε := by
    intro ε
    rw [hG]
    positivity
  have hGint : Integrable G volume := connes_logShift_integrable_full hx hα0 hα1
  have hψGint : Integrable (fun ε : ℝ => ψ |ε| * G ε) volume := by
    refine MeasureTheory.Integrable.mono' hGint ?_ (Filter.Eventually.of_forall fun ε => ?_)
    · exact ((hψc.comp continuous_abs).aestronglyMeasurable).mul hGint.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hψ0 _) (hGnn ε))]
      calc ψ |ε| * G ε ≤ 1 * G ε := mul_le_mul_of_nonneg_right (hψ1 _) (hGnn ε)
        _ = G ε := one_mul _
  have hmono : (∫ ε : ℝ, ψ |ε| * G ε) ≤ ∫ ε : ℝ, G ε := by
    refine MeasureTheory.integral_mono hψGint hGint fun ε => ?_
    calc ψ |ε| * G ε ≤ 1 * G ε := mul_le_mul_of_nonneg_right (hψ1 _) (hGnn ε)
      _ = G ε := one_mul _
  rw [connes_logShift_value_full hx α] at hmono
  exact hmono

/-! ## (46) with the local supremum -/

/-- **§VII (46).**  The commutator of the fractional kernel with multiplication by the cut-off
excess is bounded pointwise by `c'_α |x|^{-α}` times the supremum of `η` over the *unit*
neighbourhood of `x`.  Only that local bound is needed: `ψ` is supported in `[-1,1]`. -/
theorem connes_cutoff_commutator_local {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ t, 0 ≤ ψ t) (hψ1 : ∀ t, ψ t ≤ 1)
    (hψsupp : ∀ t : ℝ, 1 < t → ψ t = 0)
    (L : ℝ) (η : ℝ → ℂ) {x : ℝ} (hx : x ≠ 0) {M : ℝ}
    (hM : ∀ ε : ℝ, |ε| ≤ 1 → ‖η (x + ε)‖ ≤ M) :
    (∫ ε : ℝ, ‖((connesFracWeight α ψ ε : ℝ) : ℂ) *
        (((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ) * η (x + ε))‖)
      ≤ M * ((|x| ^ (-α)) * ∫ y : ℝ, connesLogShiftKernel α y) := by
  have hM0 : 0 ≤ M := by
    have := hM 0 (by simp)
    exact le_trans (norm_nonneg _) this
  set G : ℝ → ℝ := fun ε => abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹ with hG
  have hGnn : ∀ ε : ℝ, 0 ≤ G ε := by
    intro ε
    rw [hG]
    positivity
  have hGint : Integrable G volume := connes_logShift_integrable_full hx hα0 hα1
  have hψGint : Integrable (fun ε : ℝ => M * (ψ |ε| * G ε)) volume := by
    have hbase : Integrable (fun ε : ℝ => ψ |ε| * G ε) volume := by
      refine MeasureTheory.Integrable.mono' hGint ?_ (Filter.Eventually.of_forall fun ε => ?_)
      · exact ((hψc.comp continuous_abs).aestronglyMeasurable).mul hGint.aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hψ0 _) (hGnn ε))]
        calc ψ |ε| * G ε ≤ 1 * G ε := mul_le_mul_of_nonneg_right (hψ1 _) (hGnn ε)
          _ = G ε := one_mul _
    exact hbase.const_mul M
  have hwrw : ∀ ε : ℝ, connesFracWeight α ψ ε = ψ |ε| * (|ε| ^ (1 + α))⁻¹ := by
    intro ε
    have hrw0 := congrFun (connes_absRpow_neg_eq (α := α) (by linarith : (-1 : ℝ) < α)) ε
    rw [connesFracWeight, hrw0]
  have hptnn : ∀ ε : ℝ, 0 ≤ ‖((connesFracWeight α ψ ε : ℝ) : ℂ) *
      (((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ) * η (x + ε))‖ :=
    fun ε => norm_nonneg _
  have hptbd : ∀ ε : ℝ, ‖((connesFracWeight α ψ ε : ℝ) : ℂ) *
      (((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ) * η (x + ε))‖
      ≤ M * (ψ |ε| * G ε) := by
    intro ε
    have hwnn : 0 ≤ connesFracWeight α ψ ε := by
      rw [hwrw ε]
      have : (0 : ℝ) ≤ (|ε| ^ (1 + α))⁻¹ := by positivity
      exact mul_nonneg (hψ0 _) this
    have hnormw : ‖(((connesFracWeight α ψ ε : ℝ)) : ℂ)‖ = ψ |ε| * (|ε| ^ (1 + α))⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwnn, hwrw ε]
    by_cases hεle : |ε| ≤ 1
    · have hdelta : |connesCutoffExcess L (x + ε) - connesCutoffExcess L x|
          ≤ abs (Real.log |x + ε| - Real.log |x|) := connes_cutoffExcess_diff_le L x (x + ε)
      have hη := hM ε hεle
      have hinv : (0 : ℝ) ≤ (|ε| ^ (1 + α))⁻¹ := by positivity
      rw [norm_mul, norm_mul, hnormw, Complex.norm_real, Real.norm_eq_abs]
      calc ψ |ε| * (|ε| ^ (1 + α))⁻¹ *
            (|connesCutoffExcess L (x + ε) - connesCutoffExcess L x| * ‖η (x + ε)‖)
          ≤ ψ |ε| * (|ε| ^ (1 + α))⁻¹ *
              (abs (Real.log |x + ε| - Real.log |x|) * M) := by
            refine mul_le_mul_of_nonneg_left
              (mul_le_mul hdelta hη (norm_nonneg _) (abs_nonneg _)) ?_
            exact mul_nonneg (hψ0 _) hinv
        _ = M * (ψ |ε| * G ε) := by rw [hG]; ring
    · have hgt : 1 < |ε| := not_le.mp hεle
      have hw0 : connesFracWeight α ψ ε = 0 := connesFracWeight_eq_zero hψsupp hgt
      have hψ0' : ψ |ε| = 0 := hψsupp |ε| hgt
      rw [hw0, hψ0']
      simp
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall hptnn) hψGint (Filter.Eventually.of_forall hptbd)) ?_
  rw [MeasureTheory.integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (connes_logShift_bound_abs hx hα0 hα1 hψc hψ0 hψ1) hM0

/-! ## Where the commutator lives -/

/-- **The commutator is supported in Connes' thickened tail.**  Both `ε_Λ(x+ε)` and `ε_Λ(x)`
vanish once `|x| ≤ Λ − 1` and `|ε| ≤ 1`, with `Λ = e^L`. -/
theorem connes_cutoffExcess_diff_eq_zero {L : ℝ} (hL : 0 ≤ L) {x ε : ℝ}
    (hx : |x| ≤ Real.exp L - 1) (hε : |ε| ≤ 1) :
    connesCutoffExcess L (x + ε) - connesCutoffExcess L x = 0 := by
  have hle : ∀ z : ℝ, |z| ≤ Real.exp L → Real.log |z| ≤ L := by
    intro z hz
    rcases eq_or_ne z 0 with hz0 | hz0
    · subst hz0
      simpa using hL
    · have hpos : (0 : ℝ) < |z| := abs_pos.mpr hz0
      exact (Real.log_le_iff_le_exp hpos).mpr hz
  have h1 : Real.log |x| ≤ L := hle x (by linarith)
  have h2 : Real.log |x + ε| ≤ L := by
    refine hle (x + ε) ?_
    have := abs_add_le x ε
    linarith
  rw [connesCutoffExcess, connesCutoffExcess, max_eq_right (by linarith),
    max_eq_right (by linarith), sub_zero]

end

end GaloisForLFunctions.RHTower
