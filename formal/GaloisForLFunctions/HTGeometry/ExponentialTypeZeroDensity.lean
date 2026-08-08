/-
# Linear zero density for entire functions of finite exponential type

A nonzero entire function satisfying `‖f z‖ ≤ C exp(A‖z‖)` has at most linearly many zeros in
concentric discs.  Jensen's inequality at a nonzero anchor gives an explicit bound and hence a
uniform `K(1+r)` envelope.  This is classical `[BRIDGE]` infrastructure for the no-jet Weil-support
audit: Mellin transforms of compactly supported smooth tests have finite exponential type, whereas
the distinct simple critical-line zeta zeros have order `T log T` density.
-/
import Mathlib.Analysis.Complex.JensenFormula

open Complex Metric

namespace RHTower

/-- A nonzero entire function of finite exponential type has at most linearly many zeros in
concentric discs. -/
theorem exponentialType_zeroCount_le
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} (hfc : f c ≠ 0)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hgrow : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖))
    {r : ℝ} (hr : 1 ≤ r) :
    (↑(∑ᶠ u, (MeromorphicOn.divisor f (closedBall c r)) u) : ℝ) ≤
      (Real.log C + A * (‖c‖ + 2 * r) - Real.log ‖f c‖) / Real.log 2 := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  let R : ℝ := 2 * r
  let M : ℝ := C * Real.exp (A * (‖c‖ + 2 * r))
  have hR0 : 0 < R := by dsimp [R]; linarith
  have hrR : r < R := by dsimp [R]; linarith
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hM1 : 1 ≤ M := by
    dsimp [M]
    have hexp : 1 ≤ Real.exp (A * (‖c‖ + 2 * r)) := by
      rw [Real.one_le_exp_iff]
      positivity
    nlinarith
  have hfan : AnalyticOnNhd ℂ f (closedBall c R) :=
    (hf.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M := by
    intro z hz
    have hzdist : ‖z - c‖ = R := by simpa [mem_sphere_iff_norm] using hz
    have hznorm : ‖z‖ ≤ ‖c‖ + 2 * r := by
      have htri : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        have := norm_add_le (z - c) c
        simpa [sub_add_cancel] using this
      rw [hzdist] at htri
      dsimp [R] at htri
      linarith
    calc
      ‖f z‖ ≤ C * Real.exp (A * ‖z‖) := hgrow z
      _ ≤ C * Real.exp (A * (‖c‖ + 2 * r)) := by
        gcongr
      _ = M := rfl
  have hfanAbs : AnalyticOnNhd ℂ f (closedBall c |R|) := by
    simpa [abs_of_pos hR0] using hfan
  have hsum := hfanAbs.sum_divisor_le
    (r := r) (R := R) (M := M)
    (by simpa [abs_of_pos hr0] using hr0)
    (by simpa [abs_of_pos hr0, abs_of_pos hR0] using hrR)
    hM1 hfc (by simpa [abs_of_pos hR0] using hbound)
  have hnorm0 : 0 < ‖f c‖ := norm_pos_iff.mpr hfc
  have hRr : R / r = 2 := by dsimp [R]; field_simp
  rw [abs_of_pos hr0] at hsum
  dsimp [M] at hsum
  rw [hRr, Real.log_div (by positivity) hnorm0.ne',
    Real.log_mul hC0.ne' (Real.exp_ne_zero _), Real.log_exp] at hsum
  exact hsum

/-- Exponential type gives a uniform linear zero-count envelope. -/
theorem exponentialType_zeroCount_linear
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} (hfc : f c ≠ 0)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hgrow : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖)) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 1 ≤ r →
      (↑(∑ᶠ u, (MeromorphicOn.divisor f (closedBall c r)) u) : ℝ) ≤ K * (1 + r) := by
  let B : ℝ := |Real.log C| + A * (‖c‖ + 2) + |Real.log ‖f c‖| + Real.log 2
  let K : ℝ := B / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨K, div_pos hB hlog2, ?_⟩
  intro r hr
  have hraw := exponentialType_zeroCount_le hf hfc hA hC hgrow hr
  have hnum :
      Real.log C + A * (‖c‖ + 2 * r) - Real.log ‖f c‖ ≤ B * (1 + r) := by
    have hr0 : 0 ≤ r := le_trans zero_le_one hr
    have hlogC : Real.log C ≤ |Real.log C| := le_abs_self _
    have hlogfc : -Real.log ‖f c‖ ≤ |Real.log ‖f c‖| := neg_le_abs _
    have hgeom : ‖c‖ + 2 * r ≤ (‖c‖ + 2) * (1 + r) := by
      nlinarith [norm_nonneg c]
    have hAgeom : A * (‖c‖ + 2 * r) ≤ A * ((‖c‖ + 2) * (1 + r)) :=
      mul_le_mul_of_nonneg_left hgeom hA
    have hconst0 :
        0 ≤ |Real.log C| + |Real.log ‖f c‖| + Real.log 2 := by positivity
    have hconst :
        |Real.log C| + |Real.log ‖f c‖| ≤
          (|Real.log C| + |Real.log ‖f c‖| + Real.log 2) * (1 + r) := by
      nlinarith [abs_nonneg (Real.log C), abs_nonneg (Real.log ‖f c‖), hlog2]
    dsimp [B]
    nlinarith
  calc
    (↑(∑ᶠ u, (MeromorphicOn.divisor f (closedBall c r)) u) : ℝ)
        ≤ (Real.log C + A * (‖c‖ + 2 * r) - Real.log ‖f c‖) / Real.log 2 := hraw
    _ ≤ B * (1 + r) / Real.log 2 := div_le_div_of_nonneg_right hnum hlog2.le
    _ = K * (1 + r) := by dsimp [K]; ring

/-- A finite injective family of zeros in a closed ball contributes at least its cardinality to
the analytic divisor count in that ball. -/
theorem card_le_sum_divisor_of_finite_zeros
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} (hfc : f c ≠ 0)
    {α : Type*} [DecidableEq α] (s : Finset α) (z : α → ℂ)
    (hinj : Set.InjOn z s) {r : ℝ}
    (hball : ∀ i ∈ s, z i ∈ closedBall c r)
    (hzero : ∀ i ∈ s, f (z i) = 0) :
    (s.card : ℤ) ≤ ∑ᶠ u, (MeromorphicOn.divisor f (closedBall c r)) u := by
  let d := MeromorphicOn.divisor f (closedBall c r)
  have hfanUniv : AnalyticOnNhd ℂ f Set.univ :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  have horderC : meromorphicOrderAt f c ≠ ⊤ := by
    rw [(hfanUniv c (Set.mem_univ c)).meromorphicOrderAt_eq]
    rw [(hfanUniv c (Set.mem_univ c)).analyticOrderAt_eq_zero.mpr hfc]
    simp
  have horder : ∀ u : ℂ, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    exact hfanUniv.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ c) (Set.mem_univ u) horderC
  have hfan : AnalyticOnNhd ℂ f (closedBall c r) :=
    hfanUniv.mono (Set.subset_univ _)
  have hsupport : closedBall c r ∩ f ⁻¹' {0} = Function.support d := by
    exact hfan.meromorphicNFOn.zero_set_eq_divisor_support
      (fun u => horder u)
  let Z : Finset ℂ := s.image z
  have hZcard : Z.card = s.card := by
    exact Finset.card_image_iff.mpr hinj
  have hZsupport : (Z : Set ℂ) ⊆ Function.support d := by
    intro u hu
    simp only [Z, Finset.mem_coe, Finset.mem_image] at hu
    obtain ⟨i, hi, rfl⟩ := hu
    rw [← hsupport]
    exact ⟨hball i hi, hzero i hi⟩
  have hdnonneg : ∀ u : ℂ, 0 ≤ d u :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfan
  have hone : ∀ u ∈ Z, (1 : ℤ) ≤ d u := by
    intro u hu
    have hne : d u ≠ 0 := hZsupport hu
    have hnn : 0 ≤ d u := hdnonneg u
    omega
  have hdfin : (Function.support d).Finite :=
    d.finiteSupport (isCompact_closedBall c r)
  let D : Finset ℂ := hdfin.toFinset
  have hZsub : Z ⊆ D := by
    intro u hu
    have hu' : u ∈ Function.support d := hZsupport (by simpa using hu)
    simpa [D] using hu'
  calc
    (s.card : ℤ) = ∑ u ∈ Z, (1 : ℤ) := by simp [hZcard]
    _ ≤ ∑ u ∈ Z, d u := by
      exact Finset.sum_le_sum fun u hu => hone u hu
    _ ≤ ∑ u ∈ D, d u := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hZsub
        (fun u _ _ => hdnonneg u)
    _ = ∑ᶠ u, d u := by
      symm
      apply finsum_eq_sum_of_support_subset
      intro u hu
      simpa [D] using hu

end RHTower
