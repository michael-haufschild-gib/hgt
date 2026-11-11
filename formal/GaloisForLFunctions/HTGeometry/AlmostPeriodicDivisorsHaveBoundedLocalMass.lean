import GaloisForLFunctions.HTGeometry.ImStripAlmostPeriodicZeroDensity

/-!
# Uniform local mass of an almost-periodic zero divisor

Compact translates give a fixed positive value in every short real window.
Jensen's inequality at that value bounds the total zero multiplicity in the
window, uniformly in its position, on every smaller horizontal strip.
-/

open Complex Filter Topology Metric Set

namespace GaloisForLFunctions.HTGeometry

/-- Analytic orders on a finite subset are bounded by the full divisor mass
of the surrounding closed ball. -/
theorem sum_analyticOrderNatAt_le_divisor_mass {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (s : Finset ℂ)
    (hs : ∀ z ∈ s, z ∈ closedBall c R)
    (hfin : ∀ z ∈ s, analyticOrderAt f z ≠ ⊤) :
    (∑ z ∈ s, (analyticOrderNatAt f z : ℝ)) ≤
      ((∑ᶠ z, MeromorphicOn.divisor f (closedBall c R) z : ℤ) : ℝ) := by
  classical
  let D := MeromorphicOn.divisor f (closedBall c R)
  let t := (D.finiteSupport (isCompact_closedBall c R)).toFinset
  have hD : ∀ z ∈ s, D z = (analyticOrderNatAt f z : ℤ) := by
    intro z hz
    rw [show D z = MeromorphicOn.divisor f (closedBall c R) z by rfl,
      MeromorphicOn.AnalyticOnNhd.divisor_apply hf (hs z hz),
      ← Nat.cast_analyticOrderNatAt (hfin z hz)]
    simp
  have hsum : (∑ z ∈ s, (analyticOrderNatAt f z : ℤ)) ≤ ∑ᶠ z, D z := by
    calc
      _ = ∑ z ∈ s, D z := Finset.sum_congr rfl fun z hz => (hD z hz).symm
      _ ≤ ∑ z ∈ s ∪ t, D z := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_union_left)
        (fun z _ _ => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf z)
      _ = ∑ᶠ z, D z := (finsum_eq_sum_of_support_subset _ (by
        intro z hz
        exact Finset.mem_union_right s
          ((D.finiteSupport (isCompact_closedBall c R)).mem_toFinset.mpr hz))).symm
  exact_mod_cast hsum

/-- Every smaller closed strip has a uniform bound on total multiplicity in
real windows of some fixed positive length. -/
theorem HasCompactImStripTranslates.exists_local_divisor_bound
    {f : ℂ → ℂ} {r η a : ℝ} (h : HasCompactImStripTranslates f r)
    (hr0 : 0 < r) (hrη : r < η) (hf : DifferentiableOn ℂ f (imStrip η))
    {z₀ : ℂ} (hz₀ : z₀ ∈ imStrip r) (hfz₀ : f z₀ ≠ 0)
    (ha0 : 0 ≤ a) (har : a < r) :
    ∃ L > 0, ∃ N ≥ 0, ∀ x : ℝ, ∀ s : Finset ℂ,
      (∀ z ∈ s, x ≤ z.re ∧ z.re ≤ x + L ∧ |z.im| ≤ a) →
      (∑ z ∈ s, (analyticOrderNatAt f z : ℝ)) ≤ N := by
  classical
  let L := (r - a) / 4
  let b := (r + a) / 2
  have hL : 0 < L := by dsimp [L]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hbr : b < r := by dsimp [b]; linarith
  have hLab : L + a ≤ b := by dsimp [L, b]; linarith
  obtain ⟨m, hm, hlarge⟩ := h.exists_window_lowerBound hr0 hrη hf hL hz₀ hfz₀
  obtain ⟨B, hB⟩ := h.exists_bound
    (hf.continuousOn.mono (closedImStrip_subset_imStrip hrη))
  let M := max B 1
  have hM : 1 ≤ M := le_max_right _ _
  have hlog : 0 < Real.log (r / b) := Real.log_pos ((one_lt_div hb).mpr hbr)
  have hmM : m ≤ M := by
    obtain ⟨t, _, ht⟩ := hlarge 0
    exact ht.trans ((hB t (by simpa using hr0.le)).trans (le_max_left _ _))
  refine ⟨L, hL, Real.log (M / m) / Real.log (r / b),
    div_nonneg (Real.log_nonneg ((one_le_div hm).mpr hmM)) hlog.le, ?_⟩
  intro x s hs
  obtain ⟨t, ht, htm⟩ := hlarge x
  have hft : f (t : ℂ) ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at htm
    exact (not_le_of_gt hm) htm
  have hballStrip : closedBall (t : ℂ) r ⊆ imStrip η := by
    intro z hz
    have hi := Complex.abs_im_le_norm (z - (t : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hi
    exact (hi.trans (mem_closedBall_iff_norm.mp hz)).trans_lt hrη
  have han : AnalyticOnNhd ℂ f (imStrip η) := hf.analyticOnNhd (isOpen_imStrip η)
  have hsmall : ∀ z ∈ s, z ∈ closedBall (t : ℂ) b := by
    intro z hz
    obtain ⟨hx, hxL, hza⟩ := hs z hz
    rw [mem_closedBall_iff_norm]
    calc
      ‖z - (t : ℂ)‖ ≤ |(z - (t : ℂ)).re| + |(z - (t : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |z.re - t| + |z.im| := by
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
          Complex.ofReal_im, sub_zero]
      _ ≤ L + a := add_le_add (abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩) hza
      _ ≤ b := hLab
  have hfin : ∀ z ∈ s, analyticOrderAt f z ≠ ⊤ := by
    intro z hz htop
    exact hft (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isPreconnected_imStrip η)
      (hballStrip (closedBall_subset_closedBall hbr.le (hsmall z hz)))
      (analyticOrderAt_eq_top.mp htop) (by simp [mem_imStrip, hr0.trans hrη]))
  have hcount := sum_analyticOrderNatAt_le_divisor_mass
    (han.mono (Subset.trans (closedBall_subset_closedBall hbr.le) hballStrip)) s hsmall hfin
  have hanal : AnalyticOnNhd ℂ f (closedBall (t : ℂ) |r|) := by
    simpa only [abs_of_pos hr0] using han.mono hballStrip
  have hjensen := hanal.sum_divisor_le (r := b) (R := r) (M := M)
    (by simpa only [abs_of_pos hb] using hb)
    (by simpa only [abs_of_pos hb, abs_of_pos hr0] using hbr)
    hM hft (by
      intro z hz
      have hi := Complex.abs_im_le_norm (z - (t : ℂ))
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hi
      rw [mem_sphere, abs_of_pos hr0, dist_eq_norm] at hz
      exact (hB z (hi.trans hz.le)).trans (le_max_left _ _))
  rw [abs_of_pos hb] at hjensen
  refine hcount.trans (hjensen.trans ?_)
  apply div_le_div_of_nonneg_right _ hlog.le
  apply Real.log_le_log (div_pos (by linarith) (norm_pos_iff.mpr hft))
  exact div_le_div_of_nonneg_left (by linarith) hm htm

end GaloisForLFunctions.HTGeometry
