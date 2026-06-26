import GaloisForLFunctions.Bottcher.FigureEight
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting

open Complex Set Metric

namespace Bottcher

/-- **Surjectivity onto a deep value annulus.** For `‖w‖` large, `φ_c(z) = w` has a solution with
`‖z‖ > ‖w‖/2`. Banach fixed point: `φ_c(z)=w ⟺ z = w·exp(−S(z))` (`S = bottcherLogSum`,
`φ_c = z·exp S`), and `T(z)=w·exp(−S(z))` contracts the ball `closedBall w (‖w‖/2)` once `‖w‖²` beats
the `‖c‖`-scaled constants. So `φ_c` maps the far field ONTO a deep annulus `{|w|>R'}`, which is
rotation-invariant — the domain on which the deck map `g = ψ(ζ·φ_c)` is well-defined. -/
theorem exists_far_preimage {c w : ℂ}
    (hw : 768 * ‖c‖ + 64 < ‖w‖ ^ 2) (hw2 : 8 * max 2 ‖c‖ < ‖w‖) :
    ∃ z, ‖w‖ / 2 ≤ ‖z‖ ∧ bottcherCoord c z = w := by
  classical
  have hcnn : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  have hwpos : 0 < ‖w‖ := by nlinarith [le_max_left 2 ‖c‖]
  set S : ℂ → ℂ := fun z => ∑' k, bottcherLogTerm c z k with hSdef
  set r : ℝ := ‖w‖ / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  set D : Set ℂ := closedBall w r with hDdef
  set T : ℂ → ℂ := fun z => w * Complex.exp (-(S z)) with hTdef
  -- on D, |z| ≥ r and z ∈ escapeOpen with the bounds applicable
  have hzr : ∀ z ∈ D, r ≤ ‖z‖ := by
    intro z hz
    rw [hDdef, mem_closedBall, dist_eq_norm] at hz
    have h1 := norm_sub_norm_le w z
    rw [norm_sub_rev] at h1
    rw [hrdef] at hz ⊢; linarith
  have hzbig : ∀ z ∈ D, 2 * max 2 ‖c‖ < ‖z‖ := by
    intro z hz
    have := hzr z hz
    rw [hrdef] at this
    have hmaxlt : 2 * max 2 ‖c‖ < ‖w‖ / 2 := by nlinarith [hw2, le_max_left 2 ‖c‖]
    linarith
  have hzesc : ∀ z ∈ D, z ∈ escapeOpen c := by
    intro z hz
    have h := hzbig z hz
    show max 2 ‖c‖ < ‖z‖
    nlinarith [le_max_left 2 ‖c‖, hzr z hz, hrpos]
  -- S bound on D
  have hSbd : ∀ z ∈ D, ‖S z‖ ≤ 2 * ‖c‖ / r ^ 2 := by
    intro z hz
    obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime (hzesc z hz)
    have hb := norm_bottcherLog_sub_log_le hc hz2
    have heq : S z = bottcherLog c z - Complex.log z := by rw [hSdef]; unfold bottcherLog; ring
    rw [heq]
    refine le_trans hb ?_
    gcongr
    exact hzr z hz
  -- S' bound on D
  have hS'bd : ∀ z ∈ D, ‖deriv S z‖ ≤ 16 * ‖c‖ / r ^ 3 := by
    intro z hz
    have hb := norm_deriv_bottcherLogSum_le (hzbig z hz)
    refine le_trans hb ?_
    gcongr
    exact hzr z hz
  -- T maps D into D
  have hSmall : 2 * ‖c‖ / r ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; rw [hrdef]; nlinarith
  have hMapsTo : MapsTo T D D := by
    intro z hz
    rw [hDdef, mem_closedBall, dist_eq_norm]
    have : ‖T z - w‖ = ‖w‖ * ‖Complex.exp (-(S z)) - 1‖ := by
      rw [hTdef]; simp only; rw [show w * Complex.exp (-(S z)) - w = w * (Complex.exp (-(S z)) - 1) by ring, norm_mul]
    rw [this]
    have hexp : ‖Complex.exp (-(S z)) - 1‖ ≤ 2 * ‖S z‖ := by
      have := norm_exp_sub_one_le (x := -(S z)) (by rw [norm_neg]; exact le_trans (hSbd z hz) hSmall)
      rwa [norm_neg] at this
    have hchain : ‖w‖ * ‖Complex.exp (-(S z)) - 1‖ ≤ ‖w‖ * (2 * (2 * ‖c‖ / r ^ 2)) := by
      apply mul_le_mul_of_nonneg_left (le_trans hexp ?_) hwpos.le
      linarith [hSbd z hz]
    refine le_trans hchain ?_
    rw [hrdef]
    rw [div_le_iff₀ (by positivity)] at *
    have : ‖w‖ * (2 * (2 * ‖c‖ / (‖w‖ / 2) ^ 2)) = 16 * ‖c‖ / ‖w‖ := by
      field_simp; ring
    rw [this, div_le_iff₀ hwpos]
    nlinarith [hw]
  -- derivative of T and contraction
  have hTderiv : ∀ z ∈ D, HasDerivAt T (w * (Complex.exp (-(S z)) * (-(deriv S z)))) z := by
    intro z hz
    have hSd : HasDerivAt S (deriv S z) z :=
      ((differentiableOn_bottcherLogSum c).differentiableAt
        ((isOpen_escapeOpen c).mem_nhds (hzesc z hz))).hasDerivAt
    have h1 : HasDerivAt (fun z => Complex.exp (-(S z)))
        (Complex.exp (-(S z)) * (-(deriv S z))) z := (hSd.neg).cexp
    exact h1.const_mul w
  set C : ℝ := 384 * ‖c‖ / ‖w‖ ^ 2 with hCdef
  have hClt1 : C < 1 := by rw [hCdef, div_lt_one (by positivity)]; nlinarith [hw, hcnn]
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  have hbound : ∀ z ∈ D, ‖w * (Complex.exp (-(S z)) * (-(deriv S z)))‖ ≤ C := by
    intro z hz
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_exp]
    have hSnorm : ‖S z‖ ≤ 1 := le_trans (hSbd z hz) hSmall
    have he : Real.exp ((-(S z)).re) ≤ 3 := by
      have h1 : (-(S z)).re ≤ 1 := by
        have h2 := abs_le.mp (Complex.abs_re_le_norm (S z))
        simp only [Complex.neg_re]
        nlinarith [hSnorm, h2.1]
      calc Real.exp ((-(S z)).re) ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
        _ ≤ 3 := Real.exp_one_lt_three.le
    have hsd := hS'bd z hz
    have hkey : ‖w‖ * (Real.exp ((-(S z)).re) * ‖deriv S z‖) ≤ ‖w‖ * (3 * (16 * ‖c‖ / r ^ 3)) := by
      apply mul_le_mul_of_nonneg_left _ hwpos.le
      apply mul_le_mul he hsd (norm_nonneg _) (by norm_num)
    refine le_trans hkey (le_of_eq ?_)
    rw [hCdef, hrdef]; field_simp; ring
  set K : NNReal := ⟨C, hCnn⟩ with hKdef
  have hLip : LipschitzOnWith K T D := by
    apply (convex_closedBall w r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun z hz => (hTderiv z hz).hasDerivWithinAt)
    intro z hz
    rw [← NNReal.coe_le_coe, coe_nnnorm, hKdef]
    exact hbound z hz
  -- Banach fixed point
  have hDcomplete : IsComplete D := (isClosed_closedBall).isComplete
  have hwD : w ∈ D := by rw [hDdef, mem_closedBall, dist_self]; exact hrpos.le
  have hContr : ContractingWith K (hMapsTo.restrict T D D) := by
    refine ⟨hKdef ▸ hClt1, ?_⟩
    rw [lipschitzWith_iff_dist_le_mul]
    intro a b
    have := hLip.dist_le_mul a.val a.2 b.val b.2
    simpa [MapsTo.restrict, Subtype.dist_eq] using this
  obtain ⟨z, hzD, hzfix, -, -⟩ := hContr.exists_fixedPoint' hDcomplete hMapsTo hwD
    (by simp [edist_ne_top])
  refine ⟨z, ?_, ?_⟩
  · have := hzr z hzD; rwa [hrdef] at this
  · have hfix : w * Complex.exp (-(∑' k, bottcherLogTerm c z k)) = z := hzfix
    have hzne : z ≠ 0 := by
      have := hzr z hzD; rw [hrdef] at this
      intro h; rw [h, norm_zero] at this; linarith
    rw [bottcherCoord_eq_mul_exp hzne]
    calc z * Complex.exp (∑' k, bottcherLogTerm c z k)
        = (w * Complex.exp (-(∑' k, bottcherLogTerm c z k)))
            * Complex.exp (∑' k, bottcherLogTerm c z k) := by rw [hfix]
      _ = w := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

end Bottcher
