import GaloisForLFunctions.HTGeometry.ReflectedDividedDifference
import Mathlib.Analysis.Complex.Schwarz

/-!
# Closed anchored Schur second-jet bound

Sharp second-order Schwarz--Pick control for an anchored holomorphic disk map, including the
extremal first-derivative case. This analytic module is intentionally independent of Suzuki,
Xi-target, and prime--Gamma source infrastructure.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

private theorem diskMobius_normSq_sub
    (a w : ℂ) :
    Complex.normSq (1 - (starRingEnd ℂ) a * w) -
        Complex.normSq (w - a) =
      (1 - Complex.normSq a) * (1 - Complex.normSq w) := by
  rw [Complex.normSq_sub, Complex.normSq_sub, Complex.normSq_mul,
    Complex.normSq_conj]
  simp only [one_mul, Complex.normSq_eq_norm_sq]
  have hre : (((starRingEnd ℂ) ((starRingEnd ℂ) a * w)).re) =
      (((starRingEnd ℂ) a * w).re) := by
    simpa only [map_mul, star_star] using
      Complex.conj_re ((starRingEnd ℂ) a * w)
  rw [hre, norm_one]
  ring

private theorem diskMobius_norm_le_one
    {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) :
    ‖(w - a) / (1 - (starRingEnd ℂ) a * w)‖ ≤ 1 := by
  have hprod : ‖(starRingEnd ℂ) a * w‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc
      ‖a‖ * ‖w‖ ≤ ‖a‖ * 1 :=
        mul_le_mul_of_nonneg_left hw (norm_nonneg a)
      _ < 1 * 1 := by simpa using ha
      _ = 1 := one_mul 1
  have hden : 1 - (starRingEnd ℂ) a * w ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    have : ‖(starRingEnd ℂ) a * w‖ = 1 := by
      rw [← heq, norm_one]
    linarith
  have haSq : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hwSq : Complex.normSq w ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  have hSq : Complex.normSq (w - a) ≤
      Complex.normSq (1 - (starRingEnd ℂ) a * w) := by
    have hid := diskMobius_normSq_sub a w
    have hnonneg : 0 ≤
        (1 - Complex.normSq a) * (1 - Complex.normSq w) :=
      mul_nonneg (le_of_lt (sub_pos.mpr haSq)) (sub_nonneg.mpr hwSq)
    linarith
  rw [norm_div, div_le_one (norm_pos_iff.mpr hden)]
  rw [← (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _))]
  simpa only [← Complex.normSq_eq_norm_sq] using hSq

/-- **Anchored Schur second-jet bound.**  This is the order-two Schwarz--Pick constraint at the
origin, proved here in the exact normalization used by Suzuki's disk carrier. -/
theorem norm_iteratedDeriv_two_le_schurSlack
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf0 : f 0 = 0)
    (hmap : MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 1))
    (ha : ‖deriv f 0‖ < 1) :
    ‖iteratedDeriv 2 f 0‖ ≤ 2 * (1 - ‖deriv f 0‖ ^ 2) := by
  let g : ℂ → ℂ := dslope f 0
  let a : ℂ := deriv f 0
  let h : ℂ → ℂ :=
    fun z => (g z - a) / (1 - (starRingEnd ℂ) a * g z)
  have hball : Metric.ball (0 : ℂ) (1 : ℝ) ∈ nhds 0 :=
    Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1)
  have hg : DifferentiableOn ℂ g (Metric.ball 0 1) := by
    exact (differentiableOn_dslope hball).mpr hf
  have hgw : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖g z‖ ≤ 1 := by
    intro z hz
    have hm : MapsTo f (Metric.ball (0 : ℂ) 1)
        (Metric.closedBall (f 0) 1) := by
      simpa only [hf0] using hmap
    have hs := Complex.norm_dslope_le_div_of_mapsTo_ball hf hm hz
    norm_num [g] at hs ⊢
    exact hs
  have hden : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      1 - (starRingEnd ℂ) a * g z ≠ 0 := by
    intro z hz
    rw [sub_ne_zero]
    intro heq
    have hprod : ‖(starRingEnd ℂ) a * g z‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      calc
        ‖a‖ * ‖g z‖ ≤ ‖a‖ * 1 :=
          mul_le_mul_of_nonneg_left (hgw z hz) (norm_nonneg a)
        _ < 1 * 1 := by simpa only [a, mul_one, one_mul] using ha
        _ = 1 := one_mul 1
    have : ‖(starRingEnd ℂ) a * g z‖ = 1 := by
      rw [← heq, norm_one]
    linarith
  have hh : DifferentiableOn ℂ h (Metric.ball 0 1) := by
    intro z hz
    exact ((hg z hz).sub_const a).div
      ((differentiableWithinAt_const (c := (1 : ℂ))).sub
        ((hg z hz).const_mul ((starRingEnd ℂ) a)))
      (hden z hz)
  have hmaph : MapsTo h (Metric.ball (0 : ℂ) 1)
      (Metric.closedBall (h 0) 1) := by
    intro z hz
    have hg0 : g 0 = a := by
      simp only [g, a, dslope_same]
    have hh0 : h 0 = 0 := by
      simp only [h, hg0, sub_self, zero_div]
    rw [hh0, mem_closedBall_zero_iff]
    exact diskMobius_norm_le_one ha (hgw z hz)
  have hdh :=
    Complex.norm_deriv_le_one_of_mapsTo_ball hh hmaph (by norm_num)
  have hg0 : g 0 = a := by
    simp only [g, a, dslope_same]
  have haSq : 1 - Complex.normSq a ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hgd : HasDerivAt g (iteratedDeriv 2 f 0 / 2) 0 := by
    have hfa : AnalyticAt ℂ f 0 := hf.analyticAt hball
    have hs :=
      HTGeometry.iteratedDeriv_dslope_self_eq_iteratedDeriv_succ_div hfa 1
    have hderiv : deriv g 0 = iteratedDeriv 2 f 0 / 2 := by
      simpa only [one_add_one_eq_two, Nat.cast_one, iteratedDeriv_one, g] using hs
    rw [← hderiv]
    exact (hg.differentiableAt hball).hasDerivAt
  have hhd : HasDerivAt h
      ((iteratedDeriv 2 f 0 / 2) / (1 - Complex.normSq a)) 0 := by
    have hnum := hgd.sub_const a
    have hden' := (hasDerivAt_const (x := (0 : ℂ)) (1 : ℂ)).sub
      (hgd.const_mul ((starRingEnd ℂ) a))
    have hq := hnum.div hden' (by
      change 1 - (starRingEnd ℂ) a * g 0 ≠ 0
      rw [hg0, ← Complex.normSq_eq_conj_mul_self]
      exact_mod_cast haSq)
    simp only [Pi.sub_apply, hg0, sub_self, zero_mul, sub_zero,
      ← Complex.normSq_eq_conj_mul_self] at hq
    change HasDerivAt h
      (iteratedDeriv 2 f 0 / 2 * (1 - (Complex.normSq a : ℂ)) /
        (1 - (Complex.normSq a : ℂ)) ^ 2) 0 at hq
    have hcoeff :
        iteratedDeriv 2 f 0 / 2 * (1 - (Complex.normSq a : ℂ)) /
            (1 - (Complex.normSq a : ℂ)) ^ 2 =
          (iteratedDeriv 2 f 0 / 2) / (1 - Complex.normSq a) := by
      have hcast : (1 - (Complex.normSq a : ℂ)) ≠ 0 := by
        exact_mod_cast haSq
      field_simp [hcast]
    rw [hcoeff] at hq
    exact hq
  have hnorm :
      ‖(iteratedDeriv 2 f 0 / 2) / (1 - Complex.normSq a)‖ ≤ 1 := by
    simpa only [hhd.deriv] using hdh
  rw [norm_div, norm_div] at hnorm
  have hpos : 0 < 1 - Complex.normSq a := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hdennorm :
      ‖(1 - (Complex.normSq a : ℂ))‖ = 1 - Complex.normSq a := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpos]
  rw [hdennorm] at hnorm
  rw [Complex.normSq_eq_norm_sq] at hnorm hpos
  simp only [a] at hnorm hpos
  norm_num at hnorm
  have hhalf :
      ‖iteratedDeriv 2 f 0‖ / 2 ≤ 1 - ‖deriv f 0‖ ^ 2 :=
    (div_le_one hpos).mp hnorm
  nlinarith

/-- Closed anchored Schur second-jet bound, including the extremal first-jet case.  At equality in
Schwarz's derivative bound the map is affine on the disk, so its second jet vanishes exactly. -/
theorem norm_iteratedDeriv_two_le_schurSlack_closed
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf0 : f 0 = 0)
    (hmap : MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 1)) :
    ‖iteratedDeriv 2 f 0‖ ≤ 2 * (1 - ‖deriv f 0‖ ^ 2) := by
  have hmap' : MapsTo f (Metric.ball (0 : ℂ) 1)
      (Metric.closedBall (f 0) 1) := by
    simpa only [hf0] using hmap
  have hfirstLe : ‖deriv f 0‖ ≤ 1 :=
    Complex.norm_deriv_le_one_of_mapsTo_ball hf hmap' (by norm_num)
  by_cases hstrict : ‖deriv f 0‖ < 1
  · exact norm_iteratedDeriv_two_le_schurSlack hf hf0 hmap hstrict
  · have hfirstEq : ‖deriv f 0‖ = 1 := le_antisymm hfirstLe (not_lt.mp hstrict)
    have haffine := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
      hf hmap' (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)) (by
        simp only [dslope_same, hfirstEq]
        norm_num)
    have heq : f =ᶠ[nhds 0]
        fun z : ℂ => f 0 + (z - 0) • deriv f 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
      simpa only [dslope_same] using haffine hz
    have hlinear : iteratedDeriv 2
        (fun z : ℂ => f 0 + (z - 0) • deriv f 0) 0 = 0 := by
      have hderiv : deriv (fun z : ℂ => f 0 + (z - 0) • deriv f 0) =
          fun _ => deriv f 0 := by
        funext z
        have hconst : HasDerivAt (fun _ : ℂ => f 0) 0 z := hasDerivAt_const z _
        have hlin : HasDerivAt (fun w : ℂ => (w - 0) • deriv f 0) (deriv f 0) z := by
          simpa [smul_eq_mul] using
            ((hasDerivAt_id z).sub_const 0).mul_const (deriv f 0)
        simpa [smul_eq_mul] using (hconst.add hlin).deriv
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_one, hderiv]
      simp
    rw [heq.iteratedDeriv_eq 2, hlinear, norm_zero, hfirstEq]
    norm_num

end
end RHTower
