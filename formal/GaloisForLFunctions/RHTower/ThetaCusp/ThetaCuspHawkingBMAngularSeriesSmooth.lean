import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMAngularSeriesBounds

/-!
# Joint smoothness of the literal angular Fourier--Bessel family

Both real coordinate derivatives close on the same infinite family. Local
summable bounds certify the actual Frechet derivative of the sum. Induction
on the derivative order then gives joint smoothness without assuming it.
-/

open Complex Real Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMAngularSeries
noncomputable section

/-- The full positive-height coordinate domain. -/
def domain : Set (Fin 2 → ℝ) := {z | 0 < z 1}

private theorem domain_open : IsOpen domain :=
  isOpen_lt continuous_const (continuous_apply 1)

/-- Horizontal rate after removing the Fourier index. -/
def horizontalRate (negative : Bool) : ℂ :=
  (d4BMFourierSign negative : ℂ) * (2 * Real.pi : ℂ) * Complex.I

private abbrev coord (i : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i

/-- A coordinate gradient as an actual continuous real-linear map. -/
def gradient (X Y : ℂ) : (Fin 2 → ℝ) →L[ℝ] ℂ :=
  (coord 0).smulRight X + (coord 1).smulRight Y

/-- Exact differentiated-family expression for one summand. -/
def termGradient (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (N : ℕ) (z : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] ℂ :=
  gradient (horizontalRate negative * term u nu a (d + 1) negative N z)
    ((a : ℂ) * term u nu (a - 1) d negative N z -
      (Real.pi : ℂ) * (term u (nu + 1) a (d + 1) negative N z +
        term u (nu - 1) a (d + 1) negative N z))

private theorem phase_hasDerivAt (negative : Bool) (N : ℕ) (x : ℝ) :
    HasDerivAt (d4BMCompletedEisensteinFourierPhase negative N)
      (horizontalRate negative * ((N + 1 : ℕ) : ℂ) *
        d4BMCompletedEisensteinFourierPhase negative N x) x := by
  let r : ℝ := d4BMFourierSign negative * (2 * Real.pi * ((N : ℝ) + 1))
  have h := (((hasDerivAt_id x).const_mul r).ofReal_comp.mul_const Complex.I).cexp
  convert! h using 1
  · funext y
    dsimp [d4BMCompletedEisensteinFourierPhase, r]
    congr 1
    push_cast
    ring_nf
  · dsimp [horizontalRate, d4BMCompletedEisensteinFourierPhase, r]
    push_cast
    ring_nf

/-- The summand's true joint derivative is the coordinate derivative family. -/
theorem term_hasFDerivAt (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (N : ℕ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    HasFDerivAt (term u nu a d negative N) (termGradient u nu a d negative N z) z := by
  have hp := (phase_hasDerivAt negative N (z 0)).hasFDerivAt.comp z ((coord 0).hasFDerivAt)
  have hy := ((Real.hasDerivAt_rpow_const (p := a) (Or.inl hz.ne')).ofReal_comp).hasFDerivAt.comp z
    ((coord 1).hasFDerivAt)
  have hK := (d4BM_hasDerivAt_modifiedBesselKOrder_argument
    (by positivity : 0 < 2 * Real.pi * ((N : ℝ) + 1) * z 1) nu).scomp (z 1)
      ((hasDerivAt_id (z 1)).const_mul (2 * Real.pi * ((N : ℝ) + 1)))
  have hK' := hK.hasFDerivAt.comp z ((coord 1).hasFDerivAt)
  convert! ((hp.mul hy).mul hK').const_mul (coefficient u d N) using 1
  · funext w
    dsimp [term]
    ring
  · ext v
    simp [termGradient, gradient, term, coefficient, horizontalRate, pow_succ,
      smul_eq_mul, Complex.real_smul]
    ring

private theorem gradient_norm_le (X Y : ℂ) :
    ‖gradient X Y‖ ≤ ‖coord 0‖ * ‖X‖ + ‖coord 1‖ * ‖Y‖ := by
  calc
    _ ≤ ‖(coord 0).smulRight X‖ + ‖(coord 1).smulRight Y‖ := norm_add_le _ _
    _ = _ := by rw [ContinuousLinearMap.norm_smulRight_apply,
      ContinuousLinearMap.norm_smulRight_apply]

/-- A common locally summable bound for the full derivative, including both coordinates. -/
theorem termGradient_local_majorant (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (l h : ℝ) (hl : 0 < l) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ N z, l ≤ z 1 → z 1 ≤ h →
      ‖termGradient u nu a d negative N z‖ ≤ M N := by
  obtain ⟨Mx, hx, bx⟩ := term_local_majorant u nu a (d + 1) negative l h hl
  obtain ⟨Ma, ha, ba⟩ := term_local_majorant u nu (a - 1) d negative l h hl
  obtain ⟨Mp, hp, bp⟩ := term_local_majorant u (nu + 1) a (d + 1) negative l h hl
  obtain ⟨Mm, hm, bm⟩ := term_local_majorant u (nu - 1) a (d + 1) negative l h hl
  refine ⟨fun N => ‖coord 0‖ * (‖horizontalRate negative‖ * Mx N) +
    ‖coord 1‖ * (‖(a : ℂ)‖ * Ma N + ‖(Real.pi : ℂ)‖ * (Mp N + Mm N)),
    ((hx.mul_left _).mul_left _).add
      (((ha.mul_left _).add ((hp.add hm).mul_left _)).mul_left _), ?_⟩
  intro N z hz0 hz1
  have hx' := bx N z hz0 hz1
  have ha' := ba N z hz0 hz1
  have hp' := bp N z hz0 hz1
  have hm' := bm N z hz0 hz1
  dsimp only [termGradient]
  apply (gradient_norm_le _ _).trans
  gcongr
  · simpa only [norm_mul] using mul_le_mul_of_nonneg_left hx' (norm_nonneg _)
  · calc
      _ ≤ ‖(a : ℂ) * term u nu (a - 1) d negative N z‖ +
          ‖(Real.pi : ℂ) * (term u (nu + 1) a (d + 1) negative N z +
            term u (nu - 1) a (d + 1) negative N z)‖ := norm_sub_le _ _
      _ ≤ ‖(a : ℂ)‖ * Ma N + ‖(Real.pi : ℂ)‖ * (Mp N + Mm N) := by
        rw [norm_mul, norm_mul]
        gcongr
        exact (norm_add_le _ _).trans (add_le_add hp' hm')

/-- Derivative of the whole infinite family, expressed by four shifted families. -/
def valueGradient (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (z : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] ℂ :=
  gradient (horizontalRate negative * value u nu a (d + 1) negative z)
    ((a : ℂ) * value u nu (a - 1) d negative z -
      (Real.pi : ℂ) * (value u (nu + 1) a (d + 1) negative z +
        value u (nu - 1) a (d + 1) negative z))

private theorem termGradient_hasSum (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    HasSum (fun N => termGradient u nu a d negative N z)
      (valueGradient u nu a d negative z) := by
  have hx := (term_summable u nu a (d + 1) negative z hz).hasSum.mul_left
    (horizontalRate negative)
  have hy := ((term_summable u nu (a - 1) d negative z hz).hasSum.mul_left (a : ℂ)).sub
    (((term_summable u (nu + 1) a (d + 1) negative z hz).hasSum.add
      (term_summable u (nu - 1) a (d + 1) negative z hz).hasSum).mul_left (Real.pi : ℂ))
  exact (hx.mapL (ContinuousLinearMap.smulRightL ℝ (Fin 2 → ℝ) ℂ (coord 0))).add
    (hy.mapL (ContinuousLinearMap.smulRightL ℝ (Fin 2 → ℝ) ℂ (coord 1)))

private theorem height_bounds_of_mem_ball (z w : Fin 2 → ℝ)
    (hw : w ∈ Metric.ball z (z 1 / 2)) : z 1 / 2 ≤ w 1 ∧ w 1 ≤ 3 * z 1 / 2 := by
  have hh : |w 1 - z 1| < z 1 / 2 := by
    exact lt_of_le_of_lt (norm_le_pi_norm (w - z) 1)
      (by simpa only [Metric.mem_ball, dist_eq_norm] using hw)
  obtain ⟨hl, hu⟩ := abs_lt.mp hh
  constructor <;> linarith

/-- The actual Frechet derivative of the full infinite sum at every positive height. -/
theorem value_hasFDerivAt (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    HasFDerivAt (value u nu a d negative) (valueGradient u nu a d negative z) z := by
  obtain ⟨M, hM, bM⟩ := termGradient_local_majorant u nu a d negative
    (z 1 / 2) (3 * z 1 / 2) (by positivity)
  have hzmem : z ∈ Metric.ball z (z 1 / 2) := Metric.mem_ball_self (by positivity)
  have h := hasFDerivAt_tsum_of_isPreconnected hM Metric.isOpen_ball
    (convex_ball z (z 1 / 2)).isPreconnected
    (fun N w hw => term_hasFDerivAt u nu a d negative N w
      (lt_of_lt_of_le (by positivity) (height_bounds_of_mem_ball z w hw).1))
    (fun N w hw => bM N w (height_bounds_of_mem_ball z w hw).1
      (height_bounds_of_mem_ball z w hw).2)
    hzmem (term_summable u nu a d negative z hz) hzmem
  rw [(termGradient_hasSum u nu a d negative z hz).tsum_eq] at h
  exact h

/-- Joint differentiability on the entire positive-height domain. -/
theorem value_differentiableOn (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool) :
    DifferentiableOn ℝ (value u nu a d negative) domain :=
  fun z hz => (value_hasFDerivAt u nu a d negative z hz).differentiableAt.differentiableWithinAt

/-- All finite orders of joint smoothness; each induction step uses the actual derivative. -/
theorem value_contDiffOn_nat (k : ℕ) : ∀ (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool),
    ContDiffOn ℝ k (value u nu a d negative) domain := by
  induction k with
  | zero =>
      intro u nu a d negative
      exact contDiffOn_zero.mpr (value_differentiableOn u nu a d negative).continuousOn
  | succ k ih =>
      intro u nu a d negative
      rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 by simp]
      apply (contDiffOn_succ_iff_fderiv_of_isOpen domain_open).mpr
      refine ⟨value_differentiableOn u nu a d negative, by simp, ?_⟩
      have hx := (contDiffOn_const (c := horizontalRate negative)).mul (ih u nu a (d + 1) negative)
      have hy := ((contDiffOn_const (c := (a : ℂ))).mul (ih u nu (a - 1) d negative)).sub
        ((contDiffOn_const (c := (Real.pi : ℂ))).mul ((ih u (nu + 1) a (d + 1) negative).add
          (ih u (nu - 1) a (d + 1) negative)))
      have hg : ContDiffOn ℝ (k : ℕ∞ω) (valueGradient u nu a d negative) domain :=
        ((ContinuousLinearMap.smulRightL ℝ (Fin 2 → ℝ) ℂ (coord 0)).contDiff.comp_contDiffOn hx).add
          ((ContinuousLinearMap.smulRightL ℝ (Fin 2 → ℝ) ℂ (coord 1)).contDiff.comp_contDiffOn hy)
      exact hg.congr fun z hz => (value_hasFDerivAt u nu a d negative z hz).fderiv

/-- The literal infinite angular family is jointly smooth, for arbitrary complex parameters. -/
theorem value_contDiffOn (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool) :
    ContDiffOn ℝ ∞ (value u nu a d negative) domain :=
  contDiffOn_infty.mpr fun k => value_contDiffOn_nat k u nu a d negative

end
end RHTower.D4BMAngularSeries
