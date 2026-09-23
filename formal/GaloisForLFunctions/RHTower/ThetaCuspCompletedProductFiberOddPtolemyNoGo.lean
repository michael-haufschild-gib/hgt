import GaloisForLFunctions.RHTower.ThetaCuspWignerProductFiberNormalForm
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedFourPointParityWall
import GaloisForLFunctions.RHTower.ThetaCuspReflectedSourceOddStationary
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureBalance

/-!
# First completed product-fibre odd-Ptolemy no-go

This module rules out a fibrewise route to the reflection-odd four-point wall.
The first completed theta product fibre rises from the modular seam, is strictly
log-concave on the positive ray, and decays to zero.  Those three exact facts
force a level crossing whose midpoint and exterior secant values give a strictly
negative odd Ptolemy wall.  Continuity makes the failure persist for a germ of
strictly positive centres.

The conclusion is deliberately fibrewise: it does not assert failure of the
wall for the completed source.  Instead it proves that any successful global
argument must use genuine cancellation between product fibres before applying
Ptolemy transport.
-/

open Real Set Filter Topology

namespace RHTower

noncomputable section

private theorem exists_right_gt_of_hasDerivAt_pos
    {f : ℝ → ℝ} {f' : ℝ} (h : HasDerivAt f f' 0) (hf' : 0 < f') :
    ∃ t : ℝ, 0 < t ∧ f 0 < f t := by
  have hslope : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < t⁻¹ * (f t - f 0) := by
    simpa [smul_eq_mul] using
      h.tendsto_slope_zero_right.eventually (eventually_gt_nhds hf')
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, htSlope, ht⟩ := (hslope.and hpos).exists
  refine ⟨t, ht, ?_⟩
  rcases (mul_pos_iff.mp htSlope) with hgood | hbad
  · exact sub_pos.mp hgood.2
  · exact False.elim ((not_lt_of_ge (inv_nonneg.mpr ht.le)) hbad.1)

/-- Log-density coordinate of the first theta atom on the nonnegative ray. -/
def thetaCuspFirstAtomLogDensity (x : ℝ) : ℝ :=
  -thetaCuspBornWittenLogDensityPotential 1 x

theorem hasDerivAt_thetaCuspFirstAtomLogDensity
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt thetaCuspFirstAtomLogDensity
      (-2 * thetaCuspBornWittenSuperpotential 1 x) x := by
  unfold thetaCuspFirstAtomLogDensity
  change HasDerivAt (-thetaCuspBornWittenLogDensityPotential 1)
    (-2 * thetaCuspBornWittenSuperpotential 1 x) x
  exact (hasDerivAt_thetaCuspBornWittenLogDensityPotential
    (n := 1) (by norm_num) hx).neg.congr_deriv (by ring)

theorem hasDerivAt_deriv_thetaCuspFirstAtomLogDensity
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (deriv thetaCuspFirstAtomLogDensity)
      (-thetaCuspBornWittenLogCurvature 1 x) x := by
  have hraw :
      HasDerivAt
        (fun y : ℝ => -2 * thetaCuspBornWittenSuperpotential 1 y)
        (-thetaCuspBornWittenLogCurvature 1 x) x := by
    have hneg := (hasDerivAt_two_thetaCuspBornWittenSuperpotential
      (n := 1) (by norm_num) hx.le).neg
    apply hneg.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun y => by
      simp only [Pi.neg_apply, neg_mul])
  have heq :
      (deriv thetaCuspFirstAtomLogDensity) =ᶠ[nhds x]
        (fun y : ℝ => -2 * thetaCuspBornWittenSuperpotential 1 y) := by
    filter_upwards [show ∀ᶠ y : ℝ in nhds x, y ∈ Ioi 0 from Ioi_mem_nhds hx] with y hy
    exact (hasDerivAt_thetaCuspFirstAtomLogDensity hy.le).deriv
  exact hraw.congr_of_eventuallyEq heq

theorem strictConcaveOn_thetaCuspFirstAtomLogDensity :
    StrictConcaveOn ℝ (Ici 0) thetaCuspFirstAtomLogDensity := by
  apply strictConcaveOn_of_deriv2_neg
    (convex_Ici (0 : ℝ) : Convex ℝ (Ici (0 : ℝ)))
  · intro x hx
    exact (hasDerivAt_thetaCuspFirstAtomLogDensity hx).continuousAt.continuousWithinAt
  · intro x hx
    have hxpos : 0 < x := by
      simpa only [interior_Ici, mem_Ioi] using hx
    have hsecond :=
      (hasDerivAt_deriv_thetaCuspFirstAtomLogDensity hxpos).deriv
    have hcurv := thetaCuspBornWittenLogCurvature_floor
      (n := 1) (by norm_num) hxpos.le
    norm_num at hcurv
    rw [Function.iterate_succ_apply, Function.iterate_one]
    rw [hsecond]
    nlinarith [Real.pi_pos]

theorem thetaCuspSourceTerm_one_eq_exp_firstAtomLogDensity
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspSourceTerm x 1 =
      Real.pi * Real.exp (thetaCuspFirstAtomLogDensity x) := by
  rw [thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq_of_nonneg 1 hx]
  unfold thetaCuspFirstAtomLogDensity thetaCuspBornWittenLogDensityPotential
  rw [neg_neg, Real.exp_log]
  exact sq_pos_of_pos
    (thetaCuspBornWittenAmplitude_pos (n := 1) (by norm_num) hx)

theorem tendsto_thetaCuspSourceTerm_one_atTop_zero :
    Tendsto (fun x : ℝ => thetaCuspSourceTerm x 1) atTop (nhds 0) := by
  apply squeeze_zero' ?_ ?_ tendsto_thetaCuspFullSource_atTop_zero
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact thetaCuspSourceTerm_nonneg_of_pos hx 1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [thetaCuspFullSource]
    exact (summable_thetaCuspSourceTerm x).le_tsum 1
      (fun n _ => thetaCuspSourceTerm_nonneg_of_pos hx n)

private theorem thetaPositiveFactorPairs_one :
    thetaPositiveFactorPairs 1 = {(0, 0)} := by
  ext ⟨a, b⟩
  simp [thetaPositiveFactorPairs]

theorem thetaCuspCompletedProductFiberAmplitude_one (u t : ℝ) :
    thetaCuspCompletedProductFiberAmplitude 1 u t =
      thetaCuspSourceTerm |u + t| 1 * thetaCuspSourceTerm |u - t| 1 := by
  rw [thetaCuspCompletedProductFiberAmplitude, thetaPositiveFactorPairs_one]
  simp [thetaCuspCompletedPositiveShell]

theorem thetaCuspCompletedProductFiberAmplitude_one_zero (t : ℝ) :
    thetaCuspCompletedProductFiberAmplitude 1 0 t =
      thetaCuspSourceTerm |t| 1 ^ (2 : ℕ) := by
  rw [thetaCuspCompletedProductFiberAmplitude_one]
  simp only [zero_add, zero_sub, abs_neg]
  ring

/-- Reflection-odd four-point wall of the first completed product fibre. -/
def thetaCuspFirstCompletedProductFiberOddParityWall (u t : ℝ) : ℝ :=
  toeplitzFourOddParityWall
    (thetaCuspCompletedProductFiberAmplitude 1 u 0)
    (thetaCuspCompletedProductFiberAmplitude 1 u t)
    (thetaCuspCompletedProductFiberAmplitude 1 u (2 * t))
    (thetaCuspCompletedProductFiberAmplitude 1 u (3 * t))

theorem continuous_thetaCuspFirstCompletedProductFiberOddParityWall_left
    (t : ℝ) :
    Continuous (fun u => thetaCuspFirstCompletedProductFiberOddParityWall u t) := by
  unfold thetaCuspFirstCompletedProductFiberOddParityWall
  simp_rw [thetaCuspCompletedProductFiberAmplitude_one]
  unfold toeplitzFourOddParityWall
  have hsource : Continuous (fun x : ℝ => thetaCuspSourceTerm x 1) :=
    continuous_thetaCuspSourceTerm_one
  have hfiber (s : ℝ) : Continuous (fun u : ℝ =>
      thetaCuspSourceTerm |u + s| 1 * thetaCuspSourceTerm |u - s| 1) := by
    exact
      (hsource.comp (continuous_abs.comp (continuous_id.add continuous_const))).mul
        (hsource.comp (continuous_abs.comp (continuous_id.sub continuous_const)))
  exact (((hfiber 0).sub (hfiber (3 * t))).mul
      ((hfiber 0).sub (hfiber t))).sub
    (((hfiber t).sub (hfiber (2 * t))).pow 2)

/-- A rising, decaying strictly log-concave profile must cross a negative odd wall. -/
theorem strictConcave_crossing_forces_oddParityWall_neg
    {g f : ℝ → ℝ} {a b : ℝ}
    (hconc : StrictConcaveOn ℝ (Ici 0) g)
    (hcont : Continuous f)
    (hgf : ∀ x : ℝ, 0 ≤ x → f x = Real.pi * Real.exp (g x))
    (ha : 0 < a) (hab : a < b)
    (hrise : f 0 < f a) (hfall : f b < f 0) :
    ∃ t : ℝ, 0 < t ∧
      toeplitzFourOddParityWall
        (f 0 ^ (2 : ℕ)) (f t ^ (2 : ℕ)) (f (2 * t) ^ (2 : ℕ)) (f (3 * t) ^ (2 : ℕ)) < 0 := by
  have htarget : f 0 ∈ Icc (f b) (f a) := ⟨hfall.le, hrise.le⟩
  obtain ⟨T, hTmem, hT⟩ :=
    (intermediate_value_Icc' hab.le hcont.continuousOn htarget)
  have hTpos : 0 < T := ha.trans_le hTmem.1
  have hgT : g T = g 0 := by
    have hzero : 0 ≤ (0 : ℝ) := le_rfl
    have hTnonneg : 0 ≤ T := hTpos.le
    rw [hgf 0 hzero, hgf T hTnonneg] at hT
    have hexp : Real.exp (g T) = Real.exp (g 0) := by
      nlinarith [Real.pi_pos]
    exact Real.exp_injective hexp
  have hmidLog : g 0 < g (T / 2) := by
    have hraw := hconc.2
      (show 0 ∈ Ici (0 : ℝ) by simp)
      (show T ∈ Ici (0 : ℝ) by exact hTpos.le)
      (ne_of_lt hTpos)
      (show 0 < (1 / 2 : ℝ) by norm_num)
      (show 0 < (1 / 2 : ℝ) by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    rw [hgT] at hraw
    have hpoint :
        (1 / 2 : ℝ) • (0 : ℝ) + (1 / 2 : ℝ) • T = T / 2 := by
      norm_num only [smul_eq_mul]
      ring
    rw [hpoint] at hraw
    norm_num only [smul_eq_mul] at hraw
    linarith
  have htailLog : g (3 * (T / 2)) < g 0 := by
    have hthreePos : 0 < 3 * (T / 2) := by positivity
    have hraw := hconc.2
      (show 0 ∈ Ici (0 : ℝ) by simp)
      (show 3 * (T / 2) ∈ Ici (0 : ℝ) by exact hthreePos.le)
      (ne_of_lt hthreePos)
      (show 0 < (1 / 3 : ℝ) by norm_num)
      (show 0 < (2 / 3 : ℝ) by norm_num)
      (show (1 / 3 : ℝ) + 2 / 3 = 1 by norm_num)
    have hpoint :
        (1 / 3 : ℝ) • (0 : ℝ) + (2 / 3 : ℝ) • (3 * (T / 2)) = T := by
      norm_num only [smul_eq_mul]
      ring
    rw [hpoint, hgT] at hraw
    norm_num only [smul_eq_mul] at hraw
    linarith
  let t : ℝ := T / 2
  have ht : 0 < t := half_pos hTpos
  have hfzero : 0 < f 0 := by
    rw [hgf 0 le_rfl]
    positivity
  have hfmid : f 0 < f t := by
    rw [hgf 0 le_rfl, hgf t ht.le]
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hmidLog) Real.pi_pos
  have hfthreePos : 0 < f (3 * t) := by
    rw [hgf (3 * t) (by positivity)]
    positivity
  have hfthree : f (3 * t) < f 0 := by
    rw [hgf (3 * t) (by positivity), hgf 0 le_rfl]
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr htailLog) Real.pi_pos
  refine ⟨t, ht, ?_⟩
  unfold toeplitzFourOddParityWall
  have hsqmid : f 0 ^ (2 : ℕ) < f t ^ (2 : ℕ) := by nlinarith
  have hsqthree : f (3 * t) ^ (2 : ℕ) < f 0 ^ (2 : ℕ) := by nlinarith
  nlinarith [sq_nonneg (f t ^ (2 : ℕ) - f (2 * t) ^ (2 : ℕ))]

/-- The first completed product fibre rises strictly away from the modular seam. -/
theorem exists_thetaCuspCompletedProductFiberAmplitude_one_rise :
    ∃ t : ℝ, 0 < t ∧
      thetaCuspCompletedProductFiberAmplitude 1 0 0 <
        thetaCuspCompletedProductFiberAmplitude 1 0 t := by
  obtain ⟨t, ht, hrise⟩ := exists_right_gt_of_hasDerivAt_pos
    hasDerivAt_thetaCuspSourceTerm_one_zero
    (mul_pos thetaCuspFirstAtomBoundaryLogSlope_pos
      thetaCuspSourceTerm_one_zero_pos)
  refine ⟨t, ht, ?_⟩
  rw [thetaCuspCompletedProductFiberAmplitude_one_zero,
    thetaCuspCompletedProductFiberAmplitude_one_zero,
    abs_of_nonneg le_rfl, abs_of_nonneg ht.le]
  nlinarith [thetaCuspSourceTerm_one_zero_pos]

/-- At the modular seam, the first completed product fibre has a negative odd wall. -/
theorem exists_thetaCuspCompletedProductFiberAmplitude_one_oddParityWall_neg :
    ∃ t : ℝ, 0 < t ∧
      toeplitzFourOddParityWall
        (thetaCuspCompletedProductFiberAmplitude 1 0 0)
        (thetaCuspCompletedProductFiberAmplitude 1 0 t)
        (thetaCuspCompletedProductFiberAmplitude 1 0 (2 * t))
        (thetaCuspCompletedProductFiberAmplitude 1 0 (3 * t)) < 0 := by
  let f : ℝ → ℝ := fun x => thetaCuspSourceTerm x 1
  have hriseRaw := exists_right_gt_of_hasDerivAt_pos
    hasDerivAt_thetaCuspSourceTerm_one_zero
    (mul_pos thetaCuspFirstAtomBoundaryLogSlope_pos
      thetaCuspSourceTerm_one_zero_pos)
  obtain ⟨a, ha, hriseRaw'⟩ := hriseRaw
  have hrise : f 0 < f a := by
    dsimp only [f]
    exact hriseRaw'
  have hfallEventually : ∀ᶠ x : ℝ in atTop, f x < f 0 := by
    have hlim : Tendsto f atTop (nhds 0) :=
      tendsto_thetaCuspSourceTerm_one_atTop_zero
    exact (tendsto_order.1 hlim).2 (f 0) (by
      dsimp only [f]
      exact thetaCuspSourceTerm_one_zero_pos)
  obtain ⟨b, hfall, hab⟩ :=
    (hfallEventually.and (eventually_gt_atTop a)).exists
  obtain ⟨t, ht, hwall⟩ :=
    strictConcave_crossing_forces_oddParityWall_neg
      strictConcaveOn_thetaCuspFirstAtomLogDensity
      continuous_thetaCuspSourceTerm_one
      (fun x hx => thetaCuspSourceTerm_one_eq_exp_firstAtomLogDensity hx)
      ha hab hrise hfall
  refine ⟨t, ht, ?_⟩
  rw [thetaCuspCompletedProductFiberAmplitude_one_zero,
    thetaCuspCompletedProductFiberAmplitude_one_zero,
    thetaCuspCompletedProductFiberAmplitude_one_zero,
    thetaCuspCompletedProductFiberAmplitude_one_zero]
  rw [abs_of_nonneg le_rfl, abs_of_nonneg ht.le,
    abs_of_nonneg (by positivity : 0 ≤ 2 * t),
    abs_of_nonneg (by positivity : 0 ≤ 3 * t)]
  exact hwall

/-- The first-fibre odd-wall failure persists on a right germ of positive centres. -/
theorem exists_thetaCuspFirstCompletedProductFiberOddParityWall_neg_germ :
    ∃ t : ℝ, 0 < t ∧ ∀ᶠ u : ℝ in 𝓝[>] 0,
      thetaCuspFirstCompletedProductFiberOddParityWall u t < 0 := by
  obtain ⟨t, ht, hneg⟩ :=
    exists_thetaCuspCompletedProductFiberAmplitude_one_oddParityWall_neg
  have hneg' : thetaCuspFirstCompletedProductFiberOddParityWall 0 t < 0 := hneg
  have hnear : ∀ᶠ u : ℝ in nhds 0,
      thetaCuspFirstCompletedProductFiberOddParityWall u t < 0 :=
    (continuous_thetaCuspFirstCompletedProductFiberOddParityWall_left t).continuousAt.tendsto.eventually
      (eventually_lt_nhds hneg')
  have hnearRight : ∀ᶠ u : ℝ in 𝓝[>] 0,
      thetaCuspFirstCompletedProductFiberOddParityWall u t < 0 :=
    hnear.filter_mono (show 𝓝[>] (0 : ℝ) ≤ nhds 0 from inf_le_left)
  exact ⟨t, ht, hnearRight⟩

/-- A strictly positive centre witnesses first-fibre odd-wall failure. -/
theorem exists_pos_thetaCuspCompletedProductFiberAmplitude_one_oddParityWall_neg :
    ∃ u t : ℝ, 0 < u ∧ 0 < t ∧
      thetaCuspFirstCompletedProductFiberOddParityWall u t < 0 := by
  obtain ⟨t, ht, hnearRight⟩ :=
    exists_thetaCuspFirstCompletedProductFiberOddParityWall_neg_germ
  have hpos : ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u := self_mem_nhdsWithin
  obtain ⟨u, huneg, hu⟩ := (hnearRight.and hpos).exists
  exact ⟨u, t, hu, ht, huneg⟩

end

end RHTower
