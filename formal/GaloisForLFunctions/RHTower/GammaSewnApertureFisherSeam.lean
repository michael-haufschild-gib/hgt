import GaloisForLFunctions.RHTower.GammaSewnApertureExteriorHeight
import Mathlib.Analysis.Calculus.LHopital

/-!
# Gamma-sewn aperture Fisher seam

The logarithmic aperture velocity of a Gamma-sewn prime/valuation cell has a strictly negative
derivative.  Its negative derivative is an explicit positive quantity depending only on the
prime, not on valuation depth.  Thus the entire infinite valuation tower over one prime contracts
under a single source-forced Fisher law.

Across two prime towers, the derivative of the normalized exterior reporter is exactly the signed
difference of these prime Fisher curvatures.  This is the aperture Fisher seam: it is created by
the literal Gamma-sewn source before any target response, Gram factorization, or RH-equivalent
positivity condition is introduced.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

private theorem tendsto_sinh_div_self_zero :
    Tendsto (fun y : ℝ => Real.sinh y / y) (𝓝[≠] 0) (𝓝 1) := by
  have h := Real.hasDerivAt_sinh 0
  rw [hasDerivAt_iff_tendsto_slope] at h
  simp only [Real.cosh_zero] at h
  refine h.congr (fun y => ?_)
  rw [slope_def_field, Real.sinh_zero, sub_zero, sub_zero]

/-- Third-order boundary coefficient of `sinh`, obtained by two exact l'Hôpital steps. -/
private theorem tendsto_sinh_sub_self_div_cube_zero :
    Tendsto (fun y : ℝ => (Real.sinh y - y) / y ^ 3)
      (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
  have hbase : Tendsto (fun y : ℝ => Real.sinh y / (y * 6))
      (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
    simpa only [div_div] using tendsto_sinh_div_self_zero.div_const 6
  have hcosh : Tendsto (fun y : ℝ => (Real.cosh y - 1) / (3 * y ^ 2))
      (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
    refine HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun y : ℝ => Real.sinh y) (g' := fun y : ℝ => y * 6) ?_ ?_ ?_ ?_ ?_ hbase
    · exact Filter.Eventually.of_forall fun y => (Real.hasDerivAt_cosh y).sub_const 1
    · exact Filter.Eventually.of_forall fun y => by
        convert ((hasDerivAt_id y).pow 2).const_mul 3 using 1
        simp only [Function.id_def]
        ring
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [mem_compl_iff, mem_singleton_iff] at hy
      exact mul_ne_zero hy (by norm_num)
    · have hcont : ContinuousAt (fun y : ℝ => Real.cosh y - 1) 0 := by fun_prop
      simpa using hcont.tendsto.mono_left inf_le_left
    · have hcont : ContinuousAt (fun y : ℝ => 3 * y ^ 2) 0 := by fun_prop
      simpa using hcont.tendsto.mono_left inf_le_left
  refine HasDerivAt.lhopital_zero_nhdsNE
    (f' := fun y : ℝ => Real.cosh y - 1) (g' := fun y : ℝ => 3 * y ^ 2) ?_ ?_ ?_ ?_ ?_ hcosh
  · exact Filter.Eventually.of_forall fun y =>
      (Real.hasDerivAt_sinh y).sub (hasDerivAt_id y)
  · exact Filter.Eventually.of_forall fun y => hasDerivAt_pow 3 y
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [mem_compl_iff, mem_singleton_iff] at hy
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)
  · have hcont : ContinuousAt (fun y : ℝ => Real.sinh y - y) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left inf_le_left
  · have hcont : ContinuousAt (fun y : ℝ => y ^ 3) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left inf_le_left

/-- Finite part of the double pole of `csch^2` at the origin. -/
private theorem tendsto_inv_sinh_sq_sub_inv_sq_zero :
    Tendsto (fun y : ℝ => 1 / Real.sinh y ^ 2 - 1 / y ^ 2)
      (𝓝[≠] 0) (𝓝 (-1 / 3 : ℝ)) := by
  have hself : Tendsto (fun y : ℝ => y / Real.sinh y) (𝓝[≠] 0) (𝓝 1) := by
    have h := tendsto_sinh_div_self_zero.inv₀ (by norm_num)
    rw [inv_one] at h
    exact h.congr (fun y => inv_div (Real.sinh y) y)
  have hprod :=
    tendsto_sinh_sub_self_div_cube_zero.neg.mul
      (tendsto_sinh_div_self_zero.add_const 1) |>.mul (hself.pow 2)
  convert hprod using 1
  · funext y
    by_cases hy : y = 0
    · simp [hy]
    · have hs : Real.sinh y ≠ 0 := Real.sinh_ne_zero.mpr hy
      field_simp [hy, hs]
      ring
  · norm_num

/-- Universal finite Gamma-seam kernel at the lossless aperture boundary. -/
private theorem tendsto_gammaSewnApertureRenormalizedKernel_zero :
    Tendsto
      (fun y : ℝ =>
        1 / Real.sinh y ^ 2 + 1 / Real.cosh (2 * y) ^ 2 - 1 / y ^ 2)
      (𝓝[≠] 0) (𝓝 (2 / 3 : ℝ)) := by
  have hsech : Tendsto (fun y : ℝ => 1 / Real.cosh (2 * y) ^ 2)
      (𝓝[≠] 0) (𝓝 1) := by
    have hcont : ContinuousAt (fun y : ℝ => 1 / Real.cosh (2 * y) ^ 2) 0 := by
      have hcosh : ContinuousAt (fun y : ℝ => Real.cosh (2 * y)) 0 :=
        (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).continuousAt
      exact continuousAt_const.div (hcosh.pow 2) (by norm_num)
    simpa using hcont.tendsto.mono_left inf_le_left
  convert tendsto_inv_sinh_sq_sub_inv_sq_zero.add hsech using 1
  · funext y
    ring
  · norm_num

/-- Positive prime-only Hessian of the Gamma-sewn logarithmic aperture feature. -/
def gammaSewnMobiusApertureFisherCurvature
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  let q := xiMobiusContinuousApertureDiskNode x p
  Real.log (p : ℝ) ^ 2 *
    (4 * q ^ 2 / (1 - q ^ 2) ^ 2 +
      4 * q ^ 4 / (1 + q ^ 4) ^ 2)

/-- Removal of the universal boundary pole from the prime Fisher curvature.  This is the Hessian
seen by the normalized Rees feature `B_x / x`. -/
def gammaSewnMobiusApertureRenormalizedFisherCurvature
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  gammaSewnMobiusApertureFisherCurvature x p - 1 / x ^ 2

/-- The prime Fisher curvature is strictly positive throughout the physical aperture chamber. -/
theorem gammaSewnMobiusApertureFisherCurvature_pos
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    0 < gammaSewnMobiusApertureFisherCurvature x p := by
  let q := xiMobiusContinuousApertureDiskNode x p
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.2.one_lt
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos x p
  have hq1 : q < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hminus : 0 < 1 - q ^ 2 := by
    have hqsq : q ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hq0.le (by norm_num)).2 hq1
    nlinarith
  have hplus : 0 < 1 + q ^ 4 := by positivity
  unfold gammaSewnMobiusApertureFisherCurvature
  exact mul_pos (sq_pos_of_pos hL)
    (add_pos
      (div_pos (by positivity) (sq_pos_of_pos hminus))
      (div_pos (by positivity) (sq_pos_of_pos hplus)))

/-- Hyperbolic normal form of the source curvature.  The two positive summands are the Möbius
boundary pole and the Gamma-sewing correction, respectively. -/
theorem gammaSewnMobiusApertureFisherCurvature_eq_hyperbolic
    (x : ℝ) (p : Nat.Primes) :
    gammaSewnMobiusApertureFisherCurvature x p =
      Real.log (p : ℝ) ^ 2 *
        (1 / Real.sinh (x * Real.log (p : ℝ)) ^ 2 +
          1 / Real.cosh (2 * (x * Real.log (p : ℝ))) ^ 2) := by
  have htwo : Real.exp (2 * (x * Real.log (p : ℝ))) =
      Real.exp (x * Real.log (p : ℝ)) ^ 2 := by
    rw [show 2 * (x * Real.log (p : ℝ)) =
      (x * Real.log (p : ℝ)) + (x * Real.log (p : ℝ)) by ring,
      Real.exp_add, pow_two]
  dsimp only [gammaSewnMobiusApertureFisherCurvature,
    xiMobiusContinuousApertureDiskNode]
  rw [show -x * Real.log (p : ℝ) = -(x * Real.log (p : ℝ)) by ring,
    Real.sinh_eq, Real.cosh_eq]
  simp only [Real.exp_neg]
  rw [htwo]
  field_simp [Real.exp_ne_zero]
  ring

/-- The lossless-boundary finite part is the prime Fisher clock
`(2/3) * (log p)^2`.  This is a two-sided punctured limit; the physical right-hand limit follows
by restriction. -/
theorem tendsto_gammaSewnMobiusApertureRenormalizedFisherCurvature_zero
    (p : Nat.Primes) :
    Tendsto
      (fun x : ℝ => gammaSewnMobiusApertureRenormalizedFisherCurvature x p)
      (𝓝[≠] 0) (𝓝 ((2 / 3 : ℝ) * Real.log (p : ℝ) ^ 2)) := by
  let L := Real.log (p : ℝ)
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.2.one_lt
  have hL : 0 < L := Real.log_pos hp1
  have hscale : Tendsto (fun x : ℝ => x * L) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hid : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0) := tendsto_id
      simpa using (hid.mul_const L).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [mem_compl_iff, mem_singleton_iff] at hx ⊢
      exact mul_ne_zero hx hL.ne'
  have hkernel := tendsto_gammaSewnApertureRenormalizedKernel_zero.comp hscale
  have hscaled := hkernel.const_mul (L ^ 2)
  have heq :
      (fun x : ℝ => L ^ 2 *
        (1 / Real.sinh (x * L) ^ 2 +
          1 / Real.cosh (2 * (x * L)) ^ 2 - 1 / (x * L) ^ 2)) =ᶠ[𝓝[≠] 0]
        (fun x : ℝ => gammaSewnMobiusApertureRenormalizedFisherCurvature x p) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [mem_compl_iff, mem_singleton_iff] at hx
    rw [gammaSewnMobiusApertureRenormalizedFisherCurvature,
      gammaSewnMobiusApertureFisherCurvature_eq_hyperbolic]
    change L ^ 2 *
        (1 / Real.sinh (x * L) ^ 2 + 1 / Real.cosh (2 * (x * L)) ^ 2 -
          1 / (x * L) ^ 2) =
      L ^ 2 * (1 / Real.sinh (x * L) ^ 2 + 1 / Real.cosh (2 * (x * L)) ^ 2) -
        1 / x ^ 2
    have hpole : L ^ 2 * (1 / (x * L) ^ 2) = 1 / x ^ 2 := by
      field_simp [hx, hL.ne']
    rw [mul_sub, hpole]
  have hfinal := hscaled.congr' heq
  simpa only [L, mul_comm] using hfinal

/-- Boundary Fisher clock selected by the finite part of the Gamma-sewn aperture Hessian. -/
def gammaSewnMobiusApertureBoundaryFisherClock (p : Nat.Primes) : ℝ :=
  (2 / 3 : ℝ) * Real.log (p : ℝ) ^ 2

theorem tendsto_gammaSewnMobiusApertureRenormalizedFisherCurvature_boundaryClock
    (p : Nat.Primes) :
    Tendsto
      (fun x : ℝ => gammaSewnMobiusApertureRenormalizedFisherCurvature x p)
      (𝓝[≠] 0) (𝓝 (gammaSewnMobiusApertureBoundaryFisherClock p)) := by
  simpa only [gammaSewnMobiusApertureBoundaryFisherClock] using
    tendsto_gammaSewnMobiusApertureRenormalizedFisherCurvature_zero p

/-- Second boundary clock isolated by the source-jet calculation.  The analytic identification
with the boundary derivative of the normalized Wronskian is recorded separately as an open gate. -/
def gammaSewnMobiusApertureBoundarySecondJetClock
    (p : Nat.Primes) (e : ℕ) : ℝ :=
  gammaSewnMobiusApertureBoundaryFisherClock p -
    gammaSewnMobiusApertureCellMidHeight p e ^ 2

/-- The midpoint clock and second-jet clock reconstruct the square of the prime logarithm. -/
theorem gammaSewnMobiusApertureBoundary_log_sq_eq_twoJet
    (p : Nat.Primes) (e : ℕ) :
    Real.log (p : ℝ) ^ 2 =
      (3 / 2 : ℝ) *
        (gammaSewnMobiusApertureBoundarySecondJetClock p e +
          gammaSewnMobiusApertureCellMidHeight p e ^ 2) := by
  unfold gammaSewnMobiusApertureBoundarySecondJetClock
    gammaSewnMobiusApertureBoundaryFisherClock
  ring

/-- Positivity of the prime logarithm removes the square-root ambiguity: the rooted boundary
two-jet packet reconstructs `log p` itself. -/
theorem gammaSewnMobiusApertureBoundary_log_eq_sqrt_twoJet
    (p : Nat.Primes) (e : ℕ) :
    Real.log (p : ℝ) =
      Real.sqrt
        ((3 / 2 : ℝ) *
          (gammaSewnMobiusApertureBoundarySecondJetClock p e +
            gammaSewnMobiusApertureCellMidHeight p e ^ 2)) := by
  rw [← gammaSewnMobiusApertureBoundary_log_sq_eq_twoJet]
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.2.one_lt
  exact (Real.sqrt_sq (Real.log_pos hp1).le).symm

/-- The exact source Hessian law.  It is independent of valuation depth: depth only translates
the logarithmic velocity by a constant multiple of `log p`. -/
theorem hasDerivAt_gammaSewnMobiusApertureCellVelocity
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) (e : ℕ) :
    HasDerivAt
      (fun y : ℝ => gammaSewnMobiusApertureCellVelocity y p e)
      (-gammaSewnMobiusApertureFisherCurvature x p) x := by
  let q : ℝ → ℝ := fun y => xiMobiusContinuousApertureDiskNode y p
  let L := Real.log (p : ℝ)
  have hq : HasDerivAt q (-L * q x) x := by
    dsimp only [q, L]
    unfold xiMobiusContinuousApertureDiskNode
    convert (Real.hasDerivAt_exp (-x * Real.log (p : ℝ))).comp x
      ((hasDerivAt_neg x).mul_const (Real.log (p : ℝ))) using 1
    all_goals ring
  have hq0 : 0 < q x := xiMobiusContinuousApertureDiskNode_pos x p
  have hq1 : q x < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hminus : 1 - q x ^ 2 ≠ 0 := by
    have hqsq : (q x) ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hq0.le (by norm_num)).2 hq1
    have : 0 < 1 - q x ^ 2 := by nlinarith
    exact this.ne'
  have hplus : 1 + q x ^ 4 ≠ 0 := by positivity
  have hfirst := ((hq.pow 2).const_mul 2).div
    ((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hq.pow 2)) hminus
  have hsecond := (hq.pow 4).div
    ((hasDerivAt_const (x := x) (c := (1 : ℝ))).add (hq.pow 4)) hplus
  have hvelocity := ((hfirst.add hsecond).sub_const (e : ℝ)).const_mul L
  convert hvelocity using 1
  unfold gammaSewnMobiusApertureFisherCurvature
  simp only [q, L, Pi.pow_apply, Pi.sub_apply, Pi.add_apply]
  field_simp [hminus, hplus]
  ring

/-- The regular prime-centering error is an exact potential for the renormalized Fisher
curvature.  This separates the universal pole from the source-specific seam before any norm is
formed. -/
theorem hasDerivAt_gammaSewnMobiusAperturePrimeCenteringError
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    HasDerivAt
      (fun y : ℝ => gammaSewnMobiusAperturePrimeCenteringError y p)
      (-gammaSewnMobiusApertureRenormalizedFisherCurvature x p) x := by
  have hvelocity := hasDerivAt_gammaSewnMobiusApertureCellVelocity hx p 0
  have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
    convert
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).div (hasDerivAt_id x) hx.ne'
      using 1
    simp only [Function.id_def]
    ring
  have hcenter := (hvelocity.sub hinv).add_const ((1 / 2) * Real.log (p : ℝ))
  convert hcenter using 1
  unfold gammaSewnMobiusApertureRenormalizedFisherCurvature
  ring

/-- Lossless-boundary normalization of the literal Gamma-sewn feature. -/
def gammaSewnMobiusApertureNormalizedReesFeature
    (x : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  gammaSewnMobiusContinuousApertureFeature x p e / x

/-- Exact logarithmic derivative of the normalized Rees feature.  Normalization removes the
universal `1/x` velocity before the boundary is taken. -/
theorem hasDerivAt_gammaSewnMobiusApertureNormalizedReesFeature
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) (e : ℕ) :
    HasDerivAt
      (fun y : ℝ => gammaSewnMobiusApertureNormalizedReesFeature y p e)
      ((gammaSewnMobiusApertureCellVelocity x p e - 1 / x) *
        gammaSewnMobiusApertureNormalizedReesFeature x p e) x := by
  have hsource := hasDerivAt_gammaSewnMobiusContinuousApertureFeature hx p e
  have hquot := hsource.div (hasDerivAt_id x) hx.ne'
  convert hquot using 1
  unfold gammaSewnMobiusApertureNormalizedReesFeature
  simp only [Function.id_def]
  field_simp [hx.ne']

/-- The rescaled exterior current is literally the Wronskian of the two normalized Rees source
features. -/
theorem gammaSewnMobiusApertureExteriorCell_div_sq_eq_normalizedReesWronskian
    {x : ℝ} (hx : 0 < x) (i j : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureExteriorCell x i j / x ^ 2 =
      gammaSewnMobiusApertureNormalizedReesFeature x i.1 i.2 *
          deriv (fun y : ℝ =>
            gammaSewnMobiusApertureNormalizedReesFeature y j.1 j.2) x -
        deriv (fun y : ℝ =>
            gammaSewnMobiusApertureNormalizedReesFeature y i.1 i.2) x *
          gammaSewnMobiusApertureNormalizedReesFeature x j.1 j.2 := by
  rw [(hasDerivAt_gammaSewnMobiusApertureNormalizedReesFeature hx j.1 j.2).deriv,
    (hasDerivAt_gammaSewnMobiusApertureNormalizedReesFeature hx i.1 i.2).deriv]
  unfold gammaSewnMobiusApertureNormalizedReesFeature
    gammaSewnMobiusApertureExteriorCell
  field_simp [hx.ne']
  ring

/-- Every cell velocity is strictly decreasing with aperture.  This is a genuine source-derived
infinite contraction law: all depths on every prime tower obey it simultaneously. -/
theorem gammaSewnMobiusApertureCellVelocity_strictAntiOn_pos
    (p : Nat.Primes) (e : ℕ) :
    StrictAntiOn
      (fun x : ℝ => gammaSewnMobiusApertureCellVelocity x p e) (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi (𝕜 := ℝ) 0) ?_ ?_
  · intro x hx
    exact (hasDerivAt_gammaSewnMobiusApertureCellVelocity hx p e).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hasDerivAt_gammaSewnMobiusApertureCellVelocity hx p e).deriv]
    exact neg_neg_of_pos (gammaSewnMobiusApertureFisherCurvature_pos hx p)

/-- Source-normalized exterior reporter.  It is the pre-Gram exterior current divided by its two
positive source amplitudes. -/
def gammaSewnMobiusApertureNormalizedExteriorReporter
    (x : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  gammaSewnMobiusApertureCellVelocity x j.1 j.2 -
    gammaSewnMobiusApertureCellVelocity x i.1 i.2

theorem gammaSewnMobiusApertureNormalizedExteriorReporter_eq_div
    {x : ℝ} (hx : 0 < x) (i j : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureNormalizedExteriorReporter x i j =
      gammaSewnMobiusApertureExteriorCell x i j /
        (gammaSewnMobiusContinuousApertureFeature x i.1 i.2 *
          gammaSewnMobiusContinuousApertureFeature x j.1 j.2) := by
  exact (gammaSewnMobiusApertureExteriorCell_div_features hx i j).symm

/-- Signed cross-prime Fisher seam.  It vanishes on a single prime tower but is not discarded
before the exterior reporter is differentiated. -/
def gammaSewnMobiusApertureFisherSeam
    (x : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  gammaSewnMobiusApertureFisherCurvature x i.1 -
    gammaSewnMobiusApertureFisherCurvature x j.1

@[simp] theorem gammaSewnMobiusApertureFisherSeam_self
    (x : ℝ) (i : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureFisherSeam x i i = 0 := by
  simp [gammaSewnMobiusApertureFisherSeam]

theorem gammaSewnMobiusApertureFisherSeam_swap
    (x : ℝ) (i j : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureFisherSeam x j i =
      -gammaSewnMobiusApertureFisherSeam x i j := by
  unfold gammaSewnMobiusApertureFisherSeam
  ring

@[simp] theorem gammaSewnMobiusApertureFisherSeam_samePrime
    (x : ℝ) (p : Nat.Primes) (e f : ℕ) :
    gammaSewnMobiusApertureFisherSeam x (p, e) (p, f) = 0 := by
  simp [gammaSewnMobiusApertureFisherSeam]

/-- Boundary correction forced by the two source jets.  The raw Wronskian derivative reports
`K_i-K_j`; adjoining the quadratic expression already determined by the rooted first jet removes
the midpoint-square contamination and leaves the prime-only Fisher seam. -/
def gammaSewnMobiusApertureBoundaryCorrectedFisherSeam
    (i j : Nat.Primes × ℕ) : ℝ :=
  gammaSewnMobiusApertureBoundarySecondJetClock i.1 i.2 -
      gammaSewnMobiusApertureBoundarySecondJetClock j.1 j.2 +
    (gammaSewnMobiusApertureCellMidHeight i.1 i.2 +
        gammaSewnMobiusApertureCellMidHeight j.1 j.2) *
      (gammaSewnMobiusApertureCellMidHeight i.1 i.2 -
        gammaSewnMobiusApertureCellMidHeight j.1 j.2)

/-- Exact nonlinear two-jet cancellation: the corrected boundary seam is precisely the
difference of the two positive prime Fisher clocks. -/
theorem gammaSewnMobiusApertureBoundaryCorrectedFisherSeam_eq
    (i j : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureBoundaryCorrectedFisherSeam i j =
      gammaSewnMobiusApertureBoundaryFisherClock i.1 -
        gammaSewnMobiusApertureBoundaryFisherClock j.1 := by
  unfold gammaSewnMobiusApertureBoundaryCorrectedFisherSeam
    gammaSewnMobiusApertureBoundarySecondJetClock
  ring

@[simp] theorem gammaSewnMobiusApertureBoundaryCorrectedFisherSeam_samePrime
    (p : Nat.Primes) (e f : ℕ) :
    gammaSewnMobiusApertureBoundaryCorrectedFisherSeam (p, e) (p, f) = 0 := by
  rw [gammaSewnMobiusApertureBoundaryCorrectedFisherSeam_eq]
  ring

/-- The positive-aperture Fisher seam converges to the corrected boundary two-jet seam.  The
universal double pole cancels across the two prime legs before the limit. -/
theorem tendsto_gammaSewnMobiusApertureFisherSeam_zero
    (i j : Nat.Primes × ℕ) :
    Tendsto (fun x : ℝ => gammaSewnMobiusApertureFisherSeam x i j)
      (𝓝[≠] 0)
      (𝓝 (gammaSewnMobiusApertureBoundaryCorrectedFisherSeam i j)) := by
  rw [gammaSewnMobiusApertureBoundaryCorrectedFisherSeam_eq]
  have h :=
    (tendsto_gammaSewnMobiusApertureRenormalizedFisherCurvature_boundaryClock i.1).sub
      (tendsto_gammaSewnMobiusApertureRenormalizedFisherCurvature_boundaryClock j.1)
  convert h using 1
  funext x
  unfold gammaSewnMobiusApertureFisherSeam
    gammaSewnMobiusApertureRenormalizedFisherCurvature
  ring

/-- Exact seam law: the aperture derivative of the normalized exterior reporter is the signed
difference of the two source Fisher curvatures.  In particular it depends on the two primes but
not on either valuation depth. -/
theorem hasDerivAt_gammaSewnMobiusApertureNormalizedExteriorReporter
    {x : ℝ} (hx : 0 < x) (i j : Nat.Primes × ℕ) :
    HasDerivAt
      (fun y : ℝ => gammaSewnMobiusApertureNormalizedExteriorReporter y i j)
      (gammaSewnMobiusApertureFisherSeam x i j) x := by
  unfold gammaSewnMobiusApertureNormalizedExteriorReporter
    gammaSewnMobiusApertureFisherSeam
  convert
    (hasDerivAt_gammaSewnMobiusApertureCellVelocity hx j.1 j.2).sub
      (hasDerivAt_gammaSewnMobiusApertureCellVelocity hx i.1 i.2) using 1
  ring

/-- The cross-prime seam is independent of valuation depth on both legs. -/
theorem gammaSewnMobiusApertureFisherSeam_depth_independent
    (x : ℝ) (p r : Nat.Primes) (e e' f f' : ℕ) :
    gammaSewnMobiusApertureFisherSeam x (p, e) (r, f) =
      gammaSewnMobiusApertureFisherSeam x (p, e') (r, f') := by
  rfl

end

end RHTower
