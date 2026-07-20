import GaloisForLFunctions.RHTower.GammaSewnSynchronizedLcmContraction
import GaloisForLFunctions.RHTower.GammaSewnEulerCalibratedExterior
import GaloisForLFunctions.RHTower.GammaSewnApertureFisherSeam
import Mathlib.Analysis.Calculus.LHopital

/-!
# Synchronized Euler height and Gamma Fisher contraction

Normalize the literal synchronized singleton valuation ray before taking the lossless boundary.
This produces a genuine geometric probability law on every valuation depth, not a selected large
depth and not an inverse recovery operator.  Its physical Euler half-height barycenter contracts
strictly, with derivative exactly minus twice its infinite-depth variance.

The main source-specific identity is valid at every positive aperture: the Gamma-sewn Fisher
curvature is sixteen times that physical height variance at doubled aperture plus the positive
two-state sewing Fisher term.  Thus the factor sixteen is forced by the literal half-height
calibration and aperture doubling; it is not fitted to the boundary coefficient.  At the lossless
boundary the same barycenter recovers both the forced quarter-prime seam and the next regular
coefficient, whose sixteen-fold value is the Gamma Fisher clock.

The Laurent coefficients of `1 / (1 - exp (-y))` are classical Bernoulli theory.  The content here
is their exact occurrence inside two independently constructed source objects and the positive-
aperture decomposition connecting them.  No Xi zero or RH-equivalent positivity assumption enters.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

private def synchronizedEulerBarycenterNumerator (y : ℝ) : ℝ :=
  y - 2 + (y + 2) * Real.exp (-y)

private theorem synchronizedEulerBarycenterNumerator_hasDerivAt (y : ℝ) :
    HasDerivAt synchronizedEulerBarycenterNumerator
      (1 - (y + 1) * Real.exp (-y)) y := by
  unfold synchronizedEulerBarycenterNumerator
  convert ((hasDerivAt_id y).sub_const 2).add
    (((hasDerivAt_id y).add_const 2).mul
      ((Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y))) using 1
  all_goals (simp only [Function.id_def, Function.comp_apply]; ring)

private theorem synchronizedEulerBarycenterNumeratorFirst_hasDerivAt (y : ℝ) :
    HasDerivAt (fun z : ℝ => 1 - (z + 1) * Real.exp (-z))
      (y * Real.exp (-y)) y := by
  convert (hasDerivAt_const (x := y) (c := (1 : ℝ))).sub
    (((hasDerivAt_id y).add_const 1).mul
      ((Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y))) using 1
  all_goals (simp only [Function.id_def, Function.comp_apply]; ring)

private theorem synchronizedEulerBarycenterNumeratorSecond_hasDerivAt (y : ℝ) :
    HasDerivAt (fun z : ℝ => z * Real.exp (-z))
      ((1 - y) * Real.exp (-y)) y := by
  convert (hasDerivAt_id y).mul
    ((Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y)) using 1
  all_goals (simp only [Function.id_def, Function.comp_apply]; ring)

private theorem tendsto_synchronizedEulerBarycenterNumerator_div_cube_zero :
    Tendsto (fun y : ℝ => synchronizedEulerBarycenterNumerator y / y ^ 3)
      (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
  have hthird : Tendsto
      (fun y : ℝ => ((1 - y) * Real.exp (-y)) / 6)
      (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
    have hcont : ContinuousAt
        (fun y : ℝ => ((1 - y) * Real.exp (-y)) / 6) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left inf_le_left
  have hsecond : Tendsto
      (fun y : ℝ => (y * Real.exp (-y)) / (6 * y))
      (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
    refine HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun y : ℝ => (1 - y) * Real.exp (-y))
      (g' := fun _y : ℝ => 6) ?_ ?_ ?_ ?_ ?_ hthird
    · exact Filter.Eventually.of_forall
        synchronizedEulerBarycenterNumeratorSecond_hasDerivAt
    · exact Filter.Eventually.of_forall fun y => by
        convert (hasDerivAt_id y).const_mul 6 using 1
        all_goals simp
    · exact Filter.Eventually.of_forall fun _ => by norm_num
    · have hcont : ContinuousAt (fun y : ℝ => y * Real.exp (-y)) 0 := by fun_prop
      simpa using hcont.tendsto.mono_left inf_le_left
    · have hcont : ContinuousAt (fun y : ℝ => 6 * y) 0 := by fun_prop
      simpa using hcont.tendsto.mono_left inf_le_left
  have hfirst : Tendsto
      (fun y : ℝ => (1 - (y + 1) * Real.exp (-y)) / (3 * y ^ 2))
      (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
    refine HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun y : ℝ => y * Real.exp (-y))
      (g' := fun y : ℝ => 6 * y) ?_ ?_ ?_ ?_ ?_ hsecond
    · exact Filter.Eventually.of_forall
        synchronizedEulerBarycenterNumeratorFirst_hasDerivAt
    · exact Filter.Eventually.of_forall fun y => by
        convert ((hasDerivAt_id y).pow 2).const_mul 3 using 1
        simp only [Function.id_def]
        ring
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [mem_compl_iff, mem_singleton_iff] at hy
      exact mul_ne_zero (by norm_num) hy
    · have hcont : ContinuousAt
          (fun y : ℝ => 1 - (y + 1) * Real.exp (-y)) 0 := by fun_prop
      simpa using hcont.tendsto.mono_left inf_le_left
    · have hcont : ContinuousAt (fun y : ℝ => 3 * y ^ 2) 0 := by fun_prop
      simpa using hcont.tendsto.mono_left inf_le_left
  refine HasDerivAt.lhopital_zero_nhdsNE
    (f' := fun y : ℝ => 1 - (y + 1) * Real.exp (-y))
    (g' := fun y : ℝ => 3 * y ^ 2) ?_ ?_ ?_ ?_ ?_ hfirst
  · exact Filter.Eventually.of_forall synchronizedEulerBarycenterNumerator_hasDerivAt
  · exact Filter.Eventually.of_forall fun y => hasDerivAt_pow 3 y
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [mem_compl_iff, mem_singleton_iff] at hy
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)
  · have hcont : ContinuousAt synchronizedEulerBarycenterNumerator 0 := by
      unfold synchronizedEulerBarycenterNumerator
      fun_prop
    simpa [synchronizedEulerBarycenterNumerator] using
      hcont.tendsto.mono_left inf_le_left
  · have hcont : ContinuousAt (fun y : ℝ => y ^ 3) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left inf_le_left

private theorem tendsto_one_sub_exp_neg_div_self_zero :
    Tendsto (fun y : ℝ => (1 - Real.exp (-y)) / y)
      (𝓝[≠] 0) (𝓝 1) := by
  have hderiv : HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) 1 0 := by
    convert (hasDerivAt_const (x := 0) (c := (1 : ℝ))).sub
      ((Real.hasDerivAt_exp (-0)).comp 0 (hasDerivAt_neg 0)) using 1
    all_goals norm_num
  rw [hasDerivAt_iff_tendsto_slope] at hderiv
  convert hderiv using 1
  funext y
  rw [slope_def_field]
  norm_num

private def synchronizedEulerUniversalRegularCoefficient (y : ℝ) : ℝ :=
  (1 / (2 * (1 - Real.exp (-y))) - 1 / (2 * y) - 1 / 4) / y

private theorem tendsto_synchronizedEulerUniversalRegularCoefficient_zero :
    Tendsto synchronizedEulerUniversalRegularCoefficient
      (𝓝[≠] 0) (𝓝 (1 / 24 : ℝ)) := by
  have hden : Tendsto
      (fun y : ℝ => 4 * ((1 - Real.exp (-y)) / y))
      (𝓝[≠] 0) (𝓝 (4 : ℝ)) := by
    simpa using tendsto_one_sub_exp_neg_div_self_zero.const_mul 4
  have hquot :=
    tendsto_synchronizedEulerBarycenterNumerator_div_cube_zero.div hden (by norm_num)
  have heq :
      (fun y : ℝ =>
          (synchronizedEulerBarycenterNumerator y / y ^ 3) /
            (4 * ((1 - Real.exp (-y)) / y))) =ᶠ[𝓝[≠] 0]
        synchronizedEulerUniversalRegularCoefficient := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [mem_compl_iff, mem_singleton_iff] at hy
    have hexp : 1 - Real.exp (-y) ≠ 0 := by
      intro h
      have heq : Real.exp (-y) = 1 := by linarith
      have := (Real.exp_eq_one_iff (-y)).mp heq
      exact hy (by linarith)
    unfold synchronizedEulerUniversalRegularCoefficient
      synchronizedEulerBarycenterNumerator
    field_simp [hy, hexp]
    ring
  have hfinal := hquot.congr' heq
  norm_num at hfinal ⊢
  exact hfinal

/-- Geometric common-depth law obtained after the synchronized singleton ray is normalized. -/
def gammaSewnSynchronizedEulerDepthProbability
    (x : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  (1 - xiMobiusContinuousApertureDiskNode x p) *
    xiMobiusContinuousApertureDiskNode x p ^ e

/-- All-depth barycenter of the literal Euler half-height over one synchronized prime ray. -/
def gammaSewnSynchronizedEulerHalfHeightBarycenter
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ) /
    (2 * (1 - xiMobiusContinuousApertureDiskNode x p))

/-- The depth law is not an auxiliary probability: it is the literal synchronized singleton ray
divided by its all-depth mass. -/
theorem gammaSewnSynchronizedEulerDepthProbability_eq_normalizedLcmRay
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) (e : ℕ) :
    gammaSewnSynchronizedEulerDepthProbability x p e =
      gammaSewnSynchronizedLcmRay x {p} e /
        gammaSewnSynchronizedLcmWeight x {p} := by
  have hmult := gammaSewnMobiusValuationContractionMultiplier_pos x p
  have htrans := xiTransversePrimeApertureDiskNode_pos 1 p
  have hden : 0 < 1 + xiTransversePrimeApertureDiskNode 1 p := by positivity
  rw [gammaSewnSynchronizedLcmWeight_singleton hx]
  simp only [gammaSewnSynchronizedLcmRay, Finset.prod_singleton]
  rw [gammaSewnMobiusContinuousApertureFeature,
    xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
  unfold gammaSewnSynchronizedEulerDepthProbability
  field_simp [hmult.ne', htrans.ne', hden.ne']

theorem hasSum_gammaSewnSynchronizedEulerDepthProbability_one
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    HasSum (fun e : ℕ => gammaSewnSynchronizedEulerDepthProbability x p e) 1 := by
  let q := xiMobiusContinuousApertureDiskNode x p
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos x p
  have hq1 : q < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hq0]
    exact hq1
  have hsum := (hasSum_geometric_of_norm_lt_one hqnorm).mul_left (1 - q)
  convert hsum using 1
  have hne : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.ne'
  field_simp [hne]

/-- The closed barycenter is not a chosen depth: it is the exact expectation over every
common valuation depth in the synchronized geometric source. -/
theorem hasSum_gammaSewnSynchronizedEulerDepthProbability_mul_halfHeight
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    HasSum (fun e : ℕ =>
      gammaSewnSynchronizedEulerDepthProbability x p e *
        xiGammaEulerBoundaryHalfHeight p e)
      (gammaSewnSynchronizedEulerHalfHeightBarycenter x p) := by
  let q := xiMobiusContinuousApertureDiskNode x p
  let L := Real.log (p : ℝ)
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos x p
  have hq1 : q < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hq0]
    exact hq1
  have hne : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.ne'
  have hweighted := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hqnorm
  have hgeom := hasSum_geometric_of_norm_lt_one (K := ℝ) hqnorm
  have hsum := hweighted.add hgeom
  have hscaled := hsum.mul_left ((1 - q) * (L / 2))
  convert hscaled using 1
  · funext e
    change (1 - q) * q ^ e * ((((e : ℝ) + 1) / 2) * L) =
      (1 - q) * (L / 2) * ((e : ℝ) * q ^ e + q ^ e)
    ring
  · unfold gammaSewnSynchronizedEulerHalfHeightBarycenter
    dsimp only [q, L]
    field_simp [hne]
    ring

theorem tsum_gammaSewnSynchronizedEulerDepthProbability_mul_halfHeight
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    (∑' e : ℕ,
      gammaSewnSynchronizedEulerDepthProbability x p e *
        xiGammaEulerBoundaryHalfHeight p e) =
      gammaSewnSynchronizedEulerHalfHeightBarycenter x p :=
  (hasSum_gammaSewnSynchronizedEulerDepthProbability_mul_halfHeight hx p).tsum_eq

private theorem two_mul_choose_two_add_eq_succ_sq (e : ℕ) :
    (2 : ℝ) * ((((e + 2).choose 2 : ℕ) : ℝ)) - ((e : ℝ) + 1) =
      ((e : ℝ) + 1) ^ 2 := by
  have hd : 2 ∣ (e + 2) * (e + 1) := by
    simpa [mul_comm, add_comm, add_left_comm, add_assoc] using
      (Nat.even_mul_succ_self (e + 1)).two_dvd
  have hn : 2 * (e + 2).choose 2 = (e + 2) * (e + 1) := by
    rw [Nat.choose_two_right]
    have hsub : e + 2 - 1 = e + 1 := by omega
    rw [hsub, Nat.mul_div_cancel' hd]
  have hncast : (2 : ℝ) * ((((e + 2).choose 2 : ℕ) : ℝ)) =
      (((e + 2) * (e + 1) : ℕ) : ℝ) := by exact_mod_cast hn
  rw [hncast]
  push_cast
  ring

private theorem hasSum_succ_sq_mul_geometric
    {q : ℝ} (hqnorm : ‖q‖ < 1) :
    HasSum (fun e : ℕ => ((e : ℝ) + 1) ^ 2 * q ^ e)
      ((1 + q) / (1 - q) ^ 3) := by
  have hchoose := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hqnorm
  have hweighted := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hqnorm
  have hgeom := hasSum_geometric_of_norm_lt_one (K := ℝ) hqnorm
  have hsucc := hweighted.add hgeom
  have hraw := (hchoose.mul_left 2).sub hsucc
  convert hraw using 1
  · funext e
    rw [← two_mul_choose_two_add_eq_succ_sq e]
    ring
  · have hq : q ≠ 1 := by
      intro h
      subst q
      norm_num at hqnorm
    have hne : 1 - q ≠ 0 := sub_ne_zero.mpr hq.symm
    field_simp [hne]
    ring

theorem hasSum_gammaSewnSynchronizedEulerDepthProbability_mul_halfHeight_sq
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    HasSum
      (fun e : ℕ =>
        gammaSewnSynchronizedEulerDepthProbability x p e *
          xiGammaEulerBoundaryHalfHeight p e ^ 2)
      (Real.log (p : ℝ) ^ 2 *
        (1 + xiMobiusContinuousApertureDiskNode x p) /
          (4 * (1 - xiMobiusContinuousApertureDiskNode x p) ^ 2)) := by
  let q := xiMobiusContinuousApertureDiskNode x p
  let L := Real.log (p : ℝ)
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos x p
  have hq1 : q < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hq0]
    exact hq1
  have hne : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.ne'
  have hsum := (hasSum_succ_sq_mul_geometric hqnorm).mul_left
    ((1 - q) * (L ^ 2 / 4))
  convert hsum using 1
  · funext e
    change (1 - q) * q ^ e * (((((e : ℝ) + 1) / 2) * L) ^ 2) =
      (1 - q) * (L ^ 2 / 4) * (((e : ℝ) + 1) ^ 2 * q ^ e)
    ring
  · dsimp only [q, L]
    field_simp [hne]

/-- Literal infinite-depth variance of the physical Euler half-height. -/
def gammaSewnSynchronizedEulerHalfHeightVariance
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  ∑' e : ℕ,
    gammaSewnSynchronizedEulerDepthProbability x p e *
      (xiGammaEulerBoundaryHalfHeight p e -
        gammaSewnSynchronizedEulerHalfHeightBarycenter x p) ^ 2

theorem gammaSewnSynchronizedEulerHalfHeightVariance_eq
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnSynchronizedEulerHalfHeightVariance x p =
      Real.log (p : ℝ) ^ 2 * xiMobiusContinuousApertureDiskNode x p /
        (4 * (1 - xiMobiusContinuousApertureDiskNode x p) ^ 2) := by
  let M := gammaSewnSynchronizedEulerHalfHeightBarycenter x p
  have hsecond :=
    hasSum_gammaSewnSynchronizedEulerDepthProbability_mul_halfHeight_sq hx p
  have hmean : HasSum
      (fun e : ℕ =>
        gammaSewnSynchronizedEulerDepthProbability x p e *
          xiGammaEulerBoundaryHalfHeight p e) M :=
    hasSum_gammaSewnSynchronizedEulerDepthProbability_mul_halfHeight hx p
  have hprob := hasSum_gammaSewnSynchronizedEulerDepthProbability_one hx p
  have hcombined :=
    (hsecond.sub (hmean.mul_left (2 * M))).add (hprob.mul_left (M ^ 2))
  have hq1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hne : 1 - xiMobiusContinuousApertureDiskNode x p ≠ 0 :=
    sub_ne_zero.mpr hq1.ne'
  unfold gammaSewnSynchronizedEulerHalfHeightVariance
  change (∑' e : ℕ,
      gammaSewnSynchronizedEulerDepthProbability x p e *
        (xiGammaEulerBoundaryHalfHeight p e - M) ^ 2) = _
  calc
    _ = ∑' e : ℕ,
        (gammaSewnSynchronizedEulerDepthProbability x p e *
            xiGammaEulerBoundaryHalfHeight p e ^ 2 -
          2 * M * (gammaSewnSynchronizedEulerDepthProbability x p e *
            xiGammaEulerBoundaryHalfHeight p e) +
          M ^ 2 * gammaSewnSynchronizedEulerDepthProbability x p e) := by
      apply tsum_congr
      intro e
      ring
    _ = Real.log (p : ℝ) ^ 2 *
          (1 + xiMobiusContinuousApertureDiskNode x p) /
            (4 * (1 - xiMobiusContinuousApertureDiskNode x p) ^ 2) -
        2 * M * M + M ^ 2 * 1 := hcombined.tsum_eq
    _ = Real.log (p : ℝ) ^ 2 * xiMobiusContinuousApertureDiskNode x p /
        (4 * (1 - xiMobiusContinuousApertureDiskNode x p) ^ 2) := by
      dsimp only [M]
      unfold gammaSewnSynchronizedEulerHalfHeightBarycenter
      field_simp [hne]
      ring

/-- Fisher term contributed by the two-state Gamma sewing variable. -/
def gammaSewnSewingBernoulliFisherCurvature
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  let q := xiMobiusContinuousApertureDiskNode x p
  4 * Real.log (p : ℝ) ^ 2 * q ^ 4 / (1 + q ^ 4) ^ 2

theorem gammaSewnSynchronizedEulerHalfHeightVariance_pos
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    0 < gammaSewnSynchronizedEulerHalfHeightVariance x p := by
  rw [gammaSewnSynchronizedEulerHalfHeightVariance_eq hx]
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hq0 := xiMobiusContinuousApertureDiskNode_pos x p
  have hq1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  exact div_pos (mul_pos (sq_pos_of_pos hL) hq0)
    (mul_pos (by norm_num) (sq_pos_of_pos (sub_pos.mpr hq1)))

theorem hasDerivAt_gammaSewnSynchronizedEulerHalfHeightBarycenter
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    HasDerivAt
      (fun y : ℝ => gammaSewnSynchronizedEulerHalfHeightBarycenter y p)
      (-2 * gammaSewnSynchronizedEulerHalfHeightVariance x p) x := by
  let q : ℝ → ℝ := fun y => xiMobiusContinuousApertureDiskNode y p
  let L := Real.log (p : ℝ)
  have hq : HasDerivAt q (-L * q x) x := by
    dsimp only [q, L]
    unfold xiMobiusContinuousApertureDiskNode
    convert (Real.hasDerivAt_exp (-x * Real.log (p : ℝ))).comp x
      ((hasDerivAt_neg x).mul_const (Real.log (p : ℝ))) using 1
    all_goals ring
  have hq1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hden : 2 * (1 - q x) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr hq1.ne')
  have hderiv := (hasDerivAt_const (x := x) (c := L)).div
    (((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub hq).const_mul 2) hden
  rw [gammaSewnSynchronizedEulerHalfHeightVariance_eq hx]
  change HasDerivAt (fun y : ℝ => L / (2 * (1 - q y)))
    (-2 * (L ^ 2 * q x / (4 * (1 - q x) ^ 2))) x
  convert hderiv using 1
  dsimp only [q, L]
  field_simp [sub_ne_zero.mpr hq1.ne']
  simp only [Pi.sub_apply]
  ring

/-- The all-depth physical Euler height barycenter contracts strictly throughout the positive
aperture chamber; its speed is exactly twice its infinite-depth height variance. -/
theorem gammaSewnSynchronizedEulerHalfHeightBarycenter_strictAntiOn_pos
    (p : Nat.Primes) :
    StrictAntiOn
      (fun x : ℝ => gammaSewnSynchronizedEulerHalfHeightBarycenter x p) (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi (𝕜 := ℝ) 0) ?_ ?_
  · intro x hx
    exact (hasDerivAt_gammaSewnSynchronizedEulerHalfHeightBarycenter hx p).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hxpos : 0 < x := hx
    rw [(hasDerivAt_gammaSewnSynchronizedEulerHalfHeightBarycenter hxpos p).deriv]
    nlinarith [gammaSewnSynchronizedEulerHalfHeightVariance_pos hxpos p]

/-- **Exact synchronized height--sewing decomposition.**  The full Gamma aperture Fisher
curvature is sixteen times the literal infinite-depth Euler half-height variance at doubled
aperture, plus the positive two-state Gamma-sewing Fisher term. -/
theorem gammaSewnMobiusApertureFisherCurvature_eq_sixteen_heightVariance_add_sewing
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnMobiusApertureFisherCurvature x p =
      16 * gammaSewnSynchronizedEulerHalfHeightVariance (2 * x) p +
        gammaSewnSewingBernoulliFisherCurvature x p := by
  rw [gammaSewnSynchronizedEulerHalfHeightVariance_eq (by positivity)]
  have hnode : xiMobiusContinuousApertureDiskNode (2 * x) p =
      xiMobiusContinuousApertureDiskNode x p ^ 2 := by
    rw [show 2 * x = x + x by ring, xiMobiusContinuousApertureDiskNode_add, pow_two]
  rw [hnode]
  have hq0 := xiMobiusContinuousApertureDiskNode_pos x p
  have hq1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hqsq : xiMobiusContinuousApertureDiskNode x p ^ 2 < 1 := by
    nlinarith [sq_lt_sq₀ hq0.le (by norm_num : (0 : ℝ) ≤ 1) |>.2 hq1]
  have hminus : 1 - xiMobiusContinuousApertureDiskNode x p ^ 2 ≠ 0 := by
    nlinarith
  have hplus : 1 + xiMobiusContinuousApertureDiskNode x p ^ 4 ≠ 0 := by positivity
  unfold gammaSewnMobiusApertureFisherCurvature
    gammaSewnSewingBernoulliFisherCurvature
  field_simp [hminus, hplus]
  ring

/-- The sewing channel has the finite lossless-boundary value `(log p)^2`. -/
theorem tendsto_gammaSewnSewingBernoulliFisherCurvature_zero
    (p : Nat.Primes) :
    Tendsto (fun x : ℝ => gammaSewnSewingBernoulliFisherCurvature x p)
      (𝓝[≠] 0) (𝓝 (Real.log (p : ℝ) ^ 2)) := by
  have hcont : ContinuousAt
      (fun x : ℝ => gammaSewnSewingBernoulliFisherCurvature x p) 0 := by
    let q : ℝ → ℝ := fun x => xiMobiusContinuousApertureDiskNode x p
    have hq : ContinuousAt q 0 := by
      dsimp only [q]
      unfold xiMobiusContinuousApertureDiskNode
      fun_prop
    have hden : (1 + q 0 ^ 4) ^ 2 ≠ 0 := by
      dsimp only [q, xiMobiusContinuousApertureDiskNode]
      norm_num
    exact (continuousAt_const.mul (hq.pow 4)).div
      ((continuousAt_const.add (hq.pow 4)).pow 2) hden
  convert hcont.tendsto.mono_left inf_le_left using 1
  unfold gammaSewnSewingBernoulliFisherCurvature
    xiMobiusContinuousApertureDiskNode
  norm_num

/-- After the universal pole is removed, the infinite Euler depth-variance channel has a
*negative* finite part.  The positive Fisher clock is created only after the larger sewing
boundary term is joined. -/
theorem tendsto_sixteen_heightVariance_two_mul_sub_pole_zero
    (p : Nat.Primes) :
    Tendsto
      (fun x : ℝ =>
        16 * gammaSewnSynchronizedEulerHalfHeightVariance (2 * x) p - 1 / x ^ 2)
      (𝓝[>] 0) (𝓝 ((-1 / 3 : ℝ) * Real.log (p : ℝ) ^ 2)) := by
  have hsubset : Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    exact ne_of_gt hx
  have hfilter : (𝓝[>] (0 : ℝ)) ≤ (𝓝[≠] 0) :=
    nhdsWithin_mono 0 hsubset
  have hgamma :=
    (tendsto_gammaSewnMobiusApertureRenormalizedFisherCurvature_zero p).mono_left hfilter
  have hsewing :=
    (tendsto_gammaSewnSewingBernoulliFisherCurvature_zero p).mono_left hfilter
  have hdiff := hgamma.sub hsewing
  have heq :
      (fun x : ℝ =>
          gammaSewnMobiusApertureRenormalizedFisherCurvature x p -
            gammaSewnSewingBernoulliFisherCurvature x p) =ᶠ[𝓝[>] 0]
        (fun x : ℝ =>
          16 * gammaSewnSynchronizedEulerHalfHeightVariance (2 * x) p - 1 / x ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [gammaSewnMobiusApertureRenormalizedFisherCurvature,
      gammaSewnMobiusApertureFisherCurvature_eq_sixteen_heightVariance_add_sewing hx p]
    ring
  have hfinal := hdiff.congr' heq
  convert hfinal using 1
  ring

/-- **Boundary 3:1 sewing law.**  Relative to the final Gamma Fisher clock, the regularized
infinite-depth height channel contributes `-1/2` and the sewing channel contributes `3/2`.
The clock is their signed join, not either positive term alone. -/
theorem gammaSewnSynchronizedEulerBoundary_height_sewing_three_to_one
    (p : Nat.Primes) :
    (-1 / 3 : ℝ) * Real.log (p : ℝ) ^ 2 =
        -(1 / 2 : ℝ) * gammaSewnMobiusApertureBoundaryFisherClock p ∧
      Real.log (p : ℝ) ^ 2 =
        (3 / 2 : ℝ) * gammaSewnMobiusApertureBoundaryFisherClock p := by
  unfold gammaSewnMobiusApertureBoundaryFisherClock
  constructor <;> ring

/-- First regular aperture coefficient after subtracting the universal depth pole and the
forced quarter-prime calibration seam. -/
def gammaSewnSynchronizedEulerBarycenterRegularCoefficient
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  (gammaSewnSynchronizedEulerHalfHeightBarycenter x p - 1 / (2 * x) -
      Real.log (p : ℝ) / 4) / x

theorem tendsto_gammaSewnSynchronizedEulerBarycenterRegularCoefficient_zero
    (p : Nat.Primes) :
    Tendsto
      (fun x : ℝ => gammaSewnSynchronizedEulerBarycenterRegularCoefficient x p)
      (𝓝[≠] 0) (𝓝 (Real.log (p : ℝ) ^ 2 / 24)) := by
  let L := Real.log (p : ℝ)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hL : 0 < L := Real.log_pos hp1
  have hscale : Tendsto (fun x : ℝ => x * L) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hid : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0) := tendsto_id
      simpa using (hid.mul_const L).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [mem_compl_iff, mem_singleton_iff] at hx ⊢
      exact mul_ne_zero hx hL.ne'
  have hscaled :=
    (tendsto_synchronizedEulerUniversalRegularCoefficient_zero.comp hscale).const_mul
      (L ^ 2)
  have heq :
      (fun x : ℝ =>
        L ^ 2 * synchronizedEulerUniversalRegularCoefficient (x * L)) =ᶠ[𝓝[≠] 0]
        (fun x : ℝ => gammaSewnSynchronizedEulerBarycenterRegularCoefficient x p) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [mem_compl_iff, mem_singleton_iff] at hx
    have hnode : 1 - xiMobiusContinuousApertureDiskNode x p ≠ 0 := by
      unfold xiMobiusContinuousApertureDiskNode
      intro h
      have he : Real.exp (-x * Real.log (p : ℝ)) = 1 := by linarith
      have hz := (Real.exp_eq_one_iff _).mp he
      exact hx (by dsimp only [L] at hL ⊢; nlinarith)
    have hlog : Real.log (p : ℝ) ≠ 0 := by
      dsimp only [L] at hL
      exact hL.ne'
    unfold gammaSewnSynchronizedEulerBarycenterRegularCoefficient
      gammaSewnSynchronizedEulerHalfHeightBarycenter
      synchronizedEulerUniversalRegularCoefficient
      xiMobiusContinuousApertureDiskNode
    dsimp only [L]
    field_simp [hx, hlog, hnode]
  have hfinal := hscaled.congr' heq
  simpa only [L, div_eq_mul_inv, one_mul] using hfinal

/-- The finite part of the all-depth barycenter is exactly the quarter-prime seam independently
forced by the literal Euler phase calibration. -/
theorem tendsto_gammaSewnSynchronizedEulerHalfHeightBarycenter_sub_pole_zero
    (p : Nat.Primes) :
    Tendsto
      (fun x : ℝ =>
        gammaSewnSynchronizedEulerHalfHeightBarycenter x p - 1 / (2 * x))
      (𝓝[≠] 0) (𝓝 (Real.log (p : ℝ) / 4)) := by
  have hid : Tendsto (fun x : ℝ => x) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hrem := hid.mul
    (tendsto_gammaSewnSynchronizedEulerBarycenterRegularCoefficient_zero p)
  have hsum := hrem.const_add (Real.log (p : ℝ) / 4)
  have heq :
      (fun x : ℝ =>
          Real.log (p : ℝ) / 4 +
            x * gammaSewnSynchronizedEulerBarycenterRegularCoefficient x p) =ᶠ[𝓝[≠] 0]
        (fun x : ℝ =>
          gammaSewnSynchronizedEulerHalfHeightBarycenter x p - 1 / (2 * x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [mem_compl_iff, mem_singleton_iff] at hx
    unfold gammaSewnSynchronizedEulerBarycenterRegularCoefficient
    field_simp [hx]
    ring
  have hfinal := hsum.congr' heq
  norm_num at hfinal ⊢
  exact hfinal

/-- **Synchronized Euler--Fisher coefficient identity.**  Sixteen times the first regular
coefficient of the all-depth physical Euler height barycenter is exactly the finite Gamma-sewn
Fisher clock. -/
theorem tendsto_sixteen_mul_gammaSewnSynchronizedEulerBarycenterRegularCoefficient_fisherClock
    (p : Nat.Primes) :
    Tendsto
      (fun x : ℝ =>
        16 * gammaSewnSynchronizedEulerBarycenterRegularCoefficient x p)
      (𝓝[≠] 0) (𝓝 (gammaSewnMobiusApertureBoundaryFisherClock p)) := by
  have h :=
    (tendsto_gammaSewnSynchronizedEulerBarycenterRegularCoefficient_zero p).const_mul 16
  convert h using 1
  unfold gammaSewnMobiusApertureBoundaryFisherClock
  ring

end

end RHTower
