import GaloisForLFunctions.HyperbolicArakelovTheory.ThePositiveSquareRootOfTheAdelicPrecision
import GaloisForLFunctions.HTGeometry.LieTrotterProduct
import GaloisForLFunctions.SurfaceOfSpecZ.HyperbolicQuotientsJetCarriersAndCoupledDamping
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The hyperbolic Green kernel of the weighted adelic carrier

The positive square root of the actual finite-place precision determines
the standard hyperbolic branch. Its operator-valued radial kernel is
`exp(−rS)/(4π sinh r)`, with Robin part `−S/(4π)`.
-/

set_option autoImplicit false
noncomputable section
open Filter NormedSpace
open scoped Classical BigOperators Topology InnerProductSpace

namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic SurfaceOfSpecZ

private instance : Nontrivial ChargeSpace := by
  let y : FiniteVertices := ⟨fun p => baseVertex p, by simp⟩
  refine ⟨⟨lp.single 2 y (1 : ℝ), 0, ?_⟩⟩
  intro h
  have he := congrArg (fun f : ChargeSpace => f y) h
  simp at he

def hyperbolicEvolution (r : ℝ) : ChargeOperator := exp (r • (-hyperbolicRoot))

private theorem exp_scalar_identity (r : ℝ) :
    exp (r • (1 : ChargeOperator)) = Real.exp r • (1 : ChargeOperator) := by
  rw [← Algebra.algebraMap_eq_smul_one, ← NormedSpace.algebraMap_exp_comm r,
    Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one]

theorem hyperbolicEvolution_factor (r : ℝ) :
    hyperbolicEvolution r = Real.exp (-r * rootScale) • exp (r • rootRemainder) := by
  letI : NormedAlgebra ℚ ChargeOperator := NormedAlgebra.restrictScalars ℚ ℝ ChargeOperator
  have he : r • (-hyperbolicRoot) =
      (-r * rootScale) • (1 : ChargeOperator) + r • rootRemainder := by
    rw [hyperbolicRoot]
    module
  have hc : Commute ((-r * rootScale) • (1 : ChargeOperator)) (r • rootRemainder) :=
    ((Commute.one_left rootRemainder).smul_right r).smul_left _
  rw [hyperbolicEvolution, he, exp_add_of_commute hc, exp_scalar_identity,
    smul_mul_assoc, one_mul]

theorem hyperbolicEvolution_zero : hyperbolicEvolution 0 = 1 := by
  simp only [hyperbolicEvolution, zero_smul, exp_zero]

theorem hasDerivAt_hyperbolicEvolution (r : ℝ) :
    HasDerivAt hyperbolicEvolution (-hyperbolicRoot * hyperbolicEvolution r) r :=
  hasDerivAt_exp_smul_const' (-hyperbolicRoot) r

theorem hyperbolicEvolution_symmetric (r : ℝ) (f g : ChargeSpace) :
    ⟪hyperbolicEvolution r f, g⟫_ℝ = ⟪f, hyperbolicEvolution r g⟫_ℝ := by
  have hs : IsSelfAdjoint hyperbolicRoot :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hyperbolicRoot_symmetric
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (((IsSelfAdjoint.all r).smul hs.neg).exp)) f g

theorem hyperbolicEvolution_norm_le {r : ℝ} (hr : 0 ≤ r) :
    ‖hyperbolicEvolution r‖ ≤ Real.exp (-r / 2) := by
  rw [hyperbolicEvolution_factor, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-r * rootScale) * Real.exp ‖r • rootRemainder‖ :=
      mul_le_mul_of_nonneg_left (HTGeometry.norm_exp_le_exp_norm _)
        (Real.exp_pos _).le
    _ = Real.exp (-r * rootScale + r * ‖rootRemainder‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, ← Real.exp_add]
    _ ≤ Real.exp (-r / 2) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left rootRemainder_norm_le hr
      unfold rootRadius at h
      linarith only [h]

private theorem remainder_pow_nonneg (n : ℕ) (f : ChargeSpace) (hf : ∀ y, 0 ≤ f y)
    (y : FiniteVertices) : 0 ≤ (rootRemainder ^ n) f y := by
  induction n generalizing f y with
  | zero => exact hf y
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      exact rootRemainder_nonneg _ (fun z => ih f hf z) y

private theorem exp_remainder_apply (r : ℝ) (f : ChargeSpace) (y : FiniteVertices) :
    exp (r • rootRemainder) f y =
      ∑' n : ℕ, (n.factorial : ℝ)⁻¹ * r ^ n * (rootRemainder ^ n) f y := by
  let ev : ChargeOperator →L[ℝ] ℝ :=
    (lp.evalCLM ℝ (fun _ : FiniteVertices => ℝ) 2 y).comp
      (ContinuousLinearMap.apply ℝ ChargeSpace f)
  have hs := expSeries_summable' (𝕂 := ℝ) (r • rootRemainder)
  rw [exp_eq_tsum ℝ]
  change ev (∑' n : ℕ, (n.factorial : ℝ)⁻¹ • (r • rootRemainder) ^ n) = _
  rw [ev.map_tsum hs]
  apply tsum_congr
  intro n
  change ((n.factorial : ℝ)⁻¹ • (r • rootRemainder) ^ n) f y = _
  rw [smul_pow]
  change (n.factorial : ℝ)⁻¹ * (r ^ n * (rootRemainder ^ n) f y) = _
  ring

/-- Positivity comes from the positive remainder series, not merely self-adjointness. -/
theorem hyperbolicEvolution_nonneg {r : ℝ} (hr : 0 ≤ r)
    (f : ChargeSpace) (hf : ∀ y, 0 ≤ f y) (y : FiniteVertices) :
    0 ≤ hyperbolicEvolution r f y := by
  rw [hyperbolicEvolution_factor]
  change 0 ≤ Real.exp (-r * rootScale) * (exp (r • rootRemainder) f y)
  rw [exp_remainder_apply]
  exact mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun n =>
    mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg hr n))
      (remainder_pow_nonneg n f hf y))

/-- The standard-branch radial kernel on the full mixed carrier. -/
def mixedGreen (r : ℝ) : ChargeOperator := hyperbolicGreen 1 r • hyperbolicEvolution r

/-- The standard hyperbolic branch has uniform decay on the full adelic charge space. -/
theorem mixedGreen_norm_le {r : ℝ} (hr : 0 < r) :
    ‖mixedGreen r‖ ≤ Real.exp (-r / 2) / (4 * Real.pi * Real.sinh r) := by
  have hg : 0 ≤ hyperbolicGreen 1 r := by
    unfold hyperbolicGreen
    exact div_nonneg (Real.exp_pos _).le
      (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (Real.sinh_pos_iff.mpr hr).le)
  rw [mixedGreen, norm_smul, Real.norm_eq_abs, abs_of_nonneg hg]
  calc
    _ ≤ hyperbolicGreen 1 r * Real.exp (-r / 2) :=
      mul_le_mul_of_nonneg_left (hyperbolicEvolution_norm_le hr.le) hg
    _ = _ := by simp only [hyperbolicGreen, sub_self, neg_zero, zero_mul, Real.exp_zero]; ring

theorem mixedGreen_symmetric (r : ℝ) (f g : ChargeSpace) :
    ⟪mixedGreen r f, g⟫_ℝ = ⟪f, mixedGreen r g⟫_ℝ := by
  change ⟪hyperbolicGreen 1 r • hyperbolicEvolution r f, g⟫_ℝ =
    ⟪f, hyperbolicGreen 1 r • hyperbolicEvolution r g⟫_ℝ
  rw [real_inner_smul_left, real_inner_smul_right, hyperbolicEvolution_symmetric]

def hyperbolicPrecision : ChargeOperator := (edge + 1 / 4) • 1 - adjacencyOperator

private def freeFirst (r : ℝ) : ℝ := radialMode' 0 r / (4 * Real.pi)
private def freeSecond (r : ℝ) : ℝ := radialMode'' 0 r / (4 * Real.pi)
private def evolutionFirst (r : ℝ) : ChargeOperator := -hyperbolicRoot * hyperbolicEvolution r

private theorem hasDerivAt_freeFactor {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (hyperbolicGreen 1) (freeFirst r) r := by
  rw [hyperbolicGreen_eq_radialMode]
  simpa only [sub_self, freeFirst] using
    (hasDerivAt_radialMode 0 (by rwa [ne_eq, Real.sinh_eq_zero])).div_const (4 * Real.pi)

private theorem hasDerivAt_freeFirst {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt freeFirst (freeSecond r) r :=
  (hasDerivAt_radialMode' 0 (by rwa [ne_eq, Real.sinh_eq_zero])).div_const (4 * Real.pi)

private theorem hasDerivAt_evolutionFirst (r : ℝ) :
    HasDerivAt evolutionFirst (hyperbolicPrecision * hyperbolicEvolution r) r := by
  have h := (hasDerivAt_hyperbolicEvolution r).const_mul (-hyperbolicRoot)
  apply h.congr_deriv
  rw [← mul_assoc, neg_mul_neg, hyperbolicRoot_squared]
  rfl

private def mixedFirst (r : ℝ) : ChargeOperator :=
  freeFirst r • hyperbolicEvolution r + hyperbolicGreen 1 r • evolutionFirst r

private def mixedSecond (r : ℝ) : ChargeOperator :=
  (freeSecond r • hyperbolicEvolution r + freeFirst r • evolutionFirst r) +
    (freeFirst r • evolutionFirst r + hyperbolicGreen 1 r •
      (hyperbolicPrecision * hyperbolicEvolution r))

private theorem hasDerivAt_mixedGreen {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt mixedGreen (mixedFirst r) r := by
  exact ((hasDerivAt_freeFactor hr).smul (hasDerivAt_hyperbolicEvolution r)).congr_deriv
    (by unfold mixedFirst evolutionFirst; module)

private theorem hasDerivAt_mixedFirst {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt mixedFirst (mixedSecond r) r := by
  exact (((hasDerivAt_freeFirst hr).smul (hasDerivAt_hyperbolicEvolution r)).add
    ((hasDerivAt_freeFactor hr).smul (hasDerivAt_evolutionFirst r))).congr_deriv
      (by unfold mixedSecond evolutionFirst; module)

private theorem free_radial_identities {r : ℝ} (hr : r ≠ 0) :
    freeSecond r + 2 * (Real.cosh r / Real.sinh r) * freeFirst r = -hyperbolicGreen 1 r ∧
    2 * freeFirst r + 2 * (Real.cosh r / Real.sinh r) * hyperbolicGreen 1 r = 0 := by
  have hs : Real.sinh r ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
  constructor <;>
    norm_num [freeFirst, freeSecond, radialMode', radialMode'', hyperbolicGreen] <;>
    field_simp [hs, Real.pi_ne_zero] <;> ring

/-- The radial equation contains the original all-prime adjacency on the adelic fibre. -/
theorem mixedGreen_radial {r : ℝ} (hr : r ≠ 0) :
    deriv (deriv mixedGreen) r + (2 * (Real.cosh r / Real.sinh r)) • deriv mixedGreen r =
      (hyperbolicPrecision - 1) * mixedGreen r := by
  have he : deriv mixedGreen =ᶠ[𝓝 r] mixedFirst := by
    filter_upwards [isOpen_ne.mem_nhds hr] with t ht
    exact (hasDerivAt_mixedGreen ht).deriv
  rw [he.deriv_eq, (hasDerivAt_mixedFirst hr).deriv, (hasDerivAt_mixedGreen hr).deriv]
  obtain ⟨hscalar, hcancel⟩ := free_radial_identities hr
  calc
    _ = (freeSecond r + 2 * (Real.cosh r / Real.sinh r) * freeFirst r) •
        hyperbolicEvolution r +
        (2 * freeFirst r + 2 * (Real.cosh r / Real.sinh r) * hyperbolicGreen 1 r) •
          evolutionFirst r +
        hyperbolicGreen 1 r • (hyperbolicPrecision * hyperbolicEvolution r) := by
      unfold mixedFirst mixedSecond
      module
    _ = (hyperbolicPrecision - 1) * mixedGreen r := by
      rw [hscalar, hcancel, zero_smul, add_zero, mixedGreen, mul_smul_comm, sub_mul, one_mul]
      module

/-- The unit Newtonian coefficient is the identity on the actual adelic charge space. -/
theorem tendsto_mixedGreen_source :
    Tendsto (fun r : ℝ => (4 * Real.pi * r) • mixedGreen r) (𝓝[≠] 0) (𝓝 1) := by
  have he : Tendsto hyperbolicEvolution (𝓝[≠] 0) (𝓝 (1 : ChargeOperator)) := by
    simpa only [hyperbolicEvolution_zero] using
      (hasDerivAt_hyperbolicEvolution 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [mixedGreen, smul_smul, one_smul] using
    (tendsto_mul_hyperbolicGreen 1).smul he

private theorem mixedGreen_flux {r : ℝ} (hr : r ≠ 0) :
    (-(4 * Real.pi * Real.sinh r ^ 2)) • deriv mixedGreen r =
      Real.cosh r • hyperbolicEvolution r +
        Real.sinh r • (hyperbolicRoot * hyperbolicEvolution r) := by
  have hs : Real.sinh r ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
  have h₁ : -(4 * Real.pi * Real.sinh r ^ 2) * freeFirst r = Real.cosh r := by
    norm_num [freeFirst, radialMode']
    field_simp [hs, Real.pi_ne_zero]
  have h₂ : -(4 * Real.pi * Real.sinh r ^ 2) * hyperbolicGreen 1 r = -Real.sinh r := by
    norm_num [hyperbolicGreen]
    field_simp [hs, Real.pi_ne_zero]
  rw [(hasDerivAt_mixedGreen hr).deriv, mixedFirst, smul_add, smul_smul, smul_smul, h₁, h₂]
  unfold evolutionFirst
  rw [neg_mul]
  module

/-- The inward radial flux tends to the unit source on the full adelic fibre. -/
theorem tendsto_mixedGreen_flux :
    Tendsto (fun r : ℝ => (-(4 * Real.pi * Real.sinh r ^ 2)) • deriv mixedGreen r)
      (𝓝[≠] 0) (𝓝 (1 : ChargeOperator)) := by
  have he : Tendsto hyperbolicEvolution (𝓝[≠] 0) (𝓝 (1 : ChargeOperator)) := by
    simpa only [hyperbolicEvolution_zero] using
      (hasDerivAt_hyperbolicEvolution 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hc : Tendsto Real.cosh (𝓝[≠] (0 : ℝ)) (𝓝 (Real.cosh 0)) :=
    (Real.continuous_cosh.tendsto 0).mono_left nhdsWithin_le_nhds
  have hs : Tendsto Real.sinh (𝓝[≠] (0 : ℝ)) (𝓝 (Real.sinh 0)) :=
    (Real.continuous_sinh.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := (hc.smul he).add (hs.smul ((tendsto_const_nhds (x := hyperbolicRoot)).mul he))
  simp only [Real.cosh_zero, Real.sinh_zero, one_smul, zero_smul, add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (mixedGreen_flux (by simpa only [Set.mem_compl_singleton_iff] using hr)).symm

private theorem tendsto_freeFactor_robin :
    Tendsto (fun r : ℝ => hyperbolicGreen 1 r - 1 / (4 * Real.pi * r))
      (𝓝[≠] 0) (𝓝 0) := by
  have h := (tendsto_freeSpace_robin (1 : ℝ)).div_const (2 * Real.pi)
  simp only [sub_self, zero_div] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : r ≠ 0 := by simpa only [Set.mem_compl_singleton_iff] using hr
  field_simp [Real.pi_ne_zero, hr0]
  ring

private theorem tendsto_radius_freeFactor :
    Tendsto (fun r : ℝ => r * hyperbolicGreen 1 r)
      (𝓝[≠] 0) (𝓝 (1 / (4 * Real.pi))) := by
  have h := (tendsto_mul_hyperbolicGreen 1).div_const (4 * Real.pi)
  refine h.congr fun r => ?_
  field_simp [Real.pi_ne_zero]

/-- The finite part is forced by the square root of the actual coupled precision. -/
theorem tendsto_mixedGreen_robin :
    Tendsto (fun r : ℝ => mixedGreen r - (1 / (4 * Real.pi * r)) • (1 : ChargeOperator))
      (𝓝[≠] 0) (𝓝 ((-(1 / (4 * Real.pi))) • hyperbolicRoot)) := by
  have hd := hasDerivAt_hyperbolicEvolution 0
  rw [hyperbolicEvolution_zero, mul_one] at hd
  have he : Tendsto (fun r : ℝ => r⁻¹ • (hyperbolicEvolution r - 1))
      (𝓝[≠] 0) (𝓝 (-hyperbolicRoot)) := by
    have hslope := hasDerivAt_iff_tendsto_slope.mp hd
    change Tendsto (fun r => slope hyperbolicEvolution 0 r)
      (𝓝[≠] 0) (𝓝 (-hyperbolicRoot)) at hslope
    simpa only [slope_def_module, sub_zero, hyperbolicEvolution_zero] using
      hslope
  have h := (tendsto_freeFactor_robin.smul
    (tendsto_const_nhds (x := (1 : ChargeOperator)))).add
      (tendsto_radius_freeFactor.smul he)
  simp only [zero_smul, zero_add, smul_neg, ← neg_smul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : r ≠ 0 := by simpa only [Set.mem_compl_singleton_iff] using hr
  rw [smul_smul, show r * hyperbolicGreen 1 r * r⁻¹ = hyperbolicGreen 1 r by
    field_simp [hr0]]
  rw [mixedGreen]
  module

def mixedGreenEntry (r : ℝ) (x y : FiniteVertices) : ℝ :=
  mixedGreen r (lp.single 2 x (1 : ℝ)) y

def mixedRobinEntry (x y : FiniteVertices) : ℝ :=
  -(1 / (4 * Real.pi)) * hyperbolicRoot (lp.single 2 x (1 : ℝ)) y

private theorem single_charge_nonneg (x y : FiniteVertices) :
    0 ≤ (lp.single 2 x (1 : ℝ) : ChargeSpace) y := by
  by_cases h : y = x
  · subst y
    rw [lp.single_apply_self]
    norm_num
  · simpa only [lp.single_apply_ne (E := fun _ : FiniteVertices => ℝ) 2 x 1 h]
      using (le_refl (0 : ℝ))

private theorem single_charge_eq_pointMass (x y : FiniteVertices) :
    (lp.single 2 x (1 : ℝ) : ChargeSpace) y = pointMass x y := by
  by_cases h : x = y
  · subst y
    rw [lp.single_apply_self, pointMass, if_pos rfl]
  · rw [lp.single_apply_ne (E := fun _ : FiniteVertices => ℝ) 2 x 1 (Ne.symm h),
      pointMass, if_neg h]

theorem tendsto_mixedGreenEntry_regularized (x y : FiniteVertices) :
    Tendsto (fun r : ℝ => mixedGreenEntry r x y -
      (1 / (4 * Real.pi * r)) * pointMass x y)
      (𝓝[≠] 0) (𝓝 (mixedRobinEntry x y)) := by
  let ev : ChargeOperator →L[ℝ] ℝ :=
    (lp.evalCLM ℝ (fun _ : FiniteVertices => ℝ) 2 y).comp
      (ContinuousLinearMap.apply ℝ ChargeSpace (lp.single 2 x (1 : ℝ)))
  have h := (ev.continuous.tendsto _).comp tendsto_mixedGreen_robin
  change Tendsto (fun r : ℝ => mixedGreenEntry r x y -
      (1 / (4 * Real.pi * r)) * (lp.single 2 x (1 : ℝ) : ChargeSpace) y)
    (𝓝[≠] 0) (𝓝 (mixedRobinEntry x y)) at h
  simpa only [single_charge_eq_pointMass] using h

theorem mixedGreenEntry_symm (r : ℝ) (x y : FiniteVertices) :
    mixedGreenEntry r x y = mixedGreenEntry r y x := by
  have h := mixedGreen_symmetric r (lp.single 2 x (1 : ℝ)) (lp.single 2 y (1 : ℝ))
  rw [lp.inner_single_right, lp.inner_single_left] at h
  change 1 * mixedGreenEntry r x y = mixedGreenEntry r y x * 1 at h
  simpa only [one_mul, mul_one] using h

theorem mixedRobinEntry_symm (x y : FiniteVertices) : mixedRobinEntry x y = mixedRobinEntry y x := by
  have h := hyperbolicRoot_symmetric (lp.single 2 x (1 : ℝ)) (lp.single 2 y (1 : ℝ))
  rw [lp.inner_single_right, lp.inner_single_left] at h
  change 1 * hyperbolicRoot (lp.single 2 x (1 : ℝ)) y =
    hyperbolicRoot (lp.single 2 y (1 : ℝ)) x * 1 at h
  simp only [one_mul, mul_one] at h
  exact congrArg (fun t => -(1 / (4 * Real.pi)) * t) h

theorem mixedGreenEntry_nonneg {r : ℝ} (hr : 0 < r) (x y : FiniteVertices) :
    0 ≤ mixedGreenEntry r x y := by
  have hs := (Real.sinh_pos_iff.mpr hr).le
  have hg : 0 ≤ hyperbolicGreen 1 r := by
    unfold hyperbolicGreen
    exact div_nonneg (Real.exp_pos _).le
      (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hs)
  change 0 ≤ hyperbolicGreen 1 r * hyperbolicEvolution r (lp.single 2 x (1 : ℝ)) y
  exact mul_nonneg hg (hyperbolicEvolution_nonneg hr.le _ (single_charge_nonneg x) y)

/-- Distinct adelic fibres have a finite, nonnegative Green value at archimedean collision. -/
theorem mixedRobinEntry_off_diagonal {x y : FiniteVertices} (hxy : x ≠ y) :
    mixedRobinEntry x y =
      (1 / (4 * Real.pi)) * rootRemainder (lp.single 2 x (1 : ℝ)) y := by
  change -(1 / (4 * Real.pi)) *
    (rootScale * (lp.single 2 x (1 : ℝ) : ChargeSpace) y -
      rootRemainder (lp.single 2 x (1 : ℝ)) y) = _
  rw [lp.single_apply_ne (E := fun _ : FiniteVertices => ℝ) 2 x 1 hxy.symm]
  ring

theorem mixedRobinEntry_off_diagonal_nonneg {x y : FiniteVertices} (hxy : x ≠ y) :
    0 ≤ mixedRobinEntry x y := by
  rw [mixedRobinEntry_off_diagonal hxy]
  exact mul_nonneg (by positivity)
    (rootRemainder_nonneg _ (single_charge_nonneg x) y)

theorem tendsto_mixedGreenEntry_collision {x y : FiniteVertices} (hxy : x ≠ y) :
    Tendsto (fun r : ℝ => mixedGreenEntry r x y) (𝓝[≠] 0) (𝓝 (mixedRobinEntry x y)) := by
  simpa only [pointMass, if_neg hxy, mul_zero, sub_zero] using
    tendsto_mixedGreenEntry_regularized x y

/-- At zero archimedean distance use the finite part, including between distinct fibres. -/
def regularizedMixedEntry (r : ℝ) (x y : FiniteVertices) : ℝ :=
  if r = 0 then mixedRobinEntry x y else mixedGreenEntry r x y

def regularizedMixedKernel (x y : GlobalSpace) : ℝ :=
  regularizedMixedEntry (h3Dist x.1 y.1) x.2 y.2

#print axioms hyperbolicEvolution_norm_le
#print axioms hyperbolicEvolution_nonneg
#print axioms mixedGreen_norm_le
#print axioms mixedGreenEntry_symm
#print axioms mixedGreenEntry_nonneg
#print axioms mixedGreen_radial
#print axioms tendsto_mixedGreen_source
#print axioms tendsto_mixedGreen_flux
#print axioms tendsto_mixedGreen_robin
#print axioms tendsto_mixedGreenEntry_collision

end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
