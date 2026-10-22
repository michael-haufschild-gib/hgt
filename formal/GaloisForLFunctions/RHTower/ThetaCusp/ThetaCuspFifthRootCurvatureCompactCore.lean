import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFifthRootCurvatureCofinalChordReserve
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartz

/-!
# Compact-core reduction for modular-center theta C5

The completed source and all of its ordinary derivatives decay faster than
the polynomial weights appearing in the fifth-root numerator.  This gives the
exact cofinal limit

`C5(0,t) -> 24 * P(0,0)^(2 : ℕ) > 0`.

Together with the already-proved strict coalesced C5 chamber, the global
modular-center problem is therefore equivalent to positivity on one compact
annulus.  Both endpoints are qualitative existence witnesses: no numerical
cutoff or computation enters the proof.
-/

open Real Set Filter Topology

namespace RHTower

noncomputable section

theorem tendsto_pow_mul_iteratedDeriv_thetaCuspFullSource_atTop_zero
    (k m : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * iteratedDeriv m thetaCuspFullSource x)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖x ^ k * iteratedDeriv m thetaCuspFullSource x‖ ≤
        thetaCuspDerivativeExpConstant m * (x ^ k * Real.exp (-x)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx k)]
    have hder := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg m hx
    have hpow : 0 ≤ x ^ k := pow_nonneg hx k
    calc
      x ^ k * |iteratedDeriv m thetaCuspFullSource x| ≤
          x ^ k * (thetaCuspDerivativeExpConstant m * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left hder hpow
      _ = thetaCuspDerivativeExpConstant m * (x ^ k * Real.exp (-x)) := by ring
  have hmajor : Tendsto
      (fun x : ℝ => thetaCuspDerivativeExpConstant m *
        (x ^ k * Real.exp (-x))) atTop (𝓝 0) := by
    simpa using
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k |>.const_mul
        (thetaCuspDerivativeExpConstant m)
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hbound hmajor

theorem thetaCuspReflectedSourceProduct_zero_eq_fullSource_sq (t : ℝ) :
    thetaCuspReflectedSourceProduct 0 t = thetaCuspFullSource t ^ (2 : ℕ) := by
  unfold thetaCuspReflectedSourceProduct
  simp only [zero_add, zero_sub]
  rw [thetaCuspFullSource_neg]
  ring

private theorem hasDerivAt_thetaCuspFullSource_iterated_one (t : ℝ) :
    HasDerivAt thetaCuspFullSource
      (iteratedDeriv 1 thetaCuspFullSource t) t := by
  simpa only [iteratedDeriv_one] using
    (contDiff_thetaCuspFullSource.differentiable (by simp) t).hasDerivAt

private theorem hasDerivAt_thetaCuspFullSource_iterated_one_two (t : ℝ) :
    HasDerivAt (iteratedDeriv 1 thetaCuspFullSource)
      (iteratedDeriv 2 thetaCuspFullSource t) t := by
  have hd :=
    (contDiff_thetaCuspFullSource.differentiable_iteratedDeriv 1 (by simp)) t
  refine hd.hasDerivAt.congr_deriv ?_
  change deriv (iteratedDeriv 1 thetaCuspFullSource) t =
    iteratedDeriv 2 thetaCuspFullSource t
  conv_rhs =>
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ]

theorem thetaCuspReflectedSourceDecayFlux_zero_eq_fullSource_jets
    (t : ℝ) :
    thetaCuspReflectedSourceDecayFlux 0 t =
      -2 * thetaCuspFullSource t * iteratedDeriv 1 thetaCuspFullSource t := by
  have hsource := hasDerivAt_thetaCuspFullSource_iterated_one t
  have hsquare := hsource.pow 2
  have hlocal :
      thetaCuspReflectedSourceProduct 0 =ᶠ[nhds t]
        thetaCuspFullSource ^ (2 : ℕ) := by
    exact Filter.Eventually.of_forall fun s => by
      rw [thetaCuspReflectedSourceProduct_zero_eq_fullSource_sq]
      rfl
  have hproduct := hasDerivAt_thetaCuspReflectedSourceProduct 0 t
  have heq := hproduct.unique (hsquare.congr_of_eventuallyEq hlocal)
  norm_num at heq
  rw [iteratedDeriv_one]
  linarith

theorem thetaCuspReflectedSourceDecayFluxCurvature_zero_eq_fullSource_jets
    (t : ℝ) :
    thetaCuspReflectedSourceDecayFluxCurvature 0 t =
      -2 * (iteratedDeriv 1 thetaCuspFullSource t ^ (2 : ℕ) +
        thetaCuspFullSource t * iteratedDeriv 2 thetaCuspFullSource t) := by
  let Q : ℝ → ℝ := fun s =>
    -2 * thetaCuspFullSource s * iteratedDeriv 1 thetaCuspFullSource s
  have hQ : HasDerivAt Q
      (-2 * (iteratedDeriv 1 thetaCuspFullSource t ^ (2 : ℕ) +
        thetaCuspFullSource t * iteratedDeriv 2 thetaCuspFullSource t)) t := by
    have hraw :=
      (hasDerivAt_thetaCuspFullSource_iterated_one t).mul
        (hasDerivAt_thetaCuspFullSource_iterated_one_two t) |>.const_mul (-2)
    have hraw' : HasDerivAt
        (fun y => -2 *
          (thetaCuspFullSource * iteratedDeriv 1 thetaCuspFullSource) y)
        (-2 * (iteratedDeriv 1 thetaCuspFullSource t ^ (2 : ℕ) +
          thetaCuspFullSource t * iteratedDeriv 2 thetaCuspFullSource t)) t :=
      hraw.congr_deriv (by ring)
    change HasDerivAt
      (fun s : ℝ => -2 * thetaCuspFullSource s *
        iteratedDeriv 1 thetaCuspFullSource s)
      (-2 * (iteratedDeriv 1 thetaCuspFullSource t ^ (2 : ℕ) +
        thetaCuspFullSource t * iteratedDeriv 2 thetaCuspFullSource t)) t
    exact hraw'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by
        simp only [Pi.mul_apply]
        ring)
  have hlocal : thetaCuspReflectedSourceDecayFlux 0 =ᶠ[nhds t] Q := by
    exact Filter.Eventually.of_forall fun s =>
      thetaCuspReflectedSourceDecayFlux_zero_eq_fullSource_jets s
  have hflux := hasDerivAt_thetaCuspReflectedSourceDecayFlux 0 t
  exact hflux.unique (hQ.congr_of_eventuallyEq hlocal)

theorem tendsto_thetaCuspReflectedSourceFirstDrop_zero_atTop :
    Tendsto (thetaCuspReflectedSourceFirstDrop 0) atTop
      (𝓝 (thetaCuspReflectedSourceProduct 0 0)) := by
  unfold thetaCuspReflectedSourceFirstDrop
  have hconst : Tendsto
      (fun _ : ℝ => thetaCuspReflectedSourceProduct 0 0) atTop
      (𝓝 (thetaCuspReflectedSourceProduct 0 0)) := tendsto_const_nhds
  simpa only [sub_zero] using
    hconst.sub (tendsto_thetaCuspReflectedSourceProduct_atTop_zero 0)

theorem tendsto_id_mul_thetaCuspReflectedSourceDecayFlux_zero_atTop_zero :
    Tendsto (fun t : ℝ => t * thetaCuspReflectedSourceDecayFlux 0 t)
      atTop (𝓝 0) := by
  have hzero :=
    tendsto_pow_mul_iteratedDeriv_thetaCuspFullSource_atTop_zero 0 0
  have hone :=
    tendsto_pow_mul_iteratedDeriv_thetaCuspFullSource_atTop_zero 1 1
  have hprod := (hzero.mul hone).const_mul (-2)
  have hfun : (fun t : ℝ => t * thetaCuspReflectedSourceDecayFlux 0 t) =
      fun t : ℝ => -2 *
        ((t ^ (0 : ℕ) * iteratedDeriv 0 thetaCuspFullSource t) *
          (t ^ (1 : ℕ) * iteratedDeriv 1 thetaCuspFullSource t)) := by
    funext t
    rw [thetaCuspReflectedSourceDecayFlux_zero_eq_fullSource_jets]
    simp only [pow_zero, one_mul, pow_one, iteratedDeriv_zero]
    ring
  rw [hfun]
  simpa using hprod

theorem tendsto_sq_mul_thetaCuspReflectedSourceDecayFluxCurvature_zero_atTop_zero :
    Tendsto (fun t : ℝ => t ^ (2 : ℕ) *
      thetaCuspReflectedSourceDecayFluxCurvature 0 t) atTop (𝓝 0) := by
  have hone :=
    tendsto_pow_mul_iteratedDeriv_thetaCuspFullSource_atTop_zero 1 1
  have hzero :=
    tendsto_pow_mul_iteratedDeriv_thetaCuspFullSource_atTop_zero 0 0
  have htwo :=
    tendsto_pow_mul_iteratedDeriv_thetaCuspFullSource_atTop_zero 2 2
  have hsum := ((hone.pow 2).add (hzero.mul htwo)).const_mul (-2)
  have hfun : (fun t : ℝ => t ^ (2 : ℕ) *
      thetaCuspReflectedSourceDecayFluxCurvature 0 t) =
      fun t : ℝ => -2 *
        ((t ^ (1 : ℕ) * iteratedDeriv 1 thetaCuspFullSource t) ^ (2 : ℕ) +
          (t ^ (0 : ℕ) * iteratedDeriv 0 thetaCuspFullSource t) *
            (t ^ (2 : ℕ) * iteratedDeriv 2 thetaCuspFullSource t)) := by
    funext t
    rw [thetaCuspReflectedSourceDecayFluxCurvature_zero_eq_fullSource_jets]
    simp only [pow_zero, one_mul, pow_one, iteratedDeriv_zero]
    ring
  rw [hfun]
  simpa using hsum

theorem tendsto_thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_atTop :
    Tendsto (thetaCuspReflectedSourceFifthRootCurvatureNumerator 0) atTop
      (𝓝 (24 * thetaCuspReflectedSourceProduct 0 0 ^ (2 : ℕ))) := by
  have hA := tendsto_thetaCuspReflectedSourceFirstDrop_zero_atTop
  have hD :=
    tendsto_id_mul_thetaCuspReflectedSourceDecayFlux_zero_atTop_zero
  have hJ :=
    tendsto_sq_mul_thetaCuspReflectedSourceDecayFluxCurvature_zero_atTop_zero
  have hDsq := hD.pow 2
  have hlim :=
    ((hA.pow 2).const_mul 24).sub ((hA.mul hD).const_mul 9) |>.add
      ((hA.mul hJ).const_mul 5 |>.sub (hDsq.const_mul 4))
  have hfun : thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 =
      fun t : ℝ =>
        24 * thetaCuspReflectedSourceFirstDrop 0 t ^ (2 : ℕ) -
          9 * (thetaCuspReflectedSourceFirstDrop 0 t *
            (t * thetaCuspReflectedSourceDecayFlux 0 t)) +
          (5 * (thetaCuspReflectedSourceFirstDrop 0 t *
              (t ^ (2 : ℕ) * thetaCuspReflectedSourceDecayFluxCurvature 0 t)) -
            4 * (t * thetaCuspReflectedSourceDecayFlux 0 t) ^ (2 : ℕ)) := by
    funext t
    unfold thetaCuspReflectedSourceFifthRootCurvatureNumerator
    ring
  rw [hfun]
  simpa using hlim

theorem eventually_thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_pos :
    ∀ᶠ t : ℝ in atTop,
      0 < thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t := by
  have hP : 0 < thetaCuspReflectedSourceProduct 0 0 := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  have hlimit : 0 < 24 * thetaCuspReflectedSourceProduct 0 0 ^ (2 : ℕ) := by
    positivity
  exact
    tendsto_thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_atTop.eventually
      (eventually_gt_nhds hlimit)

theorem exists_thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_pos_tail :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t →
      0 < thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t := by
  rcases (eventually_atTop.1
    eventually_thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_pos) with
    ⟨T₀, hT₀⟩
  refine ⟨max 1 T₀, by positivity, fun t ht => ?_⟩
  exact hT₀ t ((le_max_right 1 T₀).trans ht)

/-- The modular-center C5 problem has no seam or cofinal-tail burden: it is exactly one compact
annulus problem with unspecified, noncomputed endpoints. -/
theorem exists_thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_compactCore :
    ∃ δ T : ℝ, 0 < δ ∧ δ ≤ T ∧
      ((∀ t : ℝ, 0 < t →
          0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t) ↔
        ∀ t : ℝ, δ ≤ t → t ≤ T →
          0 ≤ thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 t) := by
  rcases exists_thetaCuspReflectedSourceFifthRootCurvatureNumerator_pos_right 0 with
    ⟨δ₀, hδ₀, hnear⟩
  rcases exists_thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_pos_tail with
    ⟨T, hT, htail⟩
  let δ := min δ₀ T
  have hδ : 0 < δ := lt_min hδ₀ hT
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδT : δ ≤ T := min_le_right _ _
  refine ⟨δ, T, hδ, hδT, ?_⟩
  constructor
  · intro hall t htδ htT
    exact hall t (lt_of_lt_of_le hδ htδ)
  · intro hcore t ht
    by_cases htδ : t < δ
    · exact (hnear t ht (lt_of_lt_of_le htδ hδδ₀)).le
    · have hδt : δ ≤ t := le_of_not_gt htδ
      by_cases htT : t ≤ T
      · exact hcore t hδt htT
      · exact (htail t (le_of_lt (lt_of_not_ge htT))).le

end

end RHTower
