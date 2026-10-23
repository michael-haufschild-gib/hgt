import GaloisForLFunctions.SignedArithmeticEnergyIncidence.ResidueModesAndBackwardContinuation
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Damping is strongly continuous, with an unbounded generator

The centred damping operators `C_η` (`η > 0`) are compact on `c₀` and compose additively.  Extend
them by the identity at zero damping (`dampingFlow`).

* **Strong continuity** (`tendsto_dampingFlow`): `C_η b → b` as `η ↓ 0` for every `b ∈ c₀`.  On a
  residue mode `C_η v_d = d^{−η} v_d → v_d`; the modes span a dense subspace
  (`BezoutValuationIncidence.normalizedResidueMode_dense_span`), and the uniform bound
  `‖C_η‖ ≤ 2` carries the convergence to all of `c₀` (`tendsto_of_dense_of_bounded`).
* **No norm continuity** (`one_le_norm_dampingFlow_sub_id`): `‖C_η − I‖ ≥ 1 − d^{−η}` for every
  `d ≥ 2`, hence `‖C_η − I‖ ≥ 1` at every positive damping.
* **The generator is `−log d` on `v_d`** (`tendsto_generator_residueMode`): the difference
  quotients `η^{−1}(C_η v_d − v_d)` converge to `−log d · v_d`.
* **The generator is unbounded** (`not_exists_bounded_generator`): no bounded operator is the
  strong derivative of the flow at zero, since it would have norm at least `log d` for all `d`.

So damping time is a strongly continuous flow whose infinitesimal generator reads the modulus
logarithmically and is unbounded: compact smoothing at every positive time, no bounded
derivative at time zero.  Continuation towards zero damping has no operator-norm shortcut.
-/

open Filter Topology
open scoped ZeroAtInfty
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-- The damping flow: `C_η` at positive damping, the identity otherwise. -/
def dampingFlow (η : ℝ) : C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ) :=
  if h : 0 < η then arithmeticDampingCenteredOperator h else ContinuousLinearMap.id ℝ (C₀(ℕ, ℝ))

theorem dampingFlow_of_pos {η : ℝ} (h : 0 < η) :
    dampingFlow η = arithmeticDampingCenteredOperator h := dif_pos h

theorem norm_dampingFlow_le {η : ℝ} (h : 0 < η) : ‖dampingFlow η‖ ≤ 2 := by
  rw [dampingFlow_of_pos h]; exact norm_arithmeticDampingCenteredOperator_le h

theorem dampingFlow_residueMode {η : ℝ} (h : 0 < η) {d : ℕ} (hd : 0 < d) :
    dampingFlow η (normalizedResidueMode d) = (d : ℝ) ^ (-η) • normalizedResidueMode d := by
  rw [dampingFlow_of_pos h, centeredOperator_normalizedResidueMode h hd]

/-- `d^{−η} → 1` as `η ↓ 0`. -/
theorem tendsto_rpow_neg_nhdsGT {d : ℕ} (hd : 0 < d) :
    Tendsto (fun η : ℝ => (d : ℝ) ^ (-η)) (𝓝[>] 0) (𝓝 1) := by
  have hc : Continuous fun η : ℝ => (d : ℝ) ^ (-η) :=
    (Real.continuous_const_rpow (by exact_mod_cast hd.ne')).comp continuous_neg
  have := hc.tendsto 0
  simp only [neg_zero, Real.rpow_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem tendsto_dampingFlow_residueMode (d : ℕ) :
    Tendsto (fun η => dampingFlow η (normalizedResidueMode d)) (𝓝[>] 0)
      (𝓝 (normalizedResidueMode d)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [normalizedResidueMode_zero, map_zero, tendsto_const_nhds]
  have h1 : Tendsto (fun η : ℝ => (d : ℝ) ^ (-η) • normalizedResidueMode d) (𝓝[>] 0)
      (𝓝 ((1 : ℝ) • normalizedResidueMode d)) :=
    (tendsto_rpow_neg_nhdsGT hd).smul_const _
  rw [one_smul] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact (dampingFlow_residueMode hη hd).symm

/-- Convergence on the span of the residue modes. -/
theorem tendsto_dampingFlow_of_mem_span {b : C₀(ℕ, ℝ)}
    (hb : b ∈ Submodule.span ℝ (normalizedResidueMode '' Set.Ici 2)) :
    Tendsto (fun η => dampingFlow η b) (𝓝[>] 0) (𝓝 b) := by
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, -, rfl⟩ := hx
    exact tendsto_dampingFlow_residueMode d
  | zero => simp only [map_zero, tendsto_const_nhds]
  | add x y _ _ hx hy => simpa only [map_add] using hx.add hy
  | smul a x _ hx => simpa only [map_smul] using hx.const_smul a

/-- **Uniformly bounded operators converging on a dense set converge everywhere.** -/
theorem tendsto_of_dense_of_bounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : Type*} {l : Filter α} {T : α → E →L[ℝ] E} {C : ℝ} (hT : ∀ᶠ i in l, ‖T i‖ ≤ C)
    {S : Set E} (hS : Dense S) (hconv : ∀ s ∈ S, Tendsto (fun i => T i s) l (𝓝 s)) (b : E) :
    Tendsto (fun i => T i b) l (𝓝 b) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hC1 : 0 < |C| + 1 := by positivity
  obtain ⟨s, hball, hsS⟩ := Metric.dense_iff.1 hS b (ε / (2 * (|C| + 1))) (by positivity)
  rw [Metric.mem_ball] at hball
  filter_upwards [hT, Metric.tendsto_nhds.1 (hconv s hsS) (ε / 2) (by positivity)] with i hi hcs
  have hbs' : ‖b - s‖ < ε / (2 * (|C| + 1)) := by rwa [norm_sub_rev, ← dist_eq_norm]
  have hsplit : T i b - b = T i (b - s) + (T i s - s) + (s - b) := by
    rw [map_sub]; abel
  rw [dist_eq_norm, hsplit]
  have h1 : ‖T i (b - s)‖ ≤ |C| * ‖b - s‖ :=
    (T i).le_opNorm (b - s) |>.trans (mul_le_mul_of_nonneg_right (hi.trans (le_abs_self C))
      (norm_nonneg _))
  have h2 : ‖s - b‖ = ‖b - s‖ := norm_sub_rev s b
  have h3 : ‖T i s - s‖ < ε / 2 := by rwa [← dist_eq_norm]
  have h4 : (|C| + 1) * ‖b - s‖ < ε / 2 := by
    calc (|C| + 1) * ‖b - s‖ < (|C| + 1) * (ε / (2 * (|C| + 1))) :=
          mul_lt_mul_of_pos_left hbs' hC1
      _ = ε / 2 := by field_simp
  calc ‖T i (b - s) + (T i s - s) + (s - b)‖
      ≤ ‖T i (b - s)‖ + ‖T i s - s‖ + ‖s - b‖ := norm_add₃_le
    _ < ε := by nlinarith [norm_nonneg (b - s)]

/-- **Damping is strongly continuous at zero**: `C_η b → b` as `η ↓ 0` for every `b ∈ c₀`. -/
theorem tendsto_dampingFlow (b : C₀(ℕ, ℝ)) :
    Tendsto (fun η => dampingFlow η b) (𝓝[>] 0) (𝓝 b) := by
  refine tendsto_of_dense_of_bounded (C := 2) ?_
    (Submodule.dense_iff_topologicalClosure_eq_top.2 normalizedResidueMode_dense_span)
    (fun s hs => tendsto_dampingFlow_of_mem_span hs) b
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact norm_dampingFlow_le hη

/-! ### No norm continuity -/

/-- `‖C_η − I‖ ≥ 1 − d^{−η}` for every modulus `d ≥ 2`. -/
theorem one_sub_rpow_le_norm_dampingFlow_sub_id {η : ℝ} (h : 0 < η) {d : ℕ} (hd : 2 ≤ d) :
    1 - (d : ℝ) ^ (-η) ≤ ‖dampingFlow η - ContinuousLinearMap.id ℝ (C₀(ℕ, ℝ))‖ := by
  have hd0 : 0 < d := by omega
  have hv := norm_pos_iff.2 (normalizedResidueMode_ne_zero hd)
  have hlt : (d : ℝ) ^ (-η) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < d)) (by linarith)
  have hval : (dampingFlow η - ContinuousLinearMap.id ℝ (C₀(ℕ, ℝ))) (normalizedResidueMode d) =
      -((1 - (d : ℝ) ^ (-η)) • normalizedResidueMode d) := by
    rw [ContinuousLinearMap.sub_apply, dampingFlow_residueMode h hd0, ContinuousLinearMap.id_apply]
    ext n
    simp only [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.neg_apply,
      ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
    ring
  have hle := (dampingFlow η - ContinuousLinearMap.id ℝ (C₀(ℕ, ℝ))).le_opNorm (normalizedResidueMode d)
  rw [hval, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)] at hle
  exact le_of_mul_le_mul_right hle hv

/-- **Damping is not norm continuous**: `‖C_η − I‖ ≥ 1` at every positive damping. -/
theorem one_le_norm_dampingFlow_sub_id {η : ℝ} (h : 0 < η) :
    1 ≤ ‖dampingFlow η - ContinuousLinearMap.id ℝ (C₀(ℕ, ℝ))‖ := by
  have ht : Tendsto (fun d : ℕ => 1 - (d : ℝ) ^ (-η)) atTop (𝓝 (1 - 0)) :=
    ((tendsto_rpow_neg_atTop h).comp tendsto_natCast_atTop_atTop).const_sub 1
  rw [sub_zero] at ht
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop 2] with d hd
  exact one_sub_rpow_le_norm_dampingFlow_sub_id h hd

/-! ### The generator -/

/-- **The generator is `−log d` on the residue mode `v_d`.** -/
theorem tendsto_generator_residueMode {d : ℕ} (hd : 0 < d) :
    Tendsto (fun η : ℝ => η⁻¹ • (dampingFlow η (normalizedResidueMode d) -
      normalizedResidueMode d)) (𝓝[>] 0) (𝓝 (-Real.log d • normalizedResidueMode d)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  -- `η ↦ d^{−η} = exp(−η log d)` has derivative `−log d` at `0`
  have hder : HasDerivAt (fun η : ℝ => Real.exp (-(η * Real.log d))) (-Real.log d) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (Real.log d)).neg.exp
    simpa using this
  have hslope := hder.tendsto_slope_zero_right
  simp only [zero_add, neg_zero, zero_mul, Real.exp_zero, smul_eq_mul] at hslope
  have h1 : Tendsto (fun η : ℝ => (η⁻¹ * (Real.exp (-(η * Real.log d)) - 1)) •
      normalizedResidueMode d) (𝓝[>] 0) (𝓝 (-Real.log d • normalizedResidueMode d)) :=
    hslope.smul_const _
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [dampingFlow_residueMode hη hd, Real.rpow_def_of_pos hd',
    show Real.log d * -η = -(η * Real.log d) by ring]
  ext n
  simp only [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
  ring

/-- **The generator is unbounded**: no bounded operator is the strong derivative of the damping
flow at zero damping. -/
theorem not_exists_bounded_generator :
    ¬ ∃ A : C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ), ∀ b, Tendsto (fun η : ℝ => η⁻¹ • (dampingFlow η b - b))
      (𝓝[>] 0) (𝓝 (A b)) := by
  rintro ⟨A, hA⟩
  have hAv : ∀ d : ℕ, 2 ≤ d → A (normalizedResidueMode d) = -Real.log d • normalizedResidueMode d :=
    fun d hd => tendsto_nhds_unique (hA _) (tendsto_generator_residueMode (by omega))
  -- such an operator would have norm at least `log d` for every modulus
  have hlog : ∀ d : ℕ, 2 ≤ d → Real.log d ≤ ‖A‖ := by
    intro d hd
    have hv := norm_pos_iff.2 (normalizedResidueMode_ne_zero hd)
    have hle := A.le_opNorm (normalizedResidueMode d)
    rw [hAv d hd, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (Real.log_natCast_nonneg d)] at hle
    exact le_of_mul_le_mul_right hle hv
  obtain ⟨d, hd1, hd2⟩ := ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
    ‖A‖).and (eventually_ge_atTop 2) |>.exists
  exact absurd (hlog d hd2) (not_le.2 hd1)

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
