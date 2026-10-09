import GaloisForLFunctions.RHTower.WeilLogShiftC0PotentialOperator

/-!
# A common C₀ receiver with quantitative stability on regular affine fibres

Homogenization restricts the regular-subspace operator to an affine family.
The resulting receiver is uniformly Lipschitz in the ambient amplitude norm.
Unweighting the origin moment identifies the native history receiver with
the same coefficient construction.
-/

open Real
open scoped ZeroAtInfty BoundedContinuousFunction

noncomputable section

namespace RHTower

/-- One normalization gives a `C₀` receiver on the entire regular affine
fibre, with both an affine norm bound and a uniform difference bound. -/
theorem exists_weilLogShift_uniform_affine_c0_receiver
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E →ᵃ[ℝ] (ℕ → ℝ)) :
    ∃ (m : ℕ) (B C : ℝ), 0 < B ∧ 0 ≤ C ∧
      ∃ Φ : {a : E // WeilLogShiftHasFactorialMajorant (F a)} → C₀(ℝ, ℝ),
        (∀ (a : {a : E // WeilLogShiftHasFactorialMajorant (F a)}) (y : ℝ), HasSum (fun n : ℕ =>
          exp (-(B * n)) * (F (a : E) n * pairedLogKernel y n) / (n.factorial : ℝ) ^ m) (Φ a y)) ∧
        (∀ a, ‖Φ a‖ ≤ C * (1 + ‖(a : E)‖)) ∧
        ∀ a b, ‖Φ a - Φ b‖ ≤ C * ‖(a : E) - (b : E)‖ := by
  let H : (E × ℝ) →ₗ[ℝ] (ℕ → ℝ) :=
    F.linear.comp (LinearMap.fst ℝ E ℝ) + (LinearMap.snd ℝ E ℝ).smulRight (F 0)
  have heq (a : E) : H (a, 1) = F a := by
    change F.linear a + (1 : ℝ) • F 0 = F a
    simpa only [one_smul, vadd_eq_add, add_zero] using (F.map_vadd (0 : E) a).symm
  obtain ⟨m, B, C, hB, hC, S, hS, hvalue⟩ := exists_weilLogShift_uniform_c0_operator H
  let L : Submodule ℝ (E × ℝ) := weilLogShiftFactorialSequenceSubmodule.comap H
  let lift : {a : E // WeilLogShiftHasFactorialMajorant (F a)} → L := fun a =>
    ⟨((a : E), 1), by
      change WeilLogShiftHasFactorialMajorant (H ((a : E), 1))
      rw [heq]
      exact a.property⟩
  let Φ : {a : E // WeilLogShiftHasFactorialMajorant (F a)} → C₀(ℝ, ℝ) := fun a => S (lift a)
  have hbound (z : L) : ‖S z‖ ≤ C * ‖z‖ := S.le_of_opNorm_le hS z
  refine ⟨m, B, C, hB, hC, Φ, ?_, ?_, ?_⟩
  · intro a y
    simpa only [lift, heq] using hvalue (lift a) y
  · intro a
    have hn : ‖lift a‖ ≤ 1 + ‖(a : E)‖ := by
      change ‖((a : E), (1 : ℝ))‖ ≤ 1 + ‖(a : E)‖
      rw [Prod.norm_def, norm_one]
      exact max_le (by linarith [norm_nonneg (a : E)]) (by linarith [norm_nonneg (a : E)])
    exact (hbound (lift a)).trans (mul_le_mul_of_nonneg_left hn hC)
  · intro a b
    change ‖S (lift a) - S (lift b)‖ ≤ _
    rw [← map_sub]
    have hd : ‖lift a - lift b‖ = ‖(a : E) - (b : E)‖ := by
      change ‖((a : E) - (b : E), (1 : ℝ) - 1)‖ = ‖(a : E) - (b : E)‖
      rw [sub_self, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
    calc
      _ ≤ C * ‖lift a - lift b‖ := hbound (lift a - lift b)
      _ = _ := by rw [hd]

/-- A native finite-dimensional history family admits one common normalized
moment receiver into `C₀`, with uniform stability on its actual regular fibre. -/
theorem exists_weilLogShift_uniform_history_c0_receiver
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (center : ℕ →ᵇ ℝ) (T : E →ₗ[ℝ] (ℕ →ᵇ ℝ)) :
    ∃ (m : ℕ) (B C : ℝ), 0 < B ∧ 0 ≤ C ∧
      ∃ Φ : {a : E // ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
          (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ))} → C₀(ℝ, ℝ),
        (∀ (a : {a : E // ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
            (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ))}) (y : ℝ),
          HasSum (fun n : ℕ => exp (-(B * n)) *
          weilLogShiftRecoveryMoment y (center + T (a : E) : ℕ →ᵇ ℝ) n / (n.factorial : ℝ) ^ m)
          (Φ a y)) ∧
        (∀ a, ‖Φ a‖ ≤ C * (1 + ‖(a : E)‖)) ∧
        ∀ a b, ‖Φ a - Φ b‖ ≤ C * ‖(a : E) - (b : E)‖ := by
  let W : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ) := {
    toFun := fun f n => f n / pairedLogKernel 0 n
    map_add' := by
      intro f g
      funext n
      change (f n + g n) / pairedLogKernel 0 n =
        f n / pairedLogKernel 0 n + g n / pairedLogKernel 0 n
      ring
    map_smul' := by
      intro c f
      funext n
      change (c * f n) / pairedLogKernel 0 n = c * (f n / pairedLogKernel 0 n)
      ring }
  let F : E →ᵃ[ℝ] (ℕ → ℝ) := W.toAffineMap.comp (weilLogShiftRecoveryAmplitudeMoment center T)
  have hF (a : E) (n : ℕ) : F a n =
      WeilExcess.weilDeviation (weilLogShiftRecoveryInverse (center + T a : ℕ →ᵇ ℝ)) n := by
    change (WeilExcess.weilDeviation (weilLogShiftRecoveryInverse (center + T a : ℕ →ᵇ ℝ)) n *
      pairedLogKernel 0 n) / pairedLogKernel 0 n = _
    exact mul_div_cancel_right₀ _ (pairedLogKernel_pos 0 n).ne'
  have hreg (a : E) : WeilLogShiftHasFactorialMajorant (F a) ↔
      ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
        (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ)) := by
    have he : F a = WeilExcess.weilDeviation
        (weilLogShiftRecoveryInverse (center + T a : ℕ →ᵇ ℝ)) := funext (hF a)
    rw [he]
    exact (weilLogShiftHasFactorialMajorant_recovery_coefficients_iff
      (center + T a : ℕ →ᵇ ℝ) 0).symm.trans
        (weilLogShiftHasFactorialMajorant_some_shift_iff_origin (center + T a)).symm
  obtain ⟨m, B, C, hB, hC, Ψ, hvalue, hnorm, hdiff⟩ :=
    exists_weilLogShift_uniform_affine_c0_receiver F
  let lift : {a : E // ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
      (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ))} →
      {a : E // WeilLogShiftHasFactorialMajorant (F a)} :=
    fun a => ⟨(a : E), (hreg (a : E)).mpr a.property⟩
  refine ⟨m, B, C, hB, hC, fun a => Ψ (lift a), ?_, ?_, ?_⟩
  · intro a y
    exact (hvalue (lift a) y).congr_fun
      (fun n => by simp only [lift, hF, weilLogShiftRecoveryMoment])
  · intro a
    exact hnorm (lift a)
  · intro a b
    exact hdiff (lift a) (lift b)

end RHTower
