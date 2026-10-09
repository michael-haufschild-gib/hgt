import GaloisForLFunctions.RHTower.WeilLogShiftC0VanishingEnvelope

/-!
# Uniform vanishing of regular history receivers and their sensitivity

One normalization and one vanishing profile control the whole regular
affine history fibre. Values decay uniformly over bounded amplitudes;
differences decay uniformly whenever their amplitude separation is bounded.
-/

open Filter Topology Real
open scoped ZeroAtInfty BoundedContinuousFunction

noncomputable section

namespace RHTower

/-- One nonnegative `C₀` profile bounds every regular native amplitude and
every difference, with the same normalization on the entire real line. -/
theorem exists_weilLogShift_history_vanishing_profile
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (center : ℕ →ᵇ ℝ) (T : E →ₗ[ℝ] (ℕ →ᵇ ℝ)) :
    ∃ (m : ℕ) (B : ℝ), 0 < B ∧ ∃ g : C₀(ℝ, ℝ), (∀ y, 0 ≤ g y) ∧
      ∃ Φ : {a : E // ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
          (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ))} → C₀(ℝ, ℝ),
        (∀ (a : {a : E // ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
            (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ))}) (y : ℝ),
          HasSum (fun n : ℕ => exp (-(B * n)) *
            weilLogShiftRecoveryMoment y (center + T (a : E) : ℕ →ᵇ ℝ) n / (n.factorial : ℝ) ^ m)
            (Φ a y)) ∧
        (∀ a y, |Φ a y| ≤ (1 + ‖(a : E)‖) * g y) ∧
        ∀ a b y, |Φ a y - Φ b y| ≤ ‖(a : E) - (b : E)‖ * g y := by
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
  obtain ⟨m, B, hB, g, hg, Ψ, hvalue, hbound, hdiff⟩ :=
    exists_weilLogShift_affine_vanishing_profile F
  let lift : {a : E // ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
      (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ))} →
      {a : E // WeilLogShiftHasFactorialMajorant (F a)} :=
    fun a => ⟨(a : E), (hreg (a : E)).mpr a.property⟩
  refine ⟨m, B, hB, g, hg, fun a => Ψ (lift a), ?_, ?_, ?_⟩
  · intro a y
    exact (hvalue (lift a) y).congr_fun
      (fun n => by simp only [lift, hF, weilLogShiftRecoveryMoment])
  · intro a y
    exact hbound (lift a) y
  · intro a b y
    exact hdiff (lift a) (lift b) y

/-- One fixed normalization has uniformly vanishing tails over every bounded
regular amplitude set, and uniformly vanishing sensitivity for all regular
pairs with bounded separation, without bounding their base amplitudes. -/
theorem exists_weilLogShift_history_uniform_vanishing_and_sensitivity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (center : ℕ →ᵇ ℝ) (T : E →ₗ[ℝ] (ℕ →ᵇ ℝ)) :
    ∃ (m : ℕ) (B : ℝ), 0 < B ∧
      ∃ Φ : {a : E // ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
          (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ))} → C₀(ℝ, ℝ),
        (∀ (a : {a : E // ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
            (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ))}) (y : ℝ),
          HasSum (fun n : ℕ => exp (-(B * n)) *
            weilLogShiftRecoveryMoment y (center + T (a : E) : ℕ →ᵇ ℝ) n / (n.factorial : ℝ) ^ m)
            (Φ a y)) ∧
        ∀ R ε : ℝ, 0 < ε → ∀ᶠ y : ℝ in cocompact ℝ,
          (∀ (a : {a : E // ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
              (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ))}),
            ‖(a : E)‖ ≤ R → |Φ a y| < ε) ∧
          ∀ (a b : {a : E // ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
              (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ))}),
            ‖(a : E) - (b : E)‖ ≤ R → |Φ a y - Φ b y| < ε := by
  obtain ⟨m, B, hB, g, hg, Φ, hvalue, hbound, hdiff⟩ :=
    exists_weilLogShift_history_vanishing_profile center T
  refine ⟨m, B, hB, Φ, hvalue, ?_⟩
  intro R ε hε
  have ht : Tendsto (fun y : ℝ => (1 + max R 0) * g y) (cocompact ℝ) (𝓝 0) := by
    simpa only [mul_zero] using (zero_at_infty g).const_mul (1 + max R 0)
  filter_upwards [(tendsto_order.mp ht).2 ε hε] with y hy
  constructor
  · intro a ha
    have hR : 1 + ‖(a : E)‖ ≤ 1 + max R 0 := by
      linarith only [ha, le_max_left R (0 : ℝ)]
    exact ((hbound a y).trans (mul_le_mul_of_nonneg_right hR (hg y))).trans_lt hy
  · intro a b hab
    have hR : ‖(a : E) - (b : E)‖ ≤ 1 + max R 0 := by
      linarith only [hab, le_max_left R (0 : ℝ)]
    exact ((hdiff a b y).trans (mul_le_mul_of_nonneg_right hR (hg y))).trans_lt hy

end RHTower
