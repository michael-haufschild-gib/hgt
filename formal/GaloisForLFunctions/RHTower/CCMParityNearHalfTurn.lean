import GaloisForLFunctions.RHTower.CCMParityTopLayerNoGo

/-!
# Near half-turns of the aperture line decide the leading-order parity

For the Cauchy model with distinct positive ordinates `t`, offset `δ > 0` and weights `M`, the parity
balance `F(θ) = λ_max(T(θ)) − λ_max(T(θ + π𝟙))` satisfies `F(θ + π𝟙) = −F(θ)` and is Lipschitz in
the phases modulo `2π` with a constant `L` depending only on the model.

**Theorem** (`exists_lipschitz_halfTurn_balance`). There is `L ≥ 0` such that whenever the aperture
phases `θ(a₁) = −2ta₁` lie within `η` of `π𝟙` modulo `2π`, for every aperture `a₀` one of
`F(θ(a₀))`, `F(θ(a₀ + a₁))` is at least `|F(θ(a₀))| − Lη`.

**Consequence** (`exists_balance_pos_of_near_halfTurn`). If the aperture line passes within `η` of
`π𝟙` and `|F| > Lη` somewhere on it, then `F > 0` somewhere on it, so the odd sector wins at
arbitrarily large apertures (`ccm_frequently_odd_wins_iff`). This is the quantitative form of the
even-relations theorem: an odd-sum relation `k` keeps the line at distance `≍ 1/|k|` from `π𝟙`, so the
open residue consists of configurations whose `|F|` on the line is `O(1/|k|)` for every odd-sum
relation `k`.
-/

open Matrix Complex Filter Topology MeasureTheory Set
open RHTower.CCMParityCauchy

namespace RHTower.CCMParityTopLayer

noncomputable section

variable {m : ℕ}

theorem aperturePhase_add (t : Fin m → ℝ) (a₀ a₁ : ℝ) (j : Fin m) :
    aperturePhase t (a₀ + a₁) j = aperturePhase t a₀ j + aperturePhase t a₁ j := by
  simp only [aperturePhase]; ring

/-- **Near half-turns.** -/
theorem exists_lipschitz_halfTurn_balance {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M : Fin m → ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (a₀ a₁ η : ℝ) (z : Fin m → ℤ),
      (∀ j, |aperturePhase t a₁ j - Real.pi - z j * (2 * Real.pi)| ≤ η) →
        |ccmParityBalance δ t M (aperturePhase t a₀)| - L * η ≤
          max (ccmParityBalance δ t M (aperturePhase t a₀))
            (ccmParityBalance δ t M (aperturePhase t (a₀ + a₁))) := by
  obtain ⟨B, hB0, hB⟩ := exists_quadForm_sub_le hδ ht htpos
  set S : ℝ := ∑ j, |M j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨2 * B * S, by positivity, fun a₀ a₁ η z hnear => ?_⟩
  set θ₀ := aperturePhase t a₀ with hθ₀
  set θ := aperturePhase t (a₀ + a₁) with hθ
  have hphase : ∀ j, |θ j - halfTurn θ₀ j - z j * (2 * Real.pi)| ≤ η := by
    intro j
    have e : θ j - halfTurn θ₀ j - z j * (2 * Real.pi) =
        aperturePhase t a₁ j - Real.pi - z j * (2 * Real.pi) := by
      simp only [hθ, hθ₀, halfTurn, aperturePhase_add]; ring
    rw [e]; exact hnear j
  have hD := sum_norm_phaseWeight_sub_le M θ (halfTurn θ₀) z hphase
  have hD' := sum_norm_phaseWeight_sub_le M (halfTurn θ) (halfTurn (halfTurn θ₀)) z
    (fun j => by rw [halfTurn_sub]; exact hphase j)
  have hL1 := abs_ccmLambdaMax_sub_le hδ ht htpos hm hB M θ (halfTurn θ₀)
  have hL2 := abs_ccmLambdaMax_sub_le hδ ht htpos hm hB M (halfTurn θ) (halfTurn (halfTurn θ₀))
  have e1 : B * ∑ i, ‖phaseWeight M θ i - phaseWeight M (halfTurn θ₀) i‖ ≤ B * (S * η) :=
    mul_le_mul_of_nonneg_left hD hB0
  have e2 : B * ∑ i, ‖phaseWeight M (halfTurn θ) i - phaseWeight M (halfTurn (halfTurn θ₀)) i‖
      ≤ B * (S * η) := mul_le_mul_of_nonneg_left hD' hB0
  have hbal : -ccmParityBalance δ t M θ₀ - 2 * B * S * η ≤ ccmParityBalance δ t M θ := by
    have hflip := ccmParityBalance_halfTurn δ t M θ₀
    unfold ccmParityBalance at hflip ⊢
    rw [abs_le] at hL1 hL2
    linarith [hL1.1, hL2.2]
  rcases le_total 0 (ccmParityBalance δ t M θ₀) with h0 | h0
  · rw [abs_of_nonneg h0]
    have : 0 ≤ 2 * B * S * η := by
      have hη : 0 ≤ η := (abs_nonneg _).trans (hnear ⟨0, hm⟩)
      positivity
    exact le_trans (by linarith) (le_max_left _ _)
  · rw [abs_of_nonpos h0]
    exact le_trans (by linarith) (le_max_right _ _)

/-- **A near half-turn with a large balance gives an odd win.** -/
theorem exists_balance_pos_of_near_halfTurn {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M : Fin m → ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (a₀ a₁ η : ℝ) (z : Fin m → ℤ),
      (∀ j, |aperturePhase t a₁ j - Real.pi - z j * (2 * Real.pi)| ≤ η) →
        L * η < |ccmParityBalance δ t M (aperturePhase t a₀)| →
          ∃ a : ℝ, 0 < ccmParityBalance δ t M (aperturePhase t a) := by
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_halfTurn_balance hδ ht htpos hm M
  refine ⟨L, hL0, fun a₀ a₁ η z hnear hbig => ?_⟩
  have := hL a₀ a₁ η z hnear
  rcases le_total (ccmParityBalance δ t M (aperturePhase t a₀))
    (ccmParityBalance δ t M (aperturePhase t (a₀ + a₁))) with h | h
  · rw [max_eq_right h] at this
    exact ⟨a₀ + a₁, by linarith⟩
  · rw [max_eq_left h] at this
    exact ⟨a₀, by linarith⟩

/-- **Odd ground states from a near half-turn.** Under a finite top layer, if the aperture line
passes within `η` of `π𝟙` and the balance exceeds `Lη` in absolute value somewhere on it, then
arbitrarily large apertures have only reflection-odd ground states. -/
theorem exists_aperture_ground_odd_of_near_halfTurn {δ : ℝ} {t : Fin m → ℝ}
    (h : FiniteTopLayer δ t) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (a₀ a₁ η : ℝ) (z : Fin m → ℤ),
      (∀ j, |aperturePhase t a₁ j - Real.pi - z j * (2 * Real.pi)| ≤ η) →
        L * η < |ccmParityBalance δ t h.mult (aperturePhase t a₀)| → ∀ A : ℝ,
          ∃ a : SuzukiPositiveAperture, A < a.1 ∧
            ∀ u : CCMArchimedeanFormDomain a,
              ccmRestrictedWeilSourceQuadratic a u =
                  ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 →
                ccmArchimedeanFormReflection a u = -u := by
  obtain ⟨L, hL0, hL⟩ := exists_balance_pos_of_near_halfTurn h.pos h.injective h.t_pos
    h.nonempty h.mult
  exact ⟨L, hL0, fun a₀ a₁ η z hnear hbig A =>
    exists_aperture_ground_odd h (hL a₀ a₁ η z hnear hbig) A⟩

end

end RHTower.CCMParityTopLayer
