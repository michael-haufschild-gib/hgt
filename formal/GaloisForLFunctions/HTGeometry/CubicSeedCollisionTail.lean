/-
# The collision tail of the cubic-phase ensemble, in seed normalization

Both collision moments of the finite cubic-phase ensemble are the continuous Steinhaus moments, so
the same Chebyshev step that bounds the collision tail on the phase box bounds it on the ensemble.
The Chebyshev is written in counting form, so no measure on the coefficient space is needed, and the
collision is the unit-norm `phaseCollision`, the normalization in which a seed collision is compared
with a shell-averaged spectral collision.

Main results:
* `card_filter_gt_le_of_mean_le` — counting Chebyshev against an upper mean bound.
* `average_phaseCollision_polyEval_le`, `variance_phaseCollision_polyEval_le` — **`(8)`**.
* `card_filter_phaseCollision_polyEval_gt_le` — **`(9)` for the cubic-phase ensemble**.
* `sum_posPart_sq_phaseCollision_polyEval_le` — **`(27)`--`(28)`** at a fixed basis.
-/
import GaloisForLFunctions.HTGeometry.CubicPhaseCollisionTransfer
import GaloisForLFunctions.HTGeometry.PhaseCollisionConcentration

open Finset MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- Rearrangement of a Chebyshev count into a fraction bound. -/
theorem mul_inv_le_div_of_mul_le {B N κ V : ℝ} (hN : 0 < N) (hκ : 0 < κ)
    (h : B * κ ^ (2 : ℕ) ≤ N * V) : B * N⁻¹ ≤ V / κ ^ (2 : ℕ) := by
  have hκ2 : (0 : ℝ) < κ ^ (2 : ℕ) := by positivity
  rw [← sub_nonneg]
  have hexp : V / κ ^ (2 : ℕ) - B * N⁻¹ = (N * V - B * κ ^ (2 : ℕ)) * (N⁻¹ * (κ ^ (2 : ℕ))⁻¹) := by
    field_simp
  rw [hexp]
  have h1 : (0 : ℝ) ≤ N * V - B * κ ^ (2 : ℕ) := by linarith
  have h2 : (0 : ℝ) ≤ N⁻¹ * (κ ^ (2 : ℕ))⁻¹ := by positivity
  exact mul_nonneg h1 h2

/-- **Counting Chebyshev against an upper mean bound.**  If the uniform average of `X` over a finite
nonempty type is at most `m` and its uniform variance is at most `V`, then the fraction of points
with `X > m + κ` is at most `V / κ²`. -/
theorem card_filter_gt_le_of_mean_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) {m V κ : ℝ} (hκ : 0 < κ)
    (hmean : ((Fintype.card Ω : ℝ))⁻¹ * ∑ c, X c ≤ m)
    (hvar : ((Fintype.card Ω : ℝ))⁻¹ * ∑ c, (X c) ^ (2 : ℕ)
      - (((Fintype.card Ω : ℝ))⁻¹ * ∑ c, X c) ^ (2 : ℕ) ≤ V) :
    ((univ.filter fun c => m + κ < X c).card : ℝ) * ((Fintype.card Ω : ℝ))⁻¹ ≤ V / κ ^ (2 : ℕ) := by
  classical
  set N := (Fintype.card Ω : ℝ) with hNdef
  have hNpos : 0 < N := by
    rw [hNdef]
    exact_mod_cast Fintype.card_pos
  set μ₁ := N⁻¹ * ∑ c, X c with hμdef
  have hs : ∑ c, X c = N * μ₁ := by
    rw [hμdef, ← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]
  have hsum : ∑ c, (X c - μ₁) ^ (2 : ℕ) = (∑ c, (X c) ^ (2 : ℕ)) - N * μ₁ ^ (2 : ℕ) := by
    have hexp : ∀ c, (X c - μ₁) ^ (2 : ℕ) = (X c) ^ (2 : ℕ) - 2 * μ₁ * X c + μ₁ ^ (2 : ℕ) := fun c => by ring
    rw [Finset.sum_congr rfl (fun c _ => hexp c), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← hNdef, hs]
    ring
  have hvar' : (∑ c, (X c) ^ (2 : ℕ)) - N * μ₁ ^ (2 : ℕ) ≤ N * V := by
    have hmul := mul_le_mul_of_nonneg_left hvar (le_of_lt hNpos)
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul] at hmul
    have hsq : N * (N⁻¹ * ∑ c, X c) ^ (2 : ℕ) = N * μ₁ ^ (2 : ℕ) := by rw [← hμdef]
    rw [hsq] at hmul
    linarith [hmul]
  have hbad : ∀ c ∈ (univ.filter fun c => m + κ < X c), κ ^ (2 : ℕ) ≤ (X c - μ₁) ^ (2 : ℕ) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    have hgap : κ ≤ X c - μ₁ := by linarith [hc.2, hmean]
    nlinarith [hgap, hκ]
  have hcount : ((univ.filter fun c => m + κ < X c).card : ℝ) * κ ^ (2 : ℕ)
      ≤ ∑ c, (X c - μ₁) ^ (2 : ℕ) := by
    calc ((univ.filter fun c => m + κ < X c).card : ℝ) * κ ^ (2 : ℕ)
        = ∑ _c ∈ (univ.filter fun c => m + κ < X c), κ ^ (2 : ℕ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ c ∈ (univ.filter fun c => m + κ < X c), (X c - μ₁) ^ (2 : ℕ) :=
          Finset.sum_le_sum hbad
      _ ≤ ∑ c, (X c - μ₁) ^ (2 : ℕ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun c _ _ => sq_nonneg _)
  rw [hsum] at hcount
  have hfinal : ((univ.filter fun c => m + κ < X c).card : ℝ) * κ ^ (2 : ℕ) ≤ N * V :=
    le_trans hcount hvar'
  exact mul_inv_le_div_of_mul_le hNpos hκ hfinal


variable {ι : Type*} [Fintype ι] [DecidableEq ι] {J : Type*} [Fintype J] [DecidableEq J]

/-- **The mean half of `(8)` for the finite cubic-phase ensemble.**  The ensemble average of the
collision against an orthonormal family is at most `2/D`. -/
theorem average_phaseCollision_polyEval_le (m : ℕ) (hm : 4 ≤ 2 ^ (m + 1) - 1)
    (e : J → (ι → Bool) → ℂ)
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0)
    (hcard : Fintype.card J = Fintype.card (ι → Bool)) :
    ((Fintype.card (MonLe ι m → ZMod 8) : ℝ))⁻¹ *
        ∑ c : MonLe ι m → ZMod 8, phaseCollision e (eighthPhase (polyEval m c))
      ≤ 2 / (Fintype.card (ι → Bool) : ℝ) := by
  classical
  have he : ∀ j, (∑ a, ‖e j a‖ ^ (2 : ℕ)) ≤ 1 := fun j => le_of_eq (sum_normSq_of_orthonormal horth j)
  rw [average_phaseCollision_polyEval_eq_integral m hm e]
  have h := integral_box_phaseCollision_le e he
  rw [hcard] at h
  calc (∫ x in torusBox (ι → Bool), phaseCollision e x)
      ≤ 2 * (Fintype.card (ι → Bool) : ℝ) * ((Fintype.card (ι → Bool) : ℝ))⁻¹ ^ (2 : ℕ) := h
    _ = 2 / (Fintype.card (ι → Bool) : ℝ) := by field_simp

/-- **The variance half of `(8)` for the finite cubic-phase ensemble.**  The ensemble variance of
the collision against an orthonormal family is at most `96/D³`. -/
theorem variance_phaseCollision_polyEval_le (m : ℕ) (hm : 8 ≤ 2 ^ (m + 1) - 1)
    (e : J → (ι → Bool) → ℂ)
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0)
    (hcard : Fintype.card J = Fintype.card (ι → Bool)) :
    ((Fintype.card (MonLe ι m → ZMod 8) : ℝ))⁻¹ *
        ∑ c : MonLe ι m → ZMod 8, phaseCollision e (eighthPhase (polyEval m c)) ^ (2 : ℕ)
      - (((Fintype.card (MonLe ι m → ZMod 8) : ℝ))⁻¹ *
        ∑ c : MonLe ι m → ZMod 8, phaseCollision e (eighthPhase (polyEval m c))) ^ (2 : ℕ)
      ≤ 96 / (Fintype.card (ι → Bool) : ℝ) ^ (3 : ℕ) := by
  classical
  have hm4 : 4 ≤ 2 ^ (m + 1) - 1 := le_trans (by norm_num) hm
  rw [average_phaseCollision_polyEval_eq_integral m hm4 e,
    average_phaseCollision_sq_polyEval_eq_integral m hm e]
  have h := integral_box_variance_phaseCollision_le e horth
  rw [hcard] at h
  calc (∫ x in torusBox (ι → Bool), phaseCollision e x ^ (2 : ℕ)) -
        (∫ x in torusBox (ι → Bool), phaseCollision e x) ^ (2 : ℕ)
      ≤ 96 * (Fintype.card (ι → Bool) : ℝ) / (Fintype.card (ι → Bool) : ℝ) ^ (4 : ℕ) := h
    _ = 96 / (Fintype.card (ι → Bool) : ℝ) ^ (3 : ℕ) := by field_simp

/-- **`(9)` for the finite cubic-phase ensemble.**  Against any orthonormal basis of the register,
the fraction of degree-`≤ m` eighth-root phase polynomials whose seed has spectral collision above
`(2 + κ)/D` is at most `96/(κ² D)`, where `D` is the register dimension.  Both collision moments of
the ensemble are the Steinhaus ones by the eighth-root transfer, so the continuous Chebyshev bound
holds verbatim on the counting measure of the coefficient space. -/
theorem card_filter_phaseCollision_polyEval_gt_le (m : ℕ) (hm : 8 ≤ 2 ^ (m + 1) - 1)
    (e : J → (ι → Bool) → ℂ)
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0)
    (hcard : Fintype.card J = Fintype.card (ι → Bool)) {κ : ℝ} (hκ : 0 < κ) :
    ((univ.filter fun c : MonLe ι m → ZMod 8 =>
        (2 + κ) / (Fintype.card (ι → Bool) : ℝ)
          < phaseCollision e (eighthPhase (polyEval m c))).card : ℝ)
        * ((Fintype.card (MonLe ι m → ZMod 8) : ℝ))⁻¹
      ≤ 96 / (κ ^ (2 : ℕ) * (Fintype.card (ι → Bool) : ℝ)) := by
  classical
  haveI : Nonempty (MonLe ι m → ZMod 8) := ⟨fun _ => 0⟩
  have hDR : (0 : ℝ) < (Fintype.card (ι → Bool) : ℝ) := by
    have : 0 < Fintype.card (ι → Bool) := Fintype.card_pos
    exact_mod_cast this
  have hm4 : 4 ≤ 2 ^ (m + 1) - 1 := le_trans (by norm_num) hm
  have hcheb := card_filter_gt_le_of_mean_le
    (fun c : MonLe ι m → ZMod 8 => phaseCollision e (eighthPhase (polyEval m c)))
    (κ := κ / (Fintype.card (ι → Bool) : ℝ)) (by positivity)
    (average_phaseCollision_polyEval_le m hm4 e horth hcard)
    (variance_phaseCollision_polyEval_le m hm e horth hcard)
  rw [← collision_threshold_split (ne_of_gt hDR)] at hcheb
  rw [collision_tail_scale hDR hκ] at hcheb
  exact hcheb

/-- **`(27)`.**  The mean of the squared positive part above an upper mean bound is at most the
variance bound: the positive part above `m` is dominated by the deviation from the true mean. -/
theorem sum_posPart_sq_le_of_mean_var {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) {m V : ℝ}
    (hmean : ((Fintype.card Ω : ℝ))⁻¹ * ∑ c, X c ≤ m)
    (hvar : ((Fintype.card Ω : ℝ))⁻¹ * ∑ c, (X c) ^ (2 : ℕ)
      - (((Fintype.card Ω : ℝ))⁻¹ * ∑ c, X c) ^ (2 : ℕ) ≤ V) :
    ((Fintype.card Ω : ℝ))⁻¹ * ∑ c, (max (X c - m) 0) ^ (2 : ℕ) ≤ V := by
  classical
  set N := (Fintype.card Ω : ℝ) with hNdef
  have hNpos : 0 < N := by
    rw [hNdef]
    exact_mod_cast Fintype.card_pos
  set μ₁ := N⁻¹ * ∑ c, X c with hμdef
  have hs : ∑ c, X c = N * μ₁ := by
    rw [hμdef, ← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]
  have hsum : ∑ c, (X c - μ₁) ^ (2 : ℕ) = (∑ c, (X c) ^ (2 : ℕ)) - N * μ₁ ^ (2 : ℕ) := by
    have hexp : ∀ c, (X c - μ₁) ^ (2 : ℕ) = (X c) ^ (2 : ℕ) - 2 * μ₁ * X c + μ₁ ^ (2 : ℕ) := fun c => by ring
    rw [Finset.sum_congr rfl (fun c _ => hexp c), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← hNdef, hs]
    ring
  have hpt : ∀ c, (max (X c - m) 0) ^ (2 : ℕ) ≤ (X c - μ₁) ^ (2 : ℕ) := by
    intro c
    rcases le_or_gt (X c) m with hle | hgt
    · rw [max_eq_right (by linarith)]
      nlinarith [sq_nonneg (X c - μ₁)]
    · rw [max_eq_left (by linarith)]
      have h1 : 0 ≤ X c - m := by linarith
      have h2 : X c - m ≤ X c - μ₁ := by linarith [hmean]
      nlinarith [h1, h2]
  have hle : ∑ c, (max (X c - m) 0) ^ (2 : ℕ) ≤ (∑ c, (X c) ^ (2 : ℕ)) - N * μ₁ ^ (2 : ℕ) := by
    rw [← hsum]
    exact Finset.sum_le_sum fun c _ => hpt c
  have hvar' : (∑ c, (X c) ^ (2 : ℕ)) - N * μ₁ ^ (2 : ℕ) ≤ N * V := by
    have hmul := mul_le_mul_of_nonneg_left hvar (le_of_lt hNpos)
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul] at hmul
    have hsq : N * (N⁻¹ * ∑ c, X c) ^ (2 : ℕ) = N * μ₁ ^ (2 : ℕ) := by rw [← hμdef]
    rw [hsq] at hmul
    linarith [hmul]
  have hfinal : ∑ c, (max (X c - m) 0) ^ (2 : ℕ) ≤ N * V := le_trans hle hvar'
  rw [← div_le_iff₀' hNpos] at hfinal
  calc N⁻¹ * ∑ c, (max (X c - m) 0) ^ (2 : ℕ) = (∑ c, (max (X c - m) 0) ^ (2 : ℕ)) / N := by
        rw [div_eq_inv_mul]
    _ ≤ V := hfinal

/-- **`(28)` at a fixed basis.**  The ensemble mean of the squared positive part of the collision
above `2/D` is at most `96/D³`. -/
theorem sum_posPart_sq_phaseCollision_polyEval_le (m : ℕ) (hm : 8 ≤ 2 ^ (m + 1) - 1)
    (e : J → (ι → Bool) → ℂ)
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0)
    (hcard : Fintype.card J = Fintype.card (ι → Bool)) :
    ((Fintype.card (MonLe ι m → ZMod 8) : ℝ))⁻¹ *
        ∑ c : MonLe ι m → ZMod 8,
          (max (phaseCollision e (eighthPhase (polyEval m c))
            - 2 / (Fintype.card (ι → Bool) : ℝ)) 0) ^ (2 : ℕ)
      ≤ 96 / (Fintype.card (ι → Bool) : ℝ) ^ (3 : ℕ) := by
  classical
  haveI : Nonempty (MonLe ι m → ZMod 8) := ⟨fun _ => 0⟩
  have hm4 : 4 ≤ 2 ^ (m + 1) - 1 := le_trans (by norm_num) hm
  exact sum_posPart_sq_le_of_mean_var
    (fun c : MonLe ι m → ZMod 8 => phaseCollision e (eighthPhase (polyEval m c)))
    (average_phaseCollision_polyEval_le m hm4 e horth hcard)
    (variance_phaseCollision_polyEval_le m hm e horth hcard)

end GaloisForLFunctions.HTGeometry

end
