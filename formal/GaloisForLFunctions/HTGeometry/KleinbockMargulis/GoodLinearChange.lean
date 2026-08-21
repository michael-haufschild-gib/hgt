import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Good
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Goodness under an invertible linear change of variables

Sup-norm balls in `Fin d → ℝ` are cubes, and a linear map does not send cubes to cubes.  The
image of a cube is nevertheless contained in a cube whose side is scaled by the operator norm, and
the Lebesgue measure is scaled by the determinant, so `(C, α)`-goodness transfers along an
invertible linear change of variables with the constant multiplied by `|det T| ‖T⁻¹‖^d`.

This replaces the circumscribed-cube step of Kleinbock–Margulis, which is needed there because
their Lemma 3.3 is stated for cubes while goodness is stated for Euclidean balls.

## Main results

* `isGood_of_comp_linear` — the transfer with an abstract compatibility hypothesis on the domains.
* `radius_le_of_ball_subset_ball` — a cube contained in a cube has no larger radius.
* `isGood_of_comp_linear_ball` — the transfer between concrete cubes.
-/

open MeasureTheory Metric Set

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {d : ℕ}

/-- A ball contained in a ball has no larger radius. -/
theorem radius_le_of_ball_subset_ball [NeZero d] {x₀ x₁ : Fin d → ℝ} {r ρ : ℝ} (hr : 0 < r)
    (h : ball x₀ r ⊆ ball x₁ ρ) : r ≤ ρ := by
  by_contra hcon
  push Not at hcon
  set e : Fin d → ℝ := fun _ => (1 : ℝ) with he
  have hnorme : ‖e‖ = 1 := by rw [he, pi_norm_const]; simp
  have hρpos : 0 < ρ := lt_of_le_of_lt dist_nonneg (h (mem_ball_self hr))
  set t : ℝ := (r + ρ) / 2 with ht
  have ht1 : 0 < t := by rw [ht]; linarith
  have ht2 : t < r := by rw [ht]; linarith
  have ht3 : ρ < t := by rw [ht]; linarith
  have hmem1 : x₀ + t • e ∈ ball x₀ r := by
    rw [mem_ball, dist_eq_norm]
    simpa [norm_smul, hnorme, abs_of_pos ht1] using ht2
  have hmem2 : x₀ - t • e ∈ ball x₀ r := by
    rw [mem_ball, dist_eq_norm]
    simpa [norm_smul, hnorme, abs_of_pos ht1] using ht2
  have h1 := h hmem1
  have h2 := h hmem2
  rw [mem_ball, dist_eq_norm] at h1 h2
  have hsum : ‖(x₀ + t • e) - (x₀ - t • e)‖ ≤ ‖(x₀ + t • e) - x₁‖ + ‖x₁ - (x₀ - t • e)‖ := by
    have : (x₀ + t • e) - (x₀ - t • e) = ((x₀ + t • e) - x₁) + (x₁ - (x₀ - t • e)) := by
      abel
    rw [this]
    exact norm_add_le _ _
  have hval : ‖(x₀ + t • e) - (x₀ - t • e)‖ = 2 * t := by
    have hsm : (x₀ + t • e) - (x₀ - t • e) = (2 * t) • e := by module
    rw [hsm, norm_smul, hnorme, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [hval, ← norm_neg (x₁ - (x₀ - t • e))] at hsum
  simp only [neg_sub] at hsum
  linarith

/-- **Goodness transfers along an invertible linear change of variables.** -/
theorem isGood_of_comp_linear {C α : ℝ} (hC : 0 ≤ C)
    (T : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) {f : (Fin d → ℝ) → ℝ} {V W : Set (Fin d → ℝ)}
    (hS : 0 < ‖(T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))‖)
    (hW : ∀ (x₀ : Fin d → ℝ) (r : ℝ), 0 < r → ball x₀ r ⊆ V →
      ball (T.symm x₀) (‖(T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))‖ * r) ⊆ W)
    (hg : IsGood C α (f ∘ T) W) :
    IsGood (C * |LinearMap.det ((T : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
        : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))|
      * ‖(T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))‖ ^ d) α f V := by
  classical
  set S : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) := (T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) with hSdef
  set TL : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) := ((T : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) with hTL
  refine isGood_of_toReal ?_
  intro x₀ r hr hsub ε hε z hz
  set ρ : ℝ := ‖S‖ * r with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; exact mul_pos hS hr
  have hball : ball (T.symm x₀) ρ ⊆ W := hW x₀ r hr hsub
  -- points of the preimage stay in the enlarged ball
  have hpre : ∀ y : Fin d → ℝ, T y ∈ ball x₀ r → y ∈ ball (T.symm x₀) ρ := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have hyy : y - T.symm x₀ = S (T y - x₀) := by
      rw [map_sub]
      simp [hSdef]
    rw [hyy, hρdef]
    exact lt_of_le_of_lt (S.le_opNorm _) (mul_lt_mul_of_pos_left hy hS)
  -- the change of variables for the measure
  have himg : (⇑TL) '' {y | T y ∈ ball x₀ r ∧ |f (T y)| < ε} = {x ∈ ball x₀ r | |f x| < ε} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨T.symm x, by simpa using hx, by simp [hTL]⟩
  have hmeas : volume {x ∈ ball x₀ r | |f x| < ε}
      = ENNReal.ofReal |LinearMap.det TL| * volume {y | T y ∈ ball x₀ r ∧ |f (T y)| < ε} := by
    rw [← himg]
    exact MeasureTheory.Measure.addHaar_image_linearMap volume TL _

  -- goodness of `f ∘ T` on the enlarged ball
  have hz' : T.symm z ∈ ball (T.symm x₀) ρ := hpre _ (by simpa using hz)
  have hgood := hg.toReal_le hC (T.symm x₀) hρ hball hε hz'
  have hfz : (f ∘ T) (T.symm z) = f z := by simp
  rw [hfz] at hgood
  -- assemble
  have hsubset : {y | T y ∈ ball x₀ r ∧ |f (T y)| < ε}
      ⊆ {y ∈ ball (T.symm x₀) ρ | |(f ∘ T) y| < ε} := by
    intro y hy
    exact ⟨hpre y hy.1, hy.2⟩
  have hfin : volume {y ∈ ball (T.symm x₀) ρ | |(f ∘ T) y| < ε} ≠ ⊤ :=
    volume_sublevel_ne_top _ _ _ _
  have hmono : (volume {y | T y ∈ ball x₀ r ∧ |f (T y)| < ε}).toReal
      ≤ (volume {y ∈ ball (T.symm x₀) ρ | |(f ∘ T) y| < ε}).toReal :=
    ENNReal.toReal_mono hfin (measure_mono hsubset)
  have hvolT : (volume (ball (T.symm x₀) ρ)).toReal
      = ‖S‖ ^ d * (volume (ball x₀ r)).toReal := by
    rw [Real.volume_pi_ball _ hρ, Real.volume_pi_ball _ hr,
      ENNReal.toReal_ofReal (pow_nonneg (by linarith) _),
      ENNReal.toReal_ofReal (pow_nonneg (by linarith) _)]
    simp only [Fintype.card_fin]
    rw [hρdef, show (2 * (‖S‖ * r) : ℝ) = ‖S‖ * (2 * r) by ring, mul_pow]
  have hdetnn : (0:ℝ) ≤ |LinearMap.det TL| := abs_nonneg _
  have hεnn : (0:ℝ) ≤ ε ^ α := Real.rpow_nonneg hε.le _
  have hfnn : (0:ℝ) ≤ |f z| ^ α := Real.rpow_nonneg (abs_nonneg _) _
  rw [hmeas, ENNReal.toReal_mul, ENNReal.toReal_ofReal hdetnn]
  calc |LinearMap.det TL| * (volume {y | T y ∈ ball x₀ r ∧ |f (T y)| < ε}).toReal * |f z| ^ α
      = |LinearMap.det TL|
        * ((volume {y | T y ∈ ball x₀ r ∧ |f (T y)| < ε}).toReal * |f z| ^ α) := by ring
    _ ≤ |LinearMap.det TL|
        * ((volume {y ∈ ball (T.symm x₀) ρ | |(f ∘ T) y| < ε}).toReal * |f z| ^ α) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmono hfnn) hdetnn
    _ ≤ |LinearMap.det TL| * (C * ε ^ α * (volume (ball (T.symm x₀) ρ)).toReal) :=
        mul_le_mul_of_nonneg_left hgood hdetnn
    _ = C * |LinearMap.det TL| * ‖S‖ ^ d * ε ^ α * (volume (ball x₀ r)).toReal := by
        rw [hvolT]; ring

/-- The transfer between concrete cubes. -/
theorem isGood_of_comp_linear_ball [NeZero d] {C α : ℝ} (hC : 0 ≤ C)
    (T : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) {f : (Fin d → ℝ) → ℝ} {x₁ : Fin d → ℝ} {ρ : ℝ}
    (hS : 0 < ‖(T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))‖)
    (hg : IsGood C α (f ∘ T) (ball (T.symm x₁)
      (2 * ‖(T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))‖ * ρ))) :
    IsGood (C * |LinearMap.det ((T : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
        : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))|
      * ‖(T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))‖ ^ d) α f (ball x₁ ρ) := by
  refine isGood_of_comp_linear hC T hS ?_ hg
  intro x₀ r hr hsub y hy
  set S : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) := (T.symm : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) with hSdef
  have hrρ : r ≤ ρ := radius_le_of_ball_subset_ball hr hsub
  have hcentre : dist x₀ x₁ < ρ := hsub (mem_ball_self hr)
  rw [mem_ball] at hy ⊢
  have h1 : dist (T.symm x₀) (T.symm x₁) ≤ ‖S‖ * dist x₀ x₁ := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact S.le_opNorm _
  calc dist y (T.symm x₁) ≤ dist y (T.symm x₀) + dist (T.symm x₀) (T.symm x₁) := dist_triangle _ _ _
    _ < ‖S‖ * r + ‖S‖ * dist x₀ x₁ := by linarith
    _ ≤ 2 * ‖S‖ * ρ := by nlinarith

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
