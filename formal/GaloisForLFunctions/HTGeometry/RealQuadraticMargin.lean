import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Uniform margin of a negative definite real quadratic form

A real quadratic form on `Fin n → ℝ` that is strictly negative on every nonzero vector is
negative with a *uniform* margin: `Q c ≤ -δ ‖c‖²` for some `δ > 0`.  The mechanism is compactness
of the unit sphere in finite dimension together with homogeneity of the form.

Combined with the entrywise bound `|Q_A c - Q_B c| ≤ ε n² ‖c‖²`, this makes negative definiteness
of a Gram matrix stable under a sufficiently small entrywise perturbation.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric

variable {n : ℕ}

/-- The real quadratic form of a matrix. -/
def realQuad (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * c i * c j

theorem realQuad_zero (A : Matrix (Fin n) (Fin n) ℝ) : realQuad A 0 = 0 := by
  simp [realQuad]

/-- The form is homogeneous of degree two. -/
theorem realQuad_smul (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (c : Fin n → ℝ) :
    realQuad A (t • c) = t ^ 2 * realQuad A c := by
  simp only [realQuad, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem continuous_realQuad (A : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (realQuad A) := by
  unfold realQuad
  fun_prop

/-- The coordinate sum is controlled by the supremum norm. -/
theorem sum_abs_le_card_mul_norm (c : Fin n → ℝ) : ∑ i, |c i| ≤ (n : ℝ) * ‖c‖ := by
  calc ∑ i, |c i| ≤ ∑ _i : Fin n, ‖c‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        simpa [Real.norm_eq_abs] using norm_le_pi_norm c i
    _ = (n : ℝ) * ‖c‖ := by simp

/-- **Entrywise bound on the form.**  A matrix with all entries at most `ε` in absolute value has
quadratic form at most `ε n² ‖c‖²`. -/
theorem abs_realQuad_le_of_entries (A : Matrix (Fin n) (Fin n) ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hA : ∀ i j, |A i j| ≤ ε) (c : Fin n → ℝ) :
    |realQuad A c| ≤ ε * (n : ℝ) ^ 2 * ‖c‖ ^ 2 := by
  have hstep : |realQuad A c| ≤ ∑ i, ∑ j, ε * |c i| * |c j| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hA i j) (abs_nonneg _)) (abs_nonneg _)
  have hfact : ∑ i, ∑ j, ε * |c i| * |c j| = ε * (∑ i, |c i|) * (∑ j, |c j|) :=
    calc ∑ i, ∑ j, ε * |c i| * |c j|
        = ∑ i, (ε * |c i|) * ∑ j, |c j| := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ = (∑ i, ε * |c i|) * ∑ j, |c j| := by rw [Finset.sum_mul]
      _ = ε * (∑ i, |c i|) * ∑ j, |c j| := by rw [← Finset.mul_sum]
  have hsum := sum_abs_le_card_mul_norm c
  have hsum0 : (0 : ℝ) ≤ ∑ i, |c i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  calc |realQuad A c| ≤ ∑ i, ∑ j, ε * |c i| * |c j| := hstep
    _ = ε * (∑ i, |c i|) * (∑ j, |c j|) := hfact
    _ ≤ ε * ((n : ℝ) * ‖c‖) * ((n : ℝ) * ‖c‖) := by
        have h1 : ε * (∑ i, |c i|) ≤ ε * ((n : ℝ) * ‖c‖) :=
          mul_le_mul_of_nonneg_left hsum hε
        exact mul_le_mul h1 hsum hsum0 (by positivity)
    _ = ε * (n : ℝ) ^ 2 * ‖c‖ ^ 2 := by ring

/-- **Uniform margin of a negative definite form.**  A real quadratic form strictly negative on
every nonzero vector satisfies `Q c ≤ -δ ‖c‖²` for some `δ > 0`: the form is continuous, the unit
sphere is compact in finite dimension, so the form attains a strictly negative maximum there, and
homogeneity propagates the bound to every vector. -/
theorem exists_margin_of_negDef (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ c : Fin n → ℝ, c ≠ 0 → realQuad A c < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : Fin n → ℝ, realQuad A c ≤ -δ * ‖c‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, one_pos, fun c => ?_⟩
    have hc : c = 0 := Subsingleton.elim _ _
    subst hc
    simp [realQuad]
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hne : (sphere (0 : Fin n → ℝ) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hcomp : IsCompact (sphere (0 : Fin n → ℝ) 1) := isCompact_sphere 0 1
    obtain ⟨c₀, hc₀mem, hc₀max⟩ :=
      hcomp.exists_isMaxOn hne (continuous_realQuad A).continuousOn
    have hc₀norm : ‖c₀‖ = 1 := by rwa [mem_sphere_zero_iff_norm] at hc₀mem
    have hc₀ne : c₀ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hc₀norm
      norm_num at hc₀norm
    set δ := -realQuad A c₀ with hδdef
    have hδpos : 0 < δ := by
      have := hA c₀ hc₀ne
      simp only [hδdef]
      linarith
    refine ⟨δ, hδpos, fun c => ?_⟩
    rcases eq_or_ne c 0 with rfl | hc
    · simp [realQuad_zero]
    · have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc
      have hunit : ‖c‖⁻¹ • c ∈ sphere (0 : Fin n → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hcn.ne']
      have hmax : realQuad A (‖c‖⁻¹ • c) ≤ realQuad A c₀ :=
        (isMaxOn_iff.mp hc₀max) _ hunit
      rw [realQuad_smul] at hmax
      have : ‖c‖ ^ 2 * (‖c‖⁻¹ ^ 2 * realQuad A c) ≤ ‖c‖ ^ 2 * realQuad A c₀ :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
      rw [← mul_assoc] at this
      have hcancel : ‖c‖ ^ 2 * ‖c‖⁻¹ ^ 2 = 1 := by
        field_simp [hcn.ne']
      rw [hcancel, one_mul] at this
      calc realQuad A c ≤ ‖c‖ ^ 2 * realQuad A c₀ := this
        _ = -δ * ‖c‖ ^ 2 := by simp only [hδdef]; ring

/-- **Negative definiteness is stable under a small entrywise perturbation.**  If `A` is negative
definite with margin `δ` and every entry of `B - A` is at most `ε` with `ε n² < δ`, then `B` is
negative definite. -/
theorem negDef_of_entrywise_close {A B : Matrix (Fin n) (Fin n) ℝ} {δ ε : ℝ}
    (hε : 0 ≤ ε)
    (hmargin : ∀ c : Fin n → ℝ, realQuad A c ≤ -δ * ‖c‖ ^ 2)
    (hclose : ∀ i j, |B i j - A i j| ≤ ε)
    (hsmall : ε * (n : ℝ) ^ 2 < δ) :
    ∀ c : Fin n → ℝ, c ≠ 0 → realQuad B c < 0 := by
  intro c hc
  have hdiff : realQuad B c - realQuad A c = realQuad (B - A) c := by
    simp only [realQuad, Matrix.sub_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hbound : |realQuad (B - A) c| ≤ ε * (n : ℝ) ^ 2 * ‖c‖ ^ 2 :=
    abs_realQuad_le_of_entries _ hε (fun i j => by simpa using hclose i j) c
  have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hsq : 0 < ‖c‖ ^ 2 := by positivity
  have hA := hmargin c
  have h1 : realQuad B c ≤ realQuad A c + ε * (n : ℝ) ^ 2 * ‖c‖ ^ 2 := by
    have := (abs_le.1 hbound).2
    linarith [hdiff]
  nlinarith [h1, hA, hsq, hsmall]

end GaloisForLFunctions.HTGeometry
