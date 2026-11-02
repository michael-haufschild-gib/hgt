import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Coercivity from relative quasimode residuals

A lower frame bound forces every vector to have substantial frame coordinates. An eigenvector
below half the prescribed energy floor would instead have all its coordinates controlled by
the relative residuals. This contradiction retains individual energies in the error budget.
-/

noncomputable section

open Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

set_option autoImplicit false

/-- Small summed relative residuals force a symmetric operator above half the common energy
floor. The residual denominator retains each quasimode's individual energy. -/
theorem inner_ge_half_floor_of_relative_frame_budget
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (v : ι → E) (ε : ι → ℝ) {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ)
    (hframe : ∀ x : E, κ * ‖x‖ ^ 2 ≤ ∑ j, ⟪v j, x⟫ ^ 2)
    (hfloor : ∀ j, δ ≤ ε j)
    (hbudget : (∑ j, ‖T (v j) - ε j • v j‖ ^ 2 / ε j ^ 2) ≤ κ / 8) :
    ∀ x : E, δ / 2 * ‖x‖ ^ 2 ≤ ⟪T x, x⟫ := by
  classical
  let n := Module.finrank ℝ E
  let b := hT.eigenvectorBasis (n := n) rfl
  let eig := hT.eigenvalues (n := n) rfl
  have hnorm (i : Fin n) : ‖b i‖ = 1 := by
    have hh : ⟪b i, b i⟫ = (1 : ℝ) := by
      simpa only [ite_true] using (orthonormal_iff_ite.mp b.orthonormal) i i
    rw [real_inner_self_eq_norm_sq] at hh
    nlinarith only [hh, norm_nonneg (b i)]
  have hcoeff (x : E) (i : Fin n) : ⟪b i, T x⟫ = eig i * ⟪b i, x⟫ := by
    rw [← b.repr_apply_apply, ← b.repr_apply_apply]
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using
      hT.eigenvectorBasis_apply_self_apply (n := n) rfl x i
  have heig_floor (i : Fin n) : δ / 2 ≤ eig i := by
    by_contra hi
    have hi' : eig i < δ / 2 := lt_of_not_ge hi
    have hpoint (j : ι) : ⟪v j, b i⟫ ^ 2 ≤
        4 * ‖T (v j) - ε j • v j‖ ^ 2 / ε j ^ 2 := by
      rw [real_inner_comm (b i) (v j)]
      have hε : 0 < ε j := hδ.trans_le (hfloor j)
      have hid : ⟪b i, T (v j) - ε j • v j⟫ = (eig i - ε j) * ⟪b i, v j⟫ := by
        rw [inner_sub_right, real_inner_smul_right, hcoeff]
        ring
      have hcs := norm_inner_le_norm (𝕜 := ℝ) (b i) (T (v j) - ε j • v j)
      rw [Real.norm_eq_abs, hnorm, one_mul, hid] at hcs
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hcs 2
      rw [sq_abs, mul_pow] at hsq
      have hhalf : ε j / 2 ≤ ε j - eig i := by linarith only [hfloor j, hi']
      have hgap₀ := mul_self_le_mul_self (by positivity : 0 ≤ ε j / 2) hhalf
      have hgap : ε j ^ 2 / 4 ≤ (eig i - ε j) ^ 2 := by nlinarith only [hgap₀]
      have hmul := mul_le_mul_of_nonneg_right hgap (sq_nonneg ⟪b i, v j⟫)
      apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
      nlinarith only [hmul, hsq]
    have hsum : (∑ j, ⟪v j, b i⟫ ^ 2) ≤
        4 * ∑ j, ‖T (v j) - ε j • v j‖ ^ 2 / ε j ^ 2 := by
      calc
        _ ≤ ∑ j, 4 * ‖T (v j) - ε j • v j‖ ^ 2 / ε j ^ 2 :=
          sum_le_sum fun j _ => hpoint j
        _ = _ := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    have hmass := hframe (b i)
    rw [hnorm, one_pow, mul_one] at hmass
    linarith only [hmass, hsum, hbudget, hκ]
  intro x
  have hparseval : (∑ i, (b.repr x i) ^ 2) = ‖x‖ ^ 2 := by
    calc
      _ = ∑ i, ⟪x, b i⟫ * ⟪b i, x⟫ := by
        apply sum_congr rfl
        intro i _
        rw [b.repr_apply_apply, real_inner_comm (b i) x]
        ring
      _ = ⟪x, x⟫ := b.sum_inner_mul_inner x x
      _ = _ := real_inner_self_eq_norm_sq x
  have hquadratic : ⟪x, T x⟫ = ∑ i, eig i * (b.repr x i) ^ 2 := by
    rw [← b.sum_inner_mul_inner x (T x)]
    apply sum_congr rfl
    intro i _
    rw [real_inner_comm (b i) x, hcoeff, ← b.repr_apply_apply]
    ring
  calc
    δ / 2 * ‖x‖ ^ 2 = δ / 2 * ∑ i, (b.repr x i) ^ 2 := by rw [hparseval]
    _ ≤ ∑ i, eig i * (b.repr x i) ^ 2 := by
      rw [mul_sum]
      exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (heig_floor i) (sq_nonneg _)
    _ = ⟪x, T x⟫ := hquadratic.symm
    _ = _ := real_inner_comm _ _

/-- The same relative budget controls a compression, using residuals in the ambient space.
Orthogonal projection contracts the residuals and preserves all relevant pairings. -/
theorem inner_ge_half_floor_on_subspace_of_relative_frame_budget
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric)
    (V : Submodule ℝ E) (v : ι → V) (ε : ι → ℝ) {κ δ : ℝ}
    (hκ : 0 < κ) (hδ : 0 < δ)
    (hframe : ∀ x : V, κ * ‖x‖ ^ 2 ≤ ∑ j, ⟪v j, x⟫ ^ 2)
    (hfloor : ∀ j, δ ≤ ε j)
    (hbudget : (∑ j, ‖A (v j : E) - ε j • (v j : E)‖ ^ 2 / ε j ^ 2) ≤ κ / 8) :
    ∀ x : V, δ / 2 * ‖x‖ ^ 2 ≤ ⟪A (x : E), (x : E)⟫ := by
  let T : V →ₗ[ℝ] V := V.orthogonalProjectionOnto.toLinearMap.comp (A.comp V.subtype)
  have hproj (y : E) (x : V) : ⟪V.orthogonalProjectionOnto y, x⟫ = ⟪y, (x : E)⟫ := by
    change ⟪V.starProjection y, (x : E)⟫ = _
    have hh := V.starProjection_inner_eq_zero y (x : E) x.property
    rw [inner_sub_left] at hh
    linarith only [hh]
  have hT : T.IsSymmetric := by
    intro x y
    change ⟪V.orthogonalProjectionOnto (A (x : E)), y⟫ =
      ⟪x, V.orthogonalProjectionOnto (A (y : E))⟫
    calc
      _ = ⟪A (x : E), (y : E)⟫ := hproj _ _
      _ = ⟪(x : E), A (y : E)⟫ := hA _ _
      _ = ⟪A (y : E), (x : E)⟫ := real_inner_comm _ _
      _ = ⟪V.orthogonalProjectionOnto (A (y : E)), x⟫ := (hproj _ _).symm
      _ = _ := real_inner_comm _ _
  have hres (j : ι) : ‖T (v j) - ε j • v j‖ ^ 2 ≤
      ‖A (v j : E) - ε j • (v j : E)‖ ^ 2 := by
    have heq : T (v j) - ε j • v j =
        V.orthogonalProjectionOnto (A (v j : E) - ε j • (v j : E)) := by
      change V.orthogonalProjectionOnto (A (v j : E)) - ε j • v j = _
      rw [map_sub, map_smul, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    rw [heq]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (V.norm_orthogonalProjectionOnto_apply_le _) 2
  have hsmall : (∑ j, ‖T (v j) - ε j • v j‖ ^ 2 / ε j ^ 2) ≤ κ / 8 :=
    (sum_le_sum fun j _ => div_le_div_of_nonneg_right (hres j) (sq_nonneg _)).trans hbudget
  have hbound := inner_ge_half_floor_of_relative_frame_budget T hT v ε hκ hδ hframe hfloor hsmall
  intro x
  have hh := hbound x
  change δ / 2 * ‖x‖ ^ 2 ≤ ⟪V.orthogonalProjectionOnto (A (x : E)), x⟫ at hh
  rwa [hproj] at hh

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
