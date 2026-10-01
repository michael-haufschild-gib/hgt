import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped ComplexConjugate

noncomputable section
namespace RHTower

/-- The complex Hilbert functional is the conjugate of the original bilinear channel test. -/
theorem norm_inner_steinhausEuclideanColumn {J : ℕ} (a : Fin J → ℂ)
    (w : EuclideanSpace ℂ (Fin J)) :
    ‖inner ℂ (WithLp.toLp 2 a) w‖ = ‖∑ j, a j * conj (w j)‖ := by
  have he : inner ℂ (WithLp.toLp 2 a) w = conj (∑ j, a j * conj (w j)) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply,
      map_sum, map_mul, starRingEnd_self_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, RCLike.norm_conj]

/-- Sup-norm coercivity of the literal bilinear channel form gives Euclidean frame coercivity. -/
theorem steinhausEuclideanFrame_lower {ι : Type*} [Fintype ι] {J : ℕ} (hJ : 0 < J)
    (a : ι → Fin J → ℂ) {H : ℝ} (hH : 0 ≤ H)
    (henergy : ∀ u : Fin J → ℂ, H * ‖u‖ ^ 2 ≤ ∑ i, ‖∑ j, a i j * u j‖ ^ 2)
    (w : EuclideanSpace ℂ (Fin J)) :
    H / J * ‖w‖ ^ 2 ≤ ∑ i, ‖inner ℂ (WithLp.toLp 2 (a i)) w‖ ^ 2 := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hsize : ‖w‖ ^ 2 ≤ (J : ℝ) * ‖fun j => conj (w j)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin J, ‖fun j => conj (w j)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        simpa only [RCLike.norm_conj] using norm_le_pi_norm (fun j => conj (w j)) j
      _ = _ := by simp
  simp_rw [norm_inner_steinhausEuclideanColumn]
  calc
    _ ≤ H / J * ((J : ℝ) * ‖fun j => conj (w j)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsize (div_nonneg hH hJR.le)
    _ = H * ‖fun j => conj (w j)‖ ^ 2 := by field_simp
    _ ≤ _ := henergy _

/-- A uniform sup-norm dot estimate bounds the actual column's Euclidean norm. -/
theorem norm_steinhausEuclideanColumn_le {J : ℕ} (a : Fin J → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hdot : ∀ u : Fin J → ℂ, ‖∑ j, a j * u j‖ ≤ L * ‖u‖) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℂ (Fin J))‖ ≤ L := by
  let w : EuclideanSpace ℂ (Fin J) := WithLp.toLp 2 a
  have hsup : ‖fun j => conj (w j)‖ ≤ ‖w‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
    intro j
    rw [RCLike.norm_conj]
    exact PiLp.norm_apply_le w j
  have hquad : ‖w‖ ^ 2 ≤ L * ‖w‖ := by
    calc
      _ = ‖inner ℂ w w‖ := (inner_self_eq_norm_sq (𝕜 := ℂ) w).symm.trans
        (inner_self_re_eq_norm (𝕜 := ℂ) w)
      _ = ‖∑ j, a j * conj (w j)‖ := norm_inner_steinhausEuclideanColumn a w
      _ ≤ L * ‖fun j => conj (w j)‖ := hdot _
      _ ≤ _ := mul_le_mul_of_nonneg_left hsup hL
  by_cases hz : ‖w‖ = 0
  · change ‖w‖ ≤ L
    simpa only [hz] using hL
  · have hp : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hz)
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa only [pow_two] using hquad)

/-- Summing the coordinate-unit tests bounds the full Euclidean column energy. -/
theorem steinhausEuclideanFrame_energy_upper {ι : Type*} [Fintype ι] {J : ℕ}
    (a : ι → Fin J → ℂ) (C : ℝ)
    (henergy : ∀ u : Fin J → ℂ, (∑ i, ‖∑ j, a i j * u j‖ ^ 2) ≤ C * ‖u‖ ^ 2) :
    (∑ i, ‖(WithLp.toLp 2 (a i) : EuclideanSpace ℂ (Fin J))‖ ^ 2) ≤ J * C := by
  have hcoord (j : Fin J) : (∑ i, ‖a i j‖ ^ 2) ≤ C := by
    simpa [Pi.single_apply, Pi.norm_single] using henergy (Pi.single j (1 : ℂ))
  simp only [EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _j : Fin J, C := Finset.sum_le_sum (fun j _ => hcoord j)
    _ = _ := by simp

end RHTower
