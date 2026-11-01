import GaloisForLFunctions.HTGeometry.GroundOverlap
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A finite negative Hilbert factor

The difference of two Hilbert inner products is a nondegenerate Hermitian
form. Graphs of contractions are nonpositive, and their orthogonal
complements are nonnegative.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The positive Hilbert form minus the negative Hilbert form. -/
def pairing (v w : H × E) : ℂ := inner ℂ v.1 w.1 - inner ℂ v.2 w.2

theorem pairing_conj_symm (v w : H × E) : conj (pairing w v) = pairing v w := by
  simp only [pairing, map_sub, inner_conj_symm]

theorem pairing_smul_left (a : ℂ) (v w : H × E) :
    pairing (a • v) w = conj a * pairing v w := by
  simp only [pairing, Prod.smul_fst, Prod.smul_snd, inner_smul_left, mul_sub]

theorem pairing_smul_right (a : ℂ) (v w : H × E) :
    pairing v (a • w) = a * pairing v w := by
  simp only [pairing, Prod.smul_fst, Prod.smul_snd, inner_smul_right, mul_sub]

theorem pairing_add_left (u v w : H × E) :
    pairing (u + v) w = pairing u w + pairing v w := by
  simp only [pairing, Prod.fst_add, Prod.snd_add, inner_add_left]
  ring

theorem pairing_add_right (u v w : H × E) :
    pairing u (v + w) = pairing u v + pairing u w := by
  simp only [pairing, Prod.fst_add, Prod.snd_add, inner_add_right]
  ring

theorem pairing_self_re (v : H × E) :
    (pairing v v).re = ‖v.1‖ ^ 2 - ‖v.2‖ ^ 2 := by
  rw [pairing, Complex.sub_re]
  exact congrArg₂ (fun x y : ℝ => x - y)
    (inner_self_eq_norm_sq (𝕜 := ℂ) v.1) (inner_self_eq_norm_sq (𝕜 := ℂ) v.2)

theorem pairing_self_nonpos_iff (v : H × E) :
    (pairing v v).re ≤ 0 ↔ ‖v.1‖ ≤ ‖v.2‖ := by
  rw [pairing_self_re, sub_nonpos]
  exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)

theorem eq_zero_of_nonpositive_snd_eq_zero {v : H × E}
    (hq : (pairing v v).re ≤ 0) (hs : v.2 = 0) : v = 0 := by
  have h := (pairing_self_nonpos_iff v).mp hq
  rw [hs, norm_zero] at h
  exact Prod.ext (norm_eq_zero.mp (le_antisymm h (norm_nonneg _))) hs

/-- Orthogonality to a contraction graph forces a nonnegative square. -/
theorem nonneg_of_orthogonal_contraction_graph (A : E →ₗ[ℂ] H)
    (hA : ∀ x, ‖A x‖ ≤ ‖x‖) {v : H × E}
    (ho : ∀ x, pairing (A x, x) v = 0) : 0 ≤ (pairing v v).re := by
  have hpair : inner ℂ (A v.2) v.1 = inner ℂ v.2 v.2 := sub_eq_zero.mp (ho v.2)
  have hs : ‖v.2‖ ^ 2 ≤ ‖v.2‖ * ‖v.1‖ := by
    calc
      ‖v.2‖ ^ 2 = ‖inner ℂ v.2 v.2‖ := (GaloisForLFunctions.HTGeometry.norm_inner_self_eq _).symm
      _ = ‖inner ℂ (A v.2) v.1‖ := congrArg norm hpair.symm
      _ ≤ ‖A v.2‖ * ‖v.1‖ := norm_inner_le_norm _ _
      _ ≤ ‖v.2‖ * ‖v.1‖ := mul_le_mul_of_nonneg_right (hA v.2) (norm_nonneg _)
  have hn : ‖v.2‖ ≤ ‖v.1‖ := by
    nlinarith only [hs, norm_nonneg v.2, norm_nonneg v.1]
  rw [pairing_self_re]
  exact sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn)

theorem norm_pairing_le (v w : H × E) :
    ‖pairing v w‖ ≤ (‖v.1‖ + ‖v.2‖) * ‖w‖ := by
  calc
    ‖pairing v w‖ ≤ ‖inner ℂ v.1 w.1‖ + ‖inner ℂ v.2 w.2‖ := norm_sub_le _ _
    _ ≤ ‖v.1‖ * ‖w.1‖ + ‖v.2‖ * ‖w.2‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖v.1‖ * ‖w‖ + ‖v.2‖ * ‖w‖ := add_le_add
      (mul_le_mul_of_nonneg_left (norm_fst_le w) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (norm_snd_le w) (norm_nonneg _))
    _ = _ := (add_mul _ _ _).symm

theorem continuous_pairing : Continuous (fun p : (H × E) × (H × E) => pairing p.1 p.2) := by
  unfold pairing
  fun_prop

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
