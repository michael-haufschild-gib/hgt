import GaloisForLFunctions.HTGeometry.RegularizedDeterminantLimit
import GaloisForLFunctions.HTGeometry.FredholmDeterminantInfinite

/-! # Entire determinants of kernels with strictly increasing off-diagonal degree

No uniform bound on block sizes is needed. Every closed path has constant
degree, so all power traces and the entire Hilbert–Carleman determinant
are fixed by the diagonal. Hilbert–Schmidt admission remains a separate,
genuine analytic obligation for applications.
-/

noncomputable section
open HilbertSchmidt

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*}

def GradedTriangular (degree : ι → ℕ) (K : ι × ι → ℂ) : Prop :=
  ∀ i j, i ≠ j → degree i ≤ degree j → K (i, j) = 0

theorem GradedTriangular.comp {degree : ι → ℕ} {K L : ι × ι → ℂ}
    (hK : GradedTriangular degree K) (hL : GradedTriangular degree L) :
    GradedTriangular degree (hsComp K L) := by
  intro i j hij hd
  have hz (k : ι) : K (i, k) * L (k, j) = 0 := by
    by_cases hik : i = k
    · subst k
      rw [hL i j hij hd, mul_zero]
    · by_cases hdk : degree i ≤ degree k
      · rw [hK i k hik hdk, zero_mul]
      · have hkj : k ≠ j := by intro h; subst k; exact hdk hd
        rw [hL k j hkj (le_trans (le_of_not_ge hdk) hd), mul_zero]
  simp only [hsComp, hz, tsum_zero]

theorem GradedTriangular.hsComp_diagonal {degree : ι → ℕ} {K L : ι × ι → ℂ}
    (hK : GradedTriangular degree K) (hL : GradedTriangular degree L) (i : ι) :
    hsComp K L (i, i) = K (i, i) * L (i, i) := by
  apply tsum_eq_single i
  intro j hji
  by_cases hd : degree i ≤ degree j
  · rw [hK i j hji.symm hd, zero_mul]
  · rw [hL j i hji (le_of_not_ge hd), mul_zero]

theorem GradedTriangular.pow {degree : ι → ℕ} {K : ι × ι → ℂ}
    (hK : GradedTriangular degree K) (n : ℕ) :
    GradedTriangular degree (hsPow K n) := by
  induction n with
  | zero => exact hK
  | succ n ih => exact hK.comp ih

theorem GradedTriangular.hsPow_diagonal {degree : ι → ℕ} {K : ι × ι → ℂ}
    (hK : GradedTriangular degree K) (n : ℕ) (i : ι) :
    hsPow K n (i, i) = K (i, i) ^ (n + 1) := by
  induction n with
  | zero => simp [HilbertSchmidt.hsPow]
  | succ n ih =>
    rw [HilbertSchmidt.hsPow, hK.hsComp_diagonal (hK.pow n), ih]
    ring

theorem GradedTriangular.fredholmDet_eq_diagonal [DecidableEq ι]
    {degree : ι → ℕ} {K : ι × ι → ℂ}
    (hK : GradedTriangular degree K) :
    fredholmDet K = fredholmDet (diagMul (fun i => K (i, i))) := by
  classical
  funext z
  unfold fredholmDet fredholmExp
  congr 2
  apply tsum_congr
  intro n
  congr 1
  apply tsum_congr
  intro i
  rw [hK.hsPow_diagonal, hsPow_diagMul]
  simp [diagMul]

/-- The identity holds for the entire determinant, not only its nonvanishing local exponential. -/
theorem GradedTriangular.entireDet2_eq_diagonal [DecidableEq ι]
    {degree : ι → ℕ} {K : ι × ι → ℂ} (hK : GradedTriangular degree K) :
    entireDet2 K = entireDet2 (diagMul (fun i => K (i, i))) := by
  unfold entireDet2 detCoeff
  rw [hK.fredholmDet_eq_diagonal]

end GaloisForLFunctions.HTGeometry
