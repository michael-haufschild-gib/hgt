import GaloisForLFunctions.HTGeometry.GomesMomentNormalizedFlux
import GaloisForLFunctions.HTGeometry.MatrixQuadraticFormDetermination

/-!
# Recovering the full flux tensor from actual internal observations

Application of faithful tensor reconstruction in https://arxiv.org/abs/2607.24901,
observation Gram kernels in https://arxiv.org/abs/2509.25276, and internal-frame
geometry in https://arxiv.org/abs/2404.10461. The existing corpus polarization
theorem upgrades every wave-energy identity to equality of full matrices.
The normalized flux is exactly twice source height times the finite observation
Gram tensor. Positivity, scalar signs, the zero boundary, and reversed orientation
are classified without supplied mathematical proof hypotheses.
-/

open scoped Matrix ComplexOrder BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- One rank-one internal observation has exactly its squared amplitude as quadratic energy. -/
theorem gomesObservationRankOne_quadratic (r v : Fin 2 → ℂ) :
    star v ⬝ᵥ (Matrix.vecMulVec (star r) r *ᵥ v) = ((Complex.normSq (r ⬝ᵥ v) : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [Matrix.vecMulVec,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Complex.normSq_apply] <;> ring

/-- The full finite tensor of weighted observations of the two actual polynomial solutions. -/
def gomesMomentObservationGram (M : GomesMomentModel) (n : ℕ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ k ∈ Finset.range (n+1),
    (momentInner M.moments (monicOrtho M.moments k) (monicOrtho M.moments k))⁻¹ •
      Matrix.vecMulVec (star ![monicOrthoC M.moments k z,secondKindC M.moments k z])
        ![monicOrthoC M.moments k z,secondKindC M.moments k z]

/-- Every diagonal quadratic observation of the Gram tensor is exactly the previously proved wave energy. -/
theorem gomesMomentObservationGram_quadratic (M : GomesMomentModel) (n : ℕ) (z : ℂ) (v : Fin 2 → ℂ) :
    star v ⬝ᵥ (gomesMomentObservationGram M n z *ᵥ v) =
      ((gomesMomentWaveEnergy M v n z : ℝ) : ℂ) := by
  simp only [gomesMomentObservationGram,Matrix.sum_mulVec,dotProduct_sum,
    Matrix.smul_mulVec,dotProduct_smul,gomesObservationRankOne_quadratic]
  unfold gomesMomentWaveEnergy
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Complex.ext <;>
    simp [gomesMomentWave,dotProduct,Fin.sum_univ_two,div_eq_mul_inv,mul_comm]

/-- A real observation weight multiplies every quadratic energy by exactly that weight. -/
theorem gomesMomentObservationGram_smul_quadratic (M : GomesMomentModel) (n : ℕ) (z : ℂ)
    (c : ℝ) (v : Fin 2 → ℂ) :
    star v ⬝ᵥ ((c • gomesMomentObservationGram M n z) *ᵥ v) =
      ((c*gomesMomentWaveEnergy M v n z : ℝ) : ℂ) := by
  rw [Matrix.smul_mulVec,dotProduct_smul,gomesMomentObservationGram_quadratic]
  apply Complex.ext <;> simp

/-- Real wave energies force the reconstructed tensor to be Hermitian. -/
theorem gomesMomentObservationGram_isHermitian (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    (gomesMomentObservationGram M n z).IsHermitian := by
  change (gomesMomentObservationGram M n z)ᴴ = gomesMomentObservationGram M n z
  apply matrix_eq_of_quadraticForm_eq
  intro v
  rw [matrixQuadraticForm_conjTranspose,gomesMomentObservationGram_quadratic]
  simp

/-- Every finite observation Gram tensor is positive semidefinite. -/
theorem gomesMomentObservationGram_posSemidef (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    (gomesMomentObservationGram M n z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (gomesMomentObservationGram_isHermitian M n z)
  intro v
  rw [gomesMomentObservationGram_quadratic]
  exact Complex.zero_le_real.mpr (gomesMomentWaveEnergy_nonneg M v n z)

/-- The observation tensor is positive definite exactly when both initial directions have been observed. -/
theorem gomesMomentObservationGram_posDef_iff (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    (gomesMomentObservationGram M n z).PosDef ↔ n ≠ 0 := by
  constructor
  · intro h hn
    have hv : (![0,1] : Fin 2 → ℂ) ≠ 0 := by
      intro he
      have h1 := congrFun he 1
      simp at h1
    have hq := h.dotProduct_mulVec_pos hv
    rw [gomesMomentObservationGram_quadratic] at hq
    simp [hn,gomesMomentWaveEnergy,gomesMomentWave] at hq
  · intro hn
    cases n with
    | zero => exact (hn rfl).elim
    | succ n =>
        apply Matrix.PosDef.of_dotProduct_mulVec_pos (gomesMomentObservationGram_isHermitian M (n+1) z)
        intro v hv
        rw [gomesMomentObservationGram_quadratic]
        exact Complex.zero_lt_real.mpr ((gomesMomentWaveEnergy_succ_pos_iff M v n z).mpr hv)

/-- The Gram tensor retains the sign of any scalar observation weight. -/
theorem gomesMomentObservationGram_smul_posSemidef_iff (M : GomesMomentModel) (n : ℕ) (z : ℂ) (c : ℝ) :
    (c • gomesMomentObservationGram M n z).PosSemidef ↔ 0 ≤ c := by
  constructor
  · intro h
    have hq := h.dotProduct_mulVec_nonneg ![1,0]
    rw [gomesMomentObservationGram_smul_quadratic] at hq
    have hr := Complex.zero_le_real.mp hq
    have he := gomesMomentWaveEnergy_unit_pos M n z
    by_contra hc
    exact not_lt_of_ge hr (mul_neg_of_neg_of_pos (lt_of_not_ge hc) he)
  · intro hc
    exact (gomesMomentObservationGram_posSemidef M n z).smul hc

/-- Strict scalar-weighted positivity also detects exactly the second observation. -/
theorem gomesMomentObservationGram_smul_posDef_iff (M : GomesMomentModel) (n : ℕ) (z : ℂ) (c : ℝ) :
    (c • gomesMomentObservationGram M n z).PosDef ↔ 0 < c ∧ n ≠ 0 := by
  constructor
  · intro h
    have hv : (![1,0] : Fin 2 → ℂ) ≠ 0 := by
      intro he
      have h0 := congrFun he 0
      simp at h0
    have hq := h.dotProduct_mulVec_pos hv
    rw [gomesMomentObservationGram_smul_quadratic] at hq
    have hr := Complex.zero_lt_real.mp hq
    have he := gomesMomentWaveEnergy_unit_pos M n z
    have hc : 0 < c := by
      rcases mul_pos_iff.mp hr with hh | hh
      · exact hh.1
      · exact (not_lt_of_ge he.le hh.2).elim
    have hG := h.smul (inv_pos.mpr hc)
    rw [smul_smul,inv_mul_cancel₀ hc.ne',one_smul] at hG
    exact ⟨hc,(gomesMomentObservationGram_posDef_iff M n z).mp hG⟩
  · rintro ⟨hc,hn⟩
    exact ((gomesMomentObservationGram_posDef_iff M n z).mpr hn).smul hc

/-- Full tensor reconstruction: all wave-energy observations identify the entire normalized flux matrix. -/
theorem gomesMomentNormalizedFlux_eq_height_smul_gram (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    gomesMomentNormalizedFlux M n z = (2*z.im : ℝ) • gomesMomentObservationGram M n z := by
  apply matrix_eq_of_quadraticForm_eq
  intro v
  rw [gomesMomentNormalizedFlux_quadratic,gomesMomentObservationGram_smul_quadratic]

/-- The normalized tensor vanishes exactly on the real spectral boundary, at every level. -/
theorem gomesMomentNormalizedFlux_eq_zero_iff (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    gomesMomentNormalizedFlux M n z = 0 ↔ z.im = 0 := by
  constructor
  · intro h
    have hq := gomesMomentNormalizedFlux_quadratic M n z ![1,0]
    rw [h] at hq
    have hr := congrArg Complex.re hq
    simp at hr
    have he := (gomesMomentWaveEnergy_unit_pos M n z).ne'
    exact hr.resolve_right he
  · intro h
    simp [gomesMomentNormalizedFlux_eq_height_smul_gram,h]

/-- Reversing flux orientation detects the lower half-plane with the same exact observation threshold. -/
theorem gomesMomentNormalizedFlux_neg_posDef_iff (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    (-gomesMomentNormalizedFlux M n z).PosDef ↔ z.im < 0 ∧ n ≠ 0 := by
  rw [gomesMomentNormalizedFlux_eq_height_smul_gram,← neg_smul,
    gomesMomentObservationGram_smul_posDef_iff]
  constructor
  · rintro ⟨h,hn⟩
    exact ⟨by linarith,hn⟩
  · rintro ⟨h,hn⟩
    exact ⟨by linarith,hn⟩

end GaloisForLFunctions.HTGeometry
