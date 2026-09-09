import GaloisForLFunctions.HTGeometry.GomesMomentComplexFrameEnergy

/-!
# Complete matrix positivity boundary for normalized moment-frame flux

Application of internal-frame transport from https://arxiv.org/abs/2404.10461
and observation Gram kernels from https://arxiv.org/abs/2509.25276.
The normalized Hermitian flux matrix is evaluated exactly by weighted wave
energy. It is positive semidefinite precisely on the closed upper half-plane,
and positive definite precisely on the open upper half-plane after at least
two levels have been observed. All model positivity and coupling conditions
are proved internally; these are closed classifications including every level.
-/

open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- A weighted congruence of the flux tensor evaluates as the same weighted sum of internal fluxes. -/
theorem gomesInternalFlux_matrix_congruence (A : Matrix (Fin 2) (Fin 2) ℂ)
    (r t : ℝ) (v : Fin 2 → ℂ) :
    star v ⬝ᵥ ((r • (Aᴴ*gomesJacobiFlux*A)+t • gomesJacobiFlux) *ᵥ v) =
      ((r*gomesInternalFlux (A *ᵥ v)+t*gomesInternalFlux v : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [gomesInternalFlux,gomesJacobiFlux,gomesShearAreaMatrix,Matrix.mul_apply,
      Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.conjTranspose_apply] <;> ring

/-- The full frame's flux, normalized by its actual moment norm and corrected by its initial boundary. -/
def gomesMomentNormalizedFlux (M : GomesMomentModel) (n : ℕ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (momentInner M.moments (monicOrtho M.moments n) (monicOrtho M.moments n))⁻¹ •
    ((gomesMomentComplexFrame M n z)ᴴ*gomesJacobiFlux*gomesMomentComplexFrame M n z) +
  (momentInner M.moments (monicOrtho M.moments 0) (monicOrtho M.moments 0))⁻¹ • gomesJacobiFlux

/-- The normalized boundary correction preserves Hermitian symmetry at every complex point. -/
theorem gomesMomentNormalizedFlux_isHermitian (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    (gomesMomentNormalizedFlux M n z).IsHermitian := by
  have h := gomesJacobiFlux_isHermitian
  change gomesJacobiFluxᴴ = gomesJacobiFlux at h
  change (gomesMomentNormalizedFlux M n z)ᴴ = gomesMomentNormalizedFlux M n z
  simp [gomesMomentNormalizedFlux,Matrix.conjTranspose_mul,Matrix.mul_assoc,h]

/-- The complete normalized flux form is exactly source height times observed wave energy. -/
theorem gomesMomentNormalizedFlux_quadratic (M : GomesMomentModel) (n : ℕ) (z : ℂ) (v : Fin 2 → ℂ) :
    star v ⬝ᵥ (gomesMomentNormalizedFlux M n z *ᵥ v) =
      ((2*z.im*gomesMomentWaveEnergy M v n z : ℝ) : ℂ) := by
  rw [gomesMomentNormalizedFlux,gomesInternalFlux_matrix_congruence]
  congr 1
  calc
    _ = gomesInternalFlux (gomesMomentComplexFrame M n z *ᵥ v) /
          momentInner M.moments (monicOrtho M.moments n) (monicOrtho M.moments n) +
        gomesInternalFlux v /
          momentInner M.moments (monicOrtho M.moments 0) (monicOrtho M.moments 0) := by ring
    _ = _ := gomesMomentComplexFrame_flux_energy M v n z

/-- The first internal direction already gives a strictly positive observation energy at every level. -/
theorem gomesMomentWaveEnergy_unit_pos (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    0 < gomesMomentWaveEnergy M ![1,0] n z := by
  apply Finset.sum_pos'
  · intro k hk
    exact div_nonneg (Complex.normSq_nonneg _) (gomesMomentModel_norm_pos M k).le
  · refine ⟨0,by simp,?_⟩
    rw [gomesMomentWave_zero]
    simpa using inv_pos.mpr (gomesMomentModel_norm_pos M 0)

/-- At every recurrence level, positive semidefinite normalized flux detects exactly the closed upper half-plane. -/
theorem gomesMomentNormalizedFlux_posSemidef_iff (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    (gomesMomentNormalizedFlux M n z).PosSemidef ↔ 0 ≤ z.im := by
  constructor
  · intro h
    have hq := h.dotProduct_mulVec_nonneg ![1,0]
    rw [gomesMomentNormalizedFlux_quadratic] at hq
    have hr := Complex.zero_le_real.mp hq
    have he := gomesMomentWaveEnergy_unit_pos M n z
    by_contra hz
    have hneg : 2*z.im*gomesMomentWaveEnergy M ![1,0] n z < 0 :=
      mul_neg_of_neg_of_pos (by linarith) he
    exact not_lt_of_ge hr hneg
  · intro hz
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (gomesMomentNormalizedFlux_isHermitian M n z)
    intro v
    rw [gomesMomentNormalizedFlux_quadratic]
    exact Complex.zero_le_real.mpr (mul_nonneg (by linarith) (gomesMomentWaveEnergy_nonneg M v n z))

/-- Strict positivity detects the open upper half-plane and exactly the presence of at least two observations. -/
theorem gomesMomentNormalizedFlux_posDef_iff (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    (gomesMomentNormalizedFlux M n z).PosDef ↔ 0 < z.im ∧ n ≠ 0 := by
  constructor
  · intro h
    have hv : (![1,0] : Fin 2 → ℂ) ≠ 0 := by
      intro he
      have h0 := congrFun he 0
      simp at h0
    have hq := h.dotProduct_mulVec_pos hv
    rw [gomesMomentNormalizedFlux_quadratic] at hq
    have hr := Complex.zero_lt_real.mp hq
    have he := gomesMomentWaveEnergy_unit_pos M n z
    have hz : 0 < z.im := by
      rcases mul_pos_iff.mp hr with hh | hh
      · linarith [hh.1]
      · exact (not_lt_of_ge he.le hh.2).elim
    refine ⟨hz,?_⟩
    intro hn
    have hv' : (![0,1] : Fin 2 → ℂ) ≠ 0 := by
      intro he
      have h1 := congrFun he 1
      simp at h1
    have hq' := h.dotProduct_mulVec_pos hv'
    rw [gomesMomentNormalizedFlux_quadratic] at hq'
    simp [hn,gomesMomentWaveEnergy,gomesMomentWave] at hq'
  · rintro ⟨hz,hn⟩
    cases n with
    | zero => exact (hn rfl).elim
    | succ n =>
        apply Matrix.PosDef.of_dotProduct_mulVec_pos (gomesMomentNormalizedFlux_isHermitian M (n+1) z)
        intro v hv
        rw [gomesMomentNormalizedFlux_quadratic]
        exact Complex.zero_lt_real.mpr (mul_pos (by linarith)
          ((gomesMomentWaveEnergy_succ_pos_iff M v n z).mpr hv))

end GaloisForLFunctions.HTGeometry
