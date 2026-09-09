import GaloisForLFunctions.HTGeometry.GomesMomentHeightExpansion
import GaloisForLFunctions.HTGeometry.GomesProjectiveFlux

/-!
# Whole complex frames and exact observation energy

Application of internal-frame geometry in https://arxiv.org/abs/2404.10461 and
joint-observation kernels in https://arxiv.org/abs/2509.25276 to the actual
arcsine, Gamma, and completed free-Fock moment constructions. The complete
complex polynomial frame is invertible everywhere. Its normalized transported
flux plus the initial boundary correction equals twice source height times the
weighted energy of every internal wave. Two observed levels detect every
nonzero internal vector, with no supplied mathematical hypotheses.
-/

open scoped Matrix BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- The actual first- and second-kind polynomial frame at a complex spectral point. -/
def gomesMomentComplexFrame (M : GomesMomentModel) (n : ℕ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![monicOrthoC M.moments (n+1) z,secondKindC M.moments (n+1) z;
    monicOrthoC M.moments n z,secondKindC M.moments n z]

/-- An arbitrary internal vector selects a linear combination of the two actual polynomial solutions. -/
def gomesMomentWave (M : GomesMomentModel) (v : Fin 2 → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  monicOrthoC M.moments n z*v 0+secondKindC M.moments n z*v 1

/-- Weighted energy observed through a finite range of polynomial levels. -/
def gomesMomentWaveEnergy (M : GomesMomentModel) (v : Fin 2 → ℂ) (n : ℕ) (z : ℂ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), Complex.normSq (gomesMomentWave M v k z) /
    momentInner M.moments (monicOrtho M.moments k) (monicOrtho M.moments k)

/-- Complex evaluation preserves the same actual recurrence-frame advance law. -/
theorem gomesMomentComplexFrame_advance (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    gomesMomentComplexFrame M (n+1) z =
      gomesJacobiComplexStep (recurDiag M.moments n) (recurOff M.moments n) z *
        gomesMomentComplexFrame M n z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesMomentComplexFrame,gomesJacobiComplexStep,Matrix.mul_apply,Fin.sum_univ_two,
      monicOrthoC_succ_succ (gomesMomentModel_positive M),secondKindC_succ_succ] <;> ring

/-- The complex frame determinant remains the explicit nonzero negative norm ratio. -/
theorem gomesMomentComplexFrame_det (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    (gomesMomentComplexFrame M n z).det =
      -((momentInner M.moments (monicOrtho M.moments n) (monicOrtho M.moments n) /
        momentInner M.moments (monicOrtho M.moments 0) (monicOrtho M.moments 0) : ℝ) : ℂ) := by
  simpa [gomesMomentComplexFrame,Matrix.det_fin_two,mul_comm] using
    monicOrthoC_wronskian (gomesMomentModel_positive M) n z

/-- All concrete complex recurrence frames are invertible at every spectral point. -/
theorem gomesMomentComplexFrame_isUnit (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    IsUnit (gomesMomentComplexFrame M n z) := by
  rw [Matrix.isUnit_iff_isUnit_det,gomesMomentComplexFrame_det,isUnit_iff_ne_zero]
  have h := (div_pos (gomesMomentModel_norm_pos M n) (gomesMomentModel_norm_pos M 0)).ne'
  simpa using Complex.ofReal_ne_zero.mpr h

/-- The top frame component is exactly the next observed wave amplitude. -/
theorem gomesMomentComplexFrame_top (M : GomesMomentModel) (v : Fin 2 → ℂ) (n : ℕ) (z : ℂ) :
    (gomesMomentComplexFrame M n z *ᵥ v) 0 = gomesMomentWave M v (n+1) z := by
  simp [gomesMomentComplexFrame,gomesMomentWave,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail]

/-- The zeroth observed wave is the first internal component. -/
theorem gomesMomentWave_zero (M : GomesMomentModel) (v : Fin 2 → ℂ) (z : ℂ) :
    gomesMomentWave M v 0 z = v 0 := by
  simp [gomesMomentWave,monicOrthoC]

/-- Weighted finite wave energy is always nonnegative. -/
theorem gomesMomentWaveEnergy_nonneg (M : GomesMomentModel) (v : Fin 2 → ℂ) (n : ℕ) (z : ℂ) :
    0 ≤ gomesMomentWaveEnergy M v n z := by
  apply Finset.sum_nonneg
  intro k hk
  exact div_nonneg (Complex.normSq_nonneg _) (gomesMomentModel_norm_pos M k).le

/-- Two or more observed levels detect every nonzero internal vector, exactly. -/
theorem gomesMomentWaveEnergy_succ_pos_iff (M : GomesMomentModel) (v : Fin 2 → ℂ) (n : ℕ) (z : ℂ) :
    0 < gomesMomentWaveEnergy M v (n+1) z ↔ v ≠ 0 := by
  constructor
  · intro h he
    simp [gomesMomentWaveEnergy,gomesMomentWave,he] at h
  · intro hv
    apply Finset.sum_pos'
    · intro k hk
      exact div_nonneg (Complex.normSq_nonneg _) (gomesMomentModel_norm_pos M k).le
    · by_cases h0 : v 0 = 0
      · have h1 : v 1 ≠ 0 := by
          intro he
          apply hv
          ext i
          fin_cases i <;> simp [h0,he]
        refine ⟨1,by simp,?_⟩
        simpa [gomesMomentWave,h0] using
          div_pos (Complex.normSq_pos.mpr h1) (gomesMomentModel_norm_pos M 1)
      · refine ⟨0,by simp,?_⟩
        rw [gomesMomentWave_zero]
        exact div_pos (Complex.normSq_pos.mpr h0) (gomesMomentModel_norm_pos M 0)

/-- The initial frame has an exact boundary correction opposite to the incoming flux. -/
theorem gomesMomentComplexFrame_zero_flux (M : GomesMomentModel) (v : Fin 2 → ℂ) (z : ℂ) :
    gomesInternalFlux (gomesMomentComplexFrame M 0 z *ᵥ v) =
      2*z.im*Complex.normSq (v 0)-gomesInternalFlux v := by
  have hq : (monicOrthoC M.moments 1 z).im = z.im := by
    have h := gomesMomentQuotient_im M 0 z
    simpa [gomesMomentQuotient,gomesMomentQuotientWeight_zero,monicOrthoC] using h
  have hvec : gomesMomentComplexFrame M 0 z *ᵥ v =
      ![monicOrthoC M.moments 1 z*v 0+v 1,v 0] := by
    ext i
    fin_cases i <;> simp [gomesMomentComplexFrame,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,monicOrthoC]
  rw [hvec,gomesInternalFlux_pairing,gomesInternalFlux_pairing]
  simp [Complex.mul_im,Complex.mul_re,hq,Complex.normSq_apply]
  ring

/-- Exact finite internal-frame balance: transported flux plus boundary flux is weighted wave energy. -/
theorem gomesMomentComplexFrame_flux_energy (M : GomesMomentModel) (v : Fin 2 → ℂ) (n : ℕ) (z : ℂ) :
    gomesInternalFlux (gomesMomentComplexFrame M n z *ᵥ v) /
        momentInner M.moments (monicOrtho M.moments n) (monicOrtho M.moments n) +
      gomesInternalFlux v /
        momentInner M.moments (monicOrtho M.moments 0) (monicOrtho M.moments 0) =
      2*z.im*gomesMomentWaveEnergy M v n z := by
  induction n with
  | zero =>
      rw [gomesMomentComplexFrame_zero_flux]
      simp [gomesMomentWaveEnergy,gomesMomentWave_zero]
      ring
  | succ n ih =>
      have hn := (gomesMomentModel_norm_pos M n).ne'
      have hn1 := (gomesMomentModel_norm_pos M (n+1)).ne'
      have he : gomesInternalFlux (gomesMomentComplexFrame M (n+1) z *ᵥ v) =
          recurOff M.moments n*gomesInternalFlux (gomesMomentComplexFrame M n z *ᵥ v) +
            2*z.im*Complex.normSq (gomesMomentWave M v (n+1) z) := by
        rw [gomesMomentComplexFrame_advance,← Matrix.mulVec_mulVec,
          gomesInternalFlux_jacobi_balance,gomesMomentComplexFrame_top]
      rw [he]
      have hs : gomesMomentWaveEnergy M v (n+1) z = gomesMomentWaveEnergy M v n z +
          Complex.normSq (gomesMomentWave M v (n+1) z) /
            momentInner M.moments (monicOrtho M.moments (n+1)) (monicOrtho M.moments (n+1)) := by
        exact Finset.sum_range_succ _ _
      rw [hs]
      calc
        _ = gomesInternalFlux (gomesMomentComplexFrame M n z *ᵥ v) /
            momentInner M.moments (monicOrtho M.moments n) (monicOrtho M.moments n) +
          gomesInternalFlux v /
            momentInner M.moments (monicOrtho M.moments 0) (monicOrtho M.moments 0) +
          2*z.im*Complex.normSq (gomesMomentWave M v (n+1) z) /
            momentInner M.moments (monicOrtho M.moments (n+1)) (monicOrtho M.moments (n+1)) := by
              rw [recurOff]
              field_simp [hn,hn1]
              ring
        _ = _ := by rw [ih]; ring

end GaloisForLFunctions.HTGeometry
