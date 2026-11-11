import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheApertureIndexCountsNoExtraZeros
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFiniteStratumIsThePacketIndexDichotomy

/-!
# Smooth real packets capture the aperture index

Splitting a finite smooth complex family into real and imaginary parts
preserves its support interval and cannot decrease its negative index.
Applied to the dense form core, this captures the complete aperture index
by finitely many real packets supported strictly inside the same aperture.
-/

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open _root_.RHTower _root_.RHTower.PaperRestrictedWeil HTGeometry
open ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry
open AbsoluteGeometryOfSpecZ SquareRootThreshold Zeta23 Matrix Complex

/-- Realification retains smoothness and the original closed support. -/
theorem exists_real_smooth_packets_negIndex_ge {n : ℕ} (f : Fin n → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) {U : Set ℝ}
    (hs : ∀ i, tsupport (f i) ⊆ U) :
    ∃ (m : ℕ) (g : Fin m → ℝ → ℝ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i)) ∧
      (∀ i, HasCompactSupport (g i)) ∧ (∀ i, tsupport (g i) ⊆ U) ∧
      hermNegIndex (zeroGram zetaZeroConfig f) ≤
        hermNegIndex (zeroGram zetaZeroConfig (fun i u => (g i u : ℂ))) := by
  classical
  let g : Fin n × Fin 2 → ℝ → ℝ := fun j u =>
    if j.2 = 0 then (f j.1 u).re else (f j.1 u).im
  have hg : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j) := by
    intro j
    dsimp only [g]
    split_ifs
    · exact Complex.reCLM.contDiff.comp (hf j.1)
    · exact Complex.imCLM.contDiff.comp (hf j.1)
  have hgc : ∀ j, HasCompactSupport (g j) := by
    intro j
    dsimp only [g]
    split_ifs
    · exact (hfc j.1).comp_left rfl
    · exact (hfc j.1).comp_left rfl
  have hgs : ∀ j, tsupport (g j) ⊆ U := by
    intro j
    apply Set.Subset.trans (closure_mono ?_) (hs j.1)
    intro x hx hfx
    apply hx
    dsimp only [g]
    rw [hfx]
    split_ifs <;> rfl
  let t : Fin n × Fin 2 → testSpace := fun j =>
    ⟨fun u => (g j u : ℂ),
      contDiff_ofReal_packet ((hg j).of_le (WithTop.coe_le_coe.mpr le_top)),
      hasCompactSupport_ofReal_packet (hgc j)⟩
  let C : Matrix (Fin n) (Fin n × Fin 2) ℂ := fun i j =>
    if j.1 = i then if j.2 = 0 then 1 else Complex.I else 0
  have hcomb : (fun i => ((∑ j, C i j • t j : testSpace) : ℝ → ℂ)) = f := by
    funext i u
    simp [C, t, g, Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [mul_comm Complex.I, Complex.re_add_im]
  have hmat := zeroGram_comb zetaZeroConfig temperedConfig_zetaZeroConfig t C
  rw [hcomb] at hmat
  have hle : hermNegIndex (zeroGram zetaZeroConfig f) ≤
      hermNegIndex (zeroGram zetaZeroConfig (fun j u => (g j u : ℂ))) := by
    rw [hmat]
    exact hermNegIndex_mul_mul_conjTranspose_le C _
  let e := (Fintype.equivFin (Fin n × Fin 2)).symm
  refine ⟨Fintype.card (Fin n × Fin 2), fun i => g (e i),
    fun i => hg (e i), fun i => hgc (e i), fun i => hgs (e i), ?_⟩
  change hermNegIndex (zeroGram zetaZeroConfig f) ≤
    hermNegIndex ((zeroGram zetaZeroConfig (fun j u => (g j u : ℂ))).submatrix e e)
  rw [hermNegIndex_submatrix_equiv]
  exact hle

/-- A finite real smooth family inside the original aperture captures
every negative direction of its completed Weil form. -/
theorem exists_real_smooth_packets_capture_negativeRank (a : SuzukiPositiveAperture) :
    ∃ (m : ℕ) (g : Fin m → ℝ → ℝ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i)) ∧
      (∀ i, HasCompactSupport (g i)) ∧
      (∀ i, tsupport (g i) ⊆ Set.Ioo (-a.1) a.1) ∧
      negativeRank a 0 ≤
        hermNegIndex (zeroGram zetaZeroConfig (fun i u => (g i u : ℂ))) := by
  obtain ⟨f, hf⟩ := exists_smoothShiftedWeilGram_index_eq a 0
  rw [smoothShiftedWeilGram_zero_eq_transpose_zeroGram,
    hermNegIndex_transpose_eq (zeroGram_isHermitian _ _)] at hf
  obtain ⟨m, g, hg, hgc, hgs, hle⟩ := exists_real_smooth_packets_negIndex_ge
    (fun i => (f i : ℝ → ℂ)) (fun i => (f i).smooth)
    (fun i => (f i).hasCompactSupport) (fun i => (f i).tsupport_subset)
  exact ⟨m, g, hg, hgc, hgs, hf ▸ hle⟩

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
