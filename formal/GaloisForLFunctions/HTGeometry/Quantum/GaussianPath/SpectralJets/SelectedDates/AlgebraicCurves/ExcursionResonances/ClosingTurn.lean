import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.ClosingRatio
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.PrescribedCharacters.PhysicalClock
import GaloisForLFunctions.RHTower.GelfondSchneider

/-! # Transcendence of the closing angle in turns at physical error one tenth -/

open Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.ExcursionResonances
noncomputable section

/-- For algebraic physical error an irrational closing turn is
transcendental. Its exponential is algebraic, so Gelfond–Schneider
applied with base minus one excludes every algebraic irrational turn. -/
theorem transcendental_turn_of_algebraic_error {ε : ℝ} (hε : 0<ε) (hs : ε<sqrt 2)
    (he : IsAlgebraic ℚ (ε:ℂ)) (hi : Irrational (SharpOccupation.physicalArc ε)) :
    Transcendental ℚ (SharpOccupation.physicalArc ε) := by
  let x := SharpOccupation.physicalArc ε
  let β : ℂ := -2*(x:ℂ)
  have hz := (closingRatio_algebraic_iff hε hs).mpr he
  have hpow : (-1:ℂ)^β=closingRatio ε := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (-1:ℂ)≠0),Complex.log_neg_one,closingRatio]
    have ha : π*x=2*arcsin (ε/2) := by
      dsimp [x,SharpOccupation.physicalArc]
      field_simp
    have hc := congrArg Complex.ofReal ha
    push_cast at hc
    dsimp only [β]
    congr 1
    push_cast
    linear_combination (-2*Complex.I)*hc
  have hirr : ¬∃ q : ℚ, β=(q:ℂ) := by
    rintro ⟨q,hq⟩
    apply hi
    refine ⟨-q/2,?_⟩
    have hh := congrArg Complex.re hq
    change ((-q/2:ℚ):ℝ)=x
    push_cast
    simp [β,Complex.mul_re] at hh
    linarith only [hh]
  intro hx
  have hxZ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hx
  have hxC : IsAlgebraic ℚ (x:ℂ) := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp
    (GaloisForLFunctions.RHTower.isAlgebraic_ofReal hxZ)
  let S := algebraicClosure ℚ ℂ
  have hβ : β∈S := S.mul_mem (S.neg_mem (ofNat_mem S 2)) (mem_algebraicClosure_iff.mpr hxC)
  have hbase : IsAlgebraic ℤ (-1:ℂ) := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr
    (mem_algebraicClosure_iff.mp (S.neg_mem S.one_mem))
  have ht := GaloisForLFunctions.RHTower.gelfondSchneider_holds (-1) β hbase (by norm_num)
    (by norm_num) ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr (mem_algebraicClosure_iff.mp hβ)) hirr
  exact ht (hpow.symm ▸ hz)

/-- The endpoint phase at error one tenth is algebraic, while its
oriented arc width measured in turns is transcendental. -/
theorem tenth_closing_turn_transcendental : Transcendental ℚ (SharpOccupation.physicalArc (1/10)) := by
  have hs : (1/10:ℝ)<sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  apply transcendental_turn_of_algebraic_error (by norm_num) hs _
    EntrySensitivity.PrescribedCharacters.physicalArc_tenth_irrational
  have h : (((1/10:ℝ):ℂ))=algebraMap ℚ ℂ (1/10) := by norm_num
  rw [h]
  exact isAlgebraic_algebraMap _

#print axioms tenth_closing_turn_transcendental
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.ExcursionResonances
