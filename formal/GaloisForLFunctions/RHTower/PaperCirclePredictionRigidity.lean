import GaloisForLFunctions.RHTower.PaperCirclePosteriorPrediction

/-! # Perfect native character prediction is exactly the zero frequency

Every native cell contains consecutive grid points. Strictly positive observation
kernels retain both points after every observation, so a perfectly predictable
character must be trivial. The full zero-risk classification also identifies the
tester, while the preceding module gives the exact positive residual error.
-/

open scoped BigOperators NNReal Classical ComplexConjugate
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem paperCircleObservationCell_successor_mem (l r : ℕ) (i : Fin (2^l)) :
    (paperCircleObservationCell l i).start (l+r+10) + 1 ∈
      (paperCircleObservationCell l i).block (l+r+10) := by
  let p := paperCircleObservationCell l i
  have hp := paperCircleObservationCell_ok l r i
  have hw : 1 < p.wid (l+r+10) := by
    change 1 < 2^(l+r+10-l)
    have h := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2)
      (by omega : 1 ≤ l+r+10-l)
    simpa only [pow_one] using lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) h
  have hf := p.fitting hp.1 hp.2
  have hb : p.idx (l+r+10)+1 < 2^(l+r+10) := by omega
  have he : p.start (l+r+10)+1 = ((p.idx (l+r+10)+1 : ℕ) : Grid (l+r+10)) := by
    simp only [Node.start, Nat.cast_add, Nat.cast_one]
  change p.start (l+r+10)+1 ∈ p.block (l+r+10)
  rw [Node.mem_block_iff hp.2, he, ZMod.val_natCast_of_lt hb]
  change p.idx (l+r+10) ≤ p.idx (l+r+10)+1 ∧
    p.idx (l+r+10)+1 < (p.ix+1)*2^(l+r+10-p.lev)
  have hid : (p.ix+1)*2^(l+r+10-p.lev) = p.idx (l+r+10)+p.wid (l+r+10) := by
    unfold Node.idx Node.wid
    ring
  rw [hid]
  omega

theorem paperCircleNextCharacterMean_zero (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (z : Grid (l+r+10)) :
    paperCircleNextCharacterMean a l r k i s t 0 z = 1 := by
  simp only [paperCircleNextCharacterMean, Law.Cx, chi_zero_left, mul_one,
    ← Complex.ofReal_sum, Law.total, Complex.ofReal_one]

theorem paperCircleCaptureEnergy_zero (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    paperCircleCaptureEnergy a l r k i s t 0 = 1 := by
  rw [paperCircleCaptureEnergy_mean_square]
  simp only [paperCircleNextCharacterMean_zero, norm_one, one_pow, Law.Ex_const]

private theorem zero_risk_point (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) (c : Grid (l+r+10) → ℂ)
    (h : paperCircleCharacterRisk a l r k i s t u c = 0)
    (x z : Grid (l+r+10)) (hx : x ∈ (paperCircleObservationCell l i).block (l+r+10)) :
    chi u x = conj (c z) := by
  let P := (paperCircleHistoryCellPosterior a l r k i s).withNext
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))
  have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ =>
    mul_nonneg (P.nonneg v) (sq_nonneg ‖chi u v.1 - conj (c v.2)‖))).mp h
  have hp : 0 < P (x,z) := mul_pos
    ((paperCircleHistoryCellPosterior_pos_iff a l r k i s x).mpr hx) (Thermal.ch_pos _ x z)
  have hsq := (mul_eq_zero.mp (ht (x,z) (Finset.mem_univ _))).resolve_left hp.ne'
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))

/-- Sharp saturation boundary, valid for every native family, history, cell and observation scale. -/
theorem paperCircleCaptureEnergy_eq_one_iff (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) :
    paperCircleCaptureEnergy a l r k i s t u = 1 ↔ u = 0 := by
  constructor
  · intro he
    let c := fun z => conj (paperCircleNextCharacterMean a l r k i s t u z)
    have hr : paperCircleCharacterRisk a l r k i s t u c = 0 := by
      rw [paperCircleCharacterRisk_score, (paperCircleCharacterScore_optimizer a l r k i s t u).2,
        he, sub_self]
    let x := (paperCircleObservationCell l i).start (l+r+10)
    have hx := Node.start_mem (paperCircleObservationCell_ok l r i).1
      (paperCircleObservationCell_ok l r i).2
    have h0 := zero_risk_point a l r k i s t u c hr x 0 hx
    have h1 := zero_risk_point a l r k i s t u c hr (x+1) 0
      (paperCircleObservationCell_successor_mem l r i)
    have heq : u*(x+1) = u*x := ZMod.injective_stdAddChar (h1.trans h0.symm)
    have hz : u*(x+1)-u*x = 0 := sub_eq_zero.mpr heq
    simpa only [mul_add, mul_one, add_sub_cancel_left] using hz
  · rintro rfl
    exact paperCircleCaptureEnergy_zero a l r k i s t

theorem paperCircleCaptureEnergy_lt_one_iff (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) :
    paperCircleCaptureEnergy a l r k i s t u < 1 ↔ u ≠ 0 := by
  constructor
  · intro h he
    subst u
    rw [paperCircleCaptureEnergy_zero] at h
    exact lt_irrefl _ h
  · intro h
    rcases lt_or_eq_of_le (paperCircleCaptureEnergy_range a l r k i s t u).2 with he | he
    · exact he
    · exact (h ((paperCircleCaptureEnergy_eq_one_iff a l r k i s t u).mp he)).elim

/-- Perfect prediction occurs precisely for the trivial character and the constant unit tester. -/
theorem paperCircleCharacterRisk_eq_zero_iff (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (u : Grid (l+r+10)) (c : Grid (l+r+10) → ℂ) :
    paperCircleCharacterRisk a l r k i s t u c = 0 ↔ u = 0 ∧ ∀ z, c z = 1 := by
  constructor
  · intro hr
    have hs : paperCircleCharacterScore a l r k i s t u c = 1 := by
      rw [paperCircleCharacterRisk_score] at hr
      linarith
    have he : paperCircleCaptureEnergy a l r k i s t u = 1 := by
      have hl := paperCircleCharacterScore_le a l r k i s t u c
      have hu := (paperCircleCaptureEnergy_range a l r k i s t u).2
      linarith
    have hu := (paperCircleCaptureEnergy_eq_one_iff a l r k i s t u).mp he
    refine ⟨hu, ?_⟩
    have hc := (paperCircleCharacterScore_eq_iff a l r k i s t u c).mp (hs.trans he.symm)
    intro z
    simpa only [hu, paperCircleNextCharacterMean_zero, map_one] using hc z
  · rintro ⟨rfl, hc⟩
    rw [paperCircleCharacterRisk_score,
      (paperCircleCharacterScore_eq_iff a l r k i s t 0 c).mpr
        (fun z => by simp only [hc, paperCircleNextCharacterMean_zero, map_one]),
      paperCircleCaptureEnergy_zero, sub_self]

end
end RHTower
