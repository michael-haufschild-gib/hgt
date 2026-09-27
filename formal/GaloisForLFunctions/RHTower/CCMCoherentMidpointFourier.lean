import GaloisForLFunctions.RHTower.CCMCoherentMidpointEnergy

/-!
# The exact sine symbol of the midpoint-odd arithmetic field

Midpoint reflection turns each pair of translates into a sine multiplier.
The formula retains the signed prime sum and the oriented terminal cell;
no absolute values or diagonal approximation are introduced.
-/

noncomputable section
open Complex MeasureTheory
open scoped BigOperators

namespace RHTower

private theorem fourier_logTranslation_ae (h : ℝ) (f : SoninL2) :
    (fourierUnitary (logTranslationCLM h f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => MellinL2.fourierPhase h ξ * fourierUnitary f ξ := by
  have he : fourierUnitary (logTranslationCLM h f) =
      MellinL2.fourierPhaseMulUnitary h (fourierUnitary f) :=
    MellinL2.fourier_additiveTranslation h f
  rw [he]
  exact MellinL2.fourierPhaseMulAux_ae h (fourierUnitary f)

private theorem fourier_packet_ae {ι : Type*} (I : Finset ι)
    (c : ι → ℂ) (s : ι → ℝ) (f : SoninL2) :
    (fourierUnitary (∑ i ∈ I, c i • logTranslationCLM (s i) f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (∑ i ∈ I, c i * MellinL2.fourierPhase (s i) ξ) * fourierUnitary f ξ := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, map_zero, zero_mul]
    filter_upwards [Lp.coeFn_zero ℂ 2 volume] with ξ hξ
    exact hξ
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi, map_add, map_smul]
    filter_upwards [Lp.coeFn_add
      (c i • fourierUnitary (logTranslationCLM (s i) f))
      (fourierUnitary (∑ j ∈ I, c j • logTranslationCLM (s j) f)),
      Lp.coeFn_smul (c i) (fourierUnitary (logTranslationCLM (s i) f)),
      fourier_logTranslation_ae (s i) f, ih] with ξ ha hc ht hp
    rw [ha, Pi.add_apply, hc, Pi.smul_apply, smul_eq_mul, ht, hp]
    ring

private theorem phase_add (a b ξ : ℝ) :
    MellinL2.fourierPhase (a+b) ξ =
      MellinL2.fourierPhase a ξ * MellinL2.fourierPhase b ξ := by
  simp only [MellinL2.fourierPhase, Real.fourierChar_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A reflected translation pair has a common midpoint phase and a real sine amplitude. -/
theorem fourierPhase_midpoint_half_sub (r s ξ : ℝ) :
    ((1/2 : ℝ) : ℂ) *
      (MellinL2.fourierPhase (-s) ξ - MellinL2.fourierPhase (r+s) ξ) =
      -Complex.I * MellinL2.fourierPhase (r/2) ξ *
        (Real.sin (2*Real.pi*(s+r/2)*ξ) : ℂ) := by
  have h₁ : -s = r/2 + -(s+r/2) := by ring
  have h₂ : r+s = r/2 + (s+r/2) := by ring
  rw [h₁, h₂, phase_add, phase_add, ← mul_sub]
  have he : MellinL2.fourierPhase (-(s+r/2)) ξ -
      MellinL2.fourierPhase (s+r/2) ξ =
        -2 * (Real.sin (2*Real.pi*(s+r/2)*ξ) : ℂ) * Complex.I := by
    simp only [MellinL2.fourierPhase, Real.fourierChar_apply]
    have ha : 2*Real.pi*(-(s+r/2)*ξ) = -(2*Real.pi*(s+r/2)*ξ) := by ring
    have hb : 2*Real.pi*((s+r/2)*ξ) = 2*Real.pi*(s+r/2)*ξ := by ring
    rw [ha, hb, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [he]
  push_cast
  ring

/-- Fourier representation for an arbitrary finite real packet and its midpoint reflection. -/
theorem fourier_midpointOdd_translation_packet_ae {ι : Type*} (I : Finset ι)
    (c s : ι → ℝ) (r : ℝ) (f : SoninL2) :
    (fourierUnitary (((1/2 : ℝ) : ℂ) •
      ((∑ i ∈ I, (c i : ℂ) • logTranslationCLM (-s i) f) -
       (∑ i ∈ I, (c i : ℂ) • logTranslationCLM (r+s i) f))) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (-Complex.I * MellinL2.fourierPhase (r/2) ξ *
        ((∑ i ∈ I, c i * Real.sin (2*Real.pi*(s i+r/2)*ξ) : ℝ) : ℂ)) *
          fourierUnitary f ξ := by
  rw [map_smul, map_sub]
  filter_upwards [Lp.coeFn_smul ((1/2 : ℝ) : ℂ)
    (fourierUnitary (∑ i ∈ I, (c i : ℂ) • logTranslationCLM (-s i) f) -
     fourierUnitary (∑ i ∈ I, (c i : ℂ) • logTranslationCLM (r+s i) f)),
    Lp.coeFn_sub
      (fourierUnitary (∑ i ∈ I, (c i : ℂ) • logTranslationCLM (-s i) f))
      (fourierUnitary (∑ i ∈ I, (c i : ℂ) • logTranslationCLM (r+s i) f)),
    fourier_packet_ae I (fun i => (c i : ℂ)) (fun i => -s i) f,
    fourier_packet_ae I (fun i => (c i : ℂ)) (fun i => r+s i) f] with ξ hc hs h₁ h₂
  rw [hc, Pi.smul_apply, smul_eq_mul, hs, Pi.sub_apply, h₁, h₂]
  rw [← sub_mul, ← mul_assoc, ← Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have h := fourierPhase_midpoint_half_sub r (s i) ξ
  calc
    _ = (c i : ℂ) * (((1/2 : ℝ) : ℂ) *
        (MellinL2.fourierPhase (-s i) ξ - MellinL2.fourierPhase (r+s i) ξ)) := by ring
    _ = _ := by rw [h]; ring

/-- The full signed sine amplitude, including the terminal correction. -/
def ccmActualHeadMidpointSineSymbol (T : ℝ) (N : ℕ) (r ξ : ℝ) : ℝ :=
  (∑ n ∈ Finset.range N, ccmOutgoingQuantileDisplacementCellDensity n r *
    Real.sin (2*Real.pi*(Real.log n+r/2)*ξ)) +
  ccmActualHeadQuantileTerminalDisplacementDensity T N r *
    Real.sin (2*Real.pi*(T+r/2)*ξ)

/-- Exact Plancherel-side expression for the actual midpoint-odd field. -/
theorem fourier_ccmActualHeadMidpointOddField_ae (T : ℝ) (N : ℕ)
    (f : SoninL2) (r : ℝ) :
    (fourierUnitary (ccmActualHeadMidpointOddField T N f r) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (-Complex.I * MellinL2.fourierPhase (r/2) ξ *
        (ccmActualHeadMidpointSineSymbol T N r ξ : ℂ)) * fourierUnitary f ξ := by
  have h := fourier_midpointOdd_translation_packet_ae (Finset.range N).insertNone
    (fun o : Option ℕ => o.elim (ccmActualHeadQuantileTerminalDisplacementDensity T N r)
      (fun n => ccmOutgoingQuantileDisplacementCellDensity n r))
    (fun o : Option ℕ => o.elim T (fun n => Real.log n)) r f
  simpa only [Finset.sum_insertNone, Option.elim, add_comm,
    ccmActualHeadMidpointOddField, ccmActualHeadReflectedCoherentField,
    ccmActualHeadQuantileCompletedCoherentField, ccmActualHeadQuantileBulkCoherentField,
    ccmActualHeadQuantileCellCoherentField, ccmActualHeadQuantileTerminalCoherentField,
    ccmActualHeadMidpointSineSymbol] using h

theorem ccmActualHeadMidpointSineSymbol_zero (T : ℝ) (N : ℕ) (r : ℝ) :
    ccmActualHeadMidpointSineSymbol T N r 0 = 0 := by
  simp [ccmActualHeadMidpointSineSymbol]

theorem ccmActualHeadMidpointSineSymbol_neg (T : ℝ) (N : ℕ) (r ξ : ℝ) :
    ccmActualHeadMidpointSineSymbol T N r (-ξ) =
      -ccmActualHeadMidpointSineSymbol T N r ξ := by
  simp only [ccmActualHeadMidpointSineSymbol, mul_neg, Real.sin_neg,
    Finset.sum_neg_distrib, neg_add_rev]
  ring

end RHTower
