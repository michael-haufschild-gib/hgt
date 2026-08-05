import GaloisForLFunctions.HTGeometry.KleinGordonObservationFate

/-!
# The multipliers live in an annulus set by the estimate

Statement 325 confines the Floquet multipliers to the disc `|k| ≤ e^{b|T|}`, the bound the energy
estimate gives over one period. The evolution is reversible and its inverse obeys the same bound, so
the multipliers cannot approach zero either: the spectrum of an inverse is the inverse of the
spectrum, so `|k|⁻¹ ≤ e^{b|T|}` as well.

**Every Floquet multiplier lies in the annulus `e^{−b|T|} ≤ |k| ≤ e^{b|T|}`.**

The annulus closes onto the unit circle as the potential weakens or the period shortens, which is the
quantitative form of the free case (statement 347): a clock cannot drift faster per period than its
own energy estimate allows, in either direction of time.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Annulus

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

set_option maxHeartbeats 1000000 in
/-- **No Floquet multiplier is smaller than the estimate allows.** -/
theorem exp_neg_le_norm_of_mem_spectrum_kgMonodromy (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) {k : ℂ}
    (hk : k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)) :
    Real.exp (-(b * |T|)) ≤ ‖k‖ := by
  have hab : kgMonodromy W b hb0 hWb hWs T * kgMonodromy W b hb0 hWb hWs (-T) = 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact kgPeriodMap_right_inverse hb0 hWb hWs hper v
  have hba : kgMonodromy W b hb0 hWb hWs (-T) * kgMonodromy W b hb0 hWb hWs T = 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact kgPeriodMap_left_inverse hb0 hWb hWs hper v
  set u : (KGEnergy E →L[ℂ] KGEnergy E)ˣ :=
    ⟨kgMonodromy W b hb0 hWb hWs T, kgMonodromy W b hb0 hWb hWs (-T), hab, hba⟩ with hudef
  have hval : ((u : (KGEnergy E →L[ℂ] KGEnergy E)ˣ) : KGEnergy E →L[ℂ] KGEnergy E)
      = kgMonodromy W b hb0 hWb hWs T := rfl
  have hvalinv : (((u⁻¹ : (KGEnergy E →L[ℂ] KGEnergy E)ˣ)) : KGEnergy E →L[ℂ] KGEnergy E)
      = kgMonodromy W b hb0 hWb hWs (-T) := rfl
  have hu : IsUnit (kgMonodromy W b hb0 hWb hWs T) := ⟨u, rfl⟩
  have hk0 : k ≠ 0 := by
    intro hzero
    rw [hzero] at hk
    exact absurd hu (spectrum.not_isUnit_of_zero_mem (R := ℂ) hk)
  have hmem : k⁻¹ ∈ (spectrum ℂ ((u : (KGEnergy E →L[ℂ] KGEnergy E)ˣ) :
      KGEnergy E →L[ℂ] KGEnergy E))⁻¹ := by
    rw [Set.mem_inv, inv_inv, hval]
    exact hk
  rw [spectrum.map_inv u, hvalinv] at hmem
  have hle := spectrum.norm_le_norm_mul_of_mem hmem
  have hone := norm_one_kgEnergy (E := E)
  have hM := norm_kgMonodromy_neg_le (W := W) (T := T) hb0 hWb hWs
  have hstep : ‖kgMonodromy W b hb0 hWb hWs (-T)‖ * ‖(1 : KGEnergy E →L[ℂ] KGEnergy E)‖
      ≤ Real.exp (b * |T|) * 1 := by
    rw [hone]
    exact mul_le_mul hM le_rfl zero_le_one (Real.exp_pos _).le
  rw [mul_one] at hstep
  have hinv : ‖k‖⁻¹ ≤ Real.exp (b * |T|) := by
    rw [← norm_inv]
    exact hle.trans hstep
  have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr hk0
  have hexp : Real.exp (-(b * |T|)) = (Real.exp (b * |T|))⁻¹ := by
    rw [Real.exp_neg]
  rw [hexp]
  rw [inv_le_comm₀ (Real.exp_pos _) hkpos]
  exact hinv

/-- **Every Floquet multiplier lies in the annulus the energy estimate cuts out.** -/
theorem mem_annulus_of_mem_spectrum_kgMonodromy (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) {k : ℂ}
    (hk : k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)) :
    Real.exp (-(b * |T|)) ≤ ‖k‖ ∧ ‖k‖ ≤ Real.exp (b * |T|) :=
  ⟨exp_neg_le_norm_of_mem_spectrum_kgMonodromy hb0 hWb hWs hper hk,
    norm_le_of_mem_spectrum_kgMonodromy hb0 hWb hWs hk⟩

end Annulus

end GaloisForLFunctions.HTGeometry
