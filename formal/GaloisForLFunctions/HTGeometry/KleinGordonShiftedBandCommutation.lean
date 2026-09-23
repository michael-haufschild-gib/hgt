import GaloisForLFunctions.HTGeometry.KleinGordonShiftedInverseSquare

/-!
# The shifted operators against the band projection

All the operators of the shifted calculus are Fourier multipliers, so they commute with the low-pass
projection. Together with the collapse of the generator against `⟨D⟩⁻²` this gives the operator form
of the right-hand side of the strong equation:

`⟨D⟩⁻²(Ω²χ (Pz)) = Pz − ⟨D⟩⁻²(p (Pz))`.

Both sides are multipliers of the same symbol, and the symbol identity is the collapse proved for the
symbols.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Commutation

variable {v : E → ℝ} {b : ℝ}

theorem kgShiftedCosOp_kgLowPassOp_comm (hv : Measurable v) (t R : ℝ)
    (x : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedCosOp hv t (kgLowPassOp R x) = kgLowPassOp R (kgShiftedCosOp hv t x) :=
  fourierMulCLM_comm (measurable_kgShiftedCos hv t) (measurable_kgLowPass R) zero_le_one
    (norm_kgShiftedCos_le v t) zero_le_one (norm_kgLowPass_le R) x

theorem kgShiftedSinFreqOp_kgLowPassOp_comm (hv : Measurable v) (t R : ℝ)
    (x : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedSinFreqOp hv t (kgLowPassOp R x) = kgLowPassOp R (kgShiftedSinFreqOp hv t x) :=
  fourierMulCLM_comm (measurable_kgShiftedSinOverFreq hv t) (measurable_kgLowPass R)
    (abs_nonneg t) (norm_kgShiftedSinOverFreq_le v t) zero_le_one (norm_kgLowPass_le R) x

theorem kgShiftedFreqSqLowOp_kgLowPassOp_comm (hv : Measurable v) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hvb : ∀ ξ : E, |v ξ| ≤ b) (R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedFreqSqLowOp hv hb0 hb1 hvb R (kgLowPassOp R x)
      = kgLowPassOp R (kgShiftedFreqSqLowOp hv hb0 hb1 hvb R x) :=
  fourierMulCLM_comm (measurable_kgShiftedFreqSqLow hv R) (measurable_kgLowPass R)
    (band_bound_nonneg hb0 R) (norm_kgShiftedFreqSqLow_le hb0 hb1 hvb R) zero_le_one
    (norm_kgLowPass_le R) x

end Commutation

section InverseSquareOperator

variable {p : E → ℝ} {b : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The generator against `⟨D⟩⁻²`, in operator form**: on band-limited data it is the right-hand
side of the strong Klein–Gordon equation. -/
theorem kgFreqInvOp_sq_kgShiftedFreqSqLowOp (hp : Measurable p) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hpb : ∀ ξ : E, |p ξ| ≤ b) (R : ℝ) (z : Lp ℂ 2 (volume : Measure E)) :
    kgFreqInvOp (kgFreqInvOp (kgShiftedFreqSqLowOp hp.neg hb0 hb1 (abs_neg_pot_le hpb) R
        (kgLowPassOp R z)))
      = kgLowPassOp R z
        - kgFreqInvOp (kgFreqInvOp (fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
            (norm_kgRealPotSymbol_le hpb) (kgLowPassOp R z))) := by
  have hband := band_bound_nonneg (b := b) hb0 R
  -- symbols of the left-hand chain
  have hs1 : Measurable fun ξ : E =>
      kgShiftedFreqSqLow (fun ζ : E => -(p ζ)) R ξ * kgLowPass R ξ :=
    (measurable_kgShiftedFreqSqLow hp.neg R).mul (measurable_kgLowPass R)
  have hs1b : ∀ ξ : E, ‖kgShiftedFreqSqLow (fun ζ : E => -(p ζ)) R ξ * kgLowPass R ξ‖
      ≤ 1 + R ^ (2 : ℕ) + b := by
    intro ξ
    rw [norm_mul]
    calc ‖kgShiftedFreqSqLow (fun ζ : E => -(p ζ)) R ξ‖ * ‖kgLowPass R ξ‖
        ≤ (1 + R ^ (2 : ℕ) + b) * 1 :=
          mul_le_mul (norm_kgShiftedFreqSqLow_le hb0 hb1 (abs_neg_pot_le hpb) R ξ)
            (norm_kgLowPass_le R ξ) (norm_nonneg _) hband
      _ = 1 + R ^ (2 : ℕ) + b := mul_one _
  have hs2 : Measurable fun ξ : E => kgFreqInv ξ
      * (kgShiftedFreqSqLow (fun ζ : E => -(p ζ)) R ξ * kgLowPass R ξ) :=
    (measurable_kgFreqInv (E := E)).mul hs1
  have hs2b : ∀ ξ : E, ‖kgFreqInv ξ
      * (kgShiftedFreqSqLow (fun ζ : E => -(p ζ)) R ξ * kgLowPass R ξ)‖ ≤ 1 + R ^ (2 : ℕ) + b := by
    intro ξ
    rw [norm_mul]
    calc ‖kgFreqInv ξ‖ * ‖kgShiftedFreqSqLow (fun ζ : E => -(p ζ)) R ξ * kgLowPass R ξ‖
        ≤ 1 * (1 + R ^ (2 : ℕ) + b) :=
          mul_le_mul (norm_kgFreqInv_le ξ) (hs1b ξ) (norm_nonneg _) zero_le_one
      _ = 1 + R ^ (2 : ℕ) + b := one_mul _
  have hs3 : Measurable fun ξ : E => kgFreqInv ξ * (kgFreqInv ξ
      * (kgShiftedFreqSqLow (fun ζ : E => -(p ζ)) R ξ * kgLowPass R ξ)) :=
    (measurable_kgFreqInv (E := E)).mul hs2
  have hs3b : ∀ ξ : E, ‖kgFreqInv ξ * (kgFreqInv ξ
      * (kgShiftedFreqSqLow (fun ζ : E => -(p ζ)) R ξ * kgLowPass R ξ))‖ ≤ 1 + R ^ (2 : ℕ) + b := by
    intro ξ
    rw [norm_mul]
    calc ‖kgFreqInv ξ‖ * ‖kgFreqInv ξ
          * (kgShiftedFreqSqLow (fun ζ : E => -(p ζ)) R ξ * kgLowPass R ξ)‖
        ≤ 1 * (1 + R ^ (2 : ℕ) + b) :=
          mul_le_mul (norm_kgFreqInv_le ξ) (hs2b ξ) (norm_nonneg _) zero_le_one
      _ = 1 + R ^ (2 : ℕ) + b := one_mul _
  -- symbols of the right-hand chain
  have hq1 : Measurable fun ξ : E => kgRealPotSymbol p ξ * kgLowPass R ξ :=
    (measurable_kgRealPotSymbol hp).mul (measurable_kgLowPass R)
  have hq1b : ∀ ξ : E, ‖kgRealPotSymbol p ξ * kgLowPass R ξ‖ ≤ b := by
    intro ξ
    rw [norm_mul]
    calc ‖kgRealPotSymbol p ξ‖ * ‖kgLowPass R ξ‖
        ≤ b * 1 := mul_le_mul (norm_kgRealPotSymbol_le hpb ξ) (norm_kgLowPass_le R ξ)
          (norm_nonneg _) hb0
      _ = b := mul_one _
  have hq2 : Measurable fun ξ : E => kgFreqInv ξ * (kgRealPotSymbol p ξ * kgLowPass R ξ) :=
    (measurable_kgFreqInv (E := E)).mul hq1
  have hq2b : ∀ ξ : E, ‖kgFreqInv ξ * (kgRealPotSymbol p ξ * kgLowPass R ξ)‖ ≤ b := by
    intro ξ
    rw [norm_mul]
    calc ‖kgFreqInv ξ‖ * ‖kgRealPotSymbol p ξ * kgLowPass R ξ‖
        ≤ 1 * b := mul_le_mul (norm_kgFreqInv_le ξ) (hq1b ξ) (norm_nonneg _) zero_le_one
      _ = b := one_mul _
  have hq3 : Measurable fun ξ : E =>
      kgFreqInv ξ * (kgFreqInv ξ * (kgRealPotSymbol p ξ * kgLowPass R ξ)) :=
    (measurable_kgFreqInv (E := E)).mul hq2
  have hq3b : ∀ ξ : E,
      ‖kgFreqInv ξ * (kgFreqInv ξ * (kgRealPotSymbol p ξ * kgLowPass R ξ))‖ ≤ b := by
    intro ξ
    rw [norm_mul]
    calc ‖kgFreqInv ξ‖ * ‖kgFreqInv ξ * (kgRealPotSymbol p ξ * kgLowPass R ξ)‖
        ≤ 1 * b := mul_le_mul (norm_kgFreqInv_le ξ) (hq2b ξ) (norm_nonneg _) zero_le_one
      _ = b := one_mul _
  -- identify the chains
  have e1 : (kgShiftedFreqSqLowOp (E := E) hp.neg hb0 hb1 (abs_neg_pot_le hpb) R).comp
      (kgLowPassOp R) = fourierMulCLM hs1 hband hs1b := by
    rw [kgShiftedFreqSqLowOp, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hs1 _ _ _ _ hband hs1b (Eventually.of_forall fun _ => rfl)
  have e2 : (kgFreqInvOp (E := E)).comp (fourierMulCLM hs1 hband hs1b)
      = fourierMulCLM hs2 hband hs2b := by
    rw [kgFreqInvOp]
    exact fourierMulCLM_comp _ _ hs2 _ _ _ _ hband hs2b (Eventually.of_forall fun _ => rfl)
  have e3 : (kgFreqInvOp (E := E)).comp (fourierMulCLM hs2 hband hs2b)
      = fourierMulCLM hs3 hband hs3b := by
    rw [kgFreqInvOp]
    exact fourierMulCLM_comp _ _ hs3 _ _ _ _ hband hs3b (Eventually.of_forall fun _ => rfl)
  have f1 : (fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
      (norm_kgRealPotSymbol_le hpb)).comp (kgLowPassOp R) = fourierMulCLM hq1 hb0 hq1b := by
    rw [kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hq1 _ _ _ _ hb0 hq1b (Eventually.of_forall fun _ => rfl)
  have f2 : (kgFreqInvOp (E := E)).comp (fourierMulCLM hq1 hb0 hq1b)
      = fourierMulCLM hq2 hb0 hq2b := by
    rw [kgFreqInvOp]
    exact fourierMulCLM_comp _ _ hq2 _ _ _ _ hb0 hq2b (Eventually.of_forall fun _ => rfl)
  have f3 : (kgFreqInvOp (E := E)).comp (fourierMulCLM hq2 hb0 hq2b)
      = fourierMulCLM hq3 hb0 hq3b := by
    rw [kgFreqInvOp]
    exact fourierMulCLM_comp _ _ hq3 _ _ _ _ hb0 hq3b (Eventually.of_forall fun _ => rfl)
  have hsub : fourierMulCLM hs3 hband hs3b
      = kgLowPassOp (E := E) R - fourierMulCLM hq3 hb0 hq3b := by
    rw [kgLowPassOp_eq]
    exact fourierMulCLM_sub _ hq3 hs3 zero_le_one (norm_kgLowPass_le R) hb0 hq3b hband hs3b
      (Eventually.of_forall (kgFreqInvSq_kgShiftedFreqSqLow hb1 hpb R))
  -- assemble
  have hleft1 : kgShiftedFreqSqLowOp (E := E) hp.neg hb0 hb1 (abs_neg_pot_le hpb) R
      (kgLowPassOp R z) = fourierMulCLM hs1 hband hs1b z := by
    rw [← ContinuousLinearMap.comp_apply, e1]
  have hleft2 : kgFreqInvOp (E := E) (fourierMulCLM hs1 hband hs1b z)
      = fourierMulCLM hs2 hband hs2b z := by
    rw [← ContinuousLinearMap.comp_apply, e2]
  have hleft3 : kgFreqInvOp (E := E) (fourierMulCLM hs2 hband hs2b z)
      = fourierMulCLM hs3 hband hs3b z := by
    rw [← ContinuousLinearMap.comp_apply, e3]
  have hright1 : fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
      (norm_kgRealPotSymbol_le hpb) (kgLowPassOp (E := E) R z) = fourierMulCLM hq1 hb0 hq1b z := by
    rw [← ContinuousLinearMap.comp_apply, f1]
  have hright2 : kgFreqInvOp (E := E) (fourierMulCLM hq1 hb0 hq1b z)
      = fourierMulCLM hq2 hb0 hq2b z := by
    rw [← ContinuousLinearMap.comp_apply, f2]
  have hright3 : kgFreqInvOp (E := E) (fourierMulCLM hq2 hb0 hq2b z)
      = fourierMulCLM hq3 hb0 hq3b z := by
    rw [← ContinuousLinearMap.comp_apply, f3]
  rw [hleft1, hleft2, hleft3, hright1, hright2, hright3, hsub, sub_apply]

end InverseSquareOperator

end GaloisForLFunctions.HTGeometry
