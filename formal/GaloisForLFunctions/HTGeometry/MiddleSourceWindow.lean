/-
The exact scale window on which the middle source of a three-source covering is binding.

A pair `(κ, λ)` with positive displacement `d = (λ - κ) - 1/2` has demand `κ + c·d` at length `T^c`,
increasing in `c`, so at target `β` it covers **exactly** the scales

    **c ≤ coverThreshold(κ, λ, β) = (β - κ)/d** .

This is the scale-freeing threshold of the conjugate picture with `κ = μ(σ)`, `d = σ - 1/2`.

For the target `β = 13/84` and the final source's threshold `x₁ = 17/42`, the three low-range pairs
available to the architecture cover

    (1/9, 13/18)      →  **11/28  = 33/84**  ,  short of `17/42 = 34/84` by **1/84** ;
    (1/11, 3/4)       →  **59/147 = 118/294** ,  short of `119/294`      by **1/294** ;
    (16/237, 743/948) →  **579/1435 = 3474/8610** , short of `3485/8610` by **11/8610** .

So the middle source is binding only on the window `(579/1435, 17/42)`, of width `11/8610`.

Its exponent worth is the excess of the best low-range demand at `x₁` over the target:

    (1/9, 13/18)      →  59/378   - 13/84 = **1/756**   ,
    (1/11, 3/4)       →  41/264   - 13/84 = **1/1848**  ,
    (16/237, 743/948) →  6173/39816 - 13/84 = **11/39816** .

Thus, with Huxley's exponent pair retained but the direct Huxley source removed, the architecture
still yields `μ(1/2) ≤ 6173/39816`; the direct middle source is worth exactly `11/39816` in the
exponent, and only on a window of relative width `11/8610`.
-/
import GaloisForLFunctions.HTGeometry.ScaleAbscissaDuality

namespace HTGeometry

/-! ### The covering threshold of a pair -/

/-- A pair's demand is affine in the length with slope its displacement. -/
theorem covDemandOfPair_affine (c κ lam : ℚ) :
    covDemandOfPair c κ lam = κ + c * epDisplacement κ lam := by
  unfold covDemandOfPair covFunctional epDisplacement; ring

/-- The largest length exponent at which a pair still meets the target. -/
def coverThreshold (κ lam β : ℚ) : ℚ := (β - κ) / epDisplacement κ lam

/-- **A pair covers exactly the scales below its threshold.** -/
theorem cover_iff {κ lam β c : ℚ} (hd : 0 < epDisplacement κ lam) :
    c ≤ coverThreshold κ lam β ↔ covDemandOfPair c κ lam ≤ β := by
  rw [covDemandOfPair_affine, coverThreshold, le_div_iff₀ hd]
  constructor <;> intro h <;> linarith

/-- **The threshold grows with the target**, at rate the reciprocal of the displacement. -/
theorem coverThreshold_mono {κ lam β β' : ℚ} (hd : 0 < epDisplacement κ lam) (h : β ≤ β') :
    coverThreshold κ lam β ≤ coverThreshold κ lam β' := by
  unfold coverThreshold
  exact div_le_div_of_nonneg_right (by linarith) hd |>.mp (by linarith) |>.elim
    (fun _ => le_refl _) (fun _ => le_refl _)

/-! ### The three low-range pairs -/

/-- Displacements of the three pairs. -/
theorem lowPair_displacements :
    epDisplacement (1 / 9) (13 / 18) = 1 / 9 ∧
      epDisplacement (1 / 11) (3 / 4) = 7 / 44 ∧
      epDisplacement (16 / 237) (743 / 948) = 205 / 948 := by
  unfold epDisplacement
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **The published low-range pair covers exactly `33/84`.** -/
theorem coverThreshold_published : coverThreshold (1 / 9) (13 / 18) bourgainTheta = 11 / 28 := by
  unfold coverThreshold epDisplacement bourgainTheta; norm_num

/-- **The van der Corput word covers exactly `118/294`.** -/
theorem coverThreshold_vdcWord : coverThreshold (1 / 11) (3 / 4) bourgainTheta = 59 / 147 := by
  unfold coverThreshold epDisplacement bourgainTheta; norm_num

/-- **The `A`-image of Huxley's pair covers exactly `3474/8610`.** -/
theorem coverThreshold_procAHuxley :
    coverThreshold (16 / 237) (743 / 948) bourgainTheta = 579 / 1435 := by
  unfold coverThreshold epDisplacement bourgainTheta; norm_num

/-! ### The uncovered window -/

/-- **The published pair misses the final source's threshold by exactly `1/84`.** -/
theorem window_published : decouplingStart - coverThreshold (1 / 9) (13 / 18) bourgainTheta = 1 / 84 := by
  rw [coverThreshold_published]; unfold decouplingStart; norm_num

/-- **The van der Corput word misses it by exactly `1/294`.** -/
theorem window_vdcWord : decouplingStart - coverThreshold (1 / 11) (3 / 4) bourgainTheta = 1 / 294 := by
  rw [coverThreshold_vdcWord]; unfold decouplingStart; norm_num

/-- **The best available pair misses it by exactly `11/8610`**, and that interval is the whole of the
middle source's responsibility. -/
theorem window_procAHuxley :
    decouplingStart - coverThreshold (16 / 237) (743 / 948) bourgainTheta = 11 / 8610 := by
  rw [coverThreshold_procAHuxley]; unfold decouplingStart; norm_num

/-- **The windows are nested**, the best pair leaving the smallest. -/
theorem windows_nested :
    (11 : ℚ) / 8610 < 1 / 294 ∧ (1 : ℚ) / 294 < 1 / 84 := by
  refine ⟨by norm_num, by norm_num⟩

/-! ### What the middle source is worth -/

/-- The demands of the three pairs at the final source's threshold. -/
theorem demands_at_decouplingStart :
    covDemandOfPair decouplingStart (1 / 9) (13 / 18) = 59 / 378 ∧
      covDemandOfPair decouplingStart (1 / 11) (3 / 4) = 41 / 264 ∧
        covDemandOfPair decouplingStart (16 / 237) (743 / 948) = 6173 / 39816 := by
  unfold covDemandOfPair covFunctional decouplingStart
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **The exponent worth of the direct middle source**, for each choice of low-range pair. -/
theorem middleSource_worth :
    covDemandOfPair decouplingStart (1 / 9) (13 / 18) - bourgainTheta = 1 / 756 ∧
      covDemandOfPair decouplingStart (1 / 11) (3 / 4) - bourgainTheta = 1 / 1848 ∧
        covDemandOfPair decouplingStart (16 / 237) (743 / 948) - bourgainTheta = 11 / 39816 := by
  unfold covDemandOfPair covFunctional decouplingStart bourgainTheta
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **Removing the direct middle source costs exactly `11/39816`.**  The architecture without it still
delivers `6173/39816`, against the record `6162/39816`. -/
theorem without_middle_source :
    covDemandOfPair decouplingStart (16 / 237) (743 / 948) = 6173 / 39816 ∧
      bourgainTheta = 6162 / 39816 ∧
        (6173 : ℚ) / 39816 - 6162 / 39816 = 11 / 39816 := by
  refine ⟨demands_at_decouplingStart.2.2, ?_, by norm_num⟩
  unfold bourgainTheta; norm_num

/-- **Summary.**  At the record target the low-range input covers every scale up to `3474/8610`, the
final source covers from `3485/8610`, and the direct middle source is responsible for the intervening
`11/8610` alone — worth exactly `11/39816` in the exponent. -/
theorem middle_source_window :
    coverThreshold (16 / 237) (743 / 948) bourgainTheta = 579 / 1435 ∧
      decouplingStart - coverThreshold (16 / 237) (743 / 948) bourgainTheta = 11 / 8610 ∧
        covDemandOfPair decouplingStart (16 / 237) (743 / 948) - bourgainTheta = 11 / 39816 :=
  ⟨coverThreshold_procAHuxley, window_procAHuxley, middleSource_worth.2.2⟩

end HTGeometry
