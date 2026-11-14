import GaloisForLFunctions.WindowTowerOfSpecZ.TheEvenWeilFormHasAFloorAtAperture1881Over5000
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheGroundEnergyOfAnApertureIsAGapOfEveryWindowInsideIt

/-!
# A positive Weil floor on the first overlap window

The even and odd floors combine by orthogonal parity splitting. Complexification
and smooth approximation transfer the same floor to the closed Weil form and to
every step packet of a window of ratio at most `10609/5000`.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Finset Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticCriticalityTheory ArithmeticPositivityTheory SquareRootThreshold
open SpacingScaleHarmonicAnalysis AbsoluteGeometryOfSpecZ
open GreenCalculusOfThePrimeFreeWindow

private theorem first_overlap_floor : WeilFloor (1881 / 5000) (1 / 50000) :=
  WeilFloor.of_even_of_odd
    (fun _ hF hs he => weilQuad_ge_even_at_aperture_1881_over_5000 hF hs he)
    (oddWeilFloor_firstStep.mono (by norm_num))

/-- Every real test in the first overlap window has the floor `1/50000`. -/
theorem fullZeroForm_ge_at_aperture_1881_over_5000 {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (hs : ∀ x, (1881 / 5000 : ℝ) < |x| → F x = 0) :
    (1 / 50000 : ℝ) * (∫ x, F x ^ 2) ≤ fullZeroForm F := by
  rw [fullZeroForm_eq_re_weilFullFunctional hF.continuous hcs]
  exact first_overlap_floor F hF (tsupport_subset_Icc_of_forall_eq_zero hs)

/-- The same floor holds for complex tests, with no parity condition. -/
theorem zetaZeroConfig_re_W_ge_at_aperture_1881_over_5000 {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f)
    (hs : tsupport f ⊆ Icc (-(1881 / 5000 : ℝ)) (1881 / 5000)) :
    (1 / 50000 : ℝ) * (∫ x, ‖f x‖ ^ 2) ≤ (zetaZeroConfig.W f f).re :=
  zetaZeroConfig_re_W_ge_of_window
    (fun _ hF hcs hs => fullZeroForm_ge_at_aperture_1881_over_5000 hF hcs hs) hf hs

/-- The closed Weil form retains the first overlap floor at every smaller aperture. -/
theorem one_div_50000_le_groundEnergy_of_aperture_le_1881_over_5000
    {A : SuzukiPositiveAperture} (hA : A.1 ≤ (1881 / 5000 : ℝ)) :
    (1 / 50000 : ℝ) ≤ ccmRestrictedWeilGroundEnergy A := by
  apply WeilFloor.le_groundEnergy
  intro F hF hs
  exact first_overlap_floor F hF (hs.trans fun x hx =>
    ⟨by linarith only [hx.1, hA], by linarith only [hx.2, hA]⟩)

/-- Step packets of every window of ratio at most `10609/5000` have the same positive floor. -/
theorem packetForm_stepPacket_ge_of_first_overlap {R J Q : ℕ}
    (hR : 1 ≤ R) (hJ : 5000 * (R + J) ≤ 10609 * R) (hQ : 2 ≤ Q) (σ : ℕ → ℝ) :
    (1 / 50000 : ℝ) * ∑ j ∈ range J, σ j ^ 2 ≤ packetForm Q (stepPacket R J σ) := by
  let A : SuzukiPositiveAperture := ⟨1881 / 5000, by norm_num⟩
  have hlen : Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * A.1 :=
    log_window_lt_of_firstStep hR hJ
  have hcut : R + J < (Q + 1) * R :=
    lt_of_lt_of_le (by omega : R + J < 3 * R) (Nat.mul_le_mul_right R (by omega))
  have hμ : (1 / 50000 : ℝ) ≤ ccmRestrictedWeilGroundEnergy A :=
    one_div_50000_le_groundEnergy_of_aperture_le_1881_over_5000 le_rfl
  have hfloor := groundEnergy_mul_le_packetForm_stepPacket (A := A) hR hlen hcut σ
  exact (mul_le_mul_of_nonneg_right hμ (Finset.sum_nonneg fun j _ => sq_nonneg _)).trans hfloor

/-- Every block matrix of a window of ratio at most `10609/5000` is uniformly positive definite. -/
theorem sum_blockMatrix_ge_of_first_overlap {R J Q : ℕ}
    (hR : 1 ≤ R) (hJ : 5000 * (R + J) ≤ 10609 * R) (hQ : 2 ≤ Q) (σ : ℕ → ℝ) :
    (1 / 50000 : ℝ) * ∑ j ∈ range J, σ j ^ 2 ≤
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockMatrix Q (R + j) (R + l) := by
  rw [← packetForm_stepPacket_eq_sum_blockMatrix hR Q J σ]
  exact packetForm_stepPacket_ge_of_first_overlap hR hJ hQ σ

#print axioms fullZeroForm_ge_at_aperture_1881_over_5000
#print axioms zetaZeroConfig_re_W_ge_at_aperture_1881_over_5000
#print axioms one_div_50000_le_groundEnergy_of_aperture_le_1881_over_5000
#print axioms packetForm_stepPacket_ge_of_first_overlap
#print axioms sum_blockMatrix_ge_of_first_overlap

end GaloisForLFunctions.WindowTowerOfSpecZ
