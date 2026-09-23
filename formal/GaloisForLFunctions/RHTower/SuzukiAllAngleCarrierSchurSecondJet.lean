import GaloisForLFunctions.RHTower.SuzukiAnchoredSchurSecondJet
import GaloisForLFunctions.RHTower.SuzukiFiniteApertureHermiteBiehler

/-!
# All-angle Suzuki carrier Schur second-jet bound

Finite-aperture Hermite--Biehler separation turns Suzuki's disk-conjugated Livšic quotient into an
anchored Schur map. This module keeps that analytic bridge independent of parity, Xi-target, and
prime--Gamma moment infrastructure.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

/-- All-angle Hermite--Biehler separation supplies the closed two-jet Schur bound after Cayley
conjugation, without any nondegeneracy assumption on the first jet. -/
theorem norm_suzukiAllAngleCarrier_secondJet_le_schurSlack
    {A E : ℂ → ℂ}
    (hA : Differentiable ℂ A) (hE : Differentiable ℂ E)
    (hAi : A I = 0)
    (hreal : GaloisForLFunctions.RHTower.SuzukiAllAngleRealZeros A E) :
    let f : ℂ → ℂ := fun w =>
      GaloisForLFunctions.RHTower.suzukiLivsicQuotient A E
        (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w)
    ‖iteratedDeriv 2 f 0‖ ≤ 2 * (1 - ‖deriv f 0‖ ^ (2 : ℕ)) := by
  let f : ℂ → ℂ := fun w =>
    GaloisForLFunctions.RHTower.suzukiLivsicQuotient A E
      (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w)
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hquot :=
    GaloisForLFunctions.RHTower.differentiableOn_suzukiLivsicQuotient_upperHalfPlane
      hA hE hAi hreal
  have hf : DifferentiableOn ℂ f (Metric.ball 0 1) := by
    intro w hw
    have hwlt : ‖w‖ < 1 := by
      simpa [mem_ball_zero_iff] using hw
    have hw1 : w ≠ 1 := by
      intro heq
      rw [heq, norm_one] at hwlt
      exact (lt_irrefl 1) hwlt
    have hinv : DifferentiableAt ℂ
        GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w := by
      change DifferentiableAt ℂ (fun v : ℂ => I * ((1 + v) / (1 - v))) w
      fun_prop (disch := exact sub_ne_zero.mpr (Ne.symm hw1))
    have him :=
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_im_pos_of_norm_lt_one hwlt
    have hout : DifferentiableAt ℂ
        (GaloisForLFunctions.RHTower.suzukiLivsicQuotient A E)
        (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w) :=
      hquot.differentiableAt (hopen.mem_nhds him)
    exact (hout.comp w hinv).differentiableWithinAt
  have hf0 : f 0 = 0 := by
    change GaloisForLFunctions.RHTower.suzukiLivsicQuotient A E
      (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv 0) = 0
    rw [show GaloisForLFunctions.RHTower.suzukiUpperCayleyInv 0 = I by
      norm_num [GaloisForLFunctions.RHTower.suzukiUpperCayleyInv]]
    exact GaloisForLFunctions.RHTower.suzukiLivsicQuotient_I_eq_zero hAi
  have hmap : MapsTo f (Metric.ball (0 : ℂ) 1) (Metric.closedBall 0 1) := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    have hwlt : ‖w‖ < 1 := by
      simpa [mem_ball_zero_iff] using hw
    exact (GaloisForLFunctions.RHTower.norm_suzukiLivsicQuotient_lt_one
      hA.continuous hE.continuous hAi hreal
      (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_im_pos_of_norm_lt_one
        hwlt)).le
  exact norm_iteratedDeriv_two_le_schurSlack_closed hf hf0 hmap

end
end RHTower
