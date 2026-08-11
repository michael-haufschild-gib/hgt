import GaloisForLFunctions.RHTower.XiResolventMassRigidity
import GaloisForLFunctions.RHTower.CCMCliffordWeilProduct
import GaloisForLFunctions.RHTower.CCMUniversalWeilSourceReconstruction

/-!
# Resolvent mass as an exact line-reflection defect

The imaginary resolvent mass is exactly one quarter of the squared Hilbert distance between the
resolvent evaluation and its critical-line reflection.  Consequently RH is equivalent to literal
fixedness of every nonnegative resolvent carrier.  The same identity also rewrites the mass as the
gap between the ordinary Hilbert norm and the unconditional Weil quadratic form.

Both orientations lie in the *same* closed continued-Cauchy source carrier and admit separated
finite-source reconstruction.  This identifies the remaining producer sharply: source closure
alone contains the reflection defect but does not make it vanish; an additional source law must
force the two reconstructed orientations to agree.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The resolvent test whose divisor evaluation is the mass-rigidity carrier. -/
def xiResolventTest (X : ℝ) (z : ℂ) : ℂ :=
  (z ^ 2 + (X : ℂ))⁻¹

theorem xiResolventTest_squareSummable {X : ℝ} (hX : 0 ≤ X) :
    XiWeilSquareSummable (xiResolventTest X) := by
  unfold XiWeilSquareSummable
  apply Summable.of_nonneg_of_le (fun q => sq_nonneg _) ?_
    (summable_norm_xiResolventPoint hX)
  intro q
  change ‖xiResolventPoint X q‖ ^ 2 ≤ ‖xiResolventPoint X q‖
  have hle := norm_xiResolventPoint_le_one hX q
  nlinarith [norm_nonneg (xiResolventPoint X q)]

/-- The multiplicity-faithful resolvent evaluation on the Xi zero carrier. -/
def xiResolventLp (X : ℝ) (hX : 0 ≤ X) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiWeilEvaluationLp (xiResolventTest X) (xiResolventTest_squareSummable hX)

@[simp] theorem xiResolventLp_apply (X : ℝ) (hX : 0 ≤ X) (q : XiZeroCopy) :
    xiResolventLp X hX q = xiResolventPoint X q := rfl

@[simp] theorem xiWeilLineConjLinearIsometry_xiResolventLp_apply
    (X : ℝ) (hX : 0 ≤ X) (q : XiZeroCopy) :
    xiWeilLineConjLinearIsometry (xiResolventLp X hX) q =
      (starRingEnd ℂ) (xiResolventLp X hX q) := by
  rw [xiWeilLineConjLinearIsometry_apply, xiWeilLineConjLp_apply,
    xiResolventLp_apply, xiResolventLp_apply, xiResolventPoint_lineConj]

/-- Exact Frankenstein seam: resolvent imaginary mass is the line-reflection defect energy. -/
theorem norm_sq_xiResolvent_reflectionDefect (X : ℝ) (hX : 0 ≤ X) :
    ‖xiResolventLp X hX -
        xiWeilLineConjLinearIsometry (xiResolventLp X hX)‖ ^ 2 =
      4 * xiResolventImSqMass X := by
  rw [HilbertSchmidt.lp_norm_sq_eq, xiResolventImSqMass, ← tsum_mul_left]
  apply tsum_congr
  intro q
  change ‖xiResolventPoint X q -
      xiResolventPoint X (xiZeroCopyLineConjEquiv q)‖ ^ 2 =
    4 * (xiResolventPoint X q).im ^ 2
  rw [xiResolventPoint_lineConj, Complex.norm_sub_conj]
  ring

/-- The same mass is the exact deficit between norm energy and the Weil quadratic form. -/
theorem two_mul_xiResolventImSqMass_eq_norm_sq_sub_quadratic
    (X : ℝ) (hX : 0 ≤ X) :
    2 * xiResolventImSqMass X =
      ‖xiResolventLp X hX‖ ^ 2 -
        xiWeilHilbertQuadratic (xiResolventLp X hX) := by
  have hminus := CliffordWeil.minus_channel_energy_eq
    xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive
      (xiResolventLp X hX)
  rw [norm_sq_xiResolvent_reflectionDefect X hX] at hminus
  unfold CliffordWeil.quadratic xiWeilHilbertQuadratic at hminus ⊢
  nlinarith

/-- At any nonnegative resolvent parameter, RH is precisely line-reflection fixedness. -/
theorem riemannHypothesis_iff_xiResolventLp_lineConj_fixed {X : ℝ} (hX : 0 ≤ X) :
    RiemannHypothesis ↔
      xiWeilLineConjLinearIsometry (xiResolventLp X hX) = xiResolventLp X hX := by
  rw [riemannHypothesis_iff_xiResolventImSqMass_eq_zero hX]
  constructor
  · intro hmass
    have hnorm := norm_sq_xiResolvent_reflectionDefect X hX
    rw [hmass, mul_zero] at hnorm
    have hz : xiResolventLp X hX -
        xiWeilLineConjLinearIsometry (xiResolventLp X hX) = 0 := by
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
    exact (sub_eq_zero.mp hz).symm
  · intro hfix
    have hnorm := norm_sq_xiResolvent_reflectionDefect X hX
    rw [hfix, sub_self, norm_zero, zero_pow] at hnorm
    · nlinarith
    · norm_num

/-- Pointwise complex conjugation of the resolvent test gives the reflected orientation. -/
def xiResolventReflectedTest (X : ℝ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (xiResolventTest X z)

theorem xiResolventReflectedTest_squareSummable {X : ℝ} (hX : 0 ≤ X) :
    XiWeilSquareSummable (xiResolventReflectedTest X) := by
  simpa only [XiWeilSquareSummable, xiResolventReflectedTest, map_norm]
    using xiResolventTest_squareSummable hX

theorem xiWeilEvaluationLp_xiResolventReflectedTest
    (X : ℝ) (hX : 0 ≤ X) :
    xiWeilEvaluationLp (xiResolventReflectedTest X)
        (xiResolventReflectedTest_squareSummable hX) =
      xiWeilLineConjLinearIsometry (xiResolventLp X hX) := by
  apply Subtype.ext
  funext q
  rw [xiWeilEvaluationLp_apply, xiResolventReflectedTest,
    xiWeilLineConjLinearIsometry_xiResolventLp_apply, xiResolventLp_apply]
  rfl

/-- Both resolvent orientations are reconstructed inside one continued source carrier. -/
theorem xiResolvent_bothOrientations_mem_continuedCauchyHilbertSubspace
    (X : ℝ) (hX : 0 ≤ X) :
    xiResolventLp X hX ∈ xiWeilContinuedCauchyHilbertSubspace ∧
      xiWeilLineConjLinearIsometry (xiResolventLp X hX) ∈
        xiWeilContinuedCauchyHilbertSubspace := by
  constructor
  · exact xiWeilEvaluationLp_mem_continuedCauchyHilbertSubspace
      (xiResolventTest X) (xiResolventTest_squareSummable hX)
  · rw [← xiWeilEvaluationLp_xiResolventReflectedTest X hX]
    exact xiWeilEvaluationLp_mem_continuedCauchyHilbertSubspace
      (xiResolventReflectedTest X) (xiResolventReflectedTest_squareSummable hX)

/-- Separated finite source packets reconstruct both orientations independently on the same ray. -/
theorem exists_separatedContinuedCauchyPackets_tendsto_xiResolvent_bothOrientations
    (X : ℝ) (hX : 0 ≤ X) :
    ∃ P Psharp : ℕ → XiSeparatedContinuedCauchyPacket,
      Tendsto (fun n => (P n).evaluation) atTop (nhds (xiResolventLp X hX)) ∧
      Tendsto (fun n => (Psharp n).evaluation) atTop
        (nhds (xiWeilLineConjLinearIsometry (xiResolventLp X hX))) := by
  obtain ⟨P, hP⟩ := exists_separatedContinuedCauchyPackets_tendsto_evaluation
    (xiResolventTest X) (xiResolventTest_squareSummable hX)
  obtain ⟨Psharp, hPsharp⟩ := exists_separatedContinuedCauchyPackets_tendsto_evaluation
    (xiResolventReflectedTest X) (xiResolventReflectedTest_squareSummable hX)
  refine ⟨P, Psharp, hP, ?_⟩
  rwa [xiWeilEvaluationLp_xiResolventReflectedTest X hX] at hPsharp

end

end RHTower
