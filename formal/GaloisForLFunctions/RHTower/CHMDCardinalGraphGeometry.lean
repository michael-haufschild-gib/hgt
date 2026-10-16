import GaloisForLFunctions.RHTower.CHMDCardinalOrbitEnergy
import GaloisForLFunctions.RHTower.CHMDFiniteDivisorPairing
import GaloisForLFunctions.RHTower.CHMDPolarGraphMoments

/-!
# Admitted primitive cardinal frames and their exact signed form

Every Xi zero with positive real part supplies an actual frame in the full
arithmetic graph. Polar cancellation places both vectors in the primitive
hyperplane. Complete multiplicity removal gives exact cardinal values, and
the signed form is diagonal, with a balanced positive/negative block at each
nonreal orbit. No positivity hypothesis or zero-simplicity premise is used.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
noncomputable section
namespace RHTower
open WeilSpectral

/-- Every centered Xi zero is represented in the literal zeta zero carrier. -/
theorem exists_carrier_gammaOf_eq {a : ℂ} (hz : XiC a = 0) :
    ∃ ρ : zetaZeroConfig.carrier, gammaOf ρ = a := by
  let s : ℂ := 1/2 + a*I
  have hs : xi s = 0 := hz
  let q : XiDivisorSupport := ⟨s, mem_xi_divisor_support_of_eq_zero hs⟩
  have hstrip : 0 < s.re ∧ s.re < 1 := xi_divisor_support_re_mem_open_unit q
  have hs1 : s ≠ 1 := by intro h; simpa [h] using hstrip.2
  let ρ : zetaZeroConfig.carrier := ⟨s, (xi_eq_zero_iff hstrip.1 hs1).mp hs, hstrip⟩
  refine ⟨ρ, ?_⟩
  change (s - 1/2)/I = a
  dsimp [s]
  rw [add_sub_cancel_left, mul_div_cancel_right₀ _ I_ne_zero]

theorem cardinalPositiveMass_pos_of_zero {a : ℂ} (hz : XiC a = 0) :
    0 < cardinalPositiveMass a := by
  obtain ⟨ρ, hρ⟩ := exists_carrier_gammaOf_eq hz
  exact cardinalPositiveMass_pos ρ (Or.inl hρ)

namespace CHMDDoobGraph

theorem sourceEnergy_linearCombination_of_pair_zero {p q : SourceGraph}
    (hB : sourcePair p q = 0) (r s : ℝ) :
    sourceEnergy (r • p + s • q) = r^2 * sourceEnergy p + s^2 * sourceEnergy q := by
  have hright (x y z : SourceGraph) : sourcePair x (y+z) = sourcePair x y + sourcePair x z := by
    rw [sourcePair_symm, sourcePair_add_left, sourcePair_symm y x, sourcePair_symm z x]
  have hsmul (c : ℝ) (x y : SourceGraph) : sourcePair x (c • y) = c * sourcePair x y := by
    rw [sourcePair_symm, sourcePair_smul_left, sourcePair_symm y x]
  rw [← sourcePair_self, sourcePair_add_left]
  simp only [sourcePair_smul_left, hright, hsmul, sourcePair_self,
    sourcePair_symm q p, hB, mul_zero, zero_add, add_zero]
  ring

/-- A frame records literal sources, compact approximation, primitive status,
and the complete signed form, rather than just abstract strip multipliers. -/
structure CardinalGraphFrame (a : ℂ) where
  reVector : SourceGraph
  imVector : SourceGraph
  re_compact : reVector ∈ closure (compactTests : Set SourceGraph)
  im_compact : imVector ∈ closure (compactTests : Set SourceGraph)
  re_source : reVector.val.fst =ᵐ[massMeasure] phiDoobInv (fun x => (divisorCardinalSource a x).re)
  im_source : imVector.val.fst =ᵐ[massMeasure] phiDoobInv (fun x => (divisorCardinalSource a x).im)
  complex_source : complexSource reVector imVector =ᵐ[volume] divisorCardinalSource a
  re_primitive : sourcePair (constantLift 1) reVector = 0
  im_primitive : sourcePair (constantLift 1) imVector = 0
  re_energy : sourceEnergy reVector = cardinalPositiveMass a
  im_energy : sourceEnergy imVector = -cardinalNegativeMass a
  cross_pair : sourcePair reVector imVector = 0

/-- All admission and primitive obligations are discharged on the actual cardinal source. -/
theorem exists_cardinalGraphFrame {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) :
    Nonempty (CardinalGraphFrame a) := by
  obtain ⟨_, hj, hl, he, hb⟩ := divisorCardinalSource_regularity ha hz
  obtain ⟨p, q, hp, hq, hpr, hqi, hsource, hE, hF, hB⟩ := exists_complex_signed_graph hj hl hb
  have hr : cardinalRealSource a 1 = fun x => (divisorCardinalSource a x).re := by
    funext x
    simp [cardinalRealSource]
  have hi : cardinalRealSource a (-I) = fun x => (divisorCardinalSource a x).im := by
    funext x
    simp [cardinalRealSource, Complex.mul_re]
  have hs : cardinalRealSource a (1-I) =
      (fun x => (divisorCardinalSource a x).re) + (fun x => (divisorCardinalSource a x).im) := by
    funext x
    simp [cardinalRealSource, Complex.mul_re]
  have hEr : sourceEnergy p = cardinalPositiveMass a := by
    rw [hE, ← hr, signedZeroEnergy_cardinalRealSource ha hz]
    simp
  have hEi : sourceEnergy q = -cardinalNegativeMass a := by
    rw [hF, ← hi, signedZeroEnergy_cardinalRealSource ha hz]
    simp
  have hB0 : sourcePair p q = 0 := by
    rw [hB, signedZeroPair, ← hs, ← hr, ← hi]
    simp only [signedZeroEnergy_cardinalRealSource ha hz]
    simp
  obtain ⟨C, hC⟩ := hl
  obtain ⟨M, hM⟩ := hb
  simp_rw [thetaCuspFullSource_eq_riemannKernelReal] at hM
  have hpolarR : paperFT (fun x => ((divisorCardinalSource a x).re : ℂ)) (I/2) = 0 := by
    simpa only [hr] using (cardinalRealSource_poles ha hz 1).1
  have hpolarI : paperFT (fun x => ((divisorCardinalSource a x).im : ℂ)) (I/2) = 0 := by
    simpa only [hi] using (cardinalRealSource_poles ha hz (-I)).1
  have hpr0 : sourcePair (constantLift 1) p = 0 := by
    rw [sourcePair_ground_eq_polar hj.re ⟨1*C, RCLike.lipschitzWith_re.comp hC⟩
      ⟨M, fun x => (Complex.abs_re_le_norm _).trans (hM x)⟩
      (fun x => by rw [he x]) hpr, hpolarR]
    simp
  have hqi0 : sourcePair (constantLift 1) q = 0 := by
    rw [sourcePair_ground_eq_polar hj.im ⟨1*C, RCLike.lipschitzWith_im.comp hC⟩
      ⟨M, fun x => (Complex.abs_im_le_norm _).trans (hM x)⟩
      (fun x => by rw [he x]) hqi, hpolarI]
    simp
  exact ⟨⟨p, q, hp, hq, hpr, hqi, hsource, hpr0, hqi0, hEr, hEi, hB0⟩⟩

theorem CardinalGraphFrame.transform {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) {z : ℂ} (hzero : XiC z = 0) :
    sourceTransform (complexSource F.reVector F.imVector) z =
      if z = a ∨ z = -a then 1 else 0 := by
  rw [sourceTransform_congr_ae F.complex_source]
  exact divisorCardinalSource_transform ha hz hzero

theorem CardinalGraphFrame.poles {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) :
    sourceTransform (complexSource F.reVector F.imVector) (I/2) = 0 ∧
      sourceTransform (complexSource F.reVector F.imVector) (-I/2) = 0 := by
  simp only [sourceTransform_congr_ae F.complex_source]
  exact divisorCardinalSource_poles ha hz

/-- The exact form of every real linear combination in the admitted primitive frame. -/
theorem CardinalGraphFrame.energy {a : ℂ} (F : CardinalGraphFrame a) (r s : ℝ) :
    sourceEnergy (r • F.reVector + s • F.imVector) =
      r^2 * cardinalPositiveMass a - s^2 * cardinalNegativeMass a := by
  rw [sourceEnergy_linearCombination_of_pair_zero F.cross_pair, F.re_energy, F.im_energy]
  ring

theorem CardinalGraphFrame.primitive {a : ℂ} (F : CardinalGraphFrame a) (r s : ℝ) :
    sourcePair (constantLift 1) (r • F.reVector + s • F.imVector) = 0 := by
  rw [sourcePair_symm, sourcePair_add_left, sourcePair_smul_left, sourcePair_smul_left,
    sourcePair_symm F.reVector, sourcePair_symm F.imVector, F.re_primitive, F.im_primitive]
  simp

theorem CardinalGraphFrame.nonreal_energy {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hi : a.im ≠ 0) (r s : ℝ) :
    sourceEnergy (r • F.reVector + s • F.imVector) = cardinalPositiveMass a * (r^2-s^2) := by
  rw [F.energy, ← cardinalPositiveMass_eq_negative ha hi]
  ring

theorem CardinalGraphFrame.real_energy {a : ℂ} (F : CardinalGraphFrame a)
    (hi : a.im = 0) (r s : ℝ) :
    sourceEnergy (r • F.reVector + s • F.imVector) = cardinalPositiveMass a * r^2 := by
  rw [F.energy, cardinalNegativeMass_eq_zero_of_real hi]
  ring

theorem CardinalGraphFrame.nonreal_signs {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (hi : a.im ≠ 0) :
    0 < sourceEnergy F.reVector ∧ sourceEnergy F.imVector < 0 := by
  rw [F.re_energy, F.im_energy, ← cardinalPositiveMass_eq_negative ha hi]
  exact ⟨cardinalPositiveMass_pos_of_zero hz, neg_neg_of_pos (cardinalPositiveMass_pos_of_zero hz)⟩

/-- The nonreal frame is a genuine two-dimensional plane in the original graph. -/
theorem CardinalGraphFrame.nonreal_linearCombination_eq_zero_iff {a : ℂ}
    (F : CardinalGraphFrame a) (ha : 0 < a.re) (hz : XiC a = 0) (hi : a.im ≠ 0)
    (r s : ℝ) : r • F.reVector + s • F.imVector = 0 ↔ r = 0 ∧ s = 0 := by
  constructor
  · intro heq
    have hsign := F.nonreal_signs ha hz hi
    have hp : r * sourceEnergy F.reVector = 0 := by
      calc
        _ = sourcePair (r • F.reVector + s • F.imVector) F.reVector := by
          rw [sourcePair_add_left, sourcePair_smul_left, sourcePair_smul_left,
            sourcePair_self, sourcePair_symm F.imVector, F.cross_pair, mul_zero, add_zero]
        _ = 0 := by rw [heq]; simp [sourcePair]
    have hq : s * sourceEnergy F.imVector = 0 := by
      calc
        _ = sourcePair (r • F.reVector + s • F.imVector) F.imVector := by
          rw [sourcePair_add_left, sourcePair_smul_left, sourcePair_smul_left,
            F.cross_pair, sourcePair_self, mul_zero, zero_add]
        _ = 0 := by rw [heq]; simp [sourcePair]
    exact ⟨(mul_eq_zero.mp hp).resolve_right hsign.1.ne',
      (mul_eq_zero.mp hq).resolve_right hsign.2.ne⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- An unconditional nonzero primitive cardinal frame at an actual positive real Xi zero. -/
theorem exists_positive_primitive_cardinal_frame :
    ∃ (a : ℝ) (F : CardinalGraphFrame (a : ℂ)), 0 < a ∧ XiC (a : ℂ) = 0 ∧
      0 < sourceEnergy F.reVector ∧ sourceEnergy F.imVector = 0 ∧
      sourceTransform (complexSource F.reVector F.imVector) (a : ℂ) = 1 := by
  obtain ⟨a, ha, hz, _, _⟩ := exists_positive_thetaZeroDivision
  obtain ⟨F⟩ := exists_cardinalGraphFrame ha hz
  refine ⟨a, F, ha, hz, ?_, ?_, ?_⟩
  · rw [F.re_energy]
    exact cardinalPositiveMass_pos_of_zero hz
  · rw [F.im_energy, cardinalNegativeMass_eq_zero_of_real (by simp), neg_zero]
  · simpa using F.transform ha hz hz

end CHMDDoobGraph
end RHTower
