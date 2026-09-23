import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthBoundaryKreinReduction
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthScaleEighteenFifthsDirectAffineJoint
import GaloisForLFunctions.HTGeometry.RealTreeBPFirstCrossing

/-!
# Theta D1 boundary flux closes the finite crossing burden

This module isolates the exact remaining source theorem for the finite TCD rank-three gate.
Positive canonical boundary flux at every singular point of the missing chamber excludes a first
loss.  Seam strictness and the established right-hand chamber then yield D1 on the whole
nonnegative physical orbit.  Thus the open burden is source crossing orientation, not further
compact-interval bookkeeping.
-/

open Real Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- First zero with a weakly nonpositive right endpoint. -/
theorem exists_first_zero_of_pos_of_nonpos
    {H : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn H (Icc a b)) (hpos : 0 < H a) (hnonpos : H b ≤ 0) :
    ∃ c ∈ Ioc a b, H c = 0 ∧ ∀ y ∈ Ico a c, 0 < H y := by
  classical
  set S : Set ℝ := Icc a b ∩ H ⁻¹' Iic 0 with hS
  have hSclosed : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨b, ⟨⟨hab.le, le_refl b⟩, hnonpos⟩⟩
  have hSbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
  set c := sInf S with hc
  have hcS : c ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hac : a ≤ c := hcS.1.1
  have hcb : c ≤ b := hcS.1.2
  have hHc_le : H c ≤ 0 := hcS.2
  have hane : a ≠ c := by
    intro h
    rw [← h] at hHc_le
    exact absurd hpos (not_lt.2 hHc_le)
  have hac' : a < c := lt_of_le_of_ne hac hane
  have hleft : ∀ y ∈ Ico a c, 0 < H y := by
    intro y hy
    by_contra hcon
    have hyS : y ∈ S := ⟨⟨hy.1, le_trans hy.2.le hcb⟩, not_lt.1 hcon⟩
    exact absurd (csInf_le hSbdd hyS) (not_le.2 hy.2)
  have hIoo : Ioo a c ∈ 𝓝[<] c := by
    have h1 : Ioi a ∈ 𝓝 c := Ioi_mem_nhds hac'
    have h2 := inter_mem_nhdsWithin (Iio c) h1
    have hset : Iio c ∩ Ioi a = Ioo a c := by
      ext y
      simp [Set.mem_Ioo, and_comm]
    rwa [hset] at h2
  have hHc_ge : 0 ≤ H c := by
    have hcw : ContinuousWithinAt H (Icc a b) c := hcont c ⟨hac, hcb⟩
    have hle : 𝓝[<] c ≤ 𝓝[Icc a b] c := by
      refine le_inf inf_le_left ?_
      refine le_principal_iff.2 ?_
      filter_upwards [hIoo] with y hy
      exact ⟨hy.1.le, le_trans hy.2.le hcb⟩
    have htend : Tendsto H (𝓝[<] c) (𝓝 (H c)) := hcw.tendsto.mono_left hle
    refine ge_of_tendsto htend ?_
    filter_upwards [hIoo] with y hy
    exact (hleft y ⟨hy.1.le, hy.2⟩).le
  exact ⟨c, ⟨hac', hcb⟩, le_antisymm hHc_le hHc_ge, hleft⟩

end

end GaloisForLFunctions.HTGeometry

namespace HilbertMetric

/-- A strict lower face and a singular rank-three Hankel matrix do not determine crossing
orientation. The two-atom moment face in this witness has positive mass and strict leading
rank-two determinant, but admits a negative null-line crossing. Thus the TCD boundary theorem
cannot follow from generic finite Hankel geometry; theta source dynamics are indispensable. -/
theorem exists_signedEvenHankelThree_singular_strictHead_negativeCrossing :
    ∃ p₀ p₂ p₄ p₆ p₈ q₀ q₂ q₄ q₆ q₈ : ℝ,
      signedEvenHankelThreeDet p₀ p₂ p₄ p₆ p₈ = 0 ∧
      0 < p₀ ∧ 0 < p₀ * p₄ - p₂ ^ (2 : ℕ) ∧
      signedEvenHankelThreeBoundaryCrossing
        p₀ p₂ p₄ p₆ q₀ q₂ q₄ q₆ q₈ < 0 := by
  refine ⟨2, 1, 1, 1, 1, 0, 0, 0, 0, -1, ?_⟩
  norm_num [signedEvenHankelThreeDet, signedEvenHankelThreeBoundaryCrossing]

end HilbertMetric

namespace RHTower

noncomputable section

/-- Positive canonical boundary flux at every singular point in the missing chamber excludes every
first loss of rank-three D1 there. Together with seam strictness and the established right-hand
chamber, this closes D1 on the nonnegative physical orbit. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_boundaryCrossing
    (hcross : ∀ x : ℝ, 0 < x → x < (137 / 2000 : ℝ) →
      thetaCuspFullSourceReflectionEighthHankelCurvature x = 0 →
      0 < thetaCuspFullSourceReflectionEighthBoundaryCrossing x) :
    ∀ x : ℝ, 0 ≤ x → 0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  intro x hx
  rcases hx.eq_or_lt with rfl | hxpos
  · exact thetaCuspFullReflectionEighthHankelCurvature_zero_pos
  by_cases hxb : (137 / 2000 : ℝ) ≤ x
  · exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_oneHundredThirtySevenTwoThousandths_le
      hxb
  have hxlt : x < (137 / 2000 : ℝ) := lt_of_not_ge hxb
  by_contra hnot
  have hxnonpos : thetaCuspFullReflectionEighthHankelCurvature x ≤ 0 := not_lt.mp hnot
  obtain ⟨c, hc, hczero, hleft⟩ :=
    GaloisForLFunctions.HTGeometry.exists_first_zero_of_pos_of_nonpos hxpos
      (fun y hy => by
        rcases hy.1.eq_or_lt with rfl | hypos
        · exact continuousAt_thetaCuspFullReflectionEighthHankelCurvature_zero.continuousWithinAt
        · exact
            (hasDerivAt_thetaCuspFullReflectionEighthHankelCurvature_projectiveDrift
              hypos).continuousAt.continuousWithinAt)
      thetaCuspFullReflectionEighthHankelCurvature_zero_pos hxnonpos
  have hcpos : 0 < c := hc.1
  have hclt : c < (137 / 2000 : ℝ) := hc.2.trans_lt hxlt
  have hrawzero : thetaCuspFullSourceReflectionEighthHankelCurvature c = 0 := by
    rw [thetaCuspFullSourceReflectionEighthHankelCurvature_eq_fullReflection hcpos, hczero]
    ring
  have hboundary := hcross c hcpos hclt hrawzero
  have hdrift : 0 < thetaCuspReflectedEighthSourceProjectiveDrift c :=
    (thetaCuspReflectedEighthSourceProjectiveDrift_pos_iff_boundaryCrossing_pos_of_zero
      hcpos hrawzero).2 hboundary
  have hderivpos : 0 < deriv thetaCuspFullReflectionEighthHankelCurvature c :=
    (deriv_thetaCuspFullReflectionEighthHankelCurvature_pos_iff_projectiveDrift_pos hcpos).2
      hdrift
  have hd := hasDerivAt_thetaCuspFullReflectionEighthHankelCurvature_projectiveDrift hcpos
  have hderivnonpos :
      thetaCuspReflectedEighthSourceProjectiveDrift c /
        (4 * (thetaCuspModularSourcePositiveState
          HTGeometry.ModularThetaSourcePositiveState.Q c).re ^ (7 : ℕ)) ≤ 0 :=
    GaloisForLFunctions.HTGeometry.deriv_nonpos_of_first_zero hcpos hd hczero hleft
  rw [hd.deriv] at hderivpos
  linarith

/-- Global nonnegative-orbit D1 is equivalent to positive canonical flux at every singular point
of the missing chamber. The forward implication is vacuous because global D1 excludes such a
face; the reverse implication is the first-crossing theorem above. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_iff_boundaryCrossing :
    (∀ x : ℝ, 0 ≤ x → 0 < thetaCuspFullReflectionEighthHankelCurvature x) ↔
      (∀ x : ℝ, 0 < x → x < (137 / 2000 : ℝ) →
        thetaCuspFullSourceReflectionEighthHankelCurvature x = 0 →
        0 < thetaCuspFullSourceReflectionEighthBoundaryCrossing x) := by
  constructor
  · intro hglobal x hx _ hrawzero
    have hnative := hglobal x hx.le
    rw [thetaCuspFullSourceReflectionEighthHankelCurvature_eq_fullReflection hx] at hrawzero
    have hsource := thetaCuspFullSource_pos_all x
    nlinarith [pow_pos hsource 6]
  · exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_boundaryCrossing

end

end RHTower
