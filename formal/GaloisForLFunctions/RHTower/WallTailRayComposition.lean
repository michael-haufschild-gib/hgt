import GaloisForLFunctions.RHTower.WallTailBlockDecomposition

/-!
# Composing the four ray estimates

The four terms of the block decomposition have to be separated *inside* the frequency integral as
well, and for that each of them must be measurable in the frequency.  Three are: the propagated
threshold vector is continuous, and the two moving-endpoint averages are parametrised Bochner
integrals whose integrands are jointly continuous in frequency and position wherever the floor is
open — which is exactly the region the threshold selects.  The fourth is then measurable as a
combination, because the whole propagated tail is continuous in the frequency.

Composition then costs a fixed factor: four terms in the extended norm cost sixteen in the square.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- Four terms cost a factor sixteen. -/
theorem sq_add_four_le (a b c d : ℝ≥0∞) :
    (a + b + c + d) ^ 2 ≤ 16 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  have hpair : ∀ u v : ℝ≥0∞, (u + v) ^ 2 ≤ 4 * (u ^ 2 + v ^ 2) := by
    intro u v
    have h1 : u + v ≤ 2 * max u v :=
      (add_le_add (le_max_left u v) (le_max_right u v)).trans (by rw [two_mul])
    have h2 : max u v ^ 2 ≤ u ^ 2 + v ^ 2 := by
      rcases max_choice u v with h | h <;> rw [h]
      · exact le_self_add
      · exact le_add_self
    calc (u + v) ^ 2 ≤ (2 * max u v) ^ 2 := pow_le_pow_left' h1 2
      _ = 4 * max u v ^ 2 := by ring
      _ ≤ 4 * (u ^ 2 + v ^ 2) := mul_le_mul' le_rfl h2
  calc (a + b + c + d) ^ 2 = ((a + b) + (c + d)) ^ 2 := by ring_nf
    _ ≤ 4 * ((a + b) ^ 2 + (c + d) ^ 2) := hpair _ _
    _ ≤ 4 * (4 * (a ^ 2 + b ^ 2) + 4 * (c ^ 2 + d ^ 2)) :=
        mul_le_mul' le_rfl (add_le_add (hpair a b) (hpair c d))
    _ = 16 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by ring

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

omit [Nontrivial X] [CompleteSpace X] in
/-- For a profile supported in the block the two first-boundary averages agree. -/
theorem firstBoundaryBlock_eq_firstBoundary {g : ℝ → X} {m σ x : ℝ}
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) :
    firstBoundaryBlock T g m σ x = firstBoundary T g σ x := by
  rw [firstBoundaryBlock, firstBoundary]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun L hL => ?_
  rw [hsupp L hL, map_zero, smul_zero]

/-! ## Measurability of the two moving-endpoint averages -/

omit [Nontrivial X] [CompleteSpace X] in
theorem continuous_wallGeneratorD1 {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous fun x : ℝ => wallGeneratorD1 X σ x := by
  have hscal : Continuous (wallScalarD1 σ) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hasDerivAt_wallScalarD1 hσ0 hσ1 t).continuousAt
  have h : Continuous fun x : ℝ => wallScalarD1 σ x • (ContinuousLinearMap.id ℂ X) :=
    hscal.smul continuous_const
  exact h

omit [Nontrivial X] in
theorem continuousOn_invFamilyProduct_pair {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {S : Set (ℝ × ℝ)} (hgap : ∀ p ∈ S, 0 < wallFloor T σ p.2 + p.1) :
    ContinuousOn (fun p : ℝ × ℝ =>
      invFamilyProduct (wallGeneratorShift T σ p.1) (wallGeneratorD1 X σ) p.2) S := by
  have hA := continuousOn_invFamily_pair (T := T) hσ0 hσ1 hgap
  have hD1 : ContinuousOn (fun p : ℝ × ℝ => wallGeneratorD1 X σ p.2) S :=
    ((continuous_wallGeneratorD1 (X := X) hσ0 hσ1).comp continuous_snd).continuousOn
  have h : ContinuousOn (fun p : ℝ × ℝ =>
      invFamily (wallGeneratorShift T σ p.1) p.2
        * -(invFamily (wallGeneratorShift T σ p.1) p.2 * wallGeneratorD1 X σ p.2
            * invFamily (wallGeneratorShift T σ p.1) p.2)) S :=
    hA.mul (((hA.mul hD1).mul hA).neg)
  exact h

set_option maxHeartbeats 1000000 in
omit [Nontrivial X] in
theorem aestronglyMeasurable_firstBoundaryBlock {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g : ℝ → X} {m Y : ℝ} (hg : AEStronglyMeasurable g (volume.restrict (Icc m (m + 1))))
    (hgap : ∀ x ∈ Ioi Y, ∀ L ∈ Icc m (m + 1), 0 < wallFloor T σ x + L) :
    AEStronglyMeasurable (fun x => firstBoundaryBlock T g m σ x) (volume.restrict (Ioi Y)) := by
  set μ : Measure ℝ := volume.restrict (Ioi Y) with hμ
  set ν : Measure ℝ := volume.restrict (Icc m (m + 1)) with hν
  have hprod : μ.prod ν = (volume.prod volume).restrict (Ioi Y ×ˢ Icc m (m + 1)) := by
    rw [hμ, hν, Measure.prod_restrict]
  have hset : MeasurableSet (Ioi Y ×ˢ Icc m (m + 1)) := measurableSet_Ioi.prod measurableSet_Icc
  -- the operator factor is continuous on the region
  have hAcont : ContinuousOn (fun p : ℝ × ℝ => invFamily (wallGeneratorShift T σ p.2) p.1)
      (Ioi Y ×ˢ Icc m (m + 1)) := by
    have hswap : ContinuousOn (fun q : ℝ × ℝ => invFamily (wallGeneratorShift T σ q.1) q.2)
        (Icc m (m + 1) ×ˢ Ioi Y) := by
      refine continuousOn_invFamily_pair (T := T) hσ0 hσ1 ?_
      intro q hq
      exact hgap q.2 hq.2 q.1 hq.1
    have hcont : Continuous (Prod.swap : ℝ × ℝ → ℝ × ℝ) := continuous_swap
    have hmaps : MapsTo (Prod.swap : ℝ × ℝ → ℝ × ℝ) (Ioi Y ×ˢ Icc m (m + 1))
        (Icc m (m + 1) ×ˢ Ioi Y) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := hp
      exact ⟨hp2, hp1⟩
    have hres := hswap.comp hcont.continuousOn hmaps
    exact hres
  have hAm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => invFamily (wallGeneratorShift T σ p.2) p.1) (μ.prod ν) := by
    rw [hprod]
    exact hAcont.aestronglyMeasurable hset
  have hgm : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2) (μ.prod ν) := hg.comp_snd
  have hev : AEStronglyMeasurable
      (fun p : ℝ × ℝ => invFamily (wallGeneratorShift T σ p.2) p.1 (g p.2)) (μ.prod ν) :=
    ContinuousLinearMap.aestronglyMeasurable_comp₂ (ContinuousLinearMap.apply ℂ X) hgm hAm
  have hph : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Complex.exp (-(Complex.I) * (p.2 : ℂ) * (p.1 : ℂ))) (μ.prod ν) := by
    have : Continuous fun p : ℝ × ℝ => Complex.exp (-(Complex.I) * (p.2 : ℂ) * (p.1 : ℂ)) := by
      fun_prop
    exact this.aestronglyMeasurable
  have hjoint : AEStronglyMeasurable
      (Function.uncurry fun (x : ℝ) (L : ℝ) =>
        Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
          • (invFamily (wallGeneratorShift T σ L) x (g L))) (μ.prod ν) := hph.smul hev
  exact hjoint.integral_prod_right'

set_option maxHeartbeats 1000000 in
omit [Nontrivial X] in
theorem aestronglyMeasurable_secondBoundary {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g : ℝ → X} {m Y : ℝ} (hg : AEStronglyMeasurable g (volume.restrict (Icc m (m + 1))))
    (hgap : ∀ x ∈ Ioi Y, ∀ L ∈ Icc m (m + 1), 0 < wallFloor T σ x + L) :
    AEStronglyMeasurable (fun x => secondBoundary T g m σ x) (volume.restrict (Ioi Y)) := by
  set μ : Measure ℝ := volume.restrict (Ioi Y) with hμ
  set ν : Measure ℝ := volume.restrict (Icc m (m + 1)) with hν
  have hprod : μ.prod ν = (volume.prod volume).restrict (Ioi Y ×ˢ Icc m (m + 1)) := by
    rw [hμ, hν, Measure.prod_restrict]
  have hset : MeasurableSet (Ioi Y ×ˢ Icc m (m + 1)) := measurableSet_Ioi.prod measurableSet_Icc
  have hAcont : ContinuousOn (fun p : ℝ × ℝ =>
      invFamilyProduct (wallGeneratorShift T σ p.2) (wallGeneratorD1 X σ) p.1)
      (Ioi Y ×ˢ Icc m (m + 1)) := by
    have hswap : ContinuousOn (fun q : ℝ × ℝ =>
        invFamilyProduct (wallGeneratorShift T σ q.1) (wallGeneratorD1 X σ) q.2)
        (Icc m (m + 1) ×ˢ Ioi Y) := by
      refine continuousOn_invFamilyProduct_pair (T := T) hσ0 hσ1 ?_
      intro q hq
      exact hgap q.2 hq.2 q.1 hq.1
    have hcont : Continuous (Prod.swap : ℝ × ℝ → ℝ × ℝ) := continuous_swap
    have hmaps : MapsTo (Prod.swap : ℝ × ℝ → ℝ × ℝ) (Ioi Y ×ˢ Icc m (m + 1))
        (Icc m (m + 1) ×ˢ Ioi Y) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := hp
      exact ⟨hp2, hp1⟩
    have hres := hswap.comp hcont.continuousOn hmaps
    exact hres
  have hAm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      invFamilyProduct (wallGeneratorShift T σ p.2) (wallGeneratorD1 X σ) p.1) (μ.prod ν) := by
    rw [hprod]
    exact hAcont.aestronglyMeasurable hset
  have hgm : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2) (μ.prod ν) := hg.comp_snd
  have hev : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      invFamilyProduct (wallGeneratorShift T σ p.2) (wallGeneratorD1 X σ) p.1 (g p.2))
      (μ.prod ν) :=
    ContinuousLinearMap.aestronglyMeasurable_comp₂ (ContinuousLinearMap.apply ℂ X) hgm hAm
  have hph : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Complex.exp (-(Complex.I) * (p.2 : ℂ) * (p.1 : ℂ))) (μ.prod ν) := by
    have : Continuous fun p : ℝ × ℝ => Complex.exp (-(Complex.I) * (p.2 : ℂ) * (p.1 : ℂ)) := by
      fun_prop
    exact this.aestronglyMeasurable
  exact (hph.smul hev).integral_prod_right'

end GaloisForLFunctions.RHTower
