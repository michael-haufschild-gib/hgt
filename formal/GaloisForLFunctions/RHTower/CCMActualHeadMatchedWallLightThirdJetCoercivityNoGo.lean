import GaloisForLFunctions.RHTower.CCMActualHeadMatchedWallLightThirdJetTransmutation

open scoped BigOperators

namespace RHTower

noncomputable section

open Matrix

/-- The cubic finite difference on the first four modes of the canonical head `N + 2`.
It annihilates every clock polynomial of degree at most two. -/
def ccmActualHeadThirdJetKernelVector (N : ℕ) : Fin (2 * (N + 2) + 1) → ℝ :=
  fun i =>
    if i.val = 0 then 1
    else if i.val = 1 then -3
    else if i.val = 2 then 3
    else if i.val = 3 then -1
    else 0

theorem ccmActualHeadThirdJetKernelVector_moments (N : ℕ) :
    (∑ i, ccmActualHeadThirdJetKernelVector N i = 0) ∧
      (∑ i, ccmPublishedCenteredClock (N + 2) i *
        ccmActualHeadThirdJetKernelVector N i = 0) ∧
      (∑ i, ccmPublishedCenteredClock (N + 2) i ^ 2 *
        ccmActualHeadThirdJetKernelVector N i = 0) := by
  classical
  let i0 : Fin (2 * (N + 2) + 1) := ⟨0, by omega⟩
  let i1 : Fin (2 * (N + 2) + 1) := ⟨1, by omega⟩
  let i2 : Fin (2 * (N + 2) + 1) := ⟨2, by omega⟩
  let i3 : Fin (2 * (N + 2) + 1) := ⟨3, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    norm_num [i0, i1] at this
  have h02 : i0 ≠ i2 := by
    intro h
    have := congrArg Fin.val h
    norm_num [i0, i2] at this
  have h03 : i0 ≠ i3 := by
    intro h
    have := congrArg Fin.val h
    norm_num [i0, i3] at this
  have h12 : i1 ≠ i2 := by
    intro h
    have := congrArg Fin.val h
    norm_num [i1, i2] at this
  have h13 : i1 ≠ i3 := by
    intro h
    have := congrArg Fin.val h
    norm_num [i1, i3] at this
  have h23 : i2 ≠ i3 := by
    intro h
    have := congrArg Fin.val h
    norm_num [i2, i3] at this
  have hsupp : ∀ i ∈ Finset.univ,
      i ∉ ({i0, i1, i2, i3} : Finset (Fin (2 * (N + 2) + 1))) →
      ccmActualHeadThirdJetKernelVector N i = 0 := by
    intro i _ hi
    have hi0 : i.val ≠ 0 := by
      intro hval
      apply hi
      have heq : i = i0 := Fin.ext (by simpa [i0] using hval)
      rw [heq]
      simp
    have hi1 : i.val ≠ 1 := by
      intro hval
      apply hi
      have heq : i = i1 := Fin.ext (by simpa [i1] using hval)
      rw [heq]
      simp
    have hi2 : i.val ≠ 2 := by
      intro hval
      apply hi
      have heq : i = i2 := Fin.ext (by simpa [i2] using hval)
      rw [heq]
      simp
    have hi3 : i.val ≠ 3 := by
      intro hval
      apply hi
      have heq : i = i3 := Fin.ext (by simpa [i3] using hval)
      rw [heq]
      simp
    simp [ccmActualHeadThirdJetKernelVector, hi0, hi1, hi2, hi3]
  have hsubset : ({i0, i1, i2, i3} : Finset (Fin (2 * (N + 2) + 1))) ⊆
      Finset.univ := by simp
  have sum_four (f : Fin (2 * (N + 2) + 1) → ℝ) :
      ∑ i ∈ ({i0, i1, i2, i3} : Finset (Fin (2 * (N + 2) + 1))), f i =
        f i0 + f i1 + f i2 + f i3 := by
    simpa [add_assoc] using (by
      simp [h01, h02, h03, h12, h13, h23] :
        ∑ i ∈ ({i0, i1, i2, i3} : Finset (Fin (2 * (N + 2) + 1))), f i =
          f i0 + (f i1 + (f i2 + f i3)))
  have hv0 : ccmActualHeadThirdJetKernelVector N i0 = 1 := by
    simp [ccmActualHeadThirdJetKernelVector, i0]
  have hv1 : ccmActualHeadThirdJetKernelVector N i1 = -3 := by
    simp [ccmActualHeadThirdJetKernelVector, i1]
  have hv2 : ccmActualHeadThirdJetKernelVector N i2 = 3 := by
    simp [ccmActualHeadThirdJetKernelVector, i2]
  have hv3 : ccmActualHeadThirdJetKernelVector N i3 = -1 := by
    simp [ccmActualHeadThirdJetKernelVector, i3]
  have hc0 : ccmPublishedCenteredClock (N + 2) i0 = (0 : ℝ) - (N + 2) := by
    simp [ccmPublishedCenteredClock, ccmPublishedCenteredMode, i0]
  have hc1 : ccmPublishedCenteredClock (N + 2) i1 = (1 : ℝ) - (N + 2) := by
    simp [ccmPublishedCenteredClock, ccmPublishedCenteredMode, i1]
  have hc2 : ccmPublishedCenteredClock (N + 2) i2 = (2 : ℝ) - (N + 2) := by
    simp [ccmPublishedCenteredClock, ccmPublishedCenteredMode, i2]
  have hc3 : ccmPublishedCenteredClock (N + 2) i3 = (3 : ℝ) - (N + 2) := by
    simp [ccmPublishedCenteredClock, ccmPublishedCenteredMode, i3]
  have hsum : ∑ i, ccmActualHeadThirdJetKernelVector N i = 0 := by
    rw [← Finset.sum_subset hsubset hsupp]
    rw [sum_four]
    rw [hv0, hv1, hv2, hv3]
    norm_num
  have hclock : ∑ i, ccmPublishedCenteredClock (N + 2) i *
      ccmActualHeadThirdJetKernelVector N i = 0 := by
    rw [← Finset.sum_subset hsubset (fun i hi hnot => by rw [hsupp i hi hnot]; ring)]
    rw [sum_four]
    rw [hc0, hc1, hc2, hc3, hv0, hv1, hv2, hv3]
    ring
  have hclockSq : ∑ i, ccmPublishedCenteredClock (N + 2) i ^ 2 *
      ccmActualHeadThirdJetKernelVector N i = 0 := by
    rw [← Finset.sum_subset hsubset (fun i hi hnot => by rw [hsupp i hi hnot]; ring)]
    rw [sum_four]
    rw [hc0, hc1, hc2, hc3, hv0, hv1, hv2, hv3]
    ring
  exact ⟨hsum, hclock, hclockSq⟩

theorem ccmActualHeadThirdJetKernelVector_ne_zero (N : ℕ) :
    ccmActualHeadThirdJetKernelVector N ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin (2 * (N + 2) + 1))
  norm_num [ccmActualHeadThirdJetKernelVector] at h0

theorem ccmActualHeadMatchedWallLightThirdJetConnection_kernelVector
    (S : Finset (Nat.Primes × ℕ)) (N : ℕ) :
    Matrix.mulVec (ccmActualHeadMatchedWallLightThirdJetConnection S (N + 2))
      (ccmActualHeadThirdJetKernelVector N) = 0 := by
  rcases ccmActualHeadThirdJetKernelVector_moments N with ⟨hsum, hclock, hclockSq⟩
  have hconstant : dotProduct ccmConstantBoundary
      (ccmActualHeadThirdJetKernelVector N) = 0 := by
    simpa [dotProduct, ccmConstantBoundary] using hsum
  have hclock' : ccmPublishedCenteredClock (N + 2) ⬝ᵥ
      ccmActualHeadThirdJetKernelVector N = 0 := by
    simpa [dotProduct] using hclock
  have hclockSq' : (fun i => ccmPublishedCenteredClock (N + 2) i ^ 2) ⬝ᵥ
      ccmActualHeadThirdJetKernelVector N = 0 := by
    simpa [dotProduct] using hclockSq
  rw [ccmActualHeadMatchedWallLightThirdJetConnection_eq_rate_smul,
    Matrix.smul_mulVec,
    ccmGuinandWeilPrimeEntryUniversalThirdJet_eq_outerProducts]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, hconstant, hclock', hclockSq', MulOpposite.op_zero]
  simp

/-- The entire image of a finite matched wall-light third-jet packet lies in the universal
three-moment clock span.  Hence source labels change only three scalar coefficients, never the
finite-head range geometry. -/
theorem ccmActualHeadMatchedWallLightThirdJetConnection_range_threeMoment
    (S : Finset (Nat.Primes × ℕ)) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) :
    ∃ a b c : ℝ,
      Matrix.mulVec (ccmActualHeadMatchedWallLightThirdJetConnection S N) v =
        a • (fun i => ccmPublishedCenteredClock N i ^ 2) +
          b • ccmPublishedCenteredClock N + c • ccmConstantBoundary := by
  let rate : ℝ := ∑ pe ∈ S,
    ccmActualHeadMatchedWallLightOrientedQuadraticJet pe.1 pe.2
  refine ⟨rate * (2 * Real.pi ^ 2) * (ccmConstantBoundary ⬝ᵥ v),
    rate * (2 * Real.pi ^ 2) * (ccmPublishedCenteredClock N ⬝ᵥ v),
    rate * ((2 * Real.pi ^ 2) * ((fun i => ccmPublishedCenteredClock N i ^ 2) ⬝ᵥ v) -
      3 * (ccmConstantBoundary ⬝ᵥ v)), ?_⟩
  rw [ccmActualHeadMatchedWallLightThirdJetConnection_eq_rate_smul,
    Matrix.smul_mulVec,
    ccmGuinandWeilPrimeEntryUniversalThirdJet_eq_outerProducts]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp
  ring

/-- Every positive packet of matched wall-light third jets has a nonzero exact kernel vector
on every canonical finite head. Thus local third-jet positivity cannot yield finite-head
coercivity; a surviving source-faithful producer must escape this three-moment null space. -/
theorem exists_ccmActualHeadMatchedWallLightThirdJetConnection_nonzero_kernel
    (S : Finset (Nat.Primes × ℕ)) (N : ℕ) :
    ∃ v : Fin (2 * (N + 2) + 1) → ℝ,
      v ≠ 0 ∧ (∑ i, v i = 0) ∧
      Matrix.mulVec (ccmActualHeadMatchedWallLightThirdJetConnection S (N + 2)) v = 0 := by
  refine ⟨ccmActualHeadThirdJetKernelVector N,
    ccmActualHeadThirdJetKernelVector_ne_zero N, ?_,
    ccmActualHeadMatchedWallLightThirdJetConnection_kernelVector S N⟩
  exact (ccmActualHeadThirdJetKernelVector_moments N).1

end

end RHTower
