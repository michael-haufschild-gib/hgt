import GaloisForLFunctions.RHTower.XiCosineShiftDefectLimit
import GaloisForLFunctions.RHTower.XiSliceEventualPositivityFiniteOffLine

/-!
# Bounded cosine defects are "finitely many off-line zeros"

For `h > 0` let `A^h = cos(hD)Ξ = (Ξ(z+ih) + Ξ(z−ih))/2`, and call its non-real zeros, counted with
multiplicity, its defects.

**Theorem** (`cosineDefectsBounded_iff_finiteOffLine`).  The defect counts of `A^h`, `h > 0`, are
finite and bounded independently of `h` if and only if only finitely many zeros of `ξ` lie off the
critical line.

* With finitely many off-line zeros, the deep-zero budget bounds the defects of every level by
  twice their number (`CosineDefectBudget.finite_nonreal_zeros_cosShiftXi`).
* With infinitely many, the off-line zeros of `Ξ` are infinitely many distinct points (copies of
  bounded spectral norm are finite), and Hurwitz's theorem (`eventually_exists_nonreal_zeros_ge`)
  gives levels with arbitrarily many defects as `h → 0`.

So the cosine ladder reads the three strengths of the zero-location statements through its defect
counts: no defects at any level is RH (`riemannHypothesis_iff_eventually_cosShiftXi_real`),
uniformly bounded defects is FOL (this file), and finitely many defects at every level is, under LH,
"zeros approach the line" (`cosShiftXi_finite_nonreal_iff_zerosApproachLine`).
-/

open Complex Set Filter Topology

namespace RHTower.BacklundConverse

open RHTower.LindelofSparse RHTower.CosineSparseCluster RHTower.DeBruijn RHTower.CosineDefectBudget
open RHTower.CosineDefectLimit GaloisForLFunctions.HTGeometry

noncomputable section

/-- The defect counts of the cosine family are finite and bounded uniformly in the depth. -/
def CosineDefectsBounded : Prop :=
  ∃ M : ℕ, ∀ h : ℝ, 0 < h → ∃ hZ : {z : ℂ | cosShiftXi h z = 0 ∧ z.im ≠ 0}.Finite,
    ∑ z ∈ hZ.toFinset, zeroMult (cosShiftXi h) z ≤ M

/-- **Finitely many off-line zeros bound every cosine defect count.** -/
theorem cosineDefectsBounded_of_finiteOffLine (hF : FiniteOffLine) : CosineDefectsBounded := by
  classical
  refine ⟨2 * hF.toFinset.card, fun h hh => ?_⟩
  have hsub : deepCopies h ⊆ {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0} := fun q hq => by
    have hq' : h < (xiSpectralPoint q).im := hq
    show (xiSpectralPoint q).im ≠ 0
    linarith
  have hS : (deepCopies h).Finite := hF.subset hsub
  obtain ⟨hZ, hsum⟩ := finite_nonreal_zeros_cosShiftXi hS
  refine ⟨hZ, hsum.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card fun q hq => ?_))⟩
  rw [Set.Finite.mem_toFinset] at hq ⊢
  exact hsub hq

/-- Infinitely many off-line copies sit over infinitely many distinct off-line zeros of `Ξ`. -/
theorem infinite_offLine_XiC_zeros (hinf : ¬ FiniteOffLine) :
    {e : ℂ | XiC e = 0 ∧ e.im ≠ 0}.Infinite := by
  intro hfin
  apply hinf
  obtain ⟨M, hM⟩ := (hfin.image fun e => ‖e‖).bddAbove
  refine (xiZeroBall (⌈M⌉₊)).finite_toSet.subset fun q hq => ?_
  simp only [Finset.mem_coe, mem_xiZeroBall]
  have hz : XiC (xiSpectralPoint q) = 0 := (XiC_eq_zero_iff_exists_xiZeroCopy _).mpr ⟨q, rfl⟩
  exact (hM ⟨xiSpectralPoint q, ⟨hz, hq⟩, rfl⟩).trans (Nat.le_ceil M)

/-- **Uniformly bounded cosine defects leave finitely many off-line zeros.** -/
theorem finiteOffLine_of_cosineDefectsBounded (hB : CosineDefectsBounded) : FiniteOffLine := by
  classical
  obtain ⟨M, hM⟩ := hB
  by_contra hinf
  obtain ⟨E, hEsub, hEcard⟩ := (infinite_offLine_XiC_zeros hinf).exists_subset_card_eq (M + 1)
  have hEne : ∀ e ∈ E, e.im ≠ 0 := fun e he => (hEsub he).2
  have hEmult : M + 1 ≤ ∑ e ∈ E, zeroMult XiC e := by
    calc M + 1 = ∑ _e ∈ E, 1 := by simp [hEcard]
      _ ≤ ∑ e ∈ E, zeroMult XiC e := Finset.sum_le_sum fun e he =>
          one_le_zeroMult_of_eq_zero differentiable_XiC'
            WindowNonrealBudget.analyticOrderAt_XiC_ne_top (hEsub he).1
  -- a small positive depth where Hurwitz applies
  obtain ⟨h, hP, hh⟩ := (((eventually_exists_nonreal_zeros_ge E hEne).filter_mono
    nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  obtain ⟨F, hF, hsumF⟩ := hP
  obtain ⟨hZ, hbound⟩ := hM h hh
  have hFsub : F ⊆ hZ.toFinset := fun z hz => by
    rw [Set.Finite.mem_toFinset]
    exact ⟨(hF z hz).1, (hF z hz).2⟩
  have hle := Finset.sum_le_sum_of_subset (f := fun z => zeroMult (cosShiftXi h) z) hFsub
  omega

/-- **Uniformly bounded cosine defects are exactly finitely many off-line zeros.** -/
theorem cosineDefectsBounded_iff_finiteOffLine : CosineDefectsBounded ↔ FiniteOffLine :=
  ⟨finiteOffLine_of_cosineDefectsBounded, cosineDefectsBounded_of_finiteOffLine⟩

/-- **Uniformly bounded cosine defects are uniformly bounded slice failures.**  The cosine family
has bounded defects iff every slice coefficient is nonnegative at all large heights. -/
theorem cosineDefectsBounded_iff_eventualSlicePositivity :
    CosineDefectsBounded ↔ EventualSlicePositivity :=
  cosineDefectsBounded_iff_finiteOffLine.trans eventualSlicePositivity_iff_finiteOffLine.symm

end

end RHTower.BacklundConverse
