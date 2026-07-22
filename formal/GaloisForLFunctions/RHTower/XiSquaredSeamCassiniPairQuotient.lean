import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniSource

/-!
# Exact functional-equation quotient of Xi zeros by the Cassini source

The map `alpha ↦ 1 + alpha²` identifies exactly the two functional-equation partners
`alpha` and `-alpha`.  This module chooses one partner by a lexicographic half-plane, preserves
analytic multiplicity, and constructs the resulting equivalences on zero copies.  Consequently
every reflection-invariant nonnegative Xi divisor sum is exactly twice the corresponding Cassini
source divisor sum, with no summability hypothesis.
-/

open Complex Set
open scoped ENNReal

namespace RHTower

noncomputable section

def xiSpectralLexPositive (z : ℂ) : Prop :=
  0 < z.re ∨ (z.re = 0 ∧ 0 < z.im)

theorem xiSpectralLexPositive_or_neg {z : ℂ} (hz : z ≠ 0) :
    xiSpectralLexPositive z ∨ xiSpectralLexPositive (-z) := by
  rcases lt_trichotomy z.re 0 with hre | hre | hre
  · right
    left
    simp only [neg_re]
    linarith
  · have him : z.im ≠ 0 := by
      intro him
      apply hz
      apply Complex.ext
      · exact hre
      · exact him
    rcases lt_or_gt_of_ne him with himneg | himpos
    · right
      right
      constructor
      · simp [hre]
      · simp only [neg_im]
        linarith
    · left
      exact Or.inr ⟨hre, himpos⟩
  · left
    exact Or.inl hre

theorem not_xiSpectralLexPositive_neg_of_positive {z : ℂ}
    (hz : xiSpectralLexPositive z) :
    ¬ xiSpectralLexPositive (-z) := by
  intro hneg
  rcases hz with hre | ⟨hre, him⟩
  · rcases hneg with hnegRe | ⟨hnegRe, _⟩
    · simp only [neg_re] at hnegRe
      linarith
    · simp only [neg_re] at hnegRe
      linarith
  · rcases hneg with hnegRe | ⟨_, hnegIm⟩
    · simp only [neg_re, hre, neg_zero] at hnegRe
      linarith
    · simp only [neg_im] at hnegIm
      linarith

abbrev XiSquaredSeamPositiveSupport :=
  {rho : XiDivisorSupport // xiSpectralLexPositive (xiSpectralPointSupport rho)}

abbrev XiSquaredSeamCassiniZeroSupport :=
  {u : ℂ // xiSquaredSeamCassiniSource u = 0}

def xiSquaredSeamPositiveSupportToCassiniZeroSupport
    (rho : XiSquaredSeamPositiveSupport) : XiSquaredSeamCassiniZeroSupport :=
  ⟨xiSquaredSeamCassiniZeroSupport rho.1,
    xiSquaredSeamCassiniSource_zero_support rho.1⟩

theorem xiSquaredSeamPositiveSupportToCassiniZeroSupport_injective :
    Function.Injective xiSquaredSeamPositiveSupportToCassiniZeroSupport := by
  intro rho tau h
  apply Subtype.ext
  apply xiSpectralPointSupport_injective
  have hcoord : xiSquaredSeamCassiniZeroSupport rho.1 =
      xiSquaredSeamCassiniZeroSupport tau.1 := congrArg Subtype.val h
  have hsq : xiSpectralPointSupport rho.1 ^ 2 =
      xiSpectralPointSupport tau.1 ^ 2 := by
    simpa only [xiSquaredSeamCassiniZeroSupport] using add_left_cancel hcoord
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | hneg
  · exact heq
  · exfalso
    apply not_xiSpectralLexPositive_neg_of_positive tau.2
    rw [← hneg]
    exact rho.2

theorem xiSquaredSeamPositiveSupportToCassiniZeroSupport_surjective :
    Function.Surjective xiSquaredSeamPositiveSupportToCassiniZeroSupport := by
  intro u
  obtain ⟨q, hq⟩ :=
    (xiSquaredSeamCassiniSource_eq_zero_iff_exists_zeroCopy u.1).mp u.2
  have hsign := xiSpectralLexPositive_or_neg (xiSpectralPoint_ne_zero q)
  rcases hsign with hpos | hneg
  · refine ⟨⟨q.1, ?_⟩, ?_⟩
    · simpa only [xiSpectralPoint_eq_support] using hpos
    · apply Subtype.ext
      simpa only [xiSquaredSeamPositiveSupportToCassiniZeroSupport,
        xiSquaredSeamCassiniZero_eq_support] using hq
  · refine ⟨⟨xiZeroReflectEquiv q.1, ?_⟩, ?_⟩
    · rw [xiSpectralPointSupport_reflect]
      simpa only [xiSpectralPoint_eq_support] using hneg
    · apply Subtype.ext
      change xiSquaredSeamCassiniZeroSupport (xiZeroReflectEquiv q.1) = u.1
      rw [xiSquaredSeamCassiniZeroSupport, xiSpectralPointSupport_reflect,
        neg_sq]
      simpa only [xiSquaredSeamCassiniZero_eq_support] using hq

def xiSquaredSeamPositiveSupportEquivCassiniZeroSupport :
    XiSquaredSeamPositiveSupport ≃ XiSquaredSeamCassiniZeroSupport :=
  Equiv.ofBijective xiSquaredSeamPositiveSupportToCassiniZeroSupport
    ⟨xiSquaredSeamPositiveSupportToCassiniZeroSupport_injective,
      xiSquaredSeamPositiveSupportToCassiniZeroSupport_surjective⟩

abbrev XiSquaredSeamPositiveZeroCopy :=
  Σ rho : XiSquaredSeamPositiveSupport,
    Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho.1 : ℂ)))

abbrev XiSquaredSeamCassiniZeroCopy :=
  Σ u : XiSquaredSeamCassiniZeroSupport,
    Fin ((analyticOrderAt xiSquaredSeamCassiniSource (u.1 : ℂ)).toNat)

def xiSquaredSeamPositiveZeroCopyEquivCassiniZeroCopy :
    XiSquaredSeamPositiveZeroCopy ≃ XiSquaredSeamCassiniZeroCopy :=
  Equiv.sigmaCongr xiSquaredSeamPositiveSupportEquivCassiniZeroSupport (fun rho =>
    Equiv.cast (by
      change Fin (Int.toNat
          ((MeromorphicOn.divisor xi Set.univ) (rho.1.1 : ℂ))) =
        Fin ((analyticOrderAt xiSquaredSeamCassiniSource
          (xiSquaredSeamCassiniZeroSupport rho.1)).toNat)
      rw [analyticOrderAt_xiSquaredSeamCassiniSource_cassiniZeroSupport_eq_multiplicity]
      simp))

abbrev XiSquaredSeamPositiveZeroCopySubtype :=
  {q : XiZeroCopy // xiSpectralLexPositive (xiSpectralPointSupport q.1)}

def xiSquaredSeamPositiveZeroCopySubtypeEquiv :
    XiSquaredSeamPositiveZeroCopySubtype ≃ XiSquaredSeamPositiveZeroCopy :=
  Equiv.subtypeSigmaEquiv
    (fun rho : XiDivisorSupport =>
      Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ))))
    (fun rho => xiSpectralLexPositive (xiSpectralPointSupport rho))

def xiSquaredSeamPairToZeroCopy
    (bq : Bool × XiSquaredSeamPositiveZeroCopySubtype) : XiZeroCopy :=
  if bq.1 then xiZeroCopyReflectEquiv.symm bq.2.1 else bq.2.1

theorem xiSquaredSeamPairToZeroCopy_injective :
    Function.Injective xiSquaredSeamPairToZeroCopy := by
  rintro ⟨b, p⟩ ⟨c, q⟩ h
  cases b <;> cases c
  · simp only [xiSquaredSeamPairToZeroCopy, Bool.false_eq_true, if_false] at h
    congr
    exact Subtype.ext h
  · simp only [xiSquaredSeamPairToZeroCopy, Bool.false_eq_true, if_false,
      if_true] at h
    have he : xiZeroCopyReflectEquiv p.1 = q.1 := by
      rw [h]
      exact xiZeroCopyReflectEquiv.apply_symm_apply q.1
    have hpoint := congrArg xiSpectralPoint he
    rw [xiSpectralPoint_reflect, xiSpectralPoint_eq_support,
      xiSpectralPoint_eq_support] at hpoint
    exfalso
    exact (not_xiSpectralLexPositive_neg_of_positive p.2) (by
      rw [hpoint]
      exact q.2)
  · simp only [xiSquaredSeamPairToZeroCopy, if_true,
      Bool.false_eq_true, if_false] at h
    have he : p.1 = xiZeroCopyReflectEquiv q.1 := by
      rw [← h]
      exact (xiZeroCopyReflectEquiv.apply_symm_apply p.1).symm
    have hpoint := congrArg xiSpectralPoint he
    rw [xiSpectralPoint_reflect, xiSpectralPoint_eq_support,
      xiSpectralPoint_eq_support] at hpoint
    exfalso
    exact (not_xiSpectralLexPositive_neg_of_positive q.2) (by
      rw [← hpoint]
      exact p.2)
  · simp only [xiSquaredSeamPairToZeroCopy, if_true] at h
    congr
    exact Subtype.ext (xiZeroCopyReflectEquiv.symm.injective h)

theorem xiSquaredSeamPairToZeroCopy_surjective :
    Function.Surjective xiSquaredSeamPairToZeroCopy := by
  intro q
  rcases xiSpectralLexPositive_or_neg (xiSpectralPoint_ne_zero q) with hpos | hneg
  · refine ⟨⟨false, ⟨q, ?_⟩⟩, ?_⟩
    · simpa only [xiSpectralPoint_eq_support] using hpos
    · rfl
  · refine ⟨⟨true, ⟨xiZeroCopyReflectEquiv q, ?_⟩⟩, ?_⟩
    · rw [← xiSpectralPoint_eq_support, xiSpectralPoint_reflect]
      exact hneg
    · exact xiZeroCopyReflectEquiv.symm_apply_apply q

def xiSquaredSeamPairEquivZeroCopy :
    Bool × XiSquaredSeamPositiveZeroCopySubtype ≃ XiZeroCopy :=
  Equiv.ofBijective xiSquaredSeamPairToZeroCopy
    ⟨xiSquaredSeamPairToZeroCopy_injective,
      xiSquaredSeamPairToZeroCopy_surjective⟩

def xiSquaredSeamPositiveZeroCopySubtypeEquivCassiniZeroCopy :
    XiSquaredSeamPositiveZeroCopySubtype ≃ XiSquaredSeamCassiniZeroCopy :=
  xiSquaredSeamPositiveZeroCopySubtypeEquiv.trans
    xiSquaredSeamPositiveZeroCopyEquivCassiniZeroCopy

theorem xiSquaredSeamCassiniZero_reflect (q : XiZeroCopy) :
    xiSquaredSeamCassiniZero (xiZeroCopyReflectEquiv q) =
      xiSquaredSeamCassiniZero q := by
  rw [xiSquaredSeamCassiniZero, xiSquaredSeamCassiniZero,
    xiSpectralPoint_reflect, neg_sq]

theorem xiSquaredSeamCassiniZero_reflect_symm (q : XiZeroCopy) :
    xiSquaredSeamCassiniZero (xiZeroCopyReflectEquiv.symm q) =
      xiSquaredSeamCassiniZero q := by
  have h := xiSquaredSeamCassiniZero_reflect
    (xiZeroCopyReflectEquiv.symm q)
  rw [xiZeroCopyReflectEquiv.apply_symm_apply] at h
  exact h.symm

theorem xiSquaredSeam_tsum_eq_two_mul_positive
    (g : XiZeroCopy → ℝ≥0∞)
    (hreflect : ∀ q, g (xiZeroCopyReflectEquiv.symm q) = g q) :
    ∑' q, g q = 2 * ∑' p : XiSquaredSeamPositiveZeroCopySubtype, g p.1 := by
  rw [← xiSquaredSeamPairEquivZeroCopy.tsum_eq g,
    ENNReal.tsum_prod', tsum_bool]
  simp only [xiSquaredSeamPairEquivZeroCopy,
    Equiv.ofBijective_apply, xiSquaredSeamPairToZeroCopy, if_true]
  rw [show (∑' p : XiSquaredSeamPositiveZeroCopySubtype,
      g (xiZeroCopyReflectEquiv.symm p.1)) =
        ∑' p : XiSquaredSeamPositiveZeroCopySubtype, g p.1 by
        congr 1
        funext p
        exact hreflect p.1]
  simp [two_mul]

theorem xiSquaredSeamPositive_tsum_eq_cassiniZeroCopy
    (F : ℂ → ℝ≥0∞) :
    ∑' p : XiSquaredSeamPositiveZeroCopySubtype,
        F (xiSquaredSeamCassiniZero p.1) =
      ∑' c : XiSquaredSeamCassiniZeroCopy, F c.1.1 := by
  rw [← xiSquaredSeamPositiveZeroCopySubtypeEquivCassiniZeroCopy.tsum_eq
    (fun c => F c.1.1)]
  congr 1

theorem xiSquaredSeam_tsum_cassiniZero_eq_two_mul_sourceZeroCopy
    (F : ℂ → ℝ≥0∞) :
    ∑' q : XiZeroCopy, F (xiSquaredSeamCassiniZero q) =
      2 * ∑' c : XiSquaredSeamCassiniZeroCopy, F c.1.1 := by
  rw [xiSquaredSeam_tsum_eq_two_mul_positive
    (fun q => F (xiSquaredSeamCassiniZero q)) (fun q => by
      change F (xiSquaredSeamCassiniZero (xiZeroCopyReflectEquiv.symm q)) =
        F (xiSquaredSeamCassiniZero q)
      rw [xiSquaredSeamCassiniZero_reflect_symm]),
    xiSquaredSeamPositive_tsum_eq_cassiniZeroCopy]

/-- Radial Jensen atom indexed by one multiplicity copy of a Cassini-source zero. -/
def xiSquaredSeamCassiniSourcePowerSixtyFourJensenKernel
    (c : XiSquaredSeamCassiniZeroCopy) (r : ℝ) : ℝ≥0∞ :=
  if ‖(c.1.1 : ℂ)‖ ≤ r then
    ENNReal.ofReal (Real.log (r / ‖(c.1.1 : ℂ)‖) / r ^ 65)
  else 0

/-- Exact two-sheet quotient of the full Xi Jensen profile by functional-equation reflection. -/
theorem xiSquaredSeamPowerSixtyFourJensenKernel_tsum_eq_two_mul_source_tsum
    (r : ℝ) :
    ∑' q : XiZeroCopy, xiSquaredSeamPowerSixtyFourJensenKernel q r =
      2 * ∑' c : XiSquaredSeamCassiniZeroCopy,
        xiSquaredSeamCassiniSourcePowerSixtyFourJensenKernel c r := by
  simpa only [xiSquaredSeamPowerSixtyFourJensenKernel,
    xiSquaredSeamCassiniSourcePowerSixtyFourJensenKernel,
    norm_xiSquaredSeamCassiniZero] using
    xiSquaredSeam_tsum_cassiniZero_eq_two_mul_sourceZeroCopy
      (fun u => if ‖u‖ ≤ r then
        ENNReal.ofReal (Real.log (r / ‖u‖) / r ^ 65) else 0)

end

end RHTower
