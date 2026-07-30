import GaloisForLFunctions.RHTower.CanonicalProductPredicateSplit
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardyTransport

/-!
# True Xi Wiener--Hopf complement factorization

The complementary factor in `GammaSewnMobiusXiWardHardyTransport` is the
totalized pointwise quotient of the full Xi canonical product by its
strict-right factor. At a strict-right zero Lean assigns that quotient the
value zero, although the removable complementary factor is nonzero there.

This file constructs the genuine complement directly from the complementary
Xi divisor. It proves:

* an unconditional exact factorization into two entire canonical products;
* an unconditional entire complementary Xi source factor;
* exact divisor and analytic-multiplicity separation at strict-right zeros;
* strict disagreement with the totalized quotient at every strict-right zero;
* the sharp frontier law: the old totalized complementary source is entire if
  and only if the Riemann hypothesis holds.

Thus analytic use of the old factor is RH-equivalent. The new factor repairs
that continuation defect without assuming RH.
-/

open Complex Filter Set

namespace RHTower

noncomputable section

/-- Multiplicity copies in the complement of the strict-right Xi divisor. -/
abbrev XiRightComplementZeroCopy :=
  {q : XiZeroCopy // ¬ 0 < (I * xiSpectralPoint q).re}

/-- Genuine complementary Xi canonical product, defined from its divisor
rather than by totalized division. -/
def xiRightComplementCanonicalProduct : ℂ → ℂ :=
  canonicalProductE1IndexedComplement xiSpectralPoint
    (fun q => 0 < (I * xiSpectralPoint q).re)

theorem xiRightComplementCanonicalProduct_analytic :
    AnalyticOnNhd ℂ xiRightComplementCanonicalProduct Set.univ :=
  canonicalProductE1IndexedComplement_analytic
    xiSpectralPoint
    (fun q => 0 < (I * xiSpectralPoint q).re)
    xiSpectralPoint_ne_zero
    xiSpectralPoint_inv_sq_summable

/-- Exact infinite Xi divisor split into strict-right and complementary entire
canonical products. -/
theorem xiCanonicalProduct_eq_right_mul_trueComplement (z : ℂ) :
    xiCanonicalProduct z =
      xiRightCanonicalProduct z * xiRightComplementCanonicalProduct z := by
  simpa only [xiCanonicalProduct, xiRightCanonicalProduct,
    xiRightSpectralPoint, xiRightComplementCanonicalProduct,
    canonicalProductE1IndexedSelected] using!
    canonicalProductE1Indexed_eq_selected_mul_complement
      xiSpectralPoint
      (fun q => 0 < (I * xiSpectralPoint q).re)
      xiSpectralPoint_ne_zero
      xiSpectralPoint_inv_sq_summable
      z

/-- Complementary canonical factor does not vanish on strict-right divisor. -/
theorem xiRightComplementCanonicalProduct_ne_zero_at_right
    (q : XiRightZeroCopy) :
    xiRightComplementCanonicalProduct (xiRightSpectralPoint q) ≠ 0 := by
  apply canonicalProductE1IndexedComplement_ne_zero
    xiSpectralPoint
    (fun r => 0 < (I * xiSpectralPoint r).re)
    xiSpectralPoint_ne_zero
    xiSpectralPoint_inv_sq_summable
  intro r heq
  apply r.2
  rw [← heq]
  simpa only [xiRightSpectralPoint] using q.2

/-- Genuine entire complementary Xi source factor. -/
def xiRightComplementSourceFactor (z : ℂ) : ℂ :=
  xiHadamardQuotient z * xiRightComplementCanonicalProduct z

theorem xiRightComplementSourceFactor_analytic :
    AnalyticOnNhd ℂ xiRightComplementSourceFactor Set.univ :=
  xiHadamardQuotient_analytic.mul
    xiRightComplementCanonicalProduct_analytic

/-- Exact source-level Wiener--Hopf factorization with two entire factors. -/
theorem xiRightCanonicalProduct_mul_trueComplementSourceFactor
    (z : ℂ) :
    xiRightCanonicalProduct z * xiRightComplementSourceFactor z = XiC z := by
  have hsource := congrFun xiHadamardQuotient_mul_canonicalProduct z
  rw [Pi.mul_apply] at hsource
  calc
    xiRightCanonicalProduct z * xiRightComplementSourceFactor z =
        xiHadamardQuotient z *
          (xiRightCanonicalProduct z *
            xiRightComplementCanonicalProduct z) := by
      rw [xiRightComplementSourceFactor]
      ring
    _ = xiHadamardQuotient z * xiCanonicalProduct z := by
      rw [← xiCanonicalProduct_eq_right_mul_trueComplement z]
    _ = XiC z := hsource

/-- Genuine complementary source remains nonzero at every strict-right Xi
zero, hence absorbs none of its divisor multiplicity. -/
theorem xiRightComplementSourceFactor_ne_zero_at_right
    (q : XiRightZeroCopy) :
    xiRightComplementSourceFactor (xiRightSpectralPoint q) ≠ 0 :=
  mul_ne_zero
    (xiHadamardQuotient_ne_zero _)
    (xiRightComplementCanonicalProduct_ne_zero_at_right q)

/-! ## Exact failure of totalized division on the divisor -/

theorem xiNonrightCanonicalProduct_eq_zero_at_right
    (q : XiRightZeroCopy) :
    xiNonrightCanonicalProduct (xiRightSpectralPoint q) = 0 := by
  simp [xiNonrightCanonicalProduct, xiRightCanonicalProduct_eq_zero q]

theorem xiNonrightSourceFactor_eq_zero_at_right
    (q : XiRightZeroCopy) :
    xiNonrightSourceFactor (xiRightSpectralPoint q) = 0 := by
  rw [xiNonrightSourceFactor, xiNonrightCanonicalProduct_eq_zero_at_right q,
    mul_zero]

/-- At every strict-right Xi zero the old totalized quotient differs from the
genuine removable complement. -/
theorem xiNonrightCanonicalProduct_ne_trueComplement_at_right
    (q : XiRightZeroCopy) :
    xiNonrightCanonicalProduct (xiRightSpectralPoint q) ≠
      xiRightComplementCanonicalProduct (xiRightSpectralPoint q) := by
  rw [xiNonrightCanonicalProduct_eq_zero_at_right q]
  exact Ne.symm (xiRightComplementCanonicalProduct_ne_zero_at_right q)

/-- Source-level certificate of the same divisor defect. -/
theorem xiNonrightSourceFactor_ne_trueComplementSourceFactor_at_right
    (q : XiRightZeroCopy) :
    xiNonrightSourceFactor (xiRightSpectralPoint q) ≠
      xiRightComplementSourceFactor (xiRightSpectralPoint q) := by
  rw [xiNonrightSourceFactor_eq_zero_at_right q]
  exact Ne.symm (xiRightComplementSourceFactor_ne_zero_at_right q)

/-! ## RH-equivalent removability law for the old quotient -/

theorem isEmpty_xiRightZeroCopy_of_riemannHypothesis
    (hRH : RiemannHypothesis) : IsEmpty XiRightZeroCopy := by
  constructor
  intro q
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q.1
  have hpos := q.2
  rw [ht] at hpos
  simp at hpos

theorem xiRightCanonicalProduct_eq_one_of_riemannHypothesis
    (hRH : RiemannHypothesis) (z : ℂ) :
    xiRightCanonicalProduct z = 1 := by
  letI := isEmpty_xiRightZeroCopy_of_riemannHypothesis hRH
  simp [xiRightCanonicalProduct, canonicalProductE1Indexed]

theorem xiNonrightCanonicalProduct_eq_xiCanonicalProduct_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    xiNonrightCanonicalProduct = xiCanonicalProduct := by
  funext z
  rw [xiNonrightCanonicalProduct,
    xiRightCanonicalProduct_eq_one_of_riemannHypothesis hRH z, div_one]

theorem xiNonrightSourceFactor_eq_XiC_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    xiNonrightSourceFactor = XiC := by
  funext z
  have hsource := congrFun xiHadamardQuotient_mul_canonicalProduct z
  rw [Pi.mul_apply] at hsource
  rw [xiNonrightSourceFactor,
    xiNonrightCanonicalProduct_eq_xiCanonicalProduct_of_riemannHypothesis hRH]
  exact hsource

/-- Old and genuine complementary products agree near zero, where strict-right
factor is nonzero. -/
theorem xiNonrightCanonicalProduct_eventuallyEq_trueComplement :
    xiNonrightCanonicalProduct =ᶠ[nhds 0]
      xiRightComplementCanonicalProduct := by
  have hright :
      ∀ᶠ z in nhds (0 : ℂ), xiRightCanonicalProduct z ≠ 0 :=
    (xiRightCanonicalProduct_analytic 0 (Set.mem_univ _)).continuousAt.eventually_ne
      (by simp)
  filter_upwards [hright] with z hz
  rw [xiNonrightCanonicalProduct,
    xiCanonicalProduct_eq_right_mul_trueComplement z]
  field_simp [hz]

theorem xiNonrightSourceFactor_eventuallyEq_trueComplementSourceFactor :
    xiNonrightSourceFactor =ᶠ[nhds 0]
      xiRightComplementSourceFactor := by
  filter_upwards [xiNonrightCanonicalProduct_eventuallyEq_trueComplement] with z hz
  rw [xiNonrightSourceFactor, xiRightComplementSourceFactor, hz]

/-- Global analyticity of the old totalized complementary quotient forces RH.
Identity continuation from zero would otherwise contradict its wrong value on
an actual strict-right zero. -/
theorem riemannHypothesis_of_xiNonrightCanonicalProduct_analytic
    (hbad : AnalyticOnNhd ℂ xiNonrightCanonicalProduct Set.univ) :
    RiemannHypothesis := by
  have heq : xiNonrightCanonicalProduct =
      xiRightComplementCanonicalProduct :=
    hbad.eq_of_eventuallyEq
      xiRightComplementCanonicalProduct_analytic
      xiNonrightCanonicalProduct_eventuallyEq_trueComplement
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
  exact (xiNonrightCanonicalProduct_ne_trueComplement_at_right q)
    (congrFun heq (xiRightSpectralPoint q))

/-- **Canonical-product removability law.** The totalized complementary
quotient is entire exactly when RH holds. -/
theorem riemannHypothesis_iff_xiNonrightCanonicalProduct_analytic :
    RiemannHypothesis ↔
      AnalyticOnNhd ℂ xiNonrightCanonicalProduct Set.univ := by
  constructor
  · intro hRH
    rw [xiNonrightCanonicalProduct_eq_xiCanonicalProduct_of_riemannHypothesis hRH]
    exact xiCanonicalProduct_analytic
  · exact riemannHypothesis_of_xiNonrightCanonicalProduct_analytic

/-- Global analyticity of old totalized source factor also forces RH. -/
theorem riemannHypothesis_of_xiNonrightSourceFactor_analytic
    (hbad : AnalyticOnNhd ℂ xiNonrightSourceFactor Set.univ) :
    RiemannHypothesis := by
  have heq : xiNonrightSourceFactor =
      xiRightComplementSourceFactor :=
    hbad.eq_of_eventuallyEq
      xiRightComplementSourceFactor_analytic
      xiNonrightSourceFactor_eventuallyEq_trueComplementSourceFactor
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
  exact (xiNonrightSourceFactor_ne_trueComplementSourceFactor_at_right q)
    (congrFun heq (xiRightSpectralPoint q))

/-- **Source removability law.** The old totalized complementary Xi source is
entire exactly when RH holds. Its unconditional pointwise factorization alone
does not supply this analyticity. -/
theorem riemannHypothesis_iff_xiNonrightSourceFactor_analytic :
    RiemannHypothesis ↔
      AnalyticOnNhd ℂ xiNonrightSourceFactor Set.univ := by
  constructor
  · intro hRH
    rw [xiNonrightSourceFactor_eq_XiC_of_riemannHypothesis hRH]
    exact XiC_analytic
  · exact riemannHypothesis_of_xiNonrightSourceFactor_analytic

theorem xiNonrightSourceFactor_not_analytic_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ¬ AnalyticOnNhd ℂ xiNonrightSourceFactor Set.univ :=
  fun han => hRH (riemannHypothesis_of_xiNonrightSourceFactor_analytic han)

/-! ## Exact multiplicity separation -/

/-- Genuine complement is a unit at every strict-right Xi zero, so strict-right
canonical factor retains full Xi analytic multiplicity there. -/
theorem analyticOrderAt_XiC_eq_xiRightCanonicalProduct_at_right
    (q : XiRightZeroCopy) :
    analyticOrderAt XiC (xiRightSpectralPoint q) =
      analyticOrderAt xiRightCanonicalProduct (xiRightSpectralPoint q) := by
  have hfun :
      (fun z => xiRightCanonicalProduct z *
        xiRightComplementSourceFactor z) = XiC := by
    funext z
    exact xiRightCanonicalProduct_mul_trueComplementSourceFactor z
  have hright :=
    xiRightCanonicalProduct_analytic
      (xiRightSpectralPoint q) (Set.mem_univ _)
  have hcomplement :=
    xiRightComplementSourceFactor_analytic
      (xiRightSpectralPoint q) (Set.mem_univ _)
  have hord :
      analyticOrderAt
          (fun z => xiRightCanonicalProduct z *
            xiRightComplementSourceFactor z)
          (xiRightSpectralPoint q) =
        analyticOrderAt xiRightCanonicalProduct (xiRightSpectralPoint q) +
          analyticOrderAt xiRightComplementSourceFactor
            (xiRightSpectralPoint q) := by
    simpa only [Pi.mul_apply] using!
      analyticOrderAt_mul hright hcomplement
  rw [← hfun, hord,
    hcomplement.analyticOrderAt_eq_zero.mpr
      (xiRightComplementSourceFactor_ne_zero_at_right q),
    add_zero]

end

end RHTower
