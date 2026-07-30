import GaloisForLFunctions.HTGeometry.GammaPoleReciprocalBellOrder
import GaloisForLFunctions.HTGeometry.GammaPoleScaleDerivativeLaurentFreeness
import GaloisForLFunctions.HTGeometry.GammaInversePoleBranchScaleFreeness
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Derivative-weight grading of reciprocal-Bell compression

Reciprocal-Bell compression already turns every particle-homogeneous inverse-
section jet packet into one power of the inverse section times a covariant
polynomial.  To compare different particle sectors in native coordinates one
also has to know what happens to derivative weight.

This file proves that the complete Bell automorphism, its inverse, the sign
reflection, and simple-zero dehomogenization preserve that weight exactly.
After taking the top ordinary-homogeneous covariant component and fixing the
universal first residue, the remaining boundary polynomial has the residual
weight `W - E`, where `W` is source derivative weight and `E` is its top
covariant degree.  At fixed native pole order this residual grading separates
distinct particle sectors that the first-residue specialization could
otherwise appear to identify.

Joint factorial-scale/covariant-residue value reflection then makes this
separation analytic.  Every constant-coefficient source is canonically split
by particle degree and derivative weight; its exact tower cutoff is the
maximum `D+E` over the nonzero sectors, attained on arbitrarily remote Gamma
poles.  Consequently the arbitrary-source at-most-simple packets are exactly
the affine polynomials `a + b * X₀` in undifferentiated Gamma.
-/

open Filter Topology Polynomial LaurentPolynomial MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- Logarithmic/covariant jet coordinate `j` has derivative weight `j+1`. -/
def bellJetWeight (n : ℕ) : Fin n → ℕ := fun i => (i : ℕ) + 1

/-- The complete Bell polynomial `B_k` is derivative-weight homogeneous of
weight `k`. -/
theorem bellCore_isWeightedHomogeneous (k : ℕ) :
    (bellCore k).IsWeightedHomogeneous (bellJetWeight k) k := by
  induction k with
  | zero =>
      simpa [bellCore_zero] using
        (MvPolynomial.isWeightedHomogeneous_one ℂ (bellJetWeight 0))
  | succ k ih =>
      rw [bellCore_succ]
      apply MvPolynomial.IsWeightedHomogeneous.add
      · have hrename : (MvPolynomial.rename Fin.castSucc (bellCore k)).IsWeightedHomogeneous
            (bellJetWeight (k + 1)) k :=
          rename_isWeightedHomogeneous ih Fin.castSucc (by
            intro i
            simp [bellJetWeight])
        have hX := MvPolynomial.isWeightedHomogeneous_X ℂ (bellJetWeight (k + 1))
          (0 : Fin (k + 1))
        simpa [bellJetWeight, Nat.add_comm] using hX.mul hrename
      · apply MvPolynomial.IsWeightedHomogeneous.sum
        intro j hj
        have hp : (pderiv j (bellCore k)).IsWeightedHomogeneous
            (bellJetWeight k) (k - ((j : ℕ) + 1)) :=
          ih.pderiv (by
            change (k - ((j : ℕ) + 1)) + ((j : ℕ) + 1) = k
            exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr j.isLt))
        have hrename :
            (MvPolynomial.rename Fin.castSucc (pderiv j (bellCore k))).IsWeightedHomogeneous
              (bellJetWeight (k + 1)) (k - ((j : ℕ) + 1)) :=
          rename_isWeightedHomogeneous hp Fin.castSucc (by
            intro i
            simp [bellJetWeight])
        have hX := MvPolynomial.isWeightedHomogeneous_X ℂ (bellJetWeight (k + 1)) j.succ
        convert hrename.mul hX using 1
        simp [bellJetWeight]
        omega

/-- Substitution by generators of their matching weights preserves weighted
homogeneity. -/
theorem isWeightedHomogeneous_eval₂_of_weighted_generators
    {σ τ : Type*} {wσ : σ → ℕ} {wτ : τ → ℕ} {W : ℕ}
    {P : MvPolynomial σ ℂ} (hP : P.IsWeightedHomogeneous wσ W)
    (g : σ → MvPolynomial τ ℂ)
    (hg : ∀ i, (g i).IsWeightedHomogeneous wτ (wσ i)) :
    (MvPolynomial.eval₂ MvPolynomial.C g P).IsWeightedHomogeneous wτ W := by
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro m hm
  rw [← zero_add W]
  apply (MvPolynomial.isWeightedHomogeneous_C wτ (P.coeff m)).mul
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod m.support
    (fun i => g i ^ m i) (fun i => wσ i * m i)
      (fun i _ => by simpa [Nat.mul_comm] using (hg i).pow (m i))
  convert hprod using 1
  have hweight := hP (MvPolynomial.mem_support_iff.mp hm)
  change (∑ i ∈ m.support, m i * wσ i) = W at hweight
  calc
    W = ∑ i ∈ m.support, m i * wσ i := hweight.symm
    _ = ∑ i ∈ m.support, wσ i * m i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.mul_comm]

/-- A weight-preserving polynomial substitution commutes with projection to
every weighted-homogeneous component. -/
theorem eval₂_weightedHomogeneousComponent
    {σ τ : Type*} (wσ : σ → ℕ) (wτ : τ → ℕ)
    (g : σ → MvPolynomial τ ℂ)
    (hg : ∀ i, (g i).IsWeightedHomogeneous wτ (wσ i))
    (W : ℕ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.weightedHomogeneousComponent wτ W
        (MvPolynomial.eval₂ MvPolynomial.C g P) =
      MvPolynomial.eval₂ MvPolynomial.C g
        (MvPolynomial.weightedHomogeneousComponent wσ W P) := by
  classical
  let φ : MvPolynomial σ ℂ →+* MvPolynomial τ ℂ :=
    MvPolynomial.eval₂Hom MvPolynomial.C g
  change MvPolynomial.weightedHomogeneousComponent wτ W (φ P) =
    φ (MvPolynomial.weightedHomogeneousComponent wσ W P)
  rw [← P.support_sum_monomial_coeff]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hsrc : (MvPolynomial.monomial m (P.coeff m)).IsWeightedHomogeneous
      wσ (Finsupp.weight wσ m) :=
    MvPolynomial.isWeightedHomogeneous_monomial wσ m (P.coeff m) rfl
  have himg : (MvPolynomial.eval₂ MvPolynomial.C g
      (MvPolynomial.monomial m (P.coeff m))).IsWeightedHomogeneous
        wτ (Finsupp.weight wσ m) :=
    isWeightedHomogeneous_eval₂_of_weighted_generators hsrc g hg
  by_cases hW : Finsupp.weight wσ m = W
  · change MvPolynomial.weightedHomogeneousComponent wτ W
        (MvPolynomial.eval₂ MvPolynomial.C g
          (MvPolynomial.monomial m (P.coeff m))) =
      MvPolynomial.eval₂ MvPolynomial.C g
        (MvPolynomial.weightedHomogeneousComponent wσ W
          (MvPolynomial.monomial m (P.coeff m)))
    rw [MvPolynomial.weightedHomogeneousComponent_of_mem himg,
      MvPolynomial.weightedHomogeneousComponent_of_mem hsrc,
      if_pos hW.symm, if_pos hW.symm]
  · change MvPolynomial.weightedHomogeneousComponent wτ W
        (MvPolynomial.eval₂ MvPolynomial.C g
          (MvPolynomial.monomial m (P.coeff m))) =
      MvPolynomial.eval₂ MvPolynomial.C g
        (MvPolynomial.weightedHomogeneousComponent wσ W
          (MvPolynomial.monomial m (P.coeff m)))
    have hW' : ¬ W = Finsupp.weight wσ m := fun h => hW h.symm
    rw [MvPolynomial.weightedHomogeneousComponent_of_mem himg,
      MvPolynomial.weightedHomogeneousComponent_of_mem hsrc,
      if_neg hW', if_neg hW']
    simp

theorem bellAt_isWeightedHomogeneous (n : ℕ) (j : Fin (n + 1)) :
    (bellAt n ((j : ℕ) + 1) j.isLt).IsWeightedHomogeneous
      (bellJetWeight (n + 1)) ((j : ℕ) + 1) := by
  rw [bellAt]
  exact rename_isWeightedHomogeneous (bellCore_isWeightedHomogeneous ((j : ℕ) + 1))
    (Fin.castLE j.isLt) (by intro i; simp [bellJetWeight])

/-- Complete-Bell substitution preserves derivative weight. -/
theorem bellCoefficientMap_preserves_weight
    {n W : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 1)) W) :
    (bellCoefficientMap n P).IsWeightedHomogeneous (bellJetWeight (n + 1)) W := by
  exact isWeightedHomogeneous_eval₂_of_weighted_generators hP _
    (bellAt_isWeightedHomogeneous n)

theorem bellCoefficientMap_weightedHomogeneousComponent
    (n W : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.weightedHomogeneousComponent (bellJetWeight (n + 1)) W
        (bellCoefficientMap n P) =
      bellCoefficientMap n
        (MvPolynomial.weightedHomogeneousComponent (bellJetWeight (n + 1)) W P) := by
  exact eval₂_weightedHomogeneousComponent _ _ _
    (bellAt_isWeightedHomogeneous n) W P

/-- The polynomial inverse Bell transformation preserves the same derivative
weight, not merely nonzeroness. -/
theorem bellCoefficientEquiv_symm_preserves_weight
    {n W : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 1)) W) :
    ((HTGeometry.bellCoefficientEquiv n).symm P).IsWeightedHomogeneous
      (bellJetWeight (n + 1)) W := by
  let Q := (HTGeometry.bellCoefficientEquiv n).symm P
  intro m hm
  let V := Finsupp.weight (bellJetWeight (n + 1)) m
  have hQV : MvPolynomial.weightedHomogeneousComponent
      (bellJetWeight (n + 1)) V Q ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (MvPolynomial.coeff m) hzero
    rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos rfl] at hcoeff
    exact hm hcoeff
  have hmapV : bellCoefficientMap n
      (MvPolynomial.weightedHomogeneousComponent
        (bellJetWeight (n + 1)) V Q) ≠ 0 :=
    (bellCoefficientMap_injective n).ne hQV
  have hcomponent : MvPolynomial.weightedHomogeneousComponent
      (bellJetWeight (n + 1)) V P ≠ 0 := by
    have hPQ : bellCoefficientMap n Q = P := by
      change HTGeometry.bellCoefficientEquiv n Q = P
      exact (HTGeometry.bellCoefficientEquiv n).apply_symm_apply P
    rw [← hPQ]
    rw [bellCoefficientMap_weightedHomogeneousComponent]
    exact hmapV
  by_contra hVW
  apply hcomponent
  rw [MvPolynomial.weightedHomogeneousComponent_of_mem hP, if_neg hVW]

/-- Ordinary inverse-jet coordinate `j` has derivative weight `j`. -/
def inverseJetDerivativeWeight (n : ℕ) : Fin (n + 2) → ℕ := fun j => (j : ℕ)

theorem simpleZeroDehomogenize_preserves_derivativeWeight
    {n W : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P.IsWeightedHomogeneous (inverseJetDerivativeWeight n) W) :
    (HTGeometry.simpleZeroDehomogenize (n + 1) P).IsWeightedHomogeneous
      (bellJetWeight (n + 1)) W := by
  apply isWeightedHomogeneous_eval₂_of_weighted_generators hP
  intro j
  induction j using Fin.cases with
  | zero =>
      simpa [HTGeometry.simpleZeroDehomogenize,
        HTGeometry.simpleZeroBoundaryResidue, inverseJetDerivativeWeight] using
        (MvPolynomial.isWeightedHomogeneous_one ℂ (bellJetWeight (n + 1)))
  | succ j =>
      simpa [HTGeometry.simpleZeroDehomogenize,
        HTGeometry.simpleZeroBoundaryResidue, inverseJetDerivativeWeight,
        bellJetWeight] using
        (MvPolynomial.isWeightedHomogeneous_X ℂ (bellJetWeight (n + 1)) j)

theorem negativeRawJetMap_preserves_weight
    {n W : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 1)) W) :
    (negativeRawJetMap n P).IsWeightedHomogeneous (bellJetWeight (n + 1)) W := by
  apply isWeightedHomogeneous_eval₂_of_weighted_generators hP
  intro j
  simpa [negativeRawJetMap, diagonalCoordinateMap] using
    (MvPolynomial.isWeightedHomogeneous_C (bellJetWeight (n + 1)) (-1 : ℂ)).mul
      (MvPolynomial.isWeightedHomogeneous_X ℂ (bellJetWeight (n + 1)) j)

/-- **Reciprocal-Bell derivative-weight law.** Compression from inverse jets
to covariant simple-zero coordinates preserves native derivative weight
exactly. -/
theorem reciprocalBellCovariantTransform_preserves_derivativeWeight
    {n W : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P.IsWeightedHomogeneous (inverseJetDerivativeWeight n) W) :
    (reciprocalBellCovariantTransform n P).IsWeightedHomogeneous
      (bellJetWeight (n + 1)) W := by
  apply bellCoefficientEquiv_symm_preserves_weight
  apply negativeRawJetMap_preserves_weight
  apply bellCoefficientMap_preserves_weight
  exact simpleZeroDehomogenize_preserves_derivativeWeight hP

theorem isWeightedHomogeneous_homogeneousComponent
    {σ : Type*} {w : σ → ℕ} {W E : ℕ} {P : MvPolynomial σ ℂ}
    (hP : P.IsWeightedHomogeneous w W) :
    (MvPolynomial.homogeneousComponent E P).IsWeightedHomogeneous w W := by
  intro m hm
  rw [MvPolynomial.coeff_homogeneousComponent] at hm
  split at hm
  · exact hP hm
  · exact (hm rfl).elim

/-- For a polynomial that is both ordinary homogeneous of degree `E` and
Bell-weight homogeneous of weight `W`, subtracting one from every variable
weight gives residual weight `W-E`. -/
theorem isWeightedHomogeneous_bellJetWeight_sub_totalDegree
    {n W E : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hE : P.IsHomogeneous E)
    (hW : P.IsWeightedHomogeneous (bellJetWeight (n + 1)) W) :
    P.IsWeightedHomogeneous
      (fun i : Fin (n + 1) => bellJetWeight (n + 1) i - 1) (W - E) := by
  intro m hm
  have hdeg := hE hm
  have hweight := hW hm
  have hdeg' : (∑ i ∈ m.support, m i) = E := by
    simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using hdeg
  have hweight' : (∑ i ∈ m.support, m i * ((i : ℕ) + 1)) = W := by
    simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, bellJetWeight] using hweight
  change (∑ i ∈ m.support, m i * (((i : ℕ) + 1) - 1)) = W - E
  simp only [Nat.add_sub_cancel]
  have hexpand :
      (∑ i ∈ m.support, m i * ((i : ℕ) + 1)) =
        (∑ i ∈ m.support, m i * (i : ℕ)) + ∑ i ∈ m.support, m i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.mul_add, Nat.mul_one]
  rw [hexpand, hdeg'] at hweight'
  omega

/-- Fixing the universal first covariant residue converts Bell weight `W`
and ordinary degree `E` into the exact tail weight `W-E`. -/
theorem simpleZeroDehomogenize_residualWeight
    {n W E : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hE : P.IsHomogeneous E)
    (hW : P.IsWeightedHomogeneous (bellJetWeight (n + 1)) W) :
    (HTGeometry.simpleZeroDehomogenize n P).IsWeightedHomogeneous
      (bellJetWeight n) (W - E) := by
  have hadjusted := isWeightedHomogeneous_bellJetWeight_sub_totalDegree hE hW
  apply isWeightedHomogeneous_eval₂_of_weighted_generators hadjusted
  intro i
  induction i using Fin.cases with
  | zero =>
      simpa [HTGeometry.simpleZeroDehomogenize,
        HTGeometry.simpleZeroBoundaryResidue, bellJetWeight] using
        (MvPolynomial.isWeightedHomogeneous_one ℂ (bellJetWeight n))
  | succ i =>
      simpa [HTGeometry.simpleZeroDehomogenize,
        HTGeometry.simpleZeroBoundaryResidue, bellJetWeight] using
        (MvPolynomial.isWeightedHomogeneous_X ℂ (bellJetWeight n) i)

/-- **Top reciprocal-Bell boundary grading.** The top covariant boundary
residue of a derivative-weight `W` source has residual tail weight `W-E`,
where `E` is the reciprocal-Bell covariant degree. -/
theorem reciprocalBellTopBoundary_residualWeight
    {n W : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hW : P.IsWeightedHomogeneous (inverseJetDerivativeWeight n) W) :
    let Q := reciprocalBellCovariantTransform n P
    (HTGeometry.simpleZeroDehomogenize n
      (MvPolynomial.homogeneousComponent Q.totalDegree Q)).IsWeightedHomogeneous
        (bellJetWeight n) (W - Q.totalDegree) := by
  let Q := reciprocalBellCovariantTransform n P
  have hQW : Q.IsWeightedHomogeneous (bellJetWeight (n + 1)) W :=
    reciprocalBellCovariantTransform_preserves_derivativeWeight hW
  exact simpleZeroDehomogenize_residualWeight
    (MvPolynomial.homogeneousComponent_isHomogeneous Q.totalDegree Q)
    (isWeightedHomogeneous_homogeneousComponent hQW)

/-- Bell weight bounds ordinary degree because every Bell coordinate has
weight at least one. -/
theorem totalDegree_le_of_isWeightedHomogeneous_bellJetWeight
    {n W : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight n) W) (hP0 : P ≠ 0) :
    P.totalDegree ≤ W := by
  have htop : MvPolynomial.homogeneousComponent P.totalDegree P ≠ 0 :=
    HTGeometry.homogeneousComponent_totalDegree_ne_zero hP0
  obtain ⟨m, hm⟩ := MvPolynomial.exists_coeff_ne_zero htop
  rw [MvPolynomial.coeff_homogeneousComponent] at hm
  split at hm
  next hdegree =>
    have hweight := hP hm
    change (∑ i ∈ m.support, m i) = P.totalDegree at hdegree
    change (∑ i ∈ m.support, m i * ((i : ℕ) + 1)) = W at hweight
    rw [← hdegree, ← hweight]
    apply Finset.sum_le_sum
    intro i hi
    nlinarith
  next => exact (hm rfl).elim

/-- The top reciprocal-Bell boundary polynomial is nonzero on every nonzero
particle-homogeneous source sector. -/
theorem reciprocalBellTopBoundary_ne_zero_of_isHomogeneous
    {n D : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hD : P.IsHomogeneous D) (hP0 : P ≠ 0) :
    let Q := reciprocalBellCovariantTransform n P
    HTGeometry.simpleZeroDehomogenize n
        (MvPolynomial.homogeneousComponent Q.totalDegree Q) ≠ 0 := by
  let Q := reciprocalBellCovariantTransform n P
  have hQ0 : Q ≠ 0 :=
    reciprocalBellCovariantTransform_ne_zero_of_isHomogeneous hD hP0
  exact HTGeometry.simpleZeroDehomogenize_ne_zero_of_isHomogeneous
    (MvPolynomial.homogeneousComponent_isHomogeneous Q.totalDegree Q)
    (HTGeometry.homogeneousComponent_totalDegree_ne_zero hQ0)

/-- Distinct weighted-homogeneous summands cannot cancel.  This packages the
direct-sum interface needed by the cross-particle residue selection law. -/
theorem finset_sum_ne_zero_of_isWeightedHomogeneous_injOn
    {ι σ : Type*} (s : Finset ι) (w : σ → ℕ) (degree : ι → ℕ)
    (P : ι → MvPolynomial σ ℂ)
    (hs : s.Nonempty)
    (hdegree : Set.InjOn degree s)
    (hhom : ∀ i ∈ s, (P i).IsWeightedHomogeneous w (degree i))
    (hne : ∀ i ∈ s, P i ≠ 0) :
    ∑ i ∈ s, P i ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := hs
  intro hsum
  have hcomponent := congrArg
    (MvPolynomial.weightedHomogeneousComponent w (degree i)) hsum
  rw [map_sum, map_zero] at hcomponent
  have hsingle :
      (∑ j ∈ s,
        MvPolynomial.weightedHomogeneousComponent w (degree i) (P j)) = P i := by
    rw [Finset.sum_eq_single i]
    · rw [MvPolynomial.weightedHomogeneousComponent_of_mem (hhom i hi), if_pos rfl]
    · intro j hj hji
      rw [MvPolynomial.weightedHomogeneousComponent_of_mem (hhom j hj), if_neg]
      intro hij
      exact hji (hdegree hi hj hij).symm
    · intro hnot
      exact (hnot hi).elim
  rw [hsingle] at hcomponent
  exact hne i hi hcomponent

/-- Laurent exponent and coefficient weight form a faithful bigrading: a
finite sum of nonzero monomials with distinct bidegrees cannot cancel. -/
theorem finset_sum_laurent_single_ne_zero_of_bigraded_injOn
    {ι σ : Type*} (s : Finset ι) (w : σ → ℕ)
    (exponent : ι → ℤ) (degree : ι → ℕ)
    (P : ι → MvPolynomial σ ℂ)
    (hs : s.Nonempty)
    (hgrade : Set.InjOn (fun i => (exponent i, degree i)) s)
    (hhom : ∀ i ∈ s, (P i).IsWeightedHomogeneous w (degree i))
    (hne : ∀ i ∈ s, P i ≠ 0) :
    ∑ i ∈ s,
      (AddMonoidAlgebra.single (exponent i) (P i) :
        LaurentPolynomial (MvPolynomial σ ℂ)) ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := hs
  intro hsum
  have hsingle :
      MvPolynomial.weightedHomogeneousComponent w (degree i)
          ((∑ j ∈ s,
            (AddMonoidAlgebra.single (exponent j) (P j) :
              LaurentPolynomial (MvPolynomial σ ℂ))).coeff (exponent i)) = P i := by
    rw [AddMonoidAlgebra.coeff_sum, Finset.sum_apply', map_sum]
    rw [Finset.sum_eq_single i]
    · change MvPolynomial.weightedHomogeneousComponent w (degree i)
        ((AddMonoidAlgebra.single (exponent i) (P i) :
          LaurentPolynomial (MvPolynomial σ ℂ)).coeff (exponent i)) = P i
      rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
        MvPolynomial.weightedHomogeneousComponent_of_mem (hhom i hi), if_pos rfl]
    · intro j hj hji
      by_cases hexp : exponent j = exponent i
      · have hdegree : degree j ≠ degree i := by
          intro hdeg
          exact hji (hgrade hj hi (Prod.ext hexp hdeg))
        change MvPolynomial.weightedHomogeneousComponent w (degree i)
          ((AddMonoidAlgebra.single (exponent j) (P j) :
            LaurentPolynomial (MvPolynomial σ ℂ)).coeff (exponent i)) = 0
        rw [AddMonoidAlgebra.coeff_single, ← hexp, Finsupp.single_eq_same,
          MvPolynomial.weightedHomogeneousComponent_of_mem (hhom j hj), if_neg]
        exact Ne.symm hdegree
      · change MvPolynomial.weightedHomogeneousComponent w (degree i)
          ((AddMonoidAlgebra.single (exponent j) (P j) :
            LaurentPolynomial (MvPolynomial σ ℂ)).coeff (exponent i)) = 0
        rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne' hexp, map_zero]
    · intro hnot
      exact (hnot hi).elim
  have hzero :
      MvPolynomial.weightedHomogeneousComponent w (degree i)
          ((∑ j ∈ s,
            (AddMonoidAlgebra.single (exponent j) (P j) :
              LaurentPolynomial (MvPolynomial σ ℂ))).coeff (exponent i)) = 0 := by
    rw [hsum]
    simp
  rw [hsingle] at hzero
  exact hne i hi hzero

/-- The top covariant residue polynomial after fixing the universal first
residue. -/
def reciprocalBellTopBoundary (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) : MvPolynomial (Fin n) ℂ :=
  let Q := reciprocalBellCovariantTransform n P
  HTGeometry.simpleZeroDehomogenize n
    (MvPolynomial.homogeneousComponent Q.totalDegree Q)

/-- Native top-residue coefficient, embedded in the countable boundary ring.
The universal particle sign is included. -/
def reciprocalBellNativeTopResidueCoefficient (n D W : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) : MvPolynomial ℕ ℂ :=
  MvPolynomial.C ((-1 : ℂ) ^ (D + W)) *
    MvPolynomial.rename Fin.val (reciprocalBellTopBoundary n P)

/-- Laurent symbol of a native bihomogeneous top residue.  The Laurent
exponent records the inverse factorial scale power `-W`. -/
def reciprocalBellNativeTopResidueSymbol (n D W : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    LaurentPolynomial (MvPolynomial ℕ ℂ) :=
  AddMonoidAlgebra.single (-(W : ℤ))
    (reciprocalBellNativeTopResidueCoefficient n D W P)

/-- **Finite cross-particle residue noncancellation.**  Consider distinct
bihomogeneous source sectors whose reciprocal-Bell pole degrees all equal
the same `M`.  Laurent scale weight separates different derivative weights;
at a fixed derivative weight, residual boundary weight `W-E` separates the
different particle degrees.  Hence their native top-residue symbols cannot
cancel. -/
theorem finset_sum_reciprocalBellNativeTopResidueSymbol_ne_zero
    {ι : Type*} {n M : ℕ} (s : Finset ι)
    (D W : ι → ℕ) (P : ι → MvPolynomial (Fin (n + 2)) ℂ)
    (hs : s.Nonempty)
    (hDW : Set.InjOn (fun i => (D i, W i)) s)
    (hD : ∀ i ∈ s, (P i).IsHomogeneous (D i))
    (hW : ∀ i ∈ s,
      (P i).IsWeightedHomogeneous (inverseJetDerivativeWeight n) (W i))
    (hP : ∀ i ∈ s, P i ≠ 0)
    (hM : ∀ i ∈ s,
      D i + (reciprocalBellCovariantTransform n (P i)).totalDegree = M) :
    ∑ i ∈ s, reciprocalBellNativeTopResidueSymbol n (D i) (W i) (P i) ≠ 0 := by
  classical
  apply finset_sum_laurent_single_ne_zero_of_bigraded_injOn s
    (fun k : ℕ => k + 1)
    (fun i => -(W i : ℤ))
    (fun i => W i - (reciprocalBellCovariantTransform n (P i)).totalDegree)
    (fun i => reciprocalBellNativeTopResidueCoefficient n (D i) (W i) (P i)) hs
  · intro i hi j hj hij
    have hscaleInt := congrArg Prod.fst hij
    have hscale : W i = W j := by
      have : -(W i : ℤ) = -(W j : ℤ) := hscaleInt
      omega
    have hres := congrArg Prod.snd hij
    let Qi := reciprocalBellCovariantTransform n (P i)
    let Qj := reciprocalBellCovariantTransform n (P j)
    have hQi0 : Qi ≠ 0 :=
      reciprocalBellCovariantTransform_ne_zero_of_isHomogeneous (hD i hi) (hP i hi)
    have hQj0 : Qj ≠ 0 :=
      reciprocalBellCovariantTransform_ne_zero_of_isHomogeneous (hD j hj) (hP j hj)
    have hQiW : Qi.IsWeightedHomogeneous (bellJetWeight (n + 1)) (W i) :=
      reciprocalBellCovariantTransform_preserves_derivativeWeight (hW i hi)
    have hQjW : Qj.IsWeightedHomogeneous (bellJetWeight (n + 1)) (W j) :=
      reciprocalBellCovariantTransform_preserves_derivativeWeight (hW j hj)
    have hEi : Qi.totalDegree ≤ W i :=
      totalDegree_le_of_isWeightedHomogeneous_bellJetWeight hQiW hQi0
    have hEj : Qj.totalDegree ≤ W j :=
      totalDegree_le_of_isWeightedHomogeneous_bellJetWeight hQjW hQj0
    have hE : Qi.totalDegree = Qj.totalDegree := by
      change W i - Qi.totalDegree = W j - Qj.totalDegree at hres
      omega
    have hparticle : D i = D j := by
      have hiM := hM i hi
      have hjM := hM j hj
      change D i + Qi.totalDegree = M at hiM
      change D j + Qj.totalDegree = M at hjM
      omega
    exact hDW hi hj (Prod.ext hparticle hscale)
  · intro i hi
    have hboundary := reciprocalBellTopBoundary_residualWeight (hW i hi)
    have hrename : (MvPolynomial.rename Fin.val
        (reciprocalBellTopBoundary n (P i))).IsWeightedHomogeneous
          (fun k : ℕ => k + 1)
          (W i - (reciprocalBellCovariantTransform n (P i)).totalDegree) :=
      rename_isWeightedHomogeneous hboundary Fin.val (by
        intro j
        simp [bellJetWeight])
    have hconst := MvPolynomial.isWeightedHomogeneous_C
      (fun k : ℕ => k + 1) ((-1 : ℂ) ^ (D i + W i))
    simpa [reciprocalBellNativeTopResidueCoefficient,
      reciprocalBellTopBoundary] using hconst.mul hrename
  · intro i hi
    have hboundary : reciprocalBellTopBoundary n (P i) ≠ 0 := by
      simpa [reciprocalBellTopBoundary] using
        reciprocalBellTopBoundary_ne_zero_of_isHomogeneous (hD i hi) (hP i hi)
    have hrename : MvPolynomial.rename Fin.val
        (reciprocalBellTopBoundary n (P i)) ≠ 0 :=
      (MvPolynomial.rename_injective Fin.val Fin.val_injective).ne hboundary
    exact mul_ne_zero
      (MvPolynomial.C_ne_zero.mpr (pow_ne_zero _ (by norm_num))) hrename

local instance gammaPoleCovariantResidueNatGermAlgebra : Algebra ℂ NatGerm :=
  complexNatGerm.toAlgebra

/-- The factorial scale together with every complete covariant simple-zero
residue. -/
def gammaPoleScaleAndCovariantResidueFamily : Option ℕ → NatGerm
  | none => reciprocalSignedFactorialGerm
  | some j => gammaSimpleZeroCovariantResidueGerm j

/-- Joint algebraic independence survives the nonzero factorial diagonal
that converts reciprocal-unit coefficients into covariant residues. -/
theorem algebraicIndependent_gammaPoleScaleAndCovariantResidueFamily :
    AlgebraicIndependent ℂ gammaPoleScaleAndCovariantResidueFamily := by
  let c : Option ℕ → ℂ
    | none => 1
    | some j => ((j + 2).factorial : ℂ)
  have hc : ∀ o, c o ≠ 0 := by
    intro o
    rcases o with (_ | j)
    · exact one_ne_zero
    · simpa [c] using
        (show (((j + 2).factorial : ℂ)) ≠ 0 by
          exact_mod_cast Nat.factorial_ne_zero (j + 2))
  have hscaled := AlgebraicIndependent.diagonalScale
    algebraicIndependent_gammaPoleScaleAndReciprocalUnitCoefficientFamily hc
  have heq : (fun o => algebraMap ℂ NatGerm (c o) *
      gammaPoleScaleAndReciprocalUnitCoefficientFamily o) =
      gammaPoleScaleAndCovariantResidueFamily := by
    funext o
    rcases o with (_ | j)
    · simp [c, gammaPoleScaleAndReciprocalUnitCoefficientFamily,
        gammaPoleScaleAndCovariantResidueFamily]
    · simpa [c, gammaPoleScaleAndReciprocalUnitCoefficientFamily,
        gammaPoleScaleAndCovariantResidueFamily] using
        (gammaSimpleZeroCovariantResidueGerm_eq j).symm
  rwa [heq] at hscaled

def gammaPoleCovariantResidueEval : MvPolynomial ℕ ℂ →+* NatGerm :=
  MvPolynomial.eval₂Hom complexNatGerm gammaSimpleZeroCovariantResidueGerm

def gammaPoleScaleAndCovariantResiduePolynomialEval :
    Polynomial (MvPolynomial ℕ ℂ) →+* NatGerm :=
  Polynomial.eval₂RingHom gammaPoleCovariantResidueEval
    reciprocalSignedFactorialGerm

theorem gammaPoleScaleAndCovariantResiduePolynomialEval_eq_comp :
    gammaPoleScaleAndCovariantResiduePolynomialEval =
      (MvPolynomial.eval₂Hom complexNatGerm
        gammaPoleScaleAndCovariantResidueFamily).comp
        (MvPolynomial.optionEquivLeft ℂ ℕ).symm.toRingHom := by
  apply Polynomial.ringHom_ext
  · intro p
    let lhs : MvPolynomial ℕ ℂ →+* MvPolynomial (Option ℕ) ℂ :=
      (MvPolynomial.optionEquivLeft ℂ ℕ).symm.toRingHom.comp Polynomial.C
    have hlhs : lhs = (MvPolynomial.rename some).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [lhs]
      · intro k
        simp [lhs, MvPolynomial.optionEquivLeft_symm_C_X]
    calc
      gammaPoleScaleAndCovariantResiduePolynomialEval (Polynomial.C p) =
          gammaPoleCovariantResidueEval p := by
        simp [gammaPoleScaleAndCovariantResiduePolynomialEval]
      _ = MvPolynomial.eval₂Hom complexNatGerm
          gammaPoleScaleAndCovariantResidueFamily
          (MvPolynomial.rename some p) := by
        simp [gammaPoleCovariantResidueEval,
          gammaPoleScaleAndCovariantResidueFamily,
          MvPolynomial.eval₂_rename, Function.comp_def]
      _ = MvPolynomial.eval₂Hom complexNatGerm
          gammaPoleScaleAndCovariantResidueFamily
          ((MvPolynomial.optionEquivLeft ℂ ℕ).symm (Polynomial.C p)) := by
        have hp := RingHom.congr_fun hlhs p
        change (MvPolynomial.optionEquivLeft ℂ ℕ).symm (Polynomial.C p) =
          MvPolynomial.rename some p at hp
        exact congrArg
          (MvPolynomial.eval₂Hom complexNatGerm
            gammaPoleScaleAndCovariantResidueFamily) hp.symm
  · simp [gammaPoleScaleAndCovariantResiduePolynomialEval,
      gammaPoleCovariantResidueEval,
      gammaPoleScaleAndCovariantResidueFamily]

theorem gammaPoleScaleAndCovariantResiduePolynomialEval_injective :
    Function.Injective gammaPoleScaleAndCovariantResiduePolynomialEval := by
  rw [gammaPoleScaleAndCovariantResiduePolynomialEval_eq_comp]
  have hfull : Function.Injective
      (MvPolynomial.eval₂Hom complexNatGerm
        gammaPoleScaleAndCovariantResidueFamily) := by
    have h :=
      algebraicIndependent_iff_injective_aeval.mp
        algebraicIndependent_gammaPoleScaleAndCovariantResidueFamily
    change Function.Injective
      (MvPolynomial.eval₂Hom complexNatGerm
        gammaPoleScaleAndCovariantResidueFamily) at h
    exact h
  exact hfull.comp (MvPolynomial.optionEquivLeft ℂ ℕ).symm.injective

/-- Laurent evaluation in the factorial scale with covariant-residue
polynomial coefficients. -/
def gammaPoleScaleAndCovariantResidueLaurentEval :
    LaurentPolynomial (MvPolynomial ℕ ℂ) →+* NatGerm :=
  LaurentPolynomial.eval₂ gammaPoleCovariantResidueEval
    reciprocalSignedFactorialGermUnit

@[simp] theorem reciprocalSignedFactorialGermUnit_inv_val :
    ((reciprocalSignedFactorialGermUnit⁻¹ : NatGermˣ) : NatGerm) =
      signedFactorialGerm := by
  apply reciprocalSignedFactorialGerm_isUnit.mul_left_cancel
  calc
    reciprocalSignedFactorialGerm *
        ((reciprocalSignedFactorialGermUnit⁻¹ : NatGermˣ) : NatGerm) = 1 := by
      exact reciprocalSignedFactorialGerm_isUnit.mul_val_inv
    _ = reciprocalSignedFactorialGerm * signedFactorialGerm := by
      rw [mul_comm, signedFactorialGerm_mul_reciprocal]

theorem gammaPoleScaleAndCovariantResidueLaurentEval_single_neg
    (W : ℕ) (A : MvPolynomial ℕ ℂ) :
    gammaPoleScaleAndCovariantResidueLaurentEval
        (AddMonoidAlgebra.single (-(W : ℤ)) A) =
      signedFactorialGerm ^ W * gammaPoleCovariantResidueEval A := by
  rw [show (AddMonoidAlgebra.single (-(W : ℤ)) A :
      LaurentPolynomial (MvPolynomial ℕ ℂ)) =
        LaurentPolynomial.C A * LaurentPolynomial.T (-(W : ℤ)) from
      LaurentPolynomial.single_eq_C_mul_T A (-(W : ℤ))]
  change LaurentPolynomial.eval₂ gammaPoleCovariantResidueEval
      reciprocalSignedFactorialGermUnit
        (LaurentPolynomial.C A * LaurentPolynomial.T (-(W : ℤ))) = _
  rw [LaurentPolynomial.eval₂_C_mul_T_neg_n,
    reciprocalSignedFactorialGermUnit_inv_val, mul_comm]

theorem signedFactorialSequence_succ_eq_neg_inv_scale (branch : ℕ) :
    signedFactorialSequence (branch + 1) =
      -(reciprocalGammaFactorialScale branch)⁻¹ := by
  have h := congrArg Inv.inv
    (reciprocalSignedFactorialSequence_succ_eq_neg_scale branch)
  simpa [reciprocalSignedFactorialSequence] using h

theorem gammaPoleCovariantResidueEval_rename (n : ℕ)
    (A : MvPolynomial (Fin n) ℂ) :
    gammaPoleCovariantResidueEval (MvPolynomial.rename Fin.val A) =
      MvPolynomial.aeval
        (fun j : Fin n => gammaSimpleZeroCovariantResidueGerm j.val) A := by
  have hbase : algebraMap ℂ NatGerm = complexNatGerm := rfl
  simp [gammaPoleCovariantResidueEval, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_rename, Function.comp_def, hbase]

theorem gammaPoleCovariantResidueEval_topBoundary (n : ℕ)
    (Q : MvPolynomial (Fin (n + 1)) ℂ) :
    gammaPoleCovariantResidueEval
        (MvPolynomial.rename Fin.val
          (HTGeometry.simpleZeroDehomogenize n Q)) =
      MvPolynomial.aeval (gammaSimpleZeroBoundaryResidueGerm n) Q := by
  rw [gammaPoleCovariantResidueEval_rename,
    aeval_gammaSimpleZeroBoundaryResidueGerm]

theorem aeval_gammaSimpleZeroBoundaryResidueGerm_eq_sequence (n : ℕ)
    (Q : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.aeval (gammaSimpleZeroBoundaryResidueGerm n) Q =
      ((fun N : ℕ =>
        MvPolynomial.eval (gammaSimpleZeroBoundaryResidueValue (N - 1) n) Q :
          ℕ → ℂ) : NatGerm) := by
  rw [gammaSimpleZeroBoundaryResidueGerm_eq_sequence,
    aeval_sequenceGerm_eq, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun N => by
    rw [mvPolynomialSequenceEval_apply]

/-- **Joint Laurent value reflection.** Negative derivative-weight powers of
the factorial scale remain faithful jointly with every covariant residue. -/
theorem gammaPoleScaleAndCovariantResidueLaurentEval_injective :
    Function.Injective gammaPoleScaleAndCovariantResidueLaurentEval := by
  apply laurentPolynomial_eval₂_injective_of_polynomial_eval₂_injective
  simpa [gammaPoleScaleAndCovariantResiduePolynomialEval,
    reciprocalSignedFactorialGermUnit_val] using
      gammaPoleScaleAndCovariantResiduePolynomialEval_injective

/-- Pole-index germ obtained by evaluating one native reciprocal-Bell
top-residue symbol on the actual factorial scale and covariant residues. -/
def reciprocalBellNativeTopResidueGerm (n D W : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) : NatGerm :=
  gammaPoleScaleAndCovariantResidueLaurentEval
    (reciprocalBellNativeTopResidueSymbol n D W P)

/-- The native reciprocal-Bell residue appearing in the analytic pole limit. -/
def reciprocalBellNativeTopResidueValue (branch n D W : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) : ℂ :=
  (reciprocalGammaFactorialScale branch)⁻¹ ^ W *
    ((-1 : ℂ) ^ D *
      MvPolynomial.eval (gammaSimpleZeroBoundaryResidueValue branch n)
        (MvPolynomial.homogeneousComponent
          (reciprocalBellCovariantTransform n P).totalDegree
          (reciprocalBellCovariantTransform n P)))

theorem reciprocalBellNativeTopResidueGerm_eq_factorized (n D W : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    reciprocalBellNativeTopResidueGerm n D W P =
      signedFactorialGerm ^ W * complexNatGerm ((-1 : ℂ) ^ (D + W)) *
        MvPolynomial.aeval (gammaSimpleZeroBoundaryResidueGerm n)
          (MvPolynomial.homogeneousComponent
            (reciprocalBellCovariantTransform n P).totalDegree
            (reciprocalBellCovariantTransform n P)) := by
  have hc : gammaPoleCovariantResidueEval
      (MvPolynomial.C ((-1 : ℂ) ^ (D + W))) =
        complexNatGerm ((-1 : ℂ) ^ (D + W)) := by
    simp [gammaPoleCovariantResidueEval]
  rw [reciprocalBellNativeTopResidueGerm,
    reciprocalBellNativeTopResidueSymbol,
    gammaPoleScaleAndCovariantResidueLaurentEval_single_neg,
    reciprocalBellNativeTopResidueCoefficient, map_mul, hc,
    reciprocalBellTopBoundary,
    gammaPoleCovariantResidueEval_topBoundary]
  rw [mul_assoc]

/-- The symbolic Laurent residue is exactly the pole-index germ of the
analytic native top residues. -/
theorem reciprocalBellNativeTopResidueGerm_eq_sequence (n D W : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    reciprocalBellNativeTopResidueGerm n D W P =
      (fun N : ℕ => reciprocalBellNativeTopResidueValue (N - 1) n D W P :
        NatGerm) := by
  rw [reciprocalBellNativeTopResidueGerm_eq_factorized,
    aeval_gammaSimpleZeroBoundaryResidueGerm_eq_sequence,
    complexNatGerm_eq_constGerm]
  unfold signedFactorialGerm
  rw [← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul,
    ← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
  exact Filter.eventually_atTop.2 ⟨1, fun N hN => by
    obtain ⟨branch, rfl⟩ := Nat.exists_eq_add_of_le hN
    have hsigned : signedFactorialSequence (1 + branch) =
        -(reciprocalGammaFactorialScale branch)⁻¹ := by
      simpa [add_comm] using signedFactorialSequence_succ_eq_neg_inv_scale branch
    have hsign : ((-1 : ℂ) ^ W) * ((-1 : ℂ) ^ W) = 1 := by
      rw [← mul_pow]
      norm_num
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [Nat.add_sub_cancel_left]
    rw [hsigned, reciprocalBellNativeTopResidueValue, neg_pow, pow_add]
    calc
      (((-1 : ℂ) ^ W * (reciprocalGammaFactorialScale branch)⁻¹ ^ W) *
            ((-1 : ℂ) ^ D * (-1 : ℂ) ^ W)) *
          MvPolynomial.eval (gammaSimpleZeroBoundaryResidueValue branch n)
            (MvPolynomial.homogeneousComponent
              (reciprocalBellCovariantTransform n P).totalDegree
              (reciprocalBellCovariantTransform n P)) =
        (((-1 : ℂ) ^ W) * ((-1 : ℂ) ^ W)) *
          ((reciprocalGammaFactorialScale branch)⁻¹ ^ W *
            ((-1 : ℂ) ^ D *
              MvPolynomial.eval (gammaSimpleZeroBoundaryResidueValue branch n)
                (MvPolynomial.homogeneousComponent
                  (reciprocalBellCovariantTransform n P).totalDegree
                  (reciprocalBellCovariantTransform n P)))) := by ring
      _ = _ := by rw [hsign, one_mul]⟩

/-- Homogeneity and derivative-weight purity discharge meromorphicity for a
native Gamma jet sector. -/
theorem meromorphicAt_gammaAffineJetEval_of_bihomogeneous
    (branch : ℕ) {n D W : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hD : P.IsHomogeneous D)
    (hW : P.IsWeightedHomogeneous (inverseJetDerivativeWeight n) W) :
    MeromorphicAt (gammaAffineJetEval branch n P) 0 := by
  let Q := reciprocalBellCovariantTransform n P
  have hS := analyticAt_gammaPoleSimpleZeroSection_zero branch
  have hInv : MeromorphicAt
      (fun x => (gammaPoleSimpleZeroSection branch x)⁻¹) 0 :=
    hS.meromorphicAt.inv
  have hCov := meromorphicAt_gammaSimpleZeroCovariantEval branch n Q
  have hmodel : MeromorphicAt
      (fun x => (gammaPoleSimpleZeroSection branch x)⁻¹ ^ D *
        gammaSimpleZeroCovariantEval branch n Q x) 0 :=
    (hInv.pow D).mul hCov
  have hinverse : MeromorphicAt
      (inverseSectionJetEval (gammaPoleSimpleZeroSection branch) n P) 0 :=
    hmodel.congr
      (inverseSectionJetEval_gammaPole_eventuallyEq_covariant branch hD).symm
  have hfactorial : MeromorphicAt (gammaFactorialJetEval branch n P) 0 :=
    hinverse.congr
      (gammaFactorialJetEval_eventuallyEq_inverseSectionJetEval branch n P).symm
  have hscaled : MeromorphicAt
      (fun x => (reciprocalGammaFactorialScale branch)⁻¹ ^ W *
        gammaFactorialJetEval branch n P x) 0 :=
    analyticAt_const.meromorphicAt.mul hfactorial
  apply hscaled.congr
  apply Filter.Eventually.of_forall
  intro x
  change (reciprocalGammaFactorialScale branch)⁻¹ ^ W *
      gammaFactorialJetEval branch n P x = gammaAffineJetEval branch n P x
  rw [congrFun (gammaFactorialJetEval_eq_scale_mul_gammaAffineJetEval
    branch n hW) x]
  rw [← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ (reciprocalGammaFactorialScale_ne_zero branch),
    one_pow, one_mul]

theorem isHomogeneous_weightedHomogeneousComponent_of
    {σ R : Type*} [CommSemiring R]
    {P : MvPolynomial σ R} {D : ℕ} (hD : P.IsHomogeneous D)
    (w : σ → ℕ) (W : ℕ) :
    (MvPolynomial.weightedHomogeneousComponent w W P).IsHomogeneous D := by
  intro m hm
  rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hm
  split at hm
  · exact hD hm
  · exact (hm rfl).elim

theorem sum_weightedHomogeneousComponent_natRange
    {σ : Type*} (w : σ → ℕ) (P : MvPolynomial σ ℂ) :
    (∑ W ∈ Finset.range (P.weightedTotalDegree w + 1),
      MvPolynomial.weightedHomogeneousComponent w W P) = P := by
  classical
  ext m
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_weightedHomogeneousComponent]
  by_cases hcoeff : MvPolynomial.coeff m P = 0
  · simp [hcoeff]
  · have hm : m ∈ P.support := MvPolynomial.mem_support_iff.mpr hcoeff
    have hle := MvPolynomial.le_weightedTotalDegree w hm
    rw [Finset.sum_eq_single (Finsupp.weight w m)]
    · rw [if_pos rfl]
    · intro W hW hne
      rw [if_neg]
      exact Ne.symm hne
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))).elim

/-- Taking an ordinary homogeneous component cannot introduce a larger
derivative weight. -/
theorem weightedTotalDegree_homogeneousComponent_le
    {σ : Type*} (w : σ → ℕ)
    (D : ℕ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.homogeneousComponent D P).weightedTotalDegree w ≤
      P.weightedTotalDegree w := by
  classical
  rw [MvPolynomial.weightedTotalDegree]
  apply Finset.sup_le
  intro m hm
  rw [MvPolynomial.support_homogeneousComponent] at hm
  exact MvPolynomial.le_weightedTotalDegree w (Finset.mem_filter.mp hm).1

/-- A larger finite weight range still reconstructs the polynomial. -/
theorem sum_weightedHomogeneousComponent_range_of_le
    {σ : Type*} (w : σ → ℕ)
    (P : MvPolynomial σ ℂ) {N : ℕ}
    (hN : P.weightedTotalDegree w ≤ N) :
    ∑ W ∈ Finset.range (N + 1),
      MvPolynomial.weightedHomogeneousComponent w W P = P := by
  classical
  have hsub : Finset.range (P.weightedTotalDegree w + 1) ⊆
      Finset.range (N + 1) := by
    intro W hW
    simp only [Finset.mem_range] at hW ⊢
    omega
  conv_rhs => rw [← sum_weightedHomogeneousComponent_natRange w P]
  refine (Finset.sum_subset hsub ?_).symm
  intro W hW hWsmall
  apply MvPolynomial.weightedHomogeneousComponent_eq_zero
  simp only [Finset.mem_range, Nat.lt_add_one_iff] at hWsmall
  omega

/-- Canonical `(particle degree, derivative weight)` component. -/
def reciprocalBellBihomogeneousComponent (n D W : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    MvPolynomial (Fin (n + 2)) ℂ :=
  MvPolynomial.weightedHomogeneousComponent (inverseJetDerivativeWeight n) W
    (MvPolynomial.homogeneousComponent D P)

/-- Finite support of the canonical reciprocal-Bell source bigrading. -/
def reciprocalBellBihomogeneousSupport (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) : Finset (ℕ × ℕ) :=
  ((Finset.range (P.totalDegree + 1)).product
      (Finset.range (P.weightedTotalDegree (inverseJetDerivativeWeight n) + 1))).filter
    fun p => reciprocalBellBihomogeneousComponent n p.1 p.2 P ≠ 0

theorem reciprocalBellBihomogeneousComponent_isHomogeneous
    (n D W : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    (reciprocalBellBihomogeneousComponent n D W P).IsHomogeneous D := by
  exact isHomogeneous_weightedHomogeneousComponent_of
    (MvPolynomial.homogeneousComponent_isHomogeneous D P)
    (inverseJetDerivativeWeight n) W

theorem reciprocalBellBihomogeneousComponent_isWeightedHomogeneous
    (n D W : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    (reciprocalBellBihomogeneousComponent n D W P).IsWeightedHomogeneous
      (inverseJetDerivativeWeight n) W := by
  exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous W _

/-- The canonical finite bigrading reconstructs every constant-coefficient
jet polynomial exactly. -/
theorem sum_reciprocalBellBihomogeneousComponent_support
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    ∑ p ∈ reciprocalBellBihomogeneousSupport n P,
      reciprocalBellBihomogeneousComponent n p.1 p.2 P = P := by
  classical
  let R := (Finset.range (P.totalDegree + 1)).product
    (Finset.range (P.weightedTotalDegree (inverseJetDerivativeWeight n) + 1))
  calc
    (∑ p ∈ reciprocalBellBihomogeneousSupport n P,
        reciprocalBellBihomogeneousComponent n p.1 p.2 P) =
        ∑ p ∈ R, reciprocalBellBihomogeneousComponent n p.1 p.2 P := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p hp hnot
      have hzero : ¬ reciprocalBellBihomogeneousComponent n p.1 p.2 P ≠ 0 := by
        intro hne
        exact hnot (Finset.mem_filter.mpr ⟨hp, hne⟩)
      exact not_ne_iff.mp hzero
    _ = ∑ D ∈ Finset.range (P.totalDegree + 1),
        ∑ W ∈ Finset.range
          (P.weightedTotalDegree (inverseJetDerivativeWeight n) + 1),
          reciprocalBellBihomogeneousComponent n D W P := by
      exact Finset.sum_product'
        (Finset.range (P.totalDegree + 1))
        (Finset.range
          (P.weightedTotalDegree (inverseJetDerivativeWeight n) + 1))
        (fun D W => reciprocalBellBihomogeneousComponent n D W P)
    _ = ∑ D ∈ Finset.range (P.totalDegree + 1),
        MvPolynomial.homogeneousComponent D P := by
      apply Finset.sum_congr rfl
      intro D hD
      exact sum_weightedHomogeneousComponent_range_of_le
        (inverseJetDerivativeWeight n)
        (MvPolynomial.homogeneousComponent D P)
        (weightedTotalDegree_homogeneousComponent_le
          (inverseJetDerivativeWeight n) D P)
    _ = P := MvPolynomial.sum_homogeneousComponent P

theorem reciprocalBellBihomogeneousSupport_nonempty
    {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0) :
    (reciprocalBellBihomogeneousSupport n P).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  apply hP
  rw [← sum_reciprocalBellBihomogeneousComponent_support n P, hempty]
  simp

/-- Native pole degree attached to one canonical source bidegree. -/
def reciprocalBellBihomogeneousPoleDegree (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) (p : ℕ × ℕ) : ℕ :=
  p.1 + (reciprocalBellCovariantTransform n
    (reciprocalBellBihomogeneousComponent n p.1 p.2 P)).totalDegree

/-- Maximum native pole degree among the nonzero canonical bidegrees. -/
def reciprocalBellNativePoleDegree (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) : ℕ :=
  (reciprocalBellBihomogeneousSupport n P).sup
    (reciprocalBellBihomogeneousPoleDegree n P)

/-- Canonical bidegrees that attain the maximum native pole degree. -/
def reciprocalBellBihomogeneousTopSupport (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) : Finset (ℕ × ℕ) :=
  (reciprocalBellBihomogeneousSupport n P).filter fun p =>
    reciprocalBellBihomogeneousPoleDegree n P p =
      reciprocalBellNativePoleDegree n P

/-- Actual summed residue of the canonical maximal pole layer. -/
def reciprocalBellNativeTopResidueValueSum (branch n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) : ℂ :=
  ∑ p ∈ reciprocalBellBihomogeneousTopSupport n P,
    reciprocalBellNativeTopResidueValue branch n p.1 p.2
      (reciprocalBellBihomogeneousComponent n p.1 p.2 P)

theorem reciprocalBellBihomogeneousTopSupport_nonempty
    {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0) :
    (reciprocalBellBihomogeneousTopSupport n P).Nonempty := by
  classical
  obtain ⟨p, hp, hdegree⟩ := Finset.sup_mem_of_nonempty
    (f := reciprocalBellBihomogeneousPoleDegree n P)
    (reciprocalBellBihomogeneousSupport_nonempty hP)
  exact ⟨p, Finset.mem_filter.mpr ⟨hp, by
    simpa [reciprocalBellNativePoleDegree] using hdegree⟩⟩

theorem reciprocalBellBihomogeneousPoleDegree_le
    {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    {p : ℕ × ℕ} (hp : p ∈ reciprocalBellBihomogeneousSupport n P) :
    reciprocalBellBihomogeneousPoleDegree n P p ≤
      reciprocalBellNativePoleDegree n P := by
  exact Finset.le_sup hp

/-- Raising a bihomogeneous sector to any larger candidate pole degree kills
its residue unless the candidate is its exact reciprocal-Bell degree. -/
theorem tendsto_pow_mul_gammaAffineJetEval_of_poleDegree_le
    (branch M : ℕ) {n D W : ℕ}
    {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hD : P.IsHomogeneous D)
    (hW : P.IsWeightedHomogeneous (inverseJetDerivativeWeight n) W)
    (hdegree : D + (reciprocalBellCovariantTransform n P).totalDegree ≤ M) :
    Tendsto
      (fun x : ℂ => x ^ M * gammaAffineJetEval branch n P x)
      (𝓝[≠] 0)
      (𝓝 (if D + (reciprocalBellCovariantTransform n P).totalDegree = M then
        reciprocalBellNativeTopResidueValue branch n D W P else 0)) := by
  let q := D + (reciprocalBellCovariantTransform n P).totalDegree
  have hbase := tendsto_pow_add_reciprocalBellDegree_mul_gammaAffineJetEval
    branch hD hW
  by_cases hqM : q = M
  · subst M
    simpa [q, reciprocalBellNativeTopResidueValue] using hbase
  · have hqM' : D + (reciprocalBellCovariantTransform n P).totalDegree ≠ M := by
      simpa [q] using hqM
    have hlt : q < M := lt_of_le_of_ne (by simpa [q] using hdegree) hqM
    have hz : Tendsto (fun x : ℂ => x) (𝓝[≠] 0) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    have hpow : Tendsto (fun x : ℂ => x ^ (M - q)) (𝓝[≠] 0) (𝓝 0) := by
      simpa [zero_pow (Nat.sub_pos_of_lt hlt).ne'] using hz.pow (M - q)
    have hprod : Tendsto
        (fun x : ℂ => x ^ (M - q) *
          (x ^ (D + (reciprocalBellCovariantTransform n P).totalDegree) *
            gammaAffineJetEval branch n P x))
        (𝓝[≠] 0) (𝓝 0) := by
      simpa using hpow.mul hbase
    have hcongr : Tendsto
        (fun x : ℂ => x ^ M * gammaAffineJetEval branch n P x)
        (𝓝[≠] 0) (𝓝 0) := by
      apply hprod.congr'
      apply Filter.Eventually.of_forall
      intro x
      change x ^ (M - q) *
          (x ^ (D + (reciprocalBellCovariantTransform n P).totalDegree) *
            gammaAffineJetEval branch n P x) =
        x ^ M * gammaAffineJetEval branch n P x
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (by simpa [q] using hdegree)]
    simpa [hqM'] using hcongr

theorem meromorphicAt_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i ∈ s, MeromorphicAt (f i) z) :
    MeromorphicAt (fun x => ∑ i ∈ s, f i x) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z).meromorphicAt
  | @insert i t hit ih =>
      have hadd := (hf i (by simp)).add
        (ih fun j hj => hf j (by simp [hj]))
      change MeromorphicAt (fun x => f i x + ∑ j ∈ t, f j x) z at hadd
      simpa only [Finset.sum_insert hit] using hadd

theorem gammaAffineJetEval_eq_sum_bihomogeneousSupport
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    gammaAffineJetEval branch n P = fun x =>
      ∑ p ∈ reciprocalBellBihomogeneousSupport n P,
        gammaAffineJetEval branch n
          (reciprocalBellBihomogeneousComponent n p.1 p.2 P) x := by
  funext x
  change MvPolynomial.eval
      (fun j : Fin (n + 2) => iteratedDeriv (j : ℕ) Complex.Gamma
        (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)) P =
    ∑ p ∈ reciprocalBellBihomogeneousSupport n P,
      MvPolynomial.eval
        (fun j : Fin (n + 2) => iteratedDeriv (j : ℕ) Complex.Gamma
          (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x))
        (reciprocalBellBihomogeneousComponent n p.1 p.2 P)
  rw [← map_sum, sum_reciprocalBellBihomogeneousComponent_support]

/-- The canonical source bigrading discharges meromorphicity for every
constant-coefficient native Gamma jet polynomial. -/
theorem meromorphicAt_gammaAffineJetEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    MeromorphicAt (gammaAffineJetEval branch n P) 0 := by
  let s := reciprocalBellBihomogeneousSupport n P
  have hsum := meromorphicAt_finset_sum s
    (fun p => gammaAffineJetEval branch n
      (reciprocalBellBihomogeneousComponent n p.1 p.2 P)) 0 (fun p hp =>
        meromorphicAt_gammaAffineJetEval_of_bihomogeneous branch
          (reciprocalBellBihomogeneousComponent_isHomogeneous n p.1 p.2 P)
          (reciprocalBellBihomogeneousComponent_isWeightedHomogeneous n p.1 p.2 P))
  rw [gammaAffineJetEval_eq_sum_bihomogeneousSupport branch n P]
  exact hsum

/-- At every Gamma pole branch, maximal normalization of an arbitrary
constant-coefficient jet polynomial converges to its canonical summed top
residue; the residue may vanish on an individual branch. -/
theorem tendsto_pow_reciprocalBellNativePoleDegree_mul_gammaAffineJetEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    Tendsto
      (fun x : ℂ => x ^ reciprocalBellNativePoleDegree n P *
        gammaAffineJetEval branch n P x)
      (𝓝[≠] 0)
      (𝓝 (reciprocalBellNativeTopResidueValueSum branch n P)) := by
  classical
  let s := reciprocalBellBihomogeneousSupport n P
  let M := reciprocalBellNativePoleDegree n P
  let C : ℕ × ℕ → MvPolynomial (Fin (n + 2)) ℂ := fun p =>
    reciprocalBellBihomogeneousComponent n p.1 p.2 P
  have hterm : ∀ p ∈ s,
      Tendsto
        (fun x : ℂ => x ^ M * gammaAffineJetEval branch n (C p) x)
        (𝓝[≠] 0)
        (𝓝 (if p.1 + (reciprocalBellCovariantTransform n (C p)).totalDegree = M then
          reciprocalBellNativeTopResidueValue branch n p.1 p.2 (C p) else 0)) := by
    intro p hp
    have hpSupport : p ∈ reciprocalBellBihomogeneousSupport n P := by
      simpa [s] using hp
    exact tendsto_pow_mul_gammaAffineJetEval_of_poleDegree_le branch M
      (reciprocalBellBihomogeneousComponent_isHomogeneous n p.1 p.2 P)
      (reciprocalBellBihomogeneousComponent_isWeightedHomogeneous n p.1 p.2 P)
      (by simpa [C, M, reciprocalBellBihomogeneousPoleDegree] using
        reciprocalBellBihomogeneousPoleDegree_le hpSupport)
  have hlim := tendsto_finsetSum s hterm
  have hnormalized : Tendsto
      (fun x : ℂ => x ^ M *
        (∑ p ∈ s, gammaAffineJetEval branch n (C p) x))
      (𝓝[≠] 0)
      (𝓝 (∑ p ∈ s,
        if p.1 + (reciprocalBellCovariantTransform n (C p)).totalDegree = M then
          reciprocalBellNativeTopResidueValue branch n p.1 p.2 (C p) else 0)) := by
    simpa only [Finset.mul_sum] using hlim
  have hlimitEq :
      (∑ p ∈ s,
        if p.1 + (reciprocalBellCovariantTransform n (C p)).totalDegree = M then
          reciprocalBellNativeTopResidueValue branch n p.1 p.2 (C p) else 0) =
      reciprocalBellNativeTopResidueValueSum branch n P := by
    dsimp [s, C, M, reciprocalBellNativeTopResidueValueSum,
      reciprocalBellBihomogeneousTopSupport,
      reciprocalBellBihomogeneousPoleDegree]
    rw [Finset.sum_filter]
    rfl
  rw [hlimitEq] at hnormalized
  change Tendsto
    (fun x : ℂ => x ^ M * gammaAffineJetEval branch n P x)
    (𝓝[≠] 0) (𝓝 (reciprocalBellNativeTopResidueValueSum branch n P))
  apply hnormalized.congr'
  apply Filter.Eventually.of_forall
  intro x
  rw [gammaAffineJetEval_eq_sum_bihomogeneousSupport branch n P]

/-- The canonical maximum is a uniform pole cutoff on every Gamma branch. -/
theorem neg_reciprocalBellNativePoleDegree_le_meromorphicOrderAt_gammaAffineJetEval
    (branch n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    ((-(reciprocalBellNativePoleDegree n P : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (gammaAffineJetEval branch n P) 0 := by
  apply neg_nat_le_meromorphicOrderAt_of_tendsto_pow_mul
    (reciprocalBellNativePoleDegree n P)
    (meromorphicAt_gammaAffineJetEval branch n P)
  simpa only [sub_zero] using
    tendsto_pow_reciprocalBellNativePoleDegree_mul_gammaAffineJetEval branch n P

/-- The finite cross-particle noncancellation law reflects to an actual
nonzero Gamma pole-index germ. -/
theorem finset_sum_reciprocalBellNativeTopResidueGerm_ne_zero
    {ι : Type*} {n M : ℕ} (s : Finset ι)
    (D W : ι → ℕ) (P : ι → MvPolynomial (Fin (n + 2)) ℂ)
    (hs : s.Nonempty)
    (hDW : Set.InjOn (fun i => (D i, W i)) s)
    (hD : ∀ i ∈ s, (P i).IsHomogeneous (D i))
    (hW : ∀ i ∈ s,
      (P i).IsWeightedHomogeneous (inverseJetDerivativeWeight n) (W i))
    (hP : ∀ i ∈ s, P i ≠ 0)
    (hM : ∀ i ∈ s,
      D i + (reciprocalBellCovariantTransform n (P i)).totalDegree = M) :
    ∑ i ∈ s, reciprocalBellNativeTopResidueGerm n (D i) (W i) (P i) ≠ 0 := by
  have himage := gammaPoleScaleAndCovariantResidueLaurentEval_injective.ne
    (finset_sum_reciprocalBellNativeTopResidueSymbol_ne_zero
      s D W P hs hDW hD hW hP hM)
  simpa [reciprocalBellNativeTopResidueGerm] using himage

/-- Every finite noncancelling top layer is detected arbitrarily far along
the genuine Gamma pole tower. -/
theorem exists_cofinal_finset_sum_reciprocalBellNativeTopResidueValue_ne_zero
    {ι : Type*} {n M : ℕ} (s : Finset ι)
    (D W : ι → ℕ) (P : ι → MvPolynomial (Fin (n + 2)) ℂ)
    (hs : s.Nonempty)
    (hDW : Set.InjOn (fun i => (D i, W i)) s)
    (hD : ∀ i ∈ s, (P i).IsHomogeneous (D i))
    (hW : ∀ i ∈ s,
      (P i).IsWeightedHomogeneous (inverseJetDerivativeWeight n) (W i))
    (hP : ∀ i ∈ s, P i ≠ 0)
    (hM : ∀ i ∈ s,
      D i + (reciprocalBellCovariantTransform n (P i)).totalDegree = M)
    (B : ℕ) :
    ∃ branch : ℕ, B ≤ branch ∧
      ∑ i ∈ s, reciprocalBellNativeTopResidueValue branch n (D i) (W i) (P i) ≠ 0 := by
  have hgerm := finset_sum_reciprocalBellNativeTopResidueGerm_ne_zero
    s D W P hs hDW hD hW hP hM
  have hreflection :
      ∑ i ∈ s, reciprocalBellNativeTopResidueGerm n (D i) (W i) (P i) =
        ((fun N : ℕ => ∑ i ∈ s,
          reciprocalBellNativeTopResidueValue (N - 1) n (D i) (W i) (P i) :
            ℕ → ℂ) : NatGerm) := by
    simp_rw [reciprocalBellNativeTopResidueGerm_eq_sequence]
    change ∑ i ∈ s, (Filter.Germ.coeRingHom Filter.atTop)
        (fun N : ℕ =>
          reciprocalBellNativeTopResidueValue (N - 1) n (D i) (W i) (P i)) = _
    rw [← map_sum]
    apply congrArg (Filter.Germ.coeRingHom Filter.atTop)
    funext N
    simp
  have hsequence :
      ((fun N : ℕ => ∑ i ∈ s,
        reciprocalBellNativeTopResidueValue (N - 1) n (D i) (W i) (P i) :
          ℕ → ℂ) : NatGerm) ≠ 0 := by
    rwa [hreflection] at hgerm
  by_contra hdetect
  simp only [not_exists, not_and, not_not] at hdetect
  apply hsequence
  rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
  exact Filter.eventually_atTop.2 ⟨B + 1, fun N hN =>
    hdetect (N - 1) (by omega)⟩

/-- **Finite bihomogeneous top-layer pole law.** Distinct source bidegrees
with a common reciprocal-Bell pole degree have a noncancelling sum on
arbitrarily remote Gamma branches, so the sum has that exact native pole
order. -/
theorem exists_cofinal_meromorphicOrderAt_finset_sum_gammaAffineJetEval
    {ι : Type*} {n M : ℕ} (s : Finset ι)
    (D W : ι → ℕ) (P : ι → MvPolynomial (Fin (n + 2)) ℂ)
    (hs : s.Nonempty)
    (hDW : Set.InjOn (fun i => (D i, W i)) s)
    (hD : ∀ i ∈ s, (P i).IsHomogeneous (D i))
    (hW : ∀ i ∈ s,
      (P i).IsWeightedHomogeneous (inverseJetDerivativeWeight n) (W i))
    (hP : ∀ i ∈ s, P i ≠ 0)
    (hM : ∀ i ∈ s,
      D i + (reciprocalBellCovariantTransform n (P i)).totalDegree = M)
    (B : ℕ) :
    ∃ branch : ℕ, B ≤ branch ∧
      meromorphicOrderAt
        (fun x => ∑ i ∈ s, gammaAffineJetEval branch n (P i) x) 0 =
          ((-(M : ℤ) : ℤ) : WithTop ℤ) := by
  classical
  obtain ⟨branch, hbranch, hres⟩ :=
    exists_cofinal_finset_sum_reciprocalBellNativeTopResidueValue_ne_zero
      s D W P hs hDW hD hW hP hM B
  refine ⟨branch, hbranch, ?_⟩
  have hmero : MeromorphicAt
      (fun x => ∑ i ∈ s, gammaAffineJetEval branch n (P i) x) 0 := by
    apply meromorphicAt_finset_sum s
    intro i hi
    exact meromorphicAt_gammaAffineJetEval_of_bihomogeneous branch
      (hD i hi) (hW i hi)
  have hterm : ∀ i ∈ s,
      Tendsto
        (fun x : ℂ => x ^ M * gammaAffineJetEval branch n (P i) x)
        (𝓝[≠] 0)
        (𝓝 (reciprocalBellNativeTopResidueValue branch n (D i) (W i) (P i))) := by
    intro i hi
    have hlim := tendsto_pow_add_reciprocalBellDegree_mul_gammaAffineJetEval
      branch (hD i hi) (hW i hi)
    rw [hM i hi] at hlim
    simpa [reciprocalBellNativeTopResidueValue] using hlim
  have hlim := tendsto_finsetSum s hterm
  have hsumlim :
      Tendsto
        (fun x : ℂ => x ^ M *
          (∑ i ∈ s, gammaAffineJetEval branch n (P i) x))
        (𝓝[≠] 0)
        (𝓝 (∑ i ∈ s,
          reciprocalBellNativeTopResidueValue branch n (D i) (W i) (P i))) := by
    simpa only [Finset.mul_sum] using hlim
  apply meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul M hmero hres
  simpa only [sub_zero] using hsumlim

/-- **Canonical all-sector native Gamma-pole law.** Every nonzero
constant-coefficient Gamma jet polynomial has, on arbitrarily remote pole
branches, exact order equal to the negative maximum of `D+E` over its
canonical particle-degree/derivative-weight sectors.  Cross-sector
cancellation is impossible at that maximum. -/
theorem exists_cofinal_meromorphicOrderAt_gammaAffineJetEval
    {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P ≠ 0) (B : ℕ) :
    ∃ branch : ℕ, B ≤ branch ∧
      meromorphicOrderAt (gammaAffineJetEval branch n P) 0 =
        ((-(reciprocalBellNativePoleDegree n P : ℤ) : ℤ) : WithTop ℤ) := by
  classical
  let t := reciprocalBellBihomogeneousTopSupport n P
  let M := reciprocalBellNativePoleDegree n P
  let C : ℕ × ℕ → MvPolynomial (Fin (n + 2)) ℂ := fun p =>
    reciprocalBellBihomogeneousComponent n p.1 p.2 P
  have ht : t.Nonempty := by
    simpa [t] using reciprocalBellBihomogeneousTopSupport_nonempty hP
  have hinj : Set.InjOn (fun p : ℕ × ℕ => (p.1, p.2)) t := by
    intro p hp q hq hpq
    simpa only [Prod.eta] using hpq
  have hhom : ∀ p ∈ t, (C p).IsHomogeneous p.1 := by
    intro p hp
    exact reciprocalBellBihomogeneousComponent_isHomogeneous n p.1 p.2 P
  have hweight : ∀ p ∈ t,
      (C p).IsWeightedHomogeneous (inverseJetDerivativeWeight n) p.2 := by
    intro p hp
    exact reciprocalBellBihomogeneousComponent_isWeightedHomogeneous n p.1 p.2 P
  have hne : ∀ p ∈ t, C p ≠ 0 := by
    intro p hp
    have hpTop : p ∈ reciprocalBellBihomogeneousTopSupport n P := by
      simpa [t] using hp
    have hpSupport := (Finset.mem_filter.mp hpTop).1
    exact (Finset.mem_filter.mp hpSupport).2
  have htop : ∀ p ∈ t,
      p.1 + (reciprocalBellCovariantTransform n (C p)).totalDegree = M := by
    intro p hp
    have hpTop : p ∈ reciprocalBellBihomogeneousTopSupport n P := by
      simpa [t] using hp
    simpa [C, M, reciprocalBellBihomogeneousPoleDegree] using
      (Finset.mem_filter.mp hpTop).2
  obtain ⟨branch, hbranch, hres⟩ :=
    exists_cofinal_finset_sum_reciprocalBellNativeTopResidueValue_ne_zero
      t Prod.fst Prod.snd C ht hinj hhom hweight hne htop B
  refine ⟨branch, hbranch, ?_⟩
  have hres' : reciprocalBellNativeTopResidueValueSum branch n P ≠ 0 := by
    simpa [reciprocalBellNativeTopResidueValueSum, t, C] using hres
  change meromorphicOrderAt (gammaAffineJetEval branch n P) 0 =
    ((-(M : ℤ) : ℤ) : WithTop ℤ)
  apply meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul M
    (meromorphicAt_gammaAffineJetEval branch n P) hres'
  simpa only [sub_zero, M] using
    tendsto_pow_reciprocalBellNativePoleDegree_mul_gammaAffineJetEval branch n P

/-- **Unconditional all-sector tower filtration.** The maximum canonical
`D+E` degree is exactly the native Gamma-pole cutoff for every
constant-coefficient jet polynomial, including zero. -/
theorem gammaAffineJetTowerPoleCutoff_iff_reciprocalBellNativePoleDegree
    (n r : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    GammaAffineJetTowerPoleCutoff n r P ↔
      reciprocalBellNativePoleDegree n P ≤ r := by
  constructor
  · intro hcut
    by_cases hP : P = 0
    · subst P
      simp [reciprocalBellNativePoleDegree,
        reciprocalBellBihomogeneousSupport,
        reciprocalBellBihomogeneousComponent]
    · obtain ⟨branch, _, horder⟩ :=
        exists_cofinal_meromorphicOrderAt_gammaAffineJetEval hP 0
      have hbound := hcut branch
      rw [horder] at hbound
      have hboundInt : -(r : ℤ) ≤
          -(reciprocalBellNativePoleDegree n P : ℤ) := by
        exact_mod_cast hbound
      omega
  · intro hdegree branch
    have hcutInt : -(r : ℤ) ≤
        -(reciprocalBellNativePoleDegree n P : ℤ) := by
      omega
    have hcut : ((-(r : ℤ) : ℤ) : WithTop ℤ) ≤
        ((-(reciprocalBellNativePoleDegree n P : ℤ) : ℤ) : WithTop ℤ) := by
      exact_mod_cast hcutInt
    exact hcut.trans
      (neg_reciprocalBellNativePoleDegree_le_meromorphicOrderAt_gammaAffineJetEval
        branch n P)

/-- The arbitrary-source at-most-simple interface is the first level of the
canonical reciprocal-Bell filtration. -/
theorem gammaAffineJetTowerAtMostSimple_iff_reciprocalBellNativePoleDegree
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    GammaAffineJetTowerAtMostSimple n P ↔
      reciprocalBellNativePoleDegree n P ≤ 1 := by
  exact gammaAffineJetTowerPoleCutoff_iff_reciprocalBellNativePoleDegree n 1 P

/-- The arbitrary-source native pole-cutoff interface is closed under source
addition. -/
theorem gammaAffineJetTowerPoleCutoff_add
    (n r : ℕ) (P Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hP : GammaAffineJetTowerPoleCutoff n r P)
    (hQ : GammaAffineJetTowerPoleCutoff n r Q) :
    GammaAffineJetTowerPoleCutoff n r (P + Q) := by
  intro branch
  have hadd := meromorphicOrderAt_add
    (meromorphicAt_gammaAffineJetEval branch n P)
    (meromorphicAt_gammaAffineJetEval branch n Q)
  have hmin : ((-(r : ℤ) : ℤ) : WithTop ℤ) ≤
      min (meromorphicOrderAt (gammaAffineJetEval branch n P) 0)
        (meromorphicOrderAt (gammaAffineJetEval branch n Q) 0) :=
    le_min (hP branch) (hQ branch)
  have heval : gammaAffineJetEval branch n (P + Q) =
      gammaAffineJetEval branch n P + gammaAffineJetEval branch n Q := by
    funext x
    simp [gammaAffineJetEval]
  rw [heval]
  exact hmin.trans hadd

theorem gammaAffineJetTowerAtMostSimple_C
    (n : ℕ) (c : ℂ) :
    GammaAffineJetTowerAtMostSimple n
      (MvPolynomial.C c : MvPolynomial (Fin (n + 2)) ℂ) := by
  by_cases hc : c = 0
  · subst c
    apply (gammaAffineJetTowerAtMostSimple_iff_reciprocalBellNativePoleDegree n _).mpr
    simp [reciprocalBellNativePoleDegree, reciprocalBellBihomogeneousSupport,
      reciprocalBellBihomogeneousComponent]
  · apply (gammaAffineJetTowerAtMostSimple_iff_constant_or_undifferentiated
      (MvPolynomial.isHomogeneous_C (σ := Fin (n + 2)) c)
      (MvPolynomial.isWeightedHomogeneous_C (inverseJetDerivativeWeight n) c)
      (MvPolynomial.C_ne_zero.mpr hc)).mpr
    exact ⟨c, Or.inl rfl⟩

theorem gammaAffineJetTowerAtMostSimple_C_mul_X_zero
    (n : ℕ) (c : ℂ) :
    GammaAffineJetTowerAtMostSimple n
      (MvPolynomial.C c * MvPolynomial.X (0 : Fin (n + 2))) := by
  by_cases hc : c = 0
  · subst c
    simpa using gammaAffineJetTowerAtMostSimple_C n 0
  · have hW : (MvPolynomial.C c * MvPolynomial.X (0 : Fin (n + 2)) :
        MvPolynomial (Fin (n + 2)) ℂ).IsWeightedHomogeneous
          (inverseJetDerivativeWeight n) 0 := by
      simpa [inverseJetDerivativeWeight] using
        (MvPolynomial.isWeightedHomogeneous_C (inverseJetDerivativeWeight n) c).mul
          (MvPolynomial.isWeightedHomogeneous_X ℂ
            (inverseJetDerivativeWeight n) (0 : Fin (n + 2)))
    apply (gammaAffineJetTowerAtMostSimple_iff_constant_or_undifferentiated
      (MvPolynomial.isHomogeneous_C_mul_X c (0 : Fin (n + 2))) hW
      (mul_ne_zero (MvPolynomial.C_ne_zero.mpr hc)
        (MvPolynomial.X_ne_zero (R := ℂ) (0 : Fin (n + 2))))).mpr
    exact ⟨c, Or.inr rfl⟩

theorem finset_sum_eq_C_add_C_mul_X_zero_of_each
    {ι : Type*} (n : ℕ) (s : Finset ι)
    (F : ι → MvPolynomial (Fin (n + 2)) ℂ)
    (hF : ∀ i ∈ s, ∃ c : ℂ,
      F i = MvPolynomial.C c ∨
        F i = MvPolynomial.C c * MvPolynomial.X (0 : Fin (n + 2))) :
    ∃ a b : ℂ, ∑ i ∈ s, F i =
      MvPolynomial.C a +
        MvPolynomial.C b * MvPolynomial.X (0 : Fin (n + 2)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, 0, by simp⟩
  | @insert i t hit ih =>
      obtain ⟨c, hc | hc⟩ := hF i (by simp)
      · obtain ⟨a, b, hab⟩ := ih fun j hj => hF j (by simp [hj])
        refine ⟨c + a, b, ?_⟩
        rw [Finset.sum_insert hit, hc, hab, map_add]
        ring
      · obtain ⟨a, b, hab⟩ := ih fun j hj => hF j (by simp [hj])
        refine ⟨a, c + b, ?_⟩
        rw [Finset.sum_insert hit, hc, hab, map_add]
        ring

/-- **Unconditional arbitrary-source simple-pole classification.** A
constant-coefficient native Gamma jet polynomial has at most simple poles
on the whole tower exactly when it is affine in undifferentiated Gamma. -/
theorem gammaAffineJetTowerAtMostSimple_iff_affine_undifferentiated
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    GammaAffineJetTowerAtMostSimple n P ↔
      ∃ a b : ℂ, P = MvPolynomial.C a +
        MvPolynomial.C b * MvPolynomial.X (0 : Fin (n + 2)) := by
  classical
  constructor
  · intro hcut
    have hnative :=
      (gammaAffineJetTowerAtMostSimple_iff_reciprocalBellNativePoleDegree n P).mp hcut
    let s := reciprocalBellBihomogeneousSupport n P
    let C : ℕ × ℕ → MvPolynomial (Fin (n + 2)) ℂ := fun p =>
      reciprocalBellBihomogeneousComponent n p.1 p.2 P
    have hclass : ∀ p ∈ s, ∃ c : ℂ,
        C p = MvPolynomial.C c ∨
          C p = MvPolynomial.C c * MvPolynomial.X (0 : Fin (n + 2)) := by
      intro p hp
      have hpSupport : p ∈ reciprocalBellBihomogeneousSupport n P := by
        simpa [s] using hp
      have hp0 : C p ≠ 0 := by
        exact (Finset.mem_filter.mp hpSupport).2
      have hD := reciprocalBellBihomogeneousComponent_isHomogeneous n p.1 p.2 P
      have hW :=
        reciprocalBellBihomogeneousComponent_isWeightedHomogeneous n p.1 p.2 P
      have hpole : p.1 + (reciprocalBellCovariantTransform n (C p)).totalDegree ≤ 1 :=
        (by simpa [C, reciprocalBellBihomogeneousPoleDegree] using
          (reciprocalBellBihomogeneousPoleDegree_le hpSupport).trans hnative)
      have hsector : GammaAffineJetTowerAtMostSimple n (C p) :=
        (gammaAffineJetTowerAtMostSimple_iff hD hW hp0).mpr hpole
      exact (gammaAffineJetTowerAtMostSimple_iff_constant_or_undifferentiated
        hD hW hp0).mp hsector
    obtain ⟨a, b, hab⟩ := finset_sum_eq_C_add_C_mul_X_zero_of_each n s C hclass
    exact ⟨a, b, by
      rw [← sum_reciprocalBellBihomogeneousComponent_support n P]
      simpa [s, C] using hab⟩
  · rintro ⟨a, b, rfl⟩
    exact gammaAffineJetTowerPoleCutoff_add n 1 _ _
      (gammaAffineJetTowerAtMostSimple_C n a)
      (gammaAffineJetTowerAtMostSimple_C_mul_X_zero n b)

end

end GaloisForLFunctions
