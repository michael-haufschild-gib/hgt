import GaloisForLFunctions.RHTower.DeningerArithmeticSemisimpleHodge
import GaloisForLFunctions.RHTower.KRealKernelCokernel

/-!
# Oriented odd Hodge structure on semisimplified arithmetic cohomology

Functional-equation reflection has no fixed point on the Xi divisor: in centered coordinates it
is `a ↦ -a`, and `a = 0` is not a Xi zero.  Orient each two-point orbit by the lexicographic
positive half-plane.  The resulting sign changes under reflection.

Inserting this sign into the reflected divisor pairing makes the degree-one cup form alternating.
Inserting the same sign into the positive ordinary/compact-support identification makes Hodge star
odd, while cup followed by star remains the standard positive `ell²` metric.  This supplies the
correct graded-commutative/odd form of Deninger's weight-one Hodge data.

Frobenius obeys the cup derivation law unconditionally.  Its commutation with the odd Hodge star
is exactly RH.  No zero-location, positivity, or simplicity premise is used in the construction.
-/

open Complex
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/--
Canonical orientation sign of a functional-equation orbit, using the lexicographic positive
half-plane in centered spectral coordinates.
-/
def deningerArithmeticFEOrientation (q : XiZeroCopy) : ℂ :=
  if 0 < (xiSpectralPoint q).re then 1
  else if (xiSpectralPoint q).re < 0 then -1
  else if 0 < (xiSpectralPoint q).im then 1
  else -1

theorem deningerArithmeticFEOrientation_sq (q : XiZeroCopy) :
    deningerArithmeticFEOrientation q *
        deningerArithmeticFEOrientation q = 1 := by
  simp only [deningerArithmeticFEOrientation]
  split_ifs <;> ring

theorem deningerArithmeticFEOrientation_ne_zero (q : XiZeroCopy) :
    deningerArithmeticFEOrientation q ≠ 0 := by
  intro h
  have hsq := deningerArithmeticFEOrientation_sq q
  rw [h, zero_mul] at hsq
  exact zero_ne_one hsq

@[simp]
theorem deningerArithmeticFEOrientation_conj (q : XiZeroCopy) :
    (starRingEnd ℂ) (deningerArithmeticFEOrientation q) =
      deningerArithmeticFEOrientation q := by
  simp only [deningerArithmeticFEOrientation]
  split_ifs <;> simp

/-- Functional-equation reflection reverses the canonical orbit orientation. -/
theorem deningerArithmeticFEOrientation_reflect (q : XiZeroCopy) :
    deningerArithmeticFEOrientation (xiZeroCopyReflectEquiv q) =
      -deningerArithmeticFEOrientation q := by
  let a := xiSpectralPoint q
  have ha0 : a ≠ 0 := xiSpectralPoint_ne_zero q
  have hcoords : a.re ≠ 0 ∨ a.im ≠ 0 := by
    by_contra h
    push Not at h
    apply ha0
    exact Complex.ext h.1 h.2
  rw [deningerArithmeticFEOrientation,
    deningerArithmeticFEOrientation, xiSpectralPoint_reflect]
  simp only [Complex.neg_re, Complex.neg_im]
  by_cases hrepos : 0 < a.re
  · have hnrepos : ¬0 < -a.re := by linarith
    have hnrelt : -a.re < 0 := by linarith
    simp [a, hrepos, hnrepos, hnrelt]
  · by_cases hrelt : a.re < 0
    · have hnrepos : 0 < -a.re := by linarith
      simp [a, hrepos, hrelt, hnrepos]
    · have hre : a.re = 0 := by linarith
      have him0 : a.im ≠ 0 := hcoords.resolve_left (by simpa [hre])
      by_cases himpos : 0 < a.im
      · have hnimpos : ¬0 < -a.im := by linarith
        have hnimlt : -a.im < 0 := by linarith
        simp [a, hre, himpos, hnimpos, hnimlt]
      · have himlt : a.im < 0 := lt_of_le_of_ne
          (le_of_not_gt himpos) him0
        have hnimpos : 0 < -a.im := by linarith
        simp [a, hre, himpos, himlt, hnimpos]

/-- Functional-equation reflection has no fixed multiplicity copy. -/
theorem xiZeroCopyReflectEquiv_ne (q : XiZeroCopy) :
    xiZeroCopyReflectEquiv q ≠ q := by
  intro h
  have hspectral := congrArg xiSpectralPoint h
  rw [xiSpectralPoint_reflect] at hspectral
  have hzero : xiSpectralPoint q = 0 := by
    linear_combination (-1 / 2 : ℂ) * hspectral
  exact xiSpectralPoint_ne_zero q hzero

/-- Alternating oriented cup product followed by the degree-two trace. -/
def deningerArithmeticGradedOrientedCup :
    LinearMap.BilinForm ℂ DeningerArithmeticGradedH1 :=
  deningerArithmeticGradedPoincare.comp
    (finsuppDiagonal deningerArithmeticFEOrientation)
    LinearMap.id

/-- Coordinate-sum formula for the oriented cup product. -/
theorem deningerArithmeticGradedOrientedCup_eq_sum
    (a b : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedOrientedCup a b =
      a.sum fun q c =>
        c * deningerArithmeticFEOrientation q *
          b (xiZeroCopyReflectEquiv q) := by
  classical
  induction a using Finsupp.induction with
  | zero =>
      simp [deningerArithmeticGradedOrientedCup]
  | single_add q c a hq _hc ih =>
      rw [map_add, LinearMap.add_apply,
        Finsupp.sum_add_index' (fun _ => by ring) (fun _ _ _ => by ring)]
      have hsingle :
          deningerArithmeticGradedOrientedCup (Finsupp.single q c) b =
            c * deningerArithmeticFEOrientation q *
              b (xiZeroCopyReflectEquiv q) := by
        rw [deningerArithmeticGradedOrientedCup,
          LinearMap.BilinForm.comp_apply, LinearMap.id_apply,
          finsuppDiagonal_single, deningerArithmeticGradedPoincare,
          deningerDivisorCupTrace_single_left]
        ring
      rw [hsingle, ih]
      simp

@[simp]
theorem deningerArithmeticGradedOrientedCup_single_left
    (q : XiZeroCopy) (c : ℂ) (b : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedOrientedCup (Finsupp.single q c) b =
      c * deningerArithmeticFEOrientation q *
        b (xiZeroCopyReflectEquiv q) := by
  rw [deningerArithmeticGradedOrientedCup, LinearMap.BilinForm.comp_apply,
    LinearMap.id_apply,
    finsuppDiagonal_single, deningerArithmeticGradedPoincare,
    deningerDivisorCupTrace_single_left]
  ring

@[simp]
theorem deningerArithmeticGradedOrientedCup_single_right
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) (c : ℂ) :
    deningerArithmeticGradedOrientedCup a (Finsupp.single q c) =
      deningerArithmeticFEOrientation (xiZeroCopyReflectEquiv q) *
        a (xiZeroCopyReflectEquiv q) * c := by
  rw [deningerArithmeticGradedOrientedCup, LinearMap.BilinForm.comp_apply,
    LinearMap.id_apply,
    deningerArithmeticGradedPoincare,
    deningerDivisorCupTrace_single_right, finsuppDiagonal_apply]

/-- Oriented degree-one cup product is skew-symmetric against a coordinate vector. -/
private theorem deningerArithmeticGradedOrientedCup_single_skew
    (q : XiZeroCopy) (c : ℂ) (a : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedOrientedCup (Finsupp.single q c) a +
      deningerArithmeticGradedOrientedCup a (Finsupp.single q c) = 0 := by
  rw [deningerArithmeticGradedOrientedCup_single_left,
    deningerArithmeticGradedOrientedCup_single_right,
    deningerArithmeticFEOrientation_reflect]
  ring

/-- The oriented degree-one cup product is alternating. -/
theorem deningerArithmeticGradedOrientedCup_isAlt :
    deningerArithmeticGradedOrientedCup.IsAlt := by
  intro a
  induction a using Finsupp.induction with
  | zero =>
      simp [deningerArithmeticGradedOrientedCup]
  | single_add q c a hq _hc ih =>
      let e := Finsupp.single q c
      have hee :
          deningerArithmeticGradedOrientedCup e e = 0 := by
        rw [deningerArithmeticGradedOrientedCup_single_left]
        simp [e, xiZeroCopyReflectEquiv_ne q]
      have hcross :=
        deningerArithmeticGradedOrientedCup_single_skew q c a
      change
        deningerArithmeticGradedOrientedCup (e + a) (e + a) = 0
      simp only [map_add, LinearMap.add_apply]
      linear_combination hee + hcross + ih

/-- The oriented degree-one cup product is nondegenerate. -/
theorem deningerArithmeticGradedOrientedCup_nondegenerate :
    deningerArithmeticGradedOrientedCup.Nondegenerate := by
  constructor
  · intro a ha
    ext q
    have h := ha (Finsupp.single (xiZeroCopyReflectEquiv q) 1)
    rw [deningerArithmeticGradedOrientedCup_single_right,
      xiZeroCopyReflectEquiv_apply_apply] at h
    have h' :
        deningerArithmeticFEOrientation q * a q = 0 := by
      linear_combination h
    simpa using
      (mul_eq_zero.mp h').resolve_left
        (deningerArithmeticFEOrientation_ne_zero q)
  · intro b hb
    ext q
    have h := hb (Finsupp.single (xiZeroCopyReflectEquiv q) 1)
    rw [deningerArithmeticGradedOrientedCup_single_left,
      xiZeroCopyReflectEquiv_apply_apply, one_mul] at h
    exact (mul_eq_zero.mp h).resolve_left
      (deningerArithmeticFEOrientation_ne_zero
        (xiZeroCopyReflectEquiv q))

/-- Conjugate-linear oriented Hodge operator. -/
def deningerArithmeticGradedOrientedHodgeSigma :
    DeningerArithmeticGradedH1 →ₛₗ[starRingEnd ℂ]
      DeningerArithmeticGradedH1 where
  toFun a :=
    finsuppDiagonal
      (fun q => -deningerArithmeticFEOrientation q)
      (deningerArithmeticGradedHodgeStar a)
  map_add' a b := by
    ext q
    simp [finsuppDiagonal_apply,
      deningerArithmeticGradedHodgeStar_apply]
  map_smul' c a := by
    ext q
    simp only [finsuppDiagonal_apply,
      deningerArithmeticGradedHodgeStar_apply,
      Finsupp.smul_apply, map_mul, smul_eq_mul]
    ring

@[simp]
theorem deningerArithmeticGradedOrientedHodgeSigma_apply
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    deningerArithmeticGradedOrientedHodgeSigma a q =
      -deningerArithmeticFEOrientation q *
        (starRingEnd ℂ)
          (a (xiZeroCopyReflectEquiv q)) := by
  change
    finsuppDiagonal
        (fun q => -deningerArithmeticFEOrientation q)
        (deningerArithmeticGradedHodgeStar a) q =
      -deningerArithmeticFEOrientation q *
        (starRingEnd ℂ) (a (xiZeroCopyReflectEquiv q))
  rw [
    finsuppDiagonal_apply,
    deningerArithmeticGradedHodgeStar_apply]

/-- Genuine odd Hodge structure: its conjugate-linear operator squares to `-1`. -/
def deningerArithmeticGradedOrientedHodge :
    KRealStructure true DeningerArithmeticGradedH1 where
  sigma := deningerArithmeticGradedOrientedHodgeSigma
  sq a := by
    ext q
    rw [deningerArithmeticGradedOrientedHodgeSigma_apply,
      deningerArithmeticGradedOrientedHodgeSigma_apply,
      xiZeroCopyReflectEquiv_apply_apply,
      map_mul, map_neg,
      deningerArithmeticFEOrientation_conj,
      deningerArithmeticFEOrientation_reflect,
      starRingEnd_self_apply]
    change
      -deningerArithmeticFEOrientation q *
          (- -deningerArithmeticFEOrientation q * a q) =
        -a q
    have heps := deningerArithmeticFEOrientation_sq q
    linear_combination -a q * heps

@[simp]
theorem deningerArithmeticGradedOrientedHodge_apply
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    deningerArithmeticGradedOrientedHodge.sigma a q =
      -deningerArithmeticFEOrientation q *
        (starRingEnd ℂ) (a (xiZeroCopyReflectEquiv q)) :=
  deningerArithmeticGradedOrientedHodgeSigma_apply a q

/-- Cup followed by the odd Hodge star is the coefficient norm-square sum. -/
theorem deningerArithmeticGradedOrientedCup_hodge_self
    (a : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedOrientedCup a
        (deningerArithmeticGradedOrientedHodge.sigma a) =
      a.sum fun _ c => (Complex.normSq c : ℂ) := by
  rw [deningerArithmeticGradedOrientedCup_eq_sum]
  apply Finsupp.sum_congr
  intro q hq
  rw [deningerArithmeticGradedOrientedHodge_apply,
    xiZeroCopyReflectEquiv_apply_apply,
    deningerArithmeticFEOrientation_reflect]
  have heps := deningerArithmeticFEOrientation_sq q
  calc
    a q * deningerArithmeticFEOrientation q *
          (- -deningerArithmeticFEOrientation q *
            (starRingEnd ℂ) (a q)) =
        (deningerArithmeticFEOrientation q *
            deningerArithmeticFEOrientation q) *
          (a q * (starRingEnd ℂ) (a q)) := by ring
    _ = (Complex.normSq (a q) : ℂ) := by
      rw [heps, one_mul, Complex.mul_conj]

/-- Real diagonal of the oriented Hodge metric. -/
theorem deningerArithmeticGradedOrientedCup_hodge_self_re
    (a : DeningerArithmeticGradedH1) :
    (deningerArithmeticGradedOrientedCup a
        (deningerArithmeticGradedOrientedHodge.sigma a)).re =
      a.sum fun _ c => Complex.normSq c := by
  rw [deningerArithmeticGradedOrientedCup_hodge_self]
  simp [Finsupp.sum]

/-- The oriented Hodge metric is positive definite. -/
theorem deningerArithmeticGradedOrientedHodge_positive
    {a : DeningerArithmeticGradedH1} (ha : a ≠ 0) :
    0 < (deningerArithmeticGradedOrientedCup a
      (deningerArithmeticGradedOrientedHodge.sigma a)).re := by
  rw [deningerArithmeticGradedOrientedCup_hodge_self_re]
  apply Finsupp.sum_pos
  · intro q hq
    exact Complex.normSq_pos.mpr (Finsupp.mem_support_iff.mp hq)
  · exact ha

/-- Frobenius and the orientation diagonal commute. -/
private theorem deningerArithmeticGradedTheta_orientationDiagonal
    (a : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedTheta
        (finsuppDiagonal deningerArithmeticFEOrientation a) =
      finsuppDiagonal deningerArithmeticFEOrientation
        (deningerArithmeticGradedTheta a) := by
  ext q
  simp only [deningerArithmeticGradedTheta, deningerDivisorTheta,
    finsuppDiagonal_apply]
  ring

/-- The oriented cup product obeys Deninger's weight-one derivation law. -/
theorem deningerArithmeticGradedTheta_orientedCup
    (a b : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedOrientedCup
          (deningerArithmeticGradedTheta a) b +
        deningerArithmeticGradedOrientedCup a
          (deningerArithmeticGradedTheta b) =
      deningerArithmeticGradedOrientedCup a b := by
  unfold deningerArithmeticGradedOrientedCup
  simp only [LinearMap.BilinForm.comp_apply, LinearMap.id_apply]
  change
    deningerArithmeticGradedPoincare
          (finsuppDiagonal deningerArithmeticFEOrientation
            (deningerArithmeticGradedTheta a)) b +
        deningerArithmeticGradedPoincare
          (finsuppDiagonal deningerArithmeticFEOrientation a)
          (deningerArithmeticGradedTheta b) =
      deningerArithmeticGradedPoincare
        (finsuppDiagonal deningerArithmeticFEOrientation a) b
  rw [← deningerArithmeticGradedTheta_orientationDiagonal]
  exact deningerArithmeticGradedTheta_poincare
    (finsuppDiagonal deningerArithmeticFEOrientation a) b

/-- Exact coordinate defect for Frobenius and the genuine odd Hodge star. -/
theorem deningerArithmeticGradedTheta_orientedHodge_defect
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    (deningerArithmeticGradedTheta
        (deningerArithmeticGradedOrientedHodge.sigma a)) q -
      deningerArithmeticGradedOrientedHodge.sigma
        (deningerArithmeticGradedTheta a) q =
      -deningerArithmeticFEOrientation q *
        (deningerDivisorThetaEigen q -
          (starRingEnd ℂ)
            (deningerDivisorThetaEigen
              (xiZeroCopyReflectEquiv q))) *
        (starRingEnd ℂ) (a (xiZeroCopyReflectEquiv q)) := by
  simp only [deningerArithmeticGradedTheta, deningerDivisorTheta,
    finsuppDiagonal_apply,
    deningerArithmeticGradedOrientedHodge_apply, map_mul]
  ring

/-- Frobenius compatibility of the genuine odd Hodge star is exactly RH. -/
theorem deningerArithmeticGradedTheta_orientedHodge_iff_riemannHypothesis :
    (∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGradedTheta
          (deningerArithmeticGradedOrientedHodge.sigma a) =
        deningerArithmeticGradedOrientedHodge.sigma
          (deningerArithmeticGradedTheta a)) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    rw [← deningerArithmeticGradedTheta_hodgeStar_iff_riemannHypothesis]
    intro a
    ext q
    have hq := congrArg
      (fun x : DeningerArithmeticGradedH1 => x q) (h a)
    have horient := deningerArithmeticFEOrientation_ne_zero q
    simp only [deningerArithmeticGradedTheta, deningerDivisorTheta,
      finsuppDiagonal_apply,
      deningerArithmeticGradedOrientedHodge_apply,
      deningerArithmeticGradedHodgeStar_apply, map_mul] at hq ⊢
    apply (mul_left_cancel₀ horient)
    linear_combination -hq
  · intro hRH a
    ext q
    have h := congrArg
      (fun x : DeningerArithmeticGradedH1 => x q)
      (deningerArithmeticGradedTheta_hodgeStar_of_riemannHypothesis
        hRH a)
    simp only [deningerArithmeticGradedTheta, deningerDivisorTheta,
      finsuppDiagonal_apply,
      deningerArithmeticGradedOrientedHodge_apply,
      deningerArithmeticGradedHodgeStar_apply, map_mul] at h ⊢
    linear_combination -deningerArithmeticFEOrientation q * h

/--
Exact algebraic Deninger Hodge package on multiplicity-exact semisimplified arithmetic `H¹`.
-/
theorem deningerArithmetic_orientedHodge_package :
    deningerArithmeticGradedOrientedCup.IsAlt ∧
    deningerArithmeticGradedOrientedCup.Nondegenerate ∧
    (∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGradedOrientedHodge.sigma
          (deningerArithmeticGradedOrientedHodge.sigma a) = -a) ∧
    (∀ {a : DeningerArithmeticGradedH1}, a ≠ 0 →
      0 < (deningerArithmeticGradedOrientedCup a
        (deningerArithmeticGradedOrientedHodge.sigma a)).re) ∧
    (∀ a b : DeningerArithmeticGradedH1,
      deningerArithmeticGradedOrientedCup
            (deningerArithmeticGradedTheta a) b +
          deningerArithmeticGradedOrientedCup a
            (deningerArithmeticGradedTheta b) =
        deningerArithmeticGradedOrientedCup a b) ∧
    ((∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGradedTheta
          (deningerArithmeticGradedOrientedHodge.sigma a) =
        deningerArithmeticGradedOrientedHodge.sigma
          (deningerArithmeticGradedTheta a)) ↔
      RiemannHypothesis) := by
  exact ⟨deningerArithmeticGradedOrientedCup_isAlt,
    deningerArithmeticGradedOrientedCup_nondegenerate,
    deningerArithmeticGradedOrientedHodge.sq,
    deningerArithmeticGradedOrientedHodge_positive,
    deningerArithmeticGradedTheta_orientedCup,
    deningerArithmeticGradedTheta_orientedHodge_iff_riemannHypothesis⟩

end

end RHTower
