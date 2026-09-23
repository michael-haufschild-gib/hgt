import GaloisForLFunctions.RHTower.DeningerArithmeticOrientedHodge
import GaloisForLFunctions.RHTower.DeningerDivisorClosedGenerator

/-!
# Oriented Hilbert Hodge structure for Deninger's arithmetic cohomology

This file completes the multiplicity-exact semisimple degree-one carrier from finite support to
the Hilbert space `XiDivisorL2`.  Functional-equation reflection and the canonical orbit
orientation define an antiunitary odd Hodge operator

`(J a)_q = -epsilon_q * conjugate(a_{R q})`.

The bilinear cup-trace form is `omega(a,b) = inner (J a) b`.  It is alternating and
nondegenerate, `J^(2 : ℕ) = -1`, and `omega(a, J a)` is the Hilbert norm square.  The maximal diagonal
Frobenius generator has a closed dense domain preserved by `J`, and the weight-one cup derivation
law holds there without any zero-location assumption.

Commutation of Frobenius with `J` is exactly the Riemann hypothesis.  Thus this module supplies
the closed Hilbert/Poincare/Hodge target required by Deninger's program while keeping the final
purity input explicit.
-/

open Complex
open HilbertSchmidt
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

@[simp]
theorem norm_deningerArithmeticFEOrientation (q : XiZeroCopy) :
    ‖deningerArithmeticFEOrientation q‖ = 1 := by
  simp only [deningerArithmeticFEOrientation]
  split_ifs <;> norm_num

/-- Odd oriented Hodge operator on the completed multiplicity-exact divisor carrier. -/
def deningerArithmeticOrientedHodgeLp (a : XiDivisorL2) : XiDivisorL2 :=
  ⟨fun q =>
      -deningerArithmeticFEOrientation q *
        (starRingEnd ℂ) (a (xiZeroCopyReflectEquiv q)),
    HilbertSchmidt.memℓp_of_sq
      ((xiZeroCopyReflectEquiv.summable_iff.mpr
        (HilbertSchmidt.summable_coe_sq a)).congr fun q => by
          simp)⟩

@[simp]
theorem deningerArithmeticOrientedHodgeLp_apply
    (a : XiDivisorL2) (q : XiZeroCopy) :
    deningerArithmeticOrientedHodgeLp a q =
      -deningerArithmeticFEOrientation q *
        (starRingEnd ℂ) (a (xiZeroCopyReflectEquiv q)) :=
  rfl

/-- The completed odd Hodge operator as a conjugate-linear map. -/
def deningerArithmeticOrientedHodgeLpSigma :
    XiDivisorL2 →ₛₗ[starRingEnd ℂ] XiDivisorL2 where
  toFun := deningerArithmeticOrientedHodgeLp
  map_add' a b := by
    ext q
    change
      -deningerArithmeticFEOrientation q *
          (starRingEnd ℂ)
            (a (xiZeroCopyReflectEquiv q) +
              b (xiZeroCopyReflectEquiv q)) =
        -deningerArithmeticFEOrientation q *
            (starRingEnd ℂ) (a (xiZeroCopyReflectEquiv q)) +
          -deningerArithmeticFEOrientation q *
            (starRingEnd ℂ) (b (xiZeroCopyReflectEquiv q))
    rw [map_add]
    ring
  map_smul' c a := by
    ext q
    change
      -deningerArithmeticFEOrientation q *
          (starRingEnd ℂ)
            (c * a (xiZeroCopyReflectEquiv q)) =
        (starRingEnd ℂ) c *
          (-deningerArithmeticFEOrientation q *
            (starRingEnd ℂ) (a (xiZeroCopyReflectEquiv q)))
    rw [map_mul]
    ring

/-- Genuine odd Real structure on the Hilbert completion: `J^(2 : ℕ) = -1`. -/
def deningerArithmeticOrientedHilbertHodge :
    KRealStructure true XiDivisorL2 where
  sigma := deningerArithmeticOrientedHodgeLpSigma
  sq a := by
    ext q
    change
      deningerArithmeticOrientedHodgeLp
          (deningerArithmeticOrientedHodgeLp a) q =
        kRealParityAction true a q
    rw [deningerArithmeticOrientedHodgeLp_apply,
      deningerArithmeticOrientedHodgeLp_apply,
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

/-- The completed odd Hodge operator is norm preserving. -/
theorem norm_deningerArithmeticOrientedHodgeLp (a : XiDivisorL2) :
    ‖deningerArithmeticOrientedHodgeLp a‖ = ‖a‖ := by
  have hsq :
      ‖deningerArithmeticOrientedHodgeLp a‖ ^ (2 : ℕ) = ‖a‖ ^ (2 : ℕ) := by
    rw [HilbertSchmidt.lp_norm_sq_eq, HilbertSchmidt.lp_norm_sq_eq]
    calc
      (∑' q : XiZeroCopy, ‖deningerArithmeticOrientedHodgeLp a q‖ ^ (2 : ℕ)) =
          ∑' q : XiZeroCopy, ‖a (xiZeroCopyReflectEquiv q)‖ ^ (2 : ℕ) := by
        apply tsum_congr
        intro q
        simp
      _ = ∑' q : XiZeroCopy, ‖a q‖ ^ (2 : ℕ) :=
        xiZeroCopyReflectEquiv.tsum_eq (fun q => ‖a q‖ ^ (2 : ℕ))
  nlinarith [norm_nonneg (deningerArithmeticOrientedHodgeLp a), norm_nonneg a]

/-- Antiunitary identity for the completed odd Hodge operator. -/
theorem inner_deningerArithmeticOrientedHodgeLp
    (a b : XiDivisorL2) :
    inner ℂ (deningerArithmeticOrientedHodgeLp a)
        (deningerArithmeticOrientedHodgeLp b) =
      inner ℂ b a := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  calc
    (∑' q : XiZeroCopy,
        inner ℂ (deningerArithmeticOrientedHodgeLp a q)
          (deningerArithmeticOrientedHodgeLp b q)) =
        ∑' q : XiZeroCopy,
          inner ℂ (b (xiZeroCopyReflectEquiv q))
            (a (xiZeroCopyReflectEquiv q)) := by
      apply tsum_congr
      intro q
      rw [deningerArithmeticOrientedHodgeLp_apply,
        deningerArithmeticOrientedHodgeLp_apply,
        RCLike.inner_apply, RCLike.inner_apply,
        map_mul, map_neg,
        deningerArithmeticFEOrientation_conj,
        starRingEnd_self_apply]
      have heps := deningerArithmeticFEOrientation_sq q
      calc
        -deningerArithmeticFEOrientation q *
              (starRingEnd ℂ) (b (xiZeroCopyReflectEquiv q)) *
            (-deningerArithmeticFEOrientation q *
              a (xiZeroCopyReflectEquiv q)) =
            (deningerArithmeticFEOrientation q *
                deningerArithmeticFEOrientation q) *
              (a (xiZeroCopyReflectEquiv q) *
                (starRingEnd ℂ) (b (xiZeroCopyReflectEquiv q))) := by ring
        _ = a (xiZeroCopyReflectEquiv q) *
              (starRingEnd ℂ) (b (xiZeroCopyReflectEquiv q)) := by
          rw [heps, one_mul]
    _ = ∑' q : XiZeroCopy, inner ℂ (b q) (a q) :=
      xiZeroCopyReflectEquiv.tsum_eq (fun q => inner ℂ (b q) (a q))

/-- Completed degree-one cup product followed by the endpoint trace. -/
def deningerArithmeticOrientedHilbertCup :
    LinearMap.BilinForm ℂ XiDivisorL2 :=
  LinearMap.mk₂ ℂ
    (fun a b => inner ℂ (deningerArithmeticOrientedHodgeLp a) b)
    (by
      intro a a' b
      change
        inner ℂ (deningerArithmeticOrientedHodgeLp (a + a')) b =
          inner ℂ (deningerArithmeticOrientedHodgeLp a) b +
            inner ℂ (deningerArithmeticOrientedHodgeLp a') b
      rw [show
        deningerArithmeticOrientedHodgeLp (a + a') =
          deningerArithmeticOrientedHodgeLp a +
            deningerArithmeticOrientedHodgeLp a' from
        deningerArithmeticOrientedHodgeLpSigma.map_add a a',
        inner_add_left])
    (by
      intro c a b
      change
        inner ℂ (deningerArithmeticOrientedHodgeLp (c • a)) b =
          c • inner ℂ (deningerArithmeticOrientedHodgeLp a) b
      have hJ :
        deningerArithmeticOrientedHodgeLp (c • a) =
          (starRingEnd ℂ) c • deningerArithmeticOrientedHodgeLp a := by
        ext q
        change
          -deningerArithmeticFEOrientation q *
              (starRingEnd ℂ)
                (c * a (xiZeroCopyReflectEquiv q)) =
            (starRingEnd ℂ) c *
              (-deningerArithmeticFEOrientation q *
                (starRingEnd ℂ) (a (xiZeroCopyReflectEquiv q)))
        rw [map_mul]
        ring
      rw [hJ, inner_smul_left]
      simp)
    (by
      intro a b b'
      change
        inner ℂ (deningerArithmeticOrientedHodgeLp a) (b + b') =
          inner ℂ (deningerArithmeticOrientedHodgeLp a) b +
            inner ℂ (deningerArithmeticOrientedHodgeLp a) b'
      rw [inner_add_right])
    (by
      intro c a b
      change
        inner ℂ (deningerArithmeticOrientedHodgeLp a) (c • b) =
          c • inner ℂ (deningerArithmeticOrientedHodgeLp a) b
      rw [inner_smul_right]
      simp [smul_eq_mul])

@[simp]
theorem deningerArithmeticOrientedHilbertCup_apply
    (a b : XiDivisorL2) :
    deningerArithmeticOrientedHilbertCup a b =
      inner ℂ (deningerArithmeticOrientedHodgeLp a) b :=
  rfl

/-- Absolutely summable coordinate formula for the completed cup product. -/
theorem summable_deningerArithmeticOrientedHilbertCup
    (a b : XiDivisorL2) :
    Summable (fun q : XiZeroCopy =>
      -deningerArithmeticFEOrientation q *
        a (xiZeroCopyReflectEquiv q) * b q) := by
  exact (lp.summable_inner (deningerArithmeticOrientedHodgeLp a) b).congr
    (fun q => by
      rw [deningerArithmeticOrientedHodgeLp_apply, RCLike.inner_apply,
        map_mul, map_neg,
        deningerArithmeticFEOrientation_conj,
        starRingEnd_self_apply]
      ring)

theorem deningerArithmeticOrientedHilbertCup_eq_tsum
    (a b : XiDivisorL2) :
    deningerArithmeticOrientedHilbertCup a b =
      ∑' q : XiZeroCopy,
        -deningerArithmeticFEOrientation q *
          a (xiZeroCopyReflectEquiv q) * b q := by
  rw [deningerArithmeticOrientedHilbertCup_apply, lp.inner_eq_tsum]
  apply tsum_congr
  intro q
  rw [deningerArithmeticOrientedHodgeLp_apply, RCLike.inner_apply,
    map_mul, map_neg,
    deningerArithmeticFEOrientation_conj,
    starRingEnd_self_apply]
  ring

/-- Cup followed by Hodge star is the Hilbert norm-square pairing. -/
theorem deningerArithmeticOrientedHilbertCup_hodge
    (a : XiDivisorL2) :
    deningerArithmeticOrientedHilbertCup a
        (deningerArithmeticOrientedHodgeLp a) =
      inner ℂ (deningerArithmeticOrientedHodgeLp a)
        (deningerArithmeticOrientedHodgeLp a) := by
  rfl

/-- Hilbert metric factors exactly as cup followed by odd Hodge star. -/
theorem deningerArithmeticOrientedHilbert_inner_eq_cup_hodge
    (a b : XiDivisorL2) :
    inner ℂ a b =
      deningerArithmeticOrientedHilbertCup b
        (deningerArithmeticOrientedHodgeLp a) := by
  rw [deningerArithmeticOrientedHilbertCup_apply,
    inner_deningerArithmeticOrientedHodgeLp]

/-- The completed degree-one cup product is alternating. -/
theorem deningerArithmeticOrientedHilbertCup_isAlt :
    deningerArithmeticOrientedHilbertCup.IsAlt := by
  intro a
  have hanti :=
    inner_deningerArithmeticOrientedHodgeLp a
      (deningerArithmeticOrientedHodgeLp a)
  have hsq := deningerArithmeticOrientedHilbertHodge.sq a
  change
    deningerArithmeticOrientedHodgeLp
        (deningerArithmeticOrientedHodgeLp a) = -a at hsq
  rw [hsq, inner_neg_right] at hanti
  rw [deningerArithmeticOrientedHilbertCup_apply]
  linear_combination (-1 / 2 : ℂ) * hanti

/-- The completed degree-one cup product is nondegenerate on both sides. -/
theorem deningerArithmeticOrientedHilbertCup_nondegenerate :
    deningerArithmeticOrientedHilbertCup.Nondegenerate := by
  constructor
  · intro a ha
    have h := ha (deningerArithmeticOrientedHodgeLp a)
    rw [deningerArithmeticOrientedHilbertCup_hodge] at h
    have hJa :
        deningerArithmeticOrientedHodgeLp a = 0 :=
      inner_self_eq_zero.mp h
    have hsq := deningerArithmeticOrientedHilbertHodge.sq a
    change
      deningerArithmeticOrientedHodgeLp
          (deningerArithmeticOrientedHodgeLp a) = -a at hsq
    have hJzero : deningerArithmeticOrientedHodgeLp (0 : XiDivisorL2) = 0 :=
      deningerArithmeticOrientedHodgeLpSigma.map_zero
    rw [hJa, hJzero] at hsq
    exact neg_eq_zero.mp hsq.symm
  · intro b hb
    have h := hb (deningerArithmeticOrientedHodgeLp b)
    rw [deningerArithmeticOrientedHilbertCup_apply] at h
    have hsq := deningerArithmeticOrientedHilbertHodge.sq b
    change
      deningerArithmeticOrientedHodgeLp
          (deningerArithmeticOrientedHodgeLp b) = -b at hsq
    rw [hsq, inner_neg_left] at h
    exact inner_self_eq_zero.mp (neg_eq_zero.mp h)

/-- Cup-Hodge metric is positive definite on the Hilbert completion. -/
theorem deningerArithmeticOrientedHilbertHodge_positive
    {a : XiDivisorL2} (ha : a ≠ 0) :
    0 < (deningerArithmeticOrientedHilbertCup a
      (deningerArithmeticOrientedHodgeLp a)).re := by
  rw [deningerArithmeticOrientedHilbertCup_hodge]
  have hnorm :
      (inner ℂ (deningerArithmeticOrientedHodgeLp a)
        (deningerArithmeticOrientedHodgeLp a)).re =
        ‖deningerArithmeticOrientedHodgeLp a‖ ^ (2 : ℕ) := by
    simpa using
      (InnerProductSpace.norm_sq_eq_re_inner
        (𝕜 := ℂ) (deningerArithmeticOrientedHodgeLp a)).symm
  rw [hnorm, norm_deningerArithmeticOrientedHodgeLp]
  exact sq_pos_of_pos (norm_pos_iff.mpr ha)

/-- Coordinate norm identity used to transport the maximal Frobenius domain through Hodge star. -/
private theorem norm_deningerDivisorTheta_orientedHodge_apply
    (x : deningerDivisorClosedTheta.domain) (q : XiZeroCopy) :
    ‖deningerDivisorThetaEigen q *
        deningerArithmeticOrientedHodgeLp (x : XiDivisorL2) q‖ =
      ‖((x : XiDivisorL2) - deningerDivisorClosedTheta x)
        (xiZeroCopyReflectEquiv q)‖ := by
  have hweight := deningerDivisorThetaEigen_add_reflect q
  have hcoord :
      (x : XiDivisorL2) (xiZeroCopyReflectEquiv q) -
          deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) *
            (x : XiDivisorL2) (xiZeroCopyReflectEquiv q) =
        deningerDivisorThetaEigen q *
          (x : XiDivisorL2) (xiZeroCopyReflectEquiv q) := by
    have hlambda :
        1 - deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) =
          deningerDivisorThetaEigen q := by
      rw [← hweight]
      ring
    calc
      (x : XiDivisorL2) (xiZeroCopyReflectEquiv q) -
            deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) *
              (x : XiDivisorL2) (xiZeroCopyReflectEquiv q) =
          (1 - deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q)) *
            (x : XiDivisorL2) (xiZeroCopyReflectEquiv q) := by ring
      _ = deningerDivisorThetaEigen q *
            (x : XiDivisorL2) (xiZeroCopyReflectEquiv q) := by
        rw [hlambda]
  change
    ‖deningerDivisorThetaEigen q *
        (-deningerArithmeticFEOrientation q *
          (starRingEnd ℂ)
            ((x : XiDivisorL2) (xiZeroCopyReflectEquiv q)))‖ =
      ‖(x : XiDivisorL2) (xiZeroCopyReflectEquiv q) -
        deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) *
          (x : XiDivisorL2) (xiZeroCopyReflectEquiv q)‖
  rw [hcoord]
  simp

/-- The completed odd Hodge operator preserves the maximal diagonal Frobenius domain. -/
theorem deningerArithmeticOrientedHodgeLp_mem_domain
    (x : deningerDivisorClosedTheta.domain) :
    deningerArithmeticOrientedHodgeLp (x : XiDivisorL2) ∈
      deningerDivisorClosedTheta.domain := by
  change Memℓp
    (fun q : XiZeroCopy =>
      deningerDivisorThetaEigen q *
        deningerArithmeticOrientedHodgeLp (x : XiDivisorL2) q) 2
  apply HilbertSchmidt.memℓp_of_sq
  exact
    (xiZeroCopyReflectEquiv.summable_iff.mpr
      (HilbertSchmidt.summable_coe_sq
        ((x : XiDivisorL2) - deningerDivisorClosedTheta x))).congr
      (fun q => by
        simp only [Function.comp_apply]
        rw [norm_deningerDivisorTheta_orientedHodge_apply])

/-- Hodge star lifted to the maximal Frobenius domain. -/
def deningerArithmeticOrientedHodgeDomain
    (x : deningerDivisorClosedTheta.domain) :
    deningerDivisorClosedTheta.domain :=
  ⟨deningerArithmeticOrientedHodgeLp (x : XiDivisorL2),
    deningerArithmeticOrientedHodgeLp_mem_domain x⟩

/-- Weight-one cup derivation law on the maximal closed-generator domain. -/
theorem deningerDivisorClosedTheta_orientedCup
    (x y : deningerDivisorClosedTheta.domain) :
    deningerArithmeticOrientedHilbertCup
          (deningerDivisorClosedTheta x) (y : XiDivisorL2) +
        deningerArithmeticOrientedHilbertCup
          (x : XiDivisorL2) (deningerDivisorClosedTheta y) =
      deningerArithmeticOrientedHilbertCup
        (x : XiDivisorL2) (y : XiDivisorL2) := by
  rw [deningerArithmeticOrientedHilbertCup_eq_tsum,
    deningerArithmeticOrientedHilbertCup_eq_tsum,
    deningerArithmeticOrientedHilbertCup_eq_tsum]
  have hleft :=
    summable_deningerArithmeticOrientedHilbertCup
      (deningerDivisorClosedTheta x) (y : XiDivisorL2)
  have hright :=
    summable_deningerArithmeticOrientedHilbertCup
      (x : XiDivisorL2) (deningerDivisorClosedTheta y)
  rw [← hleft.tsum_add hright]
  apply tsum_congr
  intro q
  rw [deningerDivisorClosedTheta_apply,
    deningerDivisorClosedTheta_apply]
  have hweight := deningerDivisorThetaEigen_add_reflect q
  linear_combination
    (-deningerArithmeticFEOrientation q *
      (x : XiDivisorL2) (xiZeroCopyReflectEquiv q) *
      (y : XiDivisorL2) q) * hweight

/-- Under RH, reflected Frobenius eigenvalues are complex conjugates. -/
private theorem deningerDivisorThetaEigen_reflect_eq_conj_of_rh
    (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) =
      (starRingEnd ℂ) (deningerDivisorThetaEigen q) := by
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  have hreflect := xiSpectralPoint_reflect q
  have htreflect :
      xiSpectralPoint (xiZeroCopyReflectEquiv q) = -(t : ℂ) := by
    rw [hreflect, ht]
  rw [deningerDivisorThetaEigen_eq, deningerDivisorThetaEigen_eq,
    ht, htreflect, map_add, map_mul]
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 :=
    map_ofNat (starRingEnd ℂ) 2
  simp [htwo]

/-- RH supplies Frobenius compatibility with odd Hodge star on the maximal domain. -/
theorem deningerDivisorClosedTheta_orientedHodge_of_riemannHypothesis
    (hRH : RiemannHypothesis)
    (x : deningerDivisorClosedTheta.domain) :
    deningerArithmeticOrientedHodgeLp (deningerDivisorClosedTheta x) =
      deningerDivisorClosedTheta (deningerArithmeticOrientedHodgeDomain x) := by
  ext q
  rw [deningerArithmeticOrientedHodgeLp_apply,
    deningerDivisorClosedTheta_apply,
    deningerDivisorClosedTheta_apply,
    deningerArithmeticOrientedHodgeDomain,
    deningerArithmeticOrientedHodgeLp_apply,
    map_mul]
  have hlambda :=
    deningerDivisorThetaEigen_reflect_eq_conj_of_rh hRH
      (xiZeroCopyReflectEquiv q)
  rw [xiZeroCopyReflectEquiv_apply_apply] at hlambda
  rw [hlambda]
  ring

/-- Frobenius-Hodge compatibility on the completed maximal domain forces RH. -/
theorem riemannHypothesis_of_deningerDivisorClosedTheta_orientedHodge
    (hcompat :
      ∀ x : deningerDivisorClosedTheta.domain,
        deningerArithmeticOrientedHodgeLp (deningerDivisorClosedTheta x) =
          deningerDivisorClosedTheta
            (deningerArithmeticOrientedHodgeDomain x)) :
    RiemannHypothesis := by
  have hreal :
      ∀ q : XiZeroCopy, ∃ t : ℝ, xiSpectralPoint q = (t : ℂ) := by
    intro q
    have hq := congrArg
      (fun v : XiDivisorL2 => v (xiZeroCopyReflectEquiv q))
      (hcompat (deningerDivisorClosedThetaEigenvector q))
    simp only [deningerArithmeticOrientedHodgeLp_apply,
      deningerDivisorClosedTheta_apply,
      deningerArithmeticOrientedHodgeDomain,
      deningerDivisorClosedThetaEigenvector,
      lpBasis_apply,
      xiZeroCopyReflectEquiv_apply_apply,
      map_mul] at hq
    simp at hq
    have horient :=
      deningerArithmeticFEOrientation_ne_zero
        (xiZeroCopyReflectEquiv q)
    have hlambda :
        deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) =
          (starRingEnd ℂ) (deningerDivisorThetaEigen q) := by
      have hzero :
          deningerArithmeticFEOrientation (xiZeroCopyReflectEquiv q) *
            ((starRingEnd ℂ) (deningerDivisorThetaEigen q) -
              deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q)) = 0 := by
        calc
          deningerArithmeticFEOrientation (xiZeroCopyReflectEquiv q) *
                ((starRingEnd ℂ) (deningerDivisorThetaEigen q) -
                  deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q)) =
              deningerArithmeticFEOrientation (xiZeroCopyReflectEquiv q) *
                  (starRingEnd ℂ) (deningerDivisorThetaEigen q) -
                deningerArithmeticFEOrientation (xiZeroCopyReflectEquiv q) *
                  deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) := by ring
          _ = deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) *
                deningerArithmeticFEOrientation (xiZeroCopyReflectEquiv q) -
              deningerArithmeticFEOrientation (xiZeroCopyReflectEquiv q) *
                deningerDivisorThetaEigen (xiZeroCopyReflectEquiv q) := by
            rw [hq]
          _ = 0 := by ring
      exact (sub_eq_zero.mp
        ((mul_eq_zero.mp hzero).resolve_left horient)).symm
    have hweight := deningerDivisorThetaEigen_add_reflect q
    have hconj :
        deningerDivisorThetaEigen q +
          (starRingEnd ℂ) (deningerDivisorThetaEigen q) = 1 := by
      rw [← hlambda]
      exact hweight
    have hre := congrArg Complex.re hconj
    have hlambdaRe :
        (deningerDivisorThetaEigen q).re = 1 / 2 := by
      simp only [add_re, conj_re, one_re] at hre
      linarith
    have him : (xiSpectralPoint q).im = 0 := by
      rw [deningerDivisorThetaEigen_eq] at hlambdaRe
      simp [mul_re] at hlambdaRe
      linarith
    exact
      ⟨(xiSpectralPoint q).re,
        Complex.ext (by simp) (by simpa using him)⟩
  rw [rh_iff_xi_ne_zero_right]
  intro z hz hzero
  let ρ : XiDivisorSupport :=
    ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hpos := xi_divisor_pos_on_support ρ
  have hn :
      0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨ρ, ⟨0, hn⟩⟩
  obtain ⟨t, ht⟩ := hreal q
  have him := congrArg Complex.im ht
  have hre : z.re = 1 / 2 := by
    dsimp only [q, ρ, xiSpectralPoint] at him
    simp at him
    linarith
  exact (ne_of_gt (mem_rightHalf.mp hz)) hre

/-- Exact closed Hilbert purity gate: Frobenius commutes with odd Hodge star iff RH. -/
theorem deningerDivisorClosedTheta_orientedHodge_iff_riemannHypothesis :
    (∀ x : deningerDivisorClosedTheta.domain,
      deningerArithmeticOrientedHodgeLp (deningerDivisorClosedTheta x) =
        deningerDivisorClosedTheta
          (deningerArithmeticOrientedHodgeDomain x)) ↔
      RiemannHypothesis :=
  ⟨riemannHypothesis_of_deningerDivisorClosedTheta_orientedHodge,
    deningerDivisorClosedTheta_orientedHodge_of_riemannHypothesis⟩

/-- Closed Hilbert weight-one polarization supplied by RH.  The converse is the preceding theorem. -/
def deningerArithmeticOrientedClosedPolarization
    (hRH : RiemannHypothesis) :
    DeningerClosedWeightOnePolarization XiDivisorL2 where
  theta := deningerDivisorClosedTheta
  theta_closed := deningerDivisorClosedTheta_isClosed
  theta_dense := deningerDivisorClosedTheta_dense
  cupTrace := deningerArithmeticOrientedHilbertCup
  cup_nondegenerate := deningerArithmeticOrientedHilbertCup_nondegenerate
  star := deningerArithmeticOrientedHilbertHodge
  star_mem_domain := deningerArithmeticOrientedHodgeLp_mem_domain
  theta_cup := deningerDivisorClosedTheta_orientedCup
  star_theta :=
    deningerDivisorClosedTheta_orientedHodge_of_riemannHypothesis hRH
  inner_eq_cup_star :=
    deningerArithmeticOrientedHilbert_inner_eq_cup_hodge

end

end RHTower
