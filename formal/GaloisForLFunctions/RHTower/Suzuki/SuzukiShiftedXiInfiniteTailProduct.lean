import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedXiFiniteTailProduct

/-!
# Infinite reflection-paired shifted-Xi tail product

This file removes the finite-divisor assumption from the exact reflection pairing of the two
transverse Xi tails.  Pairing before taking the product is essential: the paired quadratic factors
are summably close to one, whereas the individual algebraic scales need not define useful products.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Reflection-paired right-tail factors form an unconditional infinite product. -/
theorem multipliable_xiShiftRightReflectionPairFactor
    (omega : ℝ) (z : ℂ) :
    Multipliable (fun q : XiShiftRightZeroCopy omega =>
      xiShiftRightReflectionPairFactor z q.1) := by
  have hright : Multipliable (fun q : XiShiftRightZeroCopy omega =>
      weierstrassE1 (z / xiSpectralPoint q.1)) :=
    canonicalProductE1IndexedSelected_multipliable
      xiSpectralPoint
      (fun q => omega < (I * xiSpectralPoint q).re)
      xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable z
  have hreflect : Multipliable (fun q : XiShiftRightZeroCopy omega =>
      weierstrassE1
        (z / xiSpectralPoint (xiZeroCopyReflectEquiv q.1))) := by
    have hneg : Multipliable (fun q : XiShiftRightZeroCopy omega =>
        weierstrassE1 (-z / xiSpectralPoint q.1)) :=
      canonicalProductE1IndexedSelected_multipliable
        xiSpectralPoint
        (fun q => omega < (I * xiSpectralPoint q).re)
        xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable (-z)
    convert hneg using 1
    ext q
    rw [xiSpectralPoint_reflect]
    congr 1
    field_simp
  convert hright.mul hreflect using 1
  ext q
  rw [xiShiftRightReflectionPairFactor, xiSpectralPoint_reflect]

/-- The full transverse canonical product is the infinite product of its right-tail reflection
pairs, with divisor multiplicities retained. -/
theorem xiShiftExtremeCanonicalProduct_eq_right_pair_tprod
    (omega : ℝ) (homega : 0 ≤ omega) (z : ℂ) :
    xiShiftExtremeCanonicalProduct omega z =
      ∏' q : XiShiftRightZeroCopy omega,
        xiShiftRightReflectionPairFactor z q.1 := by
  let f : XiZeroCopy → ℂ := fun q =>
    weierstrassE1 (z / xiSpectralPoint q)
  have hfull : Multipliable f := xiCanonicalProduct_multipliable z
  let fRight : XiShiftRightZeroCopy omega → ℂ := f ∘ Subtype.val
  have hright : Multipliable fRight := by
    exact canonicalProductE1IndexedSelected_multipliable
      xiSpectralPoint
      (fun q => omega < (I * xiSpectralPoint q).re)
      xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable z
  let fReflect : XiShiftRightZeroCopy omega → ℂ := fun q =>
    weierstrassE1
      (z / xiSpectralPoint (xiZeroCopyReflectEquiv q.1))
  have hreflect : Multipliable fReflect := by
    have hneg : Multipliable (fun q : XiShiftRightZeroCopy omega =>
        weierstrassE1 (-z / xiSpectralPoint q.1)) :=
      canonicalProductE1IndexedSelected_multipliable
        xiSpectralPoint
        (fun q => omega < (I * xiSpectralPoint q).re)
        xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable (-z)
    convert hneg using 1
    ext q
    dsimp only [fReflect]
    rw [xiSpectralPoint_reflect]
    congr 1
    field_simp
  let e := xiShiftExtremeSumEquiv omega homega
  rw [xiShiftExtremeCanonicalProduct, canonicalProductE1IndexedSelected,
    canonicalProductE1Indexed]
  calc
    (∏' q : XiShiftExtremeZeroCopy omega,
        weierstrassE1 (z / xiSpectralPoint q.1)) =
      ∏' s : XiShiftRightZeroCopy omega ⊕ XiShiftRightZeroCopy omega,
        weierstrassE1 (z / xiSpectralPoint (e.symm s).1) := by
          exact (e.symm.tprod_eq (fun q : XiShiftExtremeZeroCopy omega =>
            weierstrassE1 (z / xiSpectralPoint q.1))).symm
    _ = (∏' q : XiShiftRightZeroCopy omega,
          weierstrassE1 (z / xiSpectralPoint q.1)) *
        ∏' q : XiShiftRightZeroCopy omega,
          weierstrassE1
            (z / xiSpectralPoint (xiZeroCopyReflectEquiv q.1)) := by
      have hsum : HasProd (Sum.elim fRight fReflect)
          ((∏' q : XiShiftRightZeroCopy omega, fRight q) *
            ∏' q : XiShiftRightZeroCopy omega, fReflect q) :=
        HasProd.sum (f := Sum.elim fRight fReflect)
          hright.hasProd hreflect.hasProd
      have hsumEq :
          (∏' s : XiShiftRightZeroCopy omega ⊕ XiShiftRightZeroCopy omega,
              Sum.elim fRight fReflect s) =
            (∏' q : XiShiftRightZeroCopy omega, fRight q) *
              ∏' q : XiShiftRightZeroCopy omega, fReflect q :=
        hsum.tprod_eq
      calc
        (∏' s : XiShiftRightZeroCopy omega ⊕ XiShiftRightZeroCopy omega,
            weierstrassE1 (z / xiSpectralPoint (e.symm s).1)) =
          ∏' s : XiShiftRightZeroCopy omega ⊕ XiShiftRightZeroCopy omega,
            Sum.elim fRight fReflect s := by
              apply tprod_congr
              intro s
              rcases s with q | q <;> rfl
        _ = _ := by
          simpa only [f, fRight, fReflect, Function.comp_apply] using hsumEq
    _ = ∏' q : XiShiftRightZeroCopy omega,
        (weierstrassE1 (z / xiSpectralPoint q.1) *
          weierstrassE1
            (z / xiSpectralPoint (xiZeroCopyReflectEquiv q.1))) := by
      have hmulEq :
          (∏' q : XiShiftRightZeroCopy omega, fRight q * fReflect q) =
            (∏' q : XiShiftRightZeroCopy omega, fRight q) *
              ∏' q : XiShiftRightZeroCopy omega, fReflect q :=
        (hright.hasProd.mul hreflect.hasProd).tprod_eq
      calc
        (∏' q : XiShiftRightZeroCopy omega,
            weierstrassE1 (z / xiSpectralPoint q.1)) *
            ∏' q : XiShiftRightZeroCopy omega,
              weierstrassE1
                (z / xiSpectralPoint (xiZeroCopyReflectEquiv q.1)) =
          (∏' q : XiShiftRightZeroCopy omega, fRight q) *
            ∏' q : XiShiftRightZeroCopy omega, fReflect q := by
              rfl
        _ = ∏' q : XiShiftRightZeroCopy omega, fRight q * fReflect q :=
          hmulEq.symm
        _ = _ := by
          apply tprod_congr
          intro q
          rfl
    _ = ∏' q : XiShiftRightZeroCopy omega,
        xiShiftRightReflectionPairFactor z q.1 := by
      apply tprod_congr
      intro q
      rw [xiShiftRightReflectionPairFactor, xiSpectralPoint_reflect]

/-- The reflection-paired product converges to the literal transverse Xi canonical product. -/
theorem hasProd_xiShiftRightReflectionPairFactor
    (omega : ℝ) (homega : 0 ≤ omega) (z : ℂ) :
    HasProd (fun q : XiShiftRightZeroCopy omega =>
        xiShiftRightReflectionPairFactor z q.1)
      (xiShiftExtremeCanonicalProduct omega z) := by
  have h := (multipliable_xiShiftRightReflectionPairFactor omega z).hasProd
  rw [xiShiftExtremeCanonicalProduct_eq_right_pair_tprod omega homega z]
  exact h

/-- One exact paired factor in the infinite transverse-tail quotient. -/
def xiShiftRightReflectionPairQuotientFactor
    (omega : ℝ) (z : ℂ) (q : XiShiftRightZeroCopy omega) : ℂ :=
  xiShiftRightReflectionPairFactor (z - (omega : ℂ) * I) q.1 /
    xiShiftRightReflectionPairFactor (-z - (omega : ℂ) * I) q.1

/-- Exact infinite-product realization of the literal transverse shifted-Xi quotient, away from
its pole divisor. -/
theorem xiShiftExtremeTheta_eq_right_pair_quotient_tprod
    {omega : ℝ} (homega : 0 ≤ omega) {z : ℂ}
    (hext : xiShiftExtremeE omega z ≠ 0) :
    xiShiftExtremeTheta omega z =
      ∏' q : XiShiftRightZeroCopy omega,
        xiShiftRightReflectionPairQuotientFactor omega z q := by
  have hnum := hasProd_xiShiftRightReflectionPairFactor
    omega homega (z - (omega : ℂ) * I)
  have hden := hasProd_xiShiftRightReflectionPairFactor
    omega homega (-z - (omega : ℂ) * I)
  have hquot := HasProd.div_of_limit_ne_zero hnum hden (by
    simpa only [xiShiftExtremeE] using hext)
  simpa only [xiShiftExtremeTheta, xiShiftExtremeE, neg_neg,
    xiShiftRightReflectionPairQuotientFactor] using hquot.tprod_eq.symm

end

end RHTower
