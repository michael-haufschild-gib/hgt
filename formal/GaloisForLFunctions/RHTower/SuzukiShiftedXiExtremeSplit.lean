import GaloisForLFunctions.RHTower.SuzukiShiftedXiCoreSchur
import GaloisForLFunctions.RHTower.XiHadamardGrowth

open Complex Set

namespace RHTower

noncomputable section

/-- Multiplicity copies in the two Xi tails beyond transverse width `omega`. -/
abbrev XiShiftExtremeZeroCopy (omega : ℝ) :=
  {q : XiZeroCopy // omega < |(I * xiSpectralPoint q).re|}

/-- Canonical product over both transverse Xi tails. -/
def xiShiftExtremeCanonicalProduct (omega : ℝ) : ℂ → ℂ :=
  canonicalProductE1IndexedSelected xiSpectralPoint
    (fun q => omega < |(I * xiSpectralPoint q).re|)

theorem xiShiftExtremeCanonicalProduct_analytic (omega : ℝ) :
    AnalyticOnNhd ℂ (xiShiftExtremeCanonicalProduct omega) Set.univ :=
  canonicalProductE1IndexedSelected_analytic xiSpectralPoint
    (fun q => omega < |(I * xiSpectralPoint q).re|)
    xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable

theorem xiShiftExtremeCanonicalProduct_multipliable (omega : ℝ) (z : ℂ) :
    Multipliable (fun q : XiShiftExtremeZeroCopy omega =>
      weierstrassE1 (z / xiSpectralPoint q.1)) :=
  canonicalProductE1IndexedSelected_multipliable xiSpectralPoint
    (fun q => omega < |(I * xiSpectralPoint q).re|)
    xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable z

/-- Functional-equation reflection preserves both transverse tails. -/
def xiShiftExtremeReflectEquiv (omega : ℝ) :
    XiShiftExtremeZeroCopy omega ≃ XiShiftExtremeZeroCopy omega :=
  Equiv.subtypeEquiv xiZeroCopyReflectEquiv (fun q => by
    rw [xiSpectralPoint_reflect]
    have h : (I * -xiSpectralPoint q).re =
        -(I * xiSpectralPoint q).re := by
      norm_num [mul_re]
    rw [h, abs_neg])

theorem xiShiftExtremeCanonicalProduct_even (omega : ℝ) (z : ℂ) :
    xiShiftExtremeCanonicalProduct omega (-z) =
      xiShiftExtremeCanonicalProduct omega z := by
  rw [xiShiftExtremeCanonicalProduct, canonicalProductE1IndexedSelected,
    canonicalProductE1Indexed]
  let e := xiShiftExtremeReflectEquiv omega
  calc
    (∏' q : XiShiftExtremeZeroCopy omega,
        weierstrassE1 (-z / xiSpectralPoint q.1)) =
      ∏' q : XiShiftExtremeZeroCopy omega,
        weierstrassE1 (-z / xiSpectralPoint (e q).1) := by
          exact (e.tprod_eq (fun q : XiShiftExtremeZeroCopy omega =>
            weierstrassE1 (-z / xiSpectralPoint q.1))).symm
    _ = ∏' q : XiShiftExtremeZeroCopy omega,
        weierstrassE1 (z / xiSpectralPoint q.1) := by
          apply tprod_congr
          intro q
          change weierstrassE1
              (-z / xiSpectralPoint (xiZeroCopyReflectEquiv q.1)) = _
          rw [xiSpectralPoint_reflect]
          congr 1
          field_simp

/-- Exact multiplicity-preserving split into two transverse tails and symmetric core. -/
theorem xiCanonicalProduct_eq_extreme_mul_core (omega : ℝ) (z : ℂ) :
    xiCanonicalProduct z =
      xiShiftExtremeCanonicalProduct omega z *
        xiShiftCoreCanonicalProduct omega z := by
  have hcomp :
      canonicalProductE1IndexedComplement xiSpectralPoint
          (fun q => omega < |(I * xiSpectralPoint q).re|) z =
        xiShiftCoreCanonicalProduct omega z := by
    rw [canonicalProductE1IndexedComplement, xiShiftCoreCanonicalProduct,
      canonicalProductE1IndexedSelected]
    let e :
        {q : XiZeroCopy // ¬ omega < |(I * xiSpectralPoint q).re|} ≃
          {q : XiZeroCopy // |(I * xiSpectralPoint q).re| ≤ omega} :=
      Equiv.subtypeEquiv (Equiv.refl XiZeroCopy) (fun _ => not_lt)
    change (∏' q : {q : XiZeroCopy //
        ¬ omega < |(I * xiSpectralPoint q).re|},
        ((fun r : {r : XiZeroCopy //
            |(I * xiSpectralPoint r).re| ≤ omega} =>
          weierstrassE1 (z / xiSpectralPoint r.1)) ∘ e) q) =
      ∏' q : {q : XiZeroCopy //
        |(I * xiSpectralPoint q).re| ≤ omega},
        weierstrassE1 (z / xiSpectralPoint q.1)
    exact e.tprod_eq (fun r : {r : XiZeroCopy //
      |(I * xiSpectralPoint r).re| ≤ omega} =>
        weierstrassE1 (z / xiSpectralPoint r.1))
  rw [xiCanonicalProduct,
    canonicalProductE1Indexed_eq_selected_mul_complement
      xiSpectralPoint
      (fun q => omega < |(I * xiSpectralPoint q).re|)
      xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable z,
    xiShiftExtremeCanonicalProduct, hcomp]

/-- Shifted entire factor carrying precisely the two transverse tails. -/
def xiShiftExtremeE (omega : ℝ) (z : ℂ) : ℂ :=
  xiShiftExtremeCanonicalProduct omega (-z - (omega : ℂ) * I)

/-- Meromorphic quotient contributed by the two transverse tails. -/
def xiShiftExtremeTheta (omega : ℝ) (z : ℂ) : ℂ :=
  xiShiftExtremeE omega (-z) / xiShiftExtremeE omega z

/-- The literal Suzuki denominator is center value times tail and core factors. -/
theorem suzukiCanonicalE_eq_center_mul_extremeE_mul_coreE
    (omega : ℝ) (z : ℂ) :
    suzukiCanonicalE omega z =
      XiC 0 * xiShiftExtremeE omega z * xiShiftCoreE omega z := by
  rw [suzukiCanonicalE_eq_XiC_shift]
  have hsource := congrFun XiC_eq_constant_mul_canonicalProduct
    (-z - (omega : ℂ) * I)
  simp only [Pi.mul_apply] at hsource
  rw [hsource, xiCanonicalProduct_eq_extreme_mul_core,
    xiShiftExtremeE, xiShiftCoreE]
  ring

/-- On the regular upper-half-plane locus the literal shifted-Xi quotient factors into its
transverse-tail quotient and unconditional Schur core. -/
theorem suzukiCanonicalTheta_eq_extremeTheta_mul_coreTheta
    {omega : ℝ} {z : ℂ} (hz : 0 < z.im)
    (hE : suzukiCanonicalE omega z ≠ 0) :
    suzukiCanonicalTheta omega z =
      xiShiftExtremeTheta omega z * xiShiftCoreTheta omega z := by
  have hcore : xiShiftCoreE omega z ≠ 0 :=
    xiShiftCoreE_ne_zero_upperHalfPlane hz
  have hcenter : XiC 0 ≠ 0 := XiC_zero_ne
  have hext : xiShiftExtremeE omega z ≠ 0 := by
    intro hzero
    apply hE
    rw [suzukiCanonicalE_eq_center_mul_extremeE_mul_coreE, hzero]
    ring
  rw [suzukiCanonicalTheta_eq_E_neg_div_E,
    suzukiCanonicalE_eq_center_mul_extremeE_mul_coreE,
    suzukiCanonicalE_eq_center_mul_extremeE_mul_coreE,
    xiShiftExtremeTheta, xiShiftCoreTheta]
  field_simp

end

end RHTower
