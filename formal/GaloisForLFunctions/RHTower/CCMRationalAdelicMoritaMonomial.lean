import GaloisForLFunctions.RHTower.CCMRationalAdelicBruhatSimpleTensorTraceClass
import GaloisForLFunctions.RHTower.CCMRationalAdelicCrossedProduct

/-!
# Exact CCM Morita representation of rational adelic crossed-product monomials

At a nonzero adelic base point, a crossed-product monomial `t U_k` acts on
`ℓ²(ℚˣ)` by the weighted shift

`(π_b(t U_k) ξ)(q) = t(qb) ξ(k⁻¹q)`.

This file proves the two identities needed for the genuine CCM restriction:

* inverse adelic scaling becomes inverse translation of the rational orbit;
* twisted multiplication of monomials becomes composition of weighted shifts.

It also computes the ordinary operator trace of one monomial: only the identity
scaling sector survives, and its trace is the rational-orbit sum.  All operators
appearing here are the actual trace-class operators constructed from adelic
Bruhat--Schwartz orbit summability.
-/

noncomputable section

open ContinuousLinearMap

namespace GaloisForLFunctions
namespace RHTower

private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling

noncomputable instance ccmRationalAdelicMoritaScaleDecidableEq :
    DecidableEq Scale :=
  Classical.decEq _

@[simp]
theorem ccmRationalAdelicBruhatTensorOrbit_zero
    (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ) (q : ℚ) :
    ccmRationalAdelicBruhatTensorOrbit 0 bInf b q = 0 := by
  simp [ccmRationalAdelicBruhatTensorOrbit]

@[simp]
theorem ccmRationalAdelicBruhatTensorOrbit_add
    (t u : Core) (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ) (q : ℚ) :
    ccmRationalAdelicBruhatTensorOrbit (t + u) bInf b q =
      ccmRationalAdelicBruhatTensorOrbit t bInf b q +
        ccmRationalAdelicBruhatTensorOrbit u bInf b q := by
  simp [ccmRationalAdelicBruhatTensorOrbit]

@[simp]
theorem ccmRationalAdelicBruhatTensorOrbit_smul
    (z : ℂ) (t : Core) (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ) (q : ℚ) :
    ccmRationalAdelicBruhatTensorOrbit (z • t) bInf b q =
      z * ccmRationalAdelicBruhatTensorOrbit t bInf b q := by
  simp [ccmRationalAdelicBruhatTensorOrbit]

/-- Orbit evaluation is a character of the nonunital adelic tensor algebra. -/
theorem ccmRationalAdelicBruhatTensorOrbit_mul
    (t u : Core) (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ) (q : ℚ) :
    ccmRationalAdelicBruhatTensorOrbit (t * u) bInf b q =
      ccmRationalAdelicBruhatTensorOrbit t bInf b q *
        ccmRationalAdelicBruhatTensorOrbit u bInf b q := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f phi =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul g psi =>
          simp [ccmRationalAdelicBruhatPureTensorOrbit,
            ccmRationalArchimedeanSchwartz_mul_apply,
            ccmRationalFiniteBruhat_mul_apply]
          ring
      | add u v hu hv =>
          rw [ccmRationalAdelicBruhat_mul_add,
            ccmRationalAdelicBruhatTensorOrbit_add,
            ccmRationalAdelicBruhatTensorOrbit_add, hu, hv]
          ring
  | add t u ht hu =>
      rw [ccmRationalAdelicBruhat_add_mul,
        ccmRationalAdelicBruhatTensorOrbit_add,
        ccmRationalAdelicBruhatTensorOrbit_add, ht, hu]
      ring

/-- Inverse adelic scaling is inverse translation of the rational-orbit index. -/
theorem ccmRationalAdelicBruhatTensorOrbit_scaling
    (k : Scale) (t : Core) (bInf : ℝ)
    (b : CCMRationalFiniteAdeleˣ) (q : CCMRationalUnit) :
    ccmRationalAdelicBruhatTensorOrbit (k • t) bInf b (q : ℚ) =
      ccmRationalAdelicBruhatTensorOrbit t bInf b
        ((k.val⁻¹ * q : CCMRationalUnit) : ℚ) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f phi =>
      simp only [ccmRationalAdelicScaling_smul_tmul,
        ccmRationalAdelicBruhatTensorOrbit_tmul,
        ccmRationalAdelicBruhatPureTensorOrbit,
        ccmRationalArchimedeanScaling_apply,
        ccmRationalFiniteBruhatScaling_apply]
      congr 2
      · push_cast
        ring
      · rw [← mul_assoc]
        congr 1
        simpa only [Units.val_mul, Units.val_inv_eq_inv_val] using
          (map_mul (algebraMap ℚ CCMRationalFiniteAdele)
            (k.val⁻¹ : ℚ) (q : ℚ)).symm
  | add t u ht hu =>
      rw [smul_add, ccmRationalAdelicBruhatTensorOrbit_add,
        ccmRationalAdelicBruhatTensorOrbit_add, ht, hu]

@[simp]
theorem ccmRationalAdelicBruhatTensorOrbitCoefficient_mul
    (t u : Core) (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ)
    (q : CCMRationalUnit) :
    ccmRationalAdelicBruhatTensorOrbitCoefficient (t * u) bInf b q =
      ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b q *
        ccmRationalAdelicBruhatTensorOrbitCoefficient u bInf b q :=
  ccmRationalAdelicBruhatTensorOrbit_mul t u bInf b q

@[simp]
theorem ccmRationalAdelicBruhatTensorOrbitCoefficient_scaling
    (k : Scale) (t : Core) (bInf : ℝ)
    (b : CCMRationalFiniteAdeleˣ) (q : CCMRationalUnit) :
    ccmRationalAdelicBruhatTensorOrbitCoefficient (k • t) bInf b q =
      ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b
        (k.val⁻¹ * q) :=
  ccmRationalAdelicBruhatTensorOrbit_scaling k t bInf b q

/-- Coefficient in the product of two weighted rational shifts. -/
def ccmRationalMoritaWeightedShiftProductCoefficient
    (a d : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (q : CCMRationalUnit) : ℂ :=
  a q * d (k⁻¹ * q)

theorem ccmRationalMoritaWeightedShiftProductCoefficient_bound
    (a d : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C D : ℝ) (hC : 0 ≤ C)
    (ha : ∀ q, ‖a q‖ ≤ C) (hd : ∀ q, ‖d q‖ ≤ D) :
    ∀ q, ‖ccmRationalMoritaWeightedShiftProductCoefficient a d k q‖ ≤ C * D := by
  intro q
  rw [ccmRationalMoritaWeightedShiftProductCoefficient, norm_mul]
  exact mul_le_mul (ha q) (hd _) (norm_nonneg _) hC

/-- Exact composition law for bounded weighted rational shifts. -/
theorem ccmRationalMoritaWeightedShift_comp
    (a d : CCMRationalUnit → ℂ) (k l : CCMRationalUnit)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ q, ‖a q‖ ≤ C) (hd : ∀ q, ‖d q‖ ≤ D) :
    ccmRationalMoritaWeightedShift a k C hC ha ∘L
        ccmRationalMoritaWeightedShift d l D hD hd =
      ccmRationalMoritaWeightedShift
        (ccmRationalMoritaWeightedShiftProductCoefficient a d k)
        (k * l) (C * D) (mul_nonneg hC hD)
        (ccmRationalMoritaWeightedShiftProductCoefficient_bound
          a d k C D hC ha hd) := by
  apply ContinuousLinearMap.ext
  intro f
  ext q
  simp only [ContinuousLinearMap.comp_apply,
    ccmRationalMoritaWeightedShift_apply,
    ccmRationalMoritaWeightedShiftProductCoefficient]
  have harg : l⁻¹ * (k⁻¹ * q) = (k * l)⁻¹ * q := by
    simp [mul_inv_rev, mul_assoc]
  rw [harg]
  ring

/-- Actual trace-class CCM operator for a crossed-product monomial `t U_k`. -/
def ccmRationalAdelicMoritaMonomial
    (t : Core) {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (k : Scale) :
    CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert :=
  ccmRationalAdelicBruhatTensorWeightedShift t hbInf b k.val

theorem ccmRationalAdelicMoritaMonomial_isTraceClass
    (t : Core) {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (k : Scale) :
    (ccmRationalAdelicMoritaMonomial t hbInf b k).IsTraceClass :=
  ccmRationalAdelicBruhatTensorWeightedShift_isTraceClass t hbInf b k.val

/-- Twisted monomial multiplication is represented by operator composition. -/
theorem ccmRationalAdelicMoritaMonomial_mul
    (t u : Core) {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (k l : Scale) :
    ccmRationalAdelicMoritaMonomial (t * (k • u)) hbInf b (k * l) =
      ccmRationalAdelicMoritaMonomial t hbInf b k ∘L
        ccmRationalAdelicMoritaMonomial u hbInf b l := by
  apply ContinuousLinearMap.ext
  intro f
  ext q
  simp only [ccmRationalAdelicMoritaMonomial,
    ccmRationalAdelicBruhatTensorWeightedShift,
    ccmRationalMoritaWeightedShift_apply,
    ccmRationalAdelicBruhatTensorOrbitCoefficient_mul,
    ccmRationalAdelicBruhatTensorOrbitCoefficient_scaling,
    ContinuousLinearMap.comp_apply,
    ccmRationalAdelicScaling_mul_val]
  have harg : (k.val * l.val)⁻¹ * q =
      l.val⁻¹ * (k.val⁻¹ * q) := by
    simp [mul_inv_rev, mul_assoc]
  rw [harg]
  ring

/-- The trace of one weighted shift is supported on its identity scaling sector. -/
theorem ccmRationalMoritaWeightedShift_opTrace
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C)
    (htrace :
      (ccmRationalMoritaWeightedShift a k C hC ha).IsTraceClass) :
    opTrace (ccmRationalMoritaWeightedShift a k C hC ha) =
      if k = 1 then ∑' q, a q else 0 := by
  rw [ccmRationalMoritaHilbert_opTrace_eq_tsum_basis htrace]
  by_cases hk : k = 1
  · subst k
    rw [if_pos rfl]
    apply tsum_congr
    intro q
    rw [ccmRationalMoritaHilbert_inner_basis,
      ccmRationalMoritaWeightedShift_apply]
    simp [ccmRationalMoritaHilbertBasis_apply]
  · rw [if_neg hk]
    have hterm : ∀ q : CCMRationalUnit,
        inner ℂ (ccmRationalMoritaHilbertBasis q)
          (ccmRationalMoritaWeightedShift a k C hC ha
            (ccmRationalMoritaHilbertBasis q)) = 0 := by
      intro q
      rw [ccmRationalMoritaHilbert_inner_basis,
        ccmRationalMoritaWeightedShift_basis]
      have hkq : k * q ≠ q := by
        intro h
        apply hk
        calc
          k = (k * q) * q⁻¹ := by simp
          _ = q * q⁻¹ := by rw [h]
          _ = 1 := by simp
      simp [ccmRationalMoritaHilbertBasis_apply, hkq]
    simp_rw [hterm]
    exact tsum_zero

/-- Exact degree-zero CCM trace formula for one adelic crossed-product monomial. -/
theorem ccmRationalAdelicMoritaMonomial_opTrace
    (t : Core) {bInf : ℝ} (hbInf : bInf ≠ 0)
    (b : CCMRationalFiniteAdeleˣ) (k : Scale) :
    opTrace (ccmRationalAdelicMoritaMonomial t hbInf b k) =
      if k = 1 then
        ∑' q, ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b q
      else 0 := by
  classical
  have h := ccmRationalMoritaWeightedShift_opTrace
      (ccmRationalAdelicBruhatTensorOrbitCoefficient t bInf b) k.val
      (ccmRationalAdelicBruhatTensorOrbitCoefficientLOneBound t bInf b)
      (ccmRationalAdelicBruhatTensorOrbitCoefficientLOneBound_nonneg t bInf b)
      (ccmRationalAdelicBruhatTensorOrbitCoefficient_norm_le_lOneBound
        t hbInf b)
      (ccmRationalAdelicMoritaMonomial_isTraceClass t hbInf b k)
  by_cases hk : k = 1
  · subst k
    simpa [ccmRationalAdelicMoritaMonomial,
      ccmRationalAdelicBruhatTensorWeightedShift] using h
  · have hkval : k.val ≠ 1 := by
      intro hkval
      apply hk
      rcases k with ⟨kval⟩
      change CCMRationalAdelicScaling.mk kval =
        CCMRationalAdelicScaling.mk 1
      congr
    simpa [ccmRationalAdelicMoritaMonomial,
      ccmRationalAdelicBruhatTensorWeightedShift, hk, hkval] using h

end RHTower
end GaloisForLFunctions
