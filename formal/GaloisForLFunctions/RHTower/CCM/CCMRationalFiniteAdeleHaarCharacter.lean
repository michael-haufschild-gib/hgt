import GaloisForLFunctions.RHTower.CCM.CCMRationalIntegralAdeleHaarIndex
import GaloisForLFunctions.RHTower.CCM.CCMRationalFiniteAdeleHaarScaling

/-!
# Exact finite-adelic Haar character of rational scaling

The normalized finite-adele Haar character is computed arithmetically, without a product-formula
premise. Natural and integral scalars are handled by the exact sublattice-index theorem; an
arbitrary nonzero rational is then decomposed into sign, numerator, and denominator.

For multiplication by `q ∈ ℚˣ`, the character is `|q|∞⁻¹`. Consequently the inverse pullback
used by the CCM action has character `|k|∞`, and its finite Bruhat integral scales by
`|k|∞⁻¹`. This is the nonarchimedean half of adelic Haar cancellation.
-/

noncomputable section
open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable def ccmRationalNatUnit (n : ℕ) (hn : n ≠ 0) : CCMRationalUnit :=
  Units.mk0 (n : ℚ) (by exact_mod_cast hn)

@[simp] theorem ccmRationalNatUnit_val (n : ℕ) (hn : n ≠ 0) :
    ((ccmRationalNatUnit n hn : CCMRationalUnit) : ℚ) = n := rfl

def ccmRationalFiniteAdeleScalingEquiv (q : CCMRationalUnit) :
    CCMRationalFiniteAdele ≃ₜ+ CCMRationalFiniteAdele :=
  ContinuousAddEquiv.mulLeft (ccmRationalUnitFiniteAdele q)

@[simp] theorem ccmRationalFiniteAdeleScalingEquiv_apply (q : CCMRationalUnit)
    (x : CCMRationalFiniteAdele) :
    ccmRationalFiniteAdeleScalingEquiv q x =
      algebraMap ℚ CCMRationalFiniteAdele (q : ℚ) * x := rfl

theorem ccmRationalFiniteAdeleScalingNat_apply (n : ℕ) (hn : n ≠ 0)
    (x : CCMRationalFiniteAdele) :
    ccmRationalFiniteAdeleScalingEquiv (ccmRationalNatUnit n hn) x = n • x := by
  simp [nsmul_eq_mul]

theorem ccmRationalFiniteAdeleScalingNat_preimage_nsmulSet (n : ℕ) (hn : n ≠ 0) :
    ccmRationalFiniteAdeleScalingEquiv (ccmRationalNatUnit n hn) ⁻¹'
        ccmRationalIntegralFiniteAdelesNSMulSet n =
      ccmRationalIntegralFiniteAdeles := by
  ext x
  constructor
  · rintro ⟨z, hz⟩
    rw [ccmRationalFiniteAdeleScalingNat_apply] at hz
    have heq : ccmRationalFiniteAdeleScalingEquiv (ccmRationalNatUnit n hn) x =
        ccmRationalFiniteAdeleScalingEquiv (ccmRationalNatUnit n hn) z.1 := by
      rw [ccmRationalFiniteAdeleScalingNat_apply, ccmRationalFiniteAdeleScalingNat_apply]
      exact hz.symm
    have := (ccmRationalFiniteAdeleScalingEquiv (ccmRationalNatUnit n hn)).injective heq
    change x ∈ ccmRationalIntegralFiniteAdelesAddSubgroup
    rw [this]
    exact z.2
  · intro hx
    exact ⟨⟨x, hx⟩, by rw [ccmRationalFiniteAdeleScalingNat_apply]⟩

theorem ccmRationalFiniteAdeleScalingNatHaarCharacter (n : ℕ) (hn : n ≠ 0) :
    (addEquivAddHaarChar (ccmRationalFiniteAdeleScalingEquiv (ccmRationalNatUnit n hn)) : ENNReal) =
      (n : ENNReal)⁻¹ := by
  have h := addEquivAddHaarChar_smul_preimage
    ccmRationalFiniteAdeleHaar
    (X := ccmRationalIntegralFiniteAdelesNSMulSet n)
    (ccmRationalFiniteAdeleScalingEquiv (ccmRationalNatUnit n hn))
  rw [ccmRationalFiniteAdeleScalingNat_preimage_nsmulSet n hn,
    ccmRationalFiniteAdeleHaar_integral_subring,
    ccmRationalFiniteAdeleHaar_integralSubring_nsmul hn] at h
  simpa [ENNReal.smul_def] using h

theorem ccmRationalFiniteAdeleScalingEquiv_mul (q r : CCMRationalUnit) :
    ccmRationalFiniteAdeleScalingEquiv (q * r) =
      (ccmRationalFiniteAdeleScalingEquiv q).trans (ccmRationalFiniteAdeleScalingEquiv r) := by
  apply ContinuousAddEquiv.ext
  intro x
  change algebraMap ℚ CCMRationalFiniteAdele ((q * r : CCMRationalUnit) : ℚ) * x =
    algebraMap ℚ CCMRationalFiniteAdele (r : ℚ) *
      (algebraMap ℚ CCMRationalFiniteAdele (q : ℚ) * x)
  rw [Units.val_mul, map_mul]
  ring

theorem ccmRationalFiniteAdeleScalingEquiv_inv (q : CCMRationalUnit) :
    ccmRationalFiniteAdeleScalingEquiv q⁻¹ = (ccmRationalFiniteAdeleScalingEquiv q).symm := by
  apply ContinuousAddEquiv.ext
  intro x
  apply (Equiv.eq_symm_apply (ccmRationalFiniteAdeleScalingEquiv q).toEquiv).mpr
  rw [ccmRationalFiniteAdeleScalingEquiv_apply]
  change ccmRationalFiniteAdeleScalingEquiv q
      (algebraMap ℚ CCMRationalFiniteAdele ((q⁻¹ : CCMRationalUnit) : ℚ) * x) = x
  rw [ccmRationalFiniteAdeleScalingEquiv_apply]
  rw [Units.val_inv_eq_inv_val]
  rw [← mul_assoc, ← map_mul]
  simp

theorem ccmRationalFiniteAdeleScalingHaarCharacter_mul (q r : CCMRationalUnit) :
    addEquivAddHaarChar (ccmRationalFiniteAdeleScalingEquiv (q * r)) =
      addEquivAddHaarChar (ccmRationalFiniteAdeleScalingEquiv q) *
        addEquivAddHaarChar (ccmRationalFiniteAdeleScalingEquiv r) := by
  rw [ccmRationalFiniteAdeleScalingEquiv_mul, addEquivAddHaarChar_trans]

theorem ccmRationalFiniteAdeleScalingHaarCharacter_inv (q : CCMRationalUnit) :
    addEquivAddHaarChar (ccmRationalFiniteAdeleScalingEquiv q⁻¹) =
      (addEquivAddHaarChar (ccmRationalFiniteAdeleScalingEquiv q))⁻¹ := by
  rw [ccmRationalFiniteAdeleScalingEquiv_inv, addEquivAddHaarChar_symm]

theorem ccmRationalFiniteAdeleScalingNatHaarCharacter_nnreal (n : ℕ) (hn : n ≠ 0) :
    addEquivAddHaarChar (ccmRationalFiniteAdeleScalingEquiv (ccmRationalNatUnit n hn)) =
      (n : NNReal)⁻¹ := by
  apply ENNReal.coe_injective
  rw [ENNReal.coe_inv (by exact_mod_cast hn)]
  exact ccmRationalFiniteAdeleScalingNatHaarCharacter n hn

theorem ccmRationalFiniteAdeleScaling_negOne_apply (x : CCMRationalFiniteAdele) :
    ccmRationalFiniteAdeleScalingEquiv (-1 : CCMRationalUnit) x = -x := by
  simp [ccmRationalFiniteAdeleScalingEquiv_apply]

theorem ccmRationalFiniteAdeleScaling_negOne_preimage_integralSubring :
    ccmRationalFiniteAdeleScalingEquiv (-1 : CCMRationalUnit) ⁻¹'
        ccmRationalIntegralFiniteAdeles =
      ccmRationalIntegralFiniteAdeles := by
  ext x
  rw [Set.mem_preimage, ccmRationalFiniteAdeleScaling_negOne_apply]
  constructor
  · intro hx
    change x ∈ ccmRationalIntegralFiniteAdelesAddSubgroup
    simpa using (ccmRationalIntegralFiniteAdelesAddSubgroup.neg_mem hx)
  · exact ccmRationalIntegralFiniteAdelesAddSubgroup.neg_mem

theorem ccmRationalFiniteAdeleScaling_negOneHaarCharacter :
    addEquivAddHaarChar (ccmRationalFiniteAdeleScalingEquiv (-1 : CCMRationalUnit)) = 1 := by
  have h := addEquivAddHaarChar_smul_preimage
    ccmRationalFiniteAdeleHaar
    (X := ccmRationalIntegralFiniteAdeles)
    (ccmRationalFiniteAdeleScalingEquiv (-1 : CCMRationalUnit))
  rw [ccmRationalFiniteAdeleScaling_negOne_preimage_integralSubring,
    ccmRationalFiniteAdeleHaar_integral_subring] at h
  apply ENNReal.coe_injective
  simpa [ENNReal.smul_def] using h

noncomputable def ccmRationalIntUnit (z : ℤ) (hz : z ≠ 0) : CCMRationalUnit :=
  Units.mk0 (z : ℚ) (by exact_mod_cast hz)

@[simp] theorem ccmRationalIntUnit_val (z : ℤ) (hz : z ≠ 0) :
    ((ccmRationalIntUnit z hz : CCMRationalUnit) : ℚ) = z := rfl

theorem ccmRationalFiniteAdeleScalingIntHaarCharacter (z : ℤ) (hz : z ≠ 0) :
    addEquivAddHaarChar (ccmRationalFiniteAdeleScalingEquiv (ccmRationalIntUnit z hz)) =
      (z.natAbs : NNReal)⁻¹ := by
  cases z with
  | ofNat n =>
      have hn : n ≠ 0 := by
        intro hn
        apply hz
        simp [hn]
      have hu : ccmRationalIntUnit (Int.ofNat n) hz = ccmRationalNatUnit n hn := by
        apply Units.ext
        simp
      rw [hu, ccmRationalFiniteAdeleScalingNatHaarCharacter_nnreal n hn]
      rfl
  | negSucc n =>
      have hn : n + 1 ≠ 0 := Nat.succ_ne_zero n
      have hu : ccmRationalIntUnit (Int.negSucc n) hz =
          (-1 : CCMRationalUnit) * ccmRationalNatUnit (n + 1) hn := by
        apply Units.ext
        simp [Int.negSucc_eq]
      rw [hu, ccmRationalFiniteAdeleScalingHaarCharacter_mul, ccmRationalFiniteAdeleScaling_negOneHaarCharacter,
        ccmRationalFiniteAdeleScalingNatHaarCharacter_nnreal (n + 1) hn, one_mul]
      rfl

noncomputable def ccmRationalUnitArchimedeanNNNorm (q : CCMRationalUnit) : NNReal :=
  ⟨|(((q : CCMRationalUnit) : ℚ) : ℝ)|, abs_nonneg _⟩

@[simp] theorem ccmRationalUnitArchimedeanNNNorm_val (q : CCMRationalUnit) :
    (ccmRationalUnitArchimedeanNNNorm q : ℝ) = |(((q : CCMRationalUnit) : ℚ) : ℝ)| := rfl

theorem ccmRationalUnitArchimedeanNNNorm_eq_num_div_den (q : CCMRationalUnit) :
    ccmRationalUnitArchimedeanNNNorm q =
      (q.val.num.natAbs : NNReal) / (q.val.den : NNReal) := by
  apply NNReal.eq
  simp only [ccmRationalUnitArchimedeanNNNorm_val, NNReal.coe_div, NNReal.coe_natCast]
  rw [Rat.cast_def, abs_div]
  simp [abs_of_nonneg]

theorem ccmRationalUnit_eq_num_mul_den_inv (q : CCMRationalUnit) :
    q = ccmRationalIntUnit q.val.num
          (Rat.num_ne_zero.mpr q.ne_zero) *
        (ccmRationalNatUnit q.val.den q.val.den_nz)⁻¹ := by
  apply Units.ext
  change (q : ℚ) = (q.val.num : ℚ) * (q.val.den : ℚ)⁻¹
  rw [← div_eq_mul_inv]
  exact (Rat.num_div_den q.val).symm

theorem ccmRationalFiniteAdeleScalingHaarCharacter (q : CCMRationalUnit) :
    addEquivAddHaarChar (ccmRationalFiniteAdeleScalingEquiv q) =
      (ccmRationalUnitArchimedeanNNNorm q)⁻¹ := by
  calc
    addEquivAddHaarChar (ccmRationalFiniteAdeleScalingEquiv q) =
        addEquivAddHaarChar (ccmRationalFiniteAdeleScalingEquiv
          (ccmRationalIntUnit q.val.num (Rat.num_ne_zero.mpr q.ne_zero) *
            (ccmRationalNatUnit q.val.den q.val.den_nz)⁻¹)) := by
      rw [← ccmRationalUnit_eq_num_mul_den_inv q]
    _ = addEquivAddHaarChar (ccmRationalFiniteAdeleScalingEquiv
          (ccmRationalIntUnit q.val.num (Rat.num_ne_zero.mpr q.ne_zero))) *
        addEquivAddHaarChar (ccmRationalFiniteAdeleScalingEquiv
          (ccmRationalNatUnit q.val.den q.val.den_nz)⁻¹) :=
      ccmRationalFiniteAdeleScalingHaarCharacter_mul _ _
    _ = (q.val.num.natAbs : NNReal)⁻¹ *
        ((q.val.den : NNReal)⁻¹)⁻¹ := by
      rw [ccmRationalFiniteAdeleScalingIntHaarCharacter, ccmRationalFiniteAdeleScalingHaarCharacter_inv, ccmRationalFiniteAdeleScalingNatHaarCharacter_nnreal]
    _ = (ccmRationalUnitArchimedeanNNNorm q)⁻¹ := by
      rw [ccmRationalUnitArchimedeanNNNorm_eq_num_div_den]
      simp [div_eq_mul_inv, mul_comm]

theorem ccmRationalUnitArchimedeanNNNorm_inv (q : CCMRationalUnit) :
    ccmRationalUnitArchimedeanNNNorm q⁻¹ = (ccmRationalUnitArchimedeanNNNorm q)⁻¹ := by
  apply NNReal.eq
  rw [ccmRationalUnitArchimedeanNNNorm_val, NNReal.coe_inv, ccmRationalUnitArchimedeanNNNorm_val]
  simp [abs_inv]

theorem ccmRationalFiniteAdeleInverseScalingEquiv_eq_scalingEquiv_inv (k : CCMRationalAdelicScaling) :
    ccmRationalFiniteAdeleInverseScalingEquiv k =
      ccmRationalFiniteAdeleScalingEquiv k.val⁻¹ := rfl

theorem ccmRationalFiniteAdeleInverseScalingHaarCharacter (k : CCMRationalAdelicScaling) :
    addEquivAddHaarChar (ccmRationalFiniteAdeleInverseScalingEquiv k) =
      ccmRationalUnitArchimedeanNNNorm k.val := by
  rw [ccmRationalFiniteAdeleInverseScalingEquiv_eq_scalingEquiv_inv, ccmRationalFiniteAdeleScalingHaarCharacter,
    ccmRationalUnitArchimedeanNNNorm_inv, inv_inv]

theorem ccmRationalFiniteAdeleInverseScalingHaarCharacter_real (k : CCMRationalAdelicScaling) :
    (addEquivAddHaarChar
        (ccmRationalFiniteAdeleInverseScalingEquiv k) : ℝ) =
      |(((k.val : CCMRationalUnit) : ℚ) : ℝ)| := by
  rw [ccmRationalFiniteAdeleInverseScalingHaarCharacter]
  rfl

theorem ccmRationalFiniteBruhatIntegral_scaling
    (k : CCMRationalAdelicScaling)
    (f : CCMRationalFiniteBruhatSchwartz) :
    ccmRationalFiniteBruhatIntegral
        (ccmRationalFiniteBruhatScaling k f) =
      |(((k.val : CCMRationalUnit) : ℚ) : ℝ)|⁻¹ •
        ccmRationalFiniteBruhatIntegral f := by
  have h := ccmRationalFiniteBruhatIntegral_haarCharacter k f
  rw [ccmRationalFiniteAdeleInverseScalingHaarCharacter_real] at h
  let a := |(((k.val : CCMRationalUnit) : ℚ) : ℝ)|
  have ha : a ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast k.val.ne_zero)
  calc
    ccmRationalFiniteBruhatIntegral
        (ccmRationalFiniteBruhatScaling k f) =
        a⁻¹ • (a • ccmRationalFiniteBruhatIntegral
          (ccmRationalFiniteBruhatScaling k f)) := by
      rw [← mul_smul]
      simp [ha]
    _ = a⁻¹ • ccmRationalFiniteBruhatIntegral f := by rw [h]

end GaloisForLFunctions.RHTower

