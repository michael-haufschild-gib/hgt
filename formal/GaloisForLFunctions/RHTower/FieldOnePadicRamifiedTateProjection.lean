import GaloisForLFunctions.RHTower.FieldOnePadicRamifiedTateLinear

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set Topology
open scoped BigOperators NNReal ENNReal

variable (p : ℕ) [Fact p.Prime]

def fieldOnePadicUnitEmbedding (u : ℤ_[p]ˣ) : ℚ_[p]ˣ :=
  fieldOnePadicValuationUnitContinuousMulEquiv p
    (Multiplicative.ofAdd 0, u)

@[simp] theorem fieldOnePadicUnitEmbedding_val (u : ℤ_[p]ˣ) :
    ((fieldOnePadicUnitEmbedding p u : ℚ_[p]ˣ) : ℚ_[p]) =
      ((u : ℤ_[p]) : ℚ_[p]) := by
  change (p : ℚ_[p]) ^ (0 : ℤ) * ((u : ℤ_[p]) : ℚ_[p]) = _
  simp

def fieldOnePadicPrimitiveUnitCharacter (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) (u : ℤ_[p]ˣ) : ℂ :=
  χ.1 (fieldOnePadicUnitReduction p n u)

@[simp] theorem fieldOnePadicPrimitiveUnitCharacter_one
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    fieldOnePadicPrimitiveUnitCharacter p n χ 1 = 1 := by
  simp [fieldOnePadicPrimitiveUnitCharacter]

@[simp] theorem fieldOnePadicPrimitiveUnitCharacter_mul
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (u v : ℤ_[p]ˣ) :
    fieldOnePadicPrimitiveUnitCharacter p n χ (u * v) =
      fieldOnePadicPrimitiveUnitCharacter p n χ u *
        fieldOnePadicPrimitiveUnitCharacter p n χ v := by
  simp [fieldOnePadicPrimitiveUnitCharacter, map_mul]

theorem fieldOnePadicPrimitiveUnitCharacter_ne_zero
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (u : ℤ_[p]ˣ) :
    fieldOnePadicPrimitiveUnitCharacter p n χ u ≠ 0 := by
  have hnorm := DirichletCharacter.unit_norm_eq_one χ.1
    (fieldOnePadicUnitReduction p n u)
  intro hzero
  have hz : χ.1 (fieldOnePadicUnitReduction p n u) = 0 := hzero
  rw [hz, norm_zero] at hnorm
  exact zero_ne_one hnorm

@[simp] theorem fieldOnePadicPrimitiveUnitCharacter_inv
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (u : ℤ_[p]ˣ) :
    fieldOnePadicPrimitiveUnitCharacter p n χ u⁻¹ =
      (fieldOnePadicPrimitiveUnitCharacter p n χ u)⁻¹ := by
  have hne := fieldOnePadicPrimitiveUnitCharacter_ne_zero p n χ u
  apply mul_left_cancel₀ hne
  rw [← fieldOnePadicPrimitiveUnitCharacter_mul]
  rw [show u * u⁻¹ = 1 by group,
    fieldOnePadicPrimitiveUnitCharacter_one]
  exact (mul_inv_cancel₀ hne).symm

theorem continuous_fieldOnePadicPrimitiveUnitCharacter
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    Continuous (fieldOnePadicPrimitiveUnitCharacter p n χ) := by
  exact (continuous_of_discreteTopology : Continuous
    (fun r : (ZMod (p ^ n))ˣ => χ.1 r)).comp
      (fieldOnePadicUnitReduction_continuous p n)

theorem integrable_fieldOnePadicPrimitiveUnitCharacter
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    Integrable (fieldOnePadicPrimitiveUnitCharacter p n χ)
      (fieldOnePadicUnitNormalizedHaar p) :=
  (continuous_fieldOnePadicPrimitiveUnitCharacter p n χ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem fieldOnePadicPrimitiveAngularCharacter_ne_one
    (n : ℕ+) (χ : FieldOnePadicPrimitiveAngularCharacter p (n : ℕ)) :
    χ.1 ≠ 1 := by
  intro hχ
  have hcond : DirichletCharacter.conductor χ.1 = p ^ (n : ℕ) :=
    (DirichletCharacter.isPrimitive_def χ.1).mp χ.2
  haveI : NeZero (p ^ (n : ℕ)) :=
    ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  rw [hχ, DirichletCharacter.conductor_one] at hcond
  have hpPow : 1 < p ^ (n : ℕ) :=
    one_lt_pow₀ (Fact.out : Nat.Prime p).one_lt n.pos.ne'
  omega

theorem fieldOnePadicPrimitiveUnitCharacter_integral_eq_zero
    (n : ℕ+) (χ : FieldOnePadicPrimitiveAngularCharacter p (n : ℕ)) :
    ∫ u, fieldOnePadicPrimitiveUnitCharacter p (n : ℕ) χ u
        ∂fieldOnePadicUnitNormalizedHaar p = 0 := by
  have hquad := fieldOnePadicUnitResidueLift_integral p (n : ℕ) χ.1
  have hsumUnits :
      (∑ r : (ZMod (p ^ (n : ℕ)))ˣ, χ.1 r) = 0 := by
    have hs := fieldOneSum_mulChar_eq_sum_units χ.1
      (fun _ => (1 : ℂ))
    simp only [one_mul] at hs
    rw [← hs]
    simpa using MulChar.sum_eq_zero_of_ne_one
      (fieldOnePadicPrimitiveAngularCharacter_ne_one p n χ)
  change ∫ u, fieldOnePadicUnitResidueLift p (n : ℕ) χ.1 u
      ∂fieldOnePadicUnitNormalizedHaar p = 0
  rw [hquad, hsumUnits, mul_zero]

def fieldOnePadicPrimitiveAngularProjectionValue (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : compactlySupportedLocallyConstant ℚ_[p]) (x : ℚ_[p]) : ℂ :=
  ∫ u : ℤ_[p]ˣ,
    fieldOnePadicPrimitiveUnitCharacter p n χ u *
      f.1 (((u : ℤ_[p]) : ℚ_[p]) * x)
    ∂fieldOnePadicUnitNormalizedHaar p

theorem integrable_fieldOnePadicPrimitiveAngularProjectionValue_integrand
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : compactlySupportedLocallyConstant ℚ_[p]) (x : ℚ_[p]) :
    Integrable (fun u : ℤ_[p]ˣ =>
      fieldOnePadicPrimitiveUnitCharacter p n χ u *
        f.1 (((u : ℤ_[p]) : ℚ_[p]) * x))
      (fieldOnePadicUnitNormalizedHaar p) := by
  apply Continuous.integrable_of_hasCompactSupport
  · have huq : Continuous (fun u : ℤ_[p]ˣ =>
        ((fieldOnePadicUnitEmbedding p u : ℚ_[p]ˣ) : ℚ_[p])) :=
      Units.continuous_val.comp
        ((fieldOnePadicValuationUnitContinuousMulEquiv p).continuous.comp
          (continuous_const.prodMk continuous_id))
    have hu : Continuous (fun u : ℤ_[p]ˣ =>
        (((u : ℤ_[p]) : ℚ_[p]))) := by
      simpa only [fieldOnePadicUnitEmbedding_val] using huq
    exact (continuous_fieldOnePadicPrimitiveUnitCharacter p n χ).mul
      (f.1.continuous.comp (hu.mul continuous_const))
  · exact HasCompactSupport.of_compactSpace _

theorem fieldOnePadicDenominatorStage_unit_mul_iff
    (N : ℕ) (u : ℤ_[p]ˣ) (x : ℚ_[p]) :
    ((u : ℤ_[p]) : ℚ_[p]) * x ∈ fieldOnePadicDenominatorStage p N ↔
      x ∈ fieldOnePadicDenominatorStage p N := by
  change ‖(p : ℚ_[p]) ^ N * (((u : ℤ_[p]) : ℚ_[p]) * x)‖ ≤ 1 ↔
    ‖(p : ℚ_[p]) ^ N * x‖ ≤ 1
  have hu : ‖(((u : ℤ_[p]) : ℚ_[p]))‖ = 1 := by
    simpa only [PadicInt.norm_def] using PadicInt.norm_units u
  rw [show (p : ℚ_[p]) ^ N * (((u : ℤ_[p]) : ℚ_[p]) * x) =
      (((u : ℤ_[p]) : ℚ_[p])) * ((p : ℚ_[p]) ^ N * x) by ring,
    norm_mul, hu, one_mul]

theorem fieldOnePadicPrimitiveAngularProjectionValue_eq_zero_outside
    (n N : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hsupport : tsupport (f.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p N)
    {x : ℚ_[p]} (hx : x ∉ fieldOnePadicDenominatorStage p N) :
    fieldOnePadicPrimitiveAngularProjectionValue p n χ f x = 0 := by
  unfold fieldOnePadicPrimitiveAngularProjectionValue
  have hzero : (fun u : ℤ_[p]ˣ =>
      fieldOnePadicPrimitiveUnitCharacter p n χ u *
        f.1 (((u : ℤ_[p]) : ℚ_[p]) * x)) = 0 := by
    funext u
    have hnot : ((u : ℤ_[p]) : ℚ_[p]) * x ∉
        tsupport (f.1 : ℚ_[p] → ℂ) := by
      intro hts
      apply hx
      exact (fieldOnePadicDenominatorStage_unit_mul_iff p N u x).mp
        (hsupport hts)
    simp [image_eq_zero_of_notMem_tsupport hnot]
  rw [hzero]
  simp

theorem fieldOnePadicPrimitiveAngularProjectionValue_add_primePow
    (n L : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hperiod : ∀ x : ℚ_[p], ∀ z : ℤ_[p],
      f.1 (x + (p : ℚ_[p]) ^ L * (z : ℚ_[p])) = f.1 x)
    (x : ℚ_[p]) (z : ℤ_[p]) :
    fieldOnePadicPrimitiveAngularProjectionValue p n χ f
        (x + (p : ℚ_[p]) ^ L * (z : ℚ_[p])) =
      fieldOnePadicPrimitiveAngularProjectionValue p n χ f x := by
  unfold fieldOnePadicPrimitiveAngularProjectionValue
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    change fieldOnePadicPrimitiveUnitCharacter p n χ u *
        f.1 ((((u : ℤ_[p]) : ℚ_[p])) *
          (x + (p : ℚ_[p]) ^ L * (z : ℚ_[p]))) =
      fieldOnePadicPrimitiveUnitCharacter p n χ u *
        f.1 ((((u : ℤ_[p]) : ℚ_[p])) * x)
    congr 1
    rw [show (((u : ℤ_[p]) : ℚ_[p])) *
        (x + (p : ℚ_[p]) ^ L * (z : ℚ_[p])) =
      (((u : ℤ_[p]) : ℚ_[p])) * x +
        (p : ℚ_[p]) ^ L * (((u : ℤ_[p]) * z : ℤ_[p]) : ℚ_[p]) by
          rw [PadicInt.coe_mul]
          ring]
    exact hperiod _ ((u : ℤ_[p]) * z)

theorem fieldOnePadic_isLocallyConstant_of_primePower_period
    (L : ℕ) (g : ℚ_[p] → ℂ)
    (hperiod : ∀ x : ℚ_[p], ∀ z : ℤ_[p],
      g (x + (p : ℚ_[p]) ^ L * (z : ℚ_[p])) = g x) :
    IsLocallyConstant g := by
  let q : ℚ_[p] := (p : ℚ_[p]) ^ L
  have hq0 : q ≠ 0 := pow_ne_zero L (by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  let U : Set ℚ_[p] := (fun t : ℚ_[p] => q⁻¹ * t) ⁻¹'
    (fieldOnePadicIntegralAddSubgroup p : Set ℚ_[p])
  have hUopen : IsOpen U :=
    (fieldOnePadicIntegralAddSubgroup_isOpen p).preimage
      (continuous_const.mul continuous_id)
  have hUzero : (0 : ℚ_[p]) ∈ U := by simp [U]
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  let W : Set ℚ_[p] := {w | w - y ∈ U}
  have hWopen : IsOpen W :=
    hUopen.preimage (continuous_id.sub continuous_const)
  have hyW : y ∈ W := by simp [W, hUzero]
  filter_upwards [hWopen.mem_nhds hyW] with w hw
  let z : ℤ_[p] := ⟨q⁻¹ * (w - y), hw⟩
  have hwrep : w = y + (p : ℚ_[p]) ^ L * (z : ℚ_[p]) := by
    change w = y + q * (q⁻¹ * (w - y))
    rw [← mul_assoc, mul_inv_cancel₀ hq0, one_mul]
    abel
  rw [hwrep]
  exact hperiod y z

theorem fieldOnePadicDenominatorStage_isCompact (N : ℕ) :
    IsCompact (fieldOnePadicDenominatorStage p N : Set ℚ_[p]) := by
  rw [← fieldOnePadicInvPowIntCoeAddMonoidHom_range p N]
  rw [← Set.image_univ]
  exact isCompact_univ.image
    (fieldOnePadicInvPowIntCoeAddMonoidHom_isOpenEmbedding p N).continuous

theorem fieldOnePadicPrimitiveAngularProjectionValue_isLocallyConstant
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    IsLocallyConstant
      (fieldOnePadicPrimitiveAngularProjectionValue p n χ f) := by
  obtain ⟨_N, L, _hsupport, hperiod⟩ :=
    fieldOnePadicBruhat_exists_finiteLevel p f
  exact fieldOnePadic_isLocallyConstant_of_primePower_period p L _
    (fieldOnePadicPrimitiveAngularProjectionValue_add_primePow
      p n L χ f hperiod)

theorem fieldOnePadicPrimitiveAngularProjectionValue_hasCompactSupport
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    HasCompactSupport
      (fieldOnePadicPrimitiveAngularProjectionValue p n χ f) := by
  obtain ⟨N, _L, hsupport, _hperiod⟩ :=
    fieldOnePadicBruhat_exists_finiteLevel p f
  apply HasCompactSupport.of_support_subset_isCompact
    (fieldOnePadicDenominatorStage_isCompact p N)
  intro x hx
  by_contra hout
  exact hx (fieldOnePadicPrimitiveAngularProjectionValue_eq_zero_outside
    p n N χ f hsupport hout)

def fieldOnePadicPrimitiveAngularProjection (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    compactlySupportedLocallyConstant ℚ_[p] :=
  ⟨⟨fieldOnePadicPrimitiveAngularProjectionValue p n χ f,
      fieldOnePadicPrimitiveAngularProjectionValue_isLocallyConstant p n χ f⟩,
    fieldOnePadicPrimitiveAngularProjectionValue_hasCompactSupport p n χ f⟩

@[simp] theorem fieldOnePadicPrimitiveAngularProjection_apply
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : compactlySupportedLocallyConstant ℚ_[p]) (x : ℚ_[p]) :
    (fieldOnePadicPrimitiveAngularProjection p n χ f).1 x =
      fieldOnePadicPrimitiveAngularProjectionValue p n χ f x := rfl

theorem fieldOnePadicPrimitiveAngularProjectionValue_unit_covariance
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (v : ℤ_[p]ˣ) (x : ℚ_[p]) :
    fieldOnePadicPrimitiveAngularProjectionValue p n χ f
        (((v : ℤ_[p]) : ℚ_[p]) * x) =
      (fieldOnePadicPrimitiveUnitCharacter p n χ v)⁻¹ *
        fieldOnePadicPrimitiveAngularProjectionValue p n χ f x := by
  let H : ℤ_[p]ˣ → ℂ := fun w =>
    fieldOnePadicPrimitiveUnitCharacter p n χ (w * v⁻¹) *
      f.1 (((w : ℤ_[p]) : ℚ_[p]) * x)
  have htranslate := integral_mul_right_eq_self H v
    (μ := fieldOnePadicUnitNormalizedHaar p)
  have hleft : (fun u : ℤ_[p]ˣ => H (u * v)) =
      fun u => fieldOnePadicPrimitiveUnitCharacter p n χ u *
        f.1 (((u : ℤ_[p]) : ℚ_[p]) *
          (((v : ℤ_[p]) : ℚ_[p]) * x)) := by
    funext u
    unfold H
    rw [show (u * v) * v⁻¹ = u by group]
    congr 1
    apply congrArg f.1
    rw [show ((u * v : ℤ_[p]ˣ) : ℤ_[p]) =
      (u : ℤ_[p]) * (v : ℤ_[p]) by rfl, PadicInt.coe_mul]
    ring
  have hright : H = fun w =>
      (fieldOnePadicPrimitiveUnitCharacter p n χ v)⁻¹ *
        (fieldOnePadicPrimitiveUnitCharacter p n χ w *
          f.1 (((w : ℤ_[p]) : ℚ_[p]) * x)) := by
    funext w
    unfold H
    rw [fieldOnePadicPrimitiveUnitCharacter_mul,
      fieldOnePadicPrimitiveUnitCharacter_inv]
    ring
  unfold fieldOnePadicPrimitiveAngularProjectionValue
  rw [← hleft, htranslate, hright, integral_const_mul]

theorem fieldOnePadicPrimitiveAngularProjectionValue_zero
    (n : ℕ+) (χ : FieldOnePadicPrimitiveAngularCharacter p (n : ℕ))
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicPrimitiveAngularProjectionValue p (n : ℕ) χ f 0 = 0 := by
  unfold fieldOnePadicPrimitiveAngularProjectionValue
  simp only [mul_zero]
  rw [integral_mul_const,
    fieldOnePadicPrimitiveUnitCharacter_integral_eq_zero p n χ,
    zero_mul]

theorem fieldOnePadicValuationUnitCoordinate_mem_primePowerLattice
    (L : ℕ) (k : ℤ) (u : ℤ_[p]ˣ) (hk : (L : ℤ) ≤ k) :
    ∃ z : ℤ_[p],
      (((fieldOnePadicValuationUnitContinuousMulEquiv p)
        (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ L * (z : ℚ_[p]) := by
  let r : ℕ := (k - (L : ℤ)).toNat
  have hr : (r : ℤ) = k - (L : ℤ) :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  refine ⟨(p : ℤ_[p]) ^ r * (u : ℤ_[p]), ?_⟩
  change (p : ℚ_[p]) ^ k * ((u : ℤ_[p]) : ℚ_[p]) =
    (p : ℚ_[p]) ^ L *
      ((((p : ℤ_[p]) ^ r * (u : ℤ_[p])) : ℤ_[p]) : ℚ_[p])
  rw [PadicInt.coe_mul]
  have hpcoe : ((((p : ℤ_[p]) ^ r : ℤ_[p])) : ℚ_[p]) =
      (p : ℚ_[p]) ^ r := by norm_cast
  rw [hpcoe, ← zpow_natCast, ← zpow_natCast, ← mul_assoc,
    ← zpow_add₀]
  · rw [hr, show (L : ℤ) + (k - (L : ℤ)) = k by omega]
  · exact_mod_cast (Fact.out : Nat.Prime p).ne_zero

theorem fieldOnePadicPrimitiveAngularProjectionValue_coordinates_eq_zero_of_lt
    (n : ℕ) (N : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hsupport : tsupport (f.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p N)
    (k : ℤ) (u : ℤ_[p]ˣ) (hk : k < -(N : ℤ)) :
    fieldOnePadicPrimitiveAngularProjectionValue p n χ f
      (((fieldOnePadicValuationUnitContinuousMulEquiv p)
        (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) = 0 := by
  apply fieldOnePadicPrimitiveAngularProjectionValue_eq_zero_outside
    p n N χ f hsupport
  rw [fieldOnePadicDenominatorStage_coordinates_iff]
  omega

theorem fieldOnePadicPrimitiveAngularProjectionValue_coordinates_eq_zero_of_ge
    (n : ℕ+) (L : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p (n : ℕ))
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hperiod : ∀ x : ℚ_[p], ∀ z : ℤ_[p],
      f.1 (x + (p : ℚ_[p]) ^ L * (z : ℚ_[p])) = f.1 x)
    (k : ℤ) (u : ℤ_[p]ˣ) (hk : (L : ℤ) ≤ k) :
    fieldOnePadicPrimitiveAngularProjectionValue p (n : ℕ) χ f
      (((fieldOnePadicValuationUnitContinuousMulEquiv p)
        (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) = 0 := by
  obtain ⟨z, hz⟩ :=
    fieldOnePadicValuationUnitCoordinate_mem_primePowerLattice p L k u hk
  rw [hz, ← zero_add ((p : ℚ_[p]) ^ L * (z : ℚ_[p])),
    fieldOnePadicPrimitiveAngularProjectionValue_add_primePow
      p (n : ℕ) L χ f hperiod]
  exact fieldOnePadicPrimitiveAngularProjectionValue_zero p n χ f

theorem fieldOnePadicPrimitiveUnitCharacter_characterInv
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (u : ℤ_[p]ˣ) :
    fieldOnePadicPrimitiveUnitCharacter p n
        (fieldOnePadicPrimitiveAngularCharacterInv p n χ) u =
      (fieldOnePadicPrimitiveUnitCharacter p n χ u)⁻¹ := by
  unfold fieldOnePadicPrimitiveUnitCharacter
  rw [fieldOnePadicPrimitiveAngularCharacterInv_apply,
    MulChar.inv_apply_eq_inv']

def fieldOnePadicBruhatEvalLinear (x : ℚ_[p]) :
    compactlySupportedLocallyConstant ℚ_[p] →ₗ[ℂ] ℂ where
  toFun f := f.1 x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem fieldOnePadicBruhatEvalLinear_apply
    (x : ℚ_[p]) (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicBruhatEvalLinear p x f = f.1 x := rfl

theorem fieldOnePadicPrimitiveRadialPacketInvSynthesis_coordinates
    (n : ℕ) (hn : 0 < n)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (c : ℤ →₀ ℂ) (k : ℤ) (u : ℤ_[p]ˣ) :
    (fieldOnePadicPrimitiveRadialPacketInvSynthesis p n χ c).1
      (((fieldOnePadicValuationUnitContinuousMulEquiv p)
        (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) =
      c k * (fieldOnePadicPrimitiveUnitCharacter p n χ u)⁻¹ := by
  rw [fieldOnePadicPrimitiveRadialPacketInvSynthesis,
    Finsupp.linearCombination_apply, Finsupp.sum]
  change fieldOnePadicBruhatEvalLinear p _
    (∑ m ∈ c.support,
      c m • fieldOnePadicPrimitiveRadialPacket p n
        (fieldOnePadicPrimitiveAngularCharacterInv p n χ) m) = _
  rw [map_sum]
  simp only [map_smul, fieldOnePadicBruhatEvalLinear_apply, smul_eq_mul]
  change (∑ m ∈ c.support,
      c m *
        (fieldOnePadicPrimitiveRadialPacket p n
          (fieldOnePadicPrimitiveAngularCharacterInv p n χ) m).1
          (((fieldOnePadicValuationUnitContinuousMulEquiv p)
            (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p])) = _
  rw [Finset.sum_eq_single k]
  · rw [fieldOnePadicPrimitiveRadialPacket_coordinates p n hn]
    simp only [if_pos, fieldOnePadicPrimitiveUnitCharacter]
    rw [fieldOnePadicPrimitiveAngularCharacterInv_apply,
      MulChar.inv_apply_eq_inv']
  · intro m hm hmk
    rw [fieldOnePadicPrimitiveRadialPacket_coordinates p n hn,
      if_neg (Ne.symm hmk), mul_zero]
  · intro hk
    rw [Finsupp.notMem_support_iff.mp hk, zero_mul]

theorem fieldOnePadicPrimitiveAngularProjection_exists_radialPacketInvSynthesis
    (n : ℕ+) (χ : FieldOnePadicPrimitiveAngularCharacter p (n : ℕ))
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    ∃ c : ℤ →₀ ℂ,
      fieldOnePadicPrimitiveAngularProjection p (n : ℕ) χ f =
        fieldOnePadicPrimitiveRadialPacketInvSynthesis p (n : ℕ) χ c := by
  classical
  obtain ⟨N, L, hsupport, hperiod⟩ :=
    fieldOnePadicBruhat_exists_finiteLevel p f
  let coefficient : ℤ → ℂ := fun k =>
    fieldOnePadicPrimitiveAngularProjectionValue p (n : ℕ) χ f
      (((fieldOnePadicValuationUnitContinuousMulEquiv p)
        (Multiplicative.ofAdd k, 1) : ℚ_[p]ˣ) : ℚ_[p])
  have hcoefficient : ∀ k : ℤ, coefficient k ≠ 0 →
      k ∈ Finset.Ico (-(N : ℤ)) (L : ℤ) := by
    intro k hk0
    rw [Finset.mem_Ico]
    constructor
    · by_contra hnot
      have hk : k < -(N : ℤ) := lt_of_not_ge hnot
      exact hk0
        (fieldOnePadicPrimitiveAngularProjectionValue_coordinates_eq_zero_of_lt
          p (n : ℕ) N χ f hsupport k 1 hk)
    · by_contra hnot
      have hk : (L : ℤ) ≤ k := le_of_not_gt hnot
      exact hk0
        (fieldOnePadicPrimitiveAngularProjectionValue_coordinates_eq_zero_of_ge
          p n L χ f hperiod k 1 hk)
  let c : ℤ →₀ ℂ := Finsupp.onFinset
    (Finset.Ico (-(N : ℤ)) (L : ℤ)) coefficient hcoefficient
  refine ⟨c, ?_⟩
  have hfun :
      (fun x : ℚ_[p] =>
        (fieldOnePadicPrimitiveAngularProjection p (n : ℕ) χ f).1 x) =
      (fun x : ℚ_[p] =>
        (fieldOnePadicPrimitiveRadialPacketInvSynthesis p (n : ℕ) χ c).1 x) := by
    apply Continuous.ext_on (dense_compl_singleton (0 : ℚ_[p]))
    · exact (fieldOnePadicPrimitiveAngularProjection p (n : ℕ) χ f).1.continuous
    · exact (fieldOnePadicPrimitiveRadialPacketInvSynthesis
        p (n : ℕ) χ c).1.continuous
    · intro x hx
      have hx0 : x ≠ 0 := by simpa using hx
      let a : ℚ_[p]ˣ := Units.mk0 x hx0
      let z : Multiplicative ℤ × ℤ_[p]ˣ :=
        (fieldOnePadicValuationUnitContinuousMulEquiv p).symm a
      let k : ℤ := Multiplicative.toAdd z.1
      let u : ℤ_[p]ˣ := z.2
      have hcoordUnit :
          (fieldOnePadicValuationUnitContinuousMulEquiv p)
              (Multiplicative.ofAdd k, u) = a := by
        simp [k, u, z]
      have hxcoord : x =
          (((fieldOnePadicValuationUnitContinuousMulEquiv p)
            (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) := by
        rw [hcoordUnit]
        exact (Units.val_mk0 hx0).symm
      have hunitCoordinate :
          (((u : ℤ_[p]) : ℚ_[p])) *
              (((fieldOnePadicValuationUnitContinuousMulEquiv p)
                (Multiplicative.ofAdd k, 1) : ℚ_[p]ˣ) : ℚ_[p]) =
            (((fieldOnePadicValuationUnitContinuousMulEquiv p)
                (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) := by
        change (((u : ℤ_[p]) : ℚ_[p])) *
            ((p : ℚ_[p]) ^ k * 1) =
          (p : ℚ_[p]) ^ k * (((u : ℤ_[p]) : ℚ_[p]))
        ring
      rw [hxcoord]
      change (fieldOnePadicPrimitiveAngularProjection p (n : ℕ) χ f).1
          (((fieldOnePadicValuationUnitContinuousMulEquiv p)
            (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) =
        (fieldOnePadicPrimitiveRadialPacketInvSynthesis p (n : ℕ) χ c).1
          (((fieldOnePadicValuationUnitContinuousMulEquiv p)
            (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p])
      rw [fieldOnePadicPrimitiveRadialPacketInvSynthesis_coordinates
          p (n : ℕ) n.pos χ c k u]
      rw [← hunitCoordinate,
        fieldOnePadicPrimitiveAngularProjection_apply,
        fieldOnePadicPrimitiveAngularProjectionValue_unit_covariance]
      rw [show c k = coefficient k by
        exact Finsupp.onFinset_apply]
      change (fieldOnePadicPrimitiveUnitCharacter p (n : ℕ) χ u)⁻¹ *
          coefficient k = coefficient k *
            (fieldOnePadicPrimitiveUnitCharacter p (n : ℕ) χ u)⁻¹
      ring
  apply Subtype.ext
  exact LocallyConstant.ext fun x => congrFun hfun x

end
end GaloisForLFunctions.RHTower
