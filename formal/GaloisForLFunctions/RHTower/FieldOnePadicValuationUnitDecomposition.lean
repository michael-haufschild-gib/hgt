import GaloisForLFunctions.RHTower.FieldOnePadicMultiplicativeHaarTatePairing
import Mathlib.Analysis.Normed.Group.Ultra

open scoped NNReal BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

variable (p : ℕ) [Fact p.Prime]


def fieldOnePadicValuationUnitForward :
    Multiplicative ℤ × ℤ_[p]ˣ →* ℚ_[p]ˣ where
  toFun z := Units.mk0
    ((p : ℚ_[p]) ^ z.1.toAdd * ((z.2 : ℤ_[p]) : ℚ_[p]))
    (mul_ne_zero (zpow_ne_zero _ (by exact_mod_cast
      (Fact.out : Nat.Prime p).ne_zero))
      (PadicInt.coe_ne_zero.mpr (Units.ne_zero z.2)))
  map_one' := by
    apply Units.ext
    simp
  map_mul' x y := by
    apply Units.ext
    change
      (p : ℚ_[p]) ^ (x.1.toAdd + y.1.toAdd) *
          ((((x.2 * y.2 : ℤ_[p]ˣ) : ℤ_[p])) : ℚ_[p]) =
        ((p : ℚ_[p]) ^ x.1.toAdd * ((x.2 : ℤ_[p]) : ℚ_[p])) *
          ((p : ℚ_[p]) ^ y.1.toAdd * ((y.2 : ℤ_[p]) : ℚ_[p]))
    rw [zpow_add₀ (by exact_mod_cast
      (Fact.out : Nat.Prime p).ne_zero)]
    simp only [Units.val_mul, PadicInt.coe_mul]
    ring

theorem fieldOnePadic_valuation_coe_unit (u : ℤ_[p]ˣ) :
    Padic.valuation (((u : ℤ_[p]) : ℚ_[p])) = 0 := by
  rw [PadicInt.valuation_coe]
  have hu0 : (u : ℤ_[p]) ≠ 0 := Units.ne_zero u
  have hui0 : u.inv ≠ 0 := by
    intro h
    have := u.val_inv
    rw [h, mul_zero] at this
    exact zero_ne_one this
  have hval := PadicInt.valuation_mul hu0 hui0
  rw [u.val_inv, PadicInt.valuation_one] at hval
  omega

theorem fieldOnePadic_valuation_forward
    (z : Multiplicative ℤ × ℤ_[p]ˣ) :
    Padic.valuation ((fieldOnePadicValuationUnitForward p z : ℚ_[p])) =
      z.1.toAdd := by
  change Padic.valuation
      ((p : ℚ_[p]) ^ z.1.toAdd * ((z.2 : ℤ_[p]) : ℚ_[p])) =
    z.1.toAdd
  rw [Padic.valuation_mul]
  · rw [Padic.valuation_zpow, Padic.valuation_p,
      fieldOnePadic_valuation_coe_unit]
    simp
  · exact zpow_ne_zero _ (by exact_mod_cast
      (Fact.out : Nat.Prime p).ne_zero)
  · exact PadicInt.coe_ne_zero.mpr (Units.ne_zero z.2)

theorem fieldOnePadicValuationUnitForward_injective :
    Function.Injective (fieldOnePadicValuationUnitForward p) := by
  intro x y hxy
  have hval := congrArg (fun a : ℚ_[p]ˣ => Padic.valuation (a : ℚ_[p])) hxy
  rw [fieldOnePadic_valuation_forward, fieldOnePadic_valuation_forward] at hval
  apply Prod.ext
  · exact Multiplicative.toAdd.injective hval
  · apply Units.ext
    have hxyval := congrArg Units.val hxy
    change
      (p : ℚ_[p]) ^ x.1.toAdd * ((x.2 : ℤ_[p]) : ℚ_[p]) =
        (p : ℚ_[p]) ^ y.1.toAdd * ((y.2 : ℤ_[p]) : ℚ_[p]) at hxyval
    rw [hval] at hxyval
    have hucoe : ((x.2 : ℤ_[p]) : ℚ_[p]) = ((y.2 : ℤ_[p]) : ℚ_[p]) :=
      mul_left_cancel₀
        (zpow_ne_zero y.1.toAdd (by exact_mod_cast
          (Fact.out : Nat.Prime p).ne_zero)) hxyval
    exact Subtype.coe_injective hucoe

def fieldOnePadicAngularUnit (a : ℚ_[p]ˣ) : ℤ_[p]ˣ := by
  let v : ℤ := Padic.valuation (a : ℚ_[p])
  let u : ℚ_[p] := (p : ℚ_[p]) ^ (-v) * (a : ℚ_[p])
  have ha0 : (a : ℚ_[p]) ≠ 0 := Units.ne_zero a
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_mul, Padic.norm_p_zpow,
      Padic.norm_eq_zpow_neg_valuation ha0]
    rw [← zpow_add₀]
    · simp [v]
    · exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  exact PadicInt.mkUnits hu

@[simp] theorem fieldOnePadicAngularUnit_coe (a : ℚ_[p]ˣ) :
    (((fieldOnePadicAngularUnit p a : ℤ_[p]) : ℚ_[p])) =
      (p : ℚ_[p]) ^ (-Padic.valuation (a : ℚ_[p])) * (a : ℚ_[p]) := by
  rfl

theorem fieldOnePadicValuationUnitForward_surjective :
    Function.Surjective (fieldOnePadicValuationUnitForward p) := by
  intro a
  let v : ℤ := Padic.valuation (a : ℚ_[p])
  refine ⟨(Multiplicative.ofAdd v, fieldOnePadicAngularUnit p a), ?_⟩
  apply Units.ext
  change (p : ℚ_[p]) ^ v *
      (((fieldOnePadicAngularUnit p a : ℤ_[p]) : ℚ_[p])) = (a : ℚ_[p])
  rw [fieldOnePadicAngularUnit_coe]
  rw [← mul_assoc, ← zpow_add₀]
  · simp [v]
  · exact_mod_cast (Fact.out : Nat.Prime p).ne_zero

def fieldOnePadicValuationUnitMulEquiv :
    Multiplicative ℤ × ℤ_[p]ˣ ≃* ℚ_[p]ˣ :=
  MulEquiv.ofBijective (fieldOnePadicValuationUnitForward p)
    ⟨fieldOnePadicValuationUnitForward_injective p,
      fieldOnePadicValuationUnitForward_surjective p⟩

@[simp] theorem fieldOnePadicValuationUnitMulEquiv_symm_apply
    (a : ℚ_[p]ˣ) :
    (fieldOnePadicValuationUnitMulEquiv p).symm a =
      (Multiplicative.ofAdd (Padic.valuation (a : ℚ_[p])),
        fieldOnePadicAngularUnit p a) := by
  apply (fieldOnePadicValuationUnitMulEquiv p).injective
  rw [MulEquiv.apply_symm_apply]
  apply Units.ext
  change (a : ℚ_[p]) =
    (p : ℚ_[p]) ^ Padic.valuation (a : ℚ_[p]) *
      (((fieldOnePadicAngularUnit p a : ℤ_[p]) : ℚ_[p]))
  rw [fieldOnePadicAngularUnit_coe, ← mul_assoc,
    ← zpow_add₀]
  · simp
  · exact_mod_cast (Fact.out : Nat.Prime p).ne_zero

@[simp] theorem fieldOnePadicAngularUnit_coordinates
    (k : ℤ) (u : ℤ_[p]ˣ) :
    fieldOnePadicAngularUnit p
      ((fieldOnePadicValuationUnitMulEquiv p)
        (Multiplicative.ofAdd k, u)) = u := by
  have h := congrArg Prod.snd
    ((fieldOnePadicValuationUnitMulEquiv p).symm_apply_apply
      (Multiplicative.ofAdd k, u))
  rw [fieldOnePadicValuationUnitMulEquiv_symm_apply] at h
  exact h

theorem fieldOnePadic_valuation_eq_of_norm_eq
    {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ‖x‖ = ‖y‖) : Padic.valuation x = Padic.valuation y := by
  rw [Padic.norm_eq_zpow_neg_valuation hx,
    Padic.norm_eq_zpow_neg_valuation hy] at h
  have hpPos : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hpNeOne : (p : ℝ) ≠ 1 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_one
  have hneg : -Padic.valuation x = -Padic.valuation y :=
    (zpow_right_inj₀ hpPos hpNeOne).mp h
  exact neg_injective hneg

theorem fieldOnePadic_valuation_isLocallyConstant :
    IsLocallyConstant
      (fun a : ℚ_[p]ˣ => Multiplicative.ofAdd
        (Padic.valuation (a : ℚ_[p]))) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro a
  let U : Set ℚ_[p]ˣ :=
    (fun b : ℚ_[p]ˣ => (b : ℚ_[p])) ⁻¹'
      Metric.ball (a : ℚ_[p]) ‖(a : ℚ_[p])‖
  refine ⟨U, ?_, ?_, ?_⟩
  · exact (Units.continuous_val : Continuous
      (fun b : ℚ_[p]ˣ => (b : ℚ_[p]))).isOpen_preimage _ Metric.isOpen_ball
  · change dist (a : ℚ_[p]) (a : ℚ_[p]) < ‖(a : ℚ_[p])‖
    rw [dist_self]
    exact norm_pos_iff.mpr (Units.ne_zero a)
  · intro b hb
    apply Multiplicative.ofAdd.injective
    apply fieldOnePadic_valuation_eq_of_norm_eq p
        (Units.ne_zero b) (Units.ne_zero a)
    have hdist : ‖(b : ℚ_[p]) - (a : ℚ_[p])‖ < ‖(a : ℚ_[p])‖ := by
      simpa only [U, Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hb
    have hne : ‖(b : ℚ_[p]) - (a : ℚ_[p])‖ ≠ ‖(a : ℚ_[p])‖ :=
      ne_of_lt hdist
    calc
      ‖(b : ℚ_[p])‖ =
          ‖((b : ℚ_[p]) - (a : ℚ_[p])) + (a : ℚ_[p])‖ := by ring_nf
      _ = max ‖(b : ℚ_[p]) - (a : ℚ_[p])‖ ‖(a : ℚ_[p])‖ :=
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      _ = ‖(a : ℚ_[p])‖ := max_eq_right hdist.le

theorem continuous_fieldOnePadic_valuation :
    Continuous
      (fun a : ℚ_[p]ˣ => Multiplicative.ofAdd
        (Padic.valuation (a : ℚ_[p]))) :=
  (fieldOnePadic_valuation_isLocallyConstant p).continuous

theorem fieldOnePadic_coe_unit_inv (u : ℤ_[p]ˣ) :
    (((((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) : ℚ_[p])) =
      ((((u : ℤ_[p]) : ℚ_[p]))⁻¹) := by
  have hQ :
      (((u : ℤ_[p]) : ℚ_[p])) *
          (((((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) : ℚ_[p])) = 1 := by
    change ((u.val : ℤ_[p]) : ℚ_[p]) * ((u.inv : ℤ_[p]) : ℚ_[p]) = 1
    exact congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) u.val_inv
  exact ((mul_eq_one_iff_inv_eq₀
    (PadicInt.coe_ne_zero.mpr (Units.ne_zero u))).mp hQ).symm

theorem continuous_fieldOnePadicAngularUnit :
    Continuous (fieldOnePadicAngularUnit p) := by
  have hpow : Continuous (fun a : ℚ_[p]ˣ =>
      (p : ℚ_[p]) ^ (-Padic.valuation (a : ℚ_[p]))) := by
    let g : Multiplicative ℤ → ℚ_[p] :=
      fun z => (p : ℚ_[p]) ^ (-z.toAdd)
    have hg : Continuous g := continuous_of_discreteTopology
    exact hg.comp (continuous_fieldOnePadic_valuation p)
  have hcoe : Continuous (fun a : ℚ_[p]ˣ =>
      (((fieldOnePadicAngularUnit p a : ℤ_[p]) : ℚ_[p]))) := by
    have hmul := hpow.mul (Units.continuous_val : Continuous
      (fun a : ℚ_[p]ˣ => (a : ℚ_[p])))
    convert hmul using 1
    funext a
    exact (fieldOnePadicAngularUnit_coe p a).symm
  apply Units.continuous_iff.mpr
  constructor
  · exact PadicInt.isOpenEmbedding_coe.isEmbedding.continuous_iff.mpr hcoe
  · have hinvZ : Continuous (fun a : ℚ_[p]ˣ =>
        (((fieldOnePadicAngularUnit p a)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) := by
      apply PadicInt.isOpenEmbedding_coe.isEmbedding.continuous_iff.mpr
      have hinv := hcoe.inv₀ (fun a => PadicInt.coe_ne_zero.mpr
        (Units.ne_zero (fieldOnePadicAngularUnit p a)))
      convert hinv using 1
      funext a
      exact fieldOnePadic_coe_unit_inv p _
    exact hinvZ

theorem continuous_fieldOnePadicValuationUnitForward :
    Continuous (fieldOnePadicValuationUnitForward p) := by
  let g : Multiplicative ℤ → ℚ_[p] :=
    fun z => (p : ℚ_[p]) ^ z.toAdd
  have hg : Continuous g := continuous_of_discreteTopology
  have hpow : Continuous (fun z : Multiplicative ℤ × ℤ_[p]ˣ =>
      (p : ℚ_[p]) ^ z.1.toAdd) := hg.comp continuous_fst
  have huZ : Continuous (fun z : Multiplicative ℤ × ℤ_[p]ˣ =>
      (z.2 : ℤ_[p])) :=
    (Units.continuous_val : Continuous (fun u : ℤ_[p]ˣ => (u : ℤ_[p]))).comp
      continuous_snd
  have huQ : Continuous (fun z : Multiplicative ℤ × ℤ_[p]ˣ =>
      ((z.2 : ℤ_[p]) : ℚ_[p])) :=
    PadicInt.isOpenEmbedding_coe.continuous.comp huZ
  have hcoe : Continuous (fun z : Multiplicative ℤ × ℤ_[p]ˣ =>
      (p : ℚ_[p]) ^ z.1.toAdd * ((z.2 : ℤ_[p]) : ℚ_[p])) :=
    hpow.mul huQ
  apply Units.continuous_iff.mpr
  constructor
  · convert hcoe using 1
    funext z
    rfl
  · have hinv := hcoe.inv₀ (fun z => mul_ne_zero
      (zpow_ne_zero _ (by exact_mod_cast
        (Fact.out : Nat.Prime p).ne_zero))
      (PadicInt.coe_ne_zero.mpr (Units.ne_zero z.2)))
    convert hinv using 1
    funext z
    simp [fieldOnePadicValuationUnitForward]

theorem continuous_fieldOnePadicValuationUnitMulEquiv_symm :
    Continuous (fieldOnePadicValuationUnitMulEquiv p).symm := by
  have hformula : (fun a : ℚ_[p]ˣ =>
      (Multiplicative.ofAdd (Padic.valuation (a : ℚ_[p])),
        fieldOnePadicAngularUnit p a)) =
      (fieldOnePadicValuationUnitMulEquiv p).symm := by
    funext a
    have hleft :
        (fieldOnePadicValuationUnitMulEquiv p)
          (Multiplicative.ofAdd (Padic.valuation (a : ℚ_[p])),
            fieldOnePadicAngularUnit p a) = a := by
      apply Units.ext
      change (p : ℚ_[p]) ^ Padic.valuation (a : ℚ_[p]) *
        (((fieldOnePadicAngularUnit p a : ℤ_[p]) : ℚ_[p])) = (a : ℚ_[p])
      rw [fieldOnePadicAngularUnit_coe, ← mul_assoc,
        ← zpow_add₀]
      · simp
      · exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    apply (fieldOnePadicValuationUnitMulEquiv p).injective
    rw [hleft, MulEquiv.apply_symm_apply]
  rw [← hformula]
  exact (continuous_fieldOnePadic_valuation p).prodMk
    (continuous_fieldOnePadicAngularUnit p)

def fieldOnePadicValuationUnitHomeomorph :
    Multiplicative ℤ × ℤ_[p]ˣ ≃ₜ ℚ_[p]ˣ where
  toEquiv := fieldOnePadicValuationUnitMulEquiv p
  continuous_toFun := continuous_fieldOnePadicValuationUnitForward p
  continuous_invFun := continuous_fieldOnePadicValuationUnitMulEquiv_symm p

end
end GaloisForLFunctions.RHTower
