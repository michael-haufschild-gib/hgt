import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.GaussianPELField
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Trace

/-! The Gaussian integral lattice has its standard alternating pairing
and compatible real complex structure. -/

noncomputable section

open NumberField
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.UPel.HT.GaussOne

theorem repr_coord (a b : ℤ) : bO.repr ((a : 𝓞 Qi) + b * ζO) = Finsupp.equivFunOnFinite.symm ![a, b] := by
  have : ((a : 𝓞 Qi) + b * ζO) = a • bO 0 + b • bO 1 := by simp [bO_zero, bO_one, zsmul_eq_mul]
  rw [this, map_add, map_zsmul, map_zsmul, bO.repr_self, bO.repr_self]
  ext i; fin_cases i <;> simp

theorem repr0 (a b : ℤ) : bO.repr ((a : 𝓞 Qi) + b * ζO) 0 = a := by simp [repr_coord]
theorem repr1 (a b : ℤ) : bO.repr ((a : 𝓞 Qi) + b * ζO) 1 = b := by simp [repr_coord]

/-- The unimodular alternating pairing in the integral basis. -/
def EF : LinearMap.BilinForm ℤ (𝓞 Qi) :=
  LinearMap.mk₂ ℤ (fun x y => bO.repr x 1 * bO.repr y 0 - bO.repr x 0 * bO.repr y 1)
    (fun x x' y => by simp only [map_add, Finsupp.add_apply]; ring)
    (fun r x y => by simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [map_add, Finsupp.add_apply]; ring)
    (fun r x y => by simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]; ring)

theorem EF_coord (a b c d : ℤ) : EF ((a : 𝓞 Qi) + b * ζO) ((c : 𝓞 Qi) + d * ζO) = b * c - a * d := by
  simp only [EF, LinearMap.mk₂_apply, repr0, repr1]

theorem mul_coord (a b c d : ℤ) : ((a : 𝓞 Qi) + b * ζO) * ((c : 𝓞 Qi) + d * ζO) =
    ((a * c - b * d : ℤ) : 𝓞 Qi) + ((a * d + b * c : ℤ) : 𝓞 Qi) * ζO := by
  push_cast; linear_combination (b * d : 𝓞 Qi) * ζO_sq

theorem bar_coord (a b : ℤ) : barO ((a : 𝓞 Qi) + b * ζO) = ((a : ℤ) : 𝓞 Qi) + ((-b : ℤ) : 𝓞 Qi) * ζO := by
  simp [barO_ζO]

theorem EF_alt (x : 𝓞 Qi) : EF x x = 0 := by
  obtain ⟨a, b, rfl⟩ := coordO x
  rw [EF_coord]; ring

theorem EF_adj (b x y : 𝓞 Qi) : EF (b * x) y = EF x (barO b * y) := by
  obtain ⟨a, a', rfl⟩ := coordO b
  obtain ⟨c, c', rfl⟩ := coordO x
  obtain ⟨d, d', rfl⟩ := coordO y
  rw [bar_coord, mul_coord, mul_coord, EF_coord, EF_coord]; ring

theorem ζ_mul_coord (c d : ℤ) : ζO * ((c : 𝓞 Qi) + d * ζO) = ((-d : ℤ) : 𝓞 Qi) + ((c : ℤ) : 𝓞 Qi) * ζO := by
  push_cast; linear_combination (d : 𝓞 Qi) * ζO_sq

theorem bO_zero' : bO 0 = ((1 : ℤ) : 𝓞 Qi) + ((0 : ℤ) : 𝓞 Qi) * ζO := by simp [bO_zero]
theorem bO_one' : bO 1 = ((0 : ℤ) : 𝓞 Qi) + ((1 : ℤ) : 𝓞 Qi) * ζO := by simp [bO_one]

theorem EF_ζ_bO (i j : Fin 2) : EF (ζO * bO i) (bO j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, bO_zero', bO_one', ζ_mul_coord, EF_coord] <;> norm_num

theorem EF_ζ (x y : 𝓞 Qi) : EF (ζO * x) (ζO * y) = EF x y := by
  rw [EF_adj, ← mul_assoc, barO_ζO, neg_mul, ζO_sq, neg_neg, one_mul]

theorem trace_mulLeft (a b : ℤ) :
    LinearMap.trace ℤ (𝓞 Qi) (LinearMap.mulLeft ℤ ((a : 𝓞 Qi) + b * ζO)) = 2 * a := by
  rw [LinearMap.trace_eq_matrix_trace ℤ bO, Matrix.trace_fin_two, LinearMap.toMatrix_apply,
    LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, bO_zero', bO_one', mul_coord,
    mul_coord, repr0, repr1]
  ring

def bR : Module.Basis (Fin 2) ℝ (ℝ ⊗[ℤ] 𝓞 Qi) := Algebra.TensorProduct.basis ℝ bO

theorem bR_apply (i : Fin 2) : bR i = 1 ⊗ₜ bO i := Algebra.TensorProduct.basis_apply _ _

/-- Multiplication by the fourth root gives the real complex structure. -/
def J : ℝ ⊗[ℤ] 𝓞 Qi →ₗ[ℝ] ℝ ⊗[ℤ] 𝓞 Qi := (LinearMap.mulLeft ℤ ζO).baseChange ℝ

theorem A_eq (b : 𝓞 Qi) (A : ℝ ⊗[ℤ] 𝓞 Qi →ₗ[ℝ] ℝ ⊗[ℤ] 𝓞 Qi) (h : ∀ x : 𝓞 Qi, A (1 ⊗ₜ x) = 1 ⊗ₜ (b • x)) :
    A = (LinearMap.mulLeft ℤ b).baseChange ℝ :=
  bR.ext fun i => by rw [bR_apply, h, LinearMap.baseChange_tmul, LinearMap.mulLeft_apply, smul_eq_mul]

theorem J_J (x : ℝ ⊗[ℤ] 𝓞 Qi) : J (J x) = -x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => simp [J, ← mul_assoc, ζO_sq, TensorProduct.tmul_neg]
  | add x y hx hy => rw [map_add, map_add, hx, hy, neg_add]

theorem J_EF (x y : ℝ ⊗[ℤ] 𝓞 Qi) : EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y := by
  have key : (EF.baseChange ℝ).compl₁₂ J J = EF.baseChange ℝ :=
    LinearMap.BilinForm.ext_basis bR fun i j => by
      rw [LinearMap.compl₁₂_apply, bR_apply, bR_apply, J, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, LinearMap.BilinForm.baseChange_tmul,
        LinearMap.BilinForm.baseChange_tmul, EF_ζ]
  exact LinearMap.congr_fun₂ key x y

theorem J_pos (x : ℝ ⊗[ℤ] 𝓞 Qi) (hx : x ≠ 0) : 0 < EF.baseChange ℝ (J x) x := by
  have hG : ∀ i j, EF.baseChange ℝ (J (bR i)) (bR j) = if i = j then 1 else 0 := by
    intro i j
    rw [bR_apply, bR_apply, J, LinearMap.baseChange_tmul, LinearMap.mulLeft_apply,
      LinearMap.BilinForm.baseChange_tmul, EF_ζ_bO]
    split_ifs <;> simp
  have hx' := bR.sum_repr x
  rw [Fin.sum_univ_two] at hx'
  have hne : ¬ (bR.repr x 0 = 0 ∧ bR.repr x 1 = 0) := by
    rintro ⟨h0, h1⟩
    apply hx
    rw [← hx', h0, h1, zero_smul, zero_smul, add_zero]
  rw [← hx']
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hG]
  simp only [Fin.isValue, ite_true, show ((0 : Fin 2) = 1) = False by omega, show ((1 : Fin 2) = 0) = False by omega,
    ite_false, mul_one, mul_zero, add_zero, zero_add]
  by_cases h0 : bR.repr x 0 = 0
  · have h1 : bR.repr x 1 ≠ 0 := fun h1 => hne ⟨h0, h1⟩
    nlinarith [mul_self_pos.2 h1, h0]
  · nlinarith [mul_self_pos.2 h0, mul_self_nonneg (bR.repr x 1)]

theorem filt : Finset.univ.filter (fun τ : Qi →+* ℂ => τ ((ζO : 𝓞 Qi) : Qi) = (starRingEnd ℂ) Complex.I) =
    {(starRingEnd ℂ).comp τ₀} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    apply emb_ext
    rw [← coe_ζO, h, RingHom.comp_apply, coe_ζO, τ₀_ii]
  · rintro rfl
    show (starRingEnd ℂ) (τ₀ (ζO : Qi)) = _
    rw [coe_ζO, τ₀_ii]

theorem τ₀_int (a b : ℤ) : τ₀ (((a : 𝓞 Qi) + b * ζO : 𝓞 Qi) : Qi) = (a : ℂ) + b * Complex.I := by
  have : (((a : 𝓞 Qi) + b * ζO : 𝓞 Qi) : Qi) = (a : Qi) + b * ii := by
    rw [← coe_ζO]; push_cast; rfl
  rw [this]; simp [τ₀_ii]

/-- The alternating pairing identifies the Gaussian lattice with its integral dual. -/
theorem EF_bij : Function.Bijective EF := by
  constructor
  · intro x y h
    obtain ⟨a, b, rfl⟩ := coordO x
    obtain ⟨c, d, rfl⟩ := coordO y
    have h0 := LinearMap.congr_fun h (bO 0)
    have h1 := LinearMap.congr_fun h (bO 1)
    rw [bO_zero', EF_coord, EF_coord] at h0
    rw [bO_one', EF_coord, EF_coord] at h1
    simp only [mul_one, mul_zero, sub_zero, zero_sub] at h0 h1
    rw [h0, neg_inj.mp h1]
  · intro f
    let a := -f (bO 1)
    let b := f (bO 0)
    refine ⟨(a : 𝓞 Qi) + b * ζO, bO.ext fun i => ?_⟩
    fin_cases i
    · change EF ((a : 𝓞 Qi) + b * ζO) (bO 0) = f (bO 0)
      rw [bO_zero', EF_coord]
      simp [b]
    · change EF ((a : 𝓞 Qi) + b * ζO) (bO 1) = f (bO 1)
      rw [bO_one', EF_coord]
      simp [a]

end GlobalTheory.UPel.HT.GaussOne
