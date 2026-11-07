import GaloisForLFunctions.SelbergClass.Primon.PrincipalSeries
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Hermitian structure of the conformal principal series

The integer weight vectors embed in `ℓ²(ℤ)` with its usual positive Hermitian
form. On the principal line, raising and lowering are negative adjoints on
finite vectors. Thus their real sum and imaginary difference are
skew-symmetric, as required by the unitary Lie algebra realization.
-/

open GaloisForLFunctions.RHTower
open scoped ComplexConjugate

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The finite weight lattice inside its standard Hilbert completion. -/
def principalToL2 : SphericalKFiniteModel →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  Finsupp.linearCombination ℂ fun m => lp.single 2 m (1 : ℂ)

@[simp] theorem principalToL2_single (m : ℤ) (z : ℂ) :
    principalToL2 (Finsupp.single m z) = lp.single 2 m z := by
  rw [principalToL2, Finsupp.linearCombination_single]
  rw [← lp.single_smul]
  simp only [smul_eq_mul, mul_one]

/-- The embedding preserves every weight coordinate. -/
@[simp] theorem principalToL2_apply (v : SphericalKFiniteModel) (m : ℤ) :
    principalToL2 v m = v m := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw]
  | single n z => simp [lp.single_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]

theorem principalToL2_injective : Function.Injective principalToL2 := by
  intro v w h
  ext m
  simpa only [principalToL2_apply] using congrArg (fun x : lp (fun _ : ℤ => ℂ) 2 => x m) h

/-- Positive Hermitian pairing inherited from the weight Hilbert space. -/
def principalHermitian (v w : SphericalKFiniteModel) : ℂ :=
  inner ℂ (principalToL2 v) (principalToL2 w)

@[simp] theorem principalHermitian_single_left (m : ℤ) (z : ℂ)
    (v : SphericalKFiniteModel) :
    principalHermitian (Finsupp.single m z) v = conj z * v m := by
  simp [principalHermitian, lp.inner_single_left, RCLike.inner_apply, mul_comm]

@[simp] theorem principalHermitian_single_right (m : ℤ) (z : ℂ)
    (v : SphericalKFiniteModel) :
    principalHermitian v (Finsupp.single m z) = conj (v m) * z := by
  simp [principalHermitian, lp.inner_single_right, RCLike.inner_apply, mul_comm]

/-- Positivity is strict away from the zero finite vector. -/
theorem principalHermitian_self_eq_zero_iff (v : SphericalKFiniteModel) :
    principalHermitian v v = 0 ↔ v = 0 := by
  rw [principalHermitian, inner_self_eq_zero]
  exact ⟨fun h => principalToL2_injective (by simpa using h), fun h => by simp [h]⟩

/-- Neighboring ladder coefficients satisfy the principal-series adjoint relation. -/
theorem conj_principalRaiseCoefficient (ε : ℝ) (m : ℤ) :
    conj (principalRaiseCoefficient ε m) = -principalLowerCoefficient ε (m + 1) := by
  apply Complex.ext <;> simp [principalRaiseCoefficient, principalLowerCoefficient]
  ring

/-- Raising and lowering are negative adjoints on the entire finite weight lattice. -/
theorem principalHermitian_raising (ε : ℝ) (v w : SphericalKFiniteModel) :
    principalHermitian (principalRaising ε v) w =
      -principalHermitian v (principalLowering ε w) := by
  induction v using Finsupp.induction_linear with
  | zero => simp [principalHermitian]
  | add v u hv hu =>
    simp only [map_add, principalHermitian, inner_add_left] at hv hu ⊢
    rw [hv, hu]
    ring
  | single m z =>
    induction w using Finsupp.induction_linear with
    | zero => simp [principalHermitian]
    | add w u hw hu =>
      simp only [map_add, principalHermitian, inner_add_right] at hw hu ⊢
      rw [hw, hu]
      ring
    | single n c =>
      rw [principalRaising_single, principalLowering_single,
        principalHermitian_single_left, principalHermitian_single_right]
      by_cases h : m + 1 = n
      · subst n
        simp only [Finsupp.single_eq_same, add_sub_cancel_right, map_mul,
          conj_principalRaiseCoefficient]
        ring
      · have hn : n - 1 ≠ m := by omega
        simp [h, hn]

/-- The reverse adjoint relation follows from Hermitian symmetry. -/
theorem principalHermitian_lowering (ε : ℝ) (v w : SphericalKFiniteModel) :
    principalHermitian (principalLowering ε v) w =
      -principalHermitian v (principalRaising ε w) := by
  have h := congrArg conj (principalHermitian_raising ε w v)
  simpa only [principalHermitian, map_neg, inner_conj_symm, neg_neg] using
    congrArg Neg.neg h.symm

/-- The sum of the two ladders is skew-symmetric on finite vectors. -/
theorem principalHermitian_boost (ε : ℝ) (v w : SphericalKFiniteModel) :
    principalHermitian ((principalRaising ε + principalLowering ε) v) w =
      -principalHermitian v ((principalRaising ε + principalLowering ε) w) := by
  change principalHermitian (principalRaising ε v + principalLowering ε v) w =
    -principalHermitian v (principalRaising ε w + principalLowering ε w)
  have he := principalHermitian_raising ε v w
  have hf := principalHermitian_lowering ε v w
  simp only [principalHermitian, map_add, inner_add_left, inner_add_right] at he hf ⊢
  rw [he, hf]
  ring

/-- The imaginary difference gives the other skew-symmetric noncompact generator. -/
theorem principalHermitian_orthogonalBoost (ε : ℝ) (v w : SphericalKFiniteModel) :
    principalHermitian ((Complex.I • (principalRaising ε - principalLowering ε)) v) w =
      -principalHermitian v ((Complex.I • (principalRaising ε - principalLowering ε)) w) := by
  change principalHermitian (Complex.I • (principalRaising ε v - principalLowering ε v)) w =
    -principalHermitian v (Complex.I • (principalRaising ε w - principalLowering ε w))
  have he := principalHermitian_raising ε v w
  have hf := principalHermitian_lowering ε v w
  simp only [principalHermitian, map_smul, map_sub, inner_smul_left, inner_smul_right,
    inner_sub_left, inner_sub_right, Complex.conj_I] at he hf ⊢
  rw [he, hf]
  ring

/-- The compact weight operator is symmetric for the positive Hermitian form. -/
theorem principalHermitian_weight (ε : ℝ) (v w : SphericalKFiniteModel) :
    principalHermitian (sphericalPrincipalH v) w =
      principalHermitian v (sphericalPrincipalH w) := by
  have hc (u : SphericalKFiniteModel) : sphericalPrincipalH u =
      principalRaising ε (principalLowering ε u) -
        principalLowering ε (principalRaising ε u) := by
    exact (LinearMap.congr_fun (sphericalPrincipalE_comm_F (principalParameter ε)) u).symm
  rw [hc v, hc w]
  change inner ℂ (principalToL2 (_ - _)) (principalToL2 w) =
    inner ℂ (principalToL2 v) (principalToL2 (_ - _))
  simp only [map_sub, inner_sub_left, inner_sub_right]
  change principalHermitian (principalRaising ε (principalLowering ε v)) w -
      principalHermitian (principalLowering ε (principalRaising ε v)) w =
    principalHermitian v (principalRaising ε (principalLowering ε w)) -
      principalHermitian v (principalLowering ε (principalRaising ε w))
  rw [principalHermitian_raising, principalHermitian_lowering,
    principalHermitian_lowering, principalHermitian_raising]
  ring

/-- Multiplication by `i` converts the weight operator into a skew-symmetric rotation. -/
theorem principalHermitian_rotation (v w : SphericalKFiniteModel) :
    principalHermitian ((Complex.I • sphericalPrincipalH) v) w =
      -principalHermitian v ((Complex.I • sphericalPrincipalH) w) := by
  change principalHermitian (Complex.I • sphericalPrincipalH v) w =
    -principalHermitian v (Complex.I • sphericalPrincipalH w)
  have h := principalHermitian_weight 0 v w
  simp only [principalHermitian, map_smul, inner_smul_left, inner_smul_right,
    Complex.conj_I] at h ⊢
  rw [h]
  ring

end
end GaloisForLFunctions.SelbergClass.Primon
