import GaloisForLFunctions.RHTower.SelbergCusppieceAveraging
import GaloisForLFunctions.RHTower.SelbergEisensteinCriticalLine

open MeasureTheory UpperHalfPlane ModularGroup Set Complex
open scoped MatrixGroups Pointwise

/-!
# The constant terms of `E_∞` at the cusps of the `Γ(N)` cell

For a coset `c ∈ Γ̄(N)\PSL(2,ℤ)` with `SL(2,ℤ)` lift `σ_c` (`lift`), the constant term of `E_∞(·, u)` at the cusp
`R_c ∞` is `CT_c(u, y) = count₀(σ_c) y^u + N^{-1} φ_{∞,σ_c∞}(u) y^{1-u}` (`CT`): it is the period average
`∫_0^N E_∞(R_c(x+iy), u) dx = N CT_c(u, y)` for `Re u > 1` (`integral_eq_CT`), hence invariant under the right
`T`-shift of cosets (`CT_sh`), and `E_∞(R_c z, u) − CT_c(u, Im z) = E^*_{σ_c}(u, z)` (`poincare_sub_CT`).
-/

namespace GaloisForLFunctions.RHTower.SelbergCuspConstantTerm
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.SarnakXuePretrace
  GaloisForLFunctions.RHTower.SelbergCellCosetShift GaloisForLFunctions.RHTower.SelbergCusppieceAveraging
  GaloisForLFunctions.RHTower.SelbergEisensteinScatteringEntry GaloisForLFunctions.RHTower.SelbergEisensteinCuspConstant
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspExpansion GaloisForLFunctions.RHTower.SelbergEisensteinCuspFourier
  GaloisForLFunctions.RHTower.SelbergMaassMean
open CongruenceSubgroup

variable (N : ℕ) [NeZero N]

/-- An `SL(2, ℤ)` lift of the coset representative `R_c`. -/
noncomputable def lift (c : Cosets N) : SL(2, ℤ) := Quotient.out (Quotient.out c : PSL2Z)

omit [NeZero N] in
theorem lift_smul (c : Cosets N) (w : ℍ) : (Quotient.out c : PSL2Z) • w = lift N c • w := by
  conv_lhs => rw [← Quotient.out_eq (Quotient.out c : PSL2Z)]
  exact PSL2Z_mk_smul _ w

omit [NeZero N] in
theorem pt_eq (x y : ℝ) (hy : 0 < y) : pt x y hy = ofComplex (point x y) := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  ext; rw [ofComplex_apply_of_im_pos hp]; rfl

/-- The constant term of `E_∞(·, u)` at the cusp `R_c ∞`: `count₀ y^u + N^{-1} φ(u) y^{1-u}`. -/
noncomputable def CT (c : Cosets N) (u : ℂ) (y : ℝ) : ℂ :=
  (count0 N (lift N c) : ℂ) * ((y : ℝ) : ℂ) ^ u + (N : ℂ)⁻¹ * phiσ N (lift N c) u * ((y : ℝ) : ℂ) ^ (1 - u)

theorem integral_eq_CT (c : Cosets N) {u : ℂ} (hu : 1 < u.re) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..N, GaloisForLFunctions.RHTower.SelbergPoincare.poincare N 0 u ((Quotient.out c : PSL2Z) • pt x y hy) = N * CT N c u y := by
  simp_rw [lift_smul, pt_eq]
  rw [integral_poincare_cusp_phi N (lift N c) hu hy, CT]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp

/-- **The constant term is invariant under the right `T`-shift of cosets.** -/
theorem CT_sh (c : Cosets N) {u : ℂ} (hu : 1 < u.re) {y : ℝ} (hy : 0 < y) :
    CT N (sh N c) u y = CT N c u y := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hF : ∀ (γ : Gamma N) z, GaloisForLFunctions.RHTower.SelbergPoincare.poincare N 0 u ((γ : SL(2, ℤ)) • z) = GaloisForLFunctions.RHTower.SelbergPoincare.poincare N 0 u z :=
    fun γ z => GaloisForLFunctions.RHTower.SelbergPoincare.poincare_smul N 0 u z γ
  have h1 := integral_eq_CT N (sh N c) hu hy
  have h2 := integral_eq_CT N c hu hy
  have hshift : (fun x => GaloisForLFunctions.RHTower.SelbergPoincare.poincare N 0 u ((Quotient.out (sh N c) : PSL2Z) • pt x y hy)) =
      fun x => GaloisForLFunctions.RHTower.SelbergPoincare.poincare N 0 u ((Quotient.out c : PSL2Z) • pt (x + 1) y hy) := by
    funext x
    rw [F_out_sh N hF, show (T • pt x y hy) = (T ^ (1 : ℤ)) • pt x y hy by rw [zpow_one], T_zpow_pt]
    simp
  have hper : Function.Periodic (fun x => GaloisForLFunctions.RHTower.SelbergPoincare.poincare N 0 u ((Quotient.out c : PSL2Z) • pt x y hy)) N := by
    intro x
    have e : pt (x + N) y hy = T ^ (N : ℤ) • pt x y hy := by rw [T_zpow_pt]; simp
    simp only
    rw [e]
    exact F_out_periodic N hF c (pt x y hy)
  rw [hshift, intervalIntegral.integral_comp_add_right
    (fun x => GaloisForLFunctions.RHTower.SelbergPoincare.poincare N 0 u ((Quotient.out c : PSL2Z) • pt x y hy)) 1,
    zero_add] at h1
  have := hper.intervalIntegral_add_eq 1 0
  rw [zero_add, add_comm] at this
  rw [this, h2] at h1
  exact (mul_left_cancel₀ hN0 h1).symm

/-- **`E_∞(R_c z, u) − CT_c(u, Im z) = E^*_{σ_c}(u, z)`** for `Re u > 1`. -/
theorem poincare_sub_CT (c : Cosets N) {u : ℂ} (hu : 1 < u.re) (z : ℍ) :
    GaloisForLFunctions.RHTower.SelbergPoincare.poincare N 0 u ((Quotient.out c : PSL2Z) • z) - CT N c u z.im = Estarσ N (lift N c) u z := by
  rw [lift_smul, poincare_smul_expansion N (lift N c) hu z, CT]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hy := z.im_pos
  have e : cexp (-u * (Real.log N : ℂ)) * (((z.im / N : ℝ)) : ℂ) ^ (1 - u) =
      (N : ℂ)⁻¹ * ((z.im : ℝ) : ℂ) ^ (1 - u) := by
    have hyN : (0 : ℝ) < z.im / N := div_pos hy hN
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hyN.ne'), Complex.cpow_def_of_ne_zero
      (by exact_mod_cast hy.ne'), ← Complex.ofReal_log hyN.le, ← Complex.ofReal_log hy.le,
      Real.log_div hy.ne' hN.ne']
    have hNinv : (N : ℂ)⁻¹ = cexp (-(Real.log N : ℂ)) := by
      rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hN]; push_cast; rfl
    rw [hNinv, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  ring

end GaloisForLFunctions.RHTower.SelbergCuspConstantTerm
