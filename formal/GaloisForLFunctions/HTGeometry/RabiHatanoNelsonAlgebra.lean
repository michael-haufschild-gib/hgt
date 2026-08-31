import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-!
# Exact algebra from self-partitioned interfacial time crystals

Unconditional algebraic content of Huang--Yang, *Self-partitioned Interfacial Time Crystals*,
arXiv:2608.28126.  This module isolates results that do not depend on numerical phase diagrams,
asymptotic truncations, or existence assumptions: directional hopping symbols, periodic-boundary
residuals, imaginary-gauge skin modes, slow-spin tangency, Bogoliubov/Jacobian similarity,
generalized-Bloch determinants, resolvent shifts, and exact critical-balance laws.

All declarations are closed identities.  Complex units encode nonzero detunings where an inverse
is intrinsic to the paper's scaling law.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry.RabiHatanoNelson

noncomputable section

/-! ## Directional hopping and periodic-boundary data -/

/-- Directional nearest-neighbour symbol with forward hopping `J + κ` and backward hopping
`J - κ`. -/
def directionalHoppingSymbol (J κ q : ℝ) : ℂ :=
  ((J + κ : ℝ) : ℂ) * Complex.exp ((q : ℂ) * Complex.I) +
    ((J - κ : ℝ) : ℂ) * Complex.exp (-(q : ℂ) * Complex.I)

theorem directionalHoppingSymbol_eq (J κ q : ℝ) :
    directionalHoppingSymbol J κ q =
      (2 * J * Real.cos q : ℝ) + Complex.I * (2 * κ * Real.sin q : ℝ) := by
  rw [directionalHoppingSymbol, Complex.exp_mul_I]
  rw [Complex.exp_mul_I]
  rw [Complex.cos_neg, Complex.sin_neg]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

theorem directionalHoppingSymbol_re (J κ q : ℝ) :
    (directionalHoppingSymbol J κ q).re = 2 * J * Real.cos q := by
  rw [directionalHoppingSymbol_eq, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
  ring

theorem directionalHoppingSymbol_im (J κ q : ℝ) :
    (directionalHoppingSymbol J κ q).im = 2 * κ * Real.sin q := by
  rw [directionalHoppingSymbol_eq, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
  ring

theorem directionalHoppingSymbol_zero (J κ : ℝ) :
    directionalHoppingSymbol J κ 0 = 2 * J := by
  rw [directionalHoppingSymbol_eq]
  simp

theorem directionalHoppingSymbol_quarter (J κ : ℝ) :
    directionalHoppingSymbol J κ (Real.pi / 2) = 2 * κ * Complex.I := by
  rw [directionalHoppingSymbol_eq, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast
  ring

theorem directionalHopping_forward_sub_backward (J κ : ℝ) :
    (J + κ) - (J - κ) = 2 * κ := by ring

theorem directionalHopping_forward_mul_backward (J κ : ℝ) :
    (J + κ) * (J - κ) = J ^ 2 - κ ^ 2 := by ring

/-- Directional hopping satisfies passive reverse-adjoint reciprocity exactly in the reciprocal
case. -/
theorem directionalHopping_reverseAdjoint_iff (J κ : ℝ) :
    (((J - κ : ℝ) : ℂ) = star (((J + κ : ℝ) : ℂ))) ↔ κ = 0 := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  · rintro rfl
    norm_num

def photonDetuning (ω₀ J q : ℝ) : ℝ := ω₀ - 2 * J * Real.cos q

def dampingPlus (Γ κ q : ℝ) : ℝ := Γ + 2 * κ - 2 * κ * Real.sin q

def dampingMinus (Γ κ q : ℝ) : ℝ := Γ + 2 * κ + 2 * κ * Real.sin q

theorem dampingPlus_add_dampingMinus (Γ κ q : ℝ) :
    dampingPlus Γ κ q + dampingMinus Γ κ q = 2 * (Γ + 2 * κ) := by
  simp [dampingPlus, dampingMinus]
  ring

theorem dampingPlus_sub_dampingMinus (Γ κ q : ℝ) :
    dampingPlus Γ κ q - dampingMinus Γ κ q = -4 * κ * Real.sin q := by
  simp [dampingPlus, dampingMinus]
  ring

theorem dampingPlus_mul_dampingMinus (Γ κ q : ℝ) :
    dampingPlus Γ κ q * dampingMinus Γ κ q =
      (Γ + 2 * κ) ^ 2 - 4 * κ ^ 2 * Real.sin q ^ 2 := by
  simp [dampingPlus, dampingMinus]
  ring

theorem photonDetuning_zero (ω₀ J : ℝ) : photonDetuning ω₀ J 0 = ω₀ - 2 * J := by
  simp [photonDetuning]

theorem photonDetuning_quarter (ω₀ J : ℝ) :
    photonDetuning ω₀ J (Real.pi / 2) = ω₀ := by
  simp [photonDetuning, Real.cos_pi_div_two]

theorem dampingPlus_quarter (Γ κ : ℝ) :
    dampingPlus Γ κ (Real.pi / 2) = Γ := by
  simp [dampingPlus, Real.sin_pi_div_two]

theorem dampingMinus_quarter (Γ κ : ℝ) :
    dampingMinus Γ κ (Real.pi / 2) = Γ + 4 * κ := by
  simp [dampingMinus, Real.sin_pi_div_two]
  ring

/-- Real part of the paper's periodic-boundary instability equation after separating frequency
and damping. -/
def pbcRealResidual (Ω ω Γ κ Δ g₂ q : ℝ) : ℝ :=
  (Ω ^ 2 - ω ^ 2) *
      ((Γ + 2 * κ) ^ 2 - 4 * κ ^ 2 * Real.sin q ^ 2 + Δ ^ 2 - ω ^ 2) -
    4 * g₂ * Ω * Δ

/-- Imaginary part of the paper's periodic-boundary instability equation. -/
def pbcImagResidual (Ω ω Γ κ Δ g₂ q : ℝ) : ℝ :=
  (Ω ^ 2 - ω ^ 2) *
      ((Γ + 2 * κ) * ω + 2 * κ * Real.sin q * Δ) -
    4 * g₂ * Ω * κ * Real.sin q

theorem pbcRealResidual_quarter (Ω ω Γ κ ω₀ g₂ : ℝ) :
    pbcRealResidual Ω ω Γ κ ω₀ g₂ (Real.pi / 2) =
      (Ω ^ 2 - ω ^ 2) * (Γ * (Γ + 4 * κ) + ω₀ ^ 2 - ω ^ 2) -
        4 * g₂ * Ω * ω₀ := by
  rw [pbcRealResidual, Real.sin_pi_div_two]
  ring

theorem pbcImagResidual_quarter (Ω ω Γ κ ω₀ g₂ : ℝ) :
    pbcImagResidual Ω ω Γ κ ω₀ g₂ (Real.pi / 2) =
      (Ω ^ 2 - ω ^ 2) * ((Γ + 2 * κ) * ω + 2 * κ * ω₀) -
        4 * g₂ * Ω * κ := by
  rw [pbcImagResidual, Real.sin_pi_div_two]
  ring

/-- The uniform `q = 0` mode lies on the boundary at `J = ω₀/2` and `ω = Ω`. -/
theorem pbc_uniform_mode_on_boundary (Ω ω₀ Γ κ g₂ : ℝ) :
    pbcRealResidual Ω Ω Γ κ (photonDetuning ω₀ (ω₀ / 2) 0) g₂ 0 = 0 ∧
      pbcImagResidual Ω Ω Γ κ (photonDetuning ω₀ (ω₀ / 2) 0) g₂ 0 = 0 := by
  rw [pbcRealResidual, pbcImagResidual, photonDetuning,
    Real.cos_zero, Real.sin_zero]
  constructor <;> ring

/-- At zero photon loss the quarter mode has the coupling-free boundary root `ω = -ω₀`. -/
theorem pbc_lossless_quarter_mode_on_boundary (Ω ω₀ κ J : ℝ) :
    pbcRealResidual Ω (-ω₀) 0 κ
        (photonDetuning ω₀ J (Real.pi / 2)) 0 (Real.pi / 2) = 0 ∧
      pbcImagResidual Ω (-ω₀) 0 κ
        (photonDetuning ω₀ J (Real.pi / 2)) 0 (Real.pi / 2) = 0 := by
  rw [pbcRealResidual, pbcImagResidual, photonDetuning,
    Real.sin_pi_div_two, Real.cos_pi_div_two]
  constructor <;> ring

/-- Exact residual left by the static quarter-mode tuning `g² = Ωω₀/2`. -/
theorem pbc_static_quarter_fineTuning_defect (Ω ω₀ Γ κ : ℝ) :
    pbcRealResidual Ω 0 Γ κ ω₀ (Ω * ω₀ / 2) (Real.pi / 2) =
        Ω ^ 2 * (Γ * (Γ + 4 * κ) - ω₀ ^ 2) ∧
      pbcImagResidual Ω 0 Γ κ ω₀ (Ω * ω₀ / 2) (Real.pi / 2) = 0 := by
  constructor
  · rw [pbcRealResidual_quarter]
    ring
  · rw [pbcImagResidual_quarter]
    ring

/-! ## Imaginary gauge and skin modes -/

/-- Exponentially gauged sine mode used by the open-boundary similarity transform. -/
def skinSineMode (r k : ℝ) (n : ℕ) : ℝ := r ^ n * Real.sin (k * n)

private theorem sine_neighbor_sum (k : ℝ) (n : ℕ) :
    Real.sin (k * n) + Real.sin (k * (n + 2)) =
      2 * Real.cos k * Real.sin (k * (n + 1)) := by
  have hleft : k * (n : ℝ) = k * ((n : ℝ) + 1) - k := by ring
  have hright : k * ((n : ℝ) + 2) = k * ((n : ℝ) + 1) + k := by ring
  rw [hleft, hright, Real.sin_sub, Real.sin_add]
  ring

/-- The gauge `r^n` converts an asymmetric recurrence with hoppings `s r²` and `s` into a
reciprocal sine recurrence. -/
theorem skinSineMode_recurrence (s r k : ℝ) (n : ℕ) :
    (s * r ^ 2) * skinSineMode r k n + s * skinSineMode r k (n + 2) =
      (2 * s * r * Real.cos k) * skinSineMode r k (n + 1) := by
  rw [skinSineMode, skinSineMode, skinSineMode]
  rw [show r ^ (n + 2) = r ^ n * r ^ 2 by ring,
    show r ^ (n + 1) = r ^ n * r by ring]
  have hs := sine_neighbor_sum k n
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hs ⊢
  linear_combination s * r ^ n * r ^ 2 * hs

theorem skinSineMode_left_boundary (r k : ℝ) : skinSineMode r k 0 = 0 := by
  simp [skinSineMode]

def dirichletMomentum (N m : ℕ) : ℝ := (m : ℝ) * Real.pi / (N + 1 : ℕ)

theorem skinSineMode_right_boundary (r : ℝ) (N m : ℕ) :
    skinSineMode r (dirichletMomentum N m) (N + 1) = 0 := by
  have hden : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hphase : dirichletMomentum N m * (N + 1 : ℕ) = (m : ℝ) * Real.pi := by
    rw [dirichletMomentum]
    field_simp
  rw [skinSineMode, hphase, Real.sin_nat_mul_pi]
  ring

/-- Alternation reflects a Dirichlet sine momentum from `k` to `π-k`. -/
theorem alternating_reflects_sine_mode (k : ℝ) (j : ℕ) :
    (-1 : ℝ) ^ (j + 1) * Real.sin (k * j) =
      Real.sin ((Real.pi - k) * j) := by
  rw [sub_mul, show Real.pi * (j : ℝ) = (j : ℝ) * Real.pi by ring,
    Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
  simp [pow_succ]

/-- Pairing two skin-amplified amplitudes doubles the spatial exponent. -/
theorem skinPairingAmplification (r a b : ℂ) (n : ℕ) :
    (r ^ n * a) * (r ^ n * b) = r ^ (2 * n) * (a * b) := by
  rw [pow_mul]
  ring

/-! ## Slow time and spin-feedback tangency -/

def slowTime (g t : ℝ) : ℝ := g ^ 2 * t

theorem slowTime_coupling_rescale (c g t : ℝ) :
    slowTime (c * g) t = c ^ 2 * slowTime g t := by
  simp [slowTime]
  ring

/-- Rate of `|u|² + z²` under `du/dT = z d`, `dz/dT = -Re(conj u d)`. -/
def spinLengthRate (u d : ℂ) (z : ℝ) : ℝ :=
  2 * (star u * ((z : ℂ) * d)).re + 2 * z * (-(star u * d).re)

/-- Slow photon feedback is tangent to each spin sphere. -/
theorem spinLengthRate_eq_zero (u d : ℂ) (z : ℝ) : spinLengthRate u d z = 0 := by
  simp [spinLengthRate, Complex.mul_re]
  ring

theorem sum_spinLengthRate_eq_zero {ι : Type*} [Fintype ι]
    (u d : ι → ℂ) (z : ι → ℝ) :
    ∑ j, spinLengthRate (u j) (d j) (z j) = 0 := by
  simp [spinLengthRate_eq_zero]

/-! ## Periodic and generalized-Bloch Bogoliubov matrices -/

/-- Periodic-boundary Bogoliubov matrix, with the particle and hole diagonal entries abstracted as
`a` and `b`. -/
def periodicBdGMatrix (a b g Ω : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![a, 0, g, g;
     0, b, -g, -g;
     g, g, Ω, 0;
     -g, -g, 0, -Ω]

/-- Fixed particle/hole-to-real-spin coordinate transform from the paper. -/
def bdgCoordinateTransform : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 1;
     0, 0, Complex.I, -Complex.I]

def bdgCoordinateTransformInv : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1 / 2, -Complex.I / 2;
     0, 0, 1 / 2, Complex.I / 2]

/-- Mean-field Jacobian in real transverse-spin coordinates. -/
def meanFieldJacobianMatrix (a b g Ω : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![-Complex.I * a, 0, -Complex.I * g, 0;
     0, -Complex.I * b, Complex.I * g, 0;
     0, 0, 0, -Ω;
     2 * g, 2 * g, Ω, 0]

theorem bdgCoordinateTransform_mul_inv :
    bdgCoordinateTransform * bdgCoordinateTransformInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgCoordinateTransform, bdgCoordinateTransformInv,
      Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

theorem bdgCoordinateTransformInv_mul :
    bdgCoordinateTransformInv * bdgCoordinateTransform = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgCoordinateTransform, bdgCoordinateTransformInv,
      Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring_nf <;> simp [Complex.I_sq] <;> norm_num

/-- The mean-field Jacobian is exactly similar to `-i` times the BdG matrix. -/
theorem bdg_meanField_similarity (a b g Ω : ℂ) :
    bdgCoordinateTransform * ((-Complex.I) • periodicBdGMatrix a b g Ω) *
        bdgCoordinateTransformInv = meanFieldJacobianMatrix a b g Ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgCoordinateTransform, bdgCoordinateTransformInv, periodicBdGMatrix,
      meanFieldJacobianMatrix, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring_nf <;> simp [Complex.I_sq]

/-- Jacobian and BdG formulations have exactly the same characteristic polynomial. -/
theorem bdg_meanField_charpoly_eq (a b g Ω : ℂ) :
    (meanFieldJacobianMatrix a b g Ω).charpoly =
      (((-Complex.I) • periodicBdGMatrix a b g Ω)).charpoly := by
  let H := (-Complex.I) • periodicBdGMatrix a b g Ω
  calc
    (meanFieldJacobianMatrix a b g Ω).charpoly =
        (bdgCoordinateTransform * H * bdgCoordinateTransformInv).charpoly := by
      rw [bdg_meanField_similarity]
    _ = (bdgCoordinateTransform * (H * bdgCoordinateTransformInv)).charpoly := by
      rw [Matrix.mul_assoc]
    _ = ((H * bdgCoordinateTransformInv) * bdgCoordinateTransform).charpoly :=
      Matrix.charpoly_mul_comm _ _
    _ = H.charpoly := by
      rw [Matrix.mul_assoc, bdgCoordinateTransformInv_mul, Matrix.mul_one]
    _ = (((-Complex.I) • periodicBdGMatrix a b g Ω)).charpoly := rfl

/-- Exact periodic-boundary quartic determinant. -/
theorem periodicBdG_det_sub_scalar (a b g Ω E : ℂ) :
    (periodicBdGMatrix a b g Ω - Matrix.scalar (Fin 4) E).det =
      (E - a) * (E - b) * (E ^ 2 - Ω ^ 2) - 2 * Ω * g ^ 2 * (a - b) := by
  rw [Matrix.det_succ_row_zero]
  simp [periodicBdGMatrix, Matrix.det_fin_three, Matrix.scalar_apply,
    Fin.succAbove, Fin.sum_univ_four]
  ring

/-- Generalized-Bloch matrix with independent particle and hole symbols. -/
def generalizedBlochBdGMatrix (εp εh g Ω : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![εp, g, 0, g;
     g, Ω, g, 0;
     0, -g, -Ω, -g;
     -g, 0, -g, εh]

/-- Equation S60: exact generalized-Bloch quartic determinant. -/
theorem generalizedBlochBdG_det_sub_scalar (εp εh g Ω E : ℂ) :
    (generalizedBlochBdGMatrix εp εh g Ω - Matrix.scalar (Fin 4) E).det =
      (E ^ 2 - Ω ^ 2) * (E - εp) * (E - εh) -
        g ^ 2 * (Ω + εp) * (Ω - εh) := by
  rw [Matrix.det_succ_row_zero]
  simp [generalizedBlochBdGMatrix, Matrix.det_fin_three, Matrix.scalar_apply,
    Fin.succAbove, Fin.sum_univ_four]
  ring

/-- The reciprocal generalized-Bloch equation factors into two quadratics after clearing `β⁻¹`. -/
theorem generalizedBloch_quadratic_factorization (Jp Jm ω₀ δ β : ℂ) :
    (Jp * β ^ 2 - (ω₀ - δ) * β + Jm) *
        (Jp * β ^ 2 - (ω₀ + δ) * β + Jm) =
      (Jp * β ^ 2 - ω₀ * β + Jm) ^ 2 - δ ^ 2 * β ^ 2 := by
  ring

def generalizedBlochEta (Jp Jm ω₀ : ℂ) (β : ℂˣ) : ℂ :=
  ω₀ - Jp * (β : ℂ) - Jm * ((β⁻¹ : ℂˣ) : ℂ)

/-- Equation S63 as a polynomial identity with the inverse cleared. -/
theorem generalizedBloch_factorization_clears_inverse
    (Jp Jm ω₀ δ : ℂ) (β : ℂˣ) :
    ((β : ℂ) ^ 2) * (generalizedBlochEta Jp Jm ω₀ β ^ 2 - δ ^ 2) =
      (Jp * (β : ℂ) ^ 2 - (ω₀ - δ) * (β : ℂ) + Jm) *
        (Jp * (β : ℂ) ^ 2 - (ω₀ + δ) * (β : ℂ) + Jm) := by
  rw [generalizedBloch_quadratic_factorization]
  have hβ : (β : ℂ) ≠ 0 := Units.ne_zero β
  rw [generalizedBlochEta, Units.val_inv_eq_inv_val]
  field_simp [hβ]
  ring

/-! ## Shifted resolvents -/

/-- Photon generator shifted into the carrier frame. -/
def photonShiftedGenerator {n : ℕ} (L : Matrix (Fin n) (Fin n) ℂ) (ω₀ : ℝ) :=
  L - (Complex.I * (ω₀ : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)

theorem coRotating_resolvent_argument {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℂ) (Ω ω₀ : ℝ) :
    (Complex.I * (Ω : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        photonShiftedGenerator L ω₀ =
      (Complex.I * ((ω₀ + Ω : ℝ) : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ) - L := by
  ext i j
  simp [photonShiftedGenerator]
  ring

theorem counterRotating_resolvent_argument {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℂ) (Ω ω₀ : ℝ) :
    (-Complex.I * (Ω : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        photonShiftedGenerator L ω₀ =
      (Complex.I * ((ω₀ - Ω : ℝ) : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ) - L := by
  ext i j
  simp [photonShiftedGenerator]
  ring

/-- Co-rotating response probes the original photon generator at frequency `ω₀+Ω`. -/
theorem coRotating_resolvent {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℂ) (Ω ω₀ : ℝ) :
    ((Complex.I * (Ω : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        photonShiftedGenerator L ω₀)⁻¹ =
      ((Complex.I * ((ω₀ + Ω : ℝ) : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ) - L)⁻¹ := by
  rw [coRotating_resolvent_argument]

/-- Counter-rotating response probes the original photon generator at frequency `ω₀-Ω`. -/
theorem counterRotating_resolvent {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℂ) (Ω ω₀ : ℝ) :
    ((-Complex.I * (Ω : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        photonShiftedGenerator L ω₀)⁻¹ =
      ((Complex.I * ((ω₀ - Ω : ℝ) : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ) - L)⁻¹ := by
  rw [counterRotating_resolvent_argument]

/-! ## Interface and critical-scale balances -/

/-- Exact inverse-detuning width law, encoding exponent `-1`. -/
def firstOrderInterfaceWidth (a : ℂ) (δ : ℂˣ) : ℂ := a * ((δ⁻¹ : ℂˣ) : ℂ)

/-- Exact square-root inverse-detuning width law, encoding exponent `-1/2`. -/
def secondOrderInterfaceWidth (a : ℂ) (δ : ℂˣ) : ℂ :=
  Complex.sqrt (a * ((δ⁻¹ : ℂˣ) : ℂ))

theorem complex_sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  rw [Complex.sqrt]
  exact Complex.cpow_nat_inv_pow z (by norm_num)

theorem firstOrderInterfaceWidth_balance (a : ℂ) (δ : ℂˣ) :
    (δ : ℂ) * firstOrderInterfaceWidth a δ = a := by
  have hδ : (δ : ℂ) ≠ 0 := Units.ne_zero δ
  rw [firstOrderInterfaceWidth, Units.val_inv_eq_inv_val]
  field_simp [hδ]

theorem secondOrderInterfaceWidth_sq_eq_firstOrder (a : ℂ) (δ : ℂˣ) :
    secondOrderInterfaceWidth a δ ^ 2 = firstOrderInterfaceWidth a δ := by
  rw [secondOrderInterfaceWidth, complex_sqrt_sq]
  rfl

theorem secondOrderInterfaceWidth_balance (a : ℂ) (δ : ℂˣ) :
    (δ : ℂ) * secondOrderInterfaceWidth a δ ^ 2 = a := by
  rw [secondOrderInterfaceWidth_sq_eq_firstOrder,
    firstOrderInterfaceWidth_balance]

/-- Interior endpoint `κc = √2 Ω`. -/
def interiorCriticalKappa (Ω : ℝ) : ℝ := Real.sqrt 2 * Ω

/-- Interior endpoint `Jc = √(3/2) Ω`. -/
def interiorCriticalJ (Ω : ℝ) : ℝ := Real.sqrt (3 / 2) * Ω

theorem interiorCriticalKappa_sq (Ω : ℝ) : interiorCriticalKappa Ω ^ 2 = 2 * Ω ^ 2 := by
  rw [interiorCriticalKappa, mul_pow, Real.sq_sqrt (by norm_num)]

theorem interiorCriticalJ_sq (Ω : ℝ) :
    interiorCriticalJ Ω ^ 2 = (3 / 2 : ℝ) * Ω ^ 2 := by
  rw [interiorCriticalJ, mul_pow, Real.sq_sqrt (by norm_num)]

/-- Cleared polynomial for the exterior boundary `κ² = J²-Ω²/4`. -/
def exteriorCriticalPolynomialOne (J Ω κ : ℝ) : ℝ :=
  4 * κ ^ 2 - 4 * J ^ 2 + Ω ^ 2

/-- Cleared polynomial for the second exterior boundary. -/
def exteriorCriticalPolynomialTwo (J Ω κ : ℝ) : ℝ :=
  4 * (J ^ 2 - Ω ^ 2) * κ ^ 2 - (2 * J ^ 2 - Ω ^ 2) ^ 2

/-- Unconditional complex branch of the first exterior critical coupling. -/
def exteriorCriticalKappaOne (J Ω : ℂ) : ℂ :=
  Complex.sqrt (J ^ 2 - Ω ^ 2 / 4)

/-- Scaled second exterior coupling; unit `δ` represents its nonzero square-root denominator. -/
def exteriorCriticalKappaTwoScaled (J Ω : ℂ) (δ : ℂˣ) : ℂ :=
  (2 * J ^ 2 - Ω ^ 2) * ((2 * (δ : ℂ))⁻¹)

theorem exteriorCriticalKappaOne_sq (J Ω : ℂ) :
    exteriorCriticalKappaOne J Ω ^ 2 = J ^ 2 - Ω ^ 2 / 4 := by
  rw [exteriorCriticalKappaOne, complex_sqrt_sq]

theorem exteriorCriticalKappaOne_polynomial (J Ω : ℂ) :
    4 * exteriorCriticalKappaOne J Ω ^ 2 - 4 * J ^ 2 + Ω ^ 2 = 0 := by
  rw [exteriorCriticalKappaOne_sq]
  ring

theorem exteriorCriticalKappaTwoScaled_balance (J Ω : ℂ) (δ : ℂˣ) :
    2 * (δ : ℂ) * exteriorCriticalKappaTwoScaled J Ω δ =
      2 * J ^ 2 - Ω ^ 2 := by
  have hδ : (δ : ℂ) ≠ 0 := Units.ne_zero δ
  rw [exteriorCriticalKappaTwoScaled]
  field_simp [hδ]

theorem exteriorCriticalPolynomialOne_homogeneous (c J Ω κ : ℝ) :
    exteriorCriticalPolynomialOne (c * J) (c * Ω) (c * κ) =
      c ^ 2 * exteriorCriticalPolynomialOne J Ω κ := by
  simp [exteriorCriticalPolynomialOne]
  ring

theorem exteriorCriticalPolynomialTwo_homogeneous (c J Ω κ : ℝ) :
    exteriorCriticalPolynomialTwo (c * J) (c * Ω) (c * κ) =
      c ^ 4 * exteriorCriticalPolynomialTwo J Ω κ := by
  simp [exteriorCriticalPolynomialTwo]
  ring

end

end GaloisForLFunctions.HTGeometry.RabiHatanoNelson
