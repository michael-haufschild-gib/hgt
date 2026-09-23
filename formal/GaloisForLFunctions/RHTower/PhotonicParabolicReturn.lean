import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# Parabolic photonic return response

A rational binary transfer cell has a noncentral parabolic two-cell monodromy.
Its repeated transport, in a fixed nonsingular basis, has the convergent Dirichlet
response `[[ζ(s), ζ(s-1)], [0, ζ(s)]]` for `2 < Re s`.

On the open critical strip, analytic invertible row and column operations reduce
this response to `diag(1, ζ(s)^(2 : ℕ))`. Its defect confinement is equivalent to RH.
The defect kernel is isotropic for the two-mode flux; the flux annihilator
identifies the dual quotient rather than a positive form on that kernel.

The transfer matrices, series, and analytic reduction are formalized here.
A derivation of the slab propagators from Maxwell equations, the Laplace–Mellin
integral representation, and a physical Fourier duality are separate statements.
-/

open Complex Matrix
open scoped Matrix Matrix.Norms.Elementwise

namespace RHTower

def photonicUpper (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, b; 0, a]

theorem photonicUpper_mul (a b c d : ℂ) :
    photonicUpper a b * photonicUpper c d = photonicUpper (a * c) (a * d + b * c) := by
  simp [photonicUpper]

def photonicParabolic : Matrix (Fin 2) (Fin 2) ℂ := photonicUpper 1 1

/-- Repeated unipotent transport retains its linear nilpotent term. -/
theorem photonicParabolic_pow (n : ℕ) :
    photonicParabolic ^ n = photonicUpper 1 (n : ℂ) := by
  induction n with
  | zero => simp [photonicUpper, Matrix.one_fin_two]
  | succ n ih =>
    rw [pow_succ, ih, photonicParabolic, photonicUpper_mul]
    simp [add_comm]

noncomputable def photonicReturn (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  photonicUpper (riemannZeta s) (riemannZeta (s - 1))

private theorem photonic_hasSum_zeta {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) (riemannZeta s) := by
  have hsum : Summable (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  exact hsum.hasSum

private theorem photonic_return_weight (s : ℂ) (n : ℕ) :
    (1 / (n + 1 : ℂ) ^ s) * (n + 1 : ℂ) = 1 / (n + 1 : ℂ) ^ (s - 1) := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [Complex.cpow_sub _ _ hn, Complex.cpow_one]
  simp [div_eq_mul_inv, mul_comm]

/-- The actual repeated-cell series converges to the continued response in its initial half-plane. -/
theorem photonicReturn_hasSum :
    ∀ s : ℂ, 2 < s.re →
      HasSum (fun n : ℕ => (1 / (n + 1 : ℂ) ^ s) • photonicParabolic ^ (n + 1))
        (photonicReturn s) := by
  intro s hs
  have ha := photonic_hasSum_zeta (s := s) (by linarith)
  have hb := photonic_hasSum_zeta (s := s - 1) (by simp; linarith)
  apply Pi.hasSum.mpr
  intro i
  apply Pi.hasSum.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [photonicParabolic_pow, photonicUpper, photonicReturn] using ha
  · change HasSum (fun n : ℕ =>
      (1 / (n + 1 : ℂ) ^ s) * (photonicParabolic ^ (n + 1)) 0 1)
      (riemannZeta (s - 1))
    simp only [photonicParabolic_pow, photonicUpper, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Nat.cast_add, Nat.cast_one]
    simp_rw [photonic_return_weight]
    exact hb
  · simp [photonicParabolic_pow, photonicUpper, photonicReturn]
  · simpa [photonicParabolic_pow, photonicUpper, photonicReturn] using ha

theorem photonicReturn_det (s : ℂ) :
    (photonicReturn s).det = riemannZeta s ^ (2 : ℕ) := by
  simp [photonicReturn, photonicUpper, Matrix.det_fin_two, pow_two]

/-- Loss of invertibility detects precisely a zeta zero. -/
theorem photonicReturn_det_eq_zero_iff (s : ℂ) :
    (photonicReturn s).det = 0 ↔ riemannZeta s = 0 := by
  rw [photonicReturn_det]
  exact pow_eq_zero_iff (Nat.succ_ne_zero 1)

noncomputable def photonicBinaryCell : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / 5, 3 / 5; -12 / 5, -11 / 5]

noncomputable def photonicParabolicBasis : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; -2, -5 / 6]

/-- The binary transfer cell is the product of two exact oscillator slab matrices. -/
theorem photonicBinaryCell_eq_slab_product :
    photonicBinaryCell =
      !![3 / 5, 1 / 5; -16 / 5, 3 / 5] * !![3 / 5, 4 / 5; -4 / 5, 3 / 5] := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp [photonicBinaryCell] <;> ring

theorem photonicBinaryCell_det : photonicBinaryCell.det = 1 := by
  rw [Matrix.det_fin_two]
  dsimp [photonicBinaryCell]
  ring

theorem photonicParabolicBasis_det : photonicParabolicBasis.det = -5 / 6 := by
  rw [Matrix.det_fin_two]
  dsimp [photonicParabolicBasis]
  ring

theorem photonicBinaryCell_square_intertwines :
    photonicBinaryCell ^ (2 : ℕ) * photonicParabolicBasis =
      photonicParabolicBasis * photonicParabolic := by
  simp only [pow_two, photonicBinaryCell, photonicParabolicBasis,
    photonicParabolic, photonicUpper, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp <;> ring

theorem photonicBinaryCell_cover_intertwines (n : ℕ) :
    (photonicBinaryCell ^ (2 : ℕ)) ^ n * photonicParabolicBasis =
      photonicParabolicBasis * photonicParabolic ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc,
      photonicBinaryCell_square_intertwines, mul_assoc, ← pow_succ']

/-- The same return identity in the original binary-cell coordinates. -/
theorem photonicBinaryReturn_hasSum :
    ∀ s : ℂ, 2 < s.re →
      HasSum (fun n : ℕ => (1 / (n + 1 : ℂ) ^ s) •
        ((photonicBinaryCell ^ (2 : ℕ)) ^ (n + 1) * photonicParabolicBasis))
        (photonicParabolicBasis * photonicReturn s) := by
  intro s hs
  simpa only [photonicBinaryCell_cover_intertwines, Matrix.mul_smul] using
    (photonicReturn_hasSum s hs).mul_left photonicParabolicBasis

private theorem photonic_shift_zeta_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta (s - 1) ≠ 0 := by
  apply riemannZeta_ne_zero_of_re_lt_zero (by simp; linarith)
  intro n hn
  have hre := congrArg Complex.re hn
  simp at hre
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

noncomputable def photonicReturnLeft (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(riemannZeta (s - 1))⁻¹, 0; riemannZeta s, -riemannZeta (s - 1)]

noncomputable def photonicReturnRight (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, -riemannZeta s / riemannZeta (s - 1)]

/-- Analytic row and column operations join the two diagonal zero factors into one squared factor. -/
theorem photonicReturn_reduction :
    ∀ s : ℂ, 0 < s.re → s.re < 1 →
      photonicReturnLeft s * photonicReturn s * photonicReturnRight s =
        !![1, 0; 0, riemannZeta s ^ (2 : ℕ)] := by
  intro s h0 h1
  have hb := photonic_shift_zeta_ne_zero h0 h1
  simp only [photonicReturnLeft, photonicReturnRight, photonicReturn,
    photonicUpper, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp <;> field_simp <;> ring

/-- Both reducing matrices have unit determinant up to sign throughout the strip. -/
theorem photonicReturn_reduction_dets :
    ∀ s : ℂ, 0 < s.re → s.re < 1 →
      (photonicReturnLeft s).det = -1 ∧ (photonicReturnRight s).det = -1 := by
  intro s h0 h1
  have hb := photonic_shift_zeta_ne_zero h0 h1
  simp [photonicReturnLeft, photonicReturnRight, Matrix.det_fin_two, hb]

private theorem photonic_zeta_analytic {s : ℂ} (h1 : s.re < 1) :
    AnalyticAt ℂ riemannZeta s ∧
      AnalyticAt ℂ (fun z : ℂ => riemannZeta (z - 1)) s := by
  have hs : s ≠ 1 := by
    intro hs
    simp [hs] at h1
  have hs' : s - 1 ≠ 1 := by
    intro hs'
    have hre := congrArg Complex.re hs'
    simp only [Complex.sub_re, Complex.one_re] at hre
    linarith
  have hsub : AnalyticAt ℂ (fun z : ℂ => z - 1) s :=
    analyticAt_id.sub analyticAt_const
  exact ⟨analyticOn_riemannZeta s hs,
    (analyticOn_riemannZeta (s - 1) hs').comp (f := fun z : ℂ => z - 1) hsub⟩

/-- The response and both reducing matrices vary analytically across the entire open strip. -/
theorem photonicReturn_reduction_analytic :
    ∀ s : ℂ, 0 < s.re → s.re < 1 →
      AnalyticAt ℂ photonicReturn s ∧ AnalyticAt ℂ photonicReturnLeft s ∧
        AnalyticAt ℂ photonicReturnRight s := by
  intro s h0 h1
  obtain ⟨ha, hb⟩ := photonic_zeta_analytic h1
  have hbi := hb.inv (photonic_shift_zeta_ne_zero h0 h1)
  have hab : AnalyticAt ℂ (fun z : ℂ =>
      riemannZeta z * (riemannZeta (z - 1))⁻¹) s := ha.mul hbi
  constructor
  · apply analyticAt_pi_iff.mpr
    intro i
    apply analyticAt_pi_iff.mpr
    intro j
    fin_cases i <;> fin_cases j
    · exact ha
    · exact hb
    · exact analyticAt_const
    · exact ha
  constructor
  · apply analyticAt_pi_iff.mpr
    intro i
    apply analyticAt_pi_iff.mpr
    intro j
    fin_cases i <;> fin_cases j
    · exact hbi
    · exact analyticAt_const
    · exact ha
    · exact hb.neg
  · apply analyticAt_pi_iff.mpr
    intro i
    apply analyticAt_pi_iff.mpr
    intro j
    fin_cases i <;> fin_cases j
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · change AnalyticAt ℂ (fun z : ℂ => -riemannZeta z / riemannZeta (z - 1)) s
      convert hab.neg using 1
      funext z
      simp [div_eq_mul_inv]

/-- RH is equivalent to confinement of the nontrivial return defects. -/
theorem riemannHypothesis_iff_photonicReturn_confinement :
    RiemannHypothesis ↔
      ∀ s : ℂ, 0 < s.re → s.re < 1 → (photonicReturn s).det = 0 → s.re = 1 / 2 := by
  constructor
  · intro h s h0 h1 hz
    apply h s ((photonicReturn_det_eq_zero_iff s).mp hz)
    · rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      simp at hre
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro hs
      simp [hs] at h1
  · intro h s hz ht _
    have hs := riemannZeta_zero_re_mem_Ioo hz (fun n hn => ht ⟨n, by rw [hn]; ring⟩)
    exact h s hs.1 hs.2 ((photonicReturn_det_eq_zero_iff s).mpr hz)

/-- At a nontrivial zero the defect kernel is exactly the parabolic eigenline. -/
theorem photonicReturn_kernel_at_zero :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
      ∀ v : Fin 2 → ℂ, photonicReturn s *ᵥ v = 0 ↔ v 1 = 0 := by
  intro s h0 h1 hz v
  have hb := photonic_shift_zeta_ne_zero h0 h1
  have hv : photonicReturn s *ᵥ v = ![riemannZeta (s - 1) * v 1, 0] := by
    ext i
    fin_cases i <;> simp [photonicReturn, photonicUpper, hz, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
  rw [hv]
  constructor
  · intro h
    have hfirst := congrFun h 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at hfirst
    exact (mul_eq_zero.mp hfirst).resolve_left hb
  · intro h
    ext i
    fin_cases i <;> simp [h]

def photonicFlux (v w : Fin 2 → ℂ) : ℂ :=
  -I * (star (v 0) * w 1 - star (v 1) * w 0)

/-- The flux annihilator of the parabolic line is the same line. -/
theorem photonicFlux_annihilator (w : Fin 2 → ℂ) :
    (∀ a : ℂ, photonicFlux ![a, 0] w = 0) ↔ w 1 = 0 := by
  constructor
  · intro h
    have h1 := h 1
    simpa [photonicFlux, Complex.I_ne_zero] using h1
  · intro hw a
    simp [photonicFlux, hw]

/-- The preserved flux restricts to zero on the defect kernel. -/
theorem photonicReturn_kernel_flux_zero :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
      ∀ v w : Fin 2 → ℂ, photonicReturn s *ᵥ v = 0 →
        photonicReturn s *ᵥ w = 0 → photonicFlux v w = 0 := by
  intro s h0 h1 hz v w hv hw
  have hv1 := (photonicReturn_kernel_at_zero s h0 h1 hz v).mp hv
  have hw1 := (photonicReturn_kernel_at_zero s h0 h1 hz w).mp hw
  simp [photonicFlux, hv1, hw1]

end RHTower
