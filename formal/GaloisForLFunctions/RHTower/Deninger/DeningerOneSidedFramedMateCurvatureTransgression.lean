import GaloisForLFunctions.RHTower.Deninger.DeningerRamifiedTopConormalAmbidexterity
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittGammaTensorSquareMateIdentification

/-!
# One-sided framed mate-curvature transgression

The coherent top-conormal shift `n - 1` is the upper-right entry of the
flat affine power-semigroup representation

`A n = !![n, n - 1; 0, 1]`.

A Deninger half-density mate gain placed on both terms would be a scalar
twist.  The framed power correspondence has two distinct cotangent terms,
so the gain can instead act on the conormal term only.  This one-sided twist
does not commute with the affine transport.  Its exact composition curvature
is upper triangular, obeys the nonabelian Bianchi identity, and vanishes
exactly on the critical half-density section.

The difference between reduced curvatures for the mate gain and its inverse
is exactly the already-defined Deninger tensor-square mate curvature.  At
degree six it is therefore, up to the existing strictly positive
calibration, the literal ordered `(2,3)` Gamma/Calderon--Witt boundary
coefficient.  No Xi-zero location or curvature-vanishing premise is used.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Flat affine top-conormal transport -/

/-- Affine matrix representation of the coherent top-conormal displacement
`r_n = n - 1`. -/
def deningerTopConormalAffineTransport (n : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![(n : ℝ), (n : ℝ) - 1; 0, 1]

/-- The scalar top-conormal affine transport is flat under power
composition. -/
theorem deningerTopConormalAffineTransport_mul (m n : ℕ) :
    deningerTopConormalAffineTransport m *
        deningerTopConormalAffineTransport n =
      deningerTopConormalAffineTransport (m * n) := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [deningerTopConormalAffineTransport,
    Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- Every coherent monomial power sector is an affine coboundary with
potential zero or one.  Thus neither the raw nor top-conormal scalar sector
can supply nonflat horizontal curvature by itself. -/
theorem deningerCoherentPowerShift_is_affineCoboundary (r : ℕ → ℕ)
    (hrange : ∀ n, 0 < n → r n < n)
    (hcomp : ∀ m n, 0 < m → 0 < n →
      r (m * n) = m * r n + r m) :
    ∃ c : ℕ, (c = 0 ∨ c = 1) ∧
      ∀ n, 0 < n → r n = n * c - c := by
  rcases GaloisForLFunctions.deningerCoherentPowerShift_eq_raw_or_topConormal
      r hrange hcomp with
    hraw | htop
  · refine ⟨0, Or.inl rfl, ?_⟩
    intro n hn
    simp [hraw n hn]
  · refine ⟨1, Or.inr rfl, ?_⟩
    intro n hn
    simp [htop n hn]

/-! ## One-sided framed curvature -/

/-- Character twist acting on the conormal term of the affine framed
transport, but not on its differential term. -/
def deningerOneSidedFramedTransport (chi : ℕ → ℝ) (n : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![chi n * (n : ℝ), chi n * ((n : ℝ) - 1); 0, 1]

/-- Literal one-sided realization: diagonal conormal gain followed by flat
top-conormal affine transport. -/
theorem deningerOneSidedFramedTransport_eq_diagonal_mul
    (chi : ℕ → ℝ) (n : ℕ) :
    deningerOneSidedFramedTransport chi n =
      Matrix.diagonal (fun i : Fin 2 => if i = 0 then chi n else 1) *
        deningerTopConormalAffineTransport n := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [deningerOneSidedFramedTransport,
    deningerTopConormalAffineTransport, Matrix.mul_apply,
    Fin.sum_univ_succ]

/-- Composition curvature of any natural-number-indexed matrix transport. -/
def deningerFramedCompositionCurvature
    (T : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (m n : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  T m * T n - T (m * n)

/-- **Exact one-sided framed curvature.**  A multiplicative gain placed on
only the conormal term creates one upper-right two-curvature. -/
theorem deningerOneSidedFramedCurvature_eq
    (chi : ℕ → ℝ) (m n : ℕ)
    (hchi : chi (m * n) = chi m * chi n) :
    deningerFramedCompositionCurvature
        (deningerOneSidedFramedTransport chi) m n =
      !![0, chi m * ((m : ℝ) - 1) * (1 - chi n); 0, 0] := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [deningerFramedCompositionCurvature,
    deningerOneSidedFramedTransport, hchi]
  all_goals ring

/-- The composition curvature obeys the nonabelian Bianchi identity.  Both
sides expand to the same threefold transport defect. -/
theorem deningerFramedCompositionCurvature_bianchi
    (T : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (l m n : ℕ) :
    deningerFramedCompositionCurvature T l m * T n +
        deningerFramedCompositionCurvature T (l * m) n =
      T l * deningerFramedCompositionCurvature T m n +
        deningerFramedCompositionCurvature T l (m * n) := by
  simp only [deningerFramedCompositionCurvature]
  noncomm_ring

/-- Curvature after removing its canonical left conormal source factor. -/
def deningerOneSidedReducedCurvature (chi : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 - chi n

/-! ## Deninger half-density mate gain -/

/-- Positive radial source-inverse gain of the Deninger half-density
character. -/
def deningerHalfDensityMateGain (n : ℕ) (s : ℂ) : ℝ :=
  Real.exp ((2 * s.re - 1) * Real.log n)

theorem deningerHalfDensityMateGain_pos (n : ℕ) (s : ℂ) :
    0 < deningerHalfDensityMateGain n s :=
  Real.exp_pos _

/-- The explicit gain is the inverse squared norm of the half-density
character. -/
theorem deningerHalfDensityMateGain_eq_norm_inv_sq
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    deningerHalfDensityMateGain n s =
      ‖bilateralHalfDensityCharacter n s‖⁻¹ ^ 2 := by
  rw [deningerHalfDensityMateGain,
    norm_bilateralHalfDensityCharacter hn]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hnR, ← Real.exp_neg,
    ← Real.exp_nat_mul]
  congr 1
  ring

/-- Mate gain is a multiplicative character of positive power degrees. -/
theorem deningerHalfDensityMateGain_mul
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (s : ℂ) :
    deningerHalfDensityMateGain (m * n) s =
      deningerHalfDensityMateGain m s *
        deningerHalfDensityMateGain n s := by
  rw [deningerHalfDensityMateGain, deningerHalfDensityMateGain,
    deningerHalfDensityMateGain, Nat.cast_mul,
    Real.log_mul (by positivity : (m : ℝ) ≠ 0)
      (by positivity : (n : ℝ) ≠ 0), ← Real.exp_add]
  congr 1
  ring

/-- Gain minus inverse gain is exactly Deninger tensor-square mate
curvature. -/
theorem deningerHalfDensityMateGain_sub_inv_eq_mateCurvature
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    deningerHalfDensityMateGain n s -
        (deningerHalfDensityMateGain n s)⁻¹ =
      deningerTensorSquareRadialMateCurvature n s := by
  rw [deningerHalfDensityMateGain,
    deningerTensorSquareRadialMateCurvature_eq_sinh n s hn,
    Real.sinh_eq, ← Real.exp_neg]
  ring

/-- Source/dual polarization of the two reduced framed curvatures is exactly
the Deninger mate curvature. -/
theorem deningerOneSidedReducedCurvature_dual_sub_source
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    deningerOneSidedReducedCurvature
          (fun k => (deningerHalfDensityMateGain k s)⁻¹) n -
        deningerOneSidedReducedCurvature
          (fun k => deningerHalfDensityMateGain k s) n =
      deningerTensorSquareRadialMateCurvature n s := by
  rw [deningerOneSidedReducedCurvature,
    deningerOneSidedReducedCurvature]
  rw [← deningerHalfDensityMateGain_sub_inv_eq_mateCurvature hn s]
  ring

/-- The first nontrivial left frame already detects nonflatness: for every
degree `n ≥ 2`, the one-sided framed curvature at `(2,n)` vanishes exactly on
the critical half-density section. -/
theorem deningerOneSidedFramedCurvature_two_eq_zero_iff
    {n : ℕ} (hn : 2 ≤ n) (s : ℂ) :
    deningerFramedCompositionCurvature
        (fun k => deningerOneSidedFramedTransport
          (fun d => deningerHalfDensityMateGain d s) k) 2 n = 0 ↔
      s.re = 1 / 2 := by
  have hmul :
      deningerHalfDensityMateGain (2 * n) s =
        deningerHalfDensityMateGain 2 s *
          deningerHalfDensityMateGain n s :=
    deningerHalfDensityMateGain_mul (by omega) (by omega) s
  rw [deningerOneSidedFramedCurvature_eq
    (fun d => deningerHalfDensityMateGain d s) 2 n hmul]
  constructor
  · intro h
    have hentry := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    simp at hentry
    norm_num at hentry
    have hg2 : deningerHalfDensityMateGain 2 s ≠ 0 :=
      (deningerHalfDensityMateGain_pos 2 s).ne'
    have hgn : deningerHalfDensityMateGain n s = 1 := by
      rcases hentry with hzero | hzero
      · exact False.elim (hg2 hzero)
      · linarith
    rw [deningerHalfDensityMateGain] at hgn
    have hexp := (Real.exp_eq_one_iff _).mp hgn
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by
        exact_mod_cast (lt_of_lt_of_le one_lt_two hn))
    rcases mul_eq_zero.mp hexp with hre | hnlog
    · linarith
    · exact False.elim (ne_of_gt hlog hnlog)
  · intro hre
    have hgain (k : ℕ) : deningerHalfDensityMateGain k s = 1 := by
      simp [deningerHalfDensityMateGain, hre]
    rw [hgain 2, hgain n]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num

/-! ## Actual Gamma realization -/

/-- **Actual Gamma boundary is the framed curvature polarization.**  At the
forced composite degree six, the ordered `(2,3)` Gamma/Calderon--Witt
boundary coefficient is the existing positive calibration times the
source/dual reduced one-sided curvature difference. -/
theorem
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_framedCurvaturePolarization
    (r : XiZeroCopy) :
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient r =
      ((deningerCalderonWittBaseGammaMateCalibration *
        (deningerOneSidedReducedCurvature
              (fun k => (deningerHalfDensityMateGain k (r.1 : ℂ))⁻¹) 6 -
          deningerOneSidedReducedCurvature
              (fun k => deningerHalfDensityMateGain k (r.1 : ℂ)) 6) : ℝ) : ℂ) := by
  rw [
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_tensorSquareMateCurvature,
    deningerOneSidedReducedCurvature_dual_sub_source
      (n := 6) (by omega) (r.1 : ℂ)]

end

end RHTower
