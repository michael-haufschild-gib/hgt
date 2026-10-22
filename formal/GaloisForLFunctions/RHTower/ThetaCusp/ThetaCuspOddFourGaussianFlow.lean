import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspPairRadialRecurrence
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Literal first-atom affine flow and the shifted odd-four Gaussian reserve

The first theta atom has an exact reflected affine-Gaussian normal form.  Its
derivative flow is triangular: the affine profile couples only to itself and
the Gaussian profile.  This makes the fourteenth-jet tail accessible without
introducing a surrogate source.  The positive Gaussian odd-four head below is
the limiting reserve; it does not assert positivity of the finite-center theta
head or of the signed integrated rank-eight successor.
-/

namespace RHTower.ThetaCuspOddFour
noncomputable section
open Polynomial Matrix

def gaussian (q t : ℝ) : ℝ :=
  Real.exp (-2*q*(Real.cosh (2*t)-1))

def factor (q B t : ℝ) : ℝ :=
  B-12*q*(Real.cosh (2*t)-1)

def affine (q B t : ℝ) : ℝ :=
  gaussian q t*factor q B t

/-- Exact source identity, with the actual first theta atom and its scale. -/
theorem firstAtomPair_eq_affine (x t : ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    thetaCuspSourceTerm (x+t) 1 * thetaCuspSourceTerm (x-t) 1 =
      4*q^(2 : ℕ)*Real.exp (x-2*q)*affine q ((2*q-3)^(2 : ℕ)) t := by
  dsimp only
  set q := thetaCuspSingleAtomReflectionScale 1 x
  have hcosh : q*Real.exp (2*t)+q*Real.exp (-2*t) =
      2*q*Real.cosh (2*t) := by
    rw [Real.cosh_eq]
    ring
  have hexp : Real.exp (-(q*Real.exp (2*t)+q*Real.exp (-2*t))) =
      Real.exp (-2*q)*Real.exp (-2*q*(Real.cosh (2*t)-1)) := by
    rw [← Real.exp_add, hcosh]
    congr 1
    ring
  have hp := congrFun (thetaCuspAtomPair_eq_radialProfile 1 1 x) t
  rw [hp]
  simp only [thetaPairRadialProfile, thetaPairRadialEvenPolynomial,
    eval_sub, eval_mul, eval_C, eval_X]
  change 4*(q*q)*Real.exp x*
      (Real.exp (-(q*Real.exp (2*t)+q*Real.exp (-2*t))) *
        (4*(q*q)+9-6*(q*Real.exp (2*t)+q*Real.exp (-2*t)))) = _
  rw [hexp, hcosh,
    show Real.exp (x-2*q) = Real.exp x*Real.exp (-2*q) by
      rw [← Real.exp_add]
      congr 1
      ring]
  dsimp only [affine, gaussian, factor]
  ring

theorem gaussian_hasDerivAt (q t : ℝ) :
    HasDerivAt (gaussian q)
      (-4*q*Real.sinh (2*t)*gaussian q t) t := by
  have hc := (Real.hasDerivAt_cosh (2*t)).comp t ((hasDerivAt_id t).const_mul 2)
  have he := ((hc.sub_const 1).const_mul (-2*q)).exp
  have he' : HasDerivAt (gaussian q)
      (Real.exp (-2*q*(Real.cosh (2*t)-1)) *
        (-2*q*(Real.sinh (2*t)*2))) t := by
    change HasDerivAt (fun x => Real.exp (-2*q*(Real.cosh (2*x)-1))) _ t
    simpa [Function.comp_def] using he
  exact he'.congr_deriv (by simp only [gaussian]; ring)

/-- The exact triangular differential flow of the literal first-atom profile. -/
theorem affine_hasDerivAt (q B t : ℝ) :
    HasDerivAt (affine q B)
      (-4*q*Real.sinh (2*t)*(affine q B t+6*gaussian q t)) t := by
  have hc := (Real.hasDerivAt_cosh (2*t)).comp t ((hasDerivAt_id t).const_mul 2)
  have hH' := (hc.sub_const 1).const_mul (-12*q) |>.const_add B
  have hH : HasDerivAt (factor q B)
      (-12*q*(Real.sinh (2*t)*2)) t := by
    change HasDerivAt (fun x => B-12*q*(Real.cosh (2*x)-1)) _ t
    simpa [Function.comp_def, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hH'
  have hG := gaussian_hasDerivAt q t
  have hP := hG.mul hH
  change HasDerivAt (affine q B) _ t at hP
  exact hP.congr_deriv (by simp only [affine, factor]; ring)

/-- All affine first-atom jets obey a source-faithful finite convolution law. -/
theorem affine_jet_succ (q B : ℝ) (n : ℕ) :
    iteratedDeriv (n+1) (affine q B) 0 =
      -4*q * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        iteratedDeriv i (fun t : ℝ => Real.sinh (2*t)) 0 *
          iteratedDeriv (n-i)
            (fun t : ℝ => affine q B t+6*gaussian q t) 0 := by
  have hfun : deriv (affine q B) = fun t =>
      -4*q*Real.sinh (2*t)*(affine q B t+6*gaussian q t) :=
    funext fun t => (affine_hasDerivAt q B t).deriv
  have hs : ContDiffAt ℝ n (fun t : ℝ => Real.sinh (2*t)) 0 := by fun_prop
  have hp : ContDiffAt ℝ n
      (fun t : ℝ => affine q B t+6*gaussian q t) 0 := by
    dsimp [affine, factor, gaussian]
    fun_prop
  rw [iteratedDeriv_succ', hfun]
  conv_lhs =>
    arg 2
    ext t
    rw [show -4*q*Real.sinh (2*t)*
        (affine q B t+6*gaussian q t) =
        (-4*q)*(Real.sinh (2*t)*
          (affine q B t+6*gaussian q t)) by ring]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_mul hs hp]

/-- Exact shifted Gaussian head for odd reflection moments through order fourteen. -/
def gaussianOddFour : Matrix (Fin 4) (Fin 4) ℝ :=
  !![8, 192, 7680, 430080;
     192, 7680, 430080, 30965760;
     7680, 430080, 30965760, 2724986880;
     430080, 30965760, 2724986880, 283398635520]

/-- Cholesky identity exposing the exact fourth-coordinate Schur reserve. -/
theorem gaussianOddFour_square (v : Fin 4 → ℝ) :
    star v ⬝ᵥ gaussianOddFour.mulVec v =
      8*(v 0+24*v 1+960*v 2+53760*v 3)^(2 : ℕ) +
      3072*(v 1+80*v 2+6720*v 3)^(2 : ℕ) +
      3932160*(v 2+168*v 3)^(2 : ℕ) +
      10569646080*(v 3)^(2 : ℕ) := by
  simp [gaussianOddFour, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring

theorem gaussianOddFour_posDef : gaussianOddFour.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gaussianOddFour]
  · intro v hv
    rw [gaussianOddFour_square]
    have h0 := sq_nonneg (v 0+24*v 1+960*v 2+53760*v 3)
    have h1 := sq_nonneg (v 1+80*v 2+6720*v 3)
    have h2 := sq_nonneg (v 2+168*v 3)
    have h3 := sq_nonneg (v 3)
    by_contra h
    have hv3 : v 3 = 0 := by nlinarith
    have hv2 : v 2 = 0 := by nlinarith
    have hv1 : v 1 = 0 := by nlinarith
    have hv0 : v 0 = 0 := by nlinarith
    apply hv
    funext i
    fin_cases i <;> simp [hv0, hv1, hv2, hv3]

/-- Sharp conditional fourth-coordinate floor of the Gaussian odd-four head. -/
theorem gaussianOddFour_successor_floor (v : Fin 3 → ℝ) :
    (10569646080 : ℝ) ≤
      let w : Fin 4 → ℝ := ![v 0, v 1, v 2, 1]
      star w ⬝ᵥ gaussianOddFour.mulVec w := by
  dsimp only
  rw [gaussianOddFour_square]
  simp only [show (2 : Fin 4) = Fin.succ (1 : Fin 3) from rfl,
    show (3 : Fin 4) = Fin.succ (2 : Fin 3) from rfl,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  simp only [show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl,
    show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  simp only [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  nlinarith [sq_nonneg (v 0+24*v 1+960*v 2+53760),
    sq_nonneg (v 1+80*v 2+6720), sq_nonneg (v 2+168)]

theorem gaussianOddFour_successor_floor_attained :
    star (![-53760, 6720, -168, (1 : ℝ)] : Fin 4 → ℝ) ⬝ᵥ
      gaussianOddFour.mulVec ![-53760, 6720, -168, (1 : ℝ)] =
        (10569646080 : ℝ) := by
  rw [gaussianOddFour_square]
  simp only [show (2 : Fin 4) = Fin.succ (1 : Fin 3) from rfl,
    show (3 : Fin 4) = Fin.succ (2 : Fin 3) from rfl,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  simp only [show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl,
    show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  simp only [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

end
end RHTower.ThetaCuspOddFour
