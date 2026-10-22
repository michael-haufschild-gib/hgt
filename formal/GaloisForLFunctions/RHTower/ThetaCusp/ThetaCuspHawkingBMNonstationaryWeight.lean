import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalMomentCounterterm
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue

/-! Rational weights for the actual opposite-rate source's nonstationary Mellin phase. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
open scoped Polynomial
noncomputable section
set_option autoImplicit false

def nonstationaryWeight (P : ℂ[X]) (j : ℕ) (x : ℝ) : ℂ :=
  P.eval (x:ℂ)/(2-(x:ℂ))^(8 : ℕ)/(2+3*(x:ℂ))^j

def nonstationaryWeightFirst (P : ℂ[X]) (j : ℕ) (x : ℝ) : ℂ :=
  P.derivative.eval (x:ℂ)/(2-(x:ℂ))^(8 : ℕ)/(2+3*(x:ℂ))^j+
    8*P.eval (x:ℂ)/(2-(x:ℂ))^(9 : ℕ)/(2+3*(x:ℂ))^j-
    (j:ℂ)*3*P.eval (x:ℂ)/(2-(x:ℂ))^(8 : ℕ)/(2+3*(x:ℂ))^(j+1)

def nonstationaryWeightStep (P : ℂ[X]) (j : ℕ) : ℂ[X] :=
  Polynomial.X*((2-Polynomial.X)*(2+3*Polynomial.X)*P.derivative+
    (12*Polynomial.X-3*(j:ℂ[X])*(2-Polynomial.X))*P)

private theorem nonstationary_bases {x : ℝ} (hx : x ∈ Ioo (-(1/2):ℝ) 2) :
    (2-(x:ℂ)) ≠ 0 ∧ (2+3*(x:ℂ)) ≠ 0 := by
  constructor
  · have h : (2-x:ℝ) ≠ 0 := by linarith [hx.2]
    exact_mod_cast h
  · have h : (2+3*x:ℝ) ≠ 0 := by linarith [hx.1]
    exact_mod_cast h

theorem nonstationaryWeight_hasDerivAt (P : ℂ[X]) (j : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (-(1/2):ℝ) 2) :
    HasDerivAt (nonstationaryWeight P j) (nonstationaryWeightFirst P j x) x := by
  have hb := nonstationary_bases hx
  have h2 : HasDerivAt (fun z : ℂ => 2-z) (-1) (x:ℂ) := by
    simpa only [zero_sub,Pi.sub_apply,id_eq] using! (hasDerivAt_const (x:ℂ) (2:ℂ)).sub (hasDerivAt_id (x:ℂ))
  have h3 : HasDerivAt (fun z : ℂ => 2+3*z) 3 (x:ℂ) := by
    simpa only [zero_add,mul_one,Pi.add_apply,id_eq] using!
      (hasDerivAt_const (x:ℂ) (2:ℂ)).add ((hasDerivAt_id (x:ℂ)).const_mul 3)
  have h := (((P.hasDerivAt (x:ℂ)).div (h2.pow 8) (pow_ne_zero 8 hb.1)).div
    (h3.pow j) (pow_ne_zero j hb.2)).comp_ofReal
  apply h.congr_deriv
  dsimp only [nonstationaryWeightFirst]
  simp only [Pi.pow_apply,Pi.div_apply]
  cases j with
  | zero => simp only [Nat.cast_zero,zero_mul,mul_zero,pow_zero,div_one,sub_zero]; field_simp [hb.1,hb.2]; ring
  | succ j =>
    simp only [Nat.add_sub_cancel,pow_succ,Nat.cast_add,Nat.cast_one]
    field_simp [hb.1,hb.2,pow_ne_zero j hb.2]
    ring

theorem nonstationaryWeightFirst_continuousAt (P : ℂ[X]) (j : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (-(1/2):ℝ) 2) : ContinuousAt (nonstationaryWeightFirst P j) x := by
  have hb := nonstationary_bases hx
  have hR : ContinuousAt (fun y : ℝ => (y:ℂ)) x := Complex.continuous_ofReal.continuousAt
  have hP := (P.hasDerivAt (x:ℂ)).comp_ofReal.continuousAt
  have hPd := (P.derivative.hasDerivAt (x:ℂ)).comp_ofReal.continuousAt
  have h2 : ContinuousAt (fun y : ℝ => 2-(y:ℂ)) x := continuousAt_const.sub hR
  have h3 : ContinuousAt (fun y : ℝ => 2+3*(y:ℂ)) x := continuousAt_const.add (hR.const_mul 3)
  exact (((hPd.div (h2.pow 8) (pow_ne_zero 8 hb.1)).div (h3.pow j) (pow_ne_zero j hb.2)).add
    (((hP.const_mul 8).div (h2.pow 9) (pow_ne_zero 9 hb.1)).div (h3.pow j) (pow_ne_zero j hb.2))).sub
      (((hP.const_mul ((j:ℂ)*3)).div (h2.pow 8) (pow_ne_zero 8 hb.1)).div
        (h3.pow (j+1)) (pow_ne_zero (j+1) hb.2))

/-- One integration-by-parts step preserves a rational weight and forces a lower-endpoint zero. -/
theorem nonstationaryWeight_step (P : ℂ[X]) (j : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (-(1/2):ℝ) 2) :
    nonstationaryWeight (nonstationaryWeightStep P j) (j+2) x =
      (x:ℂ)*((2-(x:ℂ))/(2+3*(x:ℂ))*nonstationaryWeightFirst P j x-
        4*(4+3*(x:ℂ))/(2+3*(x:ℂ))^(2 : ℕ)*nonstationaryWeight P j x) := by
  have hb := nonstationary_bases hx
  simp only [nonstationaryWeight,nonstationaryWeightStep,nonstationaryWeightFirst,
    Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat,
    Polynomial.eval_natCast]
  simp only [pow_add,pow_one,div_eq_mul_inv,mul_inv_rev]
  have hB : (2+(x:ℂ)*3) ≠ 0 := by simpa only [mul_comm] using hb.2
  field_simp [hb.1,hb.2,hB,pow_ne_zero j hb.2,pow_ne_zero j hB]
  ring

theorem nonstationaryWeightStep_zero (P : ℂ[X]) (j : ℕ) :
    (nonstationaryWeightStep P j).eval 0 = 0 := by
  simp [nonstationaryWeightStep]

/-- The next rational weight gains a full power at the original singular endpoint. -/
theorem nonstationaryWeight_step_bound (P : ℂ[X]) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioc (0:ℝ) 1,
      ‖nonstationaryWeight (nonstationaryWeightStep P j) (j+2) x‖ ≤ C*x := by
  let Q : ℂ[X] := (2-Polynomial.X)*(2+3*Polynomial.X)*P.derivative+
    (12*Polynomial.X-3*(j:ℂ[X])*(2-Polynomial.X))*P
  have hf (x : ℝ) : nonstationaryWeight (nonstationaryWeightStep P j) (j+2) x =
      (x:ℂ)*nonstationaryWeight Q (j+2) x := by
    simp only [nonstationaryWeight,nonstationaryWeightStep,Polynomial.eval_mul,Polynomial.eval_X]
    dsimp only [Q]
    ring
  have hc : ContinuousOn (nonstationaryWeight Q (j+2)) (Icc (0:ℝ) 1) := by
    intro x hx
    exact (nonstationaryWeight_hasDerivAt Q (j+2)
      (by constructor <;> linarith [hx.1,hx.2])).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x hx
  rw [hf,norm_mul,Complex.norm_of_nonneg hx.1.le]
  exact (mul_le_mul_of_nonneg_left ((hC x ⟨hx.1.le,hx.2⟩).trans (le_max_left C 0)) hx.1.le).trans_eq (mul_comm _ _)

end
end RHTower.D4BMJointSource
