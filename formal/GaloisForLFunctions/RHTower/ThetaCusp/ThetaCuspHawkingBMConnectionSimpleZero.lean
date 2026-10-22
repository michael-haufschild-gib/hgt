import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceFrequencyContinuation
import GaloisForLFunctions.HTGeometry.ReciprocalGammaPoleBranch

/-! The original connection normalization has a derived simple zero at each fundamental Gamma zero. -/
open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def connectionZeroArgument (w chi : ℂ) (side : Bool) : ℂ :=
  if side then gaussC w-gaussB w chi else gaussC w-gaussA w chi

def connectionOtherArgument (w chi : ℂ) (side : Bool) : ℂ :=
  if side then gaussC w-gaussA w chi else gaussC w-gaussB w chi

def connectionSimpleSlope (w chi : ℂ) (side : Bool) : ℂ :=
  Gamma (gaussC w)*Gamma (1/2:ℂ)/(2*Gamma (connectionOtherArgument w chi side))

theorem connection_argument_sum (w chi : ℂ) (side : Bool) :
    connectionZeroArgument w chi side+connectionOtherArgument w chi side = 3/2+w := by
  cases side <;> simp only [connectionZeroArgument,connectionOtherArgument,Bool.false_eq_true,↓reduceIte]
  all_goals unfold gaussA gaussB gaussC; ring

theorem connection_selected_factorization (w chi : ℂ) (side : Bool) :
    connection w chi = Gamma (gaussC w)*Gamma (1/2:ℂ)*
      (Gamma (connectionOtherArgument w chi side))⁻¹*(Gamma (connectionZeroArgument w chi side))⁻¹ := by
  cases side <;> simp only [connectionZeroArgument,connectionOtherArgument,Bool.false_eq_true,↓reduceIte,
    connection,div_eq_mul_inv,mul_inv_rev] <;> ring

theorem connectionZeroArgument_hasDerivAt (w chi : ℂ) (side : Bool) :
    HasDerivAt (fun v => connectionZeroArgument v chi side) (1/2:ℂ) w := by
  have hC : HasDerivAt gaussC 1 w := (hasDerivAt_id w).const_add 1
  have hA : HasDerivAt (fun v => gaussA v chi) (1/2:ℂ) w :=
    (((hasDerivAt_id w).div_const 2).const_add (1/4:ℂ)).add_const (I*chi/2)
  have hB : HasDerivAt (fun v => gaussB v chi) (1/2:ℂ) w :=
    (((hasDerivAt_id w).div_const 2).const_add (1/4:ℂ)).sub_const (I*chi/2)
  cases side
  · exact (hC.sub hA).congr_deriv (by ring)
  · exact (hC.sub hB).congr_deriv (by ring)

private theorem gamma_nonzero_nonreal (z : ℂ) (hz : z.im ≠ 0) : Gamma z ≠ 0 := by
  apply Gamma_ne_zero
  intro n he
  apply hz
  rw [he]
  simp

/-- The true connection slope is nonzero; the surviving Gamma factor cannot vanish at a nonreal fundamental root. -/
theorem connectionSimpleSlope_ne_zero (w chi : ℂ) (side : Bool) (hw : w.im ≠ 0)
    (hz : connectionZeroArgument w chi side = 0) : connectionSimpleSlope w chi side ≠ 0 := by
  have ho := connection_argument_sum w chi side
  rw [hz,zero_add] at ho
  exact div_ne_zero (mul_ne_zero (gamma_nonzero_nonreal _ (by simpa [gaussC] using hw))
    (Gamma_ne_zero_of_re_pos (by norm_num))) (mul_ne_zero (by norm_num)
      (gamma_nonzero_nonreal _ (by rw [ho]; simpa using hw)))

/-- Differentiation of the original reciprocal-Gamma factors gives the exact fundamental connection slope. -/
theorem connection_fundamental_hasDerivAt (w chi : ℂ) (side : Bool) (hw : w.im ≠ 0)
    (hz : connectionZeroArgument w chi side = 0) :
    HasDerivAt (fun v => connection v chi) (connectionSimpleSlope w chi side) w := by
  let A (v : ℂ) := Gamma (gaussC v)*Gamma (1/2:ℂ)*(Gamma (connectionOtherArgument v chi side))⁻¹
  have hgc : ∀ n : ℕ, gaussC w ≠ -(n:ℂ) := by
    intro n he
    apply hw
    have hi := congrArg Complex.im he
    simpa [gaussC] using hi
  have hG := (_root_.HTGeometry.analyticAt_Gamma_off_poles hgc).comp
    (show AnalyticAt ℂ gaussC w by unfold gaussC; fun_prop)
  have hO : AnalyticAt ℂ (fun v => connectionOtherArgument v chi side) w := by
    cases side <;> simp only [connectionOtherArgument,Bool.false_eq_true,↓reduceIte]
    all_goals dsimp only [gaussA,gaussB,gaussC]; fun_prop
  have hA : AnalyticAt ℂ A w := (hG.mul analyticAt_const).mul
    ((Complex.differentiable_one_div_Gamma.analyticAt _).comp hO)
  have hZ : HasDerivAt (fun z : ℂ => (Gamma z)⁻¹) 1 (connectionZeroArgument w chi side) := by
    rw [hz]
    simpa using GaloisForLFunctions.hasDerivAt_oneDivGamma_neg_nat 0
  have hI : HasDerivAt (fun v => (Gamma (connectionZeroArgument v chi side))⁻¹) (1/2:ℂ) w := by
    simpa only [Function.comp_def,one_mul] using hZ.comp w (connectionZeroArgument_hasDerivAt w chi side)
  have hprod := hA.differentiableAt.hasDerivAt.mul hI
  change HasDerivAt (fun v => A v*(Gamma (connectionZeroArgument v chi side))⁻¹)
    (deriv A w*(Gamma (connectionZeroArgument w chi side))⁻¹+A w*(1/2)) w at hprod
  have he : (fun v => A v*(Gamma (connectionZeroArgument v chi side))⁻¹) = (fun v => connection v chi) := by
    funext v
    exact (connection_selected_factorization v chi side).symm
  rw [he] at hprod
  apply hprod.congr_deriv
  rw [hz,Gamma_zero,inv_zero,mul_zero,zero_add]
  dsimp [A,connectionSimpleSlope]
  ring

end
end RHTower.D4BMLaplaceRadial
