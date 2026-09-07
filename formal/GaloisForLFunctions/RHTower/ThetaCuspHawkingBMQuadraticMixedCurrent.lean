import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuadraticMixedSource
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularScalarEquation
import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVectorStreamEinstein
namespace RHTower.D4BMQuadraticMixedSource
open GaloisForLFunctions.HTGeometry D4BMScalarLinearEquation
noncomputable section

/-- Exact scalar--vector current, for either of the two coexact angular components. -/
def current (s r B J K : ℂ) : ℂ :=
  B^2*((5*s^2+15*s+4)/4+s*(s-1)*(s+2)^2/(4*r^2))*J -
    B^2*s*(s-1)/(4*r^2)*K

/-- Its radial derivative, with the fundamental envelope's radial rate retained. -/
def currentFirst (s r B J K : ℂ) : ℂ :=
  2*s/(r*(r^2-1))*current s r B J K -
    B^2*s*(s-1)*(s+2)^2/(2*r^3)*J+B^2*s*(s-1)/(2*r^3)*K

/-- Full product jet of the current, using the actual envelope jet. -/
def currentJet (s r B J K : ℂ) : ScalarTwoJet (Fin 4) ℂ :=
  let R := coord r 1
  (temporalRadial (2*s) r (B^2)).mul
    ((ScalarTwoJet.constant ((5*s^2+15*s+4)/4*J)).add
      ((R.inv.mul R.inv).mul
        (ScalarTwoJet.constant (s*(s-1)*(s+2)^2/4*J-s*(s-1)/4*K))))

/-- Both time and radial derivatives of the displayed current are the product-jet derivatives. -/
theorem currentJet_components (s r B J K : ℂ) (hr : r ≠ 0) (hf : r^2-1 ≠ 0) :
    (currentJet s r B J K).value = current s r B J K ∧
    (currentJet s r B J K).first 0 = 2*s*current s r B J K ∧
    (currentJet s r B J K).first 1 = currentFirst s r B J K := by
  simp only [currentJet, ScalarTwoJet.mul, ScalarTwoJet.add, ScalarTwoJet.inv,
    ScalarTwoJet.constant, temporalRadial, coord, current, currentFirst]
  simp
  constructor
  · field_simp [hr, hf]
    ring
  constructor <;> field_simp [hr, hf] <;> ring

/-- The source's radial component is the current's time derivative. -/
theorem radial_current (s r B J K : ℂ) (hr : r ≠ 0) (hf : r^2-1 ≠ 0) :
    r^2*(r^2-1)*(B^2*(radialSquare s r*J+radialGradient s r*K)) =
    2*s*current s r B J K := by
  dsimp [radialSquare, radialGradient, current]
  field_simp [hr, hf]
  ring

/-- The temporal component is the current's complete radial derivative. -/
theorem temporal_current (s r B J K : ℂ) (hr : r ≠ 0) (hf : r^2-1 ≠ 0) :
    r^2/(r^2-1)*(B^2*(timeSquare s r*J+timeGradient s r*K)) =
      currentFirst s r B J K := by
  dsimp [timeSquare, timeGradient, currentFirst, current]
  field_simp [hr, hf]
  ring

/-- The square of the actual scalar jet fixes its coexact Laplacian; no eigen-equation
for the squared scalar is inserted. -/
theorem square_coexact_laplacian (s y S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) (hy : y ≠ 0) :
    let Syy := (s+1)*(s+2)*S/y^2-Sxx
    let Sxyy := (s+1)*(s+2)*Sx/y^2-Sxxx
    let Syyy := (s+1)*(s+2)*Sy/y^2-2*(s+1)*(s+2)*S/y^3-Sxxy
    (y^2*((Sxx*Sy+2*Sx*Sxy+S*Sxxy)+(3*Sy*Syy+S*Syyy))+
        2*y*((Sy^2+S*Syy)-(-Sx^2-S*Sxx)),
      y^2*((-3*Sx*Sxx-S*Sxxx)-(2*Sy*Sxy+Sx*Syy+S*Sxyy))) =
    (2*(s+1)*(s+2)*(squareCovector S Sx Sy).1+
        2*(gradientCovector s y S Sx Sy Sxx Sxy).1,
      2*(s+1)*(s+2)*(squareCovector S Sx Sy).2+
        2*(gradientCovector s y S Sx Sy Sxx Sxy).2) := by
  dsimp [squareCovector, gradientCovector]
  apply Prod.ext <;> dsimp <;> field_simp [hy] <;> ring

/-- The two radial factors reduce the complete source current to one specific angular
resolvent defect. The defect is retained; this theorem does not assume an inverse exists. -/
theorem master_resolvent_defect (s r B J K A D : ℂ) (hr : r ≠ 0) (hf : r^2-1 ≠ 0) :
    D4BMVectorStream.master (2*s) r (B^2) (B^2*(2*s)/(r*(r^2-1)))
      (B^2*((2*s)^2-(2*s)*(3*r^2-1))/(r^2*(r^2-1)^2)) A D -
    (s*(s-1)/4)*D4BMVectorStream.master (2*s) r (B^2/r^2)
      (B^2*(-2/r^3+(2*s)/(r^3*(r^2-1))))
      (B^2*(6/r^4-4*(2*s)/(r^4*(r^2-1))+
        ((2*s)^2-(2*s)*(3*r^2-1))/(r^4*(r^2-1)^2))) J
      (2*(s+1)*(s+2)*J+2*K) - 2*current s r B J K =
    B^2*(D-(2*s+1)*(2*s+2)*A-2*(s+1)*(2*s+1)*J) := by
  rw [D4BMVectorStream.master_constant_factor _ _ _ _ _ hr hf,
    D4BMVectorStream.master_inverse_square_factor _ _ _ _ _ hr hf]
  dsimp [current]
  field_simp [hr]
  ring

/-- The angular parameter of the actual doubled fundamental time rate. -/
def resolventParameter (s : ℂ) : ℂ := (2*s+1)*(2*s+2)

/-- Both physical branches retain their damping shift in the angular parameter. -/
theorem physical_parameter_im (rho : ℂ) :
    (resolventParameter (rho-2)).im = (8*rho.re-10)*rho.im ∧
    (resolventParameter (-rho-1)).im = (8*rho.re+2)*rho.im := by
  constructor <;> norm_num [resolventParameter, Complex.mul_re, Complex.mul_im] <;> ring

/-- At every actual Xi occurrence, both shifted angular parameters are nonreal.
This requires no critical-line or tilted-fibre assumption. -/
theorem xi_resolvent_parameter_nonreal (q : XiZeroCopy) :
    (resolventParameter ((q.1 : ℂ)-2)).im ≠ 0 ∧
    (resolventParameter (-(q.1 : ℂ)-1)).im ≠ 0 := by
  have hs := xi_divisor_support_re_mem_open_unit q.1
  have hi := xi_divisor_support_im_ne_zero q.1
  rw [(physical_parameter_im (q.1 : ℂ)).1, (physical_parameter_im (q.1 : ℂ)).2]
  constructor
  · exact mul_ne_zero (by intro h; linarith [hs.2]) hi
  · exact mul_ne_zero (by intro h; linarith [hs.1]) hi

open D4BMAngularSeries
open scoped Topology ContDiff

/-- Exact response to one cusp power, retaining its actual resolvent denominator. -/
def powerResponse (lambda p A : ℂ) (z : Fin 2 → ℝ) : ℂ :=
  A/(p*(p-1)-lambda)*(z 1 : ℂ)^p

private theorem power_smooth (p : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ 2 (fun w : Fin 2 → ℝ => (w 1 : ℂ)^p) z :=
  (height_cpow_contDiffOn p 2).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)

private theorem powerResponse_smooth (lambda p A : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ 2 (powerResponse lambda p A) z :=
  contDiffAt_const.mul (power_smooth p z hz)

/-- The displayed power response solves the actual differential equation. -/
theorem power_response_equation (lambda p A : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1)
    (hd : p*(p-1)-lambda ≠ 0) :
    hyperbolicLaplacian (powerResponse lambda p A) z - lambda*powerResponse lambda p A z =
      A*(z 1 : ℂ)^p := by
  unfold powerResponse
  rw [hyperbolicLaplacian_const_mul (power_smooth p z hz),
    height_cpow_hyperbolicLaplacian p z hz]
  field_simp [hd]

/-- The three power terms in the square of both retained Weyl cusp terms. -/
def cuspPowerResponse (lambda rho A D : ℂ) (z : Fin 2 → ℝ) : ℂ :=
  powerResponse lambda (2*rho) (A^2) z + powerResponse lambda 1 (2*A*D) z +
    powerResponse lambda (2-2*rho) (D^2) z

/-- The three displayed powers are exactly the full square, including its cross term. -/
theorem cusp_power_square (rho A D : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    A^2*(z 1 : ℂ)^(2*rho)+(2*A*D)*(z 1 : ℂ)^(1:ℂ)+
      D^2*(z 1 : ℂ)^(2-2*rho) =
      (A*(z 1 : ℂ)^rho+D*(z 1 : ℂ)^(1-rho))^2 := by
  have hn : (z 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hp : ((z 1 : ℂ)^rho)^2 = (z 1 : ℂ)^(2*rho) := by
    rw [pow_two, ← Complex.cpow_add _ _ hn]
    congr 1
    ring
  have hm : ((z 1 : ℂ)^(1-rho))^2 = (z 1 : ℂ)^(2-2*rho) := by
    rw [pow_two, ← Complex.cpow_add _ _ hn]
    congr 1
    ring
  have hc : (z 1 : ℂ)^rho*(z 1 : ℂ)^(1-rho) = (z 1 : ℂ)^(1:ℂ) := by
    rw [← Complex.cpow_add _ _ hn]
    congr 1
    ring
  rw [← hp, ← hm, ← hc]
  ring

/-- The complete retained cusp power square has an explicit differential response. -/
theorem cusp_response_equation (lambda rho A D : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1)
    (h0 : (2*rho)*(2*rho-1)-lambda ≠ 0) (h1 : -lambda ≠ 0)
    (h2 : (2-2*rho)*(1-2*rho)-lambda ≠ 0) :
    hyperbolicLaplacian (cuspPowerResponse lambda rho A D) z -
      lambda*cuspPowerResponse lambda rho A D z =
      (A*(z 1 : ℂ)^rho+D*(z 1 : ℂ)^(1-rho))^2 := by
  have h0s := powerResponse_smooth lambda (2*rho) (A^2) z hz
  have h1s := powerResponse_smooth lambda 1 (2*A*D) z hz
  have h2s := powerResponse_smooth lambda (2-2*rho) (D^2) z hz
  have e0 := power_response_equation lambda (2*rho) (A^2) z hz h0
  have e1 := power_response_equation lambda 1 (2*A*D) z hz (by simpa using h1)
  have e2 := power_response_equation lambda (2-2*rho) (D^2) z hz (by convert h2 using 1; ring)
  unfold cuspPowerResponse
  rw [hyperbolicLaplacian_add (h0s.add h1s) h2s, hyperbolicLaplacian_add h0s h1s,
    ← cusp_power_square rho A D z hz]
  linear_combination e0+e1+e2

/-- Physical minus and plus branches in the actual Xi coordinate. -/
def branchParameter (rho : ℂ) (minusBranch : Bool) : ℂ :=
  if minusBranch then resolventParameter (rho-2) else resolventParameter (-rho-1)

/-- No power in the full squared cusp principal part is resonant at either physical Xi branch. -/
theorem xi_cusp_denominators (q : XiZeroCopy) (minusBranch : Bool) :
    (2*(q.1 : ℂ))*(2*(q.1 : ℂ)-1)-branchParameter (q.1 : ℂ) minusBranch ≠ 0 ∧
    -branchParameter (q.1 : ℂ) minusBranch ≠ 0 ∧
    (2-2*(q.1 : ℂ))*(1-2*(q.1 : ℂ))-branchParameter (q.1 : ℂ) minusBranch ≠ 0 := by
  have hi := xi_divisor_support_im_ne_zero q.1
  have hparam : (branchParameter (q.1 : ℂ) minusBranch).im ≠ 0 := by
    cases minusBranch
    · exact (xi_resolvent_parameter_nonreal q).2
    · exact (xi_resolvent_parameter_nonreal q).1
  have hm : -branchParameter (q.1 : ℂ) minusBranch ≠ 0 := by
    apply neg_ne_zero.mpr
    intro h
    apply hparam
    rw [h]
    rfl
  refine ⟨?_, hm, ?_⟩ <;> intro h <;> apply hi
  all_goals have hc := congrArg Complex.im h
  all_goals cases minusBranch <;>
    norm_num [branchParameter, resolventParameter, Complex.mul_re, Complex.mul_im] at hc <;>
    nlinarith

/-- At every actual Xi occurrence and on both physical branches, the full squared cusp
principal part has this explicit response to the actual hyperbolic differential operator. -/
theorem xi_cusp_response_equation (q : XiZeroCopy) (minusBranch : Bool) (A D : ℂ)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    hyperbolicLaplacian (cuspPowerResponse (branchParameter (q.1 : ℂ) minusBranch)
      (q.1 : ℂ) A D) z - branchParameter (q.1 : ℂ) minusBranch *
      cuspPowerResponse (branchParameter (q.1 : ℂ) minusBranch) (q.1 : ℂ) A D z =
    (A*(z 1 : ℂ)^(q.1 : ℂ)+D*(z 1 : ℂ)^(1-(q.1 : ℂ)))^2 := by
  obtain ⟨h0, h1, h2⟩ := xi_cusp_denominators q minusBranch
  exact cusp_response_equation _ _ _ _ _ hz h0 h1 h2

/-- The same actual cusp response retains any fixed forcing amplitude, in particular
(s+1)(2s+1) from the derived mixed Einstein source. -/
theorem xi_forced_cusp_response_equation (q : XiZeroCopy) (minusBranch : Bool) (C A D : ℂ)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    hyperbolicLaplacian (fun w => C*cuspPowerResponse (branchParameter (q.1 : ℂ) minusBranch)
      (q.1 : ℂ) A D w) z - branchParameter (q.1 : ℂ) minusBranch *
      (C*cuspPowerResponse (branchParameter (q.1 : ℂ) minusBranch) (q.1 : ℂ) A D z) =
    C*(A*(z 1 : ℂ)^(q.1 : ℂ)+D*(z 1 : ℂ)^(1-(q.1 : ℂ)))^2 := by
  have hp := ((powerResponse_smooth (branchParameter (q.1 : ℂ) minusBranch)
    (2*(q.1 : ℂ)) (A^2) z hz).add
    (powerResponse_smooth (branchParameter (q.1 : ℂ) minusBranch) 1 (2*A*D) z hz)).add
    (powerResponse_smooth (branchParameter (q.1 : ℂ) minusBranch) (2-2*(q.1 : ℂ)) (D^2) z hz)
  change ContDiffAt ℝ 2 (cuspPowerResponse (branchParameter (q.1 : ℂ) minusBranch) (q.1 : ℂ) A D) z at hp
  rw [hyperbolicLaplacian_const_mul hp C]
  have he := xi_cusp_response_equation q minusBranch A D z hz
  linear_combination C*he

end
end RHTower.D4BMQuadraticMixedSource
