import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspPacketProfile

/-!
Exact differential residual and orthogonal cutoff costs for actual cusp packets.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
noncomputable section

private def packetWindow (j : ℕ) (L t : ℝ) : ℂ :=
  cuspWindowDerivative j (cuspPacketCoordinate L t)

private theorem packetWindow_hasDerivAt (j : ℕ) (L t : ℝ) :
    HasDerivAt (packetWindow j L) ((L:ℂ)⁻¹*packetWindow (j+1) L t) t := by
  have hd := (((cuspWindowDerivative_smooth j).differentiable (by simp))
    (cuspPacketCoordinate L t)).hasDerivAt.comp t
    ((hasDerivAt_id t).sub_const (cuspPacketCenter L) |>.div_const L)
  have he := hd.ofReal_comp
  have hs : deriv (cuspWindowDerivative j) = cuspWindowDerivative (j+1) := by
    simp only [cuspWindowDerivative,Function.iterate_succ_apply']
  rw [hs] at he
  change HasDerivAt (packetWindow j L) _ t at he
  convert he using 1
  simp only [packetWindow,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one]
  ring

private theorem cuspPacketPhase_hasDerivAt (tau t : ℝ) :
    HasDerivAt (cuspPacketPhase tau) ((tau:ℂ)*Complex.I*cuspPacketPhase tau t) t := by
  have he := (((hasDerivAt_id t).ofReal_comp).const_mul ((tau:ℂ)*Complex.I)).cexp
  change HasDerivAt (cuspPacketPhase tau) _ t at he
  convert he using 1
  simp only [cuspPacketPhase,id_eq,Complex.ofReal_one,mul_one]
  ring

private theorem cuspPacketField_hasDerivAt (tau L t : ℝ) :
    HasDerivAt (cuspPacketField tau L) (cuspPacketPhase tau t*
      ((tau:ℂ)*Complex.I*packetWindow 0 L t+(L:ℂ)⁻¹*packetWindow 1 L t)) t := by
  have he := (cuspPacketPhase_hasDerivAt tau t).mul (packetWindow_hasDerivAt 0 L t)
  change HasDerivAt (cuspPacketField tau L) _ t at he
  convert he using 1
  change _ = ((tau:ℂ)*Complex.I*cuspPacketPhase tau t)*packetWindow 0 L t+
    cuspPacketPhase tau t*((L:ℂ)⁻¹*packetWindow 1 L t)
  ring

private theorem cuspPacketField_deriv (tau L : ℝ) :
    deriv (cuspPacketField tau L) = fun t => cuspPacketPhase tau t*
      ((tau:ℂ)*Complex.I*packetWindow 0 L t+(L:ℂ)⁻¹*packetWindow 1 L t) := by
  funext t
  exact (cuspPacketField_hasDerivAt tau L t).deriv

/-- The full packet residual retains both differentiated cutoff terms.
Its oscillatory principal term cancels at the original cusp threshold. -/
theorem cuspPacketField_residual (tau L t : ℝ) :
    (5/4-((5/4:ℂ)+(tau:ℂ)^(2 : ℕ)))*cuspPacketField tau L t-
      deriv (deriv (cuspPacketField tau L)) t =
      -cuspPacketPhase tau t*(2*(tau:ℂ)*Complex.I/(L:ℂ)*
        ((deriv cuspWindow (cuspPacketCoordinate L t):ℝ):ℂ)+
          (L:ℂ)⁻¹^(2 : ℕ)*((deriv (deriv cuspWindow) (cuspPacketCoordinate L t):ℝ):ℂ)) := by
  have hp := (cuspPacketPhase_hasDerivAt tau t).mul
    (((packetWindow_hasDerivAt 0 L t).const_mul ((tau:ℂ)*Complex.I)).add
      ((packetWindow_hasDerivAt 1 L t).const_mul (L:ℂ)⁻¹))
  have he := hp.deriv
  change deriv (fun r => cuspPacketPhase tau r*((tau:ℂ)*Complex.I*packetWindow 0 L r+
    (L:ℂ)⁻¹*packetWindow 1 L r)) t = _ at he
  rw [cuspPacketField_deriv,he]
  simp only [Pi.add_apply,packetWindow,cuspWindowDerivative,
    Function.iterate_succ_apply',Function.iterate_zero,Function.id_def,cuspPacketField]
  linear_combination -(tau:ℂ)^(2 : ℕ)*cuspPacketPhase tau t*
    (cuspWindow (cuspPacketCoordinate L t):ℂ)*Complex.I_sq

/-- Reality of the original cutoff derivatives makes the two residual terms
orthogonal in the complex plane, giving an exact squared norm. -/
theorem cuspPacketField_residual_norm_sq (tau L t : ℝ) :
    ‖(5/4-((5/4:ℂ)+(tau:ℂ)^(2 : ℕ)))*cuspPacketField tau L t-
      deriv (deriv (cuspPacketField tau L)) t‖^(2 : ℕ) =
      4*tau^(2 : ℕ)/L^(2 : ℕ)*(deriv cuspWindow (cuspPacketCoordinate L t))^(2 : ℕ)+
        L⁻¹^(4 : ℕ)*(deriv (deriv cuspWindow) (cuspPacketCoordinate L t))^(2 : ℕ) := by
  rw [cuspPacketField_residual,norm_mul,norm_neg,cuspPacketPhase_norm,one_mul,
    ← Complex.normSq_eq_norm_sq]
  have he : 2*(tau:ℂ)*Complex.I/(L:ℂ)*
      ((deriv cuspWindow (cuspPacketCoordinate L t):ℝ):ℂ)+
        (L:ℂ)⁻¹^(2 : ℕ)*((deriv (deriv cuspWindow) (cuspPacketCoordinate L t):ℝ):ℂ) =
      ((L⁻¹^(2 : ℕ)*deriv (deriv cuspWindow) (cuspPacketCoordinate L t):ℝ):ℂ)+
      ((2*tau/L*deriv cuspWindow (cuspPacketCoordinate L t):ℝ):ℂ)*Complex.I := by
    push_cast
    ring
  rw [he,Complex.normSq_add_mul_I]
  ring

end
end RHTower.D4BMModularCore
