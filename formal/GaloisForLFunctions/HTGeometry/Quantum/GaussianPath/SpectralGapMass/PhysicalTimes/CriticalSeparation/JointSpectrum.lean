import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.JointDates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.PhysicalLimit

/-! # Joint eigenphase laws at inverse-square-root time separations -/
open MeasureTheory Filter Finset Set Matrix Real
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section

private theorem amplitude_eq_shell (ω : PathPauliDisorder) (n : ℕ) (t : ℝ) :
    amplitude ω n t=Bulk.shellTrace (pathPauliDisorderShell ω n) t := by
  simp only [amplitude,Bulk.shellTrace,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,
    Nat.cast_pow,Nat.cast_ofNat,div_eq_inv_mul]

private theorem amplitude_norm_abs (ω : PathPauliDisorder) (n : ℕ) (t : ℝ) :
    ‖amplitude ω n |t|‖=‖amplitude ω n t‖ := by
  rcases le_total 0 t with h|h
  · rw [abs_of_nonneg h]
  rw [abs_of_nonpos h]
  let H : selfAdjoint (Register (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
  change ‖(unitaryEvolution H.val (-t)).trace/(2:ℂ)^(n+2)‖=‖(unitaryEvolution H.val t).trace/(2:ℂ)^(n+2)‖
  rw [EigenlineSignals.adjoint_evolution,Matrix.star_eq_conjTranspose,Matrix.trace_conjTranspose]
  simp only [norm_div,norm_star]

private theorem gaussian_shifted_trace :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a b : ℝ,
      Tendsto (fun n : ℕ => amplitude ω n (a+b/sqrt (n+2:ℕ))) atTop
        (𝓝 (if a=0 then (exp (-6*b^2):ℂ) else 0)) := by
  filter_upwards [Bulk.gaussian_scaled_characteristic,gaussian_trace_along_dates] with ω hsmall hlarge
  intro a b
  by_cases ha : a=0
  · subst a
    simpa only [zero_add,if_pos rfl,amplitude_eq_shell] using hsmall b
  rw [if_neg ha]
  let t (n : ℕ) := a+b/sqrt (n+2:ℕ)
  have hN := tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp (tendsto_add_atTop_nat 2)
  have ht : Tendsto t atTop (𝓝 a) := by
    simpa only [add_zero] using (tendsto_const_nhds (x:=a)).add ((tendsto_sqrt_atTop.comp hN).const_div_atTop b)
  have hpos := abs_pos.mpr ha
  have hb : ∀ᶠ n in atTop, |t n|∈Icc (|a|/2) (|a|+1) :=
    (ht.abs.eventually_const_lt (half_lt_self hpos)).and (ht.abs.eventually_lt_const (lt_add_one _))
      |>.mono fun _ h => ⟨h.1.le,h.2.le⟩
  have hh := (hlarge _ _ (half_pos hpos) (fun n => |t n|) hb).norm
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def,amplitude_norm_abs,norm_zero] using hh

/-- For physical dates a+b/√N observed on the same eigenline, only
integer relations among a survive. Each surviving character is damped
by the Gaussian in its corresponding projection of b. These coefficients
determine the joint probability measure uniquely. -/
theorem gaussian_critical_joint_spectrum :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (d : ℕ) (a b : Fin d→ℝ),
      ∃! μ : ProbabilityMeasure (UnitAddTorus (Fin d)),
        Tendsto (fun n : ℕ => jointLaw (pathPauliDisorderShell ω n)
          (fun i => a i+b i/sqrt (n+2:ℕ))) atTop (𝓝 μ) ∧
        ∀ h : Fin d→ℤ, (∫ z, UnitAddTorus.mFourier h z ∂(μ : Measure (UnitAddTorus (Fin d)))) =
          if finiteTorusCharacterDetuning h a=0 then
            (exp (-6*(finiteTorusCharacterDetuning h b)^2):ℂ) else 0 := by
  filter_upwards [gaussian_shifted_trace] with ω hw
  intro d a b
  apply existsUnique_probabilityMeasure_tendsto_of_mFourier_limit
  intro h
  have hdet (v : ℝ) : finiteTorusCharacterDetuning h (fun i => a i+b i/v) =
      finiteTorusCharacterDetuning h a+finiteTorusCharacterDetuning h b/v := by
    simp only [finiteTorusCharacterDetuning,mul_add,mul_div_assoc',sum_add_distrib,sum_div]
  simpa only [joint_moment,hdet] using hw (finiteTorusCharacterDetuning h a) (finiteTorusCharacterDetuning h b)

#print axioms gaussian_critical_joint_spectrum
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
