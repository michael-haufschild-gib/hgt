import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.LineClosure

/-! # The discrete shell boundary of physical error and trace readings -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology ContinuousLinearMap

def errorReadings : Set (ℝ × ℝ) :=
  Set.range fun G : Propagator => (‖criticalOperator-G.val‖,traceLoss G.val)

/-- Stability survives passage to limits of the two measurements. -/
theorem closure_fourth_bound (z : {z : ℝ × ℝ // z ∈ closure errorReadings}) : z.val.1^4 ≤ z.val.2 := by
  have hc : IsClosed {x : ℝ × ℝ | x.1^4 ≤ x.2} := isClosed_le (continuous_fst.pow 4) continuous_snd
  have hs : closure errorReadings ⊆ {x : ℝ × ℝ | x.1^4 ≤ x.2} := by
    apply hc.closure_subset_iff.mpr
    rintro _ ⟨G,rfl⟩
    exact (trace_stability G).2.2
  exact hs z.property

/-- Passing to a continuous scalar observable preserves joint limits with the measured trace. -/
theorem observable_closure {X I : Type*} [TopologicalSpace X] (F : I → X) (L : I → ℝ)
    (m : X → ℝ) (hm : Continuous m) (p : X × ℝ)
    (hp : p ∈ closure (Set.range fun i => (F i,L i))) :
    (m p.1,p.2) ∈ closure (Set.range fun i => (m (F i),L i)) := by
  let f (x : X × ℝ) := (m x.1,x.2)
  have h : Set.MapsTo f (Set.range fun i => (F i,L i)) (Set.range fun i => (m (F i),L i)) := by
    rintro _ ⟨i,rfl⟩
    exact ⟨i,rfl⟩
  exact h.closure ((hm.comp continuous_fst).prodMk continuous_snd) hp

private theorem continuous_distance {X : Type*} [NormedAddCommGroup X] (a : X) :
    Continuous (fun x : X => ‖a-x‖) := (continuous_const.sub continuous_id).norm

theorem line_error_mem_closure (v : Gas) :
    (‖criticalOperator-projected (omitLine v)‖,lineLoss v) ∈ closure errorReadings :=
  observable_closure (fun G : Propagator => G.val) (fun G => traceLoss G.val)
    (fun A : GasOp => ‖criticalOperator-A‖) (continuous_distance criticalOperator)
    (projected (omitLine v),lineLoss v) (line_reading_mem_closure v)

private def shell (n : ℕ+) : Gas := lp.single 2 n (1:ℂ)

private theorem shell_norm (n : ℕ+) : ‖shell n‖ = 1 := by simp [shell,lp.norm_single]

private theorem critical_shell (n : ℕ+) :
    criticalOperator (shell n) = (attenuation n : ℂ) • shell n := by
  apply lp.ext
  funext j
  rw [critical_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  by_cases h : j = n
  · rw [h]
  · simp only [shell,lp.single_apply,Pi.single_eq_of_ne h,mul_zero]

private theorem critical_shell_norm (n : ℕ+) : ‖criticalOperator (shell n)‖ = attenuation n := by
  rw [critical_shell,norm_smul,Complex.norm_real,Real.norm_of_nonneg (attenuation_pos n).le,shell_norm,mul_one]

private theorem shell_loss (n : ℕ+) : lineLoss (shell n) = attenuation n^4 := by
  have h : ‖squareHeat.val (shell n)‖ = attenuation n^2 := by
    change ‖criticalOperator (criticalOperator (shell n))‖ = _
    rw [critical_shell,map_smul,norm_smul,Complex.norm_real,Real.norm_of_nonneg (attenuation_pos n).le,
      critical_shell_norm,pow_two]
  rw [lineLoss,h,critical_shell_norm,shell_norm]
  ring

private theorem shell_error_lower (n : ℕ+) :
    attenuation n ≤ ‖criticalOperator-projected (omitLine (shell n))‖ := by
  let P := omitLine (shell n)
  have hz : projected P (shell n) = 0 := by
    apply norm_eq_zero.mp
    rw [projected_norm,critical_shell,map_smul,show P.val (shell n) = 0 from omitLine_kills _,smul_zero,norm_zero]
  have h := (criticalOperator-projected P).le_opNorm (shell n)
  rwa [sub_apply,hz,sub_zero,critical_shell_norm,shell_norm,mul_one] at h

/-- Each deleted shell is approached by positive conserving propagators in both observables. -/
theorem shell_boundary (n : ℕ+) : (attenuation n,attenuation n^4) ∈ closure errorReadings := by
  have h := line_error_mem_closure (shell n)
  rw [shell_loss] at h
  have hu := closure_fourth_bound ⟨_,h⟩
  have he := le_antisymm
    ((pow_le_pow_iff_left₀ (norm_nonneg _) (attenuation_pos n).le (by decide : 4 ≠ 0)).mp hu)
    (shell_error_lower n)
  rwa [he] at h

#print axioms line_error_mem_closure
#print axioms shell_boundary

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
