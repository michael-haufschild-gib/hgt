import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.SharpRate

/-! # Conditional escape from affordable harmonics at the original physical error -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.HarmonicRuns
noncomputable section
open SharpOccupation

private theorem subcritical_smaller {s S : ℕ → ℕ} (h : ∀ n, s n ≤ S n) (hs : subcriticalBudget S) :
    subcriticalBudget s := by
  unfold subcriticalBudget at *
  apply squeeze_zero (fun _ => by positivity) _ hs
  intro n
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (add_le_add (Nat.cast_le.mpr (h n)) le_rfl) (by positivity)

/-- Given a time t affordable with s gates, the conditional fraction
affordable at every one of its first m multiples is m^(1−D) times a
factor with logarithm o(D), also for growing m and s. -/
theorem gaussian_conditional_affordable_runs :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s m : ℕ → ℕ, (∀ n, 0 < m n) →
      subcriticalBudget (fun n => m n*(s n+1)) → ∀ ε ∈ Ioo (0:ℝ) 1,
      ∀ l b : ℝ, 0 < l → l < physicalArc ε → physicalArc ε < b → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let M := m N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
          let f := volume.real (circuitRunSet H (s N) M ε ∩ Icc a T) /
            volume.real (visitSet H (s N) ε ∩ Icc a T)
          (l/b)^D < (M:ℝ)^(D-1)*f ∧ (M:ℝ)^(D-1)*f < (b/l)^D := by
  filter_upwards [gaussian_sharp_run_rate,gaussian_cheap_occupation_rate] with ω hrun hbase
  intro s m hm hsub ε hε l b hl hlx hxb
  have h2 : (1:ℝ) < Real.sqrt 2 := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    nlinarith only [h,Real.sqrt_nonneg 2]
  obtain ⟨hx,htol⟩ := physicalArc_spec hε.1 (hε.2.trans h2)
  have hthird : zeroGateArcTolerance (1/3) = 1 := by
    rw [zeroGateArcTolerance,show Real.pi*(1/3)/2 = Real.pi/6 by ring,Real.sin_pi_div_six]
    norm_num
  have hlt := (strictMonoOn_zeroGateArcTolerance.lt_iff_lt ⟨hx.1.le,hx.2.le⟩
    (by norm_num : (1/3:ℝ) ∈ Icc (0:ℝ) (1/2))).mp (htol.trans_lt (hε.2.trans_eq hthird.symm))
  have hs := subcritical_smaller (fun n => (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (hm n))) hsub
  have hj := hrun s m hm hsub _ ⟨hx.1,hlt⟩ l b hl.le hlx hxb
  have hv := hbase s hs _ hx l b hl.le hlx hxb
  rw [htol] at hj hv
  filter_upwards [hj,hv] with k hj hv
  intro N D M H a
  filter_upwards [hj a,hv a,eventually_gt_atTop a] with T hj hv hT
  have hv' := hv (s N) le_rfl
  let f := volume.real (circuitRunSet H (s N) M ε ∩ Icc a T)/(T-a)
  let g := volume.real (visitSet H (s N) ε ∩ Icc a T)/(T-a)
  let v := (M:ℝ)^(D-1)
  have hp : 0 < v := pow_pos (Nat.cast_pos.mpr (hm N)) _
  have hL : (l:ℝ)^D < f*v := (div_lt_iff₀ hp).mp hj.1
  have hU : f*v < b^D := (lt_div_iff₀ hp).mp hj.2
  have hlg : l^D < g := hv'.1
  have hgb : g < b^D := hv'.2
  have hlp := pow_pos hl D
  have hbp := pow_pos ((hl.trans hlx).trans hxb) D
  have hg := hlp.trans hlg
  have eqf : v*(volume.real (circuitRunSet H (s N) M ε ∩ Icc a T)/
      volume.real (visitSet H (s N) ε ∩ Icc a T)) = f*v/g := by
    rw [mul_comm f,mul_div_assoc]
    congr 1
    exact (div_div_div_cancel_right₀ (sub_pos.mpr hT).ne' _ _).symm
  change (l/b)^D < v*_ ∧ v*_ < (b/l)^D
  rw [eqf,div_pow,div_pow]
  exact ⟨(div_le_div_of_nonneg_left hlp.le hg hgb.le).trans_lt ((div_lt_div_iff_of_pos_right hg).mpr hL),
    ((div_lt_div_iff_of_pos_right hg).mpr hU).trans_le (div_le_div_of_nonneg_left hbp.le hlp hlg.le)⟩

#print axioms gaussian_conditional_affordable_runs
end
end GaloisForLFunctions.HTGeometry.HarmonicRuns
