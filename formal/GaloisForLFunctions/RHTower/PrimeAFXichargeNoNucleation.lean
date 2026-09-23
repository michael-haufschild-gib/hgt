import GaloisForLFunctions.RHTower.PrimeAFChargeDirectLimit
import GaloisForLFunctions.RHTower.WindingXi
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.PrimeTailReflectionFoldedSecondOrderResolvent
import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv

/-!
# The Xi divisor charge cannot nucleate in a norm-regular AF limit

Hardy's theorem supplies an actual positive critical-line zero. A sufficiently small classical Xi
circle about it is nonvanishing on its boundary and has winding equal to the positive analytic
order. The norm-regular no-nucleation theorem then excludes uniform approximation of this boundary
loop by any sequence of continuous periodic zero-winding loops.
-/

open Complex Metric Set

namespace PrimeQuasiLocalCharge

noncomputable section

/-- Unconditionally, one Xi boundary loop is nonvanishing and has nonzero integer winding. -/
theorem exists_xiBoundaryLoop_nonzero_winding :
    ∃ gamma : ℝ → ℂ,
      Continuous gamma ∧ (∀ t, gamma t ≠ 0) ∧
      Function.Periodic gamma (2 * Real.pi) ∧
      RHTower.windingNumber gamma 0 (2 * Real.pi) ≠ 0 := by
  obtain ⟨a, b, ha, hb, hab, hza, hzb⟩ := RHTower.exists_two_distinct_positive_real_XiC_zeros
  let rho : ℂ := 1 / 2 + (a : ℂ) * Complex.I
  have hxi : RHTower.xi rho = 0 := by
    rw [RHTower.xi_eq_XiC_comp]
    have hcoord : (rho - 1 / 2) * (-Complex.I) = (a : ℂ) := by
      dsimp [rho]
      calc
        (1 / 2 + (a : ℂ) * Complex.I - 1 / 2) * (-Complex.I) =
            -(a : ℂ) * Complex.I ^ (2 : ℕ) := by ring
        _ = (a : ℂ) := by rw [Complex.I_sq]; ring
    rw [hcoord, hza]
  obtain ⟨Rw, hRw, hwind⟩ := RHTower.windingNumber_xi_zero rho
  obtain ⟨Rl, hRl, hloop⟩ := RHTower.xi_circle_isLoop rho
  let r : ℝ := min Rw Rl / 2
  have hr : 0 < r := by positivity
  have hrw : r < Rw := by dsimp [r]; linarith [min_le_left Rw Rl]
  have hrl : r < Rl := by dsimp [r]; linarith [min_le_right Rw Rl]
  let gamma : ℝ → ℂ :=
    fun theta => RHTower.xi (rho + (r : ℂ) * Complex.exp (Complex.I * (theta : ℂ)))
  have hL := hloop r hr hrl
  refine ⟨gamma, hL.continuous, hL.nonzero,
    RHTower.circleLoop_periodic RHTower.xi rho r, ?_⟩
  rw [show RHTower.windingNumber gamma 0 (2 * Real.pi) =
      ((analyticOrderAt RHTower.xi rho).toNat : ℤ) by
    exact hwind r hr hrw]
  exact_mod_cast RHTower.xi_order_toNat_ne_zero hxi

/-- One unconditional Xi boundary loop stays a fixed positive uniform distance from every
continuous periodic zero-winding loop.  Thus a finite zero-free carrier cannot approach the
decisive boundary even along a sparse subsequence. -/
theorem exists_xiBoundaryLoop_zeroWinding_uniformGap :
    ∃ (gamma : ℝ → ℂ) (m : ℝ),
      Continuous gamma ∧ (∀ t, gamma t ≠ 0) ∧
      Function.Periodic gamma (2 * Real.pi) ∧
      RHTower.windingNumber gamma 0 (2 * Real.pi) ≠ 0 ∧
      0 < m ∧
      ∀ delta : ℝ → ℂ,
        Continuous delta →
        Function.Periodic delta (2 * Real.pi) →
        RHTower.windingNumber delta 0 (2 * Real.pi) = 0 →
        ∃ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
          m ≤ ‖delta t - gamma t‖ := by
  obtain ⟨gamma, hcont, hne, hper, hcharge⟩ :=
    exists_xiBoundaryLoop_nonzero_winding
  have hKne : (Set.Icc (0 : ℝ) (2 * Real.pi)).Nonempty :=
    Set.nonempty_Icc.mpr Real.two_pi_pos.le
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    hKne hcont.norm.continuousOn
  let m : ℝ := ‖gamma t₀‖
  have hm : 0 < m := by
    dsimp only [m]
    exact norm_pos_iff.mpr (hne t₀)
  have hlow : ∀ t : ℝ, m ≤ ‖gamma t‖ := by
    intro t
    obtain ⟨y, hy, hval⟩ := hper.exists_mem_Ico₀ Real.two_pi_pos t
    rw [hval]
    exact isMinOn_iff.mp hmin y (Set.Ico_subset_Icc_self hy)
  refine ⟨gamma, m, hcont, hne, hper, hcharge, hm, fun delta hdcont hdper hdzero => ?_⟩
  by_contra hgap
  push Not at hgap
  have hdiffper : Function.Periodic (fun t => delta t - gamma t) (2 * Real.pi) := by
    intro t
    change delta (t + 2 * Real.pi) - gamma (t + 2 * Real.pi) =
      delta t - gamma t
    rw [hdper t, hper t]
  have hclose : ∀ t : ℝ, ‖delta t - gamma t‖ < m := by
    intro t
    obtain ⟨y, hy, hval⟩ := hdiffper.exists_mem_Ico₀ Real.two_pi_pos t
    rw [hval]
    exact hgap y (Set.Ico_subset_Icc_self hy)
  have hgammaLoop : gamma 0 = gamma (2 * Real.pi) := by
    have h := hper 0
    rw [zero_add] at h
    exact h.symm
  have hdeltaLoop : delta 0 = delta (2 * Real.pi) := by
    have h := hdper 0
    rw [zero_add] at h
    exact h.symm
  have hwind := RHTower.windingNumber_eq_of_close
    hcont hdcont hgammaLoop hdeltaLoop hlow hclose
  apply hcharge
  calc
    RHTower.windingNumber gamma 0 (2 * Real.pi) =
        RHTower.windingNumber delta 0 (2 * Real.pi) := hwind.symm
    _ = 0 := hdzero

/-- No sequence of regular zero-winding loops can converge uniformly to every Xi boundary loop:
one unconditional positive-charge Xi circle obstructs such a thermodynamic limit. -/
theorem exists_xiBoundaryLoop_not_uniformLimit_of_zeroWindingLoops :
    ∃ gamma : ℝ → ℂ,
      Continuous gamma ∧ (∀ t, gamma t ≠ 0) ∧
      Function.Periodic gamma (2 * Real.pi) ∧
      RHTower.windingNumber gamma 0 (2 * Real.pi) ≠ 0 ∧
      ∀ delta : ℕ → ℝ → ℂ,
        (∀ n, Continuous (delta n)) →
        (∀ n, Function.Periodic (delta n) (2 * Real.pi)) →
        (∀ n, RHTower.windingNumber (delta n) 0 (2 * Real.pi) = 0) →
        ¬ (∀ ε > 0, ∀ᶠ n in Filter.atTop,
          ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖delta n t - gamma t‖ < ε) := by
  obtain ⟨gamma, hcont, hne, hper, hcharge⟩ := exists_xiBoundaryLoop_nonzero_winding
  refine ⟨gamma, hcont, hne, hper, hcharge, fun delta hdcont hdper hdzero hconv => ?_⟩
  exact hcharge (windingNumber_eq_zero_of_uniform_limit hcont hne hper
    hdcont hdper hdzero hconv)

end

end PrimeQuasiLocalCharge
