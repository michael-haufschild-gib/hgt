import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant
import GaloisForLFunctions.RHTower.PsiDefectSqrtBound
import GaloisForLFunctions.RHTower.ChebyshevPsiScaling

/-!
# Vanishing first Mellin mass of the critical Möbius--divisor source

The stepwise Chebyshev defect `ψ(n) - n + 2γ` has zero mass against the
exact floor-cell Mellin weight `1/(n(n+1))`. This is the source-specific
cancellation of the first large-prime sampling coefficient in the terminal
square-root-core transform. It does not control the logarithmically weighted
higher Mellin moments or the terminal energy.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private theorem criticalMellinMass_psi_succ (N : ℕ) :
    chebyshevPsi (N + 1) =
      chebyshevPsi N + ArithmeticFunction.vonMangoldt (N + 1) := by
  unfold chebyshevPsi
  rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- Exact finite Mertens--harmonic decomposition of the step-source Mellin
mass. It retains the endpoint `ψ(N)/(N+1)` and the floor correction. -/
theorem mobiusDivisorCriticalMellinMassPrefix_eq (N : ℕ) :
    (∑ n ∈ Icc 1 N,
      psiDefect n / ((n : ℝ) * ((n : ℝ) + 1))) =
      (∑ k ∈ Icc 0 N,
        ArithmeticFunction.vonMangoldt k / (k : ℝ)) -
        (harmonic N : ℝ) -
        chebyshevPsi N / ((N : ℝ) + 1) +
        1 - 1 / ((N : ℝ) + 1) +
        2 * Real.eulerMascheroniConstant *
          (N : ℝ) / ((N : ℝ) + 1) := by
  induction N with
  | zero =>
      simp [psiDefect, chebyshevPsi, harmonic]
  | succ N ih =>
      rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      rw [sum_Icc_succ_top (by omega : 0 ≤ N + 1)]
      rw [ih, criticalMellinMass_psi_succ, harmonic_succ]
      simp only [psiDefect]
      rw [criticalMellinMass_psi_succ]
      push_cast
      have hn1 : ((N : ℝ) + 1) ≠ 0 := by positivity
      have hn2 : ((N : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      ring

/-- The complete critical step source has zero first Mellin mass:
`∑_{n≥1} (ψ(n)-n+2γ)/(n(n+1)) = 0`, understood as its finite-prefix limit.
This is unconditional and uses the actual Mertens constant, not a generic
prime-number-theorem estimate. -/
theorem tendsto_mobiusDivisorCriticalMellinMass_zero :
    Tendsto (fun N : ℕ =>
      ∑ n ∈ Icc 1 N,
        psiDefect n / ((n : ℝ) * ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hV : Tendsto (fun N : ℕ =>
      (∑ k ∈ Icc 0 N, ArithmeticFunction.vonMangoldt k / (k : ℝ)) -
        Real.log N) atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
    simpa only [Function.comp_def, Nat.floor_natCast] using
      tendsto_real_sum_vonMangoldt_div_sub_log.comp hnat
  have hH : Tendsto (fun N : ℕ =>
      (harmonic N : ℝ) - Real.log N) atTop
      (𝓝 Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log
  have hψ : Tendsto (fun N : ℕ => chebyshevPsi N / (N : ℝ))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, chebyshevPsiReal, Nat.floor_natCast] using
      tendsto_chebyshevPsiReal_div.comp hnat
  have hInv : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, one_div] using
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1) :
          Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop)
  have hratio : Tendsto (fun N : ℕ => (N : ℝ) / ((N : ℝ) + 1))
      atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hInv
    simpa only [sub_zero] using h.congr' (Eventually.of_forall fun N => by
      have hne : ((N : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring)
  have hψsucc : Tendsto (fun N : ℕ =>
      chebyshevPsi N / ((N : ℝ) + 1)) atTop (𝓝 1) := by
    have h := hψ.mul hratio
    simpa only [one_mul] using h.congr'
      (by
        filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
        have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
        have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
        field_simp)
  have h := (((hV.sub hH).sub hψsucc).add
      (tendsto_const_nhds (x := (1 : ℝ)))).sub hInv
  have h' := h.add (hratio.const_mul (2 * Real.eulerMascheroniConstant))
  convert h' using 1
  · ext N
    rw [mobiusDivisorCriticalMellinMassPrefix_eq]
    ring
  · ring

end RHTower
