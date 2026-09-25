import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant
import GaloisForLFunctions.RHTower.PsiDefectSqrtBound
import GaloisForLFunctions.RHTower.ChebyshevPsiScaling

open Finset Filter Topology
namespace RHTower

#check tendsto_real_sum_vonMangoldt_div_sub_log
#check Real.tendsto_harmonic_sub_log
#check tendsto_chebyshevPsiReal_div
#check sum_Icc_succ_top
#check harmonic
#check chebyshevPsiReal_eq_sum_range

private theorem psi_succ (N : ℕ) :
    chebyshevPsi (N + 1) =
      chebyshevPsi N + ArithmeticFunction.vonMangoldt (N + 1) := by
  unfold chebyshevPsi
  rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

theorem criticalMellinMassPrefix_eq (N : ℕ) :
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
      rw [ih, psi_succ, harmonic_succ]
      simp only [psiDefect]
      rw [psi_succ]
      push_cast
      have hn1 : ((N : ℝ) + 1) ≠ 0 := by positivity
      have hn2 : ((N : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      ring

theorem tendsto_criticalMellinMassPrefix_zero :
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
    rw [criticalMellinMassPrefix_eq]
    ring
  · ring

end RHTower
