import GaloisForLFunctions.RHTower.Sieve.HalaszMontgomeryIntegral
import GaloisForLFunctions.RHTower.Sieve.LogPhaseKernelBound

/-!
# The row and column masses of the logarithmic-phase kernel

The kernel of the integral Halász–Montgomery bound is `plainKernel N v = ∑_{n < N} exp(iv log(n+1))`,
which is the Dirichlet sum `∑_{m ≤ N} m^{-it}` at `t = −v`.  Brick 12's pointwise bound therefore
applies, and the near/far split of `Sieve/KernelDoubleIntegral` turns it into the mass bound the
Schur test consumes.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

theorem log_complex_ofReal_pos {x : ℝ} (hx : 0 < x) :
    Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := by
  rw [Complex.log, Complex.arg_ofReal_of_nonneg hx.le, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hx]
  simp

theorem cpow_eq_phase {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    ((m : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))
      = Complex.exp (((-t * Real.log m : ℝ) : ℂ) * Complex.I) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hne : ((m : ℕ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  rw [Complex.cpow_def_of_ne_zero hne]
  congr 1
  rw [show ((m : ℕ) : ℂ) = ((m : ℝ) : ℂ) by push_cast; ring, log_complex_ofReal_pos hm0]
  push_cast
  ring

/-- **The kernel is a Dirichlet sum.** -/
theorem plainKernel_eq_dirichlet (N : ℕ) (v : ℝ) :
    plainKernel N v
      = ∑ m ∈ Finset.Icc 1 N, ((m : ℕ) : ℂ) ^ (-(Complex.I * ((-v : ℝ) : ℂ))) := by
  classical
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext m; simp
  rw [hIcc, Finset.sum_Ico_eq_sum_range, plainKernel,
    Fin.sum_univ_eq_sum_range
      (fun i => Complex.exp (((v * Real.log ((i : ℕ) + 1) : ℝ) : ℂ) * Complex.I)) N]
  have hlen : N + 1 - 1 = N := by omega
  rw [hlen]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cpow_eq_phase (by omega : 1 ≤ 1 + i)]
  congr 2
  push_cast
  ring

theorem norm_plainKernel_neg (N : ℕ) (v : ℝ) :
    ‖plainKernel N (-v)‖ = ‖plainKernel N v‖ := by
  have hconj : plainKernel N (-v) = (starRingEnd ℂ) (plainKernel N v) := by
    rw [plainKernel, plainKernel, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [hconj, RCLike.norm_conj]

/-- **The pointwise bound for the kernel.** -/
theorem norm_plainKernel_le {N : ℕ} (hN : 1 ≤ N) {v : ℝ} (hv : v ≠ 0) :
    ‖plainKernel N v‖
      ≤ ((Nat.log 2 N : ℝ) + 1) * (214 * Real.sqrt |v|) + 3072 * (N : ℝ) / Real.sqrt |v| := by
  have hkey : ∀ w : ℝ, w < 0 → ‖plainKernel N w‖
      ≤ ((Nat.log 2 N : ℝ) + 1) * (214 * Real.sqrt |w|) + 3072 * (N : ℝ) / Real.sqrt |w| := by
    intro w hw
    have hpos : (0 : ℝ) < -w := by linarith
    have hbase := norm_sum_Icc_logPhase_le (M := N) hN (t := -w) hpos
    have habs : |w| = -w := abs_of_neg hw
    rw [habs]
    refine le_trans (le_of_eq ?_) hbase
    rw [plainKernel_eq_dirichlet]
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · exact hkey v hneg
  · have h1 := hkey (-v) (by linarith)
    rw [norm_plainKernel_neg, abs_neg] at h1
    exact h1

/-- **The row mass of the kernel over a bounded set.** -/
theorem plainKernel_row_mass {N : ℕ} (hN : 1 ≤ N) {T : ℝ} {E : Set ℝ}
    (hEs : E ⊆ Set.Icc (-T) T) (hEm : MeasurableSet E) {t : ℝ}
    (ht : t ∈ Set.Icc (-T) T) :
    (∫ u in E, ‖plainKernel N (t - u)‖)
      ≤ 2 * (N : ℝ)
        + (((Nat.log 2 N : ℝ) + 1) * (214 * Real.sqrt (2 * T)) + 3072 * (N : ℝ))
          * (volume.real E) := by
  have hCnn : (0 : ℝ) ≤ ((Nat.log 2 N : ℝ) + 1) * (214 * Real.sqrt (2 * T)) + 3072 * (N : ℝ) := by
    have : (0 : ℝ) ≤ Real.sqrt (2 * T) := Real.sqrt_nonneg _
    positivity
  refine setIntegral_norm_kernel_le (K := plainKernel N) (N := (N : ℝ))
    (continuous_plainKernel N) hEs hEm ?_ ?_ hCnn
  · -- the trivial bound
    intro v
    rw [plainKernel]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n : Fin N,
        ‖Complex.exp (((v * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      intro n
      rw [Complex.norm_exp]
      simp
    rw [Finset.sum_congr rfl fun n _ => hterm n, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  · -- the oscillation bound, only for `u ∈ E`
    intro u hu hfar
    have hne : t - u ≠ 0 := by
      intro h
      rw [h, abs_zero] at hfar
      linarith
    refine le_trans (norm_plainKernel_le hN hne) ?_
    have huE : u ∈ Set.Icc (-T) T := hEs hu
    rw [Set.mem_Icc] at ht huE
    have habs : |t - u| ≤ 2 * T := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2, huE.1, huE.2]
    have hsq : Real.sqrt |t - u| ≤ Real.sqrt (2 * T) := Real.sqrt_le_sqrt habs
    have hone : (1 : ℝ) ≤ Real.sqrt |t - u| := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hfar
    have hsq0 : (0 : ℝ) < Real.sqrt |t - u| := by linarith
    have hlog0 : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) + 1 := by positivity
    have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    have hfrac : 3072 * (N : ℝ) / Real.sqrt |t - u| ≤ 3072 * (N : ℝ) := by
      rw [div_le_iff₀ hsq0]
      nlinarith [hone, hNR]
    have hmain : ((Nat.log 2 N : ℝ) + 1) * (214 * Real.sqrt |t - u|)
        ≤ ((Nat.log 2 N : ℝ) + 1) * (214 * Real.sqrt (2 * T)) := by
      refine mul_le_mul_of_nonneg_left ?_ hlog0
      linarith [hsq]
    linarith [hmain, hfrac]

/-- **The column mass**, by the kernel's reflection symmetry. -/
theorem plainKernel_col_mass {N : ℕ} (hN : 1 ≤ N) {T : ℝ} {E : Set ℝ}
    (hEs : E ⊆ Set.Icc (-T) T) (hEm : MeasurableSet E) {u : ℝ} (hu : u ∈ Set.Icc (-T) T) :
    (∫ t in E, ‖plainKernel N (t - u)‖)
      ≤ 2 * (N : ℝ)
        + (((Nat.log 2 N : ℝ) + 1) * (214 * Real.sqrt (2 * T)) + 3072 * (N : ℝ))
          * (volume.real E) := by
  have hsym : ∀ t : ℝ, ‖plainKernel N (t - u)‖ = ‖plainKernel N (u - t)‖ := by
    intro t
    rw [show u - t = -(t - u) by ring, norm_plainKernel_neg]
  rw [MeasureTheory.setIntegral_congr_fun hEm fun t _ => hsym t]
  exact plainKernel_row_mass hN hEs hEm hu

/-- **Lemma 2.6 with every constant named.**  The mean square of a Dirichlet polynomial of length
`N` over a measurable `E ⊆ [−T, T]`. -/
theorem setIntegral_normSq_dirPoly_le_explicit {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ) {T : ℝ}
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-T) T) :
    (∫ t in E, ‖dirPoly N a t‖ ^ 2)
      ≤ (2 * (N : ℝ)
          + (((Nat.log 2 N : ℝ) + 1) * (214 * Real.sqrt (2 * T)) + 3072 * (N : ℝ))
            * (volume.real E)) * ∑ n : Fin N, ‖a n‖ ^ 2 := by
  have hvol : (0 : ℝ) ≤ volume.real E := ENNReal.toReal_nonneg
  have hsqT : (0 : ℝ) ≤ Real.sqrt (2 * T) := Real.sqrt_nonneg _
  have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hlog0 : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) := Nat.cast_nonneg _
    linarith
  have hC0 : (0 : ℝ) ≤ ((Nat.log 2 N : ℝ) + 1) * (214 * Real.sqrt (2 * T)) + 3072 * (N : ℝ) := by
    nlinarith [hlog0, hsqT, hNR]
  have hM0 : (0 : ℝ) ≤ 2 * (N : ℝ)
      + (((Nat.log 2 N : ℝ) + 1) * (214 * Real.sqrt (2 * T)) + 3072 * (N : ℝ))
        * (volume.real E) := by nlinarith [hC0, hvol, hNR]
  exact setIntegral_normSq_dirPoly_le_HM a hEm hEs
    (fun t ht => plainKernel_row_mass hN hEs hEm (hEs ht))
    (fun u hu => plainKernel_col_mass hN hEs hEm (hEs hu)) hM0

end RHTower.Sieve
