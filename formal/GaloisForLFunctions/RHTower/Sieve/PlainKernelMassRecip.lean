import GaloisForLFunctions.RHTower.Sieve.PlainKernelRecip
import GaloisForLFunctions.RHTower.Sieve.KernelRowMassRecip
import GaloisForLFunctions.RHTower.Sieve.HalaszMontgomeryIntegral

/-!
# Halász–Montgomery with the reciprocal kernel mass

`Sieve/PlainKernelMass.setIntegral_normSq_dirPoly_le_explicit` pays the far bound uniformly, and its
`3072·N·|E|` term makes the estimate vacuous for every exceptional set of measure at least a
constant.  With the Kuzmin–Landau decay the `N`-dependent part of the far bound is `12π·N/|v|`,
whose mass over the window is `logarithmic`, so the estimate becomes

```text
   ∫_E ‖A‖²  ≤  ( 2N + 48π·N·log(2 + 2T) + C(T,N)·|E| )·∑ ‖a_n‖² ,
   C(T,N) = 214(log₂⌈2T⌉ + 1)√(2T) + 12288√(2T) + log₂N + 1 ,
```

which is Lemma 2.6's `N log T + |E|√T log T`.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- The trivial size of the kernel. -/
theorem norm_plainKernel_le_card (N : ℕ) (v : ℝ) : ‖plainKernel N v‖ ≤ (N : ℝ) := by
  rw [plainKernel]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n : Fin N,
      ‖Complex.exp (((v * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    intro n
    rw [Complex.norm_exp]
    simp
  rw [Finset.sum_congr rfl fun n _ => hterm n, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The far constant of the kernel over a window of height `T`. -/
def plainKernelFarConst (N : ℕ) (T : ℝ) : ℝ :=
  ((Nat.log 2 ⌈2 * T⌉₊ : ℝ) + 1) * (214 * Real.sqrt (2 * T))
    + 12288 * Real.sqrt (2 * T) + ((Nat.log 2 N : ℝ) + 1)

theorem plainKernelFarConst_nonneg (N : ℕ) {T : ℝ} (_hT : 1 ≤ T) : 0 ≤ plainKernelFarConst N T := by
  have h2T : (0 : ℝ) ≤ 2 * T := by linarith
  have hsq : (0 : ℝ) ≤ Real.sqrt (2 * T) := Real.sqrt_nonneg _
  have h1 : (0 : ℝ) ≤ (Nat.log 2 ⌈2 * T⌉₊ : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) := Nat.cast_nonneg _
  rw [plainKernelFarConst]
  nlinarith [hsq, h1, h2]

/-- **The far bound of the kernel over the window, in `A + B/|v|` form.** -/
theorem norm_plainKernel_le_far {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (_hT : 1 ≤ T) {v : ℝ}
    (hv : 1 ≤ |v|) (hv2 : |v| ≤ 2 * T) :
    ‖plainKernel N v‖ ≤ plainKernelFarConst N T + (12 * Real.pi * (N : ℝ)) / |v| := by
  have hbase := norm_plainKernel_le_recip hN hv
  refine hbase.trans ?_
  have hsq : Real.sqrt |v| ≤ Real.sqrt (2 * T) := Real.sqrt_le_sqrt hv2
  have hsq0 : (0 : ℝ) ≤ Real.sqrt |v| := Real.sqrt_nonneg _
  have hceil : ⌈|v|⌉₊ ≤ ⌈2 * T⌉₊ := Nat.ceil_mono hv2
  have hlog : (Nat.log 2 ⌈|v|⌉₊ : ℝ) ≤ (Nat.log 2 ⌈2 * T⌉₊ : ℝ) := by
    exact_mod_cast Nat.log_mono_right hceil
  have hlog0 : (0 : ℝ) ≤ (Nat.log 2 ⌈|v|⌉₊ : ℝ) := Nat.cast_nonneg _
  have hdiv : 12 * Real.pi * (N : ℝ) / |v| = (12 * Real.pi * (N : ℝ)) / |v| := by ring
  rw [plainKernelFarConst, hdiv]
  nlinarith [hsq, hsq0, hlog, hlog0]

/-- **The row mass of the kernel with reciprocal decay.** -/
theorem plainKernel_row_mass_recip {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 1 ≤ T) {E : Set ℝ}
    (hEs : E ⊆ Set.Icc (-T) T) (hEm : MeasurableSet E) {t : ℝ} (ht : t ∈ Set.Icc (-T) T) :
    (∫ u in E, ‖plainKernel N (t - u)‖)
      ≤ 2 * (N : ℝ) + plainKernelFarConst N T * volume.real E
        + 4 * (12 * Real.pi * (N : ℝ)) * Real.log (2 + 2 * T) := by
  refine setIntegral_norm_kernel_le_recip (continuous_plainKernel N) hEs hEm hT
    (Nat.cast_nonneg N) (plainKernelFarConst_nonneg N hT) (by positivity)
    (fun v => norm_plainKernel_le_card N v)
    (fun v hv hv2 => norm_plainKernel_le_far hN hT hv hv2) ht

/-- **Lemma 2.6 with the Kuzmin–Landau constants.** -/
theorem setIntegral_normSq_dirPoly_le_recip {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ) {T : ℝ}
    (hT : 1 ≤ T) {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-T) T) :
    (∫ t in E, ‖dirPoly N a t‖ ^ 2)
      ≤ (2 * (N : ℝ) + plainKernelFarConst N T * volume.real E
          + 4 * (12 * Real.pi * (N : ℝ)) * Real.log (2 + 2 * T))
        * ∑ n : Fin N, ‖a n‖ ^ 2 := by
  have hM0 : (0 : ℝ) ≤ 2 * (N : ℝ) + plainKernelFarConst N T * volume.real E
      + 4 * (12 * Real.pi * (N : ℝ)) * Real.log (2 + 2 * T) := by
    have h1 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ volume.real E := ENNReal.toReal_nonneg
    have h3 : (0 : ℝ) ≤ plainKernelFarConst N T := plainKernelFarConst_nonneg N hT
    have h4 : (0 : ℝ) ≤ Real.log (2 + 2 * T) := Real.log_nonneg (by linarith)
    have h5 : (0 : ℝ) < Real.pi := Real.pi_pos
    have p1 : (0 : ℝ) ≤ plainKernelFarConst N T * volume.real E := mul_nonneg h3 h2
    have p2 : (0 : ℝ) ≤ 4 * (12 * Real.pi * (N : ℝ)) * Real.log (2 + 2 * T) :=
      mul_nonneg (by positivity) h4
    linarith
  refine setIntegral_normSq_dirPoly_le_HM a hEm hEs ?_ ?_ hM0
  · intro t ht
    exact plainKernel_row_mass_recip hN hT hEs hEm (hEs ht)
  · intro u hu
    have hcol : (∫ t in E, ‖plainKernel N (t - u)‖) = ∫ t in E, ‖plainKernel N (u - t)‖ := by
      refine MeasureTheory.setIntegral_congr_fun hEm fun t _ => ?_
      have hneg : u - t = -(t - u) := by ring
      rw [hneg, norm_plainKernel_neg]
    rw [hcol]
    exact plainKernel_row_mass_recip hN hT hEs hEm (hEs hu)

end

end RHTower.Sieve
