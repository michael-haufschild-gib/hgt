import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSecondOrderTermOfAHorizonBlock

/-!
# The aliasing is the dilation derivative of the bulk

The second-order term of a horizon block is Weil's form plus `log N` times the window average of
the aliasing density `a_φ(s) = Σ_{k ≥ 1} |φ̂(2πks)|²` at the local overlaps `s = cn/N`. The bulk
of the degeneration has its own invariant at overlap `s`: the completed shell energy `E₁(s)` of
the conductor-one packet, whose rescaled limit is the Jordan coefficient `J(1) = lim s^β E₁(s)`.
This file proves that the two are one object:

* **The aliasing density is the dilation derivative of the bulk energy**
  (`hasDerivAt_completedShellEnergy`): `E₁'(s) = −(2/∫φ²) a_φ(s)` for every `s > 0`. The proof
  integrates the harmonics: `E₁(c) − E₁(C) = (2/∫φ²) ∫_c^C a_φ` (`sub_eq_integral_aliasDensity`),
  which is the increment law of the completed shell energy read harmonic by harmonic.

So at depth `y = log(n/N)` of a horizon window, where the atoms overlap `c e^y`, the aliasing that
the block pays is the rate at which the bulk energy decreases under dilation:

`c⁻¹ ⟨W x, x⟩ = κ Q(H) − log N · N⁻¹ Σ_n h(log(n/N))² E₁'(cn/N) + o(1)`.

The second-order term on the horizon layer is the monodromy derivative of the first-order term of
the bulk, tested against the window mass, plus Weil's form.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ : ℝ → ℝ}

/-! ### Regularity of the aliasing density -/

/-- The harmonics are summable uniformly on `s ≥ δ`: `P((k+1)s) ≤ N_φ²/(2πδ)⁴ (k+1)^{−4}`. -/
theorem shellSpectrum_succ_mul_le {Nφ : ℝ}
    (hNφ : ∀ t, shellSpectrum φ t ≤ Nφ ^ 2 / ((1 + |2 * Real.pi * t|) ^ 2) ^ 2) {δ s : ℝ}
    (hδ : 0 < δ) (hs : δ ≤ s) (k : ℕ) :
    shellSpectrum φ ((k + 1) * s) ≤ Nφ ^ 2 / (2 * Real.pi * δ) ^ 4 * (((k : ℝ) + 1) ^ 4)⁻¹ := by
  have hpi := Real.pi_pos
  have hk : (1 : ℝ) ≤ k + 1 := by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
  set x := 2 * Real.pi * ((k + 1) * s) with hx
  have hx0 : 0 < x := by rw [hx]; have : 0 < s := lt_of_lt_of_le hδ hs; positivity
  have hxd : 2 * Real.pi * δ * (k + 1) ≤ x := by
    rw [hx]; nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (k + 1))]
  refine (hNφ _).trans ?_
  rw [abs_of_pos hx0]
  have hden : (2 * Real.pi * δ * (k + 1)) ^ 4 ≤ ((1 + x) ^ 2) ^ 2 := by
    rw [← pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 4
  have e : Nφ ^ 2 / (2 * Real.pi * δ) ^ 4 * (((k : ℝ) + 1) ^ 4)⁻¹ =
      Nφ ^ 2 / (2 * Real.pi * δ * (k + 1)) ^ 4 := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden

theorem summable_inv_succ_pow_four : Summable fun k : ℕ => (((k : ℝ) + 1) ^ 4)⁻¹ := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 4))
  refine h.congr fun k => ?_
  push_cast; rfl

/-- The aliasing density is continuous on `s > 0`. -/
theorem continuousOn_aliasDensity (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) : ContinuousOn (aliasDensity φ) (Set.Ioi 0) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  obtain ⟨Nφ, -, hNφ⟩ := exists_shellSpectrum_le hφ hφc
  intro s hs
  have hs0 : 0 < s := hs
  have hcont : ContinuousOn (aliasDensity φ) (Set.Ioi (s / 2)) := by
    refine continuousOn_tsum (u := fun k : ℕ => Nφ ^ 2 / (2 * Real.pi * (s / 2)) ^ 4 *
      (((k : ℝ) + 1) ^ 4)⁻¹) (fun k => ?_) (summable_inv_succ_pow_four.mul_left _) fun k t ht => ?_
    · exact ((continuous_shellSpectrum hφ.continuous hφc).comp
        (continuous_const.mul continuous_id)).continuousOn
    · rw [Real.norm_eq_abs, abs_of_nonneg (shellSpectrum_nonneg _)]
      exact shellSpectrum_succ_mul_le hNφ (by linarith) (le_of_lt ht) k
  exact (hcont.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt

/-! ### The bulk energy integrates the aliasing density -/

/-- **The increment of the bulk energy is the integral of the aliasing density**:
`E₁(c) − E₁(C) = (2/∫φ²) ∫_c^C a_φ(s) ds`. -/
theorem sub_eq_integral_aliasDensity (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c C : ℝ} (hc : 0 < c)
    (hcC : c ≤ C) :
    completedShellEnergy φ c - completedShellEnergy φ C =
      2 / (∫ u, φ u ^ 2) * ∫ s in c..C, aliasDensity φ s := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  obtain ⟨Nφ, -, hNφ⟩ := exists_shellSpectrum_le hφ hφc
  have hinc := hasSum_completedShellEnergy_sub hφ hφsupp hM hc hcC
  -- each harmonic as an integral over overlaps
  have hterm : ∀ k : ℕ, ((k : ℝ) + 1)⁻¹ *
      ∫ t in ((k : ℝ) + 1) * c..((k : ℝ) + 1) * C, shellSpectrum φ t =
      ∫ s in c..C, shellSpectrum φ ((k + 1) * s) := by
    intro k
    rw [intervalIntegral.integral_comp_mul_left (fun t => shellSpectrum φ t)
      (by positivity : ((k : ℝ) + 1) ≠ 0), smul_eq_mul]
  simp_rw [hterm] at hinc
  -- dominated interchange of the harmonic sum and the integral
  have hsum : HasSum (fun k : ℕ => ∫ s in c..C, shellSpectrum φ ((k + 1) * s))
      (∫ s in c..C, aliasDensity φ s) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k _ => Nφ ^ 2 / (2 * Real.pi * c) ^ 4 * (((k : ℝ) + 1) ^ 4)⁻¹) (fun k => ?_)
      (fun k => ?_) ?_ ?_ ?_
    · exact ((continuous_shellSpectrum hφ.continuous hφc).comp
        (continuous_const.mul continuous_id)).aestronglyMeasurable
    · refine Eventually.of_forall fun s hs => ?_
      rw [Set.uIoc_of_le hcC] at hs
      rw [Real.norm_eq_abs, abs_of_nonneg (shellSpectrum_nonneg _)]
      exact shellSpectrum_succ_mul_le hNφ hc hs.1.le k
    · exact Eventually.of_forall fun s _ => summable_inv_succ_pow_four.mul_left _
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun s hs => ?_
      rw [Set.uIoc_of_le hcC] at hs
      have hs0 : 0 < s := lt_of_lt_of_le hc hs.1.le
      obtain ⟨Nφ', -, hNφ'⟩ := exists_shellSpectrum_le hφ hφc
      exact ((summable_inv_succ_pow_four.mul_left (Nφ' ^ 2 / (2 * Real.pi * s) ^ 4)).of_nonneg_of_le
        (fun k => shellSpectrum_nonneg _) fun k => shellSpectrum_succ_mul_le hNφ' hs0 le_rfl k).hasSum
  have h2 := hsum.mul_left (2 / ∫ u, φ u ^ 2)
  exact hinc.unique h2

/-- **The aliasing density is the dilation derivative of the bulk energy**:
`E₁'(s) = −(2/∫φ²) a_φ(s)` for `s > 0`. -/
theorem hasDerivAt_completedShellEnergy (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (completedShellEnergy φ) (-(2 / (∫ u, φ u ^ 2)) * aliasDensity φ s) s := by
  have hcont := continuousOn_aliasDensity hφ hφsupp
  have hs2 : 0 < s / 2 := by linarith
  have hint : IntervalIntegrable (aliasDensity φ) volume (s / 2) s :=
    (hcont.mono fun t ht => by
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact lt_of_lt_of_le hs2 ht.1).intervalIntegrable
  have hderiv := intervalIntegral.integral_hasDerivAt_right hint
    (hcont.stronglyMeasurableAtFilter isOpen_Ioi s hs) (hcont.continuousAt (Ioi_mem_nhds hs))
  have hev : completedShellEnergy φ =ᶠ[𝓝 s] fun C => completedShellEnergy φ (s / 2) -
      2 / (∫ u, φ u ^ 2) * ∫ t in (s / 2)..C, aliasDensity φ t := by
    filter_upwards [Ioi_mem_nhds (show s / 2 < s by linarith)] with C hC
    have := sub_eq_integral_aliasDensity hφ hφsupp hM hs2 (le_of_lt hC)
    linarith
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have := (hderiv.const_mul (2 / (∫ u, φ u ^ 2))).const_sub (completedShellEnergy φ (s / 2))
  convert this using 1
  ring

/-- The aliasing functional of a horizon block in terms of the bulk:
`(log N/∫φ²) 𝒜_N = −(log N/N) Σ_n h(log(n/N))² E₁'(cn/N)`. -/
theorem log_mul_horizonAlias_eq (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    Real.log N / (∫ u, φ u ^ 2) * horizonAlias φ h c N =
      -(Real.log N / N * ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 *
        deriv (completedShellEnergy φ) (c * n / N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold horizonAlias
  rw [mul_sum, mul_sum, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [(hasDerivAt_completedShellEnergy hφ hφsupp hM (by positivity : 0 < c * n / N)).deriv]
  field_simp

/-- **The second-order term in terms of the bulk.** Along every schedule with `c_N ≥ 1`,
`c_N → ∞`, `c_N (log N)²/N → 0`:
`c⁻¹ ⟨W x, x⟩ − κ Q(H) + (log N/N) Σ_n h(log(n/N))² E₁'(cn/N) → 0`. -/
theorem horizon_layer_sharp_bulk (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 1 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (ArithmeticCastelnuovoSeveri.cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {h : ℝ → ℝ} {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hcinf : Tendsto c atTop atTop)
    (hclog : Tendsto (fun N : ℕ => c N * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (ArithmeticElectrostatics.atomicTest N
        (horizonWeights h N) (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) -
      (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * weilQuad (halfWeight h) +
      Real.log N / N * ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 *
        deriv (completedShellEnergy φ) (c N * n / N)) atTop (𝓝 0) := by
  refine (horizon_layer_sharp hφ hφsupp hφ2 hp hCφ hdecay hh hA hsupp hc1 hcinf hclog).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [log_mul_horizonAlias_eq hφ hφsupp hφ2 h (by linarith [hc1 N]) hN]
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
