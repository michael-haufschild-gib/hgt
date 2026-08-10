import GaloisForLFunctions.RHTower.Sieve.MRFromUniformCorrelations

/-!
# The averaged Chowla theorem, and what the reduction needs from it

The published statement — Matomäki, Radziwiłł and Tao — is

```text
∑_{k ≤ H} | ∑_{n ≤ Y} f(n)·f(n+k) |  =  o(H·Y)      (Y → ∞,  H = H(Y) → ∞) ,
```

recorded here in the equivalent two-parameter uniform form `AveragedChowlaUniform`.

The reduction needs the same sum at length `J ≤ ⌈√x + h⌉ + 5` with the normalisation `ε·h·√x`.
The passage is a single split at `J = ε√x`:

* below it the trivial bound `|∑_{i<J}| ≤ J` gives `∑_{k ≤ h} ≤ h·ε√x` outright;
* above it the theorem applies — the length `J ≍ √x` tends to infinity, and `H = ⌊h⌋ ≤ J` because
  the window law satisfies `h = o(√x)` — and gives `(ε/3)·h·3√x`.

So no cancellation is needed below `ε√x`, and above it exactly the published estimate is used.  The
window condition `h/√x → 0` is what makes the shift range fit inside the length; every window law
used downstream satisfies it.
-/

noncomputable section

namespace RHTower.Sieve

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

/-- **The averaged form of Chowla's conjecture**, in two-parameter uniform form. -/
def AveragedChowlaUniform (f : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ H₀ Y₀ : ℕ, ∀ H Y : ℕ, H₀ ≤ H → Y₀ ≤ Y → H ≤ Y →
    ∑ k ∈ Finset.Icc 1 H, |∑ i ∈ Finset.range Y, f i * f (i + k)| ≤ ε * H * Y

/-- The trivial bound on a correlation sum of a unit-bounded weight. -/
theorem abs_correlation_le_length {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) (k J : ℕ) :
    |∑ i ∈ Finset.range J, f i * f (i + k)| ≤ (J : ℝ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ i ∈ Finset.range J, |f i * f (i + k)| ≤ 1 := by
    intro i _
    rw [abs_mul]
    nlinarith [hf i, hf (i + k), abs_nonneg (f i), abs_nonneg (f (i + k))]
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 hterm) ?_
  rw [nsmul_eq_mul, Finset.card_range, mul_one]

/-- A window law with `h/√x → 0` is eventually below every fixed multiple of `√x`. -/
theorem eventually_le_const_mul_sqrt {hh : ℝ → ℝ}
    (hsmall : Tendsto (fun x => hh x / Real.sqrt x) atTop (𝓝 0)) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, hh x ≤ c * Real.sqrt x := by
  filter_upwards [Metric.tendsto_nhds.1 hsmall c hc, Filter.eventually_gt_atTop (0 : ℝ)]
    with x hx hx0
  have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  rw [Real.dist_eq, sub_zero] at hx
  have hlt := (abs_lt.1 hx).2
  rw [div_lt_iff₀ hs] at hlt
  linarith

/-- **The reduction's input follows from the averaged Chowla theorem.** -/
theorem uniformCorrelationSmall_of_averagedChowla {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1)
    {hh : ℝ → ℝ} (hgrow : Tendsto hh atTop atTop)
    (hsmall : Tendsto (fun x => hh x / Real.sqrt x) atTop (𝓝 0))
    (hAC : AveragedChowlaUniform (fun i => f (i + 1))) :
    UniformCorrelationSmall f hh := by
  intro ε hε
  obtain ⟨H₀, Y₀, hbound⟩ := hAC (ε / 3) (by linarith)
  -- the window is eventually below `ε√x` and below `√x`
  have hcapε : ∀ᶠ x : ℝ in atTop, hh x ≤ ε * Real.sqrt x :=
    eventually_le_const_mul_sqrt hsmall hε
  have hcap1 : ∀ᶠ x : ℝ in atTop, hh x ≤ Real.sqrt x := by
    have := eventually_le_const_mul_sqrt hsmall (c := 1) (by norm_num)
    simpa using this
  have hY0 : ∀ᶠ x : ℝ in atTop, (Y₀ : ℝ) ≤ ε * Real.sqrt x := by
    have := Real.tendsto_sqrt_atTop.const_mul_atTop hε
    exact this.eventually_ge_atTop _
  filter_upwards [hcapε, hcap1, hY0, hgrow.eventually_ge_atTop (max 1 (H₀ : ℝ)),
    Filter.eventually_ge_atTop (64 : ℝ)] with x hxε hx1 hxY hxH hx64
  intro J hJ
  set h := hh x with hhdef
  have hs8 : (8 : ℝ) ≤ Real.sqrt x := eight_le_sqrt hx64
  have hh1 : (1 : ℝ) ≤ h := le_trans (le_max_left _ _) hxH
  have hh0 : (0 : ℝ) ≤ h := by linarith
  have hflR : ((⌊h⌋₊ : ℕ) : ℝ) ≤ h := Nat.floor_le hh0
  have hHH : (H₀ : ℝ) ≤ h := le_trans (le_max_right _ _) hxH
  have hH0 : H₀ ≤ ⌊h⌋₊ := Nat.le_floor hHH
  have hJlen : (J : ℝ) ≤ Real.sqrt x + h + 6 := by
    have hceil : ((⌈Real.sqrt x + h⌉₊ : ℕ) : ℝ) < Real.sqrt x + h + 1 :=
      Nat.ceil_lt_add_one (by linarith [Real.sqrt_nonneg x])
    have : ((J : ℕ) : ℝ) ≤ ((fibreWinHi x h + 2 : ℕ) : ℝ) := by exact_mod_cast hJ
    rw [fibreWinHi] at this
    push_cast at this
    linarith
  rcases lt_or_ge (J : ℝ) (ε * Real.sqrt x) with hsmallJ | hbigJ
  · -- below the split: the trivial bound suffices
    refine le_trans (Finset.sum_le_card_nsmul _ _ (J : ℝ)
      (fun k _ => abs_correlation_le_length (fun n => hf (n + 1)) k J)) ?_
    rw [nsmul_eq_mul, Nat.card_Icc]
    have hcard : (((⌊h⌋₊ + 1 - 1 : ℕ)) : ℝ) ≤ h := by
      simpa using hflR
    have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
    have hstep : (((⌊h⌋₊ + 1 - 1 : ℕ)) : ℝ) * (J : ℝ) ≤ h * (ε * Real.sqrt x) :=
      mul_le_mul hcard hsmallJ.le hJ0 hh0
    calc (((⌊h⌋₊ + 1 - 1 : ℕ)) : ℝ) * (J : ℝ) ≤ h * (ε * Real.sqrt x) := hstep
      _ = ε * (h * Real.sqrt x) := by ring
  · -- above the split: the theorem applies
    have hHJ : ⌊h⌋₊ ≤ J := by
      have : ((⌊h⌋₊ : ℕ) : ℝ) ≤ (J : ℝ) := by linarith
      exact_mod_cast this
    have hYJ : Y₀ ≤ J := by
      have : ((Y₀ : ℕ) : ℝ) ≤ (J : ℝ) := by linarith
      exact_mod_cast this
    refine le_trans (hbound ⌊h⌋₊ J hH0 hYJ hHJ) ?_
    have hJ3 : (J : ℝ) ≤ 3 * Real.sqrt x := by linarith
    have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
    have hfl0 : (0 : ℝ) ≤ ((⌊h⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hstep : ((⌊h⌋₊ : ℕ) : ℝ) * (J : ℝ) ≤ h * (3 * Real.sqrt x) :=
      mul_le_mul hflR hJ3 hJ0 hh0
    have hscale : ε / 3 * (((⌊h⌋₊ : ℕ) : ℝ) * (J : ℝ)) ≤ ε / 3 * (h * (3 * Real.sqrt x)) :=
      mul_le_mul_of_nonneg_left hstep (by linarith)
    calc ε / 3 * ((⌊h⌋₊ : ℕ) : ℝ) * (J : ℝ)
        = ε / 3 * (((⌊h⌋₊ : ℕ) : ℝ) * (J : ℝ)) := by ring
      _ ≤ ε / 3 * (h * (3 * Real.sqrt x)) := hscale
      _ = ε * (h * Real.sqrt x) := by ring

/-- **The bilinear all-interval theorem at `μ`, from the averaged Chowla theorem.** -/
theorem MRBilinear_moebius_of_averagedChowla {hh : ℝ → ℝ} (hgrow : Tendsto hh atTop atTop)
    (hsmall : Tendsto (fun x => hh x / Real.sqrt x) atTop (𝓝 0))
    (hAC : AveragedChowlaUniform (fun i => ((μ (i + 1) : ℤ) : ℝ))) :
    MRBilinear (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh := by
  have hcap : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x := by
    have := eventually_le_const_mul_sqrt hsmall (c := 1) (by norm_num)
    simpa using this
  exact MRBilinear_moebius_of_uniformCorrelations hgrow hcap
    (uniformCorrelationSmall_of_averagedChowla abs_moebius_real_le_one hgrow hsmall hAC)

end RHTower.Sieve

end
