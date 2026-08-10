import GaloisForLFunctions.RHTower.Sieve.FibreSqGallagher
import GaloisForLFunctions.RHTower.Sieve.PairFibreTrivial

/-!
# The fibre mean square vanishes, given a small frequency mean square

`sum_fibreSq_le_gallagher` bounds the fibre mean square by one Gallagher budget plus `102·#block`,
and the block has at most `√x + 1` elements.  So

```text
AveragedMeanSquare f hh   ⟸   (the Gallagher budget is o(h²√x)) ,
```

the second term costing only `102(√x+1)/(h²√x) → 0`.  The input is `FrequencyMeanSquareSmall`: at
each large `x` there are admissible parameters `M`, `W₀` and an affine majorant `α·T + β` for the
frequency mean square whose Gallagher budget is below `ε·h²√x`.

With `fibreWidth ≍ h/√x` and the `W₀`-optimum, the budget is `≍ h·α`, so the input says `α = o(h√x)`
— a saving of `h` over the mean-value baseline `α ≍ ∑_{n ≤ M}|f(n)|² ≍ √x`.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Filter Topology Finset

/-- The Gallagher budget of the fibre mean square is `o(h²√x)`: at each large `x` there are
admissible parameters and an affine majorant for the frequency mean square whose budget is small. -/
def FrequencyMeanSquareSmall (f : ℕ → ℝ) (hh : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ x : ℝ in atTop, ∃ M : ℕ, ∃ α β W₀ : ℝ,
    (∀ a ∈ outerBlock x (hh x), innerFibre x (hh x) a ⊆ Finset.Icc 1 M)
      ∧ 0 < W₀ ∧ 0 ≤ α ∧ 0 ≤ β
      ∧ (∀ T : ℝ, W₀ ≤ T → (∫ w in Set.Icc (-T) T,
          ‖logPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2) ≤ α * T + β)
      ∧ 8 * Real.sqrt x
            * (2 * fibreWidth x (hh x) ^ 2 * (α * W₀ + β)
                + (4 * α / (Real.pi ^ 2 * W₀) + 4 * β / (3 * Real.pi ^ 2 * W₀ ^ 2)))
          ≤ ε * (hh x ^ 2 * Real.sqrt x)

/-- **The fibre mean square vanishes, given a small frequency mean square.** -/
theorem averagedMeanSquare_of_frequency {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {hh : ℝ → ℝ}
    (hgrow : Tendsto hh atTop atTop) (hcap : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hinput : FrequencyMeanSquareSmall f hh) :
    AveragedMeanSquare f hh := by
  rw [AveragedMeanSquare, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hquarter : (0 : ℝ) < ε / 4 := by linarith
  -- the block term is harmless
  have hblock : ∀ᶠ x : ℝ in atTop, 102 * (Real.sqrt x + 1) ≤ ε / 4 * (hh x ^ 2 * Real.sqrt x) := by
    filter_upwards [Filter.eventually_ge_atTop (16 : ℝ),
      hgrow.eventually_ge_atTop (Real.sqrt (816 / ε) + 1)] with x hx hhx
    have hs4 : (4 : ℝ) ≤ Real.sqrt x := by
      have h16 : Real.sqrt 16 = 4 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
      rw [← h16]
      exact Real.sqrt_le_sqrt hx
    have hs0 : (0 : ℝ) < Real.sqrt x := by linarith
    have hroot : (0 : ℝ) ≤ 816 / ε := by positivity
    have hsq : Real.sqrt (816 / ε) * Real.sqrt (816 / ε) = 816 / ε :=
      Real.mul_self_sqrt hroot
    have hr0 : (0 : ℝ) ≤ Real.sqrt (816 / ε) := Real.sqrt_nonneg _
    have hh1 : (1 : ℝ) ≤ hh x := by linarith
    have hhbig : 816 / ε ≤ hh x ^ 2 := by
      have hmul : Real.sqrt (816 / ε) * Real.sqrt (816 / ε) ≤ hh x * hh x := by
        refine mul_le_mul (by linarith) (by linarith) hr0 (by linarith)
      nlinarith [hmul, hsq]
    have hkey : 816 ≤ ε * hh x ^ 2 := by
      rw [div_le_iff₀ hε] at hhbig
      linarith
    have hcmp : (Real.sqrt x + 1) ≤ 2 * Real.sqrt x := by linarith
    nlinarith [hkey, hs0, hcmp, hε.le]
  filter_upwards [hinput (ε / 4) hquarter, hblock, hcap,
    hgrow.eventually_ge_atTop (1 : ℝ), Filter.eventually_ge_atTop (16 : ℝ)]
    with x hx hbx hcx hhx hx16
  obtain ⟨M, α, β, W₀, hMsub, hW₀, hα, hβ, hG, hsmall⟩ := hx
  have hs4 : (4 : ℝ) ≤ Real.sqrt x := by
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
    rw [← h16]
    exact Real.sqrt_le_sqrt hx16
  have hs0 : (0 : ℝ) < Real.sqrt x := by linarith
  have hden : (0 : ℝ) < hh x ^ 2 * Real.sqrt x := by
    have : (0 : ℝ) < hh x := by linarith
    positivity
  have hbase := sum_fibreSq_le_gallagher f hf hx16 hhx hcx hMsub hW₀ hα hβ hG
  have hcard := card_outerBlock_le (x := x) (h := hh x) (by linarith) (by linarith)
  have hnum0 : (0 : ℝ) ≤ ∑ a ∈ outerBlock x (hh x), (∑ b ∈ innerFibre x (hh x) a, f b) ^ 2 :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_lt_iff₀ hden]
  nlinarith [hbase, hcard, hsmall, hbx, hnum0, hε]

end RHTower.Sieve

end
