import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.DistinctEffectiveCyclesMeetNonnegatively
import GaloisForLFunctions.RHTower.PrimeBlindNonnegativeConeReduction

/-!
# The successor collar: consecutive Hecke cycles meet through the archimedean density alone

Two effective cycles concentrated near `a < b` (supports in `[a − δ, a + δ]`, `[b − δ, b + δ]`,
`2δ < b − a`) have archimedean collar (item 22‴, `localPair_eq_of_disjoint`)

    ∫_0^∞ ω(x) ∫ f(u) g(u + x) du dx,

and the inner integral lives on `|x − (b − a)| ≤ 2δ` with total mass `(∫f)(∫g)`. Since `ω` is
decreasing, the collar lies between `ω(b − a ± 2δ)·(∫f)(∫g)` (`collar_bounds`).

**Successor cycles** (`successor_localPair_bounds`). For `k ≥ 2` and narrow bumps at `log k` and
`log(k + 1)` the prime incidence vanishes (the lag `log(1 + 1/k) < log 2` is not the logarithm of an
integer), so the local intersection is the collar alone:

    ω(d + 2δ) m_f m_g ≤ f · g ≤ ω(d − 2δ) m_f m_g,    d = log(1 + 1/k),

with the narrow value `ω(log(1 + 1/k)) = (k + 1)√(k(k + 1))/(2k + 1)` (`archLevyDensity_log_succ`),
which grows like `k/2`. The successor cell thus carries two different numbers: its **pole mass**
`1/(k(k + 1))` (`integral_successorCell`, the pronic weight) and its **collar**
`ω(log(1 + 1/k)) ≍ k/2`, the archimedean intersection of the two Hecke cycles bounding it. Over
`𝔽_q[T]` the successor cell is degenerate (`successorCell_functionField`) and both vanish.
-/

open MeasureTheory Set Filter
open Zeta23 RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- `ω(log t) = t√t/(t² − 1)` for `t > 1`. -/
theorem archLevyDensity_log {t : ℝ} (ht : 1 < t) :
    archLevyDensity (Real.log t) = t * Real.sqrt t / (t ^ 2 - 1) := by
  have ht0 : 0 < t := by linarith
  have ht0' := ht0.ne'
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs' := hs.ne'
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have ht2 : t ^ 2 - 1 ≠ 0 := by nlinarith
  unfold archLevyDensity
  have e1 : Real.exp (-Real.log t / 2) = (Real.sqrt t)⁻¹ := by
    rw [neg_div, Real.exp_neg, ← Real.log_sqrt ht0.le, Real.exp_log hs]
  have e2 : Real.exp (-2 * Real.log t) = (t ^ 2)⁻¹ := by
    rw [show -2 * Real.log t = -Real.log (t ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_neg, Real.exp_log (by positivity)]
  have hinv : (Real.sqrt t)⁻¹ = Real.sqrt t / t := by
    rw [eq_div_iff ht0', inv_mul_eq_div, div_eq_iff hs', hss]
  rw [e1, e2, hinv, show 1 - (t ^ 2)⁻¹ = (t ^ 2 - 1) / t ^ 2 by field_simp]
  field_simp

/-- **The successor collar density**: `ω(log(1 + 1/k)) = (k + 1)√(k(k + 1))/(2k + 1)`. -/
theorem archLevyDensity_log_succ {k : ℕ} (hk : 1 ≤ k) :
    archLevyDensity (Real.log (((k : ℝ) + 1) / k)) =
      ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) * (k + 1)) / (2 * k + 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk0' := hk0.ne'
  have ht : 1 < ((k : ℝ) + 1) / k := by rw [lt_div_iff₀ hk0]; linarith
  have hsq : Real.sqrt ((k : ℝ) * (k + 1)) = k * Real.sqrt (((k : ℝ) + 1) / k) := by
    rw [show (k : ℝ) * (k + 1) = k ^ 2 * (((k : ℝ) + 1) / k) by field_simp,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk0.le]
  have h2 : (2 : ℝ) * k + 1 ≠ 0 := by positivity
  rw [archLevyDensity_log ht, hsq,
    show (((k : ℝ) + 1) / k) ^ 2 - 1 = (2 * k + 1) / k ^ 2 by field_simp; ring]
  field_simp

section Collar

variable {f g : ℝ → ℝ} {a b δ : ℝ}

/-- The forward cross-correlation `c(x) = ∫ f(u) g(u + x) du`. -/
def crossCorr (f g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u, f u * g (u + x)

theorem crossCorr_nonneg (hf0 : ∀ u, 0 ≤ f u) (hg0 : ∀ u, 0 ≤ g u) (x : ℝ) :
    0 ≤ crossCorr f g x :=
  integral_nonneg fun u => mul_nonneg (hf0 u) (hg0 _)

/-- The cross-correlation of concentrated cycles lives on `|x − (b − a)| ≤ 2δ`. -/
theorem crossCorr_eq_zero (hfs : ∀ u, f u ≠ 0 → |u - a| ≤ δ) (hgs : ∀ u, g u ≠ 0 → |u - b| ≤ δ)
    {x : ℝ} (hx : 2 * δ < |x - (b - a)|) : crossCorr f g x = 0 := by
  rw [crossCorr, ← integral_zero ℝ ℝ]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  by_contra hne
  have h1 := hfs u (left_ne_zero_of_mul hne)
  have h2 := hgs (u + x) (right_ne_zero_of_mul hne)
  have : |x - (b - a)| ≤ 2 * δ := by
    calc |x - (b - a)| = |(u + x - b) - (u - a)| := by ring_nf
      _ ≤ |u + x - b| + |u - a| := abs_sub _ _
      _ ≤ 2 * δ := by linarith
  linarith

/-- The cycle `(x, u) ↦ f(u) g(u + x)` is integrable on the plane. -/
theorem integrable_crossKernel (hf : Continuous f) (hg : Continuous g)
    (hfs : ∀ u, f u ≠ 0 → |u - a| ≤ δ) (hgs : ∀ u, g u ≠ 0 → |u - b| ≤ δ) :
    Integrable (fun p : ℝ × ℝ => f p.2 * g (p.2 + p.1)) (volume.prod volume) := by
  have hc : Continuous fun p : ℝ × ℝ => f p.2 * g (p.2 + p.1) := by fun_prop
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro
    ((isCompact_Icc (a := b - a - 2 * δ) (b := b - a + 2 * δ)).prod
      (isCompact_Icc (a := a - δ) (b := a + δ))) fun p hp => ?_)
  by_contra hne
  obtain ⟨h1, h1'⟩ := abs_le.mp (hfs p.2 (left_ne_zero_of_mul hne))
  obtain ⟨h2, h2'⟩ := abs_le.mp (hgs (p.2 + p.1) (right_ne_zero_of_mul hne))
  exact hp ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **The cross-correlation has total mass `(∫f)(∫g)`.** -/
theorem integral_crossCorr (hf : Continuous f) (hg : Continuous g)
    (hfs : ∀ u, f u ≠ 0 → |u - a| ≤ δ) (hgs : ∀ u, g u ≠ 0 → |u - b| ≤ δ) :
    ∫ x, crossCorr f g x = (∫ u, f u) * ∫ u, g u := by
  have hint := integrable_crossKernel hf hg hfs hgs
  have hswap := integral_integral_swap (f := fun x u => f u * g (u + x)) hint
  simp only [crossCorr]
  rw [hswap, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [integral_const_mul, integral_add_left_eq_self (fun x => g x) u]

/-- **Collar bounds.** Effective cycles concentrated near `a < b` have archimedean collar between
`ω(b − a ± 2δ)·(∫f)(∫g)`. -/
theorem collar_bounds (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ u, 0 ≤ f u)
    (hg0 : ∀ u, 0 ≤ g u) (hfs : ∀ u, f u ≠ 0 → |u - a| ≤ δ)
    (hgs : ∀ u, g u ≠ 0 → |u - b| ≤ δ) (hab : 2 * δ < b - a) :
    archLevyDensity (b - a + 2 * δ) * ((∫ u, f u) * ∫ u, g u) ≤
        ∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u, (f u * g (u + x) + f (u + x) * g u) ∧
      ∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u, (f u * g (u + x) + f (u + x) * g u) ≤
        archLevyDensity (b - a - 2 * δ) * ((∫ u, f u) * ∫ u, g u) := by
  set c := crossCorr f g
  -- for `x > 0` the backward term vanishes
  have hback : ∀ x ∈ Ioi (0 : ℝ), ∫ u, (f u * g (u + x) + f (u + x) * g u) = c x := by
    intro x hx
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have : f (u + x) * g u = 0 := by
      by_contra hne
      obtain ⟨-, h1⟩ := abs_le.mp (hfs (u + x) (left_ne_zero_of_mul hne))
      obtain ⟨h2, -⟩ := abs_le.mp (hgs u (right_ne_zero_of_mul hne))
      have := mem_Ioi.mp hx
      linarith
    simp only [this, add_zero]
  have hint := integrable_crossKernel hf hg hfs hgs
  have hcint : Integrable c := hint.integral_prod_left
  -- `c` lives on `[b − a − 2δ, b − a + 2δ] ⊂ (0, ∞)`
  have hsupp : ∀ x, c x ≠ 0 → b - a - 2 * δ ≤ x ∧ x ≤ b - a + 2 * δ := fun x hx => by
    by_contra h
    apply hx
    refine crossCorr_eq_zero hfs hgs ?_
    rw [lt_abs]
    rcases not_and_or.mp h with h | h
    · right; linarith
    · left; linarith
  have hmass : ∫ x in Ioi (0 : ℝ), c x = (∫ u, f u) * ∫ u, g u := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_,
      integral_crossCorr hf hg hfs hgs]
    by_contra hne
    have := (hsupp x hne).1
    exact hx (mem_Ioi.mpr (by linarith))
  -- the density is pinned on the support
  have hlo : ∀ x ∈ Ioi (0 : ℝ),
      archLevyDensity (b - a + 2 * δ) * c x ≤ archLevyDensity x * c x := fun x hx => by
    by_cases h0 : c x = 0
    · simp [h0]
    · have hx' := mem_Ioi.mp hx
      have hs := hsupp x h0
      refine mul_le_mul_of_nonneg_right ?_ (crossCorr_nonneg hf0 hg0 x)
      exact NonnegativeCone.antitoneOn_archLevyDensity hx (mem_Ioi.mpr (by linarith)) hs.2
  have hhi : ∀ x ∈ Ioi (0 : ℝ),
      archLevyDensity x * c x ≤ archLevyDensity (b - a - 2 * δ) * c x := fun x hx => by
    by_cases h0 : c x = 0
    · simp [h0]
    · have hs := hsupp x h0
      refine mul_le_mul_of_nonneg_right ?_ (crossCorr_nonneg hf0 hg0 x)
      exact NonnegativeCone.antitoneOn_archLevyDensity (mem_Ioi.mpr (by linarith)) hx hs.1
  have hωc : IntegrableOn (fun x => archLevyDensity x * c x) (Ioi 0) := by
    refine Integrable.mono' ((hcint.const_mul (archLevyDensity (b - a - 2 * δ))).integrableOn)
      ((measurable_archLevyDensity.aestronglyMeasurable.mul hcint.aestronglyMeasurable).restrict)
      ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_of_nonneg (mul_nonneg (archLevyDensity_pos hx).le (crossCorr_nonneg hf0 hg0 x))]
    exact hhi x hx
  have hcongr : ∫ x in Ioi (0 : ℝ), archLevyDensity x *
      ∫ u, (f u * g (u + x) + f (u + x) * g u) = ∫ x in Ioi (0 : ℝ), archLevyDensity x * c x :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [hback x hx]
  rw [hcongr]
  constructor
  · calc archLevyDensity (b - a + 2 * δ) * ((∫ u, f u) * ∫ u, g u)
        = ∫ x in Ioi (0 : ℝ), archLevyDensity (b - a + 2 * δ) * c x := by
          rw [integral_const_mul, hmass]
      _ ≤ ∫ x in Ioi (0 : ℝ), archLevyDensity x * c x :=
          setIntegral_mono_on (hcint.integrableOn.const_mul _) hωc measurableSet_Ioi hlo
  · calc ∫ x in Ioi (0 : ℝ), archLevyDensity x * c x
        ≤ ∫ x in Ioi (0 : ℝ), archLevyDensity (b - a - 2 * δ) * c x :=
          setIntegral_mono_on hωc (hcint.integrableOn.const_mul _) measurableSet_Ioi hhi
      _ = archLevyDensity (b - a - 2 * δ) * ((∫ u, f u) * ∫ u, g u) := by
          rw [integral_const_mul, hmass]

/-- An autocorrelation of real tests as a real integral: `(f ⋆ g̃)(x) = ∫ f(t) g(t − x) dt`. -/
theorem weilTest_ofReal (x : ℝ) :
    EF.weilTest (fun u => (f u : ℂ)) (fun u => (g u : ℂ)) x = ((∫ t, f t * g (t - x) : ℝ) : ℂ) := by
  rw [EF.weilTest, convolution_def, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', EF.tilde, Complex.conj_ofReal, neg_sub]
  push_cast
  ring

/-- Concentrated cycles have autocorrelation supported at lag `a − b ± 2δ`. -/
theorem weilTest_eq_zero_of_far (hfs : ∀ u, f u ≠ 0 → |u - a| ≤ δ)
    (hgs : ∀ u, g u ≠ 0 → |u - b| ≤ δ) {x : ℝ} (hx : 2 * δ < |x - (a - b)|) :
    EF.weilTest (fun u => (f u : ℂ)) (fun u => (g u : ℂ)) x = 0 := by
  rw [weilTest_ofReal, ← Complex.ofReal_zero, ← integral_zero ℝ ℝ]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_contra hne
  have h1 := hfs t (left_ne_zero_of_mul hne)
  have h2 := hgs (t - x) (right_ne_zero_of_mul hne)
  have : |x - (a - b)| ≤ 2 * δ := by
    calc |x - (a - b)| = |(t - a) - (t - x - b)| := by ring_nf
      _ ≤ |t - a| + |t - x - b| := abs_sub _ _
      _ ≤ 2 * δ := by linarith
  linarith

end Collar

/-- **Consecutive Hecke cycles meet through the collar alone.** For `k ≥ 2` and effective cycles
concentrated within `δ` of `log k` and `log(k + 1)`, with `2δ < log(1 + 1/k)` and
`log(1 + 1/k) + 2δ < log 2`, the prime incidence vanishes and the local intersection lies between
`ω(log(1 + 1/k) ± 2δ)·(∫f)(∫g)`. -/
theorem successor_localPair_bounds {k : ℕ} (hk : 2 ≤ k) {f g : ℝ → ℝ} {δ : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hg0 : ∀ u, 0 ≤ g u)
    (hfs : ∀ u, f u ≠ 0 → |u - Real.log k| ≤ δ)
    (hgs : ∀ u, g u ≠ 0 → |u - Real.log ((k : ℝ) + 1)| ≤ δ)
    (hδ : 2 * δ < Real.log (((k : ℝ) + 1) / k))
    (hδ' : Real.log (((k : ℝ) + 1) / k) + 2 * δ < Real.log 2) :
    archLevyDensity (Real.log (((k : ℝ) + 1) / k) + 2 * δ) * ((∫ u, f u) * ∫ u, g u) ≤
        (localPair (fun u => (f u : ℂ)) (fun u => (g u : ℂ))).re ∧
      (localPair (fun u => (f u : ℂ)) (fun u => (g u : ℂ))).re ≤
        archLevyDensity (Real.log (((k : ℝ) + 1) / k) - 2 * δ) * ((∫ u, f u) * ∫ u, g u) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hd : Real.log ((k : ℝ) + 1) - Real.log k = Real.log (((k : ℝ) + 1) / k) :=
    (Real.log_div (by positivity) hk0.ne').symm
  -- disjoint supports
  have hfg : ∀ u, f u * g u = 0 := fun u => by
    by_contra hne
    obtain ⟨h1, h1'⟩ := abs_le.mp (hfs u (left_ne_zero_of_mul hne))
    obtain ⟨h2, h2'⟩ := abs_le.mp (hgs u (right_ne_zero_of_mul hne))
    linarith
  -- the prime incidence vanishes
  have ht : 1 < ((k : ℝ) + 1) / k := by rw [lt_div_iff₀ hk0]; linarith
  have hdpos : 0 < Real.log (((k : ℝ) + 1) / k) := Real.log_pos ht
  have hdlt : Real.log (((k : ℝ) + 1) / k) < Real.log 2 := by
    refine Real.log_lt_log (by positivity) ?_
    rw [div_lt_iff₀ hk0]
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hlog2 : ∀ n : ℕ, 2 ≤ n → Real.log 2 ≤ Real.log n := fun n hn =>
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hprime : (∑' n : ℕ, ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
      else 0 : ℝ) : ℂ) * (EF.weilTest (fun u => (f u : ℂ)) (fun u => (g u : ℂ)) (Real.log n) +
        EF.weilTest (fun u => (f u : ℂ)) (fun u => (g u : ℂ)) (-Real.log n))) = 0 := by
    refine (tsum_congr fun n => ?_).trans tsum_zero
    by_cases hn : 2 ≤ n
    · have hl := hlog2 n hn
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h1 : 2 * δ < |Real.log n - (Real.log k - Real.log ((k : ℝ) + 1))| := by
        rw [abs_of_pos (by linarith)]; linarith
      have h2 : 2 * δ < |-Real.log n - (Real.log k - Real.log ((k : ℝ) + 1))| := by
        rw [abs_of_neg (by linarith)]; linarith
      rw [weilTest_eq_zero_of_far hfs hgs h1, weilTest_eq_zero_of_far hfs hgs h2, add_zero,
        mul_zero]
    · simp [hn]
  have hcol := collar_bounds hf.continuous hg.continuous hf0 hg0 hfs hgs (by linarith)
  rw [localPair_eq_of_disjoint hf hfc hg hgc hfg, hprime, Complex.zero_re, zero_add]
  rw [hd] at hcol
  exact hcol

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
