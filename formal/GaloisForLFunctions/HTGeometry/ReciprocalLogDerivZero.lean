import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The reciprocal logarithmic derivative vanishes at a zero

Writing an analytic function with an isolated zero of order `n` as `(z - z₀)^n g` with `g(z₀) ≠ 0`,

`f' = (z - z₀)^{n-1} (n g + (z - z₀) g')`,

so the derivative is nonzero on a punctured neighbourhood, and

`f/f' = (z - z₀) g / (n g + (z - z₀) g')`,

which tends to zero no matter what the order is.  So a zero of `f` is a zero of `f/f'` — the exact
statement a Herglotz limit needs to exclude: a function with strictly positive real part cannot
agree with a constant multiple of `f/f'` near a zero of `f`.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The local factorization at an isolated zero, together with the induced factorization of the
derivative. -/
theorem exists_factorization_of_zero {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hnz : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0) (h0 : f z₀ = 0) :
    ∃ (m : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
      (∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ (m + 1) * g z) ∧
      (∀ᶠ z in 𝓝 z₀, deriv f z
        = (z - z₀) ^ m * (((m : ℂ) + 1) * g z + (z - z₀) * deriv g z)) := by
  obtain ⟨n, g, hg, hg0, hfg⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  have hfg' : ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n * g z := by
    filter_upwards [hfg] with z hz
    simpa [smul_eq_mul] using hz
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · exfalso
      have hval := hfg'.self_of_nhds
      rw [hn0, h0] at hval
      simp at hval
      exact hg0 hval.symm
    · exact hn1
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have hfgEq : f =ᶠ[𝓝 z₀] (fun z => (z - z₀) ^ (m + 1) * g z) := hfg'
  refine ⟨m, g, hg, hg0, hfg', ?_⟩
  filter_upwards [hfgEq.eventuallyEq_nhds, hg.eventually_analyticAt] with z hz hgz
  have hbase : HasDerivAt (fun w : ℂ => w - z₀) 1 z := (hasDerivAt_id z).sub_const z₀
  have hpow : HasDerivAt (fun w : ℂ => (w - z₀) ^ (m + 1))
      (((m : ℂ) + 1) * (z - z₀) ^ m) z := by
    have hcomp := hbase.pow (m + 1)
    simp only [Nat.add_sub_cancel, mul_one] at hcomp
    push_cast at hcomp
    exact hcomp
  have hgd : HasDerivAt g (deriv g z) z := hgz.differentiableAt.hasDerivAt
  have hprod : HasDerivAt (fun w : ℂ => (w - z₀) ^ (m + 1) * g w)
      (((m : ℂ) + 1) * (z - z₀) ^ m * g z + (z - z₀) ^ (m + 1) * deriv g z) z :=
    hpow.mul hgd
  rw [(hprod.congr_of_eventuallyEq hz).deriv]
  ring

private theorem tendsto_sub_self (z₀ : ℂ) : Tendsto (fun z : ℂ => z - z₀) (𝓝[≠] z₀) (𝓝 0) := by
  have hc : Tendsto (fun z : ℂ => z - z₀) (𝓝 z₀) (𝓝 (z₀ - z₀)) :=
    (continuous_sub_right z₀).tendsto z₀
  rw [sub_self] at hc
  exact hc.mono_left nhdsWithin_le_nhds

private theorem tendsto_cofactor {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) (m : ℕ) :
    Tendsto (fun z : ℂ => ((m : ℂ) + 1) * g z + (z - z₀) * deriv g z) (𝓝[≠] z₀)
      (𝓝 (((m : ℂ) + 1) * g z₀)) := by
  have h1 : Tendsto (fun z : ℂ => ((m : ℂ) + 1) * g z) (𝓝[≠] z₀)
      (𝓝 (((m : ℂ) + 1) * g z₀)) :=
    (tendsto_const_nhds.mul hg.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun z : ℂ => (z - z₀) * deriv g z) (𝓝[≠] z₀) (𝓝 0) := by
    simpa using (tendsto_sub_self z₀).mul
      ((hg.deriv).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simpa using h1.add h2

private theorem cast_succ_ne_zero (m : ℕ) : ((m : ℂ) + 1) ≠ 0 := by
  have h : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
  simpa using h

/-- **The derivative is nonzero on a punctured neighbourhood of an isolated zero.** -/
theorem eventually_deriv_ne_zero_of_zero {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hnz : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0) (h0 : f z₀ = 0) :
    ∀ᶠ z in 𝓝[≠] z₀, deriv f z ≠ 0 := by
  obtain ⟨m, g, hg, hg0, -, hderiv⟩ := exists_factorization_of_zero hf hnz h0
  have hne : ∀ᶠ z in 𝓝[≠] z₀, ((m : ℂ) + 1) * g z + (z - z₀) * deriv g z ≠ 0 :=
    (tendsto_cofactor hg m).eventually_ne (mul_ne_zero (cast_succ_ne_zero m) hg0)
  filter_upwards [nhdsWithin_le_nhds hderiv, hne, self_mem_nhdsWithin] with z hdz hcz hzne
  rw [hdz]
  exact mul_ne_zero (pow_ne_zero m (sub_ne_zero.mpr hzne)) hcz

/-- **The reciprocal logarithmic derivative vanishes at an isolated zero.** -/
theorem tendsto_div_deriv_nhdsWithin_zero {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hnz : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0) (h0 : f z₀ = 0) :
    Tendsto (fun z => f z / deriv f z) (𝓝[≠] z₀) (𝓝 0) := by
  obtain ⟨m, g, hg, hg0, hval, hderiv⟩ := exists_factorization_of_zero hf hnz h0
  have hquot : ∀ᶠ z in 𝓝[≠] z₀, f z / deriv f z
      = (z - z₀) * g z / (((m : ℂ) + 1) * g z + (z - z₀) * deriv g z) := by
    filter_upwards [nhdsWithin_le_nhds hval, nhdsWithin_le_nhds hderiv,
      self_mem_nhdsWithin] with z hv hdz hzne
    have hsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hzne
    rw [hv, hdz]
    rw [show (z - z₀) ^ (m + 1) * g z = (z - z₀) ^ m * ((z - z₀) * g z) from by ring]
    rw [mul_div_mul_left _ _ (pow_ne_zero m hsub)]
  have hnum : Tendsto (fun z : ℂ => (z - z₀) * g z) (𝓝[≠] z₀) (𝓝 0) := by
    simpa using (tendsto_sub_self z₀).mul
      (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hlim := hnum.div (tendsto_cofactor hg m) (mul_ne_zero (cast_succ_ne_zero m) hg0)
  rw [zero_div] at hlim
  exact hlim.congr' (hquot.mono fun z hz => hz.symm)

/-- **A continuous function that agrees with a multiple of `f/f'` off an isolated zero of `f`
vanishes at that zero.** -/
theorem eq_zero_of_eventuallyEq_div_deriv {f T : ℂ → ℂ} {z₀ c : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hnz : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0) (h0 : f z₀ = 0)
    (hT : ContinuousAt T z₀)
    (hEq : ∀ᶠ z in 𝓝[≠] z₀, T z = c * (f z / deriv f z)) :
    T z₀ = 0 := by
  have hlim : Tendsto T (𝓝[≠] z₀) (𝓝 (T z₀)) := hT.tendsto.mono_left nhdsWithin_le_nhds
  have hquot : Tendsto (fun z => c * (f z / deriv f z)) (𝓝[≠] z₀) (𝓝 0) := by
    have := (tendsto_div_deriv_nhdsWithin_zero hf hnz h0).const_mul c
    simpa using this
  exact tendsto_nhds_unique hlim (hquot.congr' (hEq.mono fun z hz => hz.symm))

/-- A function with strictly positive real part cannot agree with a multiple of `f/f'` near an
isolated zero of `f`. -/
theorem not_re_pos_of_eventuallyEq_div_deriv {f T : ℂ → ℂ} {z₀ c : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hnz : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0) (h0 : f z₀ = 0)
    (hT : ContinuousAt T z₀)
    (hEq : ∀ᶠ z in 𝓝[≠] z₀, T z = c * (f z / deriv f z)) :
    ¬ (0 < (T z₀).re) := by
  intro hpos
  rw [eq_zero_of_eventuallyEq_div_deriv hf hnz h0 hT hEq] at hpos
  simp at hpos

end GaloisForLFunctions.HTGeometry
