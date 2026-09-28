import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.Basic

/-!
# Residues of logarithmic derivatives

If `f` is analytic at `ζ` with analytic order `n`, write `f = (z - ζ)^n g` near `ζ` with `g`
analytic and `g(ζ) ≠ 0`.  Then `f'/f = n/(z - ζ) + g'/g` on a punctured neighbourhood, so
`(z - ζ) f'(z)/f(z) → n`: the logarithmic derivative has a simple pole of residue `n`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology

/-- **Residue of a logarithmic derivative.** If `f` is analytic at `ζ` with analytic order `n`,
then `(z - ζ) f'(z)/f(z) → n` as `z → ζ`, `z ≠ ζ`. -/
theorem tendsto_sub_mul_logDeriv_of_analyticOrderAt {f : ℂ → ℂ} {ζ : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f ζ) (hn : analyticOrderAt f ζ = n) :
    Tendsto (fun z => (z - ζ) * logDeriv f z) (𝓝[≠] ζ) (𝓝 (n : ℂ)) := by
  obtain ⟨g, hg, hg0, hfg⟩ := (hf.analyticOrderAt_eq_natCast).mp hn
  have hgc : ContinuousAt g ζ := hg.continuousAt
  have hg'c : ContinuousAt (deriv g) ζ := hg.deriv.continuousAt
  -- a neighbourhood where the factorization holds and `g` does not vanish
  obtain ⟨U, hUo, hζU, hU⟩ : ∃ U : Set ℂ, IsOpen U ∧ ζ ∈ U ∧
      ∀ z ∈ U, f z = (z - ζ) ^ n • g z ∧ g z ≠ 0 ∧ AnalyticAt ℂ g z := by
    have h1 := hfg.and ((hgc.eventually_ne hg0).and hg.eventually_analyticAt)
    obtain ⟨U, hUsub, hUo, hζU⟩ := mem_nhds_iff.mp h1
    exact ⟨U, hUo, hζU, fun z hz => hUsub hz⟩
  have hlog : ∀ z ∈ U, z ≠ ζ → (z - ζ) * logDeriv f z = n + (z - ζ) * (deriv g z / g z) := by
    intro z hz hzζ
    obtain ⟨-, hgz, hgan⟩ := hU z hz
    have heq : f =ᶠ[𝓝 z] fun w => (w - ζ) ^ n * g w := by
      filter_upwards [hUo.mem_nhds hz] with w hw
      rw [(hU w hw).1, smul_eq_mul]
    have hd : HasDerivAt (fun w => (w - ζ) ^ n * g w)
        ((n : ℂ) * (z - ζ) ^ (n - 1) * g z + (z - ζ) ^ n * deriv g z) z := by
      have h1 : HasDerivAt (fun w : ℂ => (w - ζ) ^ n) ((n : ℂ) * (z - ζ) ^ (n - 1)) z := by
        have := (hasDerivAt_pow n (z - ζ)).comp z ((hasDerivAt_id z).sub_const ζ)
        simpa [Function.comp_def] using this
      exact h1.mul hgan.differentiableAt.hasDerivAt
    have hsub : z - ζ ≠ 0 := sub_ne_zero.mpr hzζ
    rw [logDeriv_apply, heq.deriv_eq, hd.deriv, heq.eq_of_nhds]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp only [CharP.cast_eq_zero, zero_mul, zero_add, pow_zero, one_mul]
    · have hpow : (z - ζ) ^ n = (z - ζ) * (z - ζ) ^ (n - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hpow]
      have hp1 : (z - ζ) ^ (n - 1) ≠ 0 := pow_ne_zero _ hsub
      field_simp
  have hlim : Tendsto (fun z => (n : ℂ) + (z - ζ) * (deriv g z / g z)) (𝓝[≠] ζ) (𝓝 (n : ℂ)) := by
    have h : ContinuousAt (fun z => (n : ℂ) + (z - ζ) * (deriv g z / g z)) ζ :=
      continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul (hg'c.div hgc hg0))
    have := h.tendsto.mono_left (nhdsWithin_le_nhds (s := {ζ}ᶜ))
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hUo.mem_nhds hζU)] with z hzζ hzU
  exact (hlog z hzU hzζ).symm

end

end GaloisForLFunctions.HTGeometry
