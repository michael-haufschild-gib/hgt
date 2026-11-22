import Mathlib

/-! Local decomposition of the logarithmic derivative at a zero of finite order. -/

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ExplicitRect

theorem logDeriv_pole {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p)
    (hn : analyticOrderAt f p ≠ ⊤) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ s in 𝓝[≠] p,
      deriv f s / f s = ((analyticOrderNatAt f p : ℕ) : ℂ) / (s - p) + g s := by
  obtain ⟨g0, hg0, hg0p, hfg⟩ :=
    (hf.analyticOrderAt_eq_natCast (n := analyticOrderNatAt f p)).mp (Nat.cast_analyticOrderNatAt hn).symm
  generalize analyticOrderNatAt f p = n at hfg ⊢
  refine ⟨fun s => deriv g0 s / g0 s, hg0.deriv.div hg0 hg0p, ?_⟩
  have hne : ∀ᶠ s in 𝓝 p, g0 s ≠ 0 := hg0.continuousAt.eventually_ne hg0p
  have hdiff : ∀ᶠ s in 𝓝 p, DifferentiableAt ℂ g0 s :=
    hg0.eventually_analyticAt.mono fun s hs => hs.differentiableAt
  filter_upwards [nhdsWithin_le_nhds hne, nhdsWithin_le_nhds hfg.eventually_nhds,
    nhdsWithin_le_nhds hdiff, nhdsWithin_le_nhds hfg, self_mem_nhdsWithin] with s h1 h2 h3 h4 h5
  have hsp : s - p ≠ 0 := sub_ne_zero.mpr h5
  have hd : HasDerivAt (fun z => (z - p) ^ n • g0 z)
      ((n : ℂ) * (s - p) ^ (n - 1) * 1 * g0 s + (s - p) ^ n * deriv g0 s) s := by
    have := (((hasDerivAt_id' s).sub_const p).pow n).mul h3.hasDerivAt
    convert this using 1
    all_goals rfl
  have h2' : f =ᶠ[𝓝 s] fun z => (z - p) ^ n • g0 z := h2
  rw [h2'.deriv_eq, h4, hd.deriv, smul_eq_mul]
  rcases n with _ | k
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]
    field_simp

theorem analyticAt_cpow {u : ℝ} (hu : 0 < u) (p : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (u : ℂ) ^ s) p := analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.2 hu)

end GlobalTheory.ExplicitRect
