/-
# Harmonic ∘ holomorphic is harmonic

A general transport lemma, not specific to the Böttcher setting: precomposing a harmonic function
with a holomorphic map yields a harmonic function. The mechanism is the local holomorphic primitive
(`HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`): a harmonic `g` equals `Re F` for a holomorphic
`F` on a ball; then `g ∘ f = Re (F ∘ f)` with `F ∘ f` holomorphic, whose real part is harmonic.

This is the law that extends the near-`∞` dynamical Green's function down the whole basin: writing
`G_c = 2⁻ⁿ · (G_c ∘ f_c^[n])`, harmonicity on the escape region propagates through every holomorphic
iterate `f_c^[n]` to the full exterior `Ω_c` — the domain where the natural-boundary (connected
case) argument lives.
-/
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

open Complex InnerProductSpace Metric Topology

/-- **Harmonic ∘ holomorphic is harmonic.** If `g : ℂ → ℝ` is harmonic at `f x` and `f : ℂ → ℂ`
is analytic (holomorphic) at `x`, then `g ∘ f` is harmonic at `x`. -/
theorem HarmonicAt.comp_analytic {g : ℂ → ℝ} {f : ℂ → ℂ} {x : ℂ}
    (hg : HarmonicAt g (f x)) (hf : AnalyticAt ℂ f x) :
    HarmonicAt (g ∘ f) x := by
  have hmem : {y | HarmonicAt g y} ∈ 𝓝 (f x) := (isOpen_setOf_harmonicAt g).mem_nhds hg
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.1 hmem
  have hgball : HarmonicOnNhd g (ball (f x) R) := fun y hy => hRsub hy
  obtain ⟨F, hFan, hFeq⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hgball
  have hcomp : AnalyticAt ℂ (F ∘ f) x := (hFan (f x) (mem_ball_self hR)).comp hf
  have hharm : HarmonicAt (fun y => ((F ∘ f) y).re) x := AnalyticAt.harmonicAt_re hcomp
  have hpre : f ⁻¹' (ball (f x) R) ∈ 𝓝 x :=
    hf.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hR)
  have heq : (fun y => ((F ∘ f) y).re) =ᶠ[𝓝 x] (g ∘ f) := by
    filter_upwards [hpre] with y hy
    simp only [Function.comp_apply]; exact hFeq hy
  exact (harmonicAt_congr_nhds heq).mp hharm

/-- `HarmonicOnNhd` version: `g` harmonic near `f '' s` and `f` analytic on `s` ⟹ `g ∘ f` harmonic
near `s`. The pointwise transport, packaged for an open domain. -/
theorem HarmonicOnNhd.comp_analytic {g : ℂ → ℝ} {f : ℂ → ℂ} {s : Set ℂ}
    (hf : ∀ x ∈ s, AnalyticAt ℂ f x) (hg : ∀ x ∈ s, HarmonicAt g (f x)) :
    HarmonicOnNhd (g ∘ f) s :=
  fun x hx => HarmonicAt.comp_analytic (hg x hx) (hf x hx)
