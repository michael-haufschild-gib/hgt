/-
# Holomorphic branches of log and root on simply connected domains

The classical route to the **fundamental normality test** (a family omitting `0, 1` is normal — the
three-value Montel theorem) lifts an omitting family through a tower of covering maps (`exp`, `z ↦ zⁿ`)
to the unit disk, where boundedness gives normality (`montel_subseq`). The lifts must be **holomorphic**.

mathlib provides *continuous* branches on simply connected domains (`exists_continuousOn_eqOn_exp_comp`,
`exists_continuousOn_pow_eq`, built on its covering-map lifting `existsUnique_continuousMap_lifts`). This
file upgrades them to **holomorphic** branches, via the local inverse of `exp` — the analytic input the
lifting tower needs.

New file (Montel/Julia lane — three-value Montel foundation). General lemmas; Mathlib only.
-/
import Mathlib

open Complex Set Filter Topology

namespace Bottcher

/-- **Holomorphic logarithm on a simply connected domain.** A holomorphic non-vanishing `f` on an open
simply connected `U` has a holomorphic branch of `log f`: some holomorphic `g` with `exp ∘ g = f`. -/
theorem exists_differentiableOn_exp_eq {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hU₀ : 0 ∉ f '' U) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ Set.EqOn (Complex.exp ∘ g) f U := by
  obtain ⟨g, hgc, hg⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUc hUo hf.continuousOn hU₀
  refine ⟨g, fun z₀ hz₀ => ?_, hg⟩
  have hne : Complex.exp (g z₀) ≠ 0 := Complex.exp_ne_zero _
  have hexp : HasStrictDerivAt Complex.exp (Complex.exp (g z₀)) (g z₀) :=
    Complex.hasStrictDerivAt_exp (g z₀)
  have hexpgz : Complex.exp (g z₀) = f z₀ := hg hz₀
  set e := hexp.localInverse Complex.exp (Complex.exp (g z₀)) (g z₀) hne with he_def
  have heinv : HasStrictDerivAt e (Complex.exp (g z₀))⁻¹ (Complex.exp (g z₀)) :=
    hexp.to_localInverse hne
  have hleft : ∀ᶠ w in 𝓝 (g z₀), e (Complex.exp w) = w := hexp.eventually_left_inverse hne
  have hgcont : ContinuousAt g z₀ := hgc.continuousAt (hUo.mem_nhds hz₀)
  have hgef : g =ᶠ[𝓝 z₀] fun z => e (f z) := by
    filter_upwards [hgcont.eventually hleft, hUo.mem_nhds hz₀] with z hz hzU
    have hfz : Complex.exp (g z) = f z := hg hzU
    show g z = e (f z)
    rw [← hfz]; exact hz.symm
  have hfd : HasDerivAt f (deriv f z₀) z₀ := (hf.differentiableAt (hUo.mem_nhds hz₀)).hasDerivAt
  have he2 : HasDerivAt e (Complex.exp (g z₀))⁻¹ (f z₀) := by rw [← hexpgz]; exact heinv.hasDerivAt
  have hcomp : HasDerivAt (fun z => e (f z)) ((Complex.exp (g z₀))⁻¹ * deriv f z₀) z₀ :=
    he2.comp z₀ hfd
  exact (hcomp.congr_of_eventuallyEq hgef).differentiableAt.differentiableWithinAt

/-- **Holomorphic `n`-th root on a simply connected domain.** A holomorphic non-vanishing `f` on an
open simply connected `U` has a holomorphic `n`-th root: some holomorphic `g` with `g ^ n = f` on `U`.
(Take `g = exp(log f / n)` with the holomorphic logarithm above.) -/
theorem exists_differentiableOn_pow_eq {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hU₀ : 0 ∉ f '' U) {n : ℕ} (hn : n ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, g z ^ n = f z := by
  obtain ⟨L, hL, hLf⟩ := exists_differentiableOn_exp_eq hUc hUo hf hU₀
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine ⟨fun z => Complex.exp (L z / n), Complex.differentiable_exp.comp_differentiableOn
    (hL.div_const _), fun z hz => ?_⟩
  rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ hnc]
  exact hLf hz

/-- **Holomorphic lift through a holomorphic covering.** If `μ` is a holomorphic local
biholomorphism (`HasStrictDerivAt μ (μ' w) w`, `μ' w ≠ 0` everywhere — the analytic shape of a
holomorphic covering map), then any **continuous** lift `g` of a **holomorphic** `f` through `μ`
(`μ ∘ g = f` on an open `U`) is itself **holomorphic**. This is the analytic glue of the lifting
tower toward three-value Montel: lifting an omitting-`{0,1}` family through the universal cover
`μ : 𝔻 → ℂ∖{0,1}` (which mathlib's `existsUnique_continuousMap_lifts` provides continuously) yields
**holomorphic** disk-valued lifts, to which `montel_subseq` / Marty apply. -/
theorem differentiableOn_of_continuousOn_lift {μ μ' : ℂ → ℂ}
    (hμ : ∀ w, HasStrictDerivAt μ (μ' w) w) (hμ' : ∀ w, μ' w ≠ 0)
    {g f : ℂ → ℂ} {U : Set ℂ} (hUo : IsOpen U)
    (hg : ContinuousOn g U) (hf : DifferentiableOn ℂ f U) (hcomp : Set.EqOn (μ ∘ g) f U) :
    DifferentiableOn ℂ g U := by
  intro z₀ hz₀
  have hexp : HasStrictDerivAt μ (μ' (g z₀)) (g z₀) := hμ (g z₀)
  have hne : μ' (g z₀) ≠ 0 := hμ' (g z₀)
  have hμgz : μ (g z₀) = f z₀ := hcomp hz₀
  set e := hexp.localInverse μ (μ' (g z₀)) (g z₀) hne with he_def
  have heinv : HasStrictDerivAt e (μ' (g z₀))⁻¹ (μ (g z₀)) := hexp.to_localInverse hne
  have hleft : ∀ᶠ w in 𝓝 (g z₀), e (μ w) = w := hexp.eventually_left_inverse hne
  have hgcont : ContinuousAt g z₀ := hg.continuousAt (hUo.mem_nhds hz₀)
  have hgef : g =ᶠ[𝓝 z₀] fun z => e (f z) := by
    filter_upwards [hgcont.eventually hleft, hUo.mem_nhds hz₀] with z hz hzU
    have hfz : μ (g z) = f z := hcomp hzU
    show g z = e (f z); rw [← hfz]; exact hz.symm
  have hfd : HasDerivAt f (deriv f z₀) z₀ := (hf.differentiableAt (hUo.mem_nhds hz₀)).hasDerivAt
  have he2 : HasDerivAt e (μ' (g z₀))⁻¹ (f z₀) := by rw [← hμgz]; exact heinv.hasDerivAt
  exact ((he2.comp z₀ hfd).congr_of_eventuallyEq hgef).differentiableAt.differentiableWithinAt

end Bottcher
