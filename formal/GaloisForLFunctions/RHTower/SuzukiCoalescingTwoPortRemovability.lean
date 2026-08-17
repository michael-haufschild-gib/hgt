import GaloisForLFunctions.RHTower.SuzukiCoalescingHalfPlaneUniqueness

/-!
# Removability and zero sharing for the two-port limit

The two-port coordinate `i/z - H/G` is not holomorphic where `G` vanishes, so the assertion that it
extends across those zeros is not a statement about the quotient at all.  It is a statement about
the *product*: the combination

`Φ = R·G - (i/z)·G + H`

is holomorphic on the whole half-plane whenever the limit `R` is, it vanishes off the discrete zero
set of `G`, and therefore vanishes identically.  Rewriting the identity gives

`H = G · (i/z - R)`,

so the analytic order of `H` at a zero of `G` is at least that of `G` — the zero-sharing claim —
with no removability argument and no multiplicity bookkeeping.

Strict positivity of the real part is separate and comes from the minimum principle: every member
of the family has nonnegative real part, hence so does the limit, and one positive value upgrades
it everywhere.
-/

open Complex Metric Set Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- **Zero sharing.**  If `H` factors through `G` by an analytic cofactor, its order dominates. -/
theorem analyticOrderAt_le_of_eq_mul {G H F : ℂ → ℂ} {z₀ : ℂ}
    (hG : AnalyticAt ℂ G z₀) (hF : AnalyticAt ℂ F z₀)
    (hHeq : ∀ᶠ z in 𝓝 z₀, H z = G z * F z) :
    analyticOrderAt G z₀ ≤ analyticOrderAt H z₀ := by
  have hcongr : analyticOrderAt H z₀ = analyticOrderAt (G * F) z₀ :=
    analyticOrderAt_congr (by filter_upwards [hHeq] with z hz using hz)
  rw [hcongr, analyticOrderAt_mul hG hF]
  exact le_self_add

/-- **The entire combination of the two-port limit.**  Off the zeros of `G` the limit is the
two-port coordinate; the product identity then holds everywhere by the identity theorem. -/
theorem twoPort_product_identity {G H R : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hUopen : IsOpen U) (hUc : IsPreconnected U)
    (hRdiff : DifferentiableOn ℂ R U) (hGdiff : DifferentiableOn ℂ G U)
    (hHdiff : DifferentiableOn ℂ H U)
    (hzero : ∀ z ∈ U, z ≠ 0)
    (hz₀ : z₀ ∈ U)
    (hlocal : ∃ᶠ z in 𝓝[≠] z₀, R z = Complex.I / z - H z / G z ∧ G z ≠ 0) :
    ∀ z ∈ U, H z = G z * (Complex.I / z - R z) := by
  set Φ : ℂ → ℂ := fun z => H z - G z * (Complex.I / z - R z) with hΦdef
  have hinv : DifferentiableOn ℂ (fun z : ℂ => Complex.I / z) U := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (differentiableAt_const _).div differentiableAt_id (hzero z hz)
  have hΦdiff : DifferentiableOn ℂ Φ U := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    have hRz : DifferentiableAt ℂ R z := (hRdiff z hz).differentiableAt (hUopen.mem_nhds hz)
    have hGz : DifferentiableAt ℂ G z := (hGdiff z hz).differentiableAt (hUopen.mem_nhds hz)
    have hHz : DifferentiableAt ℂ H z := (hHdiff z hz).differentiableAt (hUopen.mem_nhds hz)
    have hIz : DifferentiableAt ℂ (fun w : ℂ => Complex.I / w) z :=
      (hinv z hz).differentiableAt (hUopen.mem_nhds hz)
    exact hHz.sub (hGz.mul (hIz.sub hRz))
  have hana : AnalyticOnNhd ℂ Φ U := hΦdiff.analyticOnNhd hUopen
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, Φ z = 0 := by
    refine hlocal.mono fun z hz => ?_
    obtain ⟨heq, hGne⟩ := hz
    rw [hΦdef]
    simp only
    rw [heq]
    field_simp
    ring
  have hΦzero : EqOn Φ 0 U :=
    hana.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hz₀ hfreq
  intro z hz
  have := hΦzero hz
  rw [hΦdef] at this
  simp only [Pi.zero_apply] at this
  linear_combination this

/-- **Theorem H's zero sharing.**  Every zero of the two-port denominator is a zero of the
numerator of at least the same order. -/
theorem twoPort_order_le {G H R : ℂ → ℂ} {U : Set ℂ} {z₀ z₁ : ℂ}
    (hUopen : IsOpen U) (hUc : IsPreconnected U)
    (hRdiff : DifferentiableOn ℂ R U) (hGdiff : DifferentiableOn ℂ G U)
    (hHdiff : DifferentiableOn ℂ H U)
    (hzero : ∀ z ∈ U, z ≠ 0)
    (hz₀ : z₀ ∈ U)
    (hlocal : ∃ᶠ z in 𝓝[≠] z₀, R z = Complex.I / z - H z / G z ∧ G z ≠ 0)
    (hz₁ : z₁ ∈ U) :
    analyticOrderAt G z₁ ≤ analyticOrderAt H z₁ := by
  have hprod := twoPort_product_identity hUopen hUc hRdiff hGdiff hHdiff hzero hz₀ hlocal
  have hGan : AnalyticAt ℂ G z₁ :=
    (hGdiff.analyticOnNhd hUopen) z₁ hz₁
  have hRan : AnalyticAt ℂ R z₁ :=
    (hRdiff.analyticOnNhd hUopen) z₁ hz₁
  have hIan : AnalyticAt ℂ (fun w : ℂ => Complex.I / w) z₁ := by
    have hd : DifferentiableOn ℂ (fun w : ℂ => Complex.I / w) U := by
      intro z hz
      refine DifferentiableAt.differentiableWithinAt ?_
      exact (differentiableAt_const _).div differentiableAt_id (hzero z hz)
    exact (hd.analyticOnNhd hUopen) z₁ hz₁
  refine analyticOrderAt_le_of_eq_mul hGan (hIan.sub hRan) ?_
  filter_upwards [hUopen.mem_nhds hz₁] with z hz
  exact hprod z hz

end RHTower
