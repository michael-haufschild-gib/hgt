/-
# Relative basin Böttcher branch from an `ω`-primitive

The relative dendrite obstruction (`RelativeBranchFamily.false_of_global_basin_branch_analytic`) consumes a
basin Böttcher branch `β` on the basin sector — analytic, nonvanishing, with the Böttcher modulus
`‖β‖ = exp G_{c₁}` and carrying the relation `∑ᵢ aᵢ(z)·(β z)ⁱ = 0`, where `aᵢ = (Qᵢ)(·, φ_{c₂})` are the
continued relative coefficients. This file constructs that `β` from a **primitive of the Green
log-derivative** `ω = greenLogDeriv c` on the region — the relative analogue of
`GreenLogDeriv.exists_fullBottcherBranch_of_primitive`.

The branch `β = exp(F)` is built coefficient-agnostically by the already-banked
`exists_bottcherBranch_of_primitive`; only the **relation propagation** is redone with analytic
coefficients (`analyticOnNhd_relation_analytic` + the identity theorem on the preconnected region). So the
relative basin-branch input reduces to: a primitive `F` of `ω` on the (preconnected) basin region `V`, the
continued coefficients `aᵢ` analytic on `V`, and the relation holding on a far-field escape anchor `E ⊆ V`.
The primitive itself is supplied, in the connected case, by the project's Poincaré machinery
(`GreenLogDeriv.exists_primitive_glue_chain`) on a ball-chain through the basin.
-/
import GaloisForLFunctions.Bottcher.GreenLogDeriv

open Polynomial Filter Topology Set Metric Complex

namespace Bottcher

/-- The analytic-coefficient relation `z ↦ ∑_{i∈s} aᵢ(z)·(β z)ⁱ` is analytic where the `aᵢ` and `β` are. -/
theorem analyticOnNhd_relation_analytic {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {β : ℂ → ℂ} {V : Set ℂ}
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) V) (hβ : AnalyticOnNhd ℂ β V) :
    AnalyticOnNhd ℂ (fun z => ∑ i ∈ s, a i z * (β z) ^ i) V := by
  have heq : (fun z => ∑ i ∈ s, a i z * (β z) ^ i) = ∑ i ∈ s, (fun z => a i z * (β z) ^ i) := by
    ext z; rw [Finset.sum_apply]
  rw [heq]
  apply Finset.analyticOnNhd_sum
  intro i hi
  exact (ha i hi).mul (hβ.pow i)

/-- **Modulus branch satisfies the analytic relation (escape anchor) — relative form.** Mirror of
`exists_relationBranch_of_modulusBranch` with the polynomial coefficients `(P.coeff i)(z)` replaced by an
analytic family `aᵢ` (the continued `(Qᵢ)(·,φ_{c₂})`). Phase-normalize `β` to `β' = u·β` equal to
`bottcherCoord c` on `E`; the relation holds there, and by the identity theorem on the preconnected `V`
(coefficients `aᵢ` analytic on `V`), on all of `V`. -/
theorem exists_relativeRelationBranch_of_modulusBranch {c : ℂ} {V E : Set ℂ} {β : ℂ → ℂ}
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ}
    (hVc : IsPreconnected V) (hβan : AnalyticOnNhd ℂ β V)
    (hβ0 : ∀ z ∈ V, β z ≠ 0) (hβmod : ∀ z ∈ V, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) V)
    (hEV : E ⊆ V) (hEesc : E ⊆ escapeOpen c ∩ Complex.slitPlane) (hEo : IsOpen E)
    (hEc : IsPreconnected E) {e₀ : ℂ} (he₀ : e₀ ∈ E)
    (hrel : ∀ z ∈ E, ∑ i ∈ s, a i z * (bottcherCoord c z) ^ i = 0) :
    ∃ β' : ℂ → ℂ, AnalyticOnNhd ℂ β' V ∧ (∀ z ∈ V, β' z ≠ 0) ∧
      (∀ z ∈ V, ‖β' z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ V, ∑ i ∈ s, a i z * (β' z) ^ i = 0) := by
  have hgreen : ∀ z ∈ E, greenFunctionDyn c z = greenLimit c z := by
    intro z hz
    obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime (hEesc hz).1
    rw [greenFunctionDyn, if_neg (not_mem_filledJulia hc hz2)]
  have hbcan : AnalyticOnNhd ℂ (bottcherCoord c) E := (analyticOnNhd_bottcherCoord c).mono hEesc
  have hbc0 : ∀ z ∈ E, bottcherCoord c z ≠ 0 := fun z _ => bottcherCoord_ne_zero c z
  have hratioNorm : ∀ z ∈ E, ‖β z / bottcherCoord c z‖ = 1 := by
    intro z hz
    rw [norm_div, hβmod z (hEV hz), norm_bottcherCoord_eq_exp_green (hEesc hz), hgreen z hz,
      div_self (Real.exp_ne_zero _)]
  have hratioan : AnalyticOnNhd ℂ (fun z => β z / bottcherCoord c z) E :=
    fun z hz => (hβan z (hEV hz)).div (hbcan z hz) (hbc0 z hz)
  have hconstE := eqOn_const_of_norm_eq_one hEc hEo hratioan he₀ hratioNorm
  set u : ℂ := bottcherCoord c e₀ / β e₀ with hu
  have hβe0 : β e₀ ≠ 0 := hβ0 e₀ (hEV he₀)
  have hunorm : ‖u‖ = 1 := by
    rw [hu, norm_div, norm_bottcherCoord_eq_exp_green (hEesc he₀), hβmod e₀ (hEV he₀), hgreen e₀ he₀,
      div_self (Real.exp_ne_zero _)]
  have hune : u ≠ 0 := by intro h; rw [h, norm_zero] at hunorm; exact zero_ne_one hunorm
  refine ⟨fun z => u * β z, analyticOnNhd_const.mul hβan, fun z hz => mul_ne_zero hune (hβ0 z hz),
    fun z hz => by rw [norm_mul, hunorm, one_mul]; exact hβmod z hz, ?_⟩
  have hβ'E : ∀ z ∈ E, u * β z = bottcherCoord c z := by
    intro z hz
    have h1 := hconstE z hz
    have hcross : β z * bottcherCoord c e₀ = β e₀ * bottcherCoord c z :=
      (div_eq_div_iff (hbc0 z hz) (hbc0 e₀ he₀)).mp h1
    rw [hu, div_mul_eq_mul_div, div_eq_iff hβe0]
    linear_combination hcross
  have hrelE : ∀ z ∈ E, ∑ i ∈ s, a i z * (u * β z) ^ i = 0 := by
    intro z hz; rw [hβ'E z hz]; exact hrel z hz
  have hrelan : AnalyticOnNhd ℂ (fun z => ∑ i ∈ s, a i z * (u * β z) ^ i) V :=
    analyticOnNhd_relation_analytic ha (analyticOnNhd_const.mul hβan)
  have hev : (fun z => ∑ i ∈ s, a i z * (u * β z) ^ i) =ᶠ[𝓝 e₀] 0 := by
    filter_upwards [hEo.mem_nhds he₀] with z hz; exact hrelE z hz
  exact fun z hz => (hrelan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hVc
    (hEV he₀) hev) hz

/-- **Relative full Böttcher branch from an `ω`-primitive.** Given a primitive `F` of `ω = greenLogDeriv c`
on a preconnected basin region `V ⊆ Ω_c`, with the continued coefficient family `aᵢ` analytic on `V` and the
relation `∑ aᵢ·(φ_c)ⁱ = 0` holding on an escape anchor `E ⊆ V`, there is a branch `β` on `V`: analytic,
nowhere zero, with the Böttcher modulus `‖β‖ = exp G_c`, satisfying the analytic relation on all of `V`.
The relative analogue of `exists_fullBottcherBranch_of_primitive` — the `β` is built coefficient-agnostically
(`exists_bottcherBranch_of_primitive`) and the relation propagated with analytic coefficients. This reduces
the basin-branch input of `false_of_global_basin_branch_analytic` to a *primitive of `ω` on `V`*. -/
theorem exists_relativeBranch_of_primitive {c : ℂ} {V E : Set ℂ} {a : ℕ → ℂ → ℂ} {s : Finset ℕ}
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVb : V ⊆ (filledJulia c)ᶜ)
    {F : ℂ → ℂ} (hF : ∀ z ∈ V, HasDerivAt F (greenLogDeriv c z) z)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) V)
    (hEV : E ⊆ V) (hEesc : E ⊆ escapeOpen c ∩ Complex.slitPlane) (hEo : IsOpen E)
    (hEc : IsPreconnected E) {e₀ : ℂ} (he₀ : e₀ ∈ E)
    (hrel : ∀ z ∈ E, ∑ i ∈ s, a i z * (bottcherCoord c z) ^ i = 0) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β V ∧ (∀ z ∈ V, β z ≠ 0) ∧
      (∀ z ∈ V, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ V, ∑ i ∈ s, a i z * (β z) ^ i = 0) := by
  obtain ⟨β, hβan, hβ0, hβmod⟩ := exists_bottcherBranch_of_primitive hVo hVc hVb hF (hEV he₀)
  exact exists_relativeRelationBranch_of_modulusBranch hVc hβan hβ0 hβmod ha hEV hEesc hEo hEc he₀ hrel

end Bottcher
