/-
# The global logarithmic derivative `ω = φ_c'/φ_c` on the basin (Böttcher primitive setup)

The single-valued Böttcher coordinate `φ_c` on the (annular, π₁ = ℤ) connected basin is the obstruction
that gates the connected-case transcendence `hGtr` (and the dyadic lift `hDisc`). `log φ_c` is multivalued
(period `2πi` around `K_c`), but its **derivative** `φ_c'/φ_c = 2·∂G_c` is single-valued and holomorphic on
the whole basin — because `G_c` is harmonic there (`BasinBranching.harmonicOnNhd_greenLimit_basin`) and the
Wirtinger `∂`-derivative of a harmonic function is holomorphic
(`HarmonicAt.differentiableAt_complex_partial`).

This file constructs that global `ω` and records it is **conservative** (`DifferentiableOn.isConservativeOn`).
The single missing analytic step to single-valued `φ_c` on a *simply-connected* basin region `V` is then the
**Poincaré lemma** `IsConservativeOn ω V + IsSimplyConnected V ⟹ IsExactOn ω V`: a primitive `F` (with
`F' = ω`, hence `Re F = G_c` up to constant — the harmonic conjugate, `log φ_c`, so `φ_c = exp F`). Mathlib
provides exactness only on balls (`DifferentiableOn.isExactOn_ball`) and on `ℂ`; the simply-connected case is
the genuine remaining frontier brick. With it, `β := exp F` on a simply-connected basin neighbourhood of a
dendrite Julia point supplies both `hβmod` (`‖β‖ = exp G_c`) and — anchored to `escapeOpen` where it equals
`φ_c` — `hβrel`, feeding `ConnectedTranscendence.dendrite_branch_limit`.
-/
import GaloisForLFunctions.Bottcher.BasinBranching
import GaloisForLFunctions.Bottcher.BottcherCoord
import GaloisForLFunctions.Bottcher.PeriodicPoints
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import GaloisForLFunctions.Bottcher.ChainGlue

open Complex Set Topology Filter

namespace Bottcher

/-- The **logarithmic derivative** `ω = φ_c'/φ_c = 2·∂G_c` — the Wirtinger `∂`-derivative of the Green's
function, single-valued on the basin even though `log φ_c` is not. -/
noncomputable def greenLogDeriv (c : ℂ) : ℂ → ℂ :=
  fun z => fderiv ℝ (greenLimit c) z 1 - Complex.I * fderiv ℝ (greenLimit c) z Complex.I

/-- **`ω` is holomorphic on the whole basin.** At each basin point `G_c` is harmonic
(`harmonicOnNhd_greenLimit_basin`), and the Wirtinger `∂`-derivative of a harmonic function is complex
differentiable (`HarmonicAt.differentiableAt_complex_partial`). -/
theorem differentiableOn_greenLogDeriv (c : ℂ) :
    DifferentiableOn ℂ (greenLogDeriv c) (filledJulia c)ᶜ := by
  intro z hz
  have hh := harmonicOnNhd_greenLimit_basin c z hz
  exact (HarmonicAt.differentiableAt_complex_partial hh).differentiableWithinAt

/-- **`ω` is conservative on the basin** (`DifferentiableOn.isConservativeOn`): all rectangle integrals
vanish. On any simply-connected basin region this upgrades — via the Poincaré lemma — to exactness, i.e. a
single-valued primitive `F = log φ_c` with `Re F = G_c`. -/
theorem isConservativeOn_greenLogDeriv (c : ℂ) :
    IsConservativeOn (greenLogDeriv c) (filledJulia c)ᶜ :=
  (differentiableOn_greenLogDeriv c).isConservativeOn

/-- **A real function with zero derivative on an open preconnected set is constant there.** The level set is
relatively clopen (closed by continuity; open because zero `fderiv` is constant on each ball), so
preconnectedness forces it to be everything. -/
theorem eqOn_const_of_hasFDerivAt_zero {h : ℂ → ℝ} {V : Set ℂ} (hVo : IsOpen V)
    (hVc : IsPreconnected V) (hd : ∀ z ∈ V, HasFDerivAt h (0 : ℂ →L[ℝ] ℝ) z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ V) : ∀ z ∈ V, h z = h z₀ := by
  classical
  have hpre : PreconnectedSpace ↥V := (isPreconnected_iff_preconnectedSpace).mp hVc
  have hcont : Continuous (fun x : ↥V => h x.val) :=
    ContinuousOn.restrict (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
  set S : Set ↥V := {x | h x.val = h z₀} with hSdef
  have hSclosed : IsClosed S := isClosed_eq hcont continuous_const
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hVo x.val x.2
    have hconstBall : ∀ y ∈ Metric.ball x.val r, h y = h x.val := by
      intro y hy
      refine Convex.is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) (convex_ball _ _) ?_ ?_ hy
        (Metric.mem_ball_self hr)
      · exact fun z hz => (hd z (hball hz)).differentiableAt.differentiableWithinAt
      · intro z hz
        rw [(hd z (hball hz)).hasFDerivWithinAt.fderivWithin (Metric.isOpen_ball.uniqueDiffWithinAt hz)]
    have hsub : (fun y : ↥V => y.val) ⁻¹' (Metric.ball x.val r) ⊆ S := by
      intro y hy; show h y.val = h z₀; rw [hconstBall y.val hy, hx]
    apply Filter.mem_of_superset _ hsub
    exact (continuous_subtype_val.continuousAt).preimage_mem_nhds (Metric.ball_mem_nhds _ hr)
  have := isPreconnected_univ.subset_isClopen ⟨hSclosed, hSopen⟩ ⟨⟨z₀, hz₀⟩, mem_univ _, rfl⟩
  intro z hz; exact this (mem_univ (⟨z, hz⟩ : ↥V))

/-- **Harmonic-conjugate identity.** A holomorphic primitive `F` of `ω = greenLogDeriv c` on a preconnected
basin set has `Re F - G_c` constant. Cauchy–Riemann: `F' = ω = 2·∂G_c` makes `∇(Re F) = ∇G_c`. So once the
Poincaré lemma supplies `F` with `F' = ω` on a simply-connected basin region (anchored so the constant is
`0` via a deep-exterior overlap where `F = log φ_c`), `Re F = G_c`, hence `‖exp F‖ = exp(Re F) = exp G_c` —
the modulus datum `hβmod` for `β := exp F`. This is the bridge from "primitive of `ω`" to "the Böttcher
branch". -/
theorem re_primitive_sub_green_const {c : ℂ} {V : Set ℂ} (hVo : IsOpen V) (hVc : IsPreconnected V)
    {F : ℂ → ℂ} (hF : ∀ z ∈ V, HasDerivAt F (greenLogDeriv c z) z)
    (hG : ∀ z ∈ V, DifferentiableAt ℝ (greenLimit c) z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ V) :
    ∀ z ∈ V, (F z).re - greenLimit c z = (F z₀).re - greenLimit c z₀ := by
  have key : ∀ z ∈ V, HasFDerivAt (fun z => (F z).re - greenLimit c z) (0 : ℂ →L[ℝ] ℝ) z := by
    intro z hz
    have hReF : HasFDerivAt (fun z => (F z).re)
        (Complex.reCLM.comp (((1 : ℂ →L[ℂ] ℂ).smulRight (greenLogDeriv c z)).restrictScalars ℝ)) z :=
      Complex.reCLM.hasFDerivAt.comp z ((hF z hz).hasFDerivAt.restrictScalars ℝ)
    have hGF : HasFDerivAt (greenLimit c) (fderiv ℝ (greenLimit c) z) z := (hG z hz).hasFDerivAt
    have hsub := hReF.sub hGF
    have hzero : Complex.reCLM.comp (((1 : ℂ →L[ℂ] ℂ).smulRight (greenLogDeriv c z)).restrictScalars ℝ)
        - fderiv ℝ (greenLimit c) z = 0 := by
      ext v
      have hLin : fderiv ℝ (greenLimit c) z v
          = v.re * fderiv ℝ (greenLimit c) z 1 + v.im * fderiv ℝ (greenLimit c) z Complex.I := by
        conv_lhs => rw [show v = v.re • (1:ℂ) + v.im • Complex.I from by
          rw [Complex.real_smul, Complex.real_smul, mul_one]; exact (Complex.re_add_im v).symm]
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
        one_apply_eq_self, Complex.reCLM_apply, _root_.zero_apply, hLin,
        greenLogDeriv]
      rw [show v • ((fderiv ℝ (greenLimit c) z 1 : ℂ)
            - Complex.I * (fderiv ℝ (greenLimit c) z Complex.I : ℂ))
          = v * ((fderiv ℝ (greenLimit c) z 1 : ℂ)
            - Complex.I * (fderiv ℝ (greenLimit c) z Complex.I : ℂ)) from rfl]
      simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    rwa [hzero] at hsub
  exact eqOn_const_of_hasFDerivAt_zero hVo hVc key hz₀

/-- **The Böttcher branch from a primitive of `ω` (keystone).** Given a primitive `F` of `ω = greenLogDeriv c`
on a preconnected basin region `V` (the output of the Poincaré lemma on a simply-connected `V`), the
normalized exponential `β := exp(F − k)` (with `k := Re(F z₁) − G_c(z₁)`) is analytic, nowhere zero, and
carries the **exact Böttcher modulus** `‖β‖ = exp(greenFunctionDyn c)` — the datum `hβmod` of
`false_of_basin_branch_dendrite`. Proof: `re_primitive_sub_green_const` gives `Re F − G_c ≡ k`, so
`‖β‖ = exp(Re F − k) = exp G_c`. The ONLY remaining input to the whole connected/disconnected analytic core
is the primitive `F` itself — i.e. the Poincaré lemma `IsConservativeOn ω + IsSimplyConnected V ⟹ IsExactOn`,
an open WIP in mathlib (`CurveIntegral`, issue #24019). Everything downstream of it is now verified. -/
theorem exists_bottcherBranch_of_primitive {c : ℂ} {V : Set ℂ} (hVo : IsOpen V)
    (hVc : IsPreconnected V) (hVb : V ⊆ (filledJulia c)ᶜ) {F : ℂ → ℂ}
    (hF : ∀ z ∈ V, HasDerivAt F (greenLogDeriv c z) z) {z₁ : ℂ} (hz₁ : z₁ ∈ V) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β V ∧ (∀ z ∈ V, β z ≠ 0) ∧
      (∀ z ∈ V, ‖β z‖ = Real.exp (greenFunctionDyn c z)) := by
  have hG : ∀ z ∈ V, DifferentiableAt ℝ (greenLimit c) z := fun z hz =>
    (harmonicOnNhd_greenLimit_basin c z (hVb hz)).1.differentiableAt (by norm_num)
  have hFdiff : DifferentiableOn ℂ F V :=
    fun z hz => ((hF z hz).differentiableAt).differentiableWithinAt
  have hFan : AnalyticOnNhd ℂ F V := hFdiff.analyticOnNhd hVo
  set k : ℝ := (F z₁).re - greenLimit c z₁ with hk
  have hre := re_primitive_sub_green_const hVo hVc hF hG hz₁
  refine ⟨fun z => Complex.exp (F z - (k : ℂ)), (hFan.sub analyticOnNhd_const).cexp,
    fun z _ => Complex.exp_ne_zero _, ?_⟩
  intro z hz
  rw [Complex.norm_exp, Complex.sub_re, Complex.ofReal_re]
  have h1 : (F z).re - k = greenLimit c z := by have h2 := hre z hz; rw [hk]; linarith
  rw [h1, greenFunctionDyn, if_neg (hVb hz)]

/-- Analytic with unit modulus on a connected open set is constant (the `EqOn` form of
`norm_eq_one_of_open`). -/
theorem eqOn_const_of_norm_eq_one {h : ℂ → ℂ} {U : Set ℂ} (hUc : IsPreconnected U) (hUo : IsOpen U)
    (hh : AnalyticOnNhd ℂ h U) {v : ℂ} (hvU : v ∈ U) (hnorm : ∀ z ∈ U, ‖h z‖ = 1) :
    ∀ z ∈ U, h z = h v := by
  have hlm : IsLocalMax (norm ∘ h) v := by
    filter_upwards [hUo.mem_nhds hvU] with z hz
    show ‖h z‖ ≤ ‖h v‖; rw [hnorm z hz, hnorm v hvU]
  have hdiff : ∀ᶠ z in 𝓝 v, DifferentiableAt ℂ h z := by
    filter_upwards [hUo.mem_nhds hvU] with z hz; exact (hh z hz).differentiableAt
  have hconst : ∀ᶠ z in 𝓝 v, h z = h v := Complex.eventually_eq_of_isLocalMax_norm hdiff hlm
  exact fun z hz => (hh.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc hvU hconst) hz

/-- The relation function `z ↦ ∑ᵢ (P.coeff i)(z)·(β z)ⁱ` is analytic where `β` is (finite sum of products of
polynomial-evals — entire — with powers of the analytic `β`). -/
theorem analyticOnNhd_relation {β : ℂ → ℂ} {V : Set ℂ} (hβ : AnalyticOnNhd ℂ β V)
    (P : Polynomial (Polynomial ℂ)) :
    AnalyticOnNhd ℂ (fun z => ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i) V := by
  have heq : (fun z => ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i)
      = ∑ i ∈ P.support, (fun z => (P.coeff i).aeval z * (β z) ^ i) := by
    ext z; rw [Finset.sum_apply]
  rw [heq]
  apply Finset.analyticOnNhd_sum
  intro i _
  refine AnalyticOnNhd.mul ?_ (hβ.pow i)
  exact ((Polynomial.differentiable_aeval (P.coeff i)).differentiableOn.analyticOnNhd
    isOpen_univ).mono (subset_univ V)

/-- **The modulus branch satisfies the relation (escape anchor).** A modulus branch `β` (`‖β‖ = exp G_c`,
analytic, nonvanishing on a preconnected `V`) meeting the escape region `E ⊆ V ∩ escapeOpen ∩ slitPlane`
(where the hypothetical relation `P(z, φ_c)=0` holds) phase-normalizes to `β' = u·β` (`‖u‖ = 1`) equal to
`bottcherCoord c` on `E` — on `E` both have modulus `exp G_c`, so their ratio is a unit constant
(`eqOn_const_of_norm_eq_one`). Hence `β'` satisfies the relation on `E`, and by the identity theorem on the
connected `V`, on all of `V`, while keeping the modulus. With `exists_bottcherBranch_of_primitive` this gives
the FULL `β` datum (`hβmod` + `hβrel`) of `false_of_basin_branch_dendrite` from the `ω`-primitive. -/
theorem exists_relationBranch_of_modulusBranch {c : ℂ} {V E : Set ℂ} {β : ℂ → ℂ}
    (hVc : IsPreconnected V) (hβan : AnalyticOnNhd ℂ β V)
    (hβ0 : ∀ z ∈ V, β z ≠ 0) (hβmod : ∀ z ∈ V, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hEV : E ⊆ V) (hEesc : E ⊆ escapeOpen c ∩ Complex.slitPlane) (hEo : IsOpen E)
    (hEc : IsPreconnected E) {e₀ : ℂ} (he₀ : e₀ ∈ E)
    (P : Polynomial (Polynomial ℂ))
    (hrel : ∀ z ∈ E, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) :
    ∃ β' : ℂ → ℂ, AnalyticOnNhd ℂ β' V ∧ (∀ z ∈ V, β' z ≠ 0) ∧
      (∀ z ∈ V, ‖β' z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ V, ∑ i ∈ P.support, (P.coeff i).aeval z * (β' z) ^ i = 0) := by
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
  have hrelE : ∀ z ∈ E, ∑ i ∈ P.support, (P.coeff i).aeval z * (u * β z) ^ i = 0 := by
    intro z hz; rw [hβ'E z hz]; exact hrel z hz
  have hrelan : AnalyticOnNhd ℂ (fun z => ∑ i ∈ P.support, (P.coeff i).aeval z * (u * β z) ^ i) V :=
    analyticOnNhd_relation (analyticOnNhd_const.mul hβan) P
  have hev : (fun z => ∑ i ∈ P.support, (P.coeff i).aeval z * (u * β z) ^ i) =ᶠ[𝓝 e₀] 0 := by
    filter_upwards [hEo.mem_nhds he₀] with z hz; exact hrelE z hz
  exact fun z hz => (hrelan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hVc
    (hEV he₀) hev) hz

/-- **Full Böttcher branch from an `ω`-primitive (connected-case keystone).** Given a primitive `F` of
`ω = greenLogDeriv c` on a preconnected basin region `V` meeting the escape region
`E ⊆ V ∩ escapeOpen ∩ slitPlane` (nonempty, open, connected) where the hypothetical relation
`P(z, bottcherCoord c z) = 0` holds, there is a branch `β` on `V` that is analytic, nowhere zero, has the
exact Böttcher modulus `‖β‖ = exp(G_c)`, AND satisfies the algebraic relation `P(z, β z) = 0`. This is the
complete `(hβmod, hβrel)` datum that `false_of_basin_branch_dendrite` / `dendrite_branch_limit` consume —
produced solely from the primitive `F` (`exists_bottcherBranch_of_primitive` + the escape-anchor
`exists_relationBranch_of_modulusBranch`). The SINGLE remaining input to close the connected case is therefore
the primitive itself, i.e. the **Poincaré lemma** `IsConservativeOn ω + IsSimplyConnected V ⟹ IsExactOn ω V`,
an open WIP in mathlib (`CurveIntegral`, issue #24019; the full Riemann mapping theorem is likewise a `TODO`
in `RiemannMapping.lean`). `hDisc` reuses the same `ω`-primitive on the 2ⁿ-cover. -/
theorem exists_fullBottcherBranch_of_primitive {c : ℂ} {V E : Set ℂ}
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVb : V ⊆ (filledJulia c)ᶜ)
    {F : ℂ → ℂ} (hF : ∀ z ∈ V, HasDerivAt F (greenLogDeriv c z) z)
    (hEV : E ⊆ V) (hEesc : E ⊆ escapeOpen c ∩ Complex.slitPlane) (hEo : IsOpen E)
    (hEc : IsPreconnected E) {e₀ : ℂ} (he₀ : e₀ ∈ E)
    (P : Polynomial (Polynomial ℂ))
    (hrel : ∀ z ∈ E, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β V ∧ (∀ z ∈ V, β z ≠ 0) ∧
      (∀ z ∈ V, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ V, ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i = 0) := by
  obtain ⟨β, hβan, hβ0, hβmod⟩ := exists_bottcherBranch_of_primitive hVo hVc hVb hF (hEV he₀)
  exact exists_relationBranch_of_modulusBranch hVc hβan hβ0 hβmod hEV hEesc hEo hEc he₀ P hrel

/-- **Two primitives of the same form differ by a constant.** If `g₁` and `g₂` both have derivative `f` on a
preconnected open `V`, then `g₁ − g₂` is constant on `V`. The consistency brick for assembling local
primitives (each from mathlib's `DifferentiableOn.isExactOn_ball`) into a global one — the additive analogue
of the green-conjugate cocycle, and the gluing heart of the Poincaré lemma (the remaining frontier input). -/
theorem primitive_sub_const {f g₁ g₂ : ℂ → ℂ} {V : Set ℂ} (hVo : IsOpen V) (hVc : IsPreconnected V)
    (h₁ : ∀ z ∈ V, HasDerivAt g₁ (f z) z) (h₂ : ∀ z ∈ V, HasDerivAt g₂ (f z) z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ V) : ∀ z ∈ V, g₁ z - g₂ z = g₁ z₀ - g₂ z₀ := by
  classical
  have hpre : PreconnectedSpace ↥V := (isPreconnected_iff_preconnectedSpace).mp hVc
  set h : ℂ → ℂ := fun z => g₁ z - g₂ z with hh
  have hderiv : ∀ z ∈ V, HasDerivAt h 0 z := by
    intro z hz
    simpa only [hh, Pi.sub_apply, sub_self] using! (h₁ z hz).sub (h₂ z hz)
  have hcont : Continuous (fun x : ↥V => h x.val) :=
    ContinuousOn.restrict (fun z hz => (hderiv z hz).continuousAt.continuousWithinAt)
  set S : Set ↥V := {x | h x.val = h z₀} with hSdef
  have hSclosed : IsClosed S := isClosed_eq hcont continuous_const
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hVo x.val x.2
    have hconstBall : ∀ y ∈ Metric.ball x.val r, h y = h x.val := by
      intro y hy
      refine Convex.is_const_of_fderivWithin_eq_zero (𝕜 := ℂ) (convex_ball _ _) ?_ ?_ hy
        (Metric.mem_ball_self hr)
      · exact fun z hz => (hderiv z (hball hz)).differentiableAt.differentiableWithinAt
      · intro z hz
        have hfd : HasFDerivAt h (0 : ℂ →L[ℂ] ℂ) z := by simpa using (hderiv z (hball hz)).hasFDerivAt
        rw [hfd.hasFDerivWithinAt.fderivWithin (Metric.isOpen_ball.uniqueDiffWithinAt hz)]
    have hsub : (fun y : ↥V => y.val) ⁻¹' (Metric.ball x.val r) ⊆ S := by
      intro y hy; show h y.val = h z₀; rw [hconstBall y.val hy, hx]
    apply Filter.mem_of_superset _ hsub
    exact (continuous_subtype_val.continuousAt).preimage_mem_nhds (Metric.ball_mem_nhds _ hr)
  have := isPreconnected_univ.subset_isClopen ⟨hSclosed, hSopen⟩ ⟨⟨z₀, hz₀⟩, mem_univ _, rfl⟩
  intro z hz; exact this (mem_univ (⟨z, hz⟩ : ↥V))

/-- **Atomic glue of two primitives (H¹-vanishing step).** Primitives `gU`, `gW` of the same form `f` on
opens `U`, `W` with connected nonempty overlap glue — after a constant shift on `W` (the overlap difference
is constant by `primitive_sub_const`) — to a single primitive `G` on `U ∪ W`. Iterating this along a chain
of balls (each carrying a primitive by mathlib's `Convex.exists_forall_hasDerivWithinAt` /
`DifferentiableOn.isExactOn_ball`) assembles the primitive on any chain-coverable region — the constructive
core of the Poincaré lemma on the current library. -/
theorem exists_primitive_glue {f gU gW : ℂ → ℂ} {U W : Set ℂ} (hUo : IsOpen U) (hWo : IsOpen W)
    (hUW : IsConnected (U ∩ W))
    (hgU : ∀ z ∈ U, HasDerivAt gU (f z) z) (hgW : ∀ z ∈ W, HasDerivAt gW (f z) z) :
    ∃ G : ℂ → ℂ, ∀ z ∈ U ∪ W, HasDerivAt G (f z) z := by
  classical
  obtain ⟨w₀, hw₀⟩ := hUW.nonempty
  have hconst : ∀ z ∈ U ∩ W, gU z - gW z = gU w₀ - gW w₀ :=
    primitive_sub_const (hUo.inter hWo) hUW.isPreconnected
      (fun z hz => hgU z hz.1) (fun z hz => hgW z hz.2) hw₀
  set c : ℂ := gU w₀ - gW w₀ with hc
  set G : ℂ → ℂ := fun z => if z ∈ U then gU z else gW z + c with hG
  have hGU : ∀ z ∈ U, G z = gU z := fun z hz => by simp [hG, hz]
  have hGW : ∀ z ∈ W, G z = gW z + c := by
    intro z hz
    by_cases hzU : z ∈ U
    · simp only [hG, if_pos hzU]
      have h := hconst z ⟨hzU, hz⟩; linear_combination h
    · simp [hG, hzU]
  refine ⟨G, fun z hz => ?_⟩
  rcases hz with hzU | hzW
  · have hee : G =ᶠ[𝓝 z] gU := by filter_upwards [hUo.mem_nhds hzU] with y hy using hGU y hy
    exact (hgU z hzU).congr_of_eventuallyEq hee
  · have hee : G =ᶠ[𝓝 z] (fun y => gW y + c) := by
      filter_upwards [hWo.mem_nhds hzW] with y hy using hGW y hy
    exact ((hgW z hzW).add_const c).congr_of_eventuallyEq hee

/-- **Chain assembly of primitives (Poincaré on a chain-coverable region).** Local primitives `g i` of `f`
on opens `U i`, with each prefix-union meeting `U (i+1)` in a connected overlap, glue to a single primitive
on `⋃_{j ≤ k} U j`. Iterates `exists_primitive_glue`. With each `U i` a ball in the basin (where `ω` is
holomorphic, so `DifferentiableOn.isExactOn_ball` gives the local primitive), this produces a primitive of
`ω` on any chain-coverable basin region — which feeds `exists_fullBottcherBranch_of_primitive`. The remaining
geometric input is a ball-chain from `escapeOpen` toward a Julia point with connected prefix-overlaps. -/
theorem exists_primitive_glue_chain {f : ℂ → ℂ} (U : ℕ → Set ℂ) (g : ℕ → ℂ → ℂ)
    (hUo : ∀ i, IsOpen (U i))
    (hg : ∀ i, ∀ z ∈ U i, HasDerivAt (g i) (f z) z)
    (hconn : ∀ i, IsConnected ((⋃ j ∈ Finset.range (i + 1), U j) ∩ U (i + 1)))
    (k : ℕ) :
    ∃ G : ℂ → ℂ, ∀ z ∈ (⋃ j ∈ Finset.range (k + 1), U j), HasDerivAt G (f z) z :=
  exists_glue_chain (P := fun G V => ∀ z ∈ V, HasDerivAt G (f z) z)
    U g hUo hg (fun hV hW hc pf ph => exists_primitive_glue hV hW hc pf ph) hconn k

/-- **Modulus spread via the harmonic identity theorem.** If `g` is analytic and nonvanishing on a
preconnected basin region `U`, and `‖g‖ = exp(G_c)` on a nonempty open subset `C ⊆ U`, then
`‖g‖ = exp(G_c)` on ALL of `U`. (`log‖g‖ − G_c` is harmonic — `AnalyticAt.harmonicAt_log_norm` and
`harmonicOnNhd_greenLimit_basin` — hence real-analytic by `HarmonicAt.analyticAt`; it vanishes on the open
`C`, so by the identity theorem it vanishes on the connected `U`.) This is the 2-D propagation that lets a
primitive built only on a small chain-reached region near a Julia point spread the Böttcher modulus across
the whole basin-neighbourhood — sidestepping a 2-D simply-connected primitive entirely. -/
theorem norm_eq_exp_green_of_eqOn_open {c : ℂ} {g : ℂ → ℂ} {U C : Set ℂ}
    (hUc : IsPreconnected U) (hUb : U ⊆ (filledJulia c)ᶜ)
    (hgan : AnalyticOnNhd ℂ g U) (hg0 : ∀ z ∈ U, g z ≠ 0)
    (hCo : IsOpen C) (hCsub : C ⊆ U) {z₁ : ℂ} (hz₁ : z₁ ∈ C)
    (hC : ∀ z ∈ C, ‖g z‖ = Real.exp (greenLimit c z)) :
    ∀ z ∈ U, ‖g z‖ = Real.exp (greenLimit c z) := by
  set u : ℂ → ℝ := fun z => Real.log ‖g z‖ - greenLimit c z with hu
  have huan : AnalyticOnNhd ℝ u U := by
    intro z hz
    exact HarmonicAt.analyticAt
      (((hgan z hz).harmonicAt_log_norm (hg0 z hz)).sub
        (harmonicOnNhd_greenLimit_basin c z (hUb hz)))
  have huC : ∀ z ∈ C, u z = 0 := by
    intro z hz; rw [hu]; simp only; rw [hC z hz, Real.log_exp, sub_self]
  have hev : u =ᶠ[𝓝 z₁] (fun _ => (0:ℝ)) := by
    filter_upwards [hCo.mem_nhds hz₁] with z hz using huC z hz
  have huzero : ∀ z ∈ U, u z = 0 :=
    fun z hz => (huan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc (hCsub hz₁) hev) hz
  intro z hz
  have h0 : Real.log ‖g z‖ = greenLimit c z := sub_eq_zero.mp (huzero z hz)
  rw [← h0, Real.exp_log (norm_pos_iff.mpr (hg0 z hz))]

/-- **Primitive of `ω` on a basin ball-chain.** Given basin balls `U i` (each a ball contained in the basin)
with connected prefix-overlaps, there is a primitive of `ω = greenLogDeriv c` on `⋃_{j ≤ k} U j`. Each ball
gets a local primitive from mathlib's `DifferentiableOn.isExactOn_ball` (`ω` is holomorphic on the basin);
`exists_primitive_glue_chain` assembles them. This is the constructive primitive that feeds
`exists_fullBottcherBranch_of_primitive`; the only remaining input is a *geometric* ball-chain from
`escapeOpen` toward a Julia point with connected prefix-overlaps (point-set topology of a simple arc in the
open connected basin), no longer an analytic frontier theorem. -/
theorem exists_primitive_greenLogDeriv_chain {c : ℂ} (U : ℕ → Set ℂ)
    (hball : ∀ i, ∃ a r, U i = Metric.ball a r)
    (hsub : ∀ i, U i ⊆ (filledJulia c)ᶜ)
    (hconn : ∀ i, IsConnected ((⋃ j ∈ Finset.range (i + 1), U j) ∩ U (i + 1)))
    (k : ℕ) :
    ∃ G : ℂ → ℂ, ∀ z ∈ (⋃ j ∈ Finset.range (k + 1), U j), HasDerivAt G (greenLogDeriv c z) z := by
  classical
  have hUo : ∀ i, IsOpen (U i) := by
    intro i; obtain ⟨a, r, heq⟩ := hball i; rw [heq]; exact Metric.isOpen_ball
  have hlocal : ∀ i, ∃ g : ℂ → ℂ, ∀ z ∈ U i, HasDerivAt g (greenLogDeriv c z) z := by
    intro i
    obtain ⟨a, r, heq⟩ := hball i
    have hdiff : DifferentiableOn ℂ (greenLogDeriv c) (Metric.ball a r) := by
      rw [← heq]; exact (differentiableOn_greenLogDeriv c).mono (hsub i)
    obtain ⟨g, hg⟩ := hdiff.isExactOn_ball
    exact ⟨g, by rw [heq]; exact hg⟩
  choose g hg using hlocal
  exact exists_primitive_glue_chain U g hUo hg hconn k

/-- **Prefix-overlap = consecutive lens, under non-adjacent disjointness.** If `U j ∩ U (i+1) = ∅` for all
`j < i`, then `(⋃_{j ≤ i} U j) ∩ U (i+1) = U i ∩ U (i+1)`. -/
theorem prefix_inter_eq_of_disjoint {U : ℕ → Set ℂ} {i : ℕ}
    (hdisj : ∀ j, j < i → U j ∩ U (i + 1) = ∅) :
    (⋃ j ∈ Finset.range (i + 1), U j) ∩ U (i + 1) = U i ∩ U (i + 1) := by
  ext x
  simp only [mem_inter_iff, mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · rintro ⟨⟨j, hj, hxj⟩, hxi1⟩
    rcases Nat.lt_or_ge j i with hji | hji
    · exact absurd (show x ∈ U j ∩ U (i + 1) from ⟨hxj, hxi1⟩) (by rw [hdisj j hji]; exact id)
    · have hji' : j = i := by omega
      exact ⟨hji' ▸ hxj, hxi1⟩
  · rintro ⟨hxi, hxi1⟩
    exact ⟨⟨i, Nat.lt_succ_self i, hxi⟩, hxi1⟩

/-- **Chain primitive from consecutive-connected + non-adjacent-disjoint balls.** The geometrically natural
hypotheses for a simple-arc ball cover: consecutive overlaps connected, non-adjacent balls disjoint. Reduces
the connected-prefix-overlap hypothesis of `exists_primitive_glue_chain` to these (via
`prefix_inter_eq_of_disjoint`). The arc/cover from `escapeOpen` to a Julia point supplies exactly these. -/
theorem exists_primitive_glue_chain_of_disjoint {f : ℂ → ℂ} (U : ℕ → Set ℂ) (g : ℕ → ℂ → ℂ)
    (hUo : ∀ i, IsOpen (U i))
    (hg : ∀ i, ∀ z ∈ U i, HasDerivAt (g i) (f z) z)
    (hover : ∀ i, IsConnected (U i ∩ U (i + 1)))
    (hdisj : ∀ i, ∀ j, j < i → U j ∩ U (i + 1) = ∅)
    (k : ℕ) :
    ∃ G : ℂ → ℂ, ∀ z ∈ (⋃ j ∈ Finset.range (k + 1), U j), HasDerivAt G (f z) z := by
  refine exists_primitive_glue_chain U g hUo hg (fun i => ?_) k
  rw [prefix_inter_eq_of_disjoint (hdisj i)]
  exact hover i

/-- `filledJulia c` is nonempty (it contains a fixed point of `f_c`). -/
theorem nonempty_filledJulia (c : ℂ) : (filledJulia c).Nonempty := by
  obtain ⟨z, hz⟩ := exists_periodic_point c 1 (le_refl 1)
  have hfix : quadratic c z = z := by simpa using hz
  refine ⟨z, ?_⟩
  rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le]
  exact ⟨‖z‖, fun x hx => by obtain ⟨n, rfl⟩ := hx; simp [Function.iterate_fixed hfix n]⟩

/-- **Rightmost filled-Julia point.** Since `K_c` is compact and nonempty, the real-part functional
attains its maximum on `K_c`. This is the canonical half-plane anchor used by the connected hRigid
branch route. -/
theorem exists_rightmost_filledJulia (c : ℂ) :
    ∃ z₀ ∈ filledJulia c, ∀ w ∈ filledJulia c, w.re ≤ z₀.re := by
  obtain ⟨z₀, hz₀K, hz₀max⟩ :=
    (isCompact_filledJulia c).exists_isMaxOn (nonempty_filledJulia c)
      Complex.continuous_re.continuousOn
  exact ⟨z₀, hz₀K, fun w hw => hz₀max hw⟩

/-- **A rightmost filled-Julia point lies on the Julia frontier.** Points immediately to the right of
a real-part maximizer cannot lie in `K_c`, and they approach the maximizer. -/
theorem rightmost_mem_frontier_filledJulia {c z₀ : ℂ}
    (hz₀K : z₀ ∈ filledJulia c)
    (hz₀max : ∀ w ∈ filledJulia c, w.re ≤ z₀.re) :
    z₀ ∈ frontier (filledJulia c) := by
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure hz₀K, ?_⟩
  rw [Metric.mem_closure_iff]
  intro δ hδ
  let ε : ℝ := δ / 2
  let p : ℂ := z₀ + (ε : ℂ)
  have hεpos : 0 < ε := by dsimp [ε]; linarith
  have hpnot : p ∉ filledJulia c := by
    intro hpK
    have hmax := hz₀max p hpK
    have hpre : p.re = z₀.re + ε := by simp [p]
    rw [hpre] at hmax
    linarith
  refine ⟨p, hpnot, ?_⟩
  rw [dist_eq_norm]
  have hsub : z₀ - p = -((ε : ℂ)) := by simp [p]
  rw [hsub, norm_neg, Complex.norm_real, Real.norm_of_nonneg hεpos.le]
  dsimp [ε]
  linarith

/-- **Rightmost frontier sector package.** A rightmost filled-Julia point exists on the frontier, and
at every radius the strict right half-plane slice through that point is preconnected and lies in the
basin. This is intentionally weaker than the local-tip hypothesis: it supplies a canonical
preconnected basin-side sector but does not claim the whole punctured basin slice is preconnected. -/
theorem exists_rightmost_frontier_rightHalfplane_basin_sector (c : ℂ) :
    ∃ z₀ : ℂ, z₀ ∈ frontier (filledJulia c) ∧
      (∀ w ∈ filledJulia c, w.re ≤ z₀.re) ∧
      ∀ ρ : ℝ,
        IsPreconnected (Metric.ball z₀ ρ ∩ {z : ℂ | z₀.re < z.re}) ∧
          Metric.ball z₀ ρ ∩ {z : ℂ | z₀.re < z.re} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ := by
  obtain ⟨z₀, hz₀K, hz₀max⟩ := exists_rightmost_filledJulia c
  refine ⟨z₀, rightmost_mem_frontier_filledJulia hz₀K hz₀max, hz₀max, ?_⟩
  intro ρ
  refine ⟨((convex_ball z₀ ρ).inter (convex_halfSpace_re_gt z₀.re)).isPreconnected, ?_⟩
  intro z hz
  exact ⟨hz.1, fun hzK => (not_lt_of_ge (hz₀max z hzK)) hz.2⟩

/-- **Unconditional Böttcher branch with modulus on the right half-plane — discharges the `hF` hypothesis.**
The half-plane `R = {Re z > M}` with `M = max Re over K_c` is convex and disjoint from `K_c` (so `⊆` basin);
mathlib's **convex** Poincaré lemma `Convex.exists_forall_hasDerivWithinAt` gives a primitive of `ω` on `R`
with NO assumption, and `exists_bottcherBranch_of_primitive` yields a single-valued branch `β`, analytic,
nonvanishing, with the Böttcher modulus `‖β‖ = exp(greenFunctionDyn c)`. This is the first unconditional
construction of the continued Böttcher coordinate (the `hF`/primitive input is now eliminated on `R`); the
max-Re point of `K_c` lies on `∂R ∩ J_c`, the anchor for the natural-boundary contradiction. -/
theorem exists_bottcherBranch_rightHalfplane (c : ℂ) :
    ∃ (M : ℝ) (β : ℂ → ℂ),
      (∀ w ∈ filledJulia c, w.re ≤ M) ∧
      AnalyticOnNhd ℂ β {z | M < z.re} ∧ (∀ z, M < z.re → β z ≠ 0) ∧
      (∀ z, M < z.re → ‖β z‖ = Real.exp (greenFunctionDyn c z)) := by
  obtain ⟨z₀, _hz₀K, hz₀max⟩ := exists_rightmost_filledJulia c
  set M : ℝ := z₀.re with hM
  have hmax : ∀ w ∈ filledJulia c, w.re ≤ M := fun w hw => hz₀max w hw
  set R : Set ℂ := {z | M < z.re} with hR
  have hRconv : Convex ℝ R := convex_halfSpace_re_gt M
  have hRo : IsOpen R := isOpen_lt continuous_const Complex.continuous_re
  have hRb : R ⊆ (filledJulia c)ᶜ := fun z hz hzK => absurd (hmax z hzK) (not_le.mpr hz)
  have hTR : ((M + 1 : ℝ) : ℂ) ∈ R := by
    show M < ((M + 1 : ℝ) : ℂ).re; rw [Complex.ofReal_re]; linarith
  have hωdiff : DifferentiableOn ℂ (greenLogDeriv c) R := (differentiableOn_greenLogDeriv c).mono hRb
  obtain ⟨F, hF'⟩ := hRconv.exists_forall_hasDerivWithinAt hωdiff
  have hF : ∀ z ∈ R, HasDerivAt F (greenLogDeriv c z) z :=
    fun z hz => (hF' z hz).hasDerivAt (hRo.mem_nhds hz)
  obtain ⟨β, hβan, hβ0, hβmod⟩ :=
    exists_bottcherBranch_of_primitive hRo hRconv.isPreconnected hRb hF hTR
  exact ⟨M, β, hmax, hβan, hβ0, hβmod⟩

/-- **Unconditional FULL Böttcher branch on the right half-plane (modulus + relation).** As
`exists_bottcherBranch_rightHalfplane`, but the branch `β` additionally satisfies any relation
`P(z, bottcherCoord c z) = 0` that holds on `escapeOpen ∩ slitPlane` — anchored by a small escape ball
inside `R` (`exists_fullBottcherBranch_of_primitive`). This is the unconditional single-valued `φ_c` on `R`
carrying everything `false_of_basin_branch_dendrite` needs on the basin side, with NO primitive hypothesis. -/
theorem exists_fullBottcherBranch_rightHalfplane (c : ℂ)
    (P : Polynomial (Polynomial ℂ))
    (hrel : ∀ z ∈ escapeOpen c ∩ Complex.slitPlane,
        ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) :
    ∃ (M : ℝ) (β : ℂ → ℂ),
      (∀ w ∈ filledJulia c, w.re ≤ M) ∧
      AnalyticOnNhd ℂ β {z | M < z.re} ∧ (∀ z, M < z.re → β z ≠ 0) ∧
      (∀ z, M < z.re → ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z, M < z.re → ∑ i ∈ P.support, (P.coeff i).aeval z * (β z) ^ i = 0) := by
  obtain ⟨z₀, _hz₀K, hz₀max⟩ := exists_rightmost_filledJulia c
  set M : ℝ := z₀.re with hM
  have hmax : ∀ w ∈ filledJulia c, w.re ≤ M := fun w hw => hz₀max w hw
  set R : Set ℂ := {z | M < z.re} with hR
  have hRconv : Convex ℝ R := convex_halfSpace_re_gt M
  have hRo : IsOpen R := isOpen_lt continuous_const Complex.continuous_re
  have hRb : R ⊆ (filledJulia c)ᶜ := fun z hz hzK => absurd (hmax z hzK) (not_le.mpr hz)
  set MM : ℝ := max 2 ‖c‖ with hMM
  set T : ℝ := max M MM + 1 with hT
  have hTM : M < T := by have := le_max_left M MM; rw [hT]; linarith
  have hTMM : MM < T := by have := le_max_right M MM; rw [hT]; linarith
  have hTpos : 0 < T := by
    have h2 : (2:ℝ) ≤ MM := le_max_left 2 ‖c‖
    have := le_max_right M MM; rw [hT]; linarith
  have hTmem : (T : ℂ) ∈ R ∩ escapeOpen c ∩ Complex.slitPlane := by
    refine ⟨⟨?_, ?_⟩, ofReal_mem_slitPlane.mpr hTpos⟩
    · show M < ((T:ℝ):ℂ).re; rw [Complex.ofReal_re]; exact hTM
    · show MM < ‖((T:ℝ):ℂ)‖; rw [Complex.norm_real, Real.norm_of_nonneg hTpos.le]; exact hTMM
  have hOpen : IsOpen (R ∩ escapeOpen c ∩ Complex.slitPlane) :=
    (hRo.inter (isOpen_escapeOpen c)).inter Complex.isOpen_slitPlane
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hOpen _ hTmem
  have hωdiff : DifferentiableOn ℂ (greenLogDeriv c) R := (differentiableOn_greenLogDeriv c).mono hRb
  obtain ⟨F, hF'⟩ := hRconv.exists_forall_hasDerivWithinAt hωdiff
  have hF : ∀ z ∈ R, HasDerivAt F (greenLogDeriv c z) z :=
    fun z hz => (hF' z hz).hasDerivAt (hRo.mem_nhds hz)
  obtain ⟨β, hβan, hβ0, hβmod, hβrel⟩ := exists_fullBottcherBranch_of_primitive hRo
    hRconv.isPreconnected hRb hF (E := Metric.ball (T : ℂ) ρ)
    (fun z hz => ((hball hz).1).1) (fun z hz => ⟨((hball hz).1).2, (hball hz).2⟩)
    Metric.isOpen_ball (convex_ball _ _).isPreconnected (Metric.mem_ball_self hρ) P
    (fun z hz => hrel z ⟨((hball hz).1).2, (hball hz).2⟩)
  exact ⟨M, β, hmax, hβan, hβ0, hβmod, hβrel⟩

end Bottcher
