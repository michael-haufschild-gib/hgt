/-
# Harmonic minimum principle for non-negative functions

A non-negative harmonic function with an interior zero is identically zero (on the connected
component). This is the engine of the connected-case Böttcher natural-boundary argument: if the
inverse Böttcher coordinate `φ_c` continued analytically across a Julia-set point `z₀ ∈ J_c`, then
`G_c = log‖φ_c‖` would be a non-negative harmonic function on a neighborhood of `z₀` with
`G_c(z₀) = 0` (an interior zero) yet `G_c > 0` on the basin side — contradicting this principle.

The proof avoids measure theory: on a ball, a harmonic `u` equals `Re F` for a holomorphic `F`
(`exists_analyticOnNhd_ball_re_eq`); then `g = exp(−F)` is holomorphic with `‖g‖ = exp(−u) ≤ 1`,
attaining its maximum `1` at the interior zero `z₀`, so the maximum-modulus principle
(`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`) forces `g` constant, i.e. `u ≡ 0`. The local
result propagates over a preconnected domain by a clopen argument.

General lemma (not Böttcher-specific); consumes only Mathlib.
-/
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.AbsMax

open Complex InnerProductSpace Metric Topology Set

/-- **Minimum principle on a ball.** A non-negative harmonic `u` on `ball z₀ r` with `u z₀ = 0`
vanishes on the whole ball. -/
theorem harmonic_eq_zero_on_ball_of_nonneg {u : ℂ → ℝ} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hu : HarmonicOnNhd u (ball z₀ r)) (hnn : ∀ z ∈ ball z₀ r, 0 ≤ u z)
    (h0 : u z₀ = 0) : ∀ z ∈ ball z₀ r, u z = 0 := by
  obtain ⟨F, hFan, hFre⟩ := hu.exists_analyticOnNhd_ball_re_eq
  set g : ℂ → ℂ := fun z => Complex.exp (-F z) with hg
  have hgan : AnalyticOnNhd ℂ g (ball z₀ r) := fun z hz => ((hFan z hz).neg).cexp
  have hnorm : ∀ z ∈ ball z₀ r, ‖g z‖ = Real.exp (-u z) := by
    intro z hz
    rw [hg]
    simp only [Complex.norm_exp, Complex.neg_re, hFre hz]
  have hz0mem : z₀ ∈ ball z₀ r := mem_ball_self hr
  have hmax : IsMaxOn (norm ∘ g) (ball z₀ r) z₀ := by
    intro z hz
    simp only [Set.mem_setOf_eq, Function.comp_apply]
    rw [hnorm z hz, hnorm z₀ hz0mem]
    exact Real.exp_le_exp.mpr (by have := hnn z hz; have := h0; linarith)
  have heqc : EqOn g (Function.const ℂ (g z₀)) (ball z₀ r) :=
    Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball z₀ r).isPreconnected
      isOpen_ball hgan.differentiableOn hz0mem hmax
  intro z hz
  have hgz : g z = g z₀ := by have := heqc hz; simpa [Function.const] using this
  have hnormeq : ‖g z‖ = ‖g z₀‖ := by rw [hgz]
  rw [hnorm z hz, hnorm z₀ hz0mem] at hnormeq
  have hlog := congrArg Real.log hnormeq
  rw [Real.log_exp, Real.log_exp] at hlog
  have := h0
  linarith

/-- **Minimum principle on a preconnected domain.** A non-negative harmonic `u` on a preconnected
open set `V` that vanishes at one point of `V` vanishes on all of `V`. The zero set is open (ball
lemma) and closed-in-`V` (continuity), hence all of the connected `V`. -/
theorem harmonic_eqOn_zero_of_nonneg {u : ℂ → ℝ} {V : Set ℂ}
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hu : HarmonicOnNhd u V)
    (hnn : ∀ z ∈ V, 0 ≤ u z) {z₀ : ℂ} (hz₀ : z₀ ∈ V) (h0 : u z₀ = 0) :
    EqOn u 0 V := by
  -- every basin zero is an interior zero (ball lemma)
  have hzero_interior : ∀ z ∈ V, u z = 0 → z ∈ interior {w | u w = 0} := by
    intro z hzV hzz
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hVo z hzV
    have hballzero : ∀ w ∈ ball z ρ, u w = 0 :=
      harmonic_eq_zero_on_ball_of_nonneg hρ (fun w hw => hu w (hball hw))
        (fun w hw => hnn w (hball hw)) hzz
    exact mem_interior.mpr ⟨ball z ρ, hballzero, isOpen_ball, mem_ball_self hρ⟩
  have hWopen : IsOpen (V ∩ {w | u w ≠ 0}) := by
    refine isOpen_iff_mem_nhds.mpr (fun z hz => ?_)
    obtain ⟨hzV, hzne⟩ := hz
    have hcont : ContinuousAt u z := (hu z hzV).1.continuousAt
    exact Filter.inter_mem (hVo.mem_nhds hzV) (hcont.preimage_mem_nhds (isOpen_ne.mem_nhds hzne))
  have hdisj : Disjoint (interior {w | u w = 0}) (V ∩ {w | u w ≠ 0}) := by
    rw [Set.disjoint_left]
    intro z hzA hzW
    have hzA' : z ∈ {w | u w = 0} := interior_subset (s := {w | u w = 0}) hzA
    exact hzW.2 hzA'
  have hsub : V ⊆ interior {w | u w = 0} ∪ (V ∩ {w | u w ≠ 0}) := by
    intro z hzV
    by_cases hu0 : u z = 0
    · exact Or.inl (hzero_interior z hzV hu0)
    · exact Or.inr ⟨hzV, hu0⟩
  have hVA : (V ∩ interior {w | u w = 0}).Nonempty := ⟨z₀, hz₀, hzero_interior z₀ hz₀ h0⟩
  have hVsub : V ⊆ interior {w | u w = 0} :=
    hVc.subset_left_of_subset_union isOpen_interior hWopen hdisj hsub hVA
  intro z hz
  have hz0 : z ∈ {w | u w = 0} := interior_subset (s := {w | u w = 0}) (hVsub hz)
  simpa using hz0

open Filter Bornology in
/-- **Harmonic uniqueness on an exterior (unbounded) domain — E1 core.** A function continuous on `ℂ`,
harmonic on a preconnected unbounded open `Ω`, vanishing off `Ω`, and tending to `0` at `∞`, is
identically `0`. This is the maximum-principle uniqueness that forces two Green's functions of the
same filled Julia set to coincide (`K_{c₁}=K_{c₂} ⟹ G_{c₁}=G_{c₂}`). Proof: a one-sided bound `v ≤ 0`
for any such `v`; the global max `M` (attained on the compact superlevel `{ε ≤ v}`) lands at an
interior point of `Ω`, where the minimum principle on `M − v` forces `v ≡ M` on `Ω`; but `Ω` is
unbounded and `v → 0` at `∞`, so `M = 0`. Apply to `u` and `−u`. -/
theorem harmonic_exterior_unique {u : ℂ → ℝ} {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩunb : ¬ IsBounded Ω)
    (hu : HarmonicOnNhd u Ω) (hucont : Continuous u)
    (hbd : ∀ z ∉ Ω, u z = 0)
    (hinf : Tendsto u (cobounded ℂ) (𝓝 0)) :
    u = 0 := by
  have key : ∀ v : ℂ → ℝ, HarmonicOnNhd v Ω → Continuous v → (∀ z ∉ Ω, v z = 0) →
      Tendsto v (cobounded ℂ) (𝓝 0) → ∀ z, v z ≤ 0 := by
    intro v hv hvc hvbd hvinf z
    by_contra hpos
    push_neg at hpos
    set ε : ℝ := v z with hεdef
    have hεpos : 0 < ε := hpos
    have hmem : {w : ℂ | v w < ε} ∈ cobounded ℂ := hvinf (gt_mem_nhds hεpos)
    have hbdd : IsBounded {w : ℂ | ε ≤ v w} := by
      have he : {w : ℂ | ε ≤ v w} = {w | v w < ε}ᶜ := by ext w; simp [not_lt]
      rw [he, isBounded_compl_iff]; exact hmem
    have hcl : IsClosed {w : ℂ | ε ≤ v w} := isClosed_le continuous_const hvc
    have hcompact : IsCompact {w : ℂ | ε ≤ v w} := isCompact_of_isClosed_isBounded hcl hbdd
    have hne : ({w : ℂ | ε ≤ v w}).Nonempty := ⟨z, le_refl ε⟩
    obtain ⟨z₀, hz₀mem, hz₀max⟩ := hcompact.exists_isMaxOn hne hvc.continuousOn
    set M : ℝ := v z₀ with hMdef
    have hglobal : ∀ w, v w ≤ M := by
      intro w
      by_cases hw : ε ≤ v w
      · exact hz₀max hw
      · push_neg at hw; have : ε ≤ M := hz₀mem; linarith
    have hz₀Ω : z₀ ∈ Ω := by
      by_contra hz₀notΩ
      have h0 : v z₀ = 0 := hvbd z₀ hz₀notΩ
      have hεM : ε ≤ M := hz₀mem
      rw [← hMdef] at h0; linarith
    have hMvharm : HarmonicOnNhd (fun w => M - v w) Ω := (harmonicOnNhd_const M).sub hv
    have hMvnn : ∀ w ∈ Ω, 0 ≤ M - v w := fun w _ => by linarith [hglobal w]
    have hMv0 : (fun w => M - v w) z₀ = 0 := by simp [hMdef]
    have hzero := harmonic_eqOn_zero_of_nonneg hΩo hΩc hMvharm hMvnn hz₀Ω hMv0
    have hvM : ∀ w ∈ Ω, v w = M := by
      intro w hw
      have h := hzero hw
      simp only [Pi.zero_apply] at h
      linarith
    have hMzero : M = 0 := by
      by_contra hMne
      obtain ⟨w, hwΩ, hwnot⟩ := Set.not_subset.mp
        (fun hsub => hΩunb (hbdd.subset hsub) : ¬ Ω ⊆ {w : ℂ | ε ≤ v w})
      simp only [Set.mem_setOf_eq, not_le] at hwnot
      have : v w = M := hvM w hwΩ
      have hεM : ε ≤ M := hz₀mem
      linarith
    have hεM : ε ≤ M := hz₀mem
    linarith
  funext z
  simp only [Pi.zero_apply]
  have h1 := key u hu hucont hbd hinf z
  have h2 := key (fun w => -u w) hu.neg hucont.neg
    (fun w hw => by simp [hbd w hw]) (by simpa using hinf.neg) z
  simp only at h2
  linarith

