/-
# The connected Böttcher branch, assembled from one isolated per-level root datum

The connected-case global Böttcher branch is reduced (in `BasinColimit`) to producing, at every level
`n`, a single-valued analytic nowhere-zero `2ⁿ`-th root of `bottcherCoord c ∘ f^[n]` on the connected
`escapeLevel c n`. The *existence* of that root is the genuine geometric content — exactly the winding /
`π₁`-divisibility statement (the winding number of `bottcherCoord∘f^[n]` around the hole `K_c` is
divisible by `2ⁿ`) that `CoveringRoot.exists_analyticOnNhd_pow_eq_of_lift` converts into a root.

This file isolates that content as `LevelRootInput c` and discharges *everything downstream of it*: the
roots are renormalised so each restricts to `bottcherCoord c` on the far field (the discrepancy is a
`2ⁿ`-th root of unity, constant on the connected `escapeOpen c` by `const_of_pow_eq_one`, divided out),
and then `exists_global_branch_of_level_roots` glues the levels into the global branch. So the connected
Böttcher uniformisation holds unconditionally once `LevelRootInput c` is supplied — the per-level winding
datum is the only remaining input, cleanly separated from the analytic/colimit plumbing.
-/
import GaloisForLFunctions.Bottcher.BasinColimit
import GaloisForLFunctions.Bottcher.BasinConnected
import GaloisForLFunctions.Bottcher.BasinBranchGlue
import GaloisForLFunctions.Bottcher.BottcherCoord
import GaloisForLFunctions.Bottcher.BottcherInverse
import GaloisForLFunctions.Bottcher.CoveringRoot
import GaloisForLFunctions.Bottcher.EscapeLevelRoot
import GaloisForLFunctions.Bottcher.FarFieldUnivalence
import GaloisForLFunctions.Bottcher.ConnectedPi1
import GaloisForLFunctions.Bottcher.Brolin.Basic
import GaloisForLFunctions.Bottcher.DeckAnnulusData
import GaloisForLFunctions.Bottcher.ProperLocalHomeoCovering
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

open Topology
open unitInterval

namespace Bottcher

/-- **The isolated remaining geometric input for the connected case.** At every level `n`, the pullback
`bottcherCoord c ∘ f^[n]` has a single-valued analytic nowhere-zero `2ⁿ`-th root on the connected escape
level `escapeLevel c n`. This is precisely the winding/`π₁`-divisibility content (winding of
`bottcherCoord∘f^[n]` around the hole divisible by `2ⁿ`) supplied by `CoveringRoot`; with it, the whole
connected-branch assembly proceeds. -/
def LevelRootInput (c : ℂ) : Prop :=
  ∀ n : ℕ, ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (escapeLevel c n) ∧
    (∀ z ∈ escapeLevel c n, s z ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z)) ∧
    (∀ z ∈ escapeLevel c n, s z ≠ 0)

/-- **Normalized per-level roots from `LevelRootInput`.** Given arbitrary level roots, divide each one
by its constant far-field discrepancy so that every level restricts to the normalized Böttcher
coordinate on `escapeOpen c`. This is the shared normalization step behind both the plain global branch
and the modulus/functional-equation endpoint. -/
theorem exists_normalized_level_roots_of_levelRootInput (c : ℂ) (h : LevelRootInput c) :
    ∃ βlev : ℕ → ℂ → ℂ,
      (∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c n)) ∧
      (∀ n, ∀ z ∈ escapeLevel c n,
        (βlev n z) ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z)) ∧
      (∀ n, ∀ z ∈ escapeLevel c n, βlev n z ≠ 0) ∧
      (∀ n, ∀ z ∈ escapeOpen c, βlev n z = bottcherCoord c z) := by
  classical
  choose s hsan hspow hsne using h
  set dpt : ℂ := ((max 2 ‖c‖ + 1 : ℝ) : ℂ) with hdpt
  have hsub : ∀ n, escapeOpen c ⊆ escapeLevel c n := by
    intro n; rw [← escapeLevel_zero]; exact escapeLevel_subset_of_le c (Nat.zero_le n)
  have hdptEsc : dpt ∈ escapeOpen c := by
    have := deep_mem_escapeLevel c 0; rwa [escapeLevel_zero] at this
  -- the renormalising constant: `ζ n = s n / bottcherCoord` at the deep anchor, a `2ⁿ`-th root of unity
  set ζ : ℕ → ℂ := fun n => s n dpt / bottcherCoord c dpt with hζdef
  have hζne : ∀ n, ζ n ≠ 0 := fun n =>
    div_ne_zero (hsne n dpt (hsub n hdptEsc)) (bottcherCoord_ne_zero c _)
  have hζpow : ∀ n, (ζ n) ^ (2 ^ n) = 1 := by
    intro n
    obtain ⟨hcz, hz2⟩ := mem_escapeOpen_regime hdptEsc
    rw [hζdef]
    simp only
    rw [div_pow, hspow n dpt (hsub n hdptEsc), bottcherCoord_iterate hcz hz2 n, div_self]
    exact pow_ne_zero _ (bottcherCoord_ne_zero c _)
  -- the discrepancy `s n / bottcherCoord` is constant `= ζ n` on the connected far field
  have hξconst : ∀ n, ∀ z ∈ escapeOpen c, s n z / bottcherCoord c z = ζ n := by
    intro n
    have hξc : ContinuousOn (fun z => s n z / bottcherCoord c z) (escapeOpen c) := by
      apply ContinuousOn.div
      · exact ((hsan n).continuousOn).mono (hsub n)
      · exact (analyticOnNhd_bottcherCoord_full c).continuousOn
      · exact fun z _ => bottcherCoord_ne_zero c _
    have hξpow : ∀ z ∈ escapeOpen c, (fun z => s n z / bottcherCoord c z) z ^ (2 ^ n) = 1 := by
      intro z hz
      obtain ⟨hcz, hz2⟩ := mem_escapeOpen_regime hz
      simp only
      rw [div_pow, hspow n z (hsub n hz), bottcherCoord_iterate hcz hz2 n, div_self]
      exact pow_ne_zero _ (bottcherCoord_ne_zero c _)
    intro z hz
    exact const_of_pow_eq_one (isConnected_escapeOpen c).isPreconnected hξc (by positivity)
      hξpow hz hdptEsc
  -- the renormalised family `βlev n = s n / ζ n`
  set βlev : ℕ → ℂ → ℂ := fun n z => s n z / ζ n with hβdef
  refine ⟨βlev, ?_, ?_, ?_, ?_⟩
  · -- analytic
    intro n z hz
    exact (hsan n z hz).div_const
  · -- `2ⁿ`-th power law
    intro n z hz
    show (s n z / ζ n) ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z)
    rw [div_pow, hζpow n, div_one, hspow n z hz]
  · -- nowhere zero
    intro n z hz
    exact div_ne_zero (hsne n z hz) (hζne n)
  · -- anchored to `bottcherCoord` on the far field
    intro n z hz
    have hc := hξconst n z hz
    rw [div_eq_iff (bottcherCoord_ne_zero c z)] at hc
    show s n z / ζ n = bottcherCoord c z
    rw [hc]
    exact mul_div_cancel_left₀ (bottcherCoord c z) (hζne n)

/-- **The connected global Böttcher branch from the per-level root input.** Given `LevelRootInput c`,
renormalise each level root to agree with `bottcherCoord c` on the far field and glue: the result is a
single-valued analytic branch on the basin `(filledJulia c)ᶜ` extending `bottcherCoord c` on
`escapeOpen c`. -/
theorem exists_global_branch_of_levelRootInput (c : ℂ) (h : LevelRootInput c) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) := by
  obtain ⟨βlev, hanalytic, hpow, hne, hanchorEsc⟩ :=
    exists_normalized_level_roots_of_levelRootInput c h
  exact exists_global_branch_of_level_roots c βlev hanalytic hpow hne hanchorEsc

/-- **Full connected branch endpoint from the per-level root input.** This is the stronger form needed
for the Böttcher theorem: from `LevelRootInput c`, the glued branch is analytic, nonvanishing, anchored
to the far-field coordinate, has the Böttcher Green modulus on the whole basin, and satisfies the
functional equation (including all iterates). -/
theorem exists_global_branch_of_levelRootInput_modulus (c : ℂ) (h : LevelRootInput c) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
      (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
        β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) := by
  obtain ⟨βlev, hanalytic, hpow, hne, hanchorEsc⟩ :=
    exists_normalized_level_roots_of_levelRootInput c h
  obtain ⟨β, hβan, hβesc, hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c βlev hanalytic hpow hne hanchorEsc
  exact ⟨β, hβan, hβesc, hβ0, hβmod, one_lt_norm_of_global_branch_modulus hβmod,
    bottcherFE_of_global_branch hβan hβesc,
    bottcherFE_iterate_of_global_branch hβan hβesc⟩

/-- **One level of `LevelRootInput` from the winding lift (CoveringRoot, applied to `bottcherCoord∘f^[n]`).**
The pullback `bottcherCoord c ∘ f^[n]` is analytic and nowhere-zero on the connected open `escapeLevel c n`
(`analyticAt_quadratic_iterate` + `analyticOnNhd_bottcherCoord_full`, `bottcherCoord_ne_zero`). If its
`π₁`-image lands in the `2ⁿ`-th powers of `π₁(ℂ*)` — the canonical winding hypothesis `hlift`, presented
through the bundled nowhere-zero map `gSub = bottcherCoord∘f^[n]` — then it has a single-valued analytic
nowhere-zero `2ⁿ`-th root on the whole level. Running this at every level yields `LevelRootInput c`, which
`exists_global_branch_of_levelRootInput` turns into the global branch: the entire connected case is thus
reduced to the per-level winding hypothesis `hlift`, the only genuinely missing analytic input. -/
theorem exists_levelRoot_of_lift (c : ℂ) (n : ℕ)
    (gSub : C(escapeLevel c n, {w : ℂ // w ≠ 0}))
    (hgSub : ∀ a : escapeLevel c n, (gSub a : ℂ) = bottcherCoord c ((quadratic c)^[n] (a : ℂ)))
    {a₀ : escapeLevel c n} {e₀ : {w : ℂ // w ≠ 0}}
    (he : (⟨(e₀ : ℂ) ^ (2 ^ n), pow_ne_zero (2 ^ n) e₀.2⟩ : {w : ℂ // w ≠ 0}) = gSub a₀)
    (hlift : (FundamentalGroup.map gSub a₀).range ≤
      (FundamentalGroup.mapOfEq
        ⟨fun x : {w : ℂ // w ≠ 0} =>
            (⟨(x : ℂ) ^ (2 ^ n), pow_ne_zero (2 ^ n) x.2⟩ : {w : ℂ // w ≠ 0}), by fun_prop⟩
          he).range) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (escapeLevel c n) ∧
      (∀ z ∈ escapeLevel c n, s z ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z)) ∧
      (∀ z ∈ escapeLevel c n, s z ≠ 0) := by
  have hgan : AnalyticOnNhd ℂ (fun z => bottcherCoord c ((quadratic c)^[n] z)) (escapeLevel c n) :=
    fun z hz => (analyticOnNhd_bottcherCoord_full c _ hz).comp (analyticAt_quadratic_iterate c n z)
  have hne0 : ((2 ^ n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0)
  exact exists_analyticOnNhd_pow_eq_of_lift (isOpen_escapeLevel c n) (isConnected_escapeLevel c n)
    hgan hne0 gSub hgSub he hlift

/-- **Level roots from the pure iterate-image winding theorem.** This is the answer-03 root
construction in the form consumed by the connected Böttcher assembly: if every loop in
`escapeLevel c (n+1)` maps under `f_c^[n+1]` to a loop in `escapeOpen c` with winding divisible by
`2^(n+1)`, then every level has a single-valued analytic `2^n`-th root of
`bottcherCoord c ∘ f_c^[n]`. The only remaining input is the pure topological-degree statement
`hwindF`; all analytic root descent is discharged here. -/
theorem levelRootInput_of_iterate_image_winding (c : ℂ)
    (hwindF : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ m : ℤ,
        wind (fun a : escapeLevel c (n + 1) => quadratic c ((quadratic c)^[n] (a : ℂ)))
          ((continuous_quadratic c).comp
            (((continuous_quadratic c).iterate n).comp continuous_subtype_val))
          (fun a => escapeOpen_coe_ne_zero c
            ⟨quadratic c ((quadratic c)^[n] (a : ℂ)), by
              have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
              rwa [Function.iterate_succ_apply'] at ha⟩) p =
          (2 : ℤ) ^ (n + 1) * m) :
    LevelRootInput c := by
  intro n
  induction n with
  | zero =>
      refine ⟨bottcherCoord c, ?_, ?_, ?_⟩
      · simpa [escapeLevel_zero] using analyticOnNhd_bottcherCoord_full c
      · intro z hz
        simp
      · intro z hz
        exact bottcherCoord_ne_zero c z
  | succ n ih =>
      obtain ⟨βlevn, hβan, hβpow, hβne⟩ := ih
      let gSub : C(escapeLevel c (n + 1), {w : ℂ // w ≠ 0}) :=
        { toFun := fun a =>
            ⟨βlevn (quadratic c (a : ℂ)),
              hβne (quadratic c (a : ℂ)) ((quadratic_mapsTo_escapeLevel c n) a.2)⟩
          continuous_toFun := by
            apply Continuous.subtype_mk
            exact hβan.continuousOn.comp_continuous
              ((continuous_quadratic c).comp continuous_subtype_val)
              (fun a => (quadratic_mapsTo_escapeLevel c n) a.2) }
      let FSub : C(escapeLevel c (n + 1), escapeOpen c) :=
        { toFun := fun a => ⟨quadratic c ((quadratic c)^[n] (a : ℂ)), by
            have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
            rwa [Function.iterate_succ_apply'] at ha⟩
          continuous_toFun :=
            (((continuous_quadratic c).comp
              (((continuous_quadratic c).iterate n).comp continuous_subtype_val)).subtype_mk
              (fun a => by
                have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
                rwa [Function.iterate_succ_apply'] at ha)) }
      let HSub : C(escapeLevel c (n + 1), {w : ℂ // w ≠ 0}) :=
        { toFun := fun a => ⟨bottcherCoord c (FSub a : ℂ), bottcherCoord_ne_zero c _⟩
          continuous_toFun := by
            apply Continuous.subtype_mk
            exact (analyticOnNhd_bottcherCoord_full c).continuousOn.comp_continuous
              (continuous_subtype_val.comp FSub.continuous) (fun a => (FSub a).2) }
      let a₀ : escapeLevel c (n + 1) :=
        ⟨((max 2 ‖c‖ + 1 : ℝ) : ℂ), deep_mem_escapeLevel c (n + 1)⟩
      obtain ⟨e, hepow⟩ := IsAlgClosed.exists_pow_nat_eq (gSub a₀ : ℂ) (by norm_num : 0 < 2)
      have hene : e ≠ 0 := by
        intro he0
        have hzero : (gSub a₀ : ℂ) = 0 := by
          rw [← hepow, he0]
          norm_num
        exact (gSub a₀).2 hzero
      let e₀ : {w : ℂ // w ≠ 0} := ⟨e, hene⟩
      have he : (⟨(e₀ : ℂ) ^ 2, pow_ne_zero 2 e₀.2⟩ : {w : ℂ // w ≠ 0}) = gSub a₀ := by
        apply Subtype.ext
        exact hepow
      have hwindStep : ∀ p : Path a₀ a₀, ∃ m : ℤ,
          wind (fun a : escapeLevel c (n + 1) => (FSub a : ℂ))
            (continuous_subtype_val.comp FSub.continuous)
            (fun a => escapeOpen_coe_ne_zero c (FSub a)) p =
            (2 : ℤ) ^ (n + 1) * m := by
        intro p
        obtain ⟨m, hm⟩ := hwindF n p
        refine ⟨m, ?_⟩
        simpa [FSub] using hm
      obtain ⟨s, hsan, hssq⟩ :=
        exists_sqrt_pullback_of_iterate_image_winding c n βlevn hβan hβpow
          gSub (by intro a; rfl) FSub
          (by
            intro a
            simp [FSub, Function.iterate_succ_apply'])
          HSub (by intro a; rfl) he hwindStep
      refine ⟨s, hsan, ?_, ?_⟩
      · intro z hz
        have hfz : quadratic c z ∈ escapeLevel c n := (quadratic_mapsTo_escapeLevel c n) hz
        calc
          (s z) ^ (2 ^ (n + 1))
              = ((s z) ^ 2) ^ (2 ^ n) := by
                rw [show (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n from by rw [pow_succ]; ring]
                rw [pow_mul]
          _ = (βlevn (quadratic c z)) ^ (2 ^ n) := by rw [hssq z hz]
          _ = bottcherCoord c ((quadratic c)^[n] (quadratic c z)) := hβpow (quadratic c z) hfz
          _ = bottcherCoord c ((quadratic c)^[n + 1] z) := by
                rw [Function.iterate_succ_apply]
      · intro z hz hzero
        have hfz : quadratic c z ∈ escapeLevel c n := (quadratic_mapsTo_escapeLevel c n) hz
        have hβzero : βlevn (quadratic c z) = 0 := by
          rw [← hssq z hz, hzero]
          norm_num
        exact hβne (quadratic c z) hfz hβzero

/-- **Connected global branch from the pure iterate-image winding theorem.** This is the connected
Böttcher extension reduced to the exact topological-degree gap: prove the iterate image winding
divisibility, and the global single-valued branch follows. -/
theorem exists_global_branch_of_iterate_image_winding (c : ℂ)
    (hwindF : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ m : ℤ,
        wind (fun a : escapeLevel c (n + 1) => quadratic c ((quadratic c)^[n] (a : ℂ)))
          ((continuous_quadratic c).comp
            (((continuous_quadratic c).iterate n).comp continuous_subtype_val))
          (fun a => escapeOpen_coe_ne_zero c
            ⟨quadratic c ((quadratic c)^[n] (a : ℂ)), by
              have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
              rwa [Function.iterate_succ_apply'] at ha⟩) p =
          (2 : ℤ) ^ (n + 1) * m) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) :=
  exists_global_branch_of_levelRootInput c (levelRootInput_of_iterate_image_winding c hwindF)

/-- **Full connected branch from the pure iterate-image winding theorem.** This is the paper proof's
root/gluing/modulus/functional-equation endpoint, with the topological-degree winding statement left as
the only input. -/
theorem exists_global_branch_modulus_of_iterate_image_winding (c : ℂ)
    (hwindF : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ m : ℤ,
        wind (fun a : escapeLevel c (n + 1) => quadratic c ((quadratic c)^[n] (a : ℂ)))
          ((continuous_quadratic c).comp
            (((continuous_quadratic c).iterate n).comp continuous_subtype_val))
          (fun a => escapeOpen_coe_ne_zero c
            ⟨quadratic c ((quadratic c)^[n] (a : ℂ)), by
              have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
              rwa [Function.iterate_succ_apply'] at ha⟩) p =
          (2 : ℤ) ^ (n + 1) * m) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
      (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
        β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) :=
  exists_global_branch_of_levelRootInput_modulus c
    (levelRootInput_of_iterate_image_winding c hwindF)

/-- **Connected global branch from exact `ρ`-lift endpoint control.** If every loop in
`escapeLevel c (n+1)` lifts through `ρ_{n+1}` with endpoint displacement in the dyadic period lattice
`2^(n+1)·2πi·ℤ`, then the connected Böttcher branch exists on the whole basin. This is the current
end-to-end formal route from the `ConnectedPi1` universal-cover statement to the analytic branch. -/
theorem exists_global_branch_of_rho_lift_endpoints (c : ℂ)
    (hc : ∀ n, c ∉ escapeLevel c n)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ), ∃ m : ℤ,
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ)) ∧
        (L (1 : I) : ℂ) - L (0 : I) =
          (((2 : ℤ) ^ (n + 1) * m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) :=
  exists_global_branch_of_iterate_image_winding c
    (iterate_image_winding_divisible_of_rho_lift_endpoints c hc hlift)

/-- **Full connected branch from exact `ρ`-lift endpoint control.** Exact dyadic endpoint lifts imply
the winding divisibility, and the full Böttcher branch data follows. -/
theorem exists_global_branch_modulus_of_rho_lift_endpoints (c : ℂ)
    (hc : ∀ n, c ∉ escapeLevel c n)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ), ∃ m : ℤ,
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ)) ∧
        (L (1 : I) : ℂ) - L (0 : I) =
          (((2 : ℤ) ^ (n + 1) * m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
      (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
        β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) :=
  exists_global_branch_modulus_of_iterate_image_winding c
    (iterate_image_winding_divisible_of_rho_lift_endpoints c hc hlift)

/-- **Connected global branch from exact `ρ`-lift endpoint control, for Mandelbrot parameters.**
The written proof's connected-lane input `c ∈ M` supplies the critical-value exclusion needed by the
`ρ` tower; the only remaining hypothesis here is the actual dyadic endpoint lift theorem. -/
theorem exists_global_branch_of_rho_lift_endpoints_of_mem_mandelbrot (c : ℂ)
    (hcM : c ∈ mandelbrot)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ), ∃ m : ℤ,
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ)) ∧
        (L (1 : I) : ℂ) - L (0 : I) =
          (((2 : ℤ) ^ (n + 1) * m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) :=
  exists_global_branch_of_rho_lift_endpoints c
    (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot (c := c) hcM) hlift

/-- **Full connected branch from exact `ρ`-lift endpoint control, for Mandelbrot parameters.** The
Mandelbrot hypothesis supplies the critical-value exclusion; exact endpoint lifts are the only remaining
geometric input. -/
theorem exists_global_branch_modulus_of_rho_lift_endpoints_of_mem_mandelbrot (c : ℂ)
    (hcM : c ∈ mandelbrot)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ), ∃ m : ℤ,
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ)) ∧
        (L (1 : I) : ℂ) - L (0 : I) =
          (((2 : ℤ) ^ (n + 1) * m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
      (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
        β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) :=
  exists_global_branch_modulus_of_rho_lift_endpoints c
    (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot (c := c) hcM) hlift

/-- **Connected global branch from `ρ` path lifts plus sheet-swap.** This is the same global branch
constructor with endpoint arithmetic discharged internally: path lifts through `ρ_{n+1}` and the
one-step anti-period of the `ρ` tower imply the iterate-image winding divisibility, hence the connected
Böttcher branch. -/
theorem exists_global_branch_of_rho_lifts_antiperiod (c : ℂ)
    (hc : ∀ n, c ∉ escapeLevel c n)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) :=
  exists_global_branch_of_iterate_image_winding c
    (iterate_image_winding_divisible_of_rho_lifts_antiperiod c hc hanti hlift)

/-- **Full connected branch from `ρ` path lifts plus sheet-swap.** Path lifting plus the one-step
anti-period gives dyadic endpoints, then the full Böttcher branch data follows. -/
theorem exists_global_branch_modulus_of_rho_lifts_antiperiod (c : ℂ)
    (hc : ∀ n, c ∉ escapeLevel c n)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
      (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
        β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) :=
  exists_global_branch_modulus_of_iterate_image_winding c
    (iterate_image_winding_divisible_of_rho_lifts_antiperiod c hc hanti hlift)

/-- **Connected global branch from `ρ` lifts plus sheet-swap, for Mandelbrot parameters.** This is the
proof's connected-case capstone in the current formal interface: `c ∈ M` supplies the critical-value
exclusion, while the remaining work is the exact `ρ` path-lift and anti-period package. -/
theorem exists_global_branch_of_rho_lifts_antiperiod_of_mem_mandelbrot (c : ℂ)
    (hcM : c ∈ mandelbrot)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) :=
  exists_global_branch_of_rho_lifts_antiperiod c
    (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot (c := c) hcM) hanti hlift

/-- **Full connected branch from `ρ` lifts plus sheet-swap, for Mandelbrot parameters.** This is the
strongest current connected-case formal endpoint: `c ∈ M` supplies the critical-value exclusion; the
remaining exact `ρ` lift and anti-period package supplies the topological winding. -/
theorem exists_global_branch_modulus_of_rho_lifts_antiperiod_of_mem_mandelbrot (c : ℂ)
    (hcM : c ∈ mandelbrot)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
      (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
        β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) :=
  exists_global_branch_modulus_of_rho_lifts_antiperiod c
    (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot (c := c) hcM) hanti hlift

/-- **Global connected branch is locally biholomorphic.** Once the connected-case critical value
exclusion is available, any global basin branch agreeing with the far-field Böttcher coordinate has
nonzero complex derivative throughout the basin. Choose an escape level containing `z`; locally,
`bottcherCoord c ∘ f_c^[n] = β^(2^n)`. Differentiating gives a nonzero left side: the far-field
Böttcher derivative is nonzero, and the derivative of `f_c^[n]` avoids the precritical orbit because a
hit of `0` before level `n` would put the critical value `c` in an earlier escape level. Therefore
`β' z` cannot vanish. This is the formal version of the written proof's line differentiating
`β^(2^n)=Φ∘f^n` to show that the extended Böttcher map is unbranched. -/
theorem global_branch_deriv_ne_zero_of_criticalValue_not_escape {c : ℂ} {β : ℂ → ℂ}
    (hc : ∀ n, c ∉ escapeLevel c n)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c, β z = bottcherCoord c z)
    (hFEiter : ∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
      β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) :
    ∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0 := by
  intro z hz
  rw [compl_filledJulia_eq_iUnion_level, Set.mem_iUnion] at hz
  obtain ⟨n, hzn⟩ := hz
  set F : ℂ → ℂ := fun w => bottcherCoord c ((quadratic c)^[n] w) with hFdef
  set G : ℂ → ℂ := fun w => (β w) ^ (2 ^ n) with hGdef
  have hlevel_basin : escapeLevel c n ⊆ (filledJulia c)ᶜ := by
    rw [compl_filledJulia_eq_iUnion_level]
    exact Set.subset_iUnion (fun n => escapeLevel c n) n
  have hFG : F =ᶠ[𝓝 z] G := by
    filter_upwards [(isOpen_escapeLevel c n).mem_nhds hzn] with w hw
    have hwb : w ∈ (filledJulia c)ᶜ := hlevel_basin hw
    have hfw : (quadratic c)^[n] w ∈ escapeOpen c := hw
    change bottcherCoord c ((quadratic c)^[n] w) = (β w) ^ (2 ^ n)
    rw [← hβesc ((quadratic c)^[n] w) hfw, hFEiter n w hwb]
  have hy : (quadratic c)^[n] z ∈ escapeOpen c := hzn
  have hbc : HasDerivAt (bottcherCoord c) (deriv (bottcherCoord c) ((quadratic c)^[n] z))
      ((quadratic c)^[n] z) :=
    ((analyticOnNhd_bottcherCoord_full c) _ hy).differentiableAt.hasDerivAt
  have hiter : HasDerivAt ((quadratic c)^[n])
      (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) z :=
    (hasStrictDerivAt_quadratic_iterate c n z).hasDerivAt
  have hFder : HasDerivAt F
      (deriv (bottcherCoord c) ((quadratic c)^[n] z) *
        (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z)) z := by
    simpa [F, hFdef] using hbc.comp z hiter
  have hprod : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k hk
    refine mul_ne_zero (by norm_num) ?_
    intro hzero
    have hklt : k < n := Finset.mem_range.mp hk
    have hesc : (quadratic c)^[n] z ∈ escapeOpen c := hzn
    have hn_eq : n = (n - k) + k := by omega
    have hesc0 : (quadratic c)^[n - k] (0 : ℂ) ∈ escapeOpen c := by
      rw [hn_eq, Function.iterate_add_apply] at hesc
      rw [hzero] at hesc
      exact hesc
    let m : ℕ := n - k - 1
    have hd_eq : n - k = m + 1 := by
      dsimp [m]
      omega
    have hcrit : c ∈ escapeLevel c m := by
      show (quadratic c)^[m] c ∈ escapeOpen c
      have htmp : (quadratic c)^[m + 1] (0 : ℂ) ∈ escapeOpen c := by
        rwa [← hd_eq]
      rwa [Function.iterate_succ_apply, quadratic_apply,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] at htmp
    exact hc m hcrit
  have hFderiv_ne : deriv F z ≠ 0 := by
    rw [hFder.deriv]
    exact mul_ne_zero (deriv_bottcherCoord_ne_zero hy) hprod
  have hβder : HasDerivAt β (deriv β z) z :=
    (hβan z (hlevel_basin hzn)).differentiableAt.hasDerivAt
  have hGder : HasDerivAt G ((2 ^ n : ℕ) * (β z) ^ (2 ^ n - 1) * deriv β z) z := by
    simpa [G, hGdef] using hβder.pow (2 ^ n)
  intro hzero
  have hGderiv_zero : deriv G z = 0 := by
    rw [hGder.deriv, hzero]
    ring
  have hderiv_eq : deriv F z = deriv G z := hFG.deriv_eq
  exact hFderiv_ne (by rw [hderiv_eq, hGderiv_zero])

/-- **Nonzero derivative gives the local Böttcher inverse.** This is the local-biholomorphism
form of the written proof's unbranched conclusion: at every basin point where the global branch has
nonzero derivative, the holomorphic inverse function theorem supplies a local analytic inverse. -/
theorem exists_localInverse_global_branch_of_deriv_ne_zero {c : ℂ} {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβder : ∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ (filledJulia c)ᶜ) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ (β z₀) ∧
      (∀ᶠ z in 𝓝 z₀, ψ (β z) = z) ∧
      (∀ᶠ w in 𝓝 (β z₀), β (ψ w) = w) := by
  have han : AnalyticAt ℂ β z₀ := hβan z₀ hz₀
  have hd0 : deriv β z₀ ≠ 0 := hβder z₀ hz₀
  have hsd : HasStrictDerivAt β (deriv β z₀) z₀ := han.hasStrictDerivAt
  refine ⟨hsd.localInverse _ _ _ hd0, ?_, ?_, ?_⟩
  · exact han.analyticAt_localInverse hd0
  · exact hsd.eventually_left_inverse hd0
  · exact hsd.eventually_right_inverse hd0

/-- **Compact subsets of the exterior disk sit in a closed annulus.** If `K ⊆ {w | 1 < ‖w‖}`
is compact, then for some `0 < a` and some `b`, every `w ∈ K` satisfies
`e^a ≤ ‖w‖ ≤ e^b`. This is the topological wrapper used in the properness step. -/
theorem exists_norm_annulus_of_isCompact_subset_unitExterior {K : Set ℂ}
    (hK : IsCompact K) (hKsub : K ⊆ {w : ℂ | 1 < ‖w‖}) :
    ∃ a b : ℝ, 0 < a ∧ K ⊆ {w : ℂ | Real.exp a ≤ ‖w‖ ∧ ‖w‖ ≤ Real.exp b} := by
  by_cases hne : K.Nonempty
  · obtain ⟨wmin, hwminK, hmin⟩ := hK.exists_isMinOn hne continuous_norm.continuousOn
    obtain ⟨wmax, hwmaxK, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    refine ⟨Real.log ‖wmin‖, Real.log ‖wmax‖, ?_, ?_⟩
    · exact Real.log_pos (hKsub hwminK)
    · intro w hwK
      have hwmin_pos : 0 < ‖wmin‖ := lt_trans zero_lt_one (hKsub hwminK)
      have hwmax_pos : 0 < ‖wmax‖ := lt_trans zero_lt_one (hKsub hwmaxK)
      constructor
      · simpa [Real.exp_log hwmin_pos] using hmin hwK
      · simpa [Real.exp_log hwmax_pos] using hmax hwK
  · refine ⟨1, 1, by norm_num, ?_⟩
    intro w hw
    exact False.elim (hne ⟨w, hw⟩)

/-- **Compact annulus preimages for the global branch.** This is the formal core of the written
properness step: if a compact value set `K` lies in an exterior annulus
`e^a ≤ ‖w‖ ≤ e^b` with `a > 0`, then its basin preimage under a global branch carrying the Green
modulus is compact. The proof identifies that preimage with a closed subset of the compact Green band
`{a ≤ G_c ≤ b}`. -/
theorem isCompact_global_branch_preimage_of_norm_annulus {c : ℂ} {β : ℂ → ℂ} {a b : ℝ}
    (ha : 0 < a)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    {K : Set ℂ} (hK : IsCompact K)
    (hKsub : K ⊆ {w : ℂ | Real.exp a ≤ ‖w‖ ∧ ‖w‖ ≤ Real.exp b}) :
    IsCompact ({z : ℂ | z ∈ (filledJulia c)ᶜ ∧ β z ∈ K}) := by
  have hbandCompact : IsCompact (greenBand c a b) := isCompact_greenBand c a b
  have hbandClosed : IsClosed (greenBand c a b) := isClosed_greenBand c a b
  have hbandBasin : greenBand c a b ⊆ (filledJulia c)ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzK
    have hG0 : greenFunctionDyn c z = 0 := (greenFunctionDyn_eq_zero_iff c z).mpr hzK
    have hapos : a ≤ 0 := by simpa [greenBand, hG0] using hz.1
    linarith
  have hcontBand : ContinuousOn β (greenBand c a b) :=
    (hβan.continuousOn).mono hbandBasin
  have hclosedPre : IsClosed ({z : ℂ | z ∈ greenBand c a b ∧ β z ∈ K}) := by
    simpa [Set.inter_comm, Set.setOf_and] using
      hcontBand.preimage_isClosed_of_isClosed hbandClosed hK.isClosed
  have hcompBandPre : IsCompact ({z : ℂ | z ∈ greenBand c a b ∧ β z ∈ K}) :=
    hbandCompact.of_isClosed_subset hclosedPre (by intro z hz; exact hz.1)
  convert hcompBandPre using 1
  ext z
  constructor
  · rintro ⟨hzbasin, hzK⟩
    have hzann := hKsub hzK
    have hmod := hβmod z hzbasin
    refine ⟨?_, hzK⟩
    constructor
    · exact Real.exp_le_exp.mp (by simpa [hmod] using hzann.1)
    · exact Real.exp_le_exp.mp (by simpa [hmod] using hzann.2)
  · rintro ⟨hzband, hzK⟩
    exact ⟨hbandBasin hzband, hzK⟩

/-- **Compact exterior preimages for the global branch.** A compact subset of the target exterior
`{w | 1 < ‖w‖}` has compact basin preimage under any global branch carrying the Green modulus. This is
the proof's properness compactness argument before packaging the codomain as the exterior-disk subtype. -/
theorem isCompact_global_branch_preimage_of_compact_unitExterior {c : ℂ} {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ {w : ℂ | 1 < ‖w‖}) :
    IsCompact ({z : ℂ | z ∈ (filledJulia c)ᶜ ∧ β z ∈ K}) := by
  obtain ⟨a, b, ha, hKann⟩ := exists_norm_annulus_of_isCompact_subset_unitExterior hK hKsub
  exact isCompact_global_branch_preimage_of_norm_annulus ha hβan hβmod hK hKann

/-- **Properness of the global branch as a map to the exterior disk.** This packages the compact
preimage argument in the exact subtype form used by the covering step: the basin-restricted map
`z ↦ β z : {z // z ∈ Ω_c} → {w // 1 < ‖w‖}` is proper whenever `β` is analytic on the basin and
carries the Green modulus. -/
theorem isProperMap_global_branch_to_unitExterior {c : ℂ} {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖) :
    IsProperMap (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
      (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) := by
  rw [isProperMap_iff_isCompact_preimage]
  constructor
  · apply Continuous.subtype_mk
    exact hβan.continuousOn.restrict
  · intro K hK
    let F : {z : ℂ // z ∈ (filledJulia c)ᶜ} → {w : ℂ // 1 < ‖w‖} :=
      fun z => ⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩
    change IsCompact (F ⁻¹' K)
    let Kamb : Set ℂ := Subtype.val '' K
    have hKamb : IsCompact Kamb := hK.image continuous_subtype_val
    have hKambSub : Kamb ⊆ {w : ℂ | 1 < ‖w‖} := by
      rintro w ⟨u, _huK, rfl⟩
      exact u.2
    have hpreAmb : IsCompact ({z : ℂ | z ∈ (filledJulia c)ᶜ ∧ β z ∈ Kamb}) :=
      isCompact_global_branch_preimage_of_compact_unitExterior hβan hβmod hKamb hKambSub
    have hpreImage : Subtype.val '' (F ⁻¹' K) =
        ({z : ℂ | z ∈ (filledJulia c)ᶜ ∧ β z ∈ Kamb}) := by
      ext z
      constructor
      · rintro ⟨x, hxK, rfl⟩
        exact ⟨x.2, ⟨F x, hxK, rfl⟩⟩
      · rintro ⟨hzbasin, hzKamb⟩
        rcases hzKamb with ⟨w, hwK, hwβ⟩
        refine ⟨⟨z, hzbasin⟩, ?_, rfl⟩
        have hFw : F ⟨z, hzbasin⟩ = w := by
          apply Subtype.ext
          exact hwβ.symm
        simpa [hFw]
    have hemb : Topology.IsEmbedding (Subtype.val : {z : ℂ // z ∈ (filledJulia c)ᶜ} → ℂ) :=
      Topology.IsEmbedding.subtypeVal
    exact hemb.isCompact_iff.mpr (by simpa [hpreImage] using hpreAmb)

/-- **The global branch is locally a homeomorphism on the basin.** Analyticity plus nonzero complex
derivative gives an ambient inverse-function-theorem chart at every basin point. -/
theorem isLocalHomeomorphOn_global_branch {c : ℂ} {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβder : ∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) :
    IsLocalHomeomorphOn β (filledJulia c)ᶜ := by
  intro z hz
  have hstr : HasStrictDerivAt β (deriv β z) z := (hβan z hz).hasStrictDerivAt
  have hfd := hstr.hasStrictFDerivAt_equiv (hβder z hz)
  exact ⟨hfd.toOpenPartialHomeomorph β, hfd.mem_toOpenPartialHomeomorph_source,
    (hfd.toOpenPartialHomeomorph_coe).symm⟩

/-- **The basin-to-exterior global branch is a local homeomorphism.** This transfers the ambient
inverse-function-theorem charts through the open source subtype `(filledJulia c)ᶜ` and the open target
subtype `{w | 1 < ‖w‖}`. -/
theorem isLocalHomeomorph_global_branch_to_unitExterior {c : ℂ} {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖)
    (hβder : ∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) :
    IsLocalHomeomorph (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
      (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) := by
  let F : {z : ℂ // z ∈ (filledJulia c)ᶜ} → {w : ℂ // 1 < ‖w‖} :=
    fun z => ⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩
  change IsLocalHomeomorph F
  have hvalTarget : IsLocalHomeomorph (Subtype.val : {w : ℂ // 1 < ‖w‖} → ℂ) :=
    (IsOpen.isOpenEmbedding_subtypeVal (isOpen_lt continuous_const continuous_norm)).isLocalHomeomorph
  have hvalSource : IsLocalHomeomorph (Subtype.val : {z : ℂ // z ∈ (filledJulia c)ᶜ} → ℂ) :=
    (IsOpen.isOpenEmbedding_subtypeVal (isClosed_filledJulia c).isOpen_compl).isLocalHomeomorph
  have hcomp : IsLocalHomeomorph ((Subtype.val : {w : ℂ // 1 < ‖w‖} → ℂ) ∘ F) := by
    have heq : (Subtype.val : {w : ℂ // 1 < ‖w‖} → ℂ) ∘ F =
        β ∘ (Subtype.val : {z : ℂ // z ∈ (filledJulia c)ᶜ} → ℂ) := rfl
    rw [heq, isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
    exact (isLocalHomeomorphOn_global_branch hβan hβder).comp
      hvalSource.isLocalHomeomorphOn (fun z _ => z.2)
  have hcont : Continuous F := by
    apply Continuous.subtype_mk
    exact hβan.continuousOn.restrict
  exact IsLocalHomeomorph.of_comp hcomp hvalTarget hcont

/-- **The global branch is an unbranched covering of the exterior disk.** This is the formal
proper-local-homeomorphism packaging of the proof's final covering step, before proving that the
covering degree is one. -/
theorem isCoveringMap_global_branch_to_unitExterior {c : ℂ} {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖)
    (hβder : ∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) :
    IsCoveringMap (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
      (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) :=
  isCoveringMap_of_isProperMap_of_isLocalHomeomorph
    (isLocalHomeomorph_global_branch_to_unitExterior hβan hβgt hβder)
    (isProperMap_global_branch_to_unitExterior hβan hβmod hβgt)

/-- **The global branch is onto the exterior disk.** A proper local homeomorphism has closed range
and is open; the target exterior `{w | 1 < ‖w‖}` is connected and the range is nonempty, hence the
range is all of the exterior. This formalizes the proof's open/closed image paragraph. -/
theorem surjective_global_branch_to_unitExterior {c : ℂ} {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖)
    (hβder : ∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) :
    Function.Surjective (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
      (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) := by
  let F : {z : ℂ // z ∈ (filledJulia c)ᶜ} → {w : ℂ // 1 < ‖w‖} :=
    fun z => ⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩
  change Function.Surjective F
  have hproper : IsProperMap F := isProperMap_global_branch_to_unitExterior hβan hβmod hβgt
  have hlocal : IsLocalHomeomorph F := isLocalHomeomorph_global_branch_to_unitExterior hβan hβgt hβder
  have hopen : IsOpen (Set.range F) := hlocal.isOpenMap.isOpen_range
  have hclosed : IsClosed (Set.range F) := hproper.isClosedMap.isClosed_range
  letI : ConnectedSpace {w : ℂ // 1 < ‖w‖} :=
    isConnected_iff_connectedSpace.mp
      ⟨nonempty_exterior (by norm_num : (0 : ℝ) < 1),
        isPreconnected_exterior (by norm_num : (0 : ℝ) < 1)⟩
  have hpre : IsPreconnected (Set.univ : Set {w : ℂ // 1 < ‖w‖}) := isPreconnected_univ
  have hsrc : Nonempty {z : ℂ // z ∈ (filledJulia c)ᶜ} := by
    refine ⟨⟨((max 2 ‖c‖ + 1 : ℝ) : ℂ), ?_⟩⟩
    rw [compl_filledJulia_eq_iUnion_level]
    exact Set.mem_iUnion.mpr ⟨0, deep_mem_escapeLevel c 0⟩
  have hnon : (Set.range F).Nonempty := by
    rcases hsrc with ⟨z⟩
    exact ⟨F z, z, rfl⟩
  have hcover : (Set.univ : Set {w : ℂ // 1 < ‖w‖}) ⊆ Set.range F ∪ (Set.range F)ᶜ := by
    intro w _hw
    by_cases hwF : w ∈ Set.range F
    · exact Or.inl hwF
    · exact Or.inr hwF
  rcases hpre.subset_or_subset hopen hclosed.isOpen_compl disjoint_compl_right hcover with hsub | hsub
  · intro w
    exact hsub (Set.mem_univ w)
  · exfalso
    obtain ⟨w, hw⟩ := hnon
    exact hsub (Set.mem_univ w) hw

/-- **Green compactness threshold.** Above a finite Green level, all points lie outside any prescribed
closed disk. This is the compactness input in the proof's final far-field uniqueness step: a very large
value of the global branch forces every preimage into the region where the original Böttcher coordinate
is known to be injective. -/
theorem exists_green_threshold_norm_gt (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ T : ℝ, ∀ z : ℂ, T < greenFunctionDyn c z → R < ‖z‖ := by
  have hcomp : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  have hne : (Metric.closedBall (0 : ℂ) R).Nonempty := by
    exact ⟨0, by simp [Metric.mem_closedBall, hR]⟩
  obtain ⟨zmax, _hzmax, hmax⟩ :=
    hcomp.exists_isMaxOn hne (continuous_greenFunctionDyn c).continuousOn
  refine ⟨greenFunctionDyn c zmax, ?_⟩
  intro z hzG
  by_contra hzR
  have hzball : z ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact not_lt.mp hzR
  have hle := hmax hzball
  exact (not_lt_of_ge hle) hzG

/-- **The exterior disk is path-connected.** This packages the target topology needed to propagate a
singleton fiber through a covering by monodromy. -/
theorem pathConnectedSpace_unitExterior : PathConnectedSpace {w : ℂ // 1 < ‖w‖} := by
  have hconn : IsConnected {w : ℂ | 1 < ‖w‖} :=
    isConnected_setOf_lt_norm (by norm_num : (0 : ℝ) ≤ 1)
  have hpath : IsPathConnected {w : ℂ | 1 < ‖w‖} := by
    exact ((isOpen_lt continuous_const continuous_norm).isConnected_iff_isPathConnected).mp hconn
  exact isPathConnected_iff_pathConnectedSpace.mp hpath

/-- **A covering with one subsingleton fiber over a path-connected target is injective.** Monodromy
along a path from the special fiber to any target fiber is bijective, so all fibers are subsingleton. -/
theorem injective_of_coveringMap_of_subsingleton_fiber
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [PathConnectedSpace X]
    {p : E → X} (hp : IsCoveringMap p) {x₀ : X}
    (hfiber : (p ⁻¹' {x₀}).Subsingleton) : Function.Injective p := by
  intro a b hab
  let γ : Path x₀ (p a) := PathConnectedSpace.somePath x₀ (p a)
  let γq : Path.Homotopic.Quotient x₀ (p a) := ⟦γ⟧
  have hsurj : Function.Surjective (hp.monodromy γq) := (hp.monodromy_bijective γq).2
  let ea : p ⁻¹' {p a} := ⟨a, by simp⟩
  let eb : p ⁻¹' {p a} := ⟨b, by simp [hab]⟩
  obtain ⟨a₀, ha₀⟩ := hsurj ea
  obtain ⟨b₀, hb₀⟩ := hsurj eb
  have h₀ : a₀ = b₀ := Subtype.ext (hfiber a₀.2 b₀.2)
  have he : ea = eb := by rw [← ha₀, ← hb₀, h₀]
  exact Subtype.ext_iff.mp he

/-- **The global branch has a far-field subsingleton fiber.** Choose a value with modulus
`exp(T)` above the compact Green threshold for a radius where `bottcherCoord` is injective. Any basin
preimage of that value has Green value `T`, hence lies in the far field; there `β = bottcherCoord`, so
far-field univalence makes the fiber subsingleton. -/
theorem exists_subsingleton_fiber_global_branch_to_unitExterior {c : ℂ} {β : ℂ → ℂ}
    (hβesc : ∀ z ∈ escapeOpen c, β z = bottcherCoord c z)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖) :
    ∃ w₀ : {w : ℂ // 1 < ‖w‖},
      ((fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
        (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) ⁻¹' {w₀}).Subsingleton := by
  let R : ℝ := 16 * ‖c‖ + 2 * max 2 ‖c‖ + 2
  have hR0 : 0 ≤ R := by
    dsimp [R]
    have hcn : 0 ≤ ‖c‖ := norm_nonneg c
    have hm : 0 ≤ max 2 ‖c‖ := le_trans (by norm_num) (le_max_left 2 ‖c‖)
    nlinarith
  have hR1 : 2 * max 2 ‖c‖ < R := by
    dsimp [R]
    have hcn : 0 ≤ ‖c‖ := norm_nonneg c
    nlinarith
  have hR2 : 16 * ‖c‖ < R ^ 2 := by
    dsimp [R]
    have hcn : 0 ≤ ‖c‖ := norm_nonneg c
    have hm2 : 2 ≤ max 2 ‖c‖ := le_max_left 2 ‖c‖
    nlinarith [sq_nonneg (16 * ‖c‖ + 2 * max 2 ‖c‖ + 2)]
  have hRgtMax : max 2 ‖c‖ < R := by
    have hm : 0 ≤ max 2 ‖c‖ := le_trans (by norm_num) (le_max_left 2 ‖c‖)
    nlinarith
  obtain ⟨T, hT⟩ := exists_green_threshold_norm_gt c R hR0
  let S : ℝ := max T 0 + 1
  let W : ℂ := ((Real.exp S : ℝ) : ℂ)
  have hSpos : 0 < S := by
    dsimp [S]
    have hmax0 : 0 ≤ max T 0 := le_max_right T 0
    nlinarith
  have hTltS : T < S := by
    dsimp [S]
    exact lt_of_le_of_lt (le_max_left T 0) (by linarith)
  have hWnorm : ‖W‖ = Real.exp S := by
    dsimp [W]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos S)]
  have hWgt : 1 < ‖W‖ := by
    rw [hWnorm]
    exact Real.one_lt_exp_iff.mpr hSpos
  refine ⟨⟨W, hWgt⟩, ?_⟩
  intro a ha b hb
  let F : {z : ℂ // z ∈ (filledJulia c)ᶜ} → {w : ℂ // 1 < ‖w‖} :=
    fun z => ⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩
  change F a ∈ ({⟨W, hWgt⟩} : Set {w : ℂ // 1 < ‖w‖}) at ha
  change F b ∈ ({⟨W, hWgt⟩} : Set {w : ℂ // 1 < ‖w‖}) at hb
  have haeq : β (a : ℂ) = W := by
    have h : F a = ⟨W, hWgt⟩ := by simpa using ha
    exact congrArg Subtype.val h
  have hbeq : β (b : ℂ) = W := by
    have h : F b = ⟨W, hWgt⟩ := by simpa using hb
    exact congrArg Subtype.val h
  have hGa : greenFunctionDyn c (a : ℂ) = S := by
    apply Real.exp_injective
    rw [← hβmod (a : ℂ) a.2, haeq, hWnorm]
  have hGb : greenFunctionDyn c (b : ℂ) = S := by
    apply Real.exp_injective
    rw [← hβmod (b : ℂ) b.2, hbeq, hWnorm]
  have haR : R < ‖(a : ℂ)‖ := by
    exact hT (a : ℂ) (by rw [hGa]; exact hTltS)
  have hbR : R < ‖(b : ℂ)‖ := by
    exact hT (b : ℂ) (by rw [hGb]; exact hTltS)
  have haEsc : (a : ℂ) ∈ escapeOpen c := by
    show max 2 ‖c‖ < ‖(a : ℂ)‖
    exact lt_trans hRgtMax haR
  have hbEsc : (b : ℂ) ∈ escapeOpen c := by
    show max 2 ‖c‖ < ‖(b : ℂ)‖
    exact lt_trans hRgtMax hbR
  have hbc : bottcherCoord c (a : ℂ) = bottcherCoord c (b : ℂ) := by
    calc
      bottcherCoord c (a : ℂ) = β (a : ℂ) := (hβesc (a : ℂ) haEsc).symm
      _ = W := haeq
      _ = β (b : ℂ) := hbeq.symm
      _ = bottcherCoord c (b : ℂ) := hβesc (b : ℂ) hbEsc
  have hab : (a : ℂ) = (b : ℂ) :=
    bottcherCoord_injOn_far hR1 hR2 haR hbR hbc
  exact Subtype.ext hab

/-- **The proper unbranched global branch is injective.** This formalizes the proof's final
"covering degree one" sentence: one far-field subsingleton fiber propagates to all fibers by covering
monodromy over the path-connected exterior disk. -/
theorem injective_global_branch_to_unitExterior {c : ℂ} {β : ℂ → ℂ}
    (hβesc : ∀ z ∈ escapeOpen c, β z = bottcherCoord c z)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖)
    (hcov : IsCoveringMap (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
      (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖}))) :
    Function.Injective (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
      (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) := by
  let F : {z : ℂ // z ∈ (filledJulia c)ᶜ} → {w : ℂ // 1 < ‖w‖} :=
    fun z => ⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩
  change Function.Injective F
  obtain ⟨w₀, hw₀⟩ :=
    exists_subsingleton_fiber_global_branch_to_unitExterior (c := c) (β := β)
      hβesc hβmod hβgt
  letI : PathConnectedSpace {w : ℂ // 1 < ‖w‖} := pathConnectedSpace_unitExterior
  exact injective_of_coveringMap_of_subsingleton_fiber (p := F) hcov hw₀

/-- **The global branch is bijective onto the exterior disk.** Properness plus nonzero derivative gives
the covering and open/closed-image surjectivity; the far-field singleton-fiber argument gives
injectivity. -/
theorem bijective_global_branch_to_unitExterior {c : ℂ} {β : ℂ → ℂ}
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c, β z = bottcherCoord c z)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖)
    (hβder : ∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) :
    Function.Bijective (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
      (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) := by
  refine ⟨?_, ?_⟩
  · exact injective_global_branch_to_unitExterior hβesc hβmod hβgt
      (isCoveringMap_global_branch_to_unitExterior hβan hβmod hβgt hβder)
  · exact surjective_global_branch_to_unitExterior hβan hβmod hβgt hβder

/-- **Strong connected branch endpoint from `ρ` lifts plus sheet-swap.** This strengthens the current
full endpoint by adding the local-biholomorphism datum `β' ≠ 0` on the basin. It still leaves exactly
the same genuine geometric hypotheses: `ρ` path lifting and the all-level anti-period. -/
theorem exists_global_branch_modulus_deriv_ne_zero_of_rho_lifts_antiperiod (c : ℂ)
    (hc : ∀ n, c ∉ escapeLevel c n)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
      (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
        β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) := by
  obtain ⟨β, hβan, hβesc, hβ0, hβmod, hβgt, hβFE, hβFEiter⟩ :=
    exists_global_branch_modulus_of_rho_lifts_antiperiod c hc hanti hlift
  exact ⟨β, hβan, hβesc, hβ0, hβmod, hβgt, hβFE, hβFEiter,
    global_branch_deriv_ne_zero_of_criticalValue_not_escape hc hβan hβesc hβFEiter⟩

/-- **Local-biholomorphic connected branch endpoint from `ρ` lifts plus sheet-swap.** This packages
the exact data needed before the proper-covering step of the Böttcher proof: the global branch,
its Green modulus and functional equation, nonzero derivative, and a local analytic inverse at every
basin point. -/
theorem exists_global_branch_modulus_localInverse_of_rho_lifts_antiperiod (c : ℂ)
    (hc : ∀ n, c ∉ escapeLevel c n)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
      (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
        β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ (β z) ∧
        (∀ᶠ w in 𝓝 z, ψ (β w) = w) ∧
        (∀ᶠ u in 𝓝 (β z), β (ψ u) = u)) := by
  obtain ⟨β, hβan, hβesc, hβ0, hβmod, hβgt, hβFE, hβFEiter, hβder⟩ :=
    exists_global_branch_modulus_deriv_ne_zero_of_rho_lifts_antiperiod c hc hanti hlift
  exact ⟨β, hβan, hβesc, hβ0, hβmod, hβgt, hβFE, hβFEiter, hβder,
    fun z hz => exists_localInverse_global_branch_of_deriv_ne_zero hβan hβder hz⟩

/-- **Covering-level connected branch endpoint from `ρ` lifts plus sheet-swap.** This reaches the
written proof's "proper unbranched covering of `{|w| > 1}`" stage. The only remaining hypotheses are
still the genuine geometric inputs: all-level `ρ` path lifting and sheet-swap/anti-periodicity. -/
theorem exists_global_branch_covering_of_rho_lifts_antiperiod (c : ℂ)
    (hc : ∀ n, c ∉ escapeLevel c n)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      ∃ hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖,
        (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
        (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
          β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) ∧
        (∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) ∧
        IsCoveringMap (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) := by
  obtain ⟨β, hβan, hβesc, hβ0, hβmod, hβgt, hβFE, hβFEiter, hβder⟩ :=
    exists_global_branch_modulus_deriv_ne_zero_of_rho_lifts_antiperiod c hc hanti hlift
  exact ⟨β, hβan, hβesc, hβ0, hβmod, hβgt, hβFE, hβFEiter, hβder,
    isCoveringMap_global_branch_to_unitExterior hβan hβmod hβgt hβder⟩

/-- **Bijective covering-level connected branch endpoint from `ρ` lifts plus sheet-swap.** This is the
written proof through the final "covering degree one" step: the branch is a proper unbranched covering
of the exterior disk and, by far-field uniqueness plus covering monodromy, that covering is bijective. -/
theorem exists_global_branch_covering_bijective_of_rho_lifts_antiperiod (c : ℂ)
    (hc : ∀ n, c ∉ escapeLevel c n)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      ∃ hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖,
        (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
        (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
          β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) ∧
        (∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) ∧
        IsCoveringMap (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) ∧
        Function.Bijective (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) := by
  obtain ⟨β, hβan, hβesc, hβ0, hβmod, hβgt, hβFE, hβFEiter, hβder⟩ :=
    exists_global_branch_modulus_deriv_ne_zero_of_rho_lifts_antiperiod c hc hanti hlift
  exact ⟨β, hβan, hβesc, hβ0, hβmod, hβgt, hβFE, hβFEiter, hβder,
    isCoveringMap_global_branch_to_unitExterior hβan hβmod hβgt hβder,
    bijective_global_branch_to_unitExterior hβan hβesc hβmod hβgt hβder⟩

/-- **Bijective connected branch endpoint from `ρ` covering data plus sheet-swap.** This replaces the
raw path-lift hypothesis by the standard covering-map data for the explicit maps
`ρ_n : coverPlane c → escapeLevel c n`: once those maps are surjective coverings, path lifting is
provided by mathlib and the connected Böttcher branch is bijective onto the exterior disk. -/
theorem exists_global_branch_covering_bijective_of_rho_covering_antiperiod (c : ℂ)
    (hc : ∀ n, c ∉ escapeLevel c n)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hcov : ∀ n : ℕ, IsCoveringMap (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c n (t : ℂ), rho_mem_escapeLevel c hc n t.2⟩ : escapeLevel c n))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      ∃ hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖,
        (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
        (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
          β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) ∧
        (∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) ∧
        IsCoveringMap (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) ∧
        Function.Bijective (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) :=
  exists_global_branch_covering_bijective_of_rho_lifts_antiperiod c hc hanti
    (fun n {a₀} p => rho_path_lifts_of_covering c hc (n + 1)
      (hcov (n + 1)) (rho_surjective_of_antiperiod c hc hanti (n + 1)) (a₀ := a₀) p)

/-- **Bijective connected branch endpoint from `ρ` coverings plus odd half-period winding.** This is
the proof-shaped version of `exists_global_branch_covering_bijective_of_rho_covering_antiperiod`: the
sheet swap is supplied by the odd winding of the explicit loops
`s ↦ rho_n(t + 2^n·2πi·s) - c`, matching the remaining topological-degree claim in the paper proof. -/
theorem exists_global_branch_covering_bijective_of_rho_covering_odd_shift_winding (c : ℂ)
    (hc : ∀ n, c ∉ escapeLevel c n)
    (hodd : ∀ n : ℕ, ∀ {t : ℂ}, ∀ ht : t ∈ coverPlane c,
      ∃ k : ℤ, Pi1CMinusZero.degZ ⟦rhoShiftLoop c hc n ht⟧ = 2 * k + 1)
    (hcov : ∀ n : ℕ, IsCoveringMap (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c n (t : ℂ), rho_mem_escapeLevel c hc n t.2⟩ : escapeLevel c n))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      ∃ hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖,
        (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
        (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
          β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) ∧
        (∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) ∧
        IsCoveringMap (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) ∧
        Function.Bijective (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) :=
  exists_global_branch_covering_bijective_of_rho_covering_antiperiod c hc
    (rho_antiperiod_of_odd_shift_winding_all (c := c) hc hodd) hcov

/-- **Strong connected branch endpoint for Mandelbrot parameters.** The Mandelbrot hypothesis supplies
the critical-value exclusion used both by the `ρ` tower and by the derivative-nonzero proof. -/
theorem exists_global_branch_modulus_deriv_ne_zero_of_rho_lifts_antiperiod_of_mem_mandelbrot (c : ℂ)
    (hcM : c ∈ mandelbrot)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
      (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
        β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) :=
  exists_global_branch_modulus_deriv_ne_zero_of_rho_lifts_antiperiod c
    (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot (c := c) hcM) hanti hlift

/-- **Local-biholomorphic connected branch endpoint for Mandelbrot parameters.** This is the
Mandelbrot-lane version of `exists_global_branch_modulus_localInverse_of_rho_lifts_antiperiod`. -/
theorem exists_global_branch_modulus_localInverse_of_rho_lifts_antiperiod_of_mem_mandelbrot (c : ℂ)
    (hcM : c ∈ mandelbrot)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
      (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
        β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ (β z) ∧
        (∀ᶠ w in 𝓝 z, ψ (β w) = w) ∧
        (∀ᶠ u in 𝓝 (β z), β (ψ u) = u)) :=
  exists_global_branch_modulus_localInverse_of_rho_lifts_antiperiod c
    (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot (c := c) hcM) hanti hlift

/-- **Covering-level connected branch endpoint for Mandelbrot parameters.** This is the connected
Böttcher proof through the proper unbranched covering stage, with `c ∈ M` supplying the critical-value
exclusion and the remaining inputs isolated as `ρ` path lifting plus all-level anti-periodicity. -/
theorem exists_global_branch_covering_of_rho_lifts_antiperiod_of_mem_mandelbrot (c : ℂ)
    (hcM : c ∈ mandelbrot)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      ∃ hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖,
        (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
        (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
          β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) ∧
        (∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) ∧
        IsCoveringMap (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) :=
  exists_global_branch_covering_of_rho_lifts_antiperiod c
    (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot (c := c) hcM) hanti hlift

/-- **Bijective covering-level connected branch endpoint for Mandelbrot parameters.** This packages the
current strongest connected-case endpoint: under the remaining `ρ` path-lift and all-level
anti-periodicity hypotheses, the global Böttcher branch is a bijective unbranched covering of the
exterior disk. -/
theorem exists_global_branch_covering_bijective_of_rho_lifts_antiperiod_of_mem_mandelbrot (c : ℂ)
    (hcM : c ∈ mandelbrot)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      ∃ hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖,
        (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
        (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
          β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) ∧
        (∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) ∧
        IsCoveringMap (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) ∧
        Function.Bijective (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) :=
  exists_global_branch_covering_bijective_of_rho_lifts_antiperiod c
    (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot (c := c) hcM) hanti hlift

/-- **Bijective connected branch endpoint from `ρ` covering data, for Mandelbrot parameters.** The
Mandelbrot hypothesis supplies the critical-value exclusion; the remaining inputs are now the explicit
`ρ_n` surjective covering maps and the all-level sheet-swap. -/
theorem exists_global_branch_covering_bijective_of_rho_covering_antiperiod_of_mem_mandelbrot (c : ℂ)
    (hcM : c ∈ mandelbrot)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hcov : ∀ n : ℕ, IsCoveringMap (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c n (t : ℂ),
        rho_mem_escapeLevel c (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot (c := c) hcM)
          n t.2⟩ : escapeLevel c n))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      ∃ hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖,
        (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
        (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
          β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) ∧
        (∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) ∧
        IsCoveringMap (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) ∧
        Function.Bijective (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) :=
  exists_global_branch_covering_bijective_of_rho_covering_antiperiod c
    (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot (c := c) hcM) hanti hcov

/-- **Bijective connected branch endpoint from `ρ` coverings plus odd half-period winding, for
Mandelbrot parameters.** The remaining hypotheses are now the two concrete formal gaps left by the
proof: the odd topological-degree computation for the `ρ` tower and the covering-map status of the
explicit `ρ_n` maps. -/
theorem exists_global_branch_covering_bijective_of_rho_covering_odd_shift_winding_of_mem_mandelbrot
    (c : ℂ) (hcM : c ∈ mandelbrot)
    (hodd : ∀ n : ℕ, ∀ {t : ℂ}, ∀ ht : t ∈ coverPlane c,
      ∃ k : ℤ,
        Pi1CMinusZero.degZ
          ⟦rhoShiftLoop c
            (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot (c := c) hcM) n ht⟧ =
          2 * k + 1)
    (hcov : ∀ n : ℕ, IsCoveringMap (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c n (t : ℂ),
        rho_mem_escapeLevel c
          (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot (c := c) hcM) n t.2⟩ :
        escapeLevel c n))) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      ∃ hβgt : ∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖,
        (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
        (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
          β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) ∧
        (∀ z ∈ (filledJulia c)ᶜ, deriv β z ≠ 0) ∧
        IsCoveringMap (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) ∧
        Function.Bijective (fun z : {z : ℂ // z ∈ (filledJulia c)ᶜ} =>
          (⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ : {w : ℂ // 1 < ‖w‖})) :=
  exists_global_branch_covering_bijective_of_rho_covering_odd_shift_winding c
    (criticalValue_not_mem_escapeLevels_of_mem_mandelbrot (c := c) hcM) hodd hcov

end Bottcher
