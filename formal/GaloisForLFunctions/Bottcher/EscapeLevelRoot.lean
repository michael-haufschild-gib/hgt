/-
# The escape-level square root from the winding criterion (connected Böttcher, non-simply-connected)

`BasinColimit.exists_sqrt_pullback_on_simplyConnected` builds the per-level square root branch
`(βnext)² = βlev n ∘ f` only on a **simply-connected** chart of `escapeLevel c (n+1)`; gluing the charts
across the connected (`π₁ = ℤ`) level is left as the "winding step" (`hagree` in
`exists_levelBranch_succ_of_chart_agreement`). For a *connected* filled Julia set the escape level is an
annulus, so the simply-connected hypothesis genuinely fails and the winding step is the whole content.

This file discharges that step with the covering-lift root of `CoveringRoot`: the square root exists on
the *entire* connected escape level (no chart cut, no matching points) as soon as the canonical winding
hypothesis holds — the `π₁`-image of `βlev n ∘ f` lands in the squares, i.e. the winding number of
`βlev n ∘ f` around the hole `K_c` is even. (It is: `f` is degree `2`, so this winding is `2 ·
wind(βlev n)`. That dynamical evenness is the remaining geometric input, now isolated as exactly the
`π₁` condition.)

New file (hRigid / connected lane). Deps: `CoveringRoot` + `BasinColimit`.
-/
import GaloisForLFunctions.Bottcher.CoveringRoot
import GaloisForLFunctions.Bottcher.BasinColimit
import GaloisForLFunctions.Bottcher.BottcherWinding

open Topology Complex

namespace Bottcher

/-- **Base escape-level image winding.** Every closed loop in `escapeLevel c 1` has quadratic image
with even winding in `escapeOpen c`. This is the first nontrivial instance of the connected
escape-level transport: the loop closes on the square-root cover `z ↦ z²+c`, so the downstairs winding
is even. -/
theorem escapeLevel_one_image_winding_even (c : ℂ) {a₀ : escapeLevel c 1}
    (p : Path a₀ a₀) :
    ∃ m : ℤ,
      wind (fun a : escapeLevel c 1 => quadratic c (a : ℂ))
        ((continuous_quadratic c).comp continuous_subtype_val)
        (fun a => escapeOpen_coe_ne_zero c
          ⟨quadratic c (a : ℂ), by
            have ha : (quadratic c)^[1] (a : ℂ) ∈ escapeOpen c := a.2
            simpa [Function.iterate_one] using ha⟩) p = 2 * m := by
  have hesc : ∀ a : escapeLevel c 1, quadratic c (a : ℂ) ∈ escapeOpen c := by
    intro a
    have ha : (quadratic c)^[1] (a : ℂ) ∈ escapeOpen c := a.2
    simpa [Function.iterate_one] using ha
  let hne : ∀ a : escapeLevel c 1, (a : ℂ) ≠ 0 := fun a => by
    intro ha
    have hbad := hesc a
    rw [ha] at hbad
    simp only [quadratic, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
      escapeOpen, Set.mem_setOf_eq] at hbad
    exact not_lt_of_ge (le_max_right 2 ‖c‖) hbad
  refine ⟨wind (fun a : escapeLevel c 1 => (a : ℂ)) continuous_subtype_val hne p, ?_⟩
  simpa [hesc, hne] using
    (wind_quadratic_of_image_escapeOpen c (fun a : escapeLevel c 1 => (a : ℂ))
      continuous_subtype_val hesc p)

/-- **Last-step winding recurrence on every escape level.** If a loop lies in `escapeLevel c (n+1)`,
then the final quadratic step doubles the winding of the `n`-th image loop:
`wind(f_c^[n+1]∘p) = 2 · wind(f_c^[n]∘p)`. This is the algebraic recurrence behind the desired
`2ⁿ⁺¹` divisibility; the remaining topological content is proving the previous image winding is already
dyadically divisible for loops that close through the whole tower. -/
theorem escapeLevel_wind_iterate_succ_eq_two_mul (c : ℂ) (n : ℕ)
    {a₀ : escapeLevel c (n + 1)} (p : Path a₀ a₀) :
    wind (fun a : escapeLevel c (n + 1) => quadratic c ((quadratic c)^[n] (a : ℂ)))
        ((continuous_quadratic c).comp
          (((continuous_quadratic c).iterate n).comp continuous_subtype_val))
        (fun a => escapeOpen_coe_ne_zero c
          ⟨quadratic c ((quadratic c)^[n] (a : ℂ)), by
            have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
            rwa [Function.iterate_succ_apply'] at ha⟩) p
      = 2 * wind (fun a : escapeLevel c (n + 1) => (quadratic c)^[n] (a : ℂ))
          (((continuous_quadratic c).iterate n).comp continuous_subtype_val)
          (fun a => by
            intro hzero
            have hbad : quadratic c ((quadratic c)^[n] (a : ℂ)) ∈ escapeOpen c := by
              have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
              rwa [Function.iterate_succ_apply'] at ha
            change (quadratic c)^[n] (a : ℂ) = 0 at hzero
            rw [hzero] at hbad
            simp only [quadratic, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
              escapeOpen, Set.mem_setOf_eq] at hbad
            exact not_lt_of_ge (le_max_right 2 ‖c‖) hbad) p := by
  have hesc : ∀ a : escapeLevel c (n + 1),
      quadratic c ((quadratic c)^[n] (a : ℂ)) ∈ escapeOpen c := by
    intro a
    have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
    rwa [Function.iterate_succ_apply'] at ha
  simpa [hesc] using
    (wind_quadratic_of_image_escapeOpen c
      (fun a : escapeLevel c (n + 1) => (quadratic c)^[n] (a : ℂ))
      (((continuous_quadratic c).iterate n).comp continuous_subtype_val) hesc p)

/-- **Every final iterate image loop has even winding.** This is the existential divisibility form of
`escapeLevel_wind_iterate_succ_eq_two_mul`: any loop in `escapeLevel c (n+1)` maps under `f_c^[n+1]`
to an even-winding loop in `escapeOpen c`. For `n = 0` this is
`escapeLevel_one_image_winding_even`; for higher `n` it is the last-step half of the full dyadic
divisibility still needed for the connected Böttcher tower. -/
theorem escapeLevel_iterate_image_winding_even (c : ℂ) (n : ℕ)
    {a₀ : escapeLevel c (n + 1)} (p : Path a₀ a₀) :
    ∃ m : ℤ,
      wind (fun a : escapeLevel c (n + 1) => quadratic c ((quadratic c)^[n] (a : ℂ)))
        ((continuous_quadratic c).comp
          (((continuous_quadratic c).iterate n).comp continuous_subtype_val))
        (fun a => escapeOpen_coe_ne_zero c
          ⟨quadratic c ((quadratic c)^[n] (a : ℂ)), by
            have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
            rwa [Function.iterate_succ_apply'] at ha⟩) p = 2 * m := by
  refine ⟨wind (fun a : escapeLevel c (n + 1) => (quadratic c)^[n] (a : ℂ))
    (((continuous_quadratic c).iterate n).comp continuous_subtype_val) (fun a => ?_) p, ?_⟩
  · intro hzero
    have hbad : quadratic c ((quadratic c)^[n] (a : ℂ)) ∈ escapeOpen c := by
      have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
      rwa [Function.iterate_succ_apply'] at ha
    change (quadratic c)^[n] (a : ℂ) = 0 at hzero
    rw [hzero] at hbad
    simp only [quadratic, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
      escapeOpen, Set.mem_setOf_eq] at hbad
    exact not_lt_of_ge (le_max_right 2 ‖c‖) hbad
  · exact escapeLevel_wind_iterate_succ_eq_two_mul c n p

/-- **Square-root descent on the whole connected escape level, from the winding criterion.** The
pullback `βlev n ∘ f` is analytic and nowhere-zero on `escapeLevel c (n+1)`
(`f(escapeLevel c (n+1)) ⊆ escapeLevel c n`). If its `π₁`-image lands in the squares of `π₁(ℂ*)` — the
winding-even hypothesis `hlift`, presented through the bundled nowhere-zero map `gSub = βlev n ∘ f` —
then it has a **single-valued analytic square root on all of `escapeLevel c (n+1)`**, with no
simply-connectedness assumption. This is the non-simply-connected generalisation of
`exists_sqrt_pullback_on_simplyConnected`: it removes the chart cut and the matching-point hypotheses,
replacing them with the one canonical winding condition. -/
theorem exists_sqrt_pullback_of_lift (c : ℂ) (n : ℕ)
    (βlevn : ℂ → ℂ) (hβan : AnalyticOnNhd ℂ βlevn (escapeLevel c n))
    (gSub : C(escapeLevel c (n + 1), {w : ℂ // w ≠ 0}))
    (hgSub : ∀ a : escapeLevel c (n + 1), (gSub a : ℂ) = βlevn (quadratic c a))
    {a₀ : escapeLevel c (n + 1)} {e₀ : {w : ℂ // w ≠ 0}}
    (he : (⟨(e₀ : ℂ) ^ (2 : ℕ), pow_ne_zero 2 e₀.2⟩ : {w : ℂ // w ≠ 0}) = gSub a₀)
    (hlift : (FundamentalGroup.map gSub a₀).range ≤
      (FundamentalGroup.mapOfEq
        ⟨fun x : {w : ℂ // w ≠ 0} => (⟨(x : ℂ) ^ (2 : ℕ), pow_ne_zero 2 x.2⟩ : {w : ℂ // w ≠ 0}),
          by fun_prop⟩ he).range) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (escapeLevel c (n + 1)) ∧
      ∀ z ∈ escapeLevel c (n + 1), (s z) ^ (2 : ℕ) = βlevn (quadratic c z) := by
  have hmaps : Set.MapsTo (quadratic c) (escapeLevel c (n + 1)) (escapeLevel c n) :=
    quadratic_mapsTo_escapeLevel c n
  -- the pullback `g = βlev n ∘ f`, analytic and nowhere-zero on the escape level
  have hgan : AnalyticOnNhd ℂ (fun z => βlevn (quadratic c z)) (escapeLevel c (n + 1)) := fun z hz =>
    (hβan _ (hmaps hz)).comp (analyticAt_quadratic c z)
  obtain ⟨s, hsan, hspow, _hsne⟩ :=
    exists_analyticOnNhd_pow_eq_of_lift (isOpen_escapeLevel c (n + 1))
      (isConnected_escapeLevel c (n + 1)) hgan (by norm_num : ((2 : ℕ) : ℂ) ≠ 0)
      gSub hgSub he hlift
  exact ⟨s, hsan, hspow⟩

/-- **Square-root descent on an escape level from even transported winding.** This is the same
successor square-root constructor as `exists_sqrt_pullback_of_lift`, but with the paper's annular-root
input exposed directly: every transported loop of `βlev n ∘ f` has even winding. The conversion to the
covering-lift `π₁` hypothesis is handled by `exists_analyticOnNhd_sq_eq_of_even_winding`. -/
theorem exists_sqrt_pullback_of_even_winding (c : ℂ) (n : ℕ)
    (βlevn : ℂ → ℂ) (hβan : AnalyticOnNhd ℂ βlevn (escapeLevel c n))
    (gSub : C(escapeLevel c (n + 1), {w : ℂ // w ≠ 0}))
    (hgSub : ∀ a : escapeLevel c (n + 1), (gSub a : ℂ) = βlevn (quadratic c a))
    {a₀ : escapeLevel c (n + 1)} {e₀ : {w : ℂ // w ≠ 0}}
    (he : (⟨(e₀ : ℂ) ^ (2 : ℕ), pow_ne_zero 2 e₀.2⟩ : {w : ℂ // w ≠ 0}) = gSub a₀)
    (hwind : ∀ p : Path a₀ a₀,
      Even (Pi1CMinusZero.degZ ⟦transLoop (fun a : escapeLevel c (n + 1) => (gSub a : ℂ))
        (continuous_subtype_val.comp gSub.continuous) (fun a => (gSub a).2) p⟧)) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (escapeLevel c (n + 1)) ∧
      ∀ z ∈ escapeLevel c (n + 1), (s z) ^ (2 : ℕ) = βlevn (quadratic c z) := by
  have hmaps : Set.MapsTo (quadratic c) (escapeLevel c (n + 1)) (escapeLevel c n) :=
    quadratic_mapsTo_escapeLevel c n
  have hgan : AnalyticOnNhd ℂ (fun z => βlevn (quadratic c z)) (escapeLevel c (n + 1)) := fun z hz =>
    (hβan _ (hmaps hz)).comp (analyticAt_quadratic c z)
  obtain ⟨s, hsan, hspow, _hsne⟩ :=
    exists_analyticOnNhd_sq_eq_of_even_winding (isOpen_escapeLevel c (n + 1))
      (isConnected_escapeLevel c (n + 1)) hgan gSub hgSub he hwind
  exact ⟨s, hsan, hspow⟩

/-- **Square-root descent from iterate-winding divisibility.** If the current level branch satisfies
the `2ⁿ`-power law and the iterate radicand `bottcherCoord ∘ f^[n+1]` winds in multiples of `2ⁿ⁺¹` on
every loop, then `βlev n ∘ f` has even transported winding by `wind_even_of_pow`, hence admits a
single-valued analytic square root on the successor escape level. This is the direct Lean form of the
answer-03/04 divisibility step. -/
theorem exists_sqrt_pullback_of_iterate_winding (c : ℂ) (n : ℕ)
    (βlevn : ℂ → ℂ) (hβan : AnalyticOnNhd ℂ βlevn (escapeLevel c n))
    (hβpow : ∀ z ∈ escapeLevel c n,
      (βlevn z) ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z))
    (gSub : C(escapeLevel c (n + 1), {w : ℂ // w ≠ 0}))
    (hgSub : ∀ a : escapeLevel c (n + 1), (gSub a : ℂ) = βlevn (quadratic c a))
    (HSub : C(escapeLevel c (n + 1), {w : ℂ // w ≠ 0}))
    (hHSub : ∀ a : escapeLevel c (n + 1),
      (HSub a : ℂ) = bottcherCoord c ((quadratic c)^[n + 1] (a : ℂ)))
    {a₀ : escapeLevel c (n + 1)} {e₀ : {w : ℂ // w ≠ 0}}
    (he : (⟨(e₀ : ℂ) ^ (2 : ℕ), pow_ne_zero 2 e₀.2⟩ : {w : ℂ // w ≠ 0}) = gSub a₀)
    (hwindH : ∀ p : Path a₀ a₀, ∃ m : ℤ,
      wind (fun a : escapeLevel c (n + 1) => (HSub a : ℂ))
        (continuous_subtype_val.comp HSub.continuous) (fun a => (HSub a).2) p =
        2 ^ (n + 1) * m) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (escapeLevel c (n + 1)) ∧
      ∀ z ∈ escapeLevel c (n + 1), (s z) ^ (2 : ℕ) = βlevn (quadratic c z) := by
  refine exists_sqrt_pullback_of_even_winding c n βlevn hβan gSub hgSub he ?_
  intro p
  obtain ⟨m, hm⟩ := hwindH p
  have hGpow : ∀ a : escapeLevel c (n + 1),
      (fun a : escapeLevel c (n + 1) => (gSub a : ℂ)) a ^ (2 ^ n) =
        (fun a : escapeLevel c (n + 1) => (HSub a : ℂ)) a := by
    intro a
    change (gSub a : ℂ) ^ (2 ^ n) = (HSub a : ℂ)
    rw [hgSub a, hHSub a]
    have hmaps : Set.MapsTo (quadratic c) (escapeLevel c (n + 1)) (escapeLevel c n) :=
      quadratic_mapsTo_escapeLevel c n
    rw [hβpow (quadratic c (a : ℂ)) (hmaps a.2)]
    rw [← Function.iterate_succ_apply (quadratic c) n (a : ℂ)]
  have hwindG := wind_even_of_pow n
    (fun a : escapeLevel c (n + 1) => (gSub a : ℂ))
    (fun a : escapeLevel c (n + 1) => (HSub a : ℂ))
    (continuous_subtype_val.comp gSub.continuous) (fun a => (gSub a).2)
    (continuous_subtype_val.comp HSub.continuous) (fun a => (HSub a).2) p m hGpow hm
  refine ⟨m, ?_⟩
  change wind (fun a : escapeLevel c (n + 1) => (gSub a : ℂ))
      (continuous_subtype_val.comp gSub.continuous) (fun a => (gSub a).2) p = m + m
  rw [hwindG]
  ring

/-- **Remove the Böttcher factor from the iterate-winding hypothesis.** If the iterate image loop
`FSub : escapeLevel c (n+1) → escapeOpen c` has winding divisible by `2ⁿ⁺¹`, then the corresponding
Böttcher loop `HSub = bottcherCoord c ∘ FSub` has the same divisibility. This uses
`wind_bottcherCoord_comp_eq_wind_coe`, so the remaining obligation is the pure topological-degree
statement for the iterate image in `escapeOpen`. -/
theorem iterate_bottcher_winding_divisible_of_image_winding (c : ℂ) (n : ℕ)
    (FSub : C(escapeLevel c (n + 1), escapeOpen c))
    (HSub : C(escapeLevel c (n + 1), {w : ℂ // w ≠ 0}))
    (hHSubF : ∀ a : escapeLevel c (n + 1), (HSub a : ℂ) = bottcherCoord c (FSub a : ℂ))
    {a₀ : escapeLevel c (n + 1)}
    (hwindF : ∀ p : Path a₀ a₀, ∃ m : ℤ,
      wind (fun a : escapeLevel c (n + 1) => (FSub a : ℂ))
        (continuous_subtype_val.comp FSub.continuous) (fun a => escapeOpen_coe_ne_zero c (FSub a)) p =
        2 ^ (n + 1) * m) :
    ∀ p : Path a₀ a₀, ∃ m : ℤ,
      wind (fun a : escapeLevel c (n + 1) => (HSub a : ℂ))
        (continuous_subtype_val.comp HSub.continuous) (fun a => (HSub a).2) p =
        2 ^ (n + 1) * m := by
  intro p
  obtain ⟨m, hm⟩ := hwindF p
  refine ⟨m, ?_⟩
  have hfun :
      (fun a : escapeLevel c (n + 1) => bottcherCoord c (FSub a : ℂ))
        = fun a : escapeLevel c (n + 1) => (HSub a : ℂ) := by
    funext a
    rw [hHSubF a]
  have hgB : Continuous (fun a : escapeLevel c (n + 1) => bottcherCoord c (FSub a : ℂ)) := by
    rw [hfun]
    exact continuous_subtype_val.comp HSub.continuous
  calc
    wind (fun a : escapeLevel c (n + 1) => (HSub a : ℂ))
        (continuous_subtype_val.comp HSub.continuous) (fun a => (HSub a).2) p
        = wind (fun a : escapeLevel c (n + 1) => bottcherCoord c (FSub a : ℂ)) hgB
            (fun _ => bottcherCoord_ne_zero c _) p := by
          exact wind_congr hfun.symm (continuous_subtype_val.comp HSub.continuous)
            (fun a => (HSub a).2) hgB (fun _ => bottcherCoord_ne_zero c _) p
    _ = wind (fun a : escapeLevel c (n + 1) => (FSub a : ℂ))
          (continuous_subtype_val.comp FSub.continuous) (fun a => escapeOpen_coe_ne_zero c (FSub a)) p :=
        wind_bottcherCoord_comp_eq_wind_coe c FSub p hgB
    _ = 2 ^ (n + 1) * m := hm

/-- **Square-root descent from pure iterate-image winding.** This is the answer-03/04 root step with the
Böttcher-coordinate winding already reduced away: the caller only has to prove that the image of each
loop under `(quadratic c)^[n+1]` winds in `escapeOpen c` by a multiple of `2ⁿ⁺¹`. -/
theorem exists_sqrt_pullback_of_iterate_image_winding (c : ℂ) (n : ℕ)
    (βlevn : ℂ → ℂ) (hβan : AnalyticOnNhd ℂ βlevn (escapeLevel c n))
    (hβpow : ∀ z ∈ escapeLevel c n,
      (βlevn z) ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z))
    (gSub : C(escapeLevel c (n + 1), {w : ℂ // w ≠ 0}))
    (hgSub : ∀ a : escapeLevel c (n + 1), (gSub a : ℂ) = βlevn (quadratic c a))
    (FSub : C(escapeLevel c (n + 1), escapeOpen c))
    (hFSub : ∀ a : escapeLevel c (n + 1),
      (FSub a : ℂ) = (quadratic c)^[n + 1] (a : ℂ))
    (HSub : C(escapeLevel c (n + 1), {w : ℂ // w ≠ 0}))
    (hHSubF : ∀ a : escapeLevel c (n + 1), (HSub a : ℂ) = bottcherCoord c (FSub a : ℂ))
    {a₀ : escapeLevel c (n + 1)} {e₀ : {w : ℂ // w ≠ 0}}
    (he : (⟨(e₀ : ℂ) ^ (2 : ℕ), pow_ne_zero 2 e₀.2⟩ : {w : ℂ // w ≠ 0}) = gSub a₀)
    (hwindF : ∀ p : Path a₀ a₀, ∃ m : ℤ,
      wind (fun a : escapeLevel c (n + 1) => (FSub a : ℂ))
        (continuous_subtype_val.comp FSub.continuous) (fun a => escapeOpen_coe_ne_zero c (FSub a)) p =
        2 ^ (n + 1) * m) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (escapeLevel c (n + 1)) ∧
      ∀ z ∈ escapeLevel c (n + 1), (s z) ^ (2 : ℕ) = βlevn (quadratic c z) := by
  refine exists_sqrt_pullback_of_iterate_winding c n βlevn hβan hβpow gSub hgSub HSub ?_ he ?_
  · intro a
    rw [hHSubF a, hFSub a]
  · exact iterate_bottcher_winding_divisible_of_image_winding c n FSub HSub hHSubF hwindF

/-- **The first connected escape-level root is unconditional.** The base branch
`β₀ = bottcherCoord c` on `escapeOpen c = escapeLevel c 0` pulls back to a single-valued analytic
square root on `escapeLevel c 1`. The only winding input is
`escapeLevel_one_image_winding_even`, the closed-lift parity for `z ↦ z²+c`. -/
theorem exists_level_one_sqrt_pullback (c : ℂ) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (escapeLevel c 1) ∧
      ∀ z ∈ escapeLevel c 1, (s z) ^ (2 : ℕ) = bottcherCoord c (quadratic c z) := by
  classical
  have hβan : AnalyticOnNhd ℂ (bottcherCoord c) (escapeLevel c 0) := by
    simpa [escapeLevel_zero] using analyticOnNhd_bottcherCoord_full c
  have hβpow : ∀ z ∈ escapeLevel c 0,
      (bottcherCoord c z) ^ (2 ^ (0 : ℕ)) = bottcherCoord c ((quadratic c)^[0] z) := by
    intro z hz
    simp
  have hesc : ∀ a : escapeLevel c 1, quadratic c (a : ℂ) ∈ escapeOpen c := by
    intro a
    have ha : (quadratic c)^[1] (a : ℂ) ∈ escapeOpen c := a.2
    simpa [Function.iterate_one] using ha
  let FSub : C(escapeLevel c 1, escapeOpen c) :=
    { toFun := fun a => ⟨quadratic c (a : ℂ), hesc a⟩
      continuous_toFun :=
        (((continuous_quadratic c).comp continuous_subtype_val).subtype_mk hesc) }
  let HSub : C(escapeLevel c 1, {w : ℂ // w ≠ 0}) :=
    { toFun := fun a => ⟨bottcherCoord c (FSub a : ℂ), bottcherCoord_ne_zero c _⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (analyticOnNhd_bottcherCoord_full c).continuousOn.comp_continuous
          (continuous_subtype_val.comp FSub.continuous) (fun a => (FSub a).2) }
  let a₀ : escapeLevel c 1 :=
    ⟨((max 2 ‖c‖ + 1 : ℝ) : ℂ), deep_mem_escapeLevel c 1⟩
  obtain ⟨e, hepow⟩ := IsAlgClosed.exists_pow_nat_eq (HSub a₀ : ℂ) (by norm_num : 0 < 2)
  have hene : e ≠ 0 := by
    intro he0
    have hzero : (HSub a₀ : ℂ) = 0 := by
      rw [← hepow, he0]
      norm_num
    exact (HSub a₀).2 hzero
  let e₀ : {w : ℂ // w ≠ 0} := ⟨e, hene⟩
  have he : (⟨(e₀ : ℂ) ^ (2 : ℕ), pow_ne_zero 2 e₀.2⟩ : {w : ℂ // w ≠ 0}) = HSub a₀ := by
    apply Subtype.ext
    exact hepow
  refine exists_sqrt_pullback_of_iterate_image_winding c 0 (bottcherCoord c) hβan hβpow
    HSub ?_ FSub ?_ HSub ?_ he ?_
  · intro a
    rfl
  · intro a
    simp [FSub]
  · intro a
    rfl
  · intro p
    obtain ⟨m, hm⟩ := escapeLevel_one_image_winding_even c p
    refine ⟨m, ?_⟩
    simpa [FSub] using hm

end Bottcher
