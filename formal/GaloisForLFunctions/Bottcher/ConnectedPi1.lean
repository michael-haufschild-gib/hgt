/-
# Toward `π₁(escapeLevel c n) ≅ ℤ` and the connected-case winding divisibility (`hlift`, #22)

In the connected case (`c ∉ escapeLevel c n` for all `n`, i.e. the critical value never escapes) the
quadratic `f = z²+c` restricts to a genuine degree-`2` **covering map** of escape-level subtypes
`escapeLevel c (n+1) → escapeLevel c n` (`isCoveringMap_quadratic_escapeLevel`, this file, upgrading the
`IsCoveringMapOn` of `EscapeCovering`). This is the foundational object for the covering-`π₁` route to
the winding-divisibility hypothesis `hlift`:

* `f` connected double cover ⟹ its monodromy `π₁(escapeLevel c n) → ℤ/2` is onto ⟹ `image f∗ = ` the
  index-`2` (even) subgroup;
* `π₁(escapeLevel c n) ≅ ℤ` inductively (base `Pi1EscapeOpen`), with `f∗(gen) = 2·gen`;
* hence every `f∗[ℓ]` is even, so `(βlev_n)∗ ∘ f∗` lands in the squares of `π₁(ℂ*)` — exactly the
  `hlift` consumed by `exists_levelRoot_of_lift` / `exists_sqrt_pullback_of_lift`.

The covering map and the homeomorphism identifying its domain with `escapeLevel c (n+1)` are built here.
-/
import GaloisForLFunctions.Bottcher.EscapeCovering
import GaloisForLFunctions.Bottcher.CoveringPi1
import GaloisForLFunctions.Bottcher.PeriodDoubling
import GaloisForLFunctions.Bottcher.CircleDegree
import GaloisForLFunctions.Bottcher.CoveringCancellation
import Mathlib.Analysis.Complex.CoveringMap

open Topology
open unitInterval Pi1CMinusZero

namespace Bottcher

/-- **`f = z²+c` is a covering map of escape-level subtypes.** In the connected case
(`c ∉ escapeLevel c n`), `(escapeLevel c n).restrictPreimage (quadratic c)` — whose domain is
`↑((quadratic c) ⁻¹' escapeLevel c n) = ↑(escapeLevel c (n+1))` (`escapeLevel_succ_eq_preimage`) — is a
genuine `IsCoveringMap` onto `↑(escapeLevel c n)`. Upgrades `isCoveringMapOn_quadratic_escapeLevel`. -/
theorem isCoveringMap_quadratic_escapeLevel (c : ℂ) (n : ℕ) (hc : c ∉ escapeLevel c n) :
    IsCoveringMap ((escapeLevel c n).restrictPreimage (quadratic c)) :=
  (isCoveringMapOn_quadratic_escapeLevel c n hc).isCoveringMap_restrictPreimage

/-- **Direct covering form of `f_c : escapeLevel (n+1) → escapeLevel n`.** The covering supplied by
`isCoveringMap_quadratic_escapeLevel` has domain `(quadratic c) ⁻¹' escapeLevel c n`; this transports
it across the already-proved identity `escapeLevel c (n+1) = (quadratic c) ⁻¹' escapeLevel c n`, giving
the exact subtype map used in the `ρ` tower. -/
theorem isCoveringMap_quadratic_escapeLevel_succ (c : ℂ) (n : ℕ)
    (hc : c ∉ escapeLevel c n) :
    IsCoveringMap (fun z : escapeLevel c (n + 1) =>
      (⟨quadratic c (z : ℂ), quadratic_mapsTo_escapeLevel c n z.2⟩ : escapeLevel c n)) := by
  let e : escapeLevel c (n + 1) ≃ₜ ((quadratic c) ⁻¹' escapeLevel c n) :=
    Homeomorph.setCongr (escapeLevel_succ_eq_preimage c n)
  have hcov : IsCoveringMap (((escapeLevel c n).restrictPreimage (quadratic c)) ∘ e) :=
    (isCoveringMap_quadratic_escapeLevel c n hc).comp_homeomorph e
  convert hcov using 1

/-- **The connected escape-level quadratic map is locally a homeomorphism.** This is the local
unbranched part of the connected-level covering, in the exact subtype form used downstream. -/
theorem isLocalHomeomorph_quadratic_escapeLevel_succ (c : ℂ) (n : ℕ)
    (hc : c ∉ escapeLevel c n) :
    IsLocalHomeomorph (fun z : escapeLevel c (n + 1) =>
      (⟨quadratic c (z : ℂ), quadratic_mapsTo_escapeLevel c n z.2⟩ : escapeLevel c n)) :=
  (isCoveringMap_quadratic_escapeLevel_succ c n hc).isLocalHomeomorph

/-- **Path lifting through the explicit `ρ_n` cover, once packaged as a covering map.** This removes
the opaque loop-lift hypothesis from the winding route: if the subtype map
`ρ_n : coverPlane c → escapeLevel c n` is a surjective covering map, then every path in
`escapeLevel c n` admits a lift to `coverPlane c`. -/
theorem rho_path_lifts_of_covering (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ)
    (hcov : IsCoveringMap (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c n (t : ℂ), rho_mem_escapeLevel c hc n t.2⟩ : escapeLevel c n)))
    (hsurj : Function.Surjective (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c n (t : ℂ), rho_mem_escapeLevel c hc n t.2⟩ : escapeLevel c n)))
    {a₀ : escapeLevel c n} (p : Path a₀ a₀) :
    ∃ L : C(I, ℂ),
      (∀ t : I, L t ∈ coverPlane c) ∧
      (∀ t : I, rho c n (L t) = (p t : ℂ)) := by
  let R : {t : ℂ // t ∈ coverPlane c} → escapeLevel c n :=
    fun t => ⟨rho c n (t : ℂ), rho_mem_escapeLevel c hc n t.2⟩
  change IsCoveringMap R at hcov
  change Function.Surjective R at hsurj
  obtain ⟨e₀, he₀⟩ := hsurj a₀
  have hstart : p.toContinuousMap 0 = R e₀ := by
    change p 0 = R e₀
    rw [p.source]
    exact he₀.symm
  let Γ : C(I, {t : ℂ // t ∈ coverPlane c}) := hcov.liftPath p.toContinuousMap e₀ hstart
  let L : C(I, ℂ) := ⟨fun t => (Γ t : ℂ), continuous_subtype_val.comp Γ.continuous⟩
  refine ⟨L, ?_, ?_⟩
  · intro t
    exact (Γ t).2
  · intro t
    have hlift := congr_fun (hcov.liftPath_lifts p.toContinuousMap e₀ hstart) t
    change R (Γ t) = p.toContinuousMap t at hlift
    exact congrArg Subtype.val hlift

/-- **Base covering datum for the `ρ` tower.** At level zero, `ρ₀ = exp`, and the target
`escapeLevel c 0` is exactly `escapeOpen c`; this is the already-formal exponential covering of the
far-field exterior. -/
theorem rho_covering_zero (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) :
    IsCoveringMap (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c 0 (t : ℂ), rho_mem_escapeLevel c hc 0 t.2⟩ : escapeLevel c 0)) := by
  simpa [coverPlane, rho_zero, escapeLevel_zero] using isCoveringMap_exp_escapeOpen c

/-- **Continuity of the explicit `ρ_n` subtype map.** This packages the analytic-on-neighbourhood
property of `ρ_n` into the topological map used by the covering route. -/
theorem rho_continuous (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) :
    Continuous (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c n (t : ℂ), rho_mem_escapeLevel c hc n t.2⟩ : escapeLevel c n)) := by
  apply Continuous.subtype_mk
  exact (rho_analytic c hc n).continuousOn.comp_continuous continuous_subtype_val (fun t => t.2)

/-- **Every `ρ_n : coverPlane c → escapeLevel c n` is locally a homeomorphism.** The base is the
exponential covering of the far-field exterior. The successor step uses
`quadratic ∘ ρ_{n+1} = ρ_n`: since the quadratic escape-level map is locally a homeomorphism and the
composition is locally a homeomorphism, mathlib's `IsLocalHomeomorph.of_comp` gives local
homeomorphy of `ρ_{n+1}`. This closes the local-unbranched half of the remaining `ρ_n` covering input;
the remaining covering work is to assemble evenly-covered neighborhoods from the dyadic fiber/period
structure. -/
theorem rho_isLocalHomeomorph (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) :
    ∀ n : ℕ, IsLocalHomeomorph (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c n (t : ℂ), rho_mem_escapeLevel c hc n t.2⟩ : escapeLevel c n)) := by
  intro n
  induction n with
  | zero => exact (rho_covering_zero c hc).isLocalHomeomorph
  | succ n ih =>
      let Rsucc : {t : ℂ // t ∈ coverPlane c} → escapeLevel c (n + 1) :=
        fun t => ⟨rho c (n + 1) (t : ℂ), rho_mem_escapeLevel c hc (n + 1) t.2⟩
      let Rn : {t : ℂ // t ∈ coverPlane c} → escapeLevel c n :=
        fun t => ⟨rho c n (t : ℂ), rho_mem_escapeLevel c hc n t.2⟩
      let Q : escapeLevel c (n + 1) → escapeLevel c n :=
        fun z => ⟨quadratic c (z : ℂ), quadratic_mapsTo_escapeLevel c n z.2⟩
      have hQ : IsLocalHomeomorph Q :=
        isLocalHomeomorph_quadratic_escapeLevel_succ c n (hc n)
      have hcont : Continuous Rsucc := rho_continuous c hc (n + 1)
      have hcomp_eq : Q ∘ Rsucc = Rn := by
        funext t
        apply Subtype.ext
        exact quadratic_rho_succ c hc n t.2
      have hcomp : IsLocalHomeomorph (Q ∘ Rsucc) := by
        rw [hcomp_eq]
        exact ih
      exact IsLocalHomeomorph.of_comp hcomp hQ hcont

/-- **Base surjectivity datum for the `ρ` tower.** At level zero, every far-field point has the
logarithmic lift `log z` through `ρ₀ = exp`. -/
theorem rho_surjective_zero (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) :
    Function.Surjective (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c 0 (t : ℂ), rho_mem_escapeLevel c hc 0 t.2⟩ : escapeLevel c 0)) := by
  intro z
  have hzesc : (z : ℂ) ∈ escapeOpen c := by
    rw [← escapeLevel_zero c]
    exact z.2
  have hzne : (z : ℂ) ≠ 0 := escapeOpen_coe_ne_zero c ⟨(z : ℂ), hzesc⟩
  refine ⟨⟨Complex.log (z : ℂ), ?_⟩, ?_⟩
  · change Complex.exp (Complex.log (z : ℂ)) ∈ escapeOpen c
    rwa [Complex.exp_log hzne]
  · apply Subtype.ext
    simp [rho_zero, Complex.exp_log hzne]

/-- **Surjectivity propagates up the `ρ` tower from sheet-swap.** Given a point `y` at level `n+1`,
lift `f_c(y)` through `ρ_n`. The next square-root lift lands at either `y` or `-y`; in the second case
the anti-period translation swaps sheets and lands at `y`. -/
theorem rho_surjective_succ_of_antiperiod (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (n : ℕ)
    (hsurj : Function.Surjective (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c n (t : ℂ), rho_mem_escapeLevel c hc n t.2⟩ : escapeLevel c n))) :
    Function.Surjective (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c (n + 1) (t : ℂ), rho_mem_escapeLevel c hc (n + 1) t.2⟩ :
        escapeLevel c (n + 1))) := by
  intro y
  let x : escapeLevel c n := ⟨quadratic c (y : ℂ), (quadratic_mapsTo_escapeLevel c n) y.2⟩
  obtain ⟨t, ht_eq⟩ := hsurj x
  have hrho_eq : rho c n (t : ℂ) = quadratic c (y : ℂ) := congrArg Subtype.val ht_eq
  have hquad : quadratic c (rho c (n + 1) (t : ℂ)) = quadratic c (y : ℂ) := by
    rw [quadratic_rho_succ c hc n t.2, hrho_eq]
  have hsq : (rho c (n + 1) (t : ℂ)) ^ 2 = (y : ℂ) ^ 2 := by
    rw [quadratic_apply, quadratic_apply] at hquad
    linear_combination hquad
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hsame | hneg
  · refine ⟨t, ?_⟩
    apply Subtype.ext
    exact hsame
  · let P : ℂ := ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
    have hPmem : (t : ℂ) + P ∈ coverPlane c := by
      dsimp [P]
      exact exp_add_im_mem t.2 (vshift_re_zero n)
    refine ⟨⟨(t : ℂ) + P, hPmem⟩, ?_⟩
    apply Subtype.ext
    dsimp [P]
    rw [hanti n t.2, hneg]
    simp

/-- **All `ρ_n` are surjective once the all-level sheet-swap is known.** The base is the exponential
covering of the far field; the successor step uses `rho_surjective_succ_of_antiperiod`. -/
theorem rho_surjective_of_antiperiod (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t) :
    ∀ n : ℕ, Function.Surjective (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c n (t : ℂ), rho_mem_escapeLevel c hc n t.2⟩ : escapeLevel c n)) := by
  intro n
  induction n with
  | zero => exact rho_surjective_zero c hc
  | succ n ih => exact rho_surjective_succ_of_antiperiod c hc hanti n ih

/-- **Every `ρ_n : coverPlane c → escapeLevel c n` is a covering map.** This closes the connected
branch Gap 2: it is exactly the `∀ n, IsCoveringMap ρ_n` input that
`exists_global_branch_covering_bijective_of_rho_covering_antiperiod_of_mem_mandelbrot` still assumed.
The base `ρ₀ = exp` is the exponential covering of the far field (`rho_covering_zero`). The successor
step uses `Q ∘ ρ_{n+1} = ρ_n` (`quadratic_rho_succ`): `Q` (the level-quadratic double cover) and
`Q ∘ ρ_{n+1} = ρ_n` (induction hypothesis) are covering maps, `ρ_{n+1}` is continuous and surjective,
so the left-cancellation lemma `isCoveringMap_of_comp_left` upgrades `ρ_{n+1}` to a covering map. The
Hausdorff/locally-connected side conditions hold because the escape levels are open subsets of `ℂ`. -/
theorem rho_isCoveringMap (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t) :
    ∀ n : ℕ, IsCoveringMap (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c n (t : ℂ), rho_mem_escapeLevel c hc n t.2⟩ : escapeLevel c n)) := by
  intro n
  induction n with
  | zero => exact rho_covering_zero c hc
  | succ n ih =>
      let Rsucc : {t : ℂ // t ∈ coverPlane c} → escapeLevel c (n + 1) :=
        fun t => ⟨rho c (n + 1) (t : ℂ), rho_mem_escapeLevel c hc (n + 1) t.2⟩
      let Rn : {t : ℂ // t ∈ coverPlane c} → escapeLevel c n :=
        fun t => ⟨rho c n (t : ℂ), rho_mem_escapeLevel c hc n t.2⟩
      let Q : escapeLevel c (n + 1) → escapeLevel c n :=
        fun z => ⟨quadratic c (z : ℂ), quadratic_mapsTo_escapeLevel c n z.2⟩
      haveI : LocallyConnectedSpace ↥(escapeLevel c n) :=
        (isOpen_escapeLevel c n).isOpenEmbedding_subtypeVal.locallyConnectedSpace
      have hQ : IsCoveringMap Q := isCoveringMap_quadratic_escapeLevel_succ c n (hc n)
      have hcont : Continuous Rsucc := rho_continuous c hc (n + 1)
      have hsurj : Function.Surjective Rsucc :=
        rho_surjective_of_antiperiod c hc hanti (n + 1)
      have hcomp_eq : Q ∘ Rsucc = Rn := by
        funext t; apply Subtype.ext; exact quadratic_rho_succ c hc n t.2
      have hcomp : IsCoveringMap (Q ∘ Rsucc) := by rw [hcomp_eq]; exact ih
      exact isCoveringMap_of_comp_left hcomp hQ hcont hsurj

/-- **Iterate-image winding from an explicit `ρ`-lift endpoint.** Suppose a loop in
`escapeLevel c (n+1)` lifts through the universal-cover candidate `ρ_{n+1}` to a path `L` in the
covering half-plane, and the endpoint displacement of `L` is a multiple of the dyadic period
`2^(n+1)·2πi`. Then the image loop under `f_c^[n+1]` has winding divisible by `2^(n+1)`.

This is the concrete bridge from the remaining exact-fiber statement for `ρ_{n+1}` to the
iterate-image winding hypothesis consumed by `levelRootInput_of_iterate_image_winding`. -/
theorem iterate_image_winding_of_rho_lift_endpoint (c : ℂ)
    (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ)
    {a₀ : escapeLevel c (n + 1)} (p : Path a₀ a₀) (L : C(I, ℂ))
    (hLmem : ∀ t : I, L t ∈ coverPlane c)
    (hLrho : ∀ t : I, rho c (n + 1) (L t) = (p t : ℂ)) (m : ℤ)
    (hLend : (L (1 : I) : ℂ) - L (0 : I) =
      (((2 : ℤ) ^ (n + 1) * m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :
    wind (fun a : escapeLevel c (n + 1) => quadratic c ((quadratic c)^[n] (a : ℂ)))
        ((continuous_quadratic c).comp
          (((continuous_quadratic c).iterate n).comp continuous_subtype_val))
        (fun a => escapeOpen_coe_ne_zero c
          ⟨quadratic c ((quadratic c)^[n] (a : ℂ)), by
            have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
            rwa [Function.iterate_succ_apply'] at ha⟩) p =
      (2 : ℤ) ^ (n + 1) * m := by
  let F : escapeLevel c (n + 1) → ℂ :=
    fun a => quadratic c ((quadratic c)^[n] (a : ℂ))
  let hFcont : Continuous F :=
    (continuous_quadratic c).comp
      (((continuous_quadratic c).iterate n).comp continuous_subtype_val)
  let hFne : ∀ a, F a ≠ 0 := fun a =>
    escapeOpen_coe_ne_zero c
      ⟨quadratic c ((quadratic c)^[n] (a : ℂ)), by
        have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
        rwa [Function.iterate_succ_apply'] at ha⟩
  have hF_exp : ∀ t : I, F (p t) = Complex.exp (L t) := by
    intro t
    calc
      F (p t) = (quadratic c)^[n + 1] (p t : ℂ) := by
        simp [F, Function.iterate_succ_apply']
      _ = (quadratic c)^[n + 1] (rho c (n + 1) (L t)) := by
        rw [hLrho t]
      _ = Complex.exp (L t) := iterate_quadratic_rho c hc (n + 1) (hLmem t)
  have hF_base : F a₀ = Complex.exp (L (0 : I)) := by
    calc
      F a₀ = F (p (0 : I)) := by rw [p.source]
      _ = Complex.exp (L (0 : I)) := hF_exp 0
  let Lnorm : C(I, ℂ) := ⟨fun t => L t - L (0 : I), by fun_prop⟩
  have hLift : pexp ∘ Lnorm = transLoop F hFcont hFne p := by
    funext t
    apply Subtype.ext
    show Complex.exp (L t - L (0 : I)) = F (p t) / F a₀
    rw [Complex.exp_sub, hF_exp t, hF_base]
  have hL0 : Lnorm (0 : I) = (e0 : ℂ) := by
    show L (0 : I) - L (0 : I) = (e0 : ℂ)
    simp [e0]
  have hL1 : (Lnorm (1 : I) : ℂ) =
      (((2 : ℤ) ^ (n + 1) * m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    exact hLend
  change degZ ⟦transLoop F hFcont hFne p⟧ = (2 : ℤ) ^ (n + 1) * m
  exact degZ_eq_of_lift (transLoop F hFcont hFne p) Lnorm hLift hL0
    ((2 : ℤ) ^ (n + 1) * m) hL1

/-- **Iterate-image winding from dyadic endpoint lifts for all loops.** This packages
`iterate_image_winding_of_rho_lift_endpoint` in exactly the hypothesis shape consumed by
`levelRootInput_of_iterate_image_winding`: each loop in `escapeLevel c (n+1)` must lift through
`ρ_{n+1}` with endpoint displacement in `2^(n+1)·2πi·ℤ`. -/
theorem iterate_image_winding_divisible_of_rho_lift_endpoints (c : ℂ)
    (hc : ∀ n, c ∉ escapeLevel c n)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ), ∃ m : ℤ,
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ)) ∧
        (L (1 : I) : ℂ) - L (0 : I) =
          (((2 : ℤ) ^ (n + 1) * m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :
    ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ m : ℤ,
        wind (fun a : escapeLevel c (n + 1) => quadratic c ((quadratic c)^[n] (a : ℂ)))
          ((continuous_quadratic c).comp
            (((continuous_quadratic c).iterate n).comp continuous_subtype_val))
          (fun a => escapeOpen_coe_ne_zero c
            ⟨quadratic c ((quadratic c)^[n] (a : ℂ)), by
              have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
              rwa [Function.iterate_succ_apply'] at ha⟩) p =
          (2 : ℤ) ^ (n + 1) * m := by
  intro n a₀ p
  obtain ⟨L, m, hLmem, hLrho, hLend⟩ := hlift n p
  refine ⟨m, ?_⟩
  exact iterate_image_winding_of_rho_lift_endpoint c hc n p L hLmem hLrho m hLend

/-- **Iterate-image winding from `ρ` path lifts plus sheet-swap.** If every escape-level loop lifts
through `ρ_{n+1}` and the tower has the one-step anti-period
`ρ_{m+1}(t+2^m·2πi) = -ρ_{m+1}(t)`, then the lift endpoint automatically lies in the dyadic endpoint
lattice by `rho_fiber_dyadic_of_antiperiod`; hence the iterate-image winding is divisible by
`2^(n+1)`. -/
theorem iterate_image_winding_divisible_of_rho_lifts_antiperiod (c : ℂ)
    (hc : ∀ n, c ∉ escapeLevel c n)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hlift : ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ))) :
    ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ m : ℤ,
        wind (fun a : escapeLevel c (n + 1) => quadratic c ((quadratic c)^[n] (a : ℂ)))
          ((continuous_quadratic c).comp
            (((continuous_quadratic c).iterate n).comp continuous_subtype_val))
          (fun a => escapeOpen_coe_ne_zero c
            ⟨quadratic c ((quadratic c)^[n] (a : ℂ)), by
              have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
              rwa [Function.iterate_succ_apply'] at ha⟩) p =
          (2 : ℤ) ^ (n + 1) * m := by
  intro n a₀ p
  obtain ⟨L, hLmem, hLrho⟩ := hlift n p
  have hendFiber : rho c (n + 1) (L (1 : I)) = rho c (n + 1) (L (0 : I)) := by
    rw [hLrho 1, hLrho 0]
    simp [p.source, p.target]
  obtain ⟨m, hLend⟩ :=
    rho_fiber_dyadic_of_antiperiod (c := c) hc hanti (n + 1) (hLmem 1) (hLmem 0) hendFiber
  refine ⟨m, ?_⟩
  exact iterate_image_winding_of_rho_lift_endpoint c hc n p L hLmem hLrho m hLend

/-- **Iterate-image winding from `ρ` as a surjective covering plus sheet-swap.** The remaining
topological input can be expressed as the explicit `ρ_n` maps being surjective covering maps; mathlib's
covering path-lifting then supplies the loop lifts consumed by
`iterate_image_winding_divisible_of_rho_lifts_antiperiod`. -/
theorem iterate_image_winding_divisible_of_rho_covering_antiperiod (c : ℂ)
    (hc : ∀ n, c ∉ escapeLevel c n)
    (hanti : ∀ n : ℕ, ∀ {t : ℂ}, t ∈ coverPlane c →
      rho c (n + 1) (t + ((2 ^ n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = -rho c (n + 1) t)
    (hcov : ∀ n : ℕ, IsCoveringMap (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c n (t : ℂ), rho_mem_escapeLevel c hc n t.2⟩ : escapeLevel c n))) :
    ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ m : ℤ,
        wind (fun a : escapeLevel c (n + 1) => quadratic c ((quadratic c)^[n] (a : ℂ)))
          ((continuous_quadratic c).comp
            (((continuous_quadratic c).iterate n).comp continuous_subtype_val))
          (fun a => escapeOpen_coe_ne_zero c
            ⟨quadratic c ((quadratic c)^[n] (a : ℂ)), by
              have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
              rwa [Function.iterate_succ_apply'] at ha⟩) p =
          (2 : ℤ) ^ (n + 1) * m :=
  iterate_image_winding_divisible_of_rho_lifts_antiperiod c hc hanti
    (fun n {a₀} p => rho_path_lifts_of_covering c hc (n + 1)
      (hcov (n + 1)) (rho_surjective_of_antiperiod c hc hanti (n + 1)) (a₀ := a₀) p)

/-- **Iterate-image winding from `ρ` coverings plus odd half-period winding.** This is the
same endpoint as `iterate_image_winding_divisible_of_rho_covering_antiperiod`, but its
sheet-swap input is the concrete odd-winding statement for the loops
`s ↦ rho_n(t + 2^n·2πi·s) - c`. -/
theorem iterate_image_winding_divisible_of_rho_covering_odd_shift_winding (c : ℂ)
    (hc : ∀ n, c ∉ escapeLevel c n)
    (hodd : ∀ n : ℕ, ∀ {t : ℂ}, ∀ ht : t ∈ coverPlane c,
      ∃ k : ℤ, degZ ⟦rhoShiftLoop c hc n ht⟧ = 2 * k + 1)
    (hcov : ∀ n : ℕ, IsCoveringMap (fun t : {t : ℂ // t ∈ coverPlane c} =>
      (⟨rho c n (t : ℂ), rho_mem_escapeLevel c hc n t.2⟩ : escapeLevel c n))) :
    ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ m : ℤ,
        wind (fun a : escapeLevel c (n + 1) => quadratic c ((quadratic c)^[n] (a : ℂ)))
          ((continuous_quadratic c).comp
            (((continuous_quadratic c).iterate n).comp continuous_subtype_val))
          (fun a => escapeOpen_coe_ne_zero c
            ⟨quadratic c ((quadratic c)^[n] (a : ℂ)), by
              have ha : (quadratic c)^[n + 1] (a : ℂ) ∈ escapeOpen c := a.2
              rwa [Function.iterate_succ_apply'] at ha⟩) p =
          (2 : ℤ) ^ (n + 1) * m :=
  iterate_image_winding_divisible_of_rho_covering_antiperiod c hc
    (rho_antiperiod_of_odd_shift_winding_all (c := c) hc hodd) hcov

end Bottcher
