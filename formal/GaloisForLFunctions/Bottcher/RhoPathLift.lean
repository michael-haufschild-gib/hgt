/-
# The `ρ` path-lift `hlift`, discharged for `c ∈ mandelbrot`

This closes the last topological input to the connected Böttcher branch. `hlift` asks that every loop
in `escapeLevel c (n+1)` lift through `ρ_{n+1}` to a path in `coverPlane c`. We supply it from three
now-available facts, with no missing mathematics:

* `ρ_{n+1}` is **surjective** onto `escapeLevel c (n+1)` (`rho_surjective_of_antiperiod`, fed by the
  anti-period that follows from the proven odd winding `hodd`);
* the **exp covering** `ℂ → ℂˣ` (`Complex.isCoveringMap_exp`) lifts the image loop `f^[n+1]∘p`, and
  the lift lands in `coverPlane c` because `exp` of it is `f^[n+1]∘p ∈ escapeOpen`;
* `f^[n+1]` is a **covering** `escapeLevel c(n+1) → escapeLevel c 0` (`IterateCovering`), so the two
  candidate lifts `ρ_{n+1}∘L` and `p` — equal after `f^[n+1]` and agreeing at `0` — coincide by
  covering lift-uniqueness (`IsCoveringMap.eq_of_comp_eq`).
-/
import GaloisForLFunctions.Bottcher.IterateCovering
import GaloisForLFunctions.Bottcher.ConnectedBranchMandelbrot
import Mathlib.Analysis.Complex.CoveringMap

open Topology unitInterval
namespace Bottcher
noncomputable section
variable {c : ℂ}

/-- `f^[n+1] z ∈ escapeLevel c 0` for `z ∈ escapeLevel c (n+1)`. -/
theorem iterate_succ_mapsTo_zero (c : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ escapeLevel c (n + 1)) :
    (quadratic c)^[n + 1] z ∈ escapeLevel c 0 := by
  show (quadratic c)^[0] ((quadratic c)^[n + 1] z) ∈ escapeOpen c
  rw [Function.iterate_zero, id]
  exact hz

/-- Subtype fibre of `f^[n+1] : escapeLevel c(n+1) → escapeLevel c 0` is finite. -/
theorem iterate_succ_fiber_finite_zero (c : ℂ) (n : ℕ) (w : escapeLevel c 0) :
    ((fun z : escapeLevel c (n + 1) =>
      (⟨(quadratic c)^[n + 1] (z : ℂ), iterate_succ_mapsTo_zero c n z.2⟩ : escapeLevel c 0))
        ⁻¹' {w}).Finite := by
  refine Set.Finite.of_finite_image ?_ (Subtype.val_injective.injOn)
  apply (quadratic_iterate_fiber_finite c (n + 1) (w : ℂ)).subset
  rintro u ⟨z, hz, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
  exact congrArg Subtype.val hz

/-- **`f^[n+1]` is a covering `escapeLevel c(n+1) → escapeLevel c 0`** (clean target type). -/
theorem isCoveringMap_iterate_succ_zero (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) (n : ℕ) :
    IsCoveringMap (fun z : escapeLevel c (n + 1) =>
      (⟨(quadratic c)^[n + 1] (z : ℂ), iterate_succ_mapsTo_zero c n z.2⟩ : escapeLevel c 0)) := by
  induction n with
  | zero =>
    have hfun : (fun z : escapeLevel c (0 + 1) =>
          (⟨(quadratic c)^[0 + 1] (z : ℂ), iterate_succ_mapsTo_zero c 0 z.2⟩ : escapeLevel c 0))
        = (fun z : escapeLevel c 1 =>
          (⟨quadratic c (z : ℂ), quadratic_mapsTo_escapeLevel c 0 z.2⟩ : escapeLevel c 0)) := by
      funext z
      apply Subtype.ext
      show (quadratic c)^[0 + 1] (z : ℂ) = quadratic c (z : ℂ)
      rw [Function.iterate_one]
    rw [hfun]
    exact isCoveringMap_quadratic_escapeLevel_succ c 0 (hc 0)
  | succ k ih =>
    have hfun : (fun z : escapeLevel c (k + 1 + 1) =>
          (⟨(quadratic c)^[k + 1 + 1] (z : ℂ), iterate_succ_mapsTo_zero c (k + 1) z.2⟩
            : escapeLevel c 0))
        = (fun z : escapeLevel c (k + 1) =>
            (⟨(quadratic c)^[k + 1] (z : ℂ), iterate_succ_mapsTo_zero c k z.2⟩ : escapeLevel c 0))
          ∘ (fun z : escapeLevel c (k + 1 + 1) =>
            (⟨quadratic c (z : ℂ), quadratic_mapsTo_escapeLevel c (k + 1) z.2⟩
              : escapeLevel c (k + 1))) := by
      funext z
      apply Subtype.ext
      show (quadratic c)^[k + 1 + 1] (z : ℂ) = (quadratic c)^[k + 1] (quadratic c (z : ℂ))
      rw [← Function.iterate_succ_apply]
    rw [hfun]
    exact isCoveringMap_comp
      (isCoveringMap_quadratic_escapeLevel_succ c (k + 1) (hc (k + 1)))
      ih
      (iterate_succ_fiber_finite_zero c k)

end
end Bottcher

namespace Bottcher
noncomputable section
variable {c : ℂ}

/-- **The `ρ` path-lift `hlift`, unconditionally for `c ∈ mandelbrot`.** Every loop `p` in
`escapeLevel c (n+1)` lifts through `ρ_{n+1}` to a path `L` in `coverPlane c`. Proof: surjectivity of
`ρ_{n+1}` fixes a base point `e₀` with `ρ_{n+1}(e₀)=a₀`; lift the loop `f^[n+1]∘p` through the exp
covering `ℂ → ℂˣ` to `L` (so `exp∘L = f^[n+1]∘p`, whence `L` lands in `coverPlane`); then `ρ_{n+1}∘L`
and `p` have equal `f^[n+1]`-image and agree at `0`, so are equal by covering lift-uniqueness. -/
theorem rho_pathLift_of_mem_mandelbrot (c : ℂ) (hcM : c ∈ mandelbrot) :
    ∀ n : ℕ, ∀ {a₀ : escapeLevel c (n + 1)}, ∀ p : Path a₀ a₀,
      ∃ L : C(I, ℂ),
        (∀ t : I, L t ∈ coverPlane c) ∧
        (∀ t : I, rho c (n + 1) (L t) = (p t : ℂ)) := by
  intro n a₀ p
  set hc := criticalValue_not_mem_escapeLevels_of_mem_mandelbrot hcM with hhc
  obtain ⟨e₀, he₀⟩ :=
    rho_surjective_of_antiperiod c hc (rho_antiperiod_of_mem_mandelbrot hcM) (n + 1) a₀
  have hemem : (e₀ : ℂ) ∈ coverPlane c := e₀.2
  have hrhoe : rho c (n + 1) (e₀ : ℂ) = (a₀ : ℂ) := congrArg Subtype.val he₀
  have hqne : ∀ t : I, (quadratic c)^[n + 1] ((p t : ℂ)) ≠ 0 := by
    intro t h0
    have hmem : (quadratic c)^[n + 1] ((p t : ℂ)) ∈ escapeOpen c := (p t).2
    rw [h0] at hmem
    simp only [escapeOpen, Set.mem_setOf_eq, norm_zero] at hmem
    have : (0 : ℝ) < max 2 ‖c‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    linarith
  let q : C(I, {w : ℂ // w ≠ 0}) :=
    ⟨fun t => ⟨(quadratic c)^[n + 1] ((p t : ℂ)), hqne t⟩, by
      apply Continuous.subtype_mk
      exact ((continuous_quadratic c).iterate (n + 1)).comp
        (continuous_subtype_val.comp p.continuous)⟩
  have hq0 : q 0 = ⟨Complex.exp (e₀ : ℂ), Complex.exp_ne_zero _⟩ := by
    apply Subtype.ext
    show (quadratic c)^[n + 1] ((p 0 : ℂ)) = Complex.exp (e₀ : ℂ)
    rw [p.source, ← hrhoe, iterate_quadratic_rho c hc (n + 1) hemem]
  have hexp := Complex.isCoveringMap_exp
  let L : C(I, ℂ) := hexp.liftPath q (e₀ : ℂ) hq0
  have hLexp : ∀ t : I, Complex.exp (L t) = (quadratic c)^[n + 1] ((p t : ℂ)) := by
    intro t
    exact congrArg Subtype.val (congrFun (hexp.liftPath_lifts q (e₀ : ℂ) hq0) t)
  have hLcover : ∀ t : I, (L t) ∈ coverPlane c := by
    intro t
    show Complex.exp (L t) ∈ escapeOpen c
    rw [hLexp t]; exact (p t).2
  have hcov0 := isCoveringMap_iterate_succ_zero c hc n
  have hg1cont : Continuous (fun t : I =>
      (⟨rho c (n + 1) (L t), rho_mem_escapeLevel c hc (n + 1) (hLcover t)⟩ : escapeLevel c (n + 1))) := by
    apply Continuous.subtype_mk
    exact (rho_analytic c hc (n + 1)).continuousOn.comp_continuous L.continuous hLcover
  have hFcomp : (fun z : escapeLevel c (n + 1) =>
        (⟨(quadratic c)^[n + 1] (z : ℂ), iterate_succ_mapsTo_zero c n z.2⟩ : escapeLevel c 0))
      ∘ (fun t : I =>
        (⟨rho c (n + 1) (L t), rho_mem_escapeLevel c hc (n + 1) (hLcover t)⟩ : escapeLevel c (n + 1)))
      = (fun z : escapeLevel c (n + 1) =>
        (⟨(quadratic c)^[n + 1] (z : ℂ), iterate_succ_mapsTo_zero c n z.2⟩ : escapeLevel c 0)) ∘ ⇑p := by
    funext t
    apply Subtype.ext
    show (quadratic c)^[n + 1] (rho c (n + 1) (L t)) = (quadratic c)^[n + 1] ((p t : ℂ))
    rw [iterate_quadratic_rho c hc (n + 1) (hLcover t)]
    exact hLexp t
  have hg120 : (fun t : I =>
        (⟨rho c (n + 1) (L t), rho_mem_escapeLevel c hc (n + 1) (hLcover t)⟩ : escapeLevel c (n + 1))) 0
      = p 0 := by
    apply Subtype.ext
    show rho c (n + 1) (L (0 : I)) = ((p 0 : escapeLevel c (n + 1)) : ℂ)
    have hL0 : L (0 : I) = (e₀ : ℂ) := hexp.liftPath_zero q (e₀ : ℂ) hq0
    rw [hL0, hrhoe, p.source]
  have heq := hcov0.eq_of_comp_eq hg1cont p.continuous hFcomp 0 hg120
  refine ⟨L, hLcover, fun t => ?_⟩
  exact congrArg Subtype.val (congrFun heq t)

end
end Bottcher

namespace Bottcher

noncomputable section

/-- **Connected Böttcher branch for `c ∈ mandelbrot` — no topological hypotheses.** Both the
anti-period sheet-swap (from the proven odd winding `hodd`) and the path-lift `hlift` (from
`rho_pathLift_of_mem_mandelbrot`) are now theorems, so the connected branch exists for every
Mandelbrot parameter with `c ∈ mandelbrot` as the sole input. -/
theorem exists_global_branch_of_mem_mandelbrot (c : ℂ) (hcM : c ∈ mandelbrot) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) :=
  exists_global_branch_of_mem_mandelbrot_of_rho_lifts c hcM
    (rho_pathLift_of_mem_mandelbrot c hcM)

/-- **Connected branch with full modulus / functional-equation data for `c ∈ mandelbrot`, no
topological hypotheses.** -/
theorem exists_global_branch_modulus_of_mem_mandelbrot (c : ℂ) (hcM : c ∈ mandelbrot) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β z ≠ 0) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
      (∀ p : ℕ, ∀ z ∈ (filledJulia c)ᶜ,
        β ((quadratic c)^[p] z) = (β z) ^ (2 ^ p)) :=
  exists_global_branch_modulus_of_mem_mandelbrot_of_rho_lifts c hcM
    (rho_pathLift_of_mem_mandelbrot c hcM)

end

end Bottcher
