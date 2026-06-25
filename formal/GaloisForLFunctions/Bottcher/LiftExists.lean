/-
# Böttcher tower — the circle lift exists (covering path-lifting)

Assembles the continuous lift `γ : ℝ → ℂ` of the base circle `C(0,R)` through `f_c^[n]`, by lifting the
loop through the already-built covering `isCoveringMap_quadratic_iterate_restrict` (Mathlib
`IsCoveringMap.exists_path_lifts`). Choosing `R` past both gates of `LiftConstruction`, the base loop
lies in the covering base `(criticalValues)ᶜ` and its lift lands in `escapeOpen c`. The lift is built
over a slightly LONGER arc (`θ ∈ (-1, 2π+1)`) so that downstream it is differentiable on the *closed*
`[0,2π]` (endpoints interior to the arc), feeding `hasDerivAt_lift_of_continuousAt`.
-/
import GaloisForLFunctions.Bottcher.LiftConstruction
import GaloisForLFunctions.Bottcher.LiftPeriod
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.UnitInterval

open Complex Metric Set

namespace Bottcher

/-- **The continuous circle lift exists.** For some `R > max 2‖c‖`, there is a continuous `γ : ℝ → ℂ`
that lifts the base circle through `f_c^[n]` on the arc `θ ∈ (-1, 2π+1)`: `f_c^[n](γ θ) = circleMap 0 R
θ` and `γ θ ∈ escapeOpen c` there. Built by `IsCoveringMap.exists_path_lifts` on the covering
`isCoveringMap_quadratic_iterate_restrict`, with `R` past both `LiftConstruction` gates so the base
loop lies in `(criticalValues)ᶜ` and its preimages escape. Axiom-clean. -/
theorem exists_continuous_circle_lift (c : ℂ) (n : ℕ) :
    ∃ (R : ℝ) (γ : ℝ → ℂ),
      max 2 ‖c‖ < R ∧ Continuous γ ∧
      ∀ θ ∈ Set.Ioo (-(1 : ℝ)) (2 * Real.pi + 1),
        (quadratic c)^[n] (γ θ) = circleMap 0 R θ ∧ γ θ ∈ escapeOpen c := by
  obtain ⟨R₀, hR₀⟩ := exists_sphere_preimage_subset_escapeOpen c n
  obtain ⟨M, hM⟩ := exists_sphere_subset_noncritical c n
  set S₀ := ((quadratic c)^[n] '' {w | (quadraticPolyIterate c n).derivative.IsRoot w})ᶜ with hS₀
  set R := max (max R₀ M) (max 2 ‖c‖) + 1 with hRdef
  have hR2c : max 2 ‖c‖ < R := by
    have := le_max_right (max R₀ M) (max 2 ‖c‖); rw [hRdef]; linarith
  have hRR₀ : R₀ < R := by
    have h1 := le_max_left R₀ M
    have h2 := le_max_left (max R₀ M) (max 2 ‖c‖)
    rw [hRdef]; linarith
  have hRM : M < R := by
    have h1 := le_max_right R₀ M
    have h2 := le_max_left (max R₀ M) (max 2 ‖c‖)
    rw [hRdef]; linarith
  have hRpos : 0 < R := lt_of_le_of_lt (le_trans (by norm_num) (le_max_left 2 ‖c‖)) hR2c
  have hSsub : sphere (0 : ℂ) R ⊆ S₀ := hM R hRM
  have hbpmem : ∀ s : ℝ, circleMap 0 R s ∈ S₀ :=
    fun s => hSsub (circleMap_mem_sphere 0 hRpos.le s)
  -- base loop as a ContinuousMap into the covering base, parametrized over a longer arc
  let bp : C(unitInterval, ↥S₀) :=
    ⟨fun s => ⟨circleMap 0 R ((2 * Real.pi + 2) * (s : ℝ) - 1), hbpmem _⟩,
      ((continuous_circleMap 0 R).comp (by fun_prop)).subtype_mk _⟩
  -- basepoint: an `f_c^[n]`-preimage of the arc start, in the preimage subtype
  obtain ⟨z₀, hz₀⟩ := exists_iterate_eq c n
    (circleMap 0 R ((2 * Real.pi + 2) * ((0 : unitInterval) : ℝ) - 1))
  have hz₀S : z₀ ∈ (quadratic c)^[n] ⁻¹' S₀ := by
    show (quadratic c)^[n] z₀ ∈ S₀
    rw [hz₀]; exact hbpmem _
  have hbase : bp 0 = (S₀.restrictPreimage ((quadratic c)^[n])) ⟨z₀, hz₀S⟩ := by
    apply Subtype.ext
    rw [Set.restrictPreimage_coe]
    exact hz₀.symm
  obtain ⟨Γ, hΓeq, _hΓ0⟩ :=
    IsCoveringMap.exists_path_lifts (isCoveringMap_quadratic_iterate_restrict c n)
      bp ⟨z₀, hz₀S⟩ hbase
  refine ⟨R, fun θ => (Γ (projIcc 0 1 zero_le_one ((θ + 1) / (2 * Real.pi + 2)))).val,
    hR2c, ?_, ?_⟩
  · exact continuous_subtype_val.comp
      (Γ.continuous.comp (continuous_projIcc.comp (by fun_prop)))
  · intro θ hθ
    obtain ⟨hθ1, hθ2⟩ := hθ
    have hpi : (0 : ℝ) < 2 * Real.pi + 2 := by positivity
    have hpine : (2 * Real.pi + 2) ≠ 0 := hpi.ne'
    have hmem01 : (θ + 1) / (2 * Real.pi + 2) ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg (by linarith) (by positivity), ?_⟩
      rw [div_le_one hpi]; linarith
    have hρθ : projIcc (0 : ℝ) 1 zero_le_one ((θ + 1) / (2 * Real.pi + 2))
        = ⟨(θ + 1) / (2 * Real.pi + 2), hmem01⟩ := projIcc_of_mem _ hmem01
    have hval := congrArg Subtype.val
      (congrFun hΓeq (projIcc 0 1 zero_le_one ((θ + 1) / (2 * Real.pi + 2))))
    simp only [Function.comp_apply, Set.restrictPreimage_coe] at hval
    have harith : (2 * Real.pi + 2) * ((θ + 1) / (2 * Real.pi + 2)) - 1 = θ := by
      field_simp; ring
    have hlifteq : (quadratic c)^[n]
        (Γ (projIcc 0 1 zero_le_one ((θ + 1) / (2 * Real.pi + 2)))).val = circleMap 0 R θ := by
      rw [hval]
      show circleMap 0 R ((2 * Real.pi + 2)
        * ((projIcc (0 : ℝ) 1 zero_le_one ((θ + 1) / (2 * Real.pi + 2))) : ℝ) - 1)
        = circleMap 0 R θ
      rw [hρθ, harith]
    have hmem : (quadratic c)^[n]
        (Γ (projIcc 0 1 zero_le_one ((θ + 1) / (2 * Real.pi + 2)))).val ∈ sphere (0 : ℂ) R := by
      rw [hlifteq]; exact circleMap_mem_sphere 0 hRpos.le θ
    exact ⟨hlifteq, hR₀ R hRR₀ _ hmem⟩

/-- **The fractional dyadic period is realized unconditionally.** Combining the continuous circle lift
`exists_continuous_circle_lift` with the differentiability crux (`hasDerivAt_lift_of_continuousAt`,
velocity automatic via `hvel_of_diff_lift`) and `fractional_period_of_lift`: there is an `R` and a
differentiable lift `γ` of `C(0,R)` through `f_c^[n]` with `∮_γ d log φ_c = 2πi/2ⁿ`. NO hypotheses —
the order-`2ⁿ` dyadic monodromy multiplier exponent for the genuine `φ_c`, fully discharged. This is
the winding crux (#73) closed: the realized non-integer period that forces the `2ⁿ`-fold monodromy.
Axiom-clean. -/
theorem exists_circle_lift_period (c : ℂ) (n : ℕ) :
    ∃ (R : ℝ) (γ γ' : ℝ → ℂ),
      max 2 ‖c‖ < R ∧
      (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ)
        = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n := by
  obtain ⟨R, γ, hR, hγcont, hγprop⟩ := exists_continuous_circle_lift c n
  have huicc : Set.uIcc (0 : ℝ) (2 * Real.pi) = Set.Icc 0 (2 * Real.pi) :=
    Set.uIcc_of_le (by positivity)
  have hsub : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      θ ∈ Set.Ioo (-(1 : ℝ)) (2 * Real.pi + 1) := by
    intro θ hθ
    rw [huicc] at hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  refine ⟨R, γ,
    fun θ => (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] (γ θ))⁻¹ * deriv (circleMap 0 R) θ,
    hR, ?_⟩
  refine fractional_period_of_lift hR n (fun θ hθ => (hγprop θ (hsub θ hθ)).2)
    (fun θ hθ => (hγprop θ (hsub θ hθ)).1) (fun θ hθ => ?_)
  have hθ' : θ ∈ Set.Ioo (-(1 : ℝ)) (2 * Real.pi + 1) := hsub θ hθ
  obtain ⟨hlifteq, hesc⟩ := hγprop θ hθ'
  have hd : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] (γ θ)) ≠ 0 :=
    prod_two_mul_iterate_ne_zero_of_escapeOpen hesc n
  have hstrict : HasStrictDerivAt ((quadratic c)^[n])
      (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] (γ θ)) (γ θ) :=
    hasStrictDerivAt_quadratic_iterate c n (γ θ)
  have hcircderiv : HasDerivAt (circleMap 0 R) (deriv (circleMap 0 R) θ) θ :=
    (hasDerivAt_circleMap 0 R θ).differentiableAt.hasDerivAt
  have hev : (fun t => (quadratic c)^[n] (γ t)) =ᶠ[nhds θ] circleMap 0 R := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ'] with t ht using (hγprop t ht).1
  have hcomp : HasDerivAt (fun t => (quadratic c)^[n] (γ t)) (deriv (circleMap 0 R) θ) θ :=
    hcircderiv.congr_of_eventuallyEq hev
  have hγderiv : HasDerivAt γ
      ((∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] (γ θ))⁻¹ * deriv (circleMap 0 R) θ) θ :=
    hasDerivAt_lift_of_continuousAt hstrict hd hγcont.continuousAt rfl hcircderiv hev
  exact hvel_of_diff_lift
    (γ' := fun θ => (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] (γ θ))⁻¹ * deriv (circleMap 0 R) θ)
    hγderiv hcomp

/-- **Period → monodromy multiplier.** A differentiable nonvanishing path `φ` (e.g. `φ_c ∘ γ`) with a
single-valued log-antiderivative `L` of dyadic period `2πi/2ⁿ` has endpoint ratio
`φ(2π)/φ(0) = exp(2πi/2ⁿ)`. The closed-loop FTC (`exp_logDeriv_antiderivative`) reads the realized
fractional period off as the monodromy multiplier of the lifted Böttcher coordinate. Axiom-clean. -/
theorem multiplier_eq_exp_of_period {φ L : ℝ → ℂ} {n : ℕ}
    (hperiod : L (2 * Real.pi) - L 0 = 2 * (Real.pi : ℂ) * Complex.I / 2 ^ n)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), φ t ≠ 0)
    (hdφ : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), HasDerivAt φ (deriv φ t) t)
    (hL : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), HasDerivAt L (deriv φ t / φ t) t) :
    φ (2 * Real.pi) / φ 0 = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 2 ^ n) := by
  have h := exp_logDeriv_antiderivative (show (0 : ℝ) ≤ 2 * Real.pi by positivity) hφ hdφ hL
  rw [hperiod] at h
  exact h.symm

/-- **The dyadic multiplier is a primitive `2ⁿ`-th root of unity.** `exp(2πi/2ⁿ)` has order exactly
`2ⁿ` — the Kummer primitive root `ζ` that `q62_disconnected_kummer` requires. From
`Complex.isPrimitiveRoot_exp`. Axiom-clean. -/
theorem isPrimitiveRoot_dyadic_multiplier (n : ℕ) :
    IsPrimitiveRoot (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 2 ^ n)) (2 ^ n) := by
  have h := Complex.isPrimitiveRoot_exp (2 ^ n) (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
  have hcast : ((2 ^ n : ℕ) : ℂ) = (2 : ℂ) ^ n := by push_cast; ring
  rwa [hcast] at h

/-- **The differentiable circle lift exists.** Strengthening of `exists_continuous_circle_lift`: the
lift `γ` is differentiable on the closed `[0,2π]` (`HasDerivAt γ (γ' θ) θ`), with the explicit
derivative `γ' θ = (∏_{k<n} 2·f_c^[k](γ θ))⁻¹ · deriv(circleMap 0 R) θ` from the inverse function
theorem (`hasDerivAt_lift_of_continuousAt`). Exposes the differentiability + lift equation + escape
membership that the monodromy-multiplier reading (`multiplier_eq_exp_of_period`) and the
non-squareness step consume. Axiom-clean. -/
theorem exists_differentiable_circle_lift (c : ℂ) (n : ℕ) :
    ∃ (R : ℝ) (γ γ' : ℝ → ℂ),
      max 2 ‖c‖ < R ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), γ θ ∈ escapeOpen c) ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), (quadratic c)^[n] (γ θ) = circleMap 0 R θ) := by
  obtain ⟨R, γ, hR, hγcont, hγprop⟩ := exists_continuous_circle_lift c n
  have hsub : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      θ ∈ Set.Ioo (-(1 : ℝ)) (2 * Real.pi + 1) :=
    fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  refine ⟨R, γ,
    fun θ => (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] (γ θ))⁻¹ * deriv (circleMap 0 R) θ,
    hR, fun θ hθ => (hγprop θ (hsub θ hθ)).2, fun θ hθ => ?_,
    fun θ hθ => (hγprop θ (hsub θ hθ)).1⟩
  have hθ' := hsub θ hθ
  obtain ⟨hlifteq, hesc⟩ := hγprop θ hθ'
  have hd := prod_two_mul_iterate_ne_zero_of_escapeOpen hesc n
  have hstrict := hasStrictDerivAt_quadratic_iterate c n (γ θ)
  have hcircderiv : HasDerivAt (circleMap 0 R) (deriv (circleMap 0 R) θ) θ :=
    (hasDerivAt_circleMap 0 R θ).differentiableAt.hasDerivAt
  have hev : (fun t => (quadratic c)^[n] (γ t)) =ᶠ[nhds θ] circleMap 0 R := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ'] with t ht using (hγprop t ht).1
  exact hasDerivAt_lift_of_continuousAt hstrict hd hγcont.continuousAt rfl hcircderiv hev

/-- **Radical relation on the escape set (the Kummer `F^{2ᵏ} = i a` piece).** For `z ∈ escapeOpen c`,
`bottcherCoord c (f_c^[k] z) = (bottcherCoord c z)^{2ᵏ}` — the functional equation iterated. This is
exactly the radical relation the Kummer route consumes: with `F = bottcherCoord c` the cover
coordinate and `a` the germ of `bottcherCoord c ∘ f_c^[k]` in the base, `F^{2ᵏ} = i a`. So the radicand
of `X^{2ᵏ} − C a` is `F^{2ᵏ}`, and irreducibility ⟺ `a` not a square ⟺ the `2^{k-1}`-th root has the
dyadic monodromy `2πi/2ⁿ` (`exists_circle_lift_period`). Axiom-clean. -/
theorem bottcherCoord_iterate_escape {c z : ℂ} (hz : z ∈ escapeOpen c) (k : ℕ) :
    bottcherCoord c ((quadratic c)^[k] z) = (bottcherCoord c z) ^ (2 ^ k) := by
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz
  exact bottcherCoord_iterate hc hz2 k

end Bottcher
