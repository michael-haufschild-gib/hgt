/-
# Böttcher tower — toward constructing the circle lift through `f_c^[n]`

The winding crux (`LiftPeriod.fractional_period_of_lift`) needs a path `γ` in the escape set with
`f_c^[n] ∘ γ = C(0,R)`. Since `isCoveringMapOn_quadratic_iterate` already makes `f_c^[n]` an honest
covering over the complement of its (finite) critical values, the lift is obtained by lifting the
loop `C(0,R)` through that covering — provided two geometric facts, supplied here:

* `exists_sphere_subset_noncritical` — for `R` large, `C(0,R)` avoids the finite critical-value set,
  so it lies in the covering base and is liftable.
* `exists_sphere_preimage_subset_escapeOpen` — for `R` large, *every* preimage of `C(0,R)` under
  `f_c^[n]` lies in the escape set `escapeOpen c` (norms grow like `R^{1/2ⁿ} > max 2‖c‖`), so the lift
  automatically lands where `d log φ_c` is single-valued analytic.

Both are clean: the first from finiteness/boundedness of critical values, the second from the forward
norm bound `‖f_c(z)‖ ≤ ‖z‖² + ‖c‖` iterated (`escapeBound`).
-/
import GaloisForLFunctions.Bottcher.CoverConstruction
import GaloisForLFunctions.Bottcher.Winding

open Complex Metric

namespace Bottcher

/-- The forward orbit norm bound: the iterate of `t ↦ t² + ‖c‖` starting at `B`. If `‖z‖ ≤ B` then
`‖f_c^[n] z‖ ≤ escapeBound c B n`. -/
noncomputable def escapeBound (c : ℂ) (B : ℝ) : ℕ → ℝ := fun n => (fun t => t ^ (2 : ℕ) + ‖c‖)^[n] B

theorem escapeBound_succ (c : ℂ) (B : ℝ) (n : ℕ) :
    escapeBound c B (n + 1) = (escapeBound c B n) ^ (2 : ℕ) + ‖c‖ := by
  simp only [escapeBound, Function.iterate_succ_apply']

theorem escapeBound_nonneg (c : ℂ) {B : ℝ} (hB : 0 ≤ B) (n : ℕ) : 0 ≤ escapeBound c B n := by
  induction n with
  | zero => simpa [escapeBound] using hB
  | succ n ih => rw [escapeBound_succ]; positivity

/-- **Forward norm bound.** `‖z‖ ≤ B ⟹ ‖f_c^[n] z‖ ≤ escapeBound c B n`. The iterated triangle
inequality `‖z² + c‖ ≤ ‖z‖² + ‖c‖`, packaged as a clean monotone bound on the `n`-th iterate's norm.
This is what makes large circles' preimages escape. -/
theorem norm_iterate_le_escapeBound {c z : ℂ} {B : ℝ} (hB : ‖z‖ ≤ B) (n : ℕ) :
    ‖(quadratic c)^[n] z‖ ≤ escapeBound c B n := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg z) hB
  induction n with
  | zero => simpa [escapeBound] using hB
  | succ n ih =>
    rw [Function.iterate_succ_apply', quadratic_apply, escapeBound_succ]
    calc ‖((quadratic c)^[n] z) ^ (2 : ℕ) + c‖
        ≤ ‖((quadratic c)^[n] z) ^ (2 : ℕ)‖ + ‖c‖ := norm_add_le _ _
      _ = ‖(quadratic c)^[n] z‖ ^ (2 : ℕ) + ‖c‖ := by rw [norm_pow]
      _ ≤ (escapeBound c B n) ^ (2 : ℕ) + ‖c‖ := by gcongr

/-- **Preimages of large circles escape.** For `R` larger than the forward bound `escapeBound c
(max 2‖c‖) n`, every `z` with `f_c^[n] z ∈ C(0,R)` lies in `escapeOpen c`. So a lift of the base
circle through `f_c^[n]` — wherever it starts — stays inside the escape set, where `logDeriv φ_c` is
the single-valued analytic form integrated by `fractional_period_of_lift`. -/
theorem exists_sphere_preimage_subset_escapeOpen (c : ℂ) (n : ℕ) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ < R →
      ∀ z : ℂ, (quadratic c)^[n] z ∈ sphere (0 : ℂ) R → z ∈ escapeOpen c := by
  refine ⟨escapeBound c (max 2 ‖c‖) n, fun R hR z hz => ?_⟩
  have hzR : ‖(quadratic c)^[n] z‖ = R := mem_sphere_zero_iff_norm.mp hz
  by_contra hzn
  have hle : ‖z‖ ≤ max 2 ‖c‖ := by
    rw [escapeOpen, Set.mem_setOf_eq] at hzn
    exact not_lt.mp hzn
  have hb := norm_iterate_le_escapeBound (c := c) hle n
  rw [hzR] at hb
  linarith

/-- **Large circles lie in the covering base.** The critical values of `f_c^[n]` are finite
(`criticalValues_finite`), hence bounded; so for `R` past that bound the circle `C(0,R)` avoids them
entirely and lies in `(criticalValues)ᶜ`, the base over which `isCoveringMapOn_quadratic_iterate` is
an honest `2ⁿ`-fold covering. The base loop is therefore liftable. -/
theorem exists_sphere_subset_noncritical (c : ℂ) (n : ℕ) :
    ∃ M : ℝ, ∀ R : ℝ, M < R →
      sphere (0 : ℂ) R ⊆
        ((quadratic c)^[n] '' {w | (quadraticPolyIterate c n).derivative.IsRoot w})ᶜ := by
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
    (criticalValues_finite c n).isBounded
  refine ⟨M, fun R hR z hz hzc => ?_⟩
  have h1 : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
  have h2 : z ∈ closedBall (0 : ℂ) M := hM hzc
  rw [Metric.mem_closedBall, dist_zero_right] at h2
  linarith

/-- **Iterate factors are nonzero on the escape set.** For `z₀ ∈ escapeOpen c`, every orbit point
`f_c^[k] z₀` again escapes (`escapeOpen_iterate`), so has norm `> max 2‖c‖ ≥ 2 > 0`; hence the
covering-derivative `(f_c^[n])'(z₀) = ∏_{k<n} 2·f_c^[k] z₀ ≠ 0`. So every escape point is a
non-critical point of `f_c^[n]` — the local-section hypothesis is automatic there. -/
theorem prod_two_mul_iterate_ne_zero_of_escapeOpen {c z₀ : ℂ} (hz : z₀ ∈ escapeOpen c) (n : ℕ) :
    (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z₀) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro k _
  refine mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (fun h0 => ?_)
  have hmem : (quadratic c)^[k] z₀ ∈ escapeOpen c := escapeOpen_iterate hz k
  rw [escapeOpen, Set.mem_setOf_eq, h0, norm_zero] at hmem
  exact absurd hmem (not_lt.mpr (le_trans (by norm_num) (le_max_left 2 ‖c‖)))

/-- **Local analytic section of `f_c^[n]` (the differentiability seed of the lift).** At a non-critical
point `z₀` — `(f_c^[n])'(z₀) = ∏_{k<n} 2·f_c^[k] z₀ ≠ 0`, automatic on the escape set
(`prod_two_mul_iterate_ne_zero_of_escapeOpen`) — the inverse function theorem
(`HasStrictDerivAt.localInverse`/`.to_localInverse`) gives an analytic local right-inverse `ψ` of
`f_c^[n]`: it is differentiable at `f_c^[n] z₀` with derivative `(∏…)⁻¹`, sends `f_c^[n] z₀ ↦ z₀`, and
satisfies `f_c^[n](ψ w) = w` for `w` near `f_c^[n] z₀`. A continuous lift of the base circle through
`f_c^[n]` coincides locally with `ψ ∘ circleMap`, hence inherits `HasDerivAt` — discharging the
velocity hypothesis of `fractional_period_of_lift` via `hvel_of_diff_lift`. Axiom-clean. -/
theorem exists_analytic_local_section {c z₀ : ℂ} {n : ℕ}
    (hnc : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z₀) ≠ 0) :
    ∃ ψ : ℂ → ℂ,
      HasDerivAt ψ (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z₀)⁻¹ ((quadratic c)^[n] z₀) ∧
      ψ ((quadratic c)^[n] z₀) = z₀ ∧
      (∀ᶠ w in nhds ((quadratic c)^[n] z₀), (quadratic c)^[n] (ψ w) = w) := by
  have hf : HasStrictDerivAt ((quadratic c)^[n])
      (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z₀) z₀ :=
    hasStrictDerivAt_quadratic_iterate c n z₀
  exact ⟨HasStrictDerivAt.localInverse _ _ _ hf hnc,
    (hf.to_localInverse hnc).hasDerivAt,
    (hf.eventually_left_inverse hnc).self_of_nhds,
    hf.eventually_right_inverse hnc⟩

/-- **A continuous lift through a local biholomorphism is differentiable.** If `f` has a nonzero strict
derivative `d` at `z₀` (so it is a local biholomorphism there), `Γ` is a continuous lift with `Γ θ₀ =
z₀`, the base path `g = f ∘ Γ` is differentiable at `θ₀`, then `Γ` itself is differentiable at `θ₀`
with derivative `d⁻¹ · g'`. Proof: the local inverse `ψ = f⁻¹` (inverse function theorem) is analytic,
and continuity forces `Γ = ψ ∘ g` near `θ₀` (both are lifts of `g` through the locally-injective `f`,
agreeing at `θ₀`); `Γ` inherits `ψ ∘ g`'s derivative. This upgrades the *topological* circle lift
(`IsCoveringMap.exists_path_lifts`) to the *differentiable* lift that `fractional_period_of_lift`
needs — its velocity hypothesis is then automatic (`hvel_of_diff_lift`). Axiom-clean. -/
theorem hasDerivAt_lift_of_continuousAt {f : ℂ → ℂ} {Γ g : ℝ → ℂ} {z₀ d g' : ℂ} {θ₀ : ℝ}
    (hf : HasStrictDerivAt f d z₀) (hd : d ≠ 0)
    (hΓ : ContinuousAt Γ θ₀) (hΓ0 : Γ θ₀ = z₀)
    (hg : HasDerivAt g g' θ₀)
    (hfΓ : (fun θ => f (Γ θ)) =ᶠ[nhds θ₀] g) :
    HasDerivAt Γ (d⁻¹ * g') θ₀ := by
  set ψ := HasStrictDerivAt.localInverse f d z₀ hf hd with hψdef
  have hleft : ∀ᶠ x in nhds z₀, ψ (f x) = x := hf.eventually_left_inverse hd
  have hleft' : ∀ᶠ x in nhds (Γ θ₀), ψ (f x) = x := by rw [hΓ0]; exact hleft
  have h1 : ∀ᶠ θ in nhds θ₀, ψ (f (Γ θ)) = Γ θ := hΓ.eventually hleft'
  have hΓev : Γ =ᶠ[nhds θ₀] (fun θ => ψ (g θ)) := by
    filter_upwards [h1, hfΓ] with θ hθ1 hθ2
    rw [show g θ = f (Γ θ) from hθ2.symm]; exact hθ1.symm
  have hgz : g θ₀ = f z₀ := by
    have h : f (Γ θ₀) = g θ₀ := hfΓ.self_of_nhds
    rw [hΓ0] at h
    exact h.symm
  have hψderiv : HasDerivAt ψ d⁻¹ (f z₀) := (hf.to_localInverse hd).hasDerivAt
  have hcomp : HasDerivAt (fun θ => ψ (g θ)) (d⁻¹ * g') θ₀ :=
    (hgz.symm ▸ hψderiv).comp θ₀ hg
  exact hcomp.congr_of_eventuallyEq hΓev

/-- **`f_c^[n]` is surjective.** It is the evaluation of the degree-`2ⁿ` polynomial
`quadraticPolyIterate c n`, which over the algebraically closed `ℂ` takes every value (fundamental
theorem of algebra). So every `w` has an `f_c^[n]`-preimage. -/
theorem exists_iterate_eq (c : ℂ) (n : ℕ) (w : ℂ) :
    ∃ z : ℂ, (quadratic c)^[n] z = w := by
  have hnd : (quadraticPolyIterate c n - Polynomial.C w).natDegree = 2 ^ n := by
    rw [Polynomial.natDegree_sub_C, quadraticPolyIterate_natDegree]
  have hpos : 0 < (quadraticPolyIterate c n - Polynomial.C w).natDegree := by
    rw [hnd]; positivity
  obtain ⟨z, hz⟩ := Complex.exists_root (Polynomial.natDegree_pos_iff_degree_pos.mp hpos)
  refine ⟨z, ?_⟩
  rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C, quadraticPolyIterate_eval,
    sub_eq_zero] at hz
  exact hz

/-- **Starting basepoint for the circle lift.** For `R` past the escape gate, the surjective `f_c^[n]`
has a preimage `z₀ ∈ escapeOpen c` of the loop basepoint `(R : ℂ) ∈ C(0,R)`. This is the `Γ 0 = e₀`
datum that `IsCoveringMap.exists_path_lifts` requires. -/
theorem exists_escapeOpen_preimage_basepoint (c : ℂ) (n : ℕ) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ < R → 0 < R →
      ∃ z₀ : ℂ, z₀ ∈ escapeOpen c ∧ (quadratic c)^[n] z₀ = (R : ℂ) := by
  obtain ⟨R₀, hR₀⟩ := exists_sphere_preimage_subset_escapeOpen c n
  refine ⟨R₀, fun R hR hRpos => ?_⟩
  obtain ⟨z₀, hz₀⟩ := exists_iterate_eq c n (R : ℂ)
  refine ⟨z₀, hR₀ R hR z₀ ?_, hz₀⟩
  rw [hz₀, mem_sphere_zero_iff_norm]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]

end Bottcher
