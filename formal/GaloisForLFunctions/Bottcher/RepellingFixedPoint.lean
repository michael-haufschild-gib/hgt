/-
# A repelling fixed point lies on the Julia set (Montel/expansion)

The repelling-route obstruction `RelativeBranchFamily.false_of_repelling_branch_analytic` consumes a
repelling periodic point `z₀ ∈ J_{c₁}` — concretely, `z₀ ∈ filledJulia c₁` together with
`(𝓝[(filledJulia c₁)ᶜ] z₀).NeBot` (the basin accumulates at `z₀`, i.e. `z₀` is on the basin boundary
`∂K = J`). `PeriodicPoints.exists_repelling_fixed_point` already supplies a strictly repelling fixed point
in `K_c` for `c ≠ 1/4`; this file proves such a point is on the Julia set.

The mechanism is the classical Montel/expansion dichotomy: if a repelling fixed point `z₀` were interior to
`K_c`, a whole disk would have bounded orbits (`K_c` is bounded and forward-invariant), so the iterate family
`{f_c^[n]}` would be uniformly bounded there, hence **normal** (`MontelNormal.montel_subseq`); a uniform
limit of holomorphic functions has convergent derivatives (`TendstoLocallyUniformlyOn.deriv`), but
`(f_c^[n])'(z₀) = λ^n` with `‖λ‖ > 1` blows up — contradiction. So `z₀ ∉ interior K_c`, i.e.
`z₀ ∈ closure (K_c)ᶜ`, giving the `NeBot` datum the obstruction needs. This closes step (b) of the
repelling-cycle existence, with no Koenigs linearization required.
-/
import GaloisForLFunctions.Bottcher.PeriodicPoints
import GaloisForLFunctions.Bottcher.MontelNormal
import Mathlib.Analysis.Complex.LocallyUniformLimit

open Set Filter Topology Metric

namespace Bottcher

/-- A point of `K_c` stays in `K_c` under iteration (forward invariance of the filled Julia set). -/
theorem mem_filledJulia_iterate {c z : ℂ} (hz : z ∈ filledJulia c) (n : ℕ) :
    (quadratic c)^[n] z ∈ filledJulia c := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (mem_filledJulia_iff_quadratic_mem c _).mp ih

/-- The iterates `f_c^[n]` are entire (compositions of the polynomial `f_c`). -/
theorem differentiable_quadratic_iterate (c : ℂ) (n : ℕ) :
    Differentiable ℂ ((quadratic c)^[n]) := by
  induction n with
  | zero => exact differentiable_id
  | succ n ih =>
    rw [Function.iterate_succ']
    have hq : Differentiable ℂ (quadratic c) := by unfold quadratic; fun_prop
    exact hq.comp ih

/-- **A repelling fixed point is not in the interior of `K_c`.** If `ball z₀ R ⊆ K_c`, the iterates
`f_c^[n]` are uniformly bounded there (orbits stay in the bounded, forward-invariant `K_c`), hence form a
normal family (`montel_subseq`); a uniform limit's derivatives converge (`TendstoLocallyUniformlyOn.deriv`),
but `(f_c^[n])'(z₀) = (2z₀)^n` with `‖2z₀‖ > 1` blows up — contradiction. So `z₀ ∈ ∂K_c = J_c`. -/
theorem not_mem_interior_of_repelling_fixed {c z₀ : ℂ}
    (hfix : quadratic c z₀ = z₀) (hrep : 1 < ‖(2 : ℂ) * z₀‖) :
    z₀ ∉ interior (filledJulia c) := by
  intro hint
  obtain ⟨R, hR0, hRsub⟩ := Metric.isOpen_iff.mp isOpen_interior z₀ hint
  have hRK : ball z₀ R ⊆ filledJulia c := hRsub.trans interior_subset
  obtain ⟨C, hC⟩ := (isBounded_filledJulia c).exists_norm_le
  have hFdiff : ∀ n, DifferentiableOn ℂ ((quadratic c)^[n]) (ball z₀ R) :=
    fun n => (differentiable_quadratic_iterate c n).differentiableOn
  have hFbd : ∀ n, ∀ z ∈ ball z₀ R, ‖(quadratic c)^[n] z‖ ≤ C :=
    fun n z hz => hC _ (mem_filledJulia_iterate (hRK hz) n)
  set r : ℝ := R / 4 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hrR : r < R / 2 := by rw [hrdef]; linarith
  obtain ⟨φ, g, hφ, hconv, hg⟩ := montel_subseq (c := z₀) hr0 hrR hFdiff hFbd
  have hlu : TendstoLocallyUniformlyOn (fun k => (quadratic c)^[φ k]) g atTop (ball z₀ r) :=
    (hconv.mono ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hderivlu : TendstoLocallyUniformlyOn
      (deriv ∘ fun k => (quadratic c)^[φ k]) (deriv g) atTop (ball z₀ r) :=
    hlu.deriv (Filter.Eventually.of_forall fun k =>
      (hFdiff (φ k)).mono (ball_subset_ball (show r ≤ R by rw [hrdef]; linarith))) isOpen_ball
  have hderivtend : Tendsto (fun k => deriv ((quadratic c)^[φ k]) z₀) atTop (𝓝 (deriv g z₀)) :=
    hderivlu.tendsto_at (Metric.mem_ball_self hr0)
  have hf : HasDerivAt (quadratic c) ((2 : ℂ) * z₀) z₀ := by
    have h := (hasDerivAt_pow 2 z₀).add_const c
    have he : ((2 : ℕ) : ℂ) * z₀ ^ (2 - 1) = (2 : ℂ) * z₀ := by norm_num
    rw [he] at h
    exact h
  have hderivpow : ∀ k, deriv ((quadratic c)^[φ k]) z₀ = ((2 : ℂ) * z₀) ^ (φ k) :=
    fun k => (HasDerivAt.iterate z₀ hf hfix (φ k)).deriv
  rw [show (fun k => deriv ((quadratic c)^[φ k]) z₀)
        = fun k => ((2 : ℂ) * z₀) ^ (φ k) from funext hderivpow] at hderivtend
  have hnormtend : Tendsto (fun k => ‖((2 : ℂ) * z₀) ^ (φ k)‖) atTop (𝓝 ‖deriv g z₀‖) :=
    hderivtend.norm
  have hblow : Tendsto (fun k => ‖((2 : ℂ) * z₀) ^ (φ k)‖) atTop atTop := by
    simp only [norm_pow]
    exact (tendsto_pow_atTop_atTop_of_one_lt hrep).comp hφ.tendsto_atTop
  exact not_tendsto_atTop_of_tendsto_nhds hnormtend hblow

/-- **A repelling fixed point lies on the basin boundary** (`𝓝[Ω_c] z₀ ≠ ⊥`): since `z₀ ∉ interior K_c`,
`z₀ ∈ closure (K_c)ᶜ = closure Ω_c`. This is exactly the `hNeBot` hypothesis of the repelling-route
obstruction `false_of_repelling_branch_analytic`. -/
theorem nhdsWithin_compl_filledJulia_neBot_of_repelling_fixed {c z₀ : ℂ}
    (hfix : quadratic c z₀ = z₀) (hrep : 1 < ‖(2 : ℂ) * z₀‖) :
    (𝓝[(filledJulia c)ᶜ] z₀).NeBot := by
  have hcl : z₀ ∈ closure (filledJulia c)ᶜ := by
    rw [closure_compl]; exact not_mem_interior_of_repelling_fixed hfix hrep
  exact mem_closure_iff_nhdsWithin_neBot.mp hcl

/-- **A repelling fixed point on the Julia set exists (`c ≠ 1/4`).** Combining
`PeriodicPoints.exists_repelling_fixed_point` (a strictly repelling fixed point in `K_c`) with the
basin-boundary fact above: for every `c ≠ 1/4` there is a fixed point `z₀` of `f_c` with multiplier
modulus `> 1` that lies on `J_c` (`z₀ ∈ K_c` and `𝓝[Ω_c] z₀ ≠ ⊥`). This realises steps (a)+(b) of the
repelling-cycle datum that `false_of_repelling_branch_analytic` consumes — a concrete period-1 repelling
point in the Julia set, for all non-exceptional `c ≠ 1/4`. The remaining data (non-resonance, location off
`filledJulia c₂`, simple-root of the relation) are the per-relation residue. -/
theorem exists_repelling_fixed_point_on_julia (c : ℂ) (hc : c ≠ 1 / 4) :
    ∃ z₀ : ℂ, quadratic c z₀ = z₀ ∧ z₀ ∈ filledJulia c ∧
      (𝓝[(filledJulia c)ᶜ] z₀).NeBot ∧ 1 < ‖(2 : ℂ) * z₀‖ := by
  obtain ⟨z₀, hfix, hmem, hrep⟩ := exists_repelling_fixed_point c hc
  exact ⟨z₀, hfix, hmem, nhdsWithin_compl_filledJulia_neBot_of_repelling_fixed hfix hrep, hrep⟩

end Bottcher

namespace Bottcher

/-- A filled-Julia point whose basin-side neighbourhood filter is nontrivial is on the frontier. -/
theorem mem_frontier_of_mem_filledJulia_of_nhdsWithin_compl_neBot {c z₀ : ℂ}
    (hz : z₀ ∈ filledJulia c) (hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot) :
    z₀ ∈ frontier (filledJulia c) := by
  rw [frontier_eq_closure_inter_closure]
  exact ⟨subset_closure hz, mem_closure_iff_nhdsWithin_neBot.mpr hNeBot⟩

/-- A repelling fixed point lies on `frontier K_c`. -/
theorem mem_frontier_of_repelling_fixed {c z₀ : ℂ}
    (hfix : quadratic c z₀ = z₀) (hrep : 1 < ‖(2 : ℂ) * z₀‖) :
    z₀ ∈ frontier (filledJulia c) :=
  mem_frontier_of_mem_filledJulia_of_nhdsWithin_compl_neBot (mem_filledJulia_of_fixed hfix)
    (nhdsWithin_compl_filledJulia_neBot_of_repelling_fixed hfix hrep)

/-- A repelling fixed point on the frontier exists for every `c ≠ 1 / 4`. -/
theorem exists_repelling_fixed_point_on_frontier (c : ℂ) (hc : c ≠ 1 / 4) :
    ∃ z₀ : ℂ, quadratic c z₀ = z₀ ∧ z₀ ∈ frontier (filledJulia c) ∧
      1 < ‖(2 : ℂ) * z₀‖ := by
  obtain ⟨z₀, hfix, _hmem, _hNeBot, hrep⟩ := exists_repelling_fixed_point_on_julia c hc
  exact ⟨z₀, hfix, mem_frontier_of_repelling_fixed hfix hrep, hrep⟩

end Bottcher
