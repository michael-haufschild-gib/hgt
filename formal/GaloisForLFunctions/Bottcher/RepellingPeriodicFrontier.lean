/-
# Repelling periodic points lie on the Julia frontier

The fixed-point frontier bridge in `RepellingFixedPoint` is not enough for the
connected hRigid route: the relation obstruction consumes periodic targets of
arbitrary period.  This file supplies the missing dynamical part directly.

If `z₀` is fixed by `f_c^[p]` and the multiplier of that return map has norm
`> 1`, then `z₀` cannot lie in the interior of `K_c`.  The proof is the same
Montel/expansion contradiction as the fixed-point case, applied to the block
iterate `(f_c^[p])^[n]`.
-/
import GaloisForLFunctions.Bottcher.RepellingFixedPoint

open Set Filter Topology Metric

namespace Bottcher

/-- A point of `K_c` stays in `K_c` under every block iterate `(f_c^[p])^[n]`. -/
theorem mem_filledJulia_periodic_block_iterate {c z : ℂ} {p : ℕ}
    (hz : z ∈ filledJulia c) (n : ℕ) :
    ((quadratic c)^[p])^[n] z ∈ filledJulia c := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact mem_filledJulia_iterate ih p

/-- The block iterates `(f_c^[p])^[n]` are entire. -/
theorem differentiable_quadratic_periodic_block_iterate (c : ℂ) (p n : ℕ) :
    Differentiable ℂ (((quadratic c)^[p])^[n]) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ']
      exact (differentiable_quadratic_iterate c p).comp ih

/-- **A repelling periodic point is not in the interior of `K_c`.**

For a return map `F = f_c^[p]`, if `F z₀ = z₀` and `‖F'(z₀)‖ > 1`, boundedness
of all block iterates on an interior disk would give a locally uniformly
convergent subsequence by Montel.  Derivatives of that subsequence would
converge, but at `z₀` they are powers of the repelling multiplier and blow up.
-/
theorem not_mem_interior_of_repelling_periodic_deriv {c z₀ : ℂ} {p : ℕ}
    (hper : (quadratic c)^[p] z₀ = z₀)
    (hrep : 1 < ‖deriv ((quadratic c)^[p]) z₀‖) :
    z₀ ∉ interior (filledJulia c) := by
  intro hint
  obtain ⟨R, hR0, hRsub⟩ := Metric.isOpen_iff.mp isOpen_interior z₀ hint
  have hRK : ball z₀ R ⊆ filledJulia c := hRsub.trans interior_subset
  obtain ⟨C, hC⟩ := (isBounded_filledJulia c).exists_norm_le
  let F : ℕ → ℂ → ℂ := fun n => ((quadratic c)^[p])^[n]
  have hFdiff : ∀ n, DifferentiableOn ℂ (F n) (ball z₀ R) :=
    fun n => (differentiable_quadratic_periodic_block_iterate c p n).differentiableOn
  have hFbd : ∀ n, ∀ z ∈ ball z₀ R, ‖F n z‖ ≤ C :=
    fun n z hz => hC _ (mem_filledJulia_periodic_block_iterate (hRK hz) n)
  set r : ℝ := R / 4 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hrR : r < R / 2 := by rw [hrdef]; linarith
  obtain ⟨φ, g, hφ, hconv, _hg⟩ := montel_subseq (F := F) (c := z₀) hr0 hrR hFdiff hFbd
  have hlu : TendstoLocallyUniformlyOn (fun k => F (φ k)) g atTop (ball z₀ r) :=
    (hconv.mono ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hderivlu : TendstoLocallyUniformlyOn
      (deriv ∘ fun k => F (φ k)) (deriv g) atTop (ball z₀ r) :=
    hlu.deriv (Filter.Eventually.of_forall fun k =>
      (hFdiff (φ k)).mono (ball_subset_ball (show r ≤ R by rw [hrdef]; linarith))) isOpen_ball
  have hderivtend : Tendsto (fun k => deriv (F (φ k)) z₀) atTop (𝓝 (deriv g z₀)) :=
    hderivlu.tendsto_at (Metric.mem_ball_self hr0)
  have hf : HasDerivAt ((quadratic c)^[p]) (deriv ((quadratic c)^[p]) z₀) z₀ :=
    (differentiable_quadratic_iterate c p).differentiableAt.hasDerivAt
  have hderivpow : ∀ k, deriv (F (φ k)) z₀ =
      (deriv ((quadratic c)^[p]) z₀) ^ (φ k) :=
    fun k => (HasDerivAt.iterate z₀ hf hper (φ k)).deriv
  rw [show (fun k => deriv (F (φ k)) z₀)
        = fun k => (deriv ((quadratic c)^[p]) z₀) ^ (φ k) from funext hderivpow] at hderivtend
  have hnormtend : Tendsto
      (fun k => ‖(deriv ((quadratic c)^[p]) z₀) ^ (φ k)‖)
      atTop (𝓝 ‖deriv g z₀‖) :=
    hderivtend.norm
  have hblow : Tendsto
      (fun k => ‖(deriv ((quadratic c)^[p]) z₀) ^ (φ k)‖) atTop atTop := by
    simp only [norm_pow]
    exact (tendsto_pow_atTop_atTop_of_one_lt hrep).comp hφ.tendsto_atTop
  exact not_tendsto_atTop_of_tendsto_nhds hnormtend hblow

/-- A repelling periodic point has a nontrivial basin-side neighbourhood filter. -/
theorem nhdsWithin_compl_filledJulia_neBot_of_repelling_periodic_deriv {c z₀ : ℂ} {p : ℕ}
    (hper : (quadratic c)^[p] z₀ = z₀)
    (hrep : 1 < ‖deriv ((quadratic c)^[p]) z₀‖) :
    (𝓝[(filledJulia c)ᶜ] z₀).NeBot := by
  have hcl : z₀ ∈ closure (filledJulia c)ᶜ := by
    rw [closure_compl]
    exact not_mem_interior_of_repelling_periodic_deriv hper hrep
  exact mem_closure_iff_nhdsWithin_neBot.mp hcl

/-- A derivative-repelling periodic point lies on `frontier K_c`. -/
theorem mem_frontier_of_repelling_periodic_deriv {c z₀ : ℂ} {p : ℕ}
    (hper : (quadratic c)^[p] z₀ = z₀)
    (hrep : 1 < ‖deriv ((quadratic c)^[p]) z₀‖) :
    z₀ ∈ frontier (filledJulia c) := by
  have hp : 1 ≤ p := by
    by_cases hp : 1 ≤ p
    · exact hp
    · have hp0 : p = 0 := by omega
      subst p
      have hderiv : deriv ((quadratic c)^[0]) z₀ = 1 := by simp
      rw [hderiv, norm_one] at hrep
      linarith
  exact mem_frontier_of_mem_filledJulia_of_nhdsWithin_compl_neBot
    (mem_filledJulia_of_periodic hp hper)
    (nhdsWithin_compl_filledJulia_neBot_of_repelling_periodic_deriv hper hrep)

/-- The derivative of a quadratic iterate is the product of orbit multipliers. -/
theorem deriv_quadratic_iterate_eq_orbitProduct_core (c z₀ : ℂ) (p : ℕ) :
    deriv ((quadratic c)^[p]) z₀ =
      ∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z₀ := by
  exact (hasStrictDerivAt_quadratic_iterate c p z₀).hasDerivAt.deriv

/-- An orbit-product-repelling periodic point lies on `frontier K_c`. -/
theorem mem_frontier_of_repelling_periodic_orbitProduct {c z₀ : ℂ} {p : ℕ}
    (hper : (quadratic c)^[p] z₀ = z₀)
    (hrep : 1 < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z₀‖) :
    z₀ ∈ frontier (filledJulia c) := by
  exact mem_frontier_of_repelling_periodic_deriv hper
    (by simpa [deriv_quadratic_iterate_eq_orbitProduct_core] using hrep)

/-- `1 ≤ 2^p` as a real number. -/
theorem one_le_two_pow_real (p : ℕ) : (1 : ℝ) ≤ (2 ^ p : ℝ) := by
  induction p with
  | zero =>
      norm_num
  | succ p ih =>
      rw [pow_succ]
      nlinarith

/-- The hRigid strong-repelling orbit-product bound implies frontier membership. -/
theorem mem_frontier_of_strongly_repelling_periodic_orbitProduct {c z₀ : ℂ} {p : ℕ}
    (hper : (quadratic c)^[p] z₀ = z₀)
    (hrep : (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z₀‖) :
    z₀ ∈ frontier (filledJulia c) :=
  mem_frontier_of_repelling_periodic_orbitProduct hper
    (lt_of_le_of_lt (one_le_two_pow_real p) hrep)

end Bottcher
