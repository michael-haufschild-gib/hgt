/-
# Montel applied to the iterate family — normality on the interior of `K_c` (the Fatou side)

The Julia/Fatou dichotomy for `f_c = z² + c`: the iterate family `{f_c^[n]}` is **normal** exactly off
the Julia set. This file proves the Fatou-side inclusion **`interior K_c ⊆ Fatou`** in concrete form:
on any ball `ball z₀ R ⊆ K_c`, the iterates are *uniformly bounded* by `max 2 ‖c‖`
(forward-invariance `filledJulia_forward` + the a-priori bound `filledJulia_subset_closedBall`), so by
the sequential Montel theorem (`montel_subseq`) some subsequence converges locally uniformly to a
holomorphic limit.

Together with the natural-boundary engine (which handles the empty-interior boundary case) this is the
constraint side of the `J_c` dichotomy: where the orbit stays bounded the family is normal, so any
genuine obstruction to continuing `φ_c` lives on `∂K_c = J_c`.

New file (Montel/Julia lane); consumes `MontelNormal` + `Dynamics`.
-/
import GaloisForLFunctions.Bottcher.MontelNormal
import GaloisForLFunctions.Bottcher.Dynamics
import GaloisForLFunctions.Bottcher.BottcherBasin

open Complex Metric Set Filter Topology

namespace Bottcher

/-- The quadratic map `z ↦ z² + c` is (complex) differentiable everywhere. -/
theorem differentiable_quadratic (c : ℂ) : Differentiable ℂ (quadratic c) := by
  unfold quadratic; fun_prop

/-- Every iterate `f_c^[n]` is differentiable everywhere (it is a polynomial map). -/
theorem differentiable_quadratic_iterate (c : ℂ) (n : ℕ) :
    Differentiable ℂ ((quadratic c)^[n]) := by
  induction n with
  | zero => simp only [Function.iterate_zero]; exact differentiable_id
  | succ k ih => rw [Function.iterate_succ']; exact (differentiable_quadratic c).comp ih

/-- **Normality of the iterate family on the interior of `K_c`** (the Fatou side of the dichotomy).
If `ball z₀ R ⊆ K_c`, the iterates `f_c^[n]` are uniformly bounded by `max 2 ‖c‖` on that ball, so a
subsequence converges uniformly on `closedBall z₀ ρ` (`ρ < R/2`) to a holomorphic limit. Hence the
interior of the filled Julia set is contained in the Fatou set (`{f_c^[n]}` is a normal family
there). -/
theorem montel_iterates_interior {c z₀ : ℂ} {ρ R : ℝ}
    (hρ0 : 0 < ρ) (hρR : ρ < R / 2) (hball : ball z₀ R ⊆ filledJulia c) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      TendstoUniformlyOn (fun k => (quadratic c)^[φ k]) g atTop (closedBall z₀ ρ) ∧
      DifferentiableOn ℂ g (ball z₀ ρ) := by
  refine montel_subseq (F := fun n => (quadratic c)^[n]) (C := max 2 ‖c‖) hρ0 hρR
    (fun n => (differentiable_quadratic_iterate c n).differentiableOn) ?_
  intro n z hz
  have hfwd : (quadratic c)^[n] z ∈ filledJulia c := filledJulia_forward (hball hz) n
  have hb := filledJulia_subset_closedBall c hfwd
  rwa [mem_closedBall, dist_zero_right] at hb

/-- **Orbit escape to `∞` on the basin.** For `w` in the basin of `∞`, `‖f_c^[n] w‖ → ∞`: once the
orbit exceeds radius `max 2 ‖c‖` it grows geometrically (`quadratic_orbit_growth`). -/
theorem norm_iterate_tendsto_atTop_of_basin {c w : ℂ} (hw : w ∈ basin c) :
    Tendsto (fun n => ‖(quadratic c)^[n] w‖) atTop atTop := by
  obtain ⟨N, hN⟩ := hw
  simp only [escapeOpen, mem_setOf_eq] at hN
  set v := (quadratic c)^[N] w with hv
  have hv2 : 2 < ‖v‖ := lt_of_le_of_lt (le_max_left 2 ‖c‖) hN
  have hvc : ‖c‖ ≤ ‖v‖ := le_of_lt (lt_of_le_of_lt (le_max_right 2 ‖c‖) hN)
  have hbase : (1 : ℝ) < ‖v‖ - 1 := by linarith
  have hgeo : Tendsto (fun m => ‖v‖ * (‖v‖ - 1) ^ m) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hbase).const_mul_atTop (by linarith : (0 : ℝ) < ‖v‖)
  have htail : Tendsto (fun m => ‖(quadratic c)^[m + N] w‖) atTop atTop := by
    refine tendsto_atTop_mono (fun m => ?_) hgeo
    have he : (quadratic c)^[m + N] w = (quadratic c)^[m] v := by
      rw [Function.iterate_add_apply, ← hv]
    rw [he]; exact quadratic_orbit_growth hvc hv2 m
  exact (tendsto_add_atTop_iff_nat N).mp htail

/-- **Non-normality at the basin boundary (the Julia side of the dichotomy).** If a ball meets the
basin of `∞`, then `{f_c^[n]}` has **no** subsequence converging uniformly on it to a (finite,
holomorphic) limit: at a basin point the orbit escapes to `∞`, contradicting convergence to `g w`.
Combined with `montel_iterates_interior` this pins the family's non-normality locus to `∂K_c = J_c`. -/
theorem no_normal_limit_of_meets_basin {c z₀ : ℂ} {ρ : ℝ}
    (hmeet : ∃ w ∈ ball z₀ ρ, w ∈ basin c) :
    ¬ ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
        TendstoUniformlyOn (fun k => (quadratic c)^[φ k]) g atTop (ball z₀ ρ) := by
  rintro ⟨φ, g, hφ, hconv⟩
  obtain ⟨w, hwball, hwbasin⟩ := hmeet
  have hptn : Tendsto (fun k => ‖(quadratic c)^[φ k] w‖) atTop (𝓝 ‖g w‖) :=
    (hconv.tendsto_at hwball).norm
  have hsub : Tendsto (fun k => ‖(quadratic c)^[φ k] w‖) atTop atTop :=
    (norm_iterate_tendsto_atTop_of_basin hwbasin).comp hφ.tendsto_atTop
  exact not_tendsto_atTop_of_tendsto_nhds hptn hsub

end Bottcher
