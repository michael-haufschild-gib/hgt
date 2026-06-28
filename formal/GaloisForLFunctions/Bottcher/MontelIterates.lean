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
import GaloisForLFunctions.Bottcher.MartyCriterion
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

/-- Every ball around a non-interior point of `K_c` contains a point of the basin of infinity. -/
theorem exists_mem_ball_basin_of_not_mem_interior {c z₀ : ℂ} {ρ : ℝ}
    (hz₀int : z₀ ∉ interior (filledJulia c)) (hρ : 0 < ρ) :
    ∃ w ∈ ball z₀ ρ, w ∈ basin c := by
  have hzcl : z₀ ∈ closure (filledJulia c)ᶜ := by
    rw [closure_compl]
    exact hz₀int
  obtain ⟨w, hwball, hwcomp⟩ :=
    (_root_.mem_closure_iff.mp hzcl) (ball z₀ ρ) isOpen_ball (mem_ball_self hρ)
  exact ⟨w, hwball, by rwa [basin_eq_compl_filledJulia]⟩

/-- The iterate family is non-normal on every ball around a non-interior point of `K_c`. -/
theorem no_normal_limit_of_not_mem_interior {c z₀ : ℂ} {ρ : ℝ}
    (hz₀int : z₀ ∉ interior (filledJulia c)) (hρ : 0 < ρ) :
    ¬ ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
        TendstoUniformlyOn (fun k => (quadratic c)^[φ k]) g atTop (ball z₀ ρ) :=
  no_normal_limit_of_meets_basin
    (exists_mem_ball_basin_of_not_mem_interior hz₀int hρ)

/-- Frontier points of `K_c` are non-normality points for the iterate family. -/
theorem no_normal_limit_of_frontier {c z₀ : ℂ} {ρ : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ : 0 < ρ) :
    ¬ ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
        TendstoUniformlyOn (fun k => (quadratic c)^[φ k]) g atTop (ball z₀ ρ) := by
  have hzcompl : z₀ ∈ closure (filledJulia c)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hzfront
    exact hzfront.2
  have hzint : z₀ ∉ interior (filledJulia c) := by
    rwa [closure_compl] at hzcompl
  exact no_normal_limit_of_not_mem_interior hzint hρ

/-- If `K_c` has empty interior, every filled-Julia point is a non-normality point for the iterate
family. -/
theorem no_normal_limit_of_mem_emptyInterior {c z₀ : ℂ} {ρ : ℝ}
    (hempty : interior (filledJulia c) = ∅) (_hzK : z₀ ∈ filledJulia c) (hρ : 0 < ρ) :
    ¬ ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
        TendstoUniformlyOn (fun k => (quadratic c)^[φ k]) g atTop (ball z₀ ρ) := by
  exact no_normal_limit_of_not_mem_interior (by simp [hempty]) hρ

/-- Along a sequence escaping to infinity, the third stereographic coordinate tends to the north pole.

This is the scalar piece of the spherical-normality obstruction: basin orbits force the
stereographic third coordinate to `1`. -/
theorem stereo_third_tendsto_one_of_norm_tendsto_atTop {u : ℕ → ℂ}
    (h : Tendsto (fun n => ‖u n‖) atTop atTop) :
    Tendsto (fun n => (stereo (u n)).ofLp (2 : Fin 3)) atTop (𝓝 (1 : ℝ)) := by
  have hsq : Tendsto (fun n => ‖u n‖ ^ 2) atTop atTop := by
    exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp h
  have hden : Tendsto (fun n => (1 : ℝ) + ‖u n‖ ^ 2) atTop atTop := by
    simpa [add_comm] using tendsto_atTop_add_const_right atTop 1 hsq
  have hinv : Tendsto (fun n => ((1 : ℝ) + ‖u n‖ ^ 2)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_inv_atTop_zero.comp hden
  have htwo : Tendsto (fun n => (2 : ℝ) * ((1 : ℝ) + ‖u n‖ ^ 2)⁻¹)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hinv.const_mul (2 : ℝ)
  have hlim : Tendsto (fun n => (1 : ℝ) - (2 : ℝ) * ((1 : ℝ) + ‖u n‖ ^ 2)⁻¹)
      atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub htwo
  refine hlim.congr' ?_
  filter_upwards with n
  simp [stereo]
  field_simp
  ring

/-- Frontier points have no spherical locally uniform iterate limit on a closed ball.

Basin points accumulating at the frontier force the third stereographic coordinate of any continuous
uniform limit to be `1` at the frontier point. The filled-Julia orbit of the frontier point is
uniformly bounded, so the same coordinate is bounded away from `1`, contradiction. -/
theorem no_spherical_normal_limit_of_frontier {c z₀ : ℂ} {ρ : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ : 0 < ρ) :
    ¬ ∃ (φ : ℕ → ℕ) (G : ℂ → EuclideanSpace ℝ (Fin 3)), StrictMono φ ∧
        ContinuousOn G (closedBall z₀ ρ) ∧
        TendstoUniformlyOn (fun k z => stereo ((quadratic c)^[φ k] z)) G atTop
          (closedBall z₀ ρ) := by
  rintro ⟨φ, G, hφ, hGcont, hconv⟩
  let A : Set ℂ := basin c ∩ closedBall z₀ ρ
  have hzcompl : z₀ ∈ closure (filledJulia c)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hzfront
    exact hzfront.2
  have hzbasin_closure : z₀ ∈ closure (basin c) := by
    simpa [basin_eq_compl_filledJulia c] using hzcompl
  have hzA : z₀ ∈ closure A := by
    rw [mem_closure_iff_frequently] at hzbasin_closure ⊢
    exact hzbasin_closure.and_eventually (Metric.closedBall_mem_nhds z₀ hρ)
  have hzclosed : z₀ ∈ closedBall z₀ ρ := mem_closedBall_self hρ.le
  have hcoord_cont : ContinuousOn (fun z => (G z).ofLp (2 : Fin 3)) (closedBall z₀ ρ) := by
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).comp_continuousOn hGcont
  have hcoord_A : ContinuousWithinAt (fun z => (G z).ofLp (2 : Fin 3)) A z₀ := by
    exact (hcoord_cont.continuousWithinAt hzclosed).mono inter_subset_right
  have hA_one : MapsTo (fun z => (G z).ofLp (2 : Fin 3)) A ({1} : Set ℝ) := by
    intro w hw
    have hwbasin : w ∈ basin c := hw.1
    have hwclosed : w ∈ closedBall z₀ ρ := hw.2
    have hconvw : Tendsto (fun k => stereo ((quadratic c)^[φ k] w)) atTop (𝓝 (G w)) :=
      hconv.tendsto_at hwclosed
    have hconvw_coord : Tendsto
        (fun k => (stereo ((quadratic c)^[φ k] w)).ofLp (2 : Fin 3))
        atTop (𝓝 ((G w).ofLp (2 : Fin 3))) :=
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).tendsto (G w)).comp
        hconvw
    have hnorm : Tendsto (fun k => ‖(quadratic c)^[φ k] w‖) atTop atTop :=
      (norm_iterate_tendsto_atTop_of_basin hwbasin).comp hφ.tendsto_atTop
    have hthird : Tendsto
        (fun k => (stereo ((quadratic c)^[φ k] w)).ofLp (2 : Fin 3))
        atTop (𝓝 (1 : ℝ)) :=
      stereo_third_tendsto_one_of_norm_tendsto_atTop hnorm
    have hEq : (G w).ofLp (2 : Fin 3) = 1 := tendsto_nhds_unique hconvw_coord hthird
    simp [hEq]
  have hGz₀_one : (G z₀).ofLp (2 : Fin 3) = 1 := by
    have hmem : (fun z => (G z).ofLp (2 : Fin 3)) z₀ ∈ closure ({1} : Set ℝ) :=
      hcoord_A.mem_closure hzA hA_one
    simpa using hmem
  have hzKcl : z₀ ∈ closure (filledJulia c) := by
    rw [frontier_eq_closure_inter_closure] at hzfront
    exact hzfront.1
  have hzK : z₀ ∈ filledJulia c := by
    rwa [(isClosed_filledJulia c).closure_eq] at hzKcl
  let M : ℝ := max 2 ‖c‖
  let B : ℝ := 1 - 2 / (1 + M ^ 2)
  have hcoord_le : ∀ k, (stereo ((quadratic c)^[φ k] z₀)).ofLp (2 : Fin 3) ≤ B := by
    intro k
    have hiterK : (quadratic c)^[φ k] z₀ ∈ filledJulia c := filledJulia_forward hzK (φ k)
    have hnormle : ‖(quadratic c)^[φ k] z₀‖ ≤ M := by
      have hb := filledJulia_subset_closedBall c hiterK
      simpa [M, mem_closedBall, dist_zero_right] using hb
    set x : ℝ := ‖(quadratic c)^[φ k] z₀‖
    have hxnonneg : 0 ≤ x := by simp [x]
    have hMnonneg : 0 ≤ M := by
      have h2 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
      exact le_trans h2 (le_max_left 2 ‖c‖)
    have hx2le : x ^ 2 ≤ M ^ 2 := by nlinarith
    have hdenle : 1 + x ^ 2 ≤ 1 + M ^ 2 := by nlinarith
    have hdenpos : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    have hfrac : 2 / (1 + M ^ 2) ≤ 2 / (1 + x ^ 2) := by
      exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hdenpos hdenle
    have hrewrite : (x ^ 2 - 1) / (1 + x ^ 2) = 1 - 2 / (1 + x ^ 2) := by
      field_simp [hdenpos.ne']
      ring
    have hst : (stereo ((quadratic c)^[φ k] z₀)).ofLp (2 : Fin 3) =
        (x ^ 2 - 1) / (1 + x ^ 2) := by
      simp [stereo, x]
    rw [hst, hrewrite]
    dsimp [B]
    linarith
  have hconvz₀ : Tendsto (fun k => stereo ((quadratic c)^[φ k] z₀)) atTop (𝓝 (G z₀)) :=
    hconv.tendsto_at hzclosed
  have hconvz₀_coord : Tendsto
      (fun k => (stereo ((quadratic c)^[φ k] z₀)).ofLp (2 : Fin 3))
      atTop (𝓝 ((G z₀).ofLp (2 : Fin 3))) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).tendsto (G z₀)).comp
      hconvz₀
  have hGz₀_le : (G z₀).ofLp (2 : Fin 3) ≤ B := le_of_tendsto' hconvz₀_coord hcoord_le
  have hBlt : B < 1 := by
    have hdenposM : 0 < 1 + M ^ 2 := by nlinarith [sq_nonneg M]
    have hfracpos : 0 < 2 / (1 + M ^ 2) := div_pos (by norm_num) hdenposM
    dsimp [B]
    linarith
  linarith

/-- Marty-form obstruction at a frontier point: the spherical derivatives of the iterate family
cannot be uniformly bounded on any neighborhood whose smaller closed ball still meets the frontier
center.

Indeed, a uniform spherical-derivative bound would give a spherical locally uniform subsequential
limit by `marty_normal_subseq`, contradicting `no_spherical_normal_limit_of_frontier`. -/
theorem not_sphericalDeriv_bounded_iterates_on_frontier_ball {c z₀ : ℂ} {R ρ M : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < R) :
    ¬ ∀ n z, z ∈ ball z₀ R → sphericalDeriv ((quadratic c)^[n]) z ≤ M := by
  intro hM
  obtain ⟨φ, G, hφ, hconv⟩ :=
    marty_normal_subseq (f := fun n => (quadratic c)^[n]) (c := z₀) (R := R)
      (r := ρ) (M := M) hρ0 hρR
      (fun n z _hz => (differentiable_quadratic_iterate c n) z)
      hM
  have hGcont : ContinuousOn G (closedBall z₀ ρ) := by
    refine hconv.continuousOn (Frequently.of_forall ?_)
    intro k
    exact continuous_stereo.comp_continuousOn
      ((differentiable_quadratic_iterate c (φ k)).continuous.continuousOn)
  exact no_spherical_normal_limit_of_frontier hzfront hρ0 ⟨φ, G, hφ, hGcont, hconv⟩

/-- Quantitative witness form of the Marty obstruction at a frontier point: every proposed bound is
exceeded by the spherical derivative of some iterate somewhere in the local ball. -/
theorem exists_sphericalDeriv_gt_iterates_on_frontier_ball {c z₀ : ℂ} {R ρ M : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < R) :
    ∃ n z, z ∈ ball z₀ R ∧ M < sphericalDeriv ((quadratic c)^[n]) z := by
  by_contra h
  have hle : ∀ n z, z ∈ ball z₀ R → sphericalDeriv ((quadratic c)^[n]) z ≤ M := by
    intro n z hz
    by_contra hnot
    exact h ⟨n, z, hz, lt_of_not_ge hnot⟩
  exact not_sphericalDeriv_bounded_iterates_on_frontier_ball hzfront hρ0 hρR hle

end Bottcher
