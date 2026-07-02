/-
# The β fixed point as extreme boundary point (real parameters)

For real `c ≤ 0` the repelling fixed point `β = (1+√(1-4c))/2` is the norm-extreme point of the
filled Julia set: `K_c ⊆ closedBall 0 β` with `β ∈ K_c ∩ frontier K_c`.  This is the first brick
of the dendrite-tip supply for the both-connected pair lane: the tip candidate `z₀ := β` sits on
the extreme sphere, so the basin fills a full outer lune at every scale.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.GreenFunction
import Mathlib.Analysis.SpecificLimits.Basic

open Complex Set Metric Bornology

namespace Bottcher

/-- The extreme radius of the real-parameter filled Julia set. -/
noncomputable def betaFixed (c : ℝ) : ℝ := (1 + Real.sqrt (1 - 4 * c)) / 2

theorem one_le_betaFixed {c : ℝ} (hc0 : c ≤ 0) : 1 ≤ betaFixed c := by
  unfold betaFixed
  have h1 : (1:ℝ) ≤ Real.sqrt (1 - 4 * c) := by
    have h2 : Real.sqrt 1 ≤ Real.sqrt (1 - 4 * c) := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_one] at h2
  linarith

/-- The fixed-point equation `β² + c = β`. -/
theorem betaFixed_sq {c : ℝ} (hc0 : c ≤ 0) :
    betaFixed c ^ 2 + c = betaFixed c := by
  unfold betaFixed
  have h1 : Real.sqrt (1 - 4 * c) ^ 2 = 1 - 4 * c :=
    Real.sq_sqrt (by linarith)
  linear_combination (1/4 : ℝ) * h1

/-- **Extreme-radius bound**: for real `c ≤ 0` the filled Julia set lies in the closed β-ball. -/
theorem filledJulia_subset_closedBall_betaFixed {c : ℝ} (hc0 : c ≤ 0) :
    filledJulia (c : ℂ) ⊆ Metric.closedBall (0:ℂ) (betaFixed c) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  push Not at hcon
  set β := betaFixed c with hβdef
  set t₀ : ℝ := ‖z‖ - β with ht₀def
  have hβ1 : 1 ≤ β := one_le_betaFixed hc0
  have ht₀ : 0 < t₀ := by
    rw [ht₀def]
    linarith
  -- the orbit escapes geometrically
  have hgrow : ∀ n : ℕ, β + 2 ^ n * t₀ ≤ ‖(quadratic (c:ℂ))^[n] z‖ := by
    intro n
    induction n with
    | zero =>
        simp [ht₀def]
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        set w := (quadratic (c:ℂ))^[m] z with hwdef
        have h2 : ‖w‖ ^ 2 - ‖(c:ℂ)‖ ≤ ‖quadratic (c:ℂ) w‖ := by
          unfold quadratic
          calc ‖w‖ ^ 2 - ‖(c:ℂ)‖ = ‖w ^ 2‖ - ‖(c:ℂ)‖ := by rw [norm_pow]
            _ ≤ ‖w ^ 2 + (c:ℂ)‖ := by
                have := norm_sub_norm_le (w ^ 2) (-(c:ℂ))
                simpa [sub_neg_eq_add] using this
        have h3 : ‖(c:ℂ)‖ = -c := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hc0]
        have h4 : (0:ℝ) < 2 ^ m := by positivity
        have h5 : β + 2 ^ m * t₀ ≤ ‖w‖ := ih
        have h6 : (β + 2 ^ m * t₀) ^ 2 + c ≤ ‖w‖ ^ 2 + c := by
          have h7 : (0:ℝ) ≤ β + 2 ^ m * t₀ := by nlinarith
          nlinarith
        have h8 : β + 2 ^ (m + 1) * t₀ ≤ (β + 2 ^ m * t₀) ^ 2 + c := by
          have h9 := betaFixed_sq hc0
          rw [← hβdef] at h9
          have h10 : (β + 2 ^ m * t₀) ^ 2 + c
              = β ^ 2 + c + 2 * β * (2 ^ m * t₀) + (2 ^ m * t₀) ^ 2 := by ring
          rw [h10, h9]
          have h11 : (0:ℝ) ≤ (2 ^ m * t₀) ^ 2 := sq_nonneg _
          have h12 : 2 * (2 ^ m * t₀) ≤ 2 * β * (2 ^ m * t₀) := by
            nlinarith [mul_pos h4 ht₀]
          have h13 : (2:ℝ) ^ (m + 1) * t₀ = 2 * (2 ^ m * t₀) := by ring
          linarith
        calc β + 2 ^ (m + 1) * t₀ ≤ (β + 2 ^ m * t₀) ^ 2 + c := h8
          _ ≤ ‖w‖ ^ 2 + c := h6
          _ = ‖w‖ ^ 2 - ‖(c:ℂ)‖ := by rw [h3]; ring
          _ ≤ ‖quadratic (c:ℂ) w‖ := h2
  -- unboundedness contradicts membership
  have hzb : IsBounded (Set.range fun n : ℕ => (quadratic (c:ℂ))^[n] z) := hz
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hzb
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((C - β) / t₀) (by norm_num : (1:ℝ) < 2)
  rw [div_lt_iff₀ ht₀] at hn
  have h14 := hC ((quadratic (c:ℂ))^[n] z) ⟨n, rfl⟩
  have h15 := hgrow n
  linarith

/-- `β` is a fixed point, hence in the filled Julia set. -/
theorem betaFixed_mem_filledJulia {c : ℝ} (hc0 : c ≤ 0) :
    ((betaFixed c : ℝ) : ℂ) ∈ filledJulia (c : ℂ) := by
  have hfix : quadratic (c:ℂ) ((betaFixed c : ℝ) : ℂ) = ((betaFixed c : ℝ) : ℂ) := by
    unfold quadratic
    have h1 := betaFixed_sq hc0
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) h1
  have hconst : ∀ n : ℕ, (quadratic (c:ℂ))^[n] ((betaFixed c : ℝ) : ℂ)
      = ((betaFixed c : ℝ) : ℂ) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', ih, hfix]
  show IsBounded (Set.range fun n : ℕ => (quadratic (c:ℂ))^[n] ((betaFixed c : ℝ) : ℂ))
  have h2 : (Set.range fun n : ℕ => (quadratic (c:ℂ))^[n] ((betaFixed c : ℝ) : ℂ))
      = {((betaFixed c : ℝ) : ℂ)} := by
    ext w
    constructor
    · rintro ⟨n, rfl⟩
      show (quadratic (c:ℂ))^[n] ((betaFixed c : ℝ) : ℂ) ∈ _
      rw [hconst n]
      rfl
    · rintro rfl
      exact ⟨0, by simp⟩
  rw [h2]
  exact isBounded_singleton

/-- **`β` is a boundary (Julia) point**: real points just beyond `β` escape, so `β` lies in the
frontier of the filled Julia set. -/
theorem betaFixed_mem_frontier {c : ℝ} (hc0 : c ≤ 0) :
    ((betaFixed c : ℝ) : ℂ) ∈ frontier (filledJulia (c : ℂ)) := by
  rw [frontier_eq_closure_inter_closure]
  constructor
  · exact subset_closure (betaFixed_mem_filledJulia hc0)
  · -- approach from outside along the real axis
    have hβ1 : 1 ≤ betaFixed c := one_le_betaFixed hc0
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun n => ((betaFixed c + 1 / (n + 1) : ℝ) : ℂ), ?_, ?_⟩
    · intro n hmem
      have h1 := filledJulia_subset_closedBall_betaFixed hc0 hmem
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      have h2 : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      have h3 : ‖((betaFixed c + 1 / (n + 1) : ℝ) : ℂ)‖ = betaFixed c + 1 / (n + 1) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      rw [h3] at h1
      linarith
    · have h4 : Filter.Tendsto (fun n : ℕ => betaFixed c + 1 / ((n:ℝ) + 1))
          Filter.atTop (nhds (betaFixed c)) := by
        have h5 : Filter.Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) Filter.atTop (nhds (0:ℝ)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h6 : Filter.Tendsto (fun n : ℕ => betaFixed c + 1 / ((n:ℝ) + 1))
            Filter.atTop (nhds (betaFixed c + 0)) := h5.const_add (betaFixed c)
        simpa using h6
      have h7 : Filter.Tendsto (fun x : ℝ => (x : ℂ)) (nhds (betaFixed c))
          (nhds ((betaFixed c : ℝ) : ℂ)) := Complex.continuous_ofReal.continuousAt
      exact h7.comp h4

end Bottcher
