import GaloisForLFunctions.HTGeometry.NevCombinationDiscrete
import GaloisForLFunctions.HTGeometry.NevZeroDichotomy
import GaloisForLFunctions.HTGeometry.ChristoffelBoundedKernel

/-!
# The remaining parameter `τ = 0`

For `τ ≠ 0` the value `B(0)τ − D(0) = −τ` witnesses non-vanishing at the origin.  At `τ = 0` the
combination is `−D`, and `D(0) = 0`, so the witness has to come from elsewhere.

It comes from the factorisation `D(z) = h₀·z·(∑ₖ Qₖ(0)Qₖ(z)/hₖ)`: the factor `z` is what hides the
non-vanishing at the origin, and the series itself is nonzero there because at a real point its terms
are the squares `Qₖ(0)²/hₖ`, whose `k = 0` term is `1/h₀ > 0`.  Continuity then supplies a nearby
point where `D` itself is nonzero.
-/

open scoped BigOperators
open Filter Topology

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- `D` is the linear factor times its series. -/
theorem nevDinf_eq (s : ℕ → ℝ) (z : ℂ) :
    nevDinf s z
      = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z * nevDseries s z :=
  rfl

/-- At the origin the `D` series is the real Christoffel series. -/
theorem nevDseries_zero_eq (s : ℕ → ℝ) :
    nevDseries s 0
      = ((∑' k, ((monicOrtho s k).eval 0) ^ 2 /
          momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
  have hterm : ∀ k : ℕ, monicOrthoC s k 0 * monicOrthoC s k 0 /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
      = ((((monicOrtho s k).eval 0) ^ 2 /
          momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
    intro k
    have hre : monicOrthoC s k (0 : ℂ) = ((((monicOrtho s k).eval (0:ℝ)) : ℝ) : ℂ) := by
      simpa using monicOrthoC_ofReal s k 0
    rw [hre]
    push_cast
    ring
  simp only [nevDseries]
  rw [Complex.ofReal_tsum]
  exact tsum_congr hterm

/-- **The `D` series is nonzero at the origin.**  Its terms there are `Qₖ(0)²/hₖ`, and the `k = 0`
term is `1/h₀ > 0`. -/
theorem nevDseries_zero_ne_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    nevDseries s 0 ≠ 0 := by
  have hb : BoundedKernel s ((0:ℝ) : ℂ) := by simpa using h0b
  have hsum : Summable (fun k => ((monicOrtho s k).eval 0) ^ 2 /
      momentInner s (monicOrtho s k) (monicOrtho s k)) := by
    have hsum0 := summable_of_boundedKernel h hb
    have hterm : (fun k => Complex.normSq (monicOrthoC s k ((0:ℝ) : ℂ)) /
        momentInner s (monicOrtho s k) (monicOrtho s k))
        = fun k => ((monicOrtho s k).eval 0) ^ 2 /
          momentInner s (monicOrtho s k) (monicOrtho s k) := by
      funext k
      rw [normSq_monicOrthoC_ofReal]
    rw [hterm] at hsum0
    exact hsum0
  have hnn : ∀ k, 0 ≤ ((monicOrtho s k).eval 0) ^ 2 /
      momentInner s (monicOrtho s k) (monicOrtho s k) :=
    fun k => div_nonneg (sq_nonneg _) (monicOrtho_inner_self_pos h k).le
  have heval : ((monicOrtho s 0).eval (0:ℝ)) = 1 := by simp
  have hpos0 : 0 < ((monicOrtho s 0).eval 0) ^ 2 /
      momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    div_pos (by rw [heval]; norm_num) (monicOrtho_inner_self_pos h 0)
  have hle := hsum.le_tsum 0 (fun k _ => hnn k)
  rw [nevDseries_zero_eq]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hpos0 hle))

/-- The `D` series is entire. -/
theorem differentiable_nevDseries (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    Differentiable ℂ (nevDseries s) := by
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  intro z
  have hnorm : ∀ w ∈ Metric.ball (0:ℂ) (‖z‖ + 1), ‖w‖ ≤ ‖z‖ + 1 := by
    intro w hw
    have := Metric.mem_ball.mp hw
    rw [dist_zero_right] at this
    exact this.le
  have hmem : z ∈ Metric.ball (0:ℂ) (‖z‖ + 1) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  exact (differentiableOn_nevD_series h (Metric.ball 0 (‖z‖ + 1)) Metric.isOpen_ball hS
    (fun w hw N => kernelRoot_le_ballBoundQ h hS hP (hnorm w hw) N)).differentiableAt
      (Metric.isOpen_ball.mem_nhds hmem)

/-- **`D` does not vanish identically.**  Near the origin the series stays nonzero, so any nearby
point other than `0` is a witness. -/
theorem exists_nevDinf_ne_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    ∃ z, nevDinf s z ≠ 0 := by
  have hd := differentiable_nevDseries h h0b
  have hev : ∀ᶠ w in 𝓝 (0:ℂ), nevDseries s w ≠ 0 :=
    (hd 0).continuousAt.eventually_ne (nevDseries_zero_ne_zero h h0b)
  have hev' : ∀ᶠ w in 𝓝[≠] (0:ℂ), nevDseries s w ≠ 0 := hev.filter_mono nhdsWithin_le_nhds
  have hev2 : ∀ᶠ w in 𝓝[≠] (0:ℂ), w ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with w hw using hw
  obtain ⟨z, hz1, hz2⟩ := (hev'.and hev2).exists
  refine ⟨z, ?_⟩
  rw [nevDinf_eq]
  have h0 : ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (monicOrtho_inner_self_pos h 0).ne'
  exact mul_ne_zero (mul_ne_zero h0 hz2) hz1

/-- **The zeros of `D` are isolated.**  This is the `τ = 0` member of the family. -/
theorem eventually_ne_zero_nevDinf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, nevDinf s w ≠ 0 := by
  obtain ⟨-, -, -, hD, -⟩ := nevanlinna_entire_unimodular h h0b
  obtain ⟨z₁, hz₁⟩ := exists_nevDinf_ne_zero h h0b
  exact eventually_ne_zero_of_entire hD hz₁ z

/-- **Every member of the Nevanlinna family has isolated zeros.**  For every parameter `τ ∈ ℂ` the
zeros of `B τ − D` are isolated, and by `eventually_ne_zero_nevBinf` the same holds for the
remaining parameter `τ = ∞`. -/
theorem eventually_ne_zero_nevCombination_all (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (tau : ℂ) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, nevBinf s w * tau - nevDinf s w ≠ 0 := by
  rcases eq_or_ne tau 0 with rfl | htau
  · filter_upwards [eventually_ne_zero_nevDinf h h0b z] with w hw
    simpa using hw
  · exact eventually_ne_zero_nevCombination h h0b htau z

end HTGeometry
