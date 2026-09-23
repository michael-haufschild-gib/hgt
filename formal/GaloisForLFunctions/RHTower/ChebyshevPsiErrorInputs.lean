import GaloisForLFunctions.RHTower.Sieve.ChebyshevPsiBigO
import GaloisForLFunctions.HTGeometry.SubexponentialSqrtSummable

/-!
# The two analytic inputs extracted from the prime number theorem with error term

The corpus's `ψ(x) - x = O(x e^{-c√(log x)})` gives both inputs of the Abel route to Mertens: the
summatory function has mean one, and the error weight `|ψ(m) - m|/m²` is summable.
-/

open Filter Topology Asymptotics

namespace RHTower

noncomputable section

/-- The explicit eventual form of the prime number theorem with error term. -/
theorem exists_psi_error_eventually :
    ∃ C c : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤ C * (x * Real.exp (-c * Real.sqrt (Real.log x))) := by
  obtain ⟨c, hc, hO⟩ := Sieve.chebyshevPsi_sub_id_isBigO
  obtain ⟨C, hC⟩ := hO.bound
  refine ⟨|C|, c, hc, abs_nonneg C, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs] at hx
  have hg : |x * Real.exp (-c * Real.sqrt (Real.log x))|
      = x * Real.exp (-c * Real.sqrt (Real.log x)) := abs_of_pos (by positivity)
  rw [hg] at hx
  have hnn : (0 : ℝ) ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by positivity
  exact hx.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hnn)

/-- **The summatory von Mangoldt function has mean one.** -/
theorem tendsto_psi_div_self : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
  obtain ⟨C, c, hc, hC, hbound⟩ := exists_psi_error_eventually
  have hexp : Tendsto (fun x : ℝ => C * Real.exp (-c * Real.sqrt (Real.log x))) atTop (𝓝 0) := by
    have hlog : Tendsto (fun x : ℝ => Real.log x) atTop atTop := Real.tendsto_log_atTop
    have hsq : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hlog
    have harg : Tendsto (fun x : ℝ => -c * Real.sqrt (Real.log x)) atTop atBot := by
      have hmul := hsq.const_mul_atTop hc
      have := tendsto_neg_atBot_iff.2 hmul
      simpa [neg_mul] using this
    have := (Real.tendsto_exp_atBot.comp harg).const_mul C
    simpa using this
  have hsq : Tendsto (fun x : ℝ => |Chebyshev.psi x / x - 1|) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hexp
    filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hdiv : Chebyshev.psi x / x - 1 = (Chebyshev.psi x - x) / x := by
      field_simp
    rw [hdiv, abs_div, abs_of_pos hx0]
    rw [div_le_iff₀ hx0]
    calc |Chebyshev.psi x - x|
        ≤ C * (x * Real.exp (-c * Real.sqrt (Real.log x))) := hx
      _ = C * Real.exp (-c * Real.sqrt (Real.log x)) * x := by ring
  rw [← tendsto_sub_nhds_zero_iff]
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  simpa [Real.norm_eq_abs] using hsq

/-- **The error weight of the Abel tail is summable.** -/
theorem summable_psi_error_weight :
    Summable fun k : ℕ =>
      |Chebyshev.psi ((k : ℝ) + 1) - ((k : ℝ) + 1)| * (2 / ((k : ℝ) + 1) ^ (2 : ℕ)) := by
  obtain ⟨C, c, hc, hC, hbound⟩ := exists_psi_error_eventually
  obtain ⟨X, hX⟩ := eventually_atTop.1 hbound
  obtain ⟨N, hN⟩ := exists_nat_ge (max X 1)
  set g : ℕ → ℝ := fun m => Real.exp (-(c * Real.sqrt (Real.log m))) / m with hg
  have hgsum : Summable g := GaloisForLFunctions.HTGeometry.summable_exp_neg_sqrt_log_div hc
  set M : ℕ := N + 1 with hM
  have hmaj : Summable fun k : ℕ => 2 * C * g (k + (M + 1)) :=
    ((summable_nat_add_iff (M + 1)).2 hgsum).mul_left (2 * C)
  refine (summable_nat_add_iff M).1
    (Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hmaj)
  set x : ℝ := ((k + (M + 1) : ℕ) : ℝ) with hx
  have hxval : ((k : ℕ) : ℝ) + (M : ℕ) + 1 = x := by
    rw [hx]
    push_cast
    ring
  have hxpos : (0 : ℝ) < x := by
    rw [hx]
    positivity
  have hXle : X ≤ x := by
    have h1 : X ≤ max X 1 := le_max_left X 1
    have h2 : max X 1 ≤ (N : ℝ) := hN
    have h3 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [hx]
    push_cast
    rw [hM]
    push_cast
    linarith
  have hb := hX x hXle
  have hxeq : ((k + M : ℕ) : ℝ) + 1 = x := by
    rw [hx]
    push_cast
    ring
  have hshape : |Chebyshev.psi (((k + M : ℕ) : ℝ) + 1) - (((k + M : ℕ) : ℝ) + 1)|
      * (2 / (((k + M : ℕ) : ℝ) + 1) ^ (2 : ℕ))
      = |Chebyshev.psi x - x| * (2 / x ^ (2 : ℕ)) := by
    rw [hxeq]
  rw [hshape]
  have hstep : |Chebyshev.psi x - x| * (2 / x ^ (2 : ℕ))
      ≤ (C * (x * Real.exp (-c * Real.sqrt (Real.log x)))) * (2 / x ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_right hb (by positivity)
  refine hstep.trans (le_of_eq ?_)
  rw [hg]
  simp only
  have hgx : ((k + (M + 1) : ℕ) : ℝ) = x := hx.symm
  rw [hgx]
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hneg : -(c * Real.sqrt (Real.log x)) = -c * Real.sqrt (Real.log x) := by ring
  rw [hneg]
  field_simp

end

end RHTower
