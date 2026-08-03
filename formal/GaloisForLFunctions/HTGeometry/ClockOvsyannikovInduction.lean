import GaloisForLFunctions.HTGeometry.ClockOvsyannikovSeries

/-!
# The exact balance of one step of the analytic iteration

The iteration for `∂ξ∂η u = (Δ⊥ u + V u)/4` carries the bound

`‖u_m(ξ,η)‖_ρ ≤ Kᵐ m^{2m} |ξ-ξ₀|ᵐ |η-η₀|ᵐ / ((m!)² (ρ₀-ρ)^{2m})`

from one step to the next. The step is performed at the intermediate radius
`σ = ρ + (ρ₀-ρ)/(m+1)`, chosen so that the loss factor `K/(σ-ρ)²` is exactly `K(m+1)²/(ρ₀-ρ)²`
while the gap remaining above `σ` is `(ρ₀-ρ)·m/(m+1)`. The two double integrations contribute
`1/(m+1)²`.

What makes the scheme close is that these three factors multiply to *exactly* the next bound: the
`m^{2m}` produced by the induction hypothesis is cancelled by the shrunken gap, and the leftover
`(m+1)²` is absorbed by `((m+1)!)² = (m!)²(m+1)²`. This file proves that identity, and records the
resulting geometric domination.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The induction hypothesis re-expressed at the intermediate radius.** The gap remaining above
`σ = ρ + (ρ₀-ρ)/(m+1)` is `(ρ₀-ρ)·m/(m+1)`, and it cancels the `m^{2m}` of the hypothesis. -/
theorem sq_pow_ratio_intermediate {G : ℝ} (hG : 0 < G) (m : ℕ) :
    (m : ℝ) ^ (2 * m) / (G * (m : ℝ) / ((m : ℝ) + 1)) ^ (2 * m)
      = ((m : ℝ) + 1) ^ (2 * m) / G ^ (2 * m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    have h1 : ((m : ℝ) + 1) ≠ 0 := by positivity
    have hGne : G ≠ 0 := hG.ne'
    rw [div_pow, mul_pow]
    field_simp

/-- **One step of the iteration lands exactly on the next bound.** -/
theorem ovsyannikov_step_identity {K G x y : ℝ} (hG : 0 < G) (m : ℕ) :
    K * ((m : ℝ) + 1) ^ 2 / G ^ 2
        * (K ^ m * ((m : ℝ) + 1) ^ (2 * m) / ((m.factorial : ℝ) ^ 2 * G ^ (2 * m)))
        * (x ^ (m + 1) * y ^ (m + 1) / ((m : ℝ) + 1) ^ 2)
      = K ^ (m + 1) * ((m : ℝ) + 1) ^ (2 * (m + 1)) * (x ^ (m + 1) * y ^ (m + 1))
          / (((m + 1).factorial : ℝ) ^ 2 * G ^ (2 * (m + 1))) := by
  have hGne : G ≠ 0 := hG.ne'
  have h1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hfacne : (m.factorial : ℝ) ≠ 0 := hfac.ne'
  have hsucc : (((m + 1).factorial : ℝ)) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hexp : 2 * (m + 1) = 2 * m + 2 := by ring
  rw [hsucc, hexp, pow_add, pow_add]
  field_simp
  ring

/-- **The bound carried by the induction is geometric.** Rewriting `m^{2m}/(m!)²` as `(m^m/m!)²`
turns the `m`-th bound into the term controlled by the exponential estimate. -/
theorem ovsyannikov_bound_le {K G T : ℝ} (hK : 0 ≤ K) (hG : 0 < G) (m : ℕ) :
    K ^ m * (m : ℝ) ^ (2 * m) * (T ^ m * T ^ m) / ((m.factorial : ℝ) ^ 2 * G ^ (2 * m))
      ≤ (K * T ^ 2 * Real.exp 2 / G ^ 2) ^ m := by
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hGne : G ≠ 0 := hG.ne'
  have hm2 : (m : ℝ) ^ (2 * m) = ((m : ℝ) ^ m) ^ 2 := by rw [mul_comm, pow_mul]
  have hT2 : T ^ m * T ^ m = (T ^ m) ^ 2 := by rw [sq]
  have hG2 : G ^ (2 * m) = (G ^ 2) ^ m := by rw [pow_mul]
  have hTm : (T ^ 2) ^ m = (T ^ m) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
  have hG2ne : (G : ℝ) ^ 2 ≠ 0 := by positivity
  have hrw : K ^ m * (m : ℝ) ^ (2 * m) * (T ^ m * T ^ m)
        / ((m.factorial : ℝ) ^ 2 * G ^ (2 * m))
      = (K * T ^ 2 / G ^ 2) ^ m * ((m : ℝ) ^ m / (m.factorial : ℝ)) ^ 2 := by
    rw [hm2, hT2, hG2]
    simp only [div_pow, mul_pow]
    rw [hTm]
    field_simp
  have hA : (0 : ℝ) ≤ K * T ^ 2 / G ^ 2 := by positivity
  have hterm := ovsyannikov_term_le hA m
  rw [hrw]
  refine hterm.trans (le_of_eq ?_)
  congr 1
  ring

/-- **The iteration converges when the rectangle is small compared with the radius of
analyticity.** -/
theorem summable_ovsyannikov_bound {K G T : ℝ} (hK : 0 ≤ K) (hG : 0 < G) (hT : 0 ≤ T)
    (hsmall : K * T ^ 2 * Real.exp 2 / G ^ 2 < 1) :
    Summable fun m : ℕ =>
      K ^ m * (m : ℝ) ^ (2 * m) * (T ^ m * T ^ m)
        / ((m.factorial : ℝ) ^ 2 * G ^ (2 * m)) := by
  have hpos : (0 : ℝ) ≤ K * T ^ 2 * Real.exp 2 / G ^ 2 := by positivity
  have hgeo : Summable fun m : ℕ => (K * T ^ 2 * Real.exp 2 / G ^ 2) ^ m :=
    summable_geometric_of_lt_one hpos hsmall
  refine hgeo.of_nonneg_of_le (fun m => ?_) (fun m => ovsyannikov_bound_le hK hG m)
  positivity

end GaloisForLFunctions.HTGeometry
