import GaloisForLFunctions.HTGeometry.StableWirtinger

/-!
# Weighted Wirtinger inequality over a supercritical partition

For nodes `p 0 < p 1 < ⋯ < p N` with `max(|p j|, |p (j+1)|)·(p (j+1) − p j) ≤ a/2` and `F` of class
`C¹` on `[p 0, p N]`:
`∫ x²|F|² ≤ (1+ε)² (a/2π)² ∫ |F'|² + K_ε (a/2) Σ_j max(|p j|,|p (j+1)|)(|F(p j)|² + |F(p (j+1))|²)`,
with `K_ε = (1 + ε⁻¹)(2 + 2(1+ε)/π²)`.

On each gap the weight `x²` is at most `max(|p j|, |p (j+1)|)²`, and the stable Wirtinger
inequality turns the gap condition into the constant `(a/2π)²`. This is the sampling form of the
Poincaré–Wirtinger estimate behind Kulikov–Nazarov–Sodin uniqueness pairs: the uncertainty
`‖xF‖ ≲ (a/2π)‖F'‖` holds up to the node samples.
-/

open MeasureTheory intervalIntegral Set Complex Real

namespace GaloisForLFunctions.HTGeometry

/-- One gap: `∫ x²|F|²` over `[p, q]` with `max(|p|,|q|)·(q−p) ≤ a/2`. -/
theorem gap_weighted_wirtinger {ε a p q : ℝ} (hε : 0 < ε) (hpq : p < q)
    (hgap : max |p| |q| * (q - p) ≤ a / 2)
    {F F' : ℝ → ℂ} (hF : ∀ x ∈ Icc p q, HasDerivAt F (F' x) x)
    (hF'c : ContinuousOn F' (Icc p q)) :
    ∫ x in p..q, x ^ 2 * ‖F x‖ ^ 2 ≤ (1 + ε) ^ 2 * (a / (2 * π)) ^ 2 * (∫ x in p..q, ‖F' x‖ ^ 2)
      + (1 + ε⁻¹) * (2 + 2 * (1 + ε) / π ^ 2) * (a / 2) * max |p| |q| *
        (‖F p‖ ^ 2 + ‖F q‖ ^ 2) := by
  set M := max |p| |q| with hM
  set L := q - p with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  have hM0 : 0 ≤ M := le_max_of_le_left (abs_nonneg p)
  have hFc : ContinuousOn F (Icc p q) := fun x hx => (hF x hx).continuousAt.continuousWithinAt
  have hW := stable_wirtinger_intervalIntegral hε hpq hF hF'c
  have h1 : ∫ x in p..q, x ^ 2 * ‖F x‖ ^ 2 ≤ ∫ x in p..q, M ^ 2 * ‖F x‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on hpq.le
    · exact ((continuousOn_id.pow 2).mul (hFc.norm.pow 2)).intervalIntegrable_of_Icc hpq.le
    · exact (continuousOn_const.mul (hFc.norm.pow 2)).intervalIntegrable_of_Icc hpq.le
    · intro x hx
      have hx2 : x ^ 2 ≤ M ^ 2 := by
        rw [← sq_abs x]
        exact pow_le_pow_left₀ (abs_nonneg x) (abs_le_max_abs_abs hx.1 hx.2) 2
      exact mul_le_mul_of_nonneg_right hx2 (by positivity)
  rw [intervalIntegral.integral_const_mul] at h1
  have hML : M * L ≤ a / 2 := hgap
  have hK : 0 ≤ (1 + ε⁻¹) * (2 + 2 * (1 + ε) / π ^ 2) := by positivity
  have hIF : 0 ≤ ∫ x in p..q, ‖F' x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hpq.le (fun x _ => by positivity)
  have hE : 0 ≤ ‖F p‖ ^ 2 + ‖F q‖ ^ 2 := by positivity
  have hlead : M ^ 2 * ((1 + ε) ^ 2 * (L / π) ^ 2) ≤ (1 + ε) ^ 2 * (a / (2 * π)) ^ 2 := by
    have hpi : 0 < π := Real.pi_pos
    have h2 : (M * L) ^ 2 ≤ (a / 2) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hM0 hL0.le) hML 2
    have : M ^ 2 * (L / π) ^ 2 ≤ (a / (2 * π)) ^ 2 := by
      rw [div_pow, div_pow, mul_div_assoc', ← mul_pow, show (2 * π) ^ 2 = 2 ^ 2 * π ^ 2 by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : (a / 2) ^ 2 = a ^ 2 / 2 ^ 2 := by ring
      rw [this] at h2
      rw [le_div_iff₀ (by positivity)] at h2
      nlinarith [sq_nonneg π]
    calc M ^ 2 * ((1 + ε) ^ 2 * (L / π) ^ 2) = (1 + ε) ^ 2 * (M ^ 2 * (L / π) ^ 2) := by ring
      _ ≤ (1 + ε) ^ 2 * (a / (2 * π)) ^ 2 := by gcongr
  have hend : M ^ 2 * ((1 + ε⁻¹) * (2 + 2 * (1 + ε) / π ^ 2) * L * (‖F p‖ ^ 2 + ‖F q‖ ^ 2))
      ≤ (1 + ε⁻¹) * (2 + 2 * (1 + ε) / π ^ 2) * (a / 2) * M * (‖F p‖ ^ 2 + ‖F q‖ ^ 2) := by
    have : M ^ 2 * L = M * (M * L) := by ring
    calc M ^ 2 * ((1 + ε⁻¹) * (2 + 2 * (1 + ε) / π ^ 2) * L * (‖F p‖ ^ 2 + ‖F q‖ ^ 2))
        = (1 + ε⁻¹) * (2 + 2 * (1 + ε) / π ^ 2) * (M * (M * L)) * (‖F p‖ ^ 2 + ‖F q‖ ^ 2) := by ring
      _ ≤ (1 + ε⁻¹) * (2 + 2 * (1 + ε) / π ^ 2) * (M * (a / 2)) * (‖F p‖ ^ 2 + ‖F q‖ ^ 2) := by
        gcongr
      _ = _ := by ring
  calc ∫ x in p..q, x ^ 2 * ‖F x‖ ^ 2 ≤ M ^ 2 * ∫ x in p..q, ‖F x‖ ^ 2 := h1
    _ ≤ M ^ 2 * ((1 + ε) ^ 2 * (L / π) ^ 2 * (∫ x in p..q, ‖F' x‖ ^ 2)
        + (1 + ε⁻¹) * (2 + 2 * (1 + ε) / π ^ 2) * L * (‖F p‖ ^ 2 + ‖F q‖ ^ 2)) := by
      gcongr
    _ = M ^ 2 * ((1 + ε) ^ 2 * (L / π) ^ 2) * (∫ x in p..q, ‖F' x‖ ^ 2)
        + M ^ 2 * ((1 + ε⁻¹) * (2 + 2 * (1 + ε) / π ^ 2) * L * (‖F p‖ ^ 2 + ‖F q‖ ^ 2)) := by ring
    _ ≤ _ := by
      gcongr

/-- Sum over a finite partition `p 0 < p 1 < ⋯ < p N` whose gaps satisfy
`max(|p j|, |p (j+1)|)·(p (j+1) − p j) ≤ a/2`. -/
theorem partition_weighted_wirtinger {ε a : ℝ} (hε : 0 < ε) {p : ℕ → ℝ} (hp : StrictMono p)
    {N : ℕ} (hgap : ∀ j < N, max |p j| |p (j + 1)| * (p (j + 1) - p j) ≤ a / 2)
    {F F' : ℝ → ℂ} (hF : ∀ x ∈ Icc (p 0) (p N), HasDerivAt F (F' x) x)
    (hF'c : ContinuousOn F' (Icc (p 0) (p N))) :
    ∫ x in p 0..p N, x ^ 2 * ‖F x‖ ^ 2 ≤
      (1 + ε) ^ 2 * (a / (2 * π)) ^ 2 * (∫ x in p 0..p N, ‖F' x‖ ^ 2)
      + (1 + ε⁻¹) * (2 + 2 * (1 + ε) / π ^ 2) * (a / 2) *
        ∑ j ∈ Finset.range N, max |p j| |p (j + 1)| * (‖F (p j)‖ ^ 2 + ‖F (p (j + 1))‖ ^ 2) := by
  have hsub : ∀ k < N, Icc (p k) (p (k + 1)) ⊆ Icc (p 0) (p N) := fun k hk =>
    Icc_subset_Icc (hp.monotone (Nat.zero_le k)) (hp.monotone (by omega))
  have hFc : ContinuousOn F (Icc (p 0) (p N)) := fun x hx =>
    (hF x hx).continuousAt.continuousWithinAt
  have i1 : ∀ k < N, IntervalIntegrable (fun x => x ^ 2 * ‖F x‖ ^ 2) volume (p k) (p (k + 1)) :=
    fun k hk => (((continuousOn_id.pow 2).mul (hFc.norm.pow 2)).mono (hsub k hk)).intervalIntegrable_of_Icc
      (hp (Nat.lt_succ_self k)).le
  have i2 : ∀ k < N, IntervalIntegrable (fun x => ‖F' x‖ ^ 2) volume (p k) (p (k + 1)) :=
    fun k hk => ((hF'c.norm.pow 2).mono (hsub k hk)).intervalIntegrable_of_Icc
      (hp (Nat.lt_succ_self k)).le
  rw [← intervalIntegral.sum_integral_adjacent_intervals i1,
    ← intervalIntegral.sum_integral_adjacent_intervals i2, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have hjN := Finset.mem_range.mp hj
  have h := gap_weighted_wirtinger hε (hp (Nat.lt_succ_self j)) (hgap j hjN)
    (fun x hx => hF x (hsub j hjN hx)) (hF'c.mono (hsub j hjN))
  calc _ ≤ _ := h
    _ = _ := by ring

end GaloisForLFunctions.HTGeometry
