import GaloisForLFunctions.TransHorizonIncidenceMechanics.DirichletChainDoubledPrefixAndRobinRamp

/-!
# Mixed chains

A chain `u₀ = 0, u₁, …, u_M` pinned at its bottom and free at its top is half of the Dirichlet
chain obtained by reflecting it across its free end: the reflection doubles both the mass and
the jump energy and adds no jump at the fold. Hence

`(2 - 2 cos(π/(2M+1))) Σ_{i≤M} u_i² ≤ Σ_{i<M} (u_{i+1} - u_i)²`,

the mixed (Dirichlet–Neumann) constant of a chain of length `M`, which is the Dirichlet constant
of a chain of length `2M`. Splitting the first `p` steps into half-steps absorbs half-weighted
steps at the pinned end exactly as for Dirichlet chains, at the price of lengthening the chain
by `p`.
-/

open Finset

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- **Mixed chain bound.** For `u₀ = 0` and a free top at `M`,
`(2 - 2 cos(π/(2M+1))) Σ_{i≤M} u_i² ≤ Σ_{i<M} (u_{i+1} - u_i)²`. -/
theorem mixed_chain_energy_bound (M : ℕ) (u : ℕ → ℝ) (h0 : u 0 = 0) :
    (2 - 2 * Real.cos (Real.pi / (2 * (M : ℝ) + 1))) * (∑ i ∈ range (M + 1), u i ^ 2) ≤
      ∑ i ∈ range M, (u (i + 1) - u i) ^ 2 := by
  set v : ℕ → ℝ := fun j => if j ≤ M then u j else u (2 * M + 1 - j) with hv
  have hlow (k : ℕ) (hk : k ≤ M) : v k = u k := by simp only [hv]; rw [if_pos hk]
  have hhigh (k : ℕ) (hk : k ≤ M) : v (M + 1 + k) = u (M - k) := by
    simp only [hv]; rw [if_neg (by omega)]; congr 1; omega
  have hv0 : v 0 = 0 := by rw [hlow 0 (Nat.zero_le _), h0]
  have hvend : v (2 * M + 1) = 0 := by
    have := hhigh M le_rfl
    rw [show M + 1 + M = 2 * M + 1 by ring, Nat.sub_self, h0] at this
    exact this
  have h := dirichlet_chain_energy_bound (2 * M) v hv0 hvend
  have hmass : ∑ k ∈ range (2 * M + 1), v k ^ 2 = 2 * ∑ i ∈ range (M + 1), u i ^ 2 := by
    have hA : ∑ k ∈ range (M + 1), v k ^ 2 = ∑ k ∈ range (M + 1), u k ^ 2 :=
      sum_congr rfl fun k hk => by rw [hlow k (by have := mem_range.mp hk; omega)]
    have hB : ∑ k ∈ range M, v (M + 1 + k) ^ 2 = ∑ k ∈ range M, u (M - k) ^ 2 :=
      sum_congr rfl fun k hk => by rw [hhigh k (by have := mem_range.mp hk; omega)]
    rw [show 2 * M + 1 = (M + 1) + M by ring, sum_range_add, hA, hB]
    have hrefl : ∑ k ∈ range M, u (M - k) ^ 2 = ∑ i ∈ range M, u (i + 1) ^ 2 := by
      rw [← sum_range_reflect]
      exact sum_congr rfl fun i hi => by
        have := mem_range.mp hi; congr 2; omega
    rw [hrefl, sum_range_succ' (fun i => u i ^ 2), h0]
    ring
  have henergy : ∑ k ∈ range (2 * M + 1), (v (k + 1) - v k) ^ 2 =
      2 * ∑ i ∈ range M, (u (i + 1) - u i) ^ 2 := by
    rw [show 2 * M + 1 = M + (M + 1) by ring, sum_range_add, sum_range_succ']
    have h1 : ∑ k ∈ range M, (v (k + 1) - v k) ^ 2 = ∑ k ∈ range M, (u (k + 1) - u k) ^ 2 :=
      sum_congr rfl fun k hk => by
        have := mem_range.mp hk; rw [hlow (k + 1) (by omega), hlow k (by omega)]
    have hmid : (v (M + 0 + 1) - v (M + 0)) ^ 2 = 0 := by
      rw [show M + 0 + 1 = M + 1 + 0 by ring, hhigh 0 (Nat.zero_le _), Nat.sub_zero,
        Nat.add_zero, hlow M le_rfl, sub_self]; ring
    have h2 : ∑ k ∈ range M, (v (M + (k + 1) + 1) - v (M + (k + 1))) ^ 2 =
        ∑ k ∈ range M, (u (k + 1) - u k) ^ 2 := by
      rw [← sum_range_reflect]
      refine sum_congr rfl fun i hi => ?_
      have hi' := mem_range.mp hi
      rw [show M + (M - 1 - i + 1) + 1 = M + 1 + (M - i) by omega,
        show M + (M - 1 - i + 1) = M + 1 + (M - 1 - i) by omega,
        hhigh (M - i) (by omega), hhigh (M - 1 - i) (by omega),
        show M - (M - i) = i by omega, show M - (M - 1 - i) = i + 1 by omega]
      ring
    rw [h1, hmid, h2]
    ring
  rw [hmass, henergy] at h
  have hcast : (((2 * M : ℕ) : ℝ) + 1) = 2 * (M : ℝ) + 1 := by push_cast; ring
  rw [hcast] at h
  linarith

/-- The chain with its first `p` steps split into half-steps. -/
private def halfStepChain (z : ℕ → ℝ) (p j : ℕ) : ℝ :=
  if j < 2 * p then (if j % 2 = 0 then z (j / 2) else (z (j / 2) + z (j / 2 + 1)) / 2)
  else z (j - p)

private theorem halfStepChain_even (z : ℕ → ℝ) {p i : ℕ} (hi : i ≤ p) :
    halfStepChain z p (2 * i) = z i := by
  unfold halfStepChain
  split_ifs with h1 h2
  · congr 1; omega
  · omega
  · congr 1; omega

private theorem halfStepChain_odd (z : ℕ → ℝ) {p i : ℕ} (hi : i < p) :
    halfStepChain z p (2 * i + 1) = (z i + z (i + 1)) / 2 := by
  unfold halfStepChain
  rw [if_pos (by omega), if_neg (by omega)]
  congr 2 <;> congr 1 <;> omega

private theorem halfStepChain_late (z : ℕ → ℝ) (p j : ℕ) :
    halfStepChain z p (2 * p + j) = z (p + j) := by
  unfold halfStepChain
  rw [if_neg (by omega)]
  congr 1; omega

private theorem sum_range_two_mul' (p : ℕ) (g : ℕ → ℝ) :
    (∑ j ∈ range (2 * p), g j) = ∑ i ∈ range p, (g (2 * i) + g (2 * i + 1)) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [show 2 * (p + 1) = 2 * p + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring_nf

/-- **Mixed chain with a soft prefix.** For `z₀ = 0`, a free top at `n`, and the first `p ≤ n`
steps half-weighted:
`(2 - 2 cos(π/(2(n+p)+1))) Σ_{i≤n} z_i² ≤ ½ Σ_{i<p} (Δz)² + Σ_{p≤i<n} (Δz)²`. -/
theorem mixed_chain_soft_prefix_bound (n p : ℕ) (hp : p ≤ n) (z : ℕ → ℝ) (h0 : z 0 = 0) :
    (2 - 2 * Real.cos (Real.pi / (2 * ((n + p : ℕ) : ℝ) + 1))) *
        (∑ i ∈ range (n + 1), z i ^ 2) ≤
      (1 / 2) * (∑ i ∈ range p, (z (i + 1) - z i) ^ 2) +
        ∑ j ∈ range (n - p), (z (p + j + 1) - z (p + j)) ^ 2 := by
  have hu0 : halfStepChain z p 0 = 0 := by
    rcases Nat.eq_zero_or_pos p with rfl | hpos
    · simp [halfStepChain, h0]
    · simpa [h0] using halfStepChain_even z (p := p) (i := 0) (Nat.zero_le _)
  have hlam : 0 ≤ 2 - 2 * Real.cos (Real.pi / (2 * ((n + p : ℕ) : ℝ) + 1)) := by
    linarith [Real.cos_le_one (Real.pi / (2 * ((n + p : ℕ) : ℝ) + 1))]
  have hchain := mixed_chain_energy_bound (n + p) (halfStepChain z p) hu0
  have hsplit (f : ℕ → ℝ) : (∑ j ∈ range (n + p + 1), f j) =
      (∑ j ∈ range (2 * p), f j) + ∑ j ∈ range (n - p + 1), f (2 * p + j) := by
    have h := sum_range_add f (2 * p) (n - p + 1)
    rwa [show 2 * p + (n - p + 1) = n + p + 1 by omega] at h
  have hsplit' (f : ℕ → ℝ) : (∑ j ∈ range (n + p), f j) =
      (∑ j ∈ range (2 * p), f j) + ∑ j ∈ range (n - p), f (2 * p + j) := by
    have h := sum_range_add f (2 * p) (n - p)
    rwa [show 2 * p + (n - p) = n + p by omega] at h
  have hmass : (∑ i ∈ range (n + 1), z i ^ 2) ≤
      ∑ j ∈ range (n + p + 1), halfStepChain z p j ^ 2 := by
    rw [hsplit, sum_range_two_mul']
    have horig : (∑ i ∈ range (n + 1), z i ^ 2) =
        (∑ i ∈ range p, z i ^ 2) + ∑ j ∈ range (n - p + 1), z (p + j) ^ 2 := by
      have h := sum_range_add (fun i => z i ^ 2) p (n - p + 1)
      rwa [show p + (n - p + 1) = n + 1 by omega] at h
    rw [horig]
    apply add_le_add
    · apply sum_le_sum
      intro i hi
      have hi' := mem_range.mp hi
      rw [halfStepChain_even z hi'.le, halfStepChain_odd z hi']
      nlinarith [sq_nonneg ((z i + z (i + 1)) / 2)]
    · exact le_of_eq (sum_congr rfl fun j _ => by rw [halfStepChain_late])
  have henergy : (∑ j ∈ range (n + p), (halfStepChain z p (j + 1) - halfStepChain z p j) ^ 2) =
      (1 / 2) * (∑ i ∈ range p, (z (i + 1) - z i) ^ 2) +
        ∑ j ∈ range (n - p), (z (p + j + 1) - z (p + j)) ^ 2 := by
    rw [hsplit', sum_range_two_mul', mul_sum]
    congr 1
    · refine sum_congr rfl fun i hi => ?_
      have hi' := mem_range.mp hi
      rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring, halfStepChain_even z hi'.le,
        halfStepChain_odd z hi', halfStepChain_even z (by omega : i + 1 ≤ p)]
      ring
    · refine sum_congr rfl fun j _ => ?_
      rw [show 2 * p + j + 1 = 2 * p + (j + 1) by ring, halfStepChain_late,
        halfStepChain_late, show p + (j + 1) = p + j + 1 by ring]
  rw [← henergy]
  calc _ ≤ (2 - 2 * Real.cos (Real.pi / (2 * ((n + p : ℕ) : ℝ) + 1))) *
          ∑ j ∈ range (n + p + 1), halfStepChain z p j ^ 2 := mul_le_mul_of_nonneg_left hmass hlam
    _ ≤ _ := hchain

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
