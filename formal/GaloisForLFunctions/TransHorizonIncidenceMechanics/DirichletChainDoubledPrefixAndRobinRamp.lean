import GaloisForLFunctions.RHTower.AutocorrelationChainSineCertificate

/-!
# Dirichlet chains with a soft prefix and a Robin ramp

A finite chain `z₀ = 0, z₁, …, zₙ, z_{n+1} = 0` with both ends pinned satisfies the discrete
Dirichlet inequality `(2 - 2 cos(π/(n+1))) Σ z² ≤ Σ (Δz)²`. Two soft boundary mechanisms reduce
to it without changing the leading constant:

* **Soft prefix.** Steps carrying only half weight are split into two half-steps. A prefix of
  `p` half-weighted steps lengthens the chain by `p`.
* **Robin ramp.** A terminal value `y` whose continuation halves forever costs exactly `y²/3` of
  jump energy beyond the last site; a three-step linear ramp to zero costs the same `y²/3`.

Together they give the Dirichlet constant `2 - 2 cos(π/(D + m + 5))` for a chain of `D + 1` free
sites whose first `m + 1` steps are half-weighted and whose top continues by halving. This is
the boundary structure of a dyadic ray observed through all of its Fermi boundaries.
-/

open Finset

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- Energy form of the Dirichlet chain bound: `λ Σ x² ≤ Σ (Δx)²` with `λ = 2 - 2 cos(π/(n+1))`. -/
theorem dirichlet_chain_energy_bound (n : ℕ) (x : ℕ → ℝ) (h0 : x 0 = 0)
    (hend : x (n + 1) = 0) :
    (2 - 2 * Real.cos (Real.pi / ((n : ℝ) + 1))) * (∑ k ∈ range (n + 1), x k ^ 2) ≤
      ∑ k ∈ range (n + 1), (x (k + 1) - x k) ^ 2 := by
  have hb := RHTower.autocorrelation_chain_sine_bound n x h0 hend
  have hshift : (∑ k ∈ range (n + 1), x (k + 1) ^ 2) = ∑ k ∈ range (n + 1), x k ^ 2 := by
    rw [sum_range_succ (fun k => x (k + 1) ^ 2), sum_range_succ' (fun k => x k ^ 2), hend, h0]
  have he : (∑ k ∈ range (n + 1), (x (k + 1) - x k) ^ 2) =
      (∑ k ∈ range (n + 1), x (k + 1) ^ 2) + (∑ k ∈ range (n + 1), x k ^ 2) -
        2 * ∑ k ∈ range (n + 1), x k * x (k + 1) := by
    rw [← sum_add_distrib, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [he, hshift]
  nlinarith [hb]

private theorem sum_range_two_mul (p : ℕ) (g : ℕ → ℝ) :
    (∑ j ∈ range (2 * p), g j) = ∑ i ∈ range p, (g (2 * i) + g (2 * i + 1)) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [show 2 * (p + 1) = 2 * p + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring_nf

/-- The chain with its first `p` steps split into half-steps. -/
private def softPrefixChain (z : ℕ → ℝ) (p j : ℕ) : ℝ :=
  if j < 2 * p then (if j % 2 = 0 then z (j / 2) else (z (j / 2) + z (j / 2 + 1)) / 2)
  else z (j - p)

private theorem softPrefixChain_even (z : ℕ → ℝ) {p i : ℕ} (hi : i ≤ p) :
    softPrefixChain z p (2 * i) = z i := by
  unfold softPrefixChain
  split_ifs with h1 h2
  · congr 1; omega
  · omega
  · congr 1; omega

private theorem softPrefixChain_odd (z : ℕ → ℝ) {p i : ℕ} (hi : i < p) :
    softPrefixChain z p (2 * i + 1) = (z i + z (i + 1)) / 2 := by
  unfold softPrefixChain
  rw [if_pos (by omega), if_neg (by omega)]
  congr 2 <;> congr 1 <;> omega

private theorem softPrefixChain_late (z : ℕ → ℝ) (p j : ℕ) :
    softPrefixChain z p (2 * p + j) = z (p + j) := by
  unfold softPrefixChain
  rw [if_neg (by omega)]
  congr 1; omega

/-- **Soft-prefix Dirichlet bound.** For a pinned chain whose first `p` steps carry half weight,
`(2 - 2 cos(π/(n+p+1))) Σ z² ≤ ½ Σ_{i<p} (Δz)² + Σ_{p≤i≤n} (Δz)²`. -/
theorem dirichlet_chain_soft_prefix_bound (n p : ℕ) (hp : p ≤ n + 1) (z : ℕ → ℝ)
    (h0 : z 0 = 0) (hend : z (n + 1) = 0) :
    (2 - 2 * Real.cos (Real.pi / (((n + p : ℕ) : ℝ) + 1))) *
        (∑ i ∈ range (n + 1), z i ^ 2) ≤
      (1 / 2) * (∑ i ∈ range p, (z (i + 1) - z i) ^ 2) +
        ∑ j ∈ range (n + 1 - p), (z (p + j + 1) - z (p + j)) ^ 2 := by
  have hu0 : softPrefixChain z p 0 = 0 := by
    rcases Nat.eq_zero_or_pos p with rfl | hpos
    · simp [softPrefixChain, h0]
    · simpa [h0] using softPrefixChain_even z (p := p) (i := 0) (Nat.zero_le _)
  have hue : softPrefixChain z p (n + p + 1) = 0 := by
    have := softPrefixChain_late z p (n + 1 - p)
    rw [show 2 * p + (n + 1 - p) = n + p + 1 by omega,
      show p + (n + 1 - p) = n + 1 by omega, hend] at this
    exact this
  have hlam : 0 ≤ 2 - 2 * Real.cos (Real.pi / (((n + p : ℕ) : ℝ) + 1)) := by
    linarith [Real.cos_le_one (Real.pi / (((n + p : ℕ) : ℝ) + 1))]
  have hchain := dirichlet_chain_energy_bound (n + p) (softPrefixChain z p) hu0
    (by simpa using hue)
  have hsplit (f : ℕ → ℝ) : (∑ j ∈ range (n + p + 1), f j) =
      (∑ j ∈ range (2 * p), f j) + ∑ j ∈ range (n + 1 - p), f (2 * p + j) := by
    have h := sum_range_add f (2 * p) (n + 1 - p)
    rwa [show 2 * p + (n + 1 - p) = n + p + 1 by omega] at h
  -- mass of the split chain dominates the original mass
  have hmass : (∑ i ∈ range (n + 1), z i ^ 2) ≤
      ∑ j ∈ range (n + p + 1), softPrefixChain z p j ^ 2 := by
    rw [hsplit, sum_range_two_mul]
    have horig : (∑ i ∈ range (n + 1), z i ^ 2) =
        (∑ i ∈ range p, z i ^ 2) + ∑ j ∈ range (n + 1 - p), z (p + j) ^ 2 := by
      have h := sum_range_add (fun i => z i ^ 2) p (n + 1 - p)
      rwa [show p + (n + 1 - p) = n + 1 by omega] at h
    rw [horig]
    apply add_le_add
    · apply sum_le_sum
      intro i hi
      have hi' := mem_range.mp hi
      rw [softPrefixChain_even z hi'.le, softPrefixChain_odd z hi']
      nlinarith [sq_nonneg ((z i + z (i + 1)) / 2)]
    · apply le_of_eq
      apply sum_congr rfl
      intro j _
      rw [softPrefixChain_late]
  -- energy of the split chain
  have henergy : (∑ j ∈ range (n + p + 1),
      (softPrefixChain z p (j + 1) - softPrefixChain z p j) ^ 2) =
      (1 / 2) * (∑ i ∈ range p, (z (i + 1) - z i) ^ 2) +
        ∑ j ∈ range (n + 1 - p), (z (p + j + 1) - z (p + j)) ^ 2 := by
    rw [hsplit, sum_range_two_mul, mul_sum]
    congr 1
    · apply sum_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring, softPrefixChain_even z hi'.le,
        softPrefixChain_odd z hi', softPrefixChain_even z (by omega : i + 1 ≤ p)]
      ring
    · apply sum_congr rfl
      intro j _
      rw [show 2 * p + j + 1 = 2 * p + (j + 1) by ring, softPrefixChain_late,
        softPrefixChain_late, show p + (j + 1) = p + j + 1 by ring]
  rw [← henergy]
  calc _ ≤ (2 - 2 * Real.cos (Real.pi / (((n + p : ℕ) : ℝ) + 1))) *
          ∑ j ∈ range (n + p + 1), softPrefixChain z p j ^ 2 :=
        mul_le_mul_of_nonneg_left hmass hlam
    _ ≤ _ := by simpa using hchain

/-- A ray of `D + 1` free sites, pinned below by a virtual zero and continued above by a
three-step ramp to zero. -/
private def rampChain (y : ℕ → ℝ) (D i : ℕ) : ℝ :=
  if i = 0 then 0 else if i ≤ D + 1 then y (i - 1)
  else if i = D + 2 then 2 / 3 * y D else if i = D + 3 then y D / 3 else 0

/-- **Ray bound with soft prefix and Robin ramp.** For every sequence `y`, cutoff `m ≤ D`:
`(2 - 2 cos(π/(D+m+5))) Σ_{k≤D} y_k² ≤ ½ (y₀² + Σ_{k<m} (y_k - y_{k+1})²)
  + Σ_{m≤k<D} (y_k - y_{k+1})² + y_D²/3`. -/
theorem ray_dirichlet_robin_bound (D m : ℕ) (hm : m ≤ D) (y : ℕ → ℝ) :
    (2 - 2 * Real.cos (Real.pi / (((D + m + 4 : ℕ) : ℝ) + 1))) *
        (∑ k ∈ range (D + 1), y k ^ 2) ≤
      (1 / 2) * (y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2) +
        (∑ j ∈ range (D - m), (y (m + j) - y (m + j + 1)) ^ 2) + y D ^ 2 / 3 := by
  have hz0 : rampChain y D 0 = 0 := by simp [rampChain]
  have hzend : rampChain y D (D + 3 + 1) = 0 := by
    unfold rampChain
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hzy (k : ℕ) (hk : k ≤ D) : rampChain y D (k + 1) = y k := by
    unfold rampChain
    rw [if_neg (by omega), if_pos (by omega)]
    rfl
  have hz2 : rampChain y D (D + 2) = 2 / 3 * y D := by
    unfold rampChain
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
  have hz3 : rampChain y D (D + 3) = y D / 3 := by
    unfold rampChain
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  have h := dirichlet_chain_soft_prefix_bound (D + 3) (m + 1) (by omega) (rampChain y D)
    hz0 hzend
  rw [show D + 3 + (m + 1) = D + m + 4 by ring] at h
  have hlam : 0 ≤ 2 - 2 * Real.cos (Real.pi / (((D + m + 4 : ℕ) : ℝ) + 1)) := by
    linarith [Real.cos_le_one (Real.pi / (((D + m + 4 : ℕ) : ℝ) + 1))]
  -- mass
  have hmass : (∑ k ∈ range (D + 1), y k ^ 2) ≤
      ∑ i ∈ range (D + 3 + 1), rampChain y D i ^ 2 := by
    rw [sum_range_succ' (fun i => rampChain y D i ^ 2), hz0]
    have hsub : (∑ k ∈ range (D + 1), y k ^ 2) =
        ∑ k ∈ range (D + 1), rampChain y D (k + 1) ^ 2 :=
      sum_congr rfl fun k hk => by rw [hzy k (by have := mem_range.mp hk; omega)]
    rw [hsub]
    have := sum_le_sum_of_subset_of_nonneg (range_mono (show D + 1 ≤ D + 3 by omega))
      (fun k _ _ => sq_nonneg (rampChain y D (k + 1)))
    linarith [sq_nonneg (0 : ℝ)]
  -- soft prefix energy
  have hpre : (∑ i ∈ range (m + 1), (rampChain y D (i + 1) - rampChain y D i) ^ 2) =
      y 0 ^ 2 + ∑ k ∈ range m, (y k - y (k + 1)) ^ 2 := by
    rw [sum_range_succ', hz0, hzy 0 (by omega)]
    have : (∑ k ∈ range m, (rampChain y D (k + 1 + 1) - rampChain y D (k + 1)) ^ 2) =
        ∑ k ∈ range m, (y k - y (k + 1)) ^ 2 := by
      apply sum_congr rfl
      intro k hk
      have hk' := mem_range.mp hk
      rw [hzy (k + 1) (by omega), hzy k (by omega)]
      ring
    rw [this]
    ring
  -- remaining energy: the bulk differences and the three ramp steps
  have hrest : (∑ j ∈ range (D + 3 + 1 - (m + 1)),
      (rampChain y D (m + 1 + j + 1) - rampChain y D (m + 1 + j)) ^ 2) =
      (∑ j ∈ range (D - m), (y (m + j) - y (m + j + 1)) ^ 2) + y D ^ 2 / 3 := by
    rw [show D + 3 + 1 - (m + 1) = D - m + 1 + 1 + 1 by omega, sum_range_succ,
      sum_range_succ, sum_range_succ]
    have hbulk : (∑ j ∈ range (D - m),
        (rampChain y D (m + 1 + j + 1) - rampChain y D (m + 1 + j)) ^ 2) =
        ∑ j ∈ range (D - m), (y (m + j) - y (m + j + 1)) ^ 2 := by
      apply sum_congr rfl
      intro j hj
      have hj' := mem_range.mp hj
      rw [show m + 1 + j + 1 = (m + j + 1) + 1 by ring, hzy (m + j + 1) (by omega),
        show m + 1 + j = (m + j) + 1 by ring, hzy (m + j) (by omega)]
      ring
    rw [hbulk, show m + 1 + (D - m) = D + 1 by omega,
      show m + 1 + (D - m + 1) = D + 2 by omega, show m + 1 + (D - m + 1 + 1) = D + 3 by omega,
      show D + 1 + 1 = D + 2 by ring, show D + 2 + 1 = D + 3 by ring, hz2, hz3, hzend,
      hzy D le_rfl]
    ring
  rw [hpre, hrest] at h
  calc _ ≤ (2 - 2 * Real.cos (Real.pi / (((D + m + 4 : ℕ) : ℝ) + 1))) *
        ∑ i ∈ range (D + 3 + 1), rampChain y D i ^ 2 := mul_le_mul_of_nonneg_left hmass hlam
    _ ≤ _ := by linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
