import GaloisForLFunctions.HTGeometry.BinomialTailBetaThreshold

/-!
# The binomial tail polynomial has derivative at most its replica order

The derivative of the binomial tail polynomial is the replica order times one binomial probability
term.  Every such term is a single summand of the binomial expansion of one, and all summands are
nonnegative, so the term never exceeds one and the derivative never exceeds the replica order.

Consequently the bounded replica reporter is Lipschitz with constant the replica order, which is the
only regularity its influence estimates use.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

section BinomialDerivative

/-- A single binomial probability term never exceeds one. -/
theorem binomialTerm_prob_le_one {n i : ℕ} (hi : i ≤ n) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (n.choose i : ℝ) * u ^ i * (1 - u) ^ (n - i) ≤ 1 := by
  have hone : ((u + (1 - u)) : ℝ) ^ n = 1 := by
    rw [show u + (1 - u) = (1 : ℝ) by ring, one_pow]
  have hexp : ((u + (1 - u)) : ℝ) ^ n =
      ∑ m ∈ Finset.range (n + 1), u ^ m * (1 - u) ^ (n - m) * (n.choose m : ℝ) :=
    add_pow u (1 - u) n
  have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hnn : ∀ m ∈ Finset.range (n + 1),
      0 ≤ u ^ m * (1 - u) ^ (n - m) * (n.choose m : ℝ) := by
    intro m _
    have h1 : (0 : ℝ) ≤ 1 - u := by linarith
    positivity
  have hsingle := Finset.single_le_sum hnn hmem
  rw [← hexp, hone] at hsingle
  calc (n.choose i : ℝ) * u ^ i * (1 - u) ^ (n - i)
      = u ^ i * (1 - u) ^ (n - i) * (n.choose i : ℝ) := by ring
    _ ≤ 1 := hsingle

/-- **The replica reporter derivative is bounded by the replica order.** -/
theorem betaKernel_le_replicaOrder (r k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : betaKernel r k u ≤ (r : ℝ) := by
  have hr : 1 ≤ r := le_trans hk1 hkr
  have hterm : ((r - 1).choose (k - 1) : ℝ) * u ^ (k - 1) * (1 - u) ^ (r - k) ≤ 1 := by
    have hle : k - 1 ≤ r - 1 := by omega
    have hsub : (r - 1) - (k - 1) = r - k := by omega
    have h := binomialTerm_prob_le_one (n := r - 1) (i := k - 1) hle hu0 hu1
    rwa [hsub] at h
  have hkernel : betaKernel r k u =
      (r : ℝ) * (((r - 1).choose (k - 1) : ℝ) * u ^ (k - 1) * (1 - u) ^ (r - k)) := by
    unfold betaKernel
    ring
  rw [hkernel]
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  nlinarith [hterm, hr0]

/-- The bounded replica reporter is Lipschitz with constant the replica order on the unit
interval. -/
theorem abs_binomialTail_sub_le (r k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r) {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    |binomialTail r k u - binomialTail r k v| ≤ (r : ℝ) * |u - v| := by
  have hderiv : ∀ x ∈ Set.uIcc v u, HasDerivAt (binomialTail r k) (betaKernel r k x) x :=
    fun x _ => hasDerivAt_binomialTail r k hk1 hkr x
  have hbound : ∀ x ∈ Set.uIcc v u, ‖betaKernel r k x‖ ≤ (r : ℝ) := by
    intro x hx
    have hx0 : 0 ≤ x := by
      rcases Set.mem_uIcc.mp hx with h | h
      · linarith [h.1]
      · linarith [h.1]
    have hx1 : x ≤ 1 := by
      rcases Set.mem_uIcc.mp hx with h | h
      · linarith [h.2]
      · linarith [h.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (betaKernel_nonneg hx0 hx1 r k)]
    exact betaKernel_le_replicaOrder r k hk1 hkr hx0 hx1
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := binomialTail r k) (f' := betaKernel r k) (C := (r : ℝ))
    (fun x hx => (hderiv x hx).hasDerivWithinAt) hbound (convex_uIcc v u)
    (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

end BinomialDerivative

end GaloisForLFunctions.HTGeometry
