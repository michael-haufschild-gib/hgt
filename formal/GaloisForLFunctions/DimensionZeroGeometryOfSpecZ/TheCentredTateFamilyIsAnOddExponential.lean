import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.TheWallIsADirichletInversion
import GaloisForLFunctions.WindowTowerOfSpecZ.TheTateFamilyIsAnExponentialOfPointCounts

/-!
# The centred Tate family is an odd exponential

WTZ writes the Jordan family as an exponential on every window: `J_k ≡ exp g_k`,
`g_k(n) = ℓ(n)(n^k − 1)`, `ℓ = Λ/log` (the logarithm of the zeta function of `𝔸^k∖0`). Twisting by
`n^{−k/2}` centres it (`centredTate`, `K_k = ζ(s − k/2)/ζ(s + k/2)`), and the exponent becomes odd:

* **The centred exponent** (`centredExponent`, `centredExponent_apply`):
  `c_k(n) = ℓ(n)(n^{k/2} − n^{−k/2}) = 2ℓ(n) sinh(k log n/2)`, the coefficients of
  `log ζ(s − k/2) − log ζ(s + k/2)`. It is **odd in the dimension** (`centredExponent_neg`),
  nonnegative for `k ≥ 0` (`centredExponent_nonneg`), and `c_k ≈ kΛ` at `k = 0`.
* **The centred family is its exponential on every window** (`expTrunc_sub_centredTate_mem`,
  `windowRep_centredTate_eq_exp`): `ρ_A(K_k) = Σ_{j≤L} ρ_A(c_k)^j/j!` as soon as `e^A < 2^{L+1}`.

So the reflection across the wall is the negation of an exponent: `K_{−k} = exp(−c_k) = K_k^{−1}`
(the Dirichlet inversion `centredTate_neg_mul`). On a window the centred Tate operators form an
exponential curve `k ↦ exp ρ_A(c_k)` whose tangent at `k = 0` is Weil's arithmetic operator `ρ_A(Λ)`;
the exponent is a positive combination of prime-power folds for `k > 0` (counts) and its negative for
`k < 0`. The parity sign that the values acquire across the wall (`centredTate_neg_of_squarefree`)
comes from exponentiating an odd exponent.
-/

noncomputable section

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

open WindowTowerOfSpecZ CohomologyOfWindowsOfSpecZ

/-- The **centred exponent** `c_k(n) = ℓ(n)(n^{k/2} − n^{−k/2})`. -/
def centredExponent (k : ℝ) : ArithmeticFunction ℝ := tateTwist (k / 2) (tateExponent k)

theorem centredExponent_apply (k : ℝ) (n : ℕ) :
    centredExponent k n = primePowerLog n * ((n : ℝ) ^ (k / 2) - (n : ℝ) ^ (-(k / 2))) := by
  rw [centredExponent, tateTwist_apply, tateExponent_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (n : ℝ) ^ k * (n : ℝ) ^ (-(k / 2)) = (n : ℝ) ^ (k / 2) := by
    rw [← Real.rpow_add hn0]; congr 1; ring
  rw [mul_assoc, sub_mul, e, one_mul]

/-- **The centred exponent is odd in the dimension.** -/
theorem centredExponent_neg (k : ℝ) (n : ℕ) : centredExponent (-k) n = -centredExponent k n := by
  rw [centredExponent_apply, centredExponent_apply, show -k / 2 = -(k / 2) by ring, neg_neg]
  ring

/-- In nonnegative dimension the centred exponent is nonnegative. -/
theorem centredExponent_nonneg {k : ℝ} (hk : 0 ≤ k) (n : ℕ) : 0 ≤ centredExponent k n := by
  rw [centredExponent_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact mul_nonneg (primePowerLog_nonneg n)
    (sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)))

theorem tateTwist_mem_truncIdeal (c : ℝ) {N : ℕ} {f : ArithmeticFunction ℝ}
    (hf : f ∈ truncIdeal N) : tateTwist c f ∈ truncIdeal N := fun n h1 hN => by
  rw [tateTwist_apply, hf n h1 hN, zero_mul]

theorem tateTwist_single_one (c a : ℝ) : tateTwist c (single 1 a) = single 1 a := by
  ext n
  rw [tateTwist_apply, single_apply]
  split_ifs with h
  · rw [h.1, Nat.cast_one, Real.one_rpow, mul_one]
  · rw [zero_mul]

/-- The Tate twist commutes with the truncated exponential. -/
theorem tateTwist_expTrunc (c : ℝ) (L : ℕ) (g : ArithmeticFunction ℝ) :
    tateTwist c (expTrunc L g) = expTrunc L (tateTwist c g) := by
  show tateTwistHom c (expTrunc L g) = _
  rw [expTrunc, map_sum, expTrunc]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow]
  show tateTwist c (single 1 _) * tateTwist c g ^ j = _
  rw [tateTwist_single_one]

/-- **The centred Tate family is the exponential of the centred exponent on every window.** -/
theorem expTrunc_sub_centredTate_mem {N L : ℕ} (hNL : N < 2 ^ (L + 1)) (k : ℝ) :
    expTrunc L (centredExponent k) - centredTate k ∈ truncIdeal N := by
  have h := tateTwist_mem_truncIdeal (k / 2) (expTrunc_sub_jordan_mem hNL k)
  have e : tateTwist (k / 2) (expTrunc L (tateExponent k) - jordanFun k) =
      expTrunc L (centredExponent k) - centredTate k := by
    show tateTwistHom (k / 2) _ = _
    rw [map_sub]
    show tateTwist (k / 2) (expTrunc L (tateExponent k)) - tateTwist (k / 2) (jordanFun k) = _
    rw [tateTwist_expTrunc]
    rfl
  rwa [e] at h

/-- **On a window the centred Tate operator is an exponential**: `ρ_A(K_k) = Σ_{j≤L} ρ_A(c_k)^j/j!`
when `e^A < 2^{L+1}`. -/
theorem windowRep_centredTate_eq_exp {A : ℝ} {L : ℕ} (hL : windowLevel A < 2 ^ (L + 1)) (k : ℝ) :
    windowRep A (centredTate k) = ∑ j ∈ Finset.range (L + 1),
      windowRep A (single 1 ((j.factorial : ℝ)⁻¹)) * windowRep A (centredExponent k) ^ j := by
  have h := windowRep_eq_zero_of_mem (expTrunc_sub_centredTate_mem (N := windowLevel A) hL k)
  rw [map_sub, sub_eq_zero] at h
  rw [← h, expTrunc, map_sum]
  simp only [map_mul, map_pow]

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ
