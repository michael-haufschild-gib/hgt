import GaloisForLFunctions.RHTower.ComplexFugacityLeeYangChain

/-!
# Unimodular-fugacity chains are free spins

When every wall fugacity of the complex-fugacity Lee–Yang chain has modulus one, the transfer
matrices `[[1, α],[ᾱu, u]]` have rank one and the chain decouples:

`Z = (1 + α₀u₀) · ∏_{j=1}^{N−1} (1 + α_j ᾱ_{j−1} u_j) · (1 + ᾱ_{N−1} u_N)`.

* `cChainPair_snd_of_norm_eq_one`: `B_{k+1} = u_{k+1} ᾱ_k A_{k+1}`;
* `cChainPair_fst_of_norm_eq_one`: `A_{k+1} = (1 + α₀u₀) ∏_{j=1}^{k} (1 + α_j ᾱ_{j−1} u_j)`;
* `cChainZ_of_norm_eq_one`: the product formula above.

Each factor is a single site in a phase-shifted field, so the zero set of a unimodular chain is a
union of arithmetic progressions (one per site, with spacing `2π/λ_j` for `u_j = e^{−iλ_j z}`).
Fugacities in the open disc interpolate between this free product and the two-configuration
crystal `1 + ∏ u_j` at zero fugacity.
-/

open Complex Finset

namespace RHTower.LeeYangChain

theorem conj_mul_self_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) : (starRingEnd ℂ) a * a = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
  norm_num

theorem cChainPair_snd_of_norm_eq_one {α : ℕ → ℂ} (hα : ∀ k, ‖α k‖ = 1) (u : ℕ → ℂ) (k : ℕ) :
    (cChainPair α u (k + 1)).2 = u (k + 1) * (starRingEnd ℂ) (α k) * (cChainPair α u (k + 1)).1 := by
  simp only [cChainPair]
  rw [mul_assoc, mul_add (starRingEnd ℂ (α k)), ← mul_assoc (starRingEnd ℂ (α k)) (α k),
    conj_mul_self_of_norm_eq_one (hα k), one_mul]

theorem cChainPair_fst_of_norm_eq_one {α : ℕ → ℂ} (hα : ∀ k, ‖α k‖ = 1) (u : ℕ → ℂ) (k : ℕ) :
    (cChainPair α u (k + 1)).1 = (1 + α 0 * u 0) *
      ∏ j ∈ range k, (1 + α (j + 1) * (starRingEnd ℂ) (α j) * u (j + 1)) := by
  induction k with
  | zero => simp [cChainPair, mul_comm]
  | succ k ih =>
    have hB := cChainPair_snd_of_norm_eq_one hα u k
    rw [show (cChainPair α u (k + 1 + 1)).1 =
        (cChainPair α u (k + 1)).1 + α (k + 1) * (cChainPair α u (k + 1)).2 from rfl, hB, ih,
      prod_range_succ]
    ring

/-- **Free-spin factorisation of unimodular chains.** -/
theorem cChainZ_of_norm_eq_one {α : ℕ → ℂ} (hα : ∀ k, ‖α k‖ = 1) (u : ℕ → ℂ) (N : ℕ) :
    cChainZ α u (N + 1) = (1 + α 0 * u 0) *
      (∏ j ∈ range N, (1 + α (j + 1) * (starRingEnd ℂ) (α j) * u (j + 1))) *
        (1 + (starRingEnd ℂ) (α N) * u (N + 1)) := by
  rw [cChainZ, cChainPair_snd_of_norm_eq_one hα u N, cChainPair_fst_of_norm_eq_one hα u N]
  ring

end RHTower.LeeYangChain
