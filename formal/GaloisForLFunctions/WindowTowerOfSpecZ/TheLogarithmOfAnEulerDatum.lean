import GaloisForLFunctions.WindowTowerOfSpecZ.TheTateFamilyIsAnExponentialOfPointCounts

/-!
# The logarithm of an Euler datum

An Euler datum `(F, G)`, `F * G = 1`, has a **logarithm** `g` when `D F = (D g) * F` and `g(1) = 0`
(`D` the degree derivation): `F ≡ exp g` on every window. Its Tate family is then the exponential
of the Tate-twisted increment of the logarithm:

* **Exponential form** (`expTrunc_sub_tateFamily_mem`): `J^F_k ≡ exp(g·(n^k − 1))` on every window,
  because `D J^F_k = D(twist_{−k} g − g) * J^F_k` (`degD_tateFamily`).
* **Positive logarithm ⇒ Tate positivity in every real dimension**
  (`tateFamily_ge_of_log_nonneg`): if `g ≥ 0`, then for every real `k ≥ 0` and every `n`,
  `J^F_k(n) ≥ [n = 1] + g(n)(n^k − 1) ≥ 0`.
* **The shifted datum** `ζ(s)ζ(s − ε)` has the positive logarithm `ℓ + ℓ·n^ε`
  (`degD_shiftedDatum`), so it is Tate positive in every real dimension `k ≥ 0` at every integer
  (`shiftedDatum_tateFamily_ge`), although its zeros `ρ + ε` lie off the line. Positivity of the
  logarithm is soft: Tate positivity selects only against data whose logarithm is negative somewhere
  (flip twins: `ℓ_F(p) = −1`), and the quadratic `L(s, χ)` — whose logarithm `χℓ` is negative at the
  inert primes — fails it too. Selection is not by the sign of the logarithm.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ ArithmeticDegenerationTheory

variable {F G g : ArithmeticFunction ℝ}

theorem apply_one_of_mul_eq_one (hFG : F * G = 1) (hF1 : F 1 = 1) : G 1 = 1 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f 1) hFG
  simp only [ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one, Finset.sum_singleton,
    ArithmeticFunction.one_one, hF1, one_mul] at h
  exact h

/-- The inverse of a datum with logarithm `g` has logarithm `−g`: `D G = −(D g) * G`. -/
theorem degD_inverse (hFG : F * G = 1) (hD : degD F = degD g * F) : degD G = -(degD g * G) := by
  have h1 : degD (F * G) = 0 := by
    rw [hFG]; ext n; rw [degD_apply, ArithmeticFunction.one_apply]
    split_ifs with h
    · rw [h, Nat.cast_one, Real.log_one, mul_zero]; rfl
    · rw [zero_mul]; rfl
  rw [degD_mul, hD] at h1
  have h2 : degD G = G * F * degD G := by rw [mul_comm G F, hFG, one_mul]
  have h3 : F * degD G = -(degD g * (F * G)) := by linear_combination h1
  rw [hFG, mul_one] at h3
  rw [h2, mul_assoc, h3]; ring

/-- `D J^F_k = D(twist_{−k} g − g) * J^F_k`. -/
theorem degD_tateFamily (hFG : F * G = 1) (hD : degD F = degD g * F) (k : ℝ) :
    degD (tateFamily F G k) = degD (tateTwist (-k) g - g) * tateFamily F G k := by
  rw [tateFamily, degD_mul, degD_tateTwist, hD, tateTwist_mul, degD_inverse hFG hD, degD_sub,
    degD_tateTwist]
  ring

/-- **The Tate family of a datum with a logarithm is an exponential**:
`J^F_k ≡ exp(twist_{−k} g − g)` on every window. -/
theorem expTrunc_sub_tateFamily_mem {N L : ℕ} (hNL : N < 2 ^ (L + 1)) (hFG : F * G = 1)
    (hF1 : F 1 = 1) (hg1 : g 1 = 0) (hD : degD F = degD g * F) (k : ℝ) :
    expTrunc L (tateTwist (-k) g - g) - tateFamily F G k ∈ truncIdeal N := by
  refine expTrunc_sub_mem hNL (by rw [sub_apply', tateTwist_apply, hg1, zero_mul, sub_zero]) ?_ ?_
  · rw [tateFamily, ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one,
      Finset.sum_singleton, tateTwist_apply, hF1, apply_one_of_mul_eq_one hFG hF1]
    simp
  · rw [degD_tateFamily hFG hD, sub_self]; exact Submodule.zero_mem _

theorem tateIncrement_apply (k : ℝ) (n : ℕ) :
    (tateTwist (-k) g - g) n = g n * ((n : ℝ) ^ k - 1) := by
  rw [sub_apply', tateTwist_apply, neg_neg]; ring

/-- **A positive logarithm makes the datum Tate positive in every real dimension**:
`J^F_k(n) ≥ [n = 1] + g(n)(n^k − 1)` for `k ≥ 0`. -/
theorem tateFamily_ge_of_log_nonneg (hFG : F * G = 1) (hF1 : F 1 = 1) (hg1 : g 1 = 0)
    (hD : degD F = degD g * F) (hg : ∀ n, 0 ≤ g n) {k : ℝ} (hk : 0 ≤ k) (n : ℕ) :
    (if n = 1 then 1 else 0) + g n * ((n : ℝ) ^ k - 1) ≤ tateFamily F G k n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hinc : ∀ m, 0 ≤ (tateTwist (-k) g - g) m := fun m => by
    rw [tateIncrement_apply]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    exact mul_nonneg (hg m) (sub_nonneg.mpr (Real.one_le_rpow (by exact_mod_cast hm) hk))
  have hmem := expTrunc_sub_tateFamily_mem (N := n) (L := n)
    (Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (by omega))) hFG hF1 hg1 hD k
    n hn le_rfl
  rw [sub_apply', sub_eq_zero] at hmem
  rw [← hmem, expTrunc, finsetSum_apply]
  have hterm : ∀ j ∈ Finset.range (n + 1), 0 ≤
      (single 1 ((j.factorial : ℝ)⁻¹) * (tateTwist (-k) g - g) ^ j) n := fun j _ => by
    rw [single_one_mul_apply]
    exact mul_nonneg (by positivity) (pow_apply_nonneg hinc j n)
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (n + 1) := by
    intro j hj
    rw [Finset.mem_insert, Finset.mem_singleton] at hj
    rw [Finset.mem_range]; omega
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsub fun j hj _ => hterm j hj)
  rw [Finset.sum_pair zero_ne_one, single_one_mul_apply, single_one_mul_apply, pow_zero, pow_one,
    ArithmeticFunction.one_apply, tateIncrement_apply]
  simp

/-! ### The shifted datum -/

/-- `ζ` has the logarithm `ℓ`. -/
theorem degD_zeta :
    degD (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      degD primePowerLog * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
  rw [degD_primePowerLog, degD, RHTower.zeta_pmul_log, ArithmeticFunction.vonMangoldt_mul_zeta]

/-- `ζ(s)ζ(s − ε)` has the logarithm `ℓ + ℓ·n^ε`. -/
theorem degD_shiftedDatum (ε : ℝ) :
    degD (shiftedDatum ε) = degD (primePowerLog + tateTwist (-ε) primePowerLog) * shiftedDatum ε := by
  rw [shiftedDatum, degD_mul, degD_tateTwist, degD_zeta, degD_add, degD_tateTwist, tateTwist_mul]
  ring

theorem shiftedDatum_one (ε : ℝ) : shiftedDatum ε 1 = 1 := by
  rw [shiftedDatum, ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one,
    Finset.sum_singleton, tateTwist_apply]
  simp

/-- **The shifted datum is Tate positive in every real dimension**, at every integer:
`J^{F_ε}_k(n) ≥ [n = 1] + ℓ(n)(1 + n^ε)(n^k − 1)` for `k ≥ 0`. -/
theorem shiftedDatum_tateFamily_ge (ε : ℝ) {k : ℝ} (hk : 0 ≤ k) (n : ℕ) :
    (if n = 1 then 1 else 0) + (primePowerLog + tateTwist (-ε) primePowerLog) n * ((n : ℝ) ^ k - 1) ≤
      tateFamily (shiftedDatum ε) (shiftedInverse ε) k n := by
  refine tateFamily_ge_of_log_nonneg (shiftedDatum_mul_inverse ε) (shiftedDatum_one ε)
    (by rw [ArithmeticFunction.add_apply, tateTwist_apply, primePowerLog_one, zero_mul, add_zero])
    (degD_shiftedDatum ε) (fun m => ?_) hk n
  rw [ArithmeticFunction.add_apply, tateTwist_apply]
  exact add_nonneg (primePowerLog_nonneg m)
    (mul_nonneg (primePowerLog_nonneg m) (Real.rpow_nonneg (Nat.cast_nonneg m) _))

end GaloisForLFunctions.WindowTowerOfSpecZ
