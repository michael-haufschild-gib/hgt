import GaloisForLFunctions.SurfaceOfSpecZ.ThePointCountOfSpecZ

/-!
# Pointwise, the shifts of the point count are dense

The cyclic module of the point count `N(n) = Λ(n) + 1 + 1/(n² − 1)` is spanned by its shifts
`F_k N = (N(kn))_n`. In a ring of sequences the natural topology is that of pointwise
convergence, whose continuous functionals are the finite combinations of the coordinates.

* **No finite relation survives** (`eq_zero_of_forall_sum_mul_pointCount_eq_zero`): if
  `Σ_{n ≤ m} c_n N(kn) = 0` for every `k ≥ 1`, then every `c_n` is zero.

So no nonzero continuous functional vanishes on the cyclic module: it is dense in the space of
all sequences, and every weight line `(n^z)_n` is a pointwise limit of combinations of shifts of
`N`. In this topology the cyclic module of the point count has every weight, and the zeros are
not distinguished. They are distinguished against packets at a scale, where growth is seen
(`contactScale_eq`).

The proof uses the shifts by the multiples of `6` alone. A multiple of `6` is not a prime power,
so `N(6jn) = n²/(n² − t)` with `t = (6j)^{−2}`: the contacts drop out and the jets remain. A
relation among the `n²/(n² − t)`, `n ≤ m`, at infinitely many `t` is a polynomial identity, and
its value at `t = n₀²` isolates `c_{n₀}`.
-/

open Finset Polynomial
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open GaloisForLFunctions.SurfaceOfSpecZ

theorem not_isPrimePow_of_six_dvd {n : ℕ} (h : 6 ∣ n) : ¬ IsPrimePow n := by
  intro hpp
  obtain ⟨p, k, hp, -, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
  have e2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow ((by norm_num : 2 ∣ 6).trans h))
  have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
    (Nat.prime_three.dvd_of_dvd_pow ((by norm_num : 3 ∣ 6).trans h))
  omega

/-- On the multiples of `6` the point count has no contact: `N(6jn) = n²/(n² − (6j)^{−2})`. -/
theorem pointCount_six_mul {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    pointCount (6 * j * n) = (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1 / (6 * (j : ℝ)) ^ 2) := by
  have h2 : 2 ≤ 6 * j * n := by nlinarith
  have hΛ : (Λ (6 * j * n) : ℝ) = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (not_isPrimePow_of_six_dvd ⟨j * n, by ring⟩)
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hA : (6 * (j : ℝ)) ^ 2 ≠ 0 := by positivity
  have hjn : (1 : ℝ) ≤ (j : ℝ) * n := by nlinarith
  have h1 : (6 * (j : ℝ) * n) ^ 2 - 1 ≠ 0 := by nlinarith
  have e : (n : ℝ) ^ 2 - 1 / (6 * (j : ℝ)) ^ 2 =
      ((6 * (j : ℝ) * n) ^ 2 - 1) / (6 * (j : ℝ)) ^ 2 := by
    field_simp
  rw [pointCount_eq h2, hΛ, e]
  push_cast
  field_simp
  ring

/-- **No finite relation among the coordinates survives on the shifts of the point count.** If
`Σ_{n ≤ m} c_n N(kn) = 0` for every `k ≥ 1`, then `c_n = 0` for every `n ≤ m`. -/
theorem eq_zero_of_forall_sum_mul_pointCount_eq_zero {m : ℕ} {c : ℕ → ℝ}
    (h : ∀ k : ℕ, 1 ≤ k → ∑ n ∈ Icc 1 m, c n * pointCount (k * n) = 0) :
    ∀ n ∈ Icc 1 m, c n = 0 := by
  -- the relation at the shifts `6j`, cleared of denominators, as a polynomial in `t = (6j)^{−2}`
  have hroot : ∀ j : ℕ, 1 ≤ j →
      (∑ n ∈ Icc 1 m, C (c n * (n : ℝ) ^ 2) *
        ∏ i ∈ (Icc 1 m).erase n, (C ((i : ℝ) ^ 2) - X) : ℝ[X]).IsRoot
        (1 / (6 * (j : ℝ)) ^ 2) := by
    intro j hj
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have ht1 : 1 / (6 * (j : ℝ)) ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith
    have hfac : ∀ n ∈ Icc 1 m, (n : ℝ) ^ 2 - 1 / (6 * (j : ℝ)) ^ 2 ≠ 0 := fun n hn => by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      linarith
    have hterm : ∀ n ∈ Icc 1 m,
        (C (c n * (n : ℝ) ^ 2) * ∏ i ∈ (Icc 1 m).erase n, (C ((i : ℝ) ^ 2) - X) : ℝ[X]).eval
            (1 / (6 * (j : ℝ)) ^ 2) =
          (∏ i ∈ Icc 1 m, ((i : ℝ) ^ 2 - 1 / (6 * (j : ℝ)) ^ 2)) *
            (c n * pointCount (6 * j * n)) := fun n hn => by
      rw [pointCount_six_mul (Finset.mem_Icc.mp hn).1 hj, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_prod,
        ← Finset.mul_prod_erase (Icc 1 m) (fun i : ℕ => (i : ℝ) ^ 2 - 1 / (6 * (j : ℝ)) ^ 2) hn]
      simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
      field_simp [hfac n hn]
    rw [Polynomial.IsRoot.def, Polynomial.eval_finsetSum, Finset.sum_congr rfl hterm,
      ← Finset.mul_sum, h (6 * j) (by omega), mul_zero]
  have hinj : Function.Injective fun j : ℕ => 1 / (6 * ((j + 1 : ℕ) : ℝ)) ^ 2 := by
    intro a b hab
    have ha : (0 : ℝ) < 6 * ((a + 1 : ℕ) : ℝ) := by positivity
    have hb : (0 : ℝ) < 6 * ((b + 1 : ℕ) : ℝ) := by positivity
    have h1 : (6 * ((a + 1 : ℕ) : ℝ)) ^ 2 = (6 * ((b + 1 : ℕ) : ℝ)) ^ 2 := by
      have h2 : 1 / (6 * ((a + 1 : ℕ) : ℝ)) ^ 2 = 1 / (6 * ((b + 1 : ℕ) : ℝ)) ^ 2 := hab
      rw [div_eq_div_iff (by positivity) (by positivity)] at h2
      linarith
    have h3 : 6 * ((a + 1 : ℕ) : ℝ) = 6 * ((b + 1 : ℕ) : ℝ) :=
      (pow_left_injective₀ (M₀ := ℝ) two_ne_zero) |>.eq_iff.mp (by
        show (⟨6 * ((a + 1 : ℕ) : ℝ), ha.le⟩ : {x : ℝ // 0 ≤ x}).1 ^ 2 = _
        exact h1) |> fun _ => by nlinarith [sq_nonneg (6 * ((a + 1 : ℕ) : ℝ) - 6 * ((b + 1 : ℕ) : ℝ))]
    have h4 : ((a + 1 : ℕ) : ℝ) = ((b + 1 : ℕ) : ℝ) := by linarith
    have h5 : a + 1 = b + 1 := by exact_mod_cast h4
    omega
  have hQ : (∑ n ∈ Icc 1 m, C (c n * (n : ℝ) ^ 2) *
      ∏ i ∈ (Icc 1 m).erase n, (C ((i : ℝ) ^ 2) - X) : ℝ[X]) = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _
      ((Set.infinite_range_of_injective hinj).mono ?_)
    rintro _ ⟨j, rfl⟩
    exact hroot (j + 1) (Nat.succ_pos j)
  -- the value at `t = n₀²` isolates `c_{n₀}`
  intro n₀ hn₀
  have hn₀' : (1 : ℝ) ≤ n₀ := by exact_mod_cast (Finset.mem_Icc.mp hn₀).1
  have heval := congrArg (fun p : ℝ[X] => p.eval ((n₀ : ℝ) ^ 2)) hQ
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_zero] at heval
  rw [Finset.sum_eq_single_of_mem n₀ hn₀ (fun n _ hne => by
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h => hne h.symm, hn₀⟩) (sub_self _),
      mul_zero])] at heval
  have hprod : ∏ i ∈ (Icc 1 m).erase n₀, ((i : ℝ) ^ 2 - (n₀ : ℝ) ^ 2) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    obtain ⟨hne, hi'⟩ := Finset.mem_erase.mp hi
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Icc.mp hi').1
    have hne' : (i : ℝ) ≠ n₀ := by exact_mod_cast hne
    intro h0
    have hsq : ((i : ℝ) - n₀) * ((i : ℝ) + n₀) = 0 := by nlinarith
    rcases mul_eq_zero.mp hsq with h1 | h1
    · exact hne' (by linarith)
    · linarith
  have hn2 : (n₀ : ℝ) ^ 2 ≠ 0 := by positivity
  rcases mul_eq_zero.mp heval with h1 | h1
  · exact (mul_eq_zero.mp h1).resolve_right hn2
  · exact absurd h1 hprod

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
