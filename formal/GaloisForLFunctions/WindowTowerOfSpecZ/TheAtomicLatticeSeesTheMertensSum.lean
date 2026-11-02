import GaloisForLFunctions.WindowTowerOfSpecZ.TheAtomicLatticeOfAWindow

/-!
# The atomic lattice sees the Mertens sum

On general window tests the arithmetic term of Weil's form reaches the canonical degree:
`|⟨ρ_A(Λ)H, H⟩|` can be as large as `ψ_{1/2}(e^A)‖H‖² ≈ 2e^{A/2}‖H‖²` (wide, slowly varying tests).
On the atomic lattice it is exponentially smaller:

* **Mertens bound** (`abs_sum_vonMangoldt_mul_le`): for every `g`,
  `|Σ_{k≤N} (Λ * g)(k) g(k)/k| ≤ ½(Σ_{d≤N} Λ(d)/d + log N)·Σ_{k≤N} g(k)²/k`.
  Each term `Λ(d)g(m)g(dm)/(dm)` is split by AM–GM; the first halves sum to the Mertens sum
  `Σ_{d≤N/m} Λ(d)/d`, the second to `Σ_{d∣k} Λ(d) = log k`.
* **On atomic window tests** (`abs_integral_windowRep_vonMangoldt_atomic_le`):
  `|⟨ρ_A(Λ)ιg, ιg⟩| ≤ ½(Σ_{d≤N} Λ(d)/d + log N)·‖ιg‖²`.

The Mertens sum is `log N + O(1) ≈ A`, against `ψ_{1/2}(N) ≈ 2√N` for the canonical class: the
canonical class is invisible to the integers of the window. Numerically the extreme eigenvalues of
the atomic arithmetic form are `≈ ±½ log N`, so the constant is sharp to leading order. The
negativity of a long window does not live on its atoms; it lives on wide tests, where the folds
overlap the canonical class.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ

/-- Pointwise AM–GM for one term: `|Λ(d) g(m) g(dm)|/(dm) ≤ ½Λ(d)(g(m)² + g(dm)²)/(dm)`. -/
theorem abs_term_le (d m : ℕ) (g : ArithmeticFunction ℝ) :
    |ArithmeticFunction.vonMangoldt d * g m * g (d * m) / ((d * m : ℕ) : ℝ)| ≤
      ArithmeticFunction.vonMangoldt d * (g m ^ 2 + g (d * m) ^ 2) / 2 / ((d * m : ℕ) : ℝ) := by
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (d * m))]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [abs_mul, abs_mul, abs_of_nonneg hΛ, mul_assoc, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hΛ
  nlinarith [sq_nonneg (|g m| - |g (d * m)|), sq_abs (g m), sq_abs (g (d * m))]

/-- **The Mertens bound** for the arithmetic form on the truncated Dirichlet ring. -/
theorem abs_sum_vonMangoldt_mul_le (N : ℕ) (g : ArithmeticFunction ℝ) :
    |∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt * g) k * g k / k| ≤
      (∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d / d + Real.log N) / 2 *
        ∑ k ∈ Finset.Icc 1 N, g k ^ 2 / k := by
  set Λ := (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ)
  -- expand the convolution and regroup by the factorization `k = d m`
  have hexp : ∑ k ∈ Finset.Icc 1 N, (Λ * g) k * g k / k =
      ∑ x ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun x => x.1 * x.2 ≤ N),
        Λ x.1 * g x.2 * g (x.1 * x.2) / ((x.1 * x.2 : ℕ) : ℝ) := by
    rw [← sum_Icc_divisorsAntidiagonal]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ArithmeticFunction.mul_apply, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  set S := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun x => x.1 * x.2 ≤ N)
  have hsplit : ∀ x ∈ S, Λ x.1 * (g x.2 ^ 2 + g (x.1 * x.2) ^ 2) / 2 / ((x.1 * x.2 : ℕ) : ℝ) =
      (Λ x.1 / x.1) * (g x.2 ^ 2 / x.2) / 2 +
        Λ x.1 * (g (x.1 * x.2) ^ 2 / ((x.1 * x.2 : ℕ) : ℝ)) / 2 := fun x hx => by
    obtain ⟨hp, _⟩ := Finset.mem_filter.mp hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    have ha : (0 : ℝ) < x.1 := by exact_mod_cast (Finset.mem_Icc.mp h1).1
    have hb : (0 : ℝ) < x.2 := by exact_mod_cast (Finset.mem_Icc.mp h2).1
    rw [Nat.cast_mul]
    field_simp
  -- first half: the Mertens sum
  have hfirst : ∑ x ∈ S, (Λ x.1 / x.1) * (g x.2 ^ 2 / x.2) / 2 ≤
      (∑ d ∈ Finset.Icc 1 N, Λ d / d) / 2 * ∑ k ∈ Finset.Icc 1 N, g k ^ 2 / k := by
    have hnn : ∀ x : ℕ × ℕ, 0 ≤ (Λ x.1 / x.1) * (g x.2 ^ 2 / x.2) / 2 := fun x =>
      div_nonneg (mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
        (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))) (by norm_num)
    calc ∑ x ∈ S, (Λ x.1 / x.1) * (g x.2 ^ 2 / x.2) / 2
        ≤ ∑ x ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, (Λ x.1 / x.1) * (g x.2 ^ 2 / x.2) / 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ => hnn x
      _ = (∑ d ∈ Finset.Icc 1 N, Λ d / d) / 2 * ∑ k ∈ Finset.Icc 1 N, g k ^ 2 / k := by
          rw [Finset.sum_product, Finset.sum_div, Finset.sum_mul]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by dsimp only; ring
  -- second half: `Σ_{d∣k} Λ(d) = log k ≤ log N`
  have hsecond : ∑ x ∈ S, Λ x.1 * (g (x.1 * x.2) ^ 2 / ((x.1 * x.2 : ℕ) : ℝ)) / 2 ≤
      Real.log N / 2 * ∑ k ∈ Finset.Icc 1 N, g k ^ 2 / k := by
    rw [← sum_Icc_divisorsAntidiagonal N (fun x => Λ x.1 * (g (x.1 * x.2) ^ 2 /
      ((x.1 * x.2 : ℕ) : ℝ)) / 2), Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hkN := (Finset.mem_Icc.mp hk).2
    have hcongr : ∑ x ∈ k.divisorsAntidiagonal, Λ x.1 * (g (x.1 * x.2) ^ 2 /
        ((x.1 * x.2 : ℕ) : ℝ)) / 2 = (∑ x ∈ k.divisorsAntidiagonal, Λ x.1) * (g k ^ 2 / k) / 2 := by
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
    rw [hcongr, Nat.sum_divisorsAntidiagonal (fun a _ => Λ a), ArithmeticFunction.vonMangoldt_sum]
    have hlog : Real.log k ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast hk1) (by exact_mod_cast hkN)
    have hg : 0 ≤ g k ^ 2 / k := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    nlinarith
  rw [hexp]
  calc |∑ x ∈ S, Λ x.1 * g x.2 * g (x.1 * x.2) / ((x.1 * x.2 : ℕ) : ℝ)|
      ≤ ∑ x ∈ S, |Λ x.1 * g x.2 * g (x.1 * x.2) / ((x.1 * x.2 : ℕ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ S, Λ x.1 * (g x.2 ^ 2 + g (x.1 * x.2) ^ 2) / 2 / ((x.1 * x.2 : ℕ) : ℝ) :=
        Finset.sum_le_sum fun x _ => abs_term_le x.1 x.2 g
    _ = ∑ x ∈ S, ((Λ x.1 / x.1) * (g x.2 ^ 2 / x.2) / 2 +
          Λ x.1 * (g (x.1 * x.2) ^ 2 / ((x.1 * x.2 : ℕ) : ℝ)) / 2) := Finset.sum_congr rfl hsplit
    _ ≤ _ := by
        rw [Finset.sum_add_distrib]
        linarith

/-- **The atomic lattice sees only the Mertens sum**: on atomic window tests of level `N`,
`|⟨ρ_A(Λ)ιg, ιg⟩| ≤ ½(Σ_{d≤N} Λ(d)/d + log N)·‖ιg‖²`. -/
theorem abs_integral_windowRep_vonMangoldt_atomic_le {A : ℝ} {N : ℕ} {φ : ℝ → ℝ} {δ : ℝ}
    (hA : windowLevel A = N) (hφ : IsAtomProfile N δ φ) (hc : Continuous φ)
    (g : ArithmeticFunction ℝ) :
    |∫ u, windowRepFun A ArithmeticFunction.vonMangoldt (atomicEmbedding N φ g) u *
        atomicEmbedding N φ g u| ≤
      (∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d / d + Real.log N) / 2 *
        ∫ u, atomicEmbedding N φ g u ^ 2 := by
  have hnorm : ∫ u, atomicEmbedding N φ g u ^ 2 =
      (∫ v, φ v ^ 2) * ∑ k ∈ Finset.Icc 1 N, g k ^ 2 / k := by
    have h := integral_atomicEmbedding_mul hφ hc g g
    simp only [← sq] at h
    exact h
  rw [integral_windowRep_atomicEmbedding hA hφ hc, hnorm, abs_mul,
    abs_of_nonneg (integral_nonneg fun v => sq_nonneg _)]
  have hb := abs_sum_vonMangoldt_mul_le N g
  have hsq : 0 ≤ ∫ v, φ v ^ 2 := integral_nonneg fun v => sq_nonneg _
  calc (∫ v, φ v ^ 2) * |∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt * g) k * g k / k|
      ≤ (∫ v, φ v ^ 2) * ((∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d / d +
          Real.log N) / 2 * ∑ k ∈ Finset.Icc 1 N, g k ^ 2 / k) :=
        mul_le_mul_of_nonneg_left hb hsq
    _ = _ := by ring

end GaloisForLFunctions.WindowTowerOfSpecZ
