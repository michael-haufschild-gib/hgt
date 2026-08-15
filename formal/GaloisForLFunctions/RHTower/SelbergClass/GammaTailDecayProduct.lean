import GaloisForLFunctions.RHTower.SelbergClass.GammaTailDecay

/-!
# Fixed-height decay for the Selberg Gamma product

This is only the finite product of the concrete Gamma-pair estimate in
`GammaTailDecay`.  It excludes the sine, conductor, phase, Dirichlet-series,
and contour components of the asymmetric functional equation.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/--
The complete finite Gamma product occurring in `asymmetricH` satisfies a
polynomial-times-exponential source-L3 bound when every actual Gamma pair
satisfies its explicit `K`-height condition.  The exponential rate is the sum
of the pair rates: `π * (∑ j, G.lambda j) * κ / 2`.
-/
theorem SelbergGammaData.exists_bound_norm_asymmetricGammaProduct_sourceL3
    (G : SelbergGammaData) (s : ℂ) {κ K : ℝ}
    (hκ : 0 < κ)
    (hheight : ∀ j : Fin G.rank,
      2 * (G.lambda j * |s.im| + |(G.mu j).im| + 1) ≤ G.lambda j * κ * K) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ v : ℝ, K ≤ v →
      ‖∏ j : Fin G.rank,
        Complex.Gamma ((G.lambda j : ℂ) * (1 - selbergSourceL3Point s κ K v) + star (G.mu j)) *
          Complex.Gamma (1 - (G.lambda j : ℂ) * selbergSourceL3Point s κ K v - G.mu j)‖
        ≤ C * v ^ N * Real.exp (-(Real.pi * (∑ j : Fin G.rank, G.lambda j) * κ * v / 2)) := by
  choose C N hC hbound using fun j =>
    G.exists_bound_norm_asymmetricGammaPair_sourceL3 j s hκ (hheight j)
  let D : Fin G.rank → ℝ := fun j => C j * (2 * G.lambda j * κ) ^ N j
  refine ⟨∏ j, D j, ∑ j, N j, Finset.prod_nonneg (fun j _ => ?_), ?_⟩
  · dsimp [D]
    have hbase : 0 ≤ 2 * G.lambda j * κ :=
      (mul_pos (mul_pos (by norm_num) (G.lambda_pos j)) hκ).le
    exact mul_nonneg (hC j) (pow_nonneg hbase _)
  intro v hv
  have hKpos (j : Fin G.rank) : 0 < K := by
    have hleft : 0 < 2 * (G.lambda j * |s.im| + |(G.mu j).im| + 1) := by
      have hterm : 0 ≤ G.lambda j * |s.im| :=
        mul_nonneg (G.lambda_pos j).le (abs_nonneg _)
      have hmu : 0 ≤ |(G.mu j).im| := abs_nonneg _
      nlinarith
    have htop : 0 < G.lambda j * κ * K := lt_of_lt_of_le hleft (hheight j)
    exact pos_of_mul_pos_right htop (mul_pos (G.lambda_pos j) hκ).le
  have hvnonneg (j : Fin G.rank) : 0 ≤ v :=
    (lt_of_lt_of_le (hKpos j) hv).le
  have hpair (j : Fin G.rank) :
      ‖Complex.Gamma ((G.lambda j : ℂ) * (1 - selbergSourceL3Point s κ K v) + star (G.mu j)) *
        Complex.Gamma (1 - (G.lambda j : ℂ) * selbergSourceL3Point s κ K v - G.mu j)‖
      ≤ D j * v ^ N j * Real.exp (-(Real.pi * G.lambda j * κ * v / 2)) := by
    calc
      ‖Complex.Gamma ((G.lambda j : ℂ) * (1 - selbergSourceL3Point s κ K v) + star (G.mu j)) *
          Complex.Gamma (1 - (G.lambda j : ℂ) * selbergSourceL3Point s κ K v - G.mu j)‖
          ≤ C j * (2 * G.lambda j * κ * v) ^ N j *
              Real.exp (-(Real.pi * G.lambda j * κ * v / 2)) := hbound j v hv
      _ = D j * v ^ N j * Real.exp (-(Real.pi * G.lambda j * κ * v / 2)) := by
        dsimp [D]
        rw [show 2 * G.lambda j * κ * v = (2 * G.lambda j * κ) * v by ring, mul_pow]
        ring
  have hprod :
      (∏ j : Fin G.rank,
        ‖Complex.Gamma ((G.lambda j : ℂ) * (1 - selbergSourceL3Point s κ K v) + star (G.mu j)) *
          Complex.Gamma (1 - (G.lambda j : ℂ) * selbergSourceL3Point s κ K v - G.mu j)‖)
      ≤ ∏ j : Fin G.rank,
        D j * v ^ N j * Real.exp (-(Real.pi * G.lambda j * κ * v / 2)) := by
    refine Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => ?_)
    exact hpair j
  have hsum :
      (∑ j : Fin G.rank, -(Real.pi * G.lambda j * κ * v / 2)) =
        -(Real.pi * (∑ j : Fin G.rank, G.lambda j) * κ * v / 2) := by
    calc
      (∑ j : Fin G.rank, -(Real.pi * G.lambda j * κ * v / 2)) =
          ∑ j : Fin G.rank, G.lambda j * (-(Real.pi * κ * v / 2)) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ j : Fin G.rank, G.lambda j) * (-(Real.pi * κ * v / 2)) := by
            rw [Finset.sum_mul]
      _ = -(Real.pi * (∑ j : Fin G.rank, G.lambda j) * κ * v / 2) := by ring
  calc
    ‖∏ j : Fin G.rank,
      Complex.Gamma ((G.lambda j : ℂ) * (1 - selbergSourceL3Point s κ K v) + star (G.mu j)) *
        Complex.Gamma (1 - (G.lambda j : ℂ) * selbergSourceL3Point s κ K v - G.mu j)‖
        = ∏ j : Fin G.rank,
          ‖Complex.Gamma ((G.lambda j : ℂ) * (1 - selbergSourceL3Point s κ K v) + star (G.mu j)) *
            Complex.Gamma (1 - (G.lambda j : ℂ) * selbergSourceL3Point s κ K v - G.mu j)‖ := norm_prod _ _
    _ ≤ ∏ j : Fin G.rank,
        D j * v ^ N j * Real.exp (-(Real.pi * G.lambda j * κ * v / 2)) := hprod
    _ = (∏ j : Fin G.rank, D j) * v ^ (∑ j : Fin G.rank, N j) *
        Real.exp (-(Real.pi * (∑ j : Fin G.rank, G.lambda j) * κ * v / 2)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        ← Real.exp_sum, hsum]

end
end RHTower
