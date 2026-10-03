import GaloisForLFunctions.RHTower.Sieve.VinogradovMeanValueExplicit
import GaloisForLFunctions.RHTower.Sieve.VinogradovUpperHalfSaving

/-!
# Bilinear Weyl sums with the explicit mean value theorem

For the upper-half bilinear sum `B(α) = Σ_{Q ≤ l, m < 2Q} e(Σ_{j<k} α_j (lm)^{j+1})`, Hölder and the
mean value theorem (`norm_vinogradovEmbeddedBilinearSum_pow_le_mixedProduct`) give

`‖B‖^{4b²} ≤ P^{8b²-4b} · J_b(P)² · Π_j cost_j`,   `P = 2Q`.

Here every coordinate in a set `U` carries a rational approximation `a_j/q_j` with
`P^{2e_j} ≤ q_j ≤ P^{2(j+1) - 2e_j}` and saves `P^{e_j}` against its natural cost `24b²P^{2(j+1)}`
(`vinogradovRationalCoordinateCost_le_saving`, any `e_j` with `2e_j ≤ j+1`).  With
`card_vinogradovDiagonalSolution_le_explicit` the result is

`‖B‖^{4b²} ≤ C_{k,b}² (24b²)^k P^{8b² + 2Kθ^{b/k}} / P^{Σ_U e_j}`,   `K = k(k+1)/2`, `θ = 1 - 1/k`

(`norm_vinogradovUpperHalfBilinearSum_pow_le_explicit`): the saving `Σ_U e_j` competes only with the
mean value defect `2Kθ^{b/k}`.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- One useful coordinate with denominator window `[P^{2e}, P^{2(j+1)-2e}]` saves `P^e`. -/
theorem vinogradovRationalCoordinateCost_le_saving
    {Q b q k e : ℕ} (hQ : 1 ≤ Q) (hb : 1 ≤ b) (j : Fin k) (he : 2 * e ≤ j.val + 1)
    (hRq : Q ^ (2 * e) ≤ q) (hqR : q * Q ^ (2 * e) ≤ (Q ^ (j.val + 1)) ^ (2 : ℕ))
    (habsorb : 32 * (b : ℝ) ^ (2 : ℕ) * (1 + Real.log ((q : ℝ) + 1)) ≤ (Q : ℝ) ^ e) :
    vinogradovRationalCoordinateCost Q Q b q j ≤
      2 * ((Q ^ (j.val + 1) : ℕ) : ℝ) ^ (2 : ℕ) / (Q : ℝ) ^ e := by
  set P : ℕ := Q ^ (j.val + 1) with hPdef
  set R : ℕ := Q ^ (2 * e) with hRdef
  have hR : 0 < R := pow_pos (by omega) _
  have hwindow := vinogradovRationalCoordinateCost_le_window hQ hb hR hRq j hqR
  have hRP : R ≤ P := Nat.pow_le_pow_right (by omega) he
  have hPR : (0 : ℝ) < R := by exact_mod_cast hR
  have hPle : (P : ℝ) ≤ (P : ℝ) ^ (2 : ℕ) / (R : ℝ) := by
    rw [le_div_iff₀ hPR]
    have hRPR : (R : ℝ) ≤ P := by exact_mod_cast hRP
    have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
    nlinarith
  have hbracket : (P : ℝ) ^ (2 : ℕ) / (R : ℝ) + (P : ℝ) ≤
      2 * ((P : ℝ) ^ (2 : ℕ) / (R : ℝ)) := by linarith
  have hscale :
      32 * (b : ℝ) ^ (2 : ℕ) * (1 + Real.log ((q : ℝ) + 1)) *
          ((P : ℝ) ^ (2 : ℕ) / (R : ℝ) + (P : ℝ)) ≤
        ((Q : ℝ) ^ e) * (2 * ((P : ℝ) ^ (2 : ℕ) / (R : ℝ))) :=
    mul_le_mul habsorb hbracket (by positivity) (by positivity)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  calc vinogradovRationalCoordinateCost Q Q b q j
      ≤ 32 * (b : ℝ) ^ (2 : ℕ) * (1 + Real.log ((q : ℝ) + 1)) *
          ((P : ℝ) ^ (2 : ℕ) / (R : ℝ) + (P : ℝ)) := hwindow
    _ ≤ ((Q : ℝ) ^ e) * (2 * ((P : ℝ) ^ (2 : ℕ) / (R : ℝ))) := hscale
    _ = 2 * ((P : ℝ) ^ (2 : ℕ)) / ((Q : ℝ) ^ e) := by
      rw [hRdef]
      push_cast
      rw [pow_mul]
      field_simp
      ring

/-- The envelope `24b²P^{2(j+1)}`, divided by `P^{e_j}` on useful coordinates. -/
def vinogradovSavingEnvelope {k : ℕ} (U : Fin k → Prop) [DecidablePred U] (e : Fin k → ℕ)
    (Q b : ℕ) (j : Fin k) : ℝ :=
  24 * (b : ℝ) ^ (2 : ℕ) * ((Q : ℝ) ^ (2 * (j.val + 1))) *
    (if U j then ((Q : ℝ) ^ e j)⁻¹ else 1)

theorem vinogradovMixedCoordinateCost_le_savingEnvelope
    {Q b k : ℕ} (hQ : 1 ≤ Q) (hb : 1 ≤ b) (U : Fin k → Prop) [DecidablePred U]
    (q e : Fin k → ℕ) (he : ∀ j, U j → 2 * e j ≤ j.val + 1)
    (hRq : ∀ j, U j → Q ^ (2 * e j) ≤ q j)
    (hqR : ∀ j, U j → q j * Q ^ (2 * e j) ≤ (Q ^ (j.val + 1)) ^ (2 : ℕ))
    (habsorb : ∀ j, U j →
      32 * (b : ℝ) ^ (2 : ℕ) * (1 + Real.log ((q j : ℝ) + 1)) ≤ (Q : ℝ) ^ e j)
    (j : Fin k) :
    vinogradovMixedCoordinateCost U Q Q b q j ≤ vinogradovSavingEnvelope U e Q b j := by
  by_cases hj : U j
  · rw [vinogradovMixedCoordinateCost, if_pos hj, vinogradovSavingEnvelope, if_pos hj]
    have hsaving := vinogradovRationalCoordinateCost_le_saving hQ hb j (he j hj) (hRq j hj)
      (hqR j hj) (habsorb j hj)
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
    have hden : 0 < (Q : ℝ) ^ e j := by positivity
    calc _ ≤ 2 * ((Q ^ (j.val + 1) : ℕ) : ℝ) ^ (2 : ℕ) / (Q : ℝ) ^ e j := hsaving
      _ ≤ 24 * (b : ℝ) ^ (2 : ℕ) * ((Q ^ (j.val + 1) : ℕ) : ℝ) ^ (2 : ℕ) / (Q : ℝ) ^ e j := by
        apply div_le_div_of_nonneg_right _ hden.le
        have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
        have hcoef : (2 : ℝ) ≤ 24 * (b : ℝ) ^ (2 : ℕ) := by nlinarith
        exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ = 24 * (b : ℝ) ^ (2 : ℕ) * ((Q : ℝ) ^ (2 * (j.val + 1))) * ((Q : ℝ) ^ e j)⁻¹ := by
        push_cast
        rw [← pow_mul]
        ring
  · rw [vinogradovMixedCoordinateCost, if_neg hj, vinogradovSavingEnvelope, if_neg hj, mul_one]
    convert vinogradovTrivialCoordinateCost_le_naturalScale hQ hb j using 1
    push_cast
    rw [← pow_mul]
    ring

theorem prod_vinogradovSavingEnvelope {Q b k : ℕ} (hQ : 1 ≤ Q) (U : Fin k → Prop)
    [DecidablePred U] (e : Fin k → ℕ) :
    ∏ j : Fin k, vinogradovSavingEnvelope U e Q b j =
      (24 * (b : ℝ) ^ (2 : ℕ)) ^ k * (Q : ℝ) ^ (k * (k + 1)) *
        ((Q : ℝ) ^ (∑ j ∈ (Finset.univ : Finset (Fin k)).filter U, e j))⁻¹ := by
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  unfold vinogradovSavingEnvelope
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have hpow : ∏ j : Fin k, (Q : ℝ) ^ (2 * (j.val + 1)) = (Q : ℝ) ^ (k * (k + 1)) := by
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    have := sum_two_mul_fin_succ k
    simpa using this
  have hif : ∏ j : Fin k, (if U j then ((Q : ℝ) ^ e j)⁻¹ else 1) =
      ((Q : ℝ) ^ (∑ j ∈ (Finset.univ : Finset (Fin k)).filter U, e j))⁻¹ := by
    rw [← Finset.prod_filter, ← Finset.prod_pow_eq_pow_sum, Finset.prod_inv_distrib]
  rw [hpow, hif]

/-- **Bilinear Weyl sums with the explicit mean value theorem.** -/
theorem norm_vinogradovUpperHalfBilinearSum_pow_le_explicit
    {k b Q : ℕ} (hk : 3 ≤ k) (hb : 1 ≤ b) (hQ : 1 ≤ Q)
    (α : Fin k → ℝ) (U : Fin k → Prop) [DecidablePred U] (a q e : Fin k → ℕ)
    (hq : ∀ j, U j → 0 < q j) (hcop : ∀ j, U j → Nat.Coprime (a j) (q j))
    (happrox : ∀ j, U j → |α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ (2 : ℕ))
    (he : ∀ j, U j → 2 * e j ≤ j.val + 1)
    (hRq : ∀ j, U j → (2 * Q) ^ (2 * e j) ≤ q j)
    (hqR : ∀ j, U j → q j * (2 * Q) ^ (2 * e j) ≤ ((2 * Q) ^ (j.val + 1)) ^ (2 : ℕ))
    (habsorb : ∀ j, U j →
      32 * (b : ℝ) ^ (2 : ℕ) * (1 + Real.log ((q j : ℝ) + 1)) ≤ ((2 * Q : ℕ) : ℝ) ^ e j) :
    ‖vinogradovUpperHalfBilinearSum Q α‖ ^ (4 * b ^ 2) ≤
      vinogradovExplicitConstant k b ^ 2 * (24 * (b : ℝ) ^ 2) ^ k *
        ((2 * Q : ℕ) : ℝ) ^ (8 * (b : ℝ) ^ 2 +
          2 * ((k * (k + 1) / 2 : ℝ) * (1 - 1 / (k : ℝ)) ^ ((b : ℝ) / k))) *
        (((2 * Q : ℕ) : ℝ) ^ (∑ j ∈ (Finset.univ : Finset (Fin k)).filter U, e j))⁻¹ := by
  set P : ℕ := 2 * Q with hPdef
  have hP1 : 1 ≤ P := by omega
  have hP0 : P ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP1
  have hPpos : (0 : ℝ) < P := by linarith
  have hbase := norm_vinogradovEmbeddedBilinearSum_pow_le_mixedProduct
    hb0 hP0 hP0 (vinogradovUpperHalfEmbedding Q) (vinogradovUpperHalfEmbedding Q) α U a q hq hcop
    happrox
  have hcard : (Fintype.card ((Fin b → Fin Q) × (Fin b → Fin Q)) : ℝ) = (Q : ℝ) ^ (2 * b) := by
    norm_cast
    exact card_vinogradovTuplePair Q b
  rw [hcard] at hbase
  set C := vinogradovExplicitConstant k b with hC
  set lb := vinogradovDecayExponent k b with hlb
  have hJ := card_vinogradovDiagonalSolution_le_explicit hk b P hP0
  rw [← hC, ← hlb] at hJ
  have hC0 : 0 ≤ C := (vinogradovExplicitConstant_pos k b).le
  have hJJ : (Fintype.card (VinogradovDiagonalSolution P b k) : ℝ) *
      Fintype.card (VinogradovDiagonalSolution P b k) ≤ (C * (P : ℝ) ^ lb) * (C * (P : ℝ) ^ lb) :=
    mul_le_mul hJ hJ (Nat.cast_nonneg _) (by positivity)
  have hcost := Finset.prod_le_prod
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) =>
      vinogradovMixedCoordinateCost_nonneg U P P b q j)
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) =>
      vinogradovMixedCoordinateCost_le_savingEnvelope hP1 hb U q e he hRq hqR habsorb j)
  rw [prod_vinogradovSavingEnvelope hP1 U e] at hcost
  have hQP : (Q : ℝ) ≤ P := by rw [hPdef]; push_cast; linarith [(Nat.cast_nonneg Q : (0 : ℝ) ≤ Q)]
  have houter : ((Q : ℝ) ^ (2 * b - 1)) ^ (2 * b) * ((Q : ℝ) ^ (2 * b)) ^ (2 * b - 1) ≤
      ((P : ℝ) ^ (2 * b - 1)) ^ (2 * b) * ((P : ℝ) ^ (2 * b)) ^ (2 * b - 1) := by
    have h1 : (Q : ℝ) ^ (2 * b - 1) ≤ (P : ℝ) ^ (2 * b - 1) :=
      pow_le_pow_left₀ (by positivity) hQP _
    have h2 : (Q : ℝ) ^ (2 * b) ≤ (P : ℝ) ^ (2 * b) := pow_le_pow_left₀ (by positivity) hQP _
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) h1 _) (pow_le_pow_left₀ (by positivity) h2 _)
      (by positivity) (by positivity)
  have hcost0 : 0 ≤ ∏ j : Fin k, vinogradovMixedCoordinateCost U P P b q j :=
    Finset.prod_nonneg fun j _ => vinogradovMixedCoordinateCost_nonneg U P P b q j
  set S := ∑ j ∈ (Finset.univ : Finset (Fin k)).filter U, e j with hS
  -- the exponent
  have hexp : ((8 * b ^ 2 - 4 * b : ℕ) : ℝ) + 2 * lb + ((k * (k + 1) : ℕ) : ℝ) =
      8 * (b : ℝ) ^ 2 + 2 * ((k * (k + 1) / 2 : ℝ) * (1 - 1 / (k : ℝ)) ^ ((b : ℝ) / k)) := by
    rw [hlb]
    unfold vinogradovDecayExponent
    have h4 : 4 * b ≤ 8 * b ^ 2 := by nlinarith
    rw [Nat.cast_sub h4]
    push_cast
    ring
  have houterP : ((P : ℝ) ^ (2 * b - 1)) ^ (2 * b) * ((P : ℝ) ^ (2 * b)) ^ (2 * b - 1) =
      (P : ℝ) ^ (8 * b ^ 2 - 4 * b) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    have e1 : 2 * (c + 1) - 1 = 2 * c + 1 := by omega
    have e2 : 8 * (c + 1) ^ 2 - 4 * (c + 1) =
        (2 * c + 1) * (2 * (c + 1)) + 2 * (c + 1) * (2 * c + 1) := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [e1, e2]
  calc ‖vinogradovUpperHalfBilinearSum Q α‖ ^ (4 * b ^ 2)
      ≤ (((Q : ℝ) ^ (2 * b - 1)) ^ (2 * b) * ((Q : ℝ) ^ (2 * b)) ^ (2 * b - 1)) *
          ((Fintype.card (VinogradovDiagonalSolution P b k) : ℝ) *
            Fintype.card (VinogradovDiagonalSolution P b k)) *
          ∏ j : Fin k, vinogradovMixedCoordinateCost U P P b q j := by
        simpa [vinogradovUpperHalfBilinearSum, P] using hbase
    _ ≤ (((P : ℝ) ^ (2 * b - 1)) ^ (2 * b) * ((P : ℝ) ^ (2 * b)) ^ (2 * b - 1)) *
          ((C * (P : ℝ) ^ lb) * (C * (P : ℝ) ^ lb)) *
          ((24 * (b : ℝ) ^ (2 : ℕ)) ^ k * (P : ℝ) ^ (k * (k + 1)) * ((P : ℝ) ^ S)⁻¹) := by
        apply mul_le_mul (mul_le_mul houter hJJ (by positivity) (by positivity)) hcost hcost0
        positivity
    _ = C ^ 2 * (24 * (b : ℝ) ^ 2) ^ k *
          ((P : ℝ) ^ (8 * b ^ 2 - 4 * b) * ((P : ℝ) ^ lb * (P : ℝ) ^ lb) *
            (P : ℝ) ^ (k * (k + 1))) * ((P : ℝ) ^ S)⁻¹ := by
        rw [houterP]; ring
    _ = C ^ 2 * (24 * (b : ℝ) ^ 2) ^ k *
          (P : ℝ) ^ (8 * (b : ℝ) ^ 2 +
            2 * ((k * (k + 1) / 2 : ℝ) * (1 - 1 / (k : ℝ)) ^ ((b : ℝ) / k))) *
          ((P : ℝ) ^ S)⁻¹ := by
        congr 2
        rw [← hexp, Real.rpow_add hPpos, Real.rpow_add hPpos, Real.rpow_natCast,
          Real.rpow_natCast, two_mul, Real.rpow_add hPpos]

end

end RHTower.Sieve
