import GaloisForLFunctions.RHTower.Sieve.VinogradovCoordinateCostWindow
import GaloisForLFunctions.RHTower.Sieve.VinogradovBilinearHolder

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovUsefulCoordinate (u : ℕ)
    (j : Fin (vinogradovRouteTOrder (4 * u))) : Prop :=
  200 * u ≤ j.val + 1

instance vinogradovUsefulCoordinateDecidable (u : ℕ)
    (j : Fin (vinogradovRouteTOrder (4 * u))) :
    Decidable (vinogradovUsefulCoordinate u j) := by
  unfold vinogradovUsefulCoordinate
  infer_instance

def vinogradovUsefulCoordinateEmbedding (u : ℕ) :
    Fin (200 * u) ↪
      {j : Fin (vinogradovRouteTOrder (4 * u)) //
        vinogradovUsefulCoordinate u j} where
  toFun n := ⟨⟨200 * u + n.val, by
    have hn := n.isLt
    change 200 * u + n.val < 100 * (4 * u)
    omega⟩, by
      unfold vinogradovUsefulCoordinate
      change 200 * u ≤ (200 * u + n.val) + 1
      omega⟩
  inj' := by
    intro a b h
    have hval := congrArg
      (fun j : {j : Fin (vinogradovRouteTOrder (4 * u)) //
        vinogradovUsefulCoordinate u j} => j.1.val) h
    dsimp at hval
    apply Fin.ext
    omega

theorem card_vinogradovUsefulCoordinate_ge (u : ℕ) :
    200 * u ≤ Fintype.card
      {j : Fin (vinogradovRouteTOrder (4 * u)) //
        vinogradovUsefulCoordinate u j} := by
  simpa using Fintype.card_le_of_embedding
    (vinogradovUsefulCoordinateEmbedding u)

theorem vinogradovCoordinateSavingExponent_ge
    (u : ℕ)
    (j : {j : Fin (vinogradovRouteTOrder (4 * u)) //
      vinogradovUsefulCoordinate u j}) :
    u ≤ vinogradovCoordinateSavingExponent j.1 := by
  unfold vinogradovCoordinateSavingExponent
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 200)]
  unfold vinogradovUsefulCoordinate at j
  simpa [mul_comm] using j.2

/-- Exact aggregate power reserve from the useful upper half of the
Route-T coordinates.  This is the integer invariant behind the eventual
`u^-4` Weyl saving. -/
theorem sum_vinogradovCoordinateSavingExponent_ge (u : ℕ) :
    200 * u ^ 2 ≤
      ∑ j : {j : Fin (vinogradovRouteTOrder (4 * u)) //
        vinogradovUsefulCoordinate u j},
          vinogradovCoordinateSavingExponent j.1 := by
  have hcard := card_vinogradovUsefulCoordinate_ge u
  calc
    200 * u ^ 2 = (200 * u) * u := by ring
    _ ≤ Fintype.card
        {j : Fin (vinogradovRouteTOrder (4 * u)) //
          vinogradovUsefulCoordinate u j} * u :=
      Nat.mul_le_mul_right u hcard
    _ = ∑ _j : {j : Fin (vinogradovRouteTOrder (4 * u)) //
          vinogradovUsefulCoordinate u j}, u := by simp
    _ ≤ ∑ j : {j : Fin (vinogradovRouteTOrder (4 * u)) //
          vinogradovUsefulCoordinate u j},
            vinogradovCoordinateSavingExponent j.1 :=
      Finset.sum_le_sum fun j _ => vinogradovCoordinateSavingExponent_ge u j

def vinogradovCoordinateEnvelope
    {k : ℕ} (U : Fin k → Prop) [DecidablePred U]
    (Q b : ℕ) (j : Fin k) : ℝ :=
  24 * (b : ℝ) ^ 2 * ((Q : ℝ) ^ (2 * (j.val + 1))) *
    (if U j then ((Q : ℝ) ^ vinogradovCoordinateSavingExponent j)⁻¹ else 1)

theorem vinogradovCoordinateEnvelope_nonneg
    {k : ℕ} (U : Fin k → Prop) [DecidablePred U]
    (Q b : ℕ) (j : Fin k) :
    0 ≤ vinogradovCoordinateEnvelope U Q b j := by
  unfold vinogradovCoordinateEnvelope
  split_ifs <;> positivity

theorem vinogradovMixedCoordinateCost_le_envelope
    {Q b k : ℕ} (hQ : 1 ≤ Q) (hb : 1 ≤ b)
    (U : Fin k → Prop) [DecidablePred U]
    (q : Fin k → ℕ)
    (hRq : ∀ j, U j →
      Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤ q j)
    (hqR : ∀ j, U j →
      q j * Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤
        (Q ^ (j.val + 1)) ^ 2)
    (habsorb : ∀ j, U j →
      32 * (b : ℝ) ^ 2 * (1 + Real.log ((q j : ℝ) + 1)) ≤
        (Q : ℝ) ^ vinogradovCoordinateSavingExponent j)
    (j : Fin k) :
    vinogradovMixedCoordinateCost U Q Q b q j ≤
      vinogradovCoordinateEnvelope U Q b j := by
  by_cases hj : U j
  · rw [vinogradovMixedCoordinateCost, if_pos hj]
    rw [vinogradovCoordinateEnvelope, if_pos hj]
    have hsaving := vinogradovRationalCoordinateCost_le_powerSaving
      hQ hb j (hRq j hj) (hqR j hj) (habsorb j hj)
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
    have hden : 0 < (Q : ℝ) ^ vinogradovCoordinateSavingExponent j := by
      positivity
    calc
      _ ≤ 2 * ((Q ^ (j.val + 1) : ℕ) : ℝ) ^ 2 /
          (Q : ℝ) ^ vinogradovCoordinateSavingExponent j := hsaving
      _ ≤ 24 * (b : ℝ) ^ 2 * ((Q ^ (j.val + 1) : ℕ) : ℝ) ^ 2 /
          (Q : ℝ) ^ vinogradovCoordinateSavingExponent j := by
        apply div_le_div_of_nonneg_right _ hden.le
        have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
        have hcoef : (2 : ℝ) ≤ 24 * (b : ℝ) ^ 2 := by
          nlinarith [sq_nonneg ((b : ℝ) - 1)]
        exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ = 24 * (b : ℝ) ^ 2 * ((Q : ℝ) ^ (2 * (j.val + 1))) *
          ((Q : ℝ) ^ vinogradovCoordinateSavingExponent j)⁻¹ := by
        push_cast
        rw [← pow_mul]
        ring
  · rw [vinogradovMixedCoordinateCost, if_neg hj]
    rw [vinogradovCoordinateEnvelope, if_neg hj, mul_one]
    convert vinogradovTrivialCoordinateCost_le_naturalScale hQ hb j using 1 <;>
      push_cast <;> rw [← pow_mul] <;> ring

theorem prod_vinogradovMixedCoordinateCost_le_envelope
    {Q b k : ℕ} (hQ : 1 ≤ Q) (hb : 1 ≤ b)
    (U : Fin k → Prop) [DecidablePred U]
    (q : Fin k → ℕ)
    (hRq : ∀ j, U j →
      Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤ q j)
    (hqR : ∀ j, U j →
      q j * Q ^ (2 * vinogradovCoordinateSavingExponent j) ≤
        (Q ^ (j.val + 1)) ^ 2)
    (habsorb : ∀ j, U j →
      32 * (b : ℝ) ^ 2 * (1 + Real.log ((q j : ℝ) + 1)) ≤
        (Q : ℝ) ^ vinogradovCoordinateSavingExponent j) :
    (∏ j : Fin k, vinogradovMixedCoordinateCost U Q Q b q j) ≤
      ∏ j : Fin k, vinogradovCoordinateEnvelope U Q b j := by
  apply Finset.prod_le_prod
  · intro j _
    exact vinogradovMixedCoordinateCost_nonneg U Q Q b q j
  · intro j _
    exact vinogradovMixedCoordinateCost_le_envelope
      hQ hb U q hRq hqR habsorb j

def vinogradovUsefulSavingSum
    {k : ℕ} (U : Fin k → Prop) [DecidablePred U] : ℕ :=
  ∑ j ∈ (Finset.univ : Finset (Fin k)).filter U,
    vinogradovCoordinateSavingExponent j

theorem prod_vinogradovCoordinateEnvelope_eq
    {Q b k : ℕ} (U : Fin k → Prop) [DecidablePred U] :
    (∏ j : Fin k, vinogradovCoordinateEnvelope U Q b j) =
      (24 * (b : ℝ) ^ 2) ^ k *
        (Q : ℝ) ^ (∑ j : Fin k, 2 * (j.val + 1)) *
          ((Q : ℝ) ^ vinogradovUsefulSavingSum U)⁻¹ := by
  unfold vinogradovCoordinateEnvelope
  rw [show (∏ j : Fin k,
      24 * (b : ℝ) ^ 2 * (Q : ℝ) ^ (2 * (j.val + 1)) *
        (if U j then ((Q : ℝ) ^ vinogradovCoordinateSavingExponent j)⁻¹ else 1)) =
      (∏ _j : Fin k, 24 * (b : ℝ) ^ 2) *
        (∏ j : Fin k, (Q : ℝ) ^ (2 * (j.val + 1))) *
        ∏ j : Fin k,
          (if U j then ((Q : ℝ) ^ vinogradovCoordinateSavingExponent j)⁻¹ else 1) by
    simp_rw [Finset.prod_mul_distrib]]
  rw [Finset.prod_const, Finset.card_univ]
  rw [Finset.prod_pow_eq_pow_sum]
  have hinv :
      (∏ j : Fin k,
        if U j then ((Q : ℝ) ^ vinogradovCoordinateSavingExponent j)⁻¹ else 1) =
        ((Q : ℝ) ^ vinogradovUsefulSavingSum U)⁻¹ := by
    rw [← Finset.prod_filter]
    rw [Finset.prod_inv_distrib]
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hinv]
  simp only [Fintype.card_fin]

theorem sum_two_mul_fin_succ (k : ℕ) :
    (∑ j : Fin k, 2 * (j.val + 1)) = k * (k + 1) := by
  change (∑ j : Fin k, (fun i : ℕ => 2 * (i + 1)) j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => 2 * (i + 1)) k]
  calc
    (∑ i ∈ Finset.range k, 2 * (i + 1)) =
        2 * ((∑ i ∈ Finset.range k, i) + k) := by
      calc
        _ = 2 * (∑ i ∈ Finset.range k, i + 1) := by
          rw [Finset.mul_sum]
        _ = 2 * ((∑ i ∈ Finset.range k, i) +
            ∑ _i ∈ Finset.range k, 1) := by
          rw [Finset.sum_add_distrib]
        _ = 2 * ((∑ i ∈ Finset.range k, i) + k) := by simp
    _ = 2 * (k * (k - 1) / 2 + k) := by rw [Finset.sum_range_id]
    _ = k * (k + 1) := by
      have heven : 2 ∣ k * (k - 1) := by
        rcases Nat.even_or_odd k with hk | hk
        · exact hk.two_dvd.mul_right (k - 1)
        · have hk1 : Even (k - 1) := by
            obtain ⟨m, hm⟩ := hk
            use m
            omega
          exact hk1.two_dvd.mul_left k
      rw [Nat.mul_div_cancel' heven]
      ring

theorem vinogradovUsefulSavingSum_eq_subtype_sum
    {k : ℕ} (U : Fin k → Prop) [DecidablePred U] :
    vinogradovUsefulSavingSum U =
      ∑ j : {j : Fin k // U j}, vinogradovCoordinateSavingExponent j.1 := by
  unfold vinogradovUsefulSavingSum
  exact Finset.sum_subtype
    ((Finset.univ : Finset (Fin k)).filter U)
    (by intro j; simp) (fun j => vinogradovCoordinateSavingExponent j)

theorem vinogradovUsefulSavingSum_ge (u : ℕ) :
    200 * u ^ 2 ≤
      vinogradovUsefulSavingSum (vinogradovUsefulCoordinate u) := by
  rw [vinogradovUsefulSavingSum_eq_subtype_sum]
  exact sum_vinogradovCoordinateSavingExponent_ge u

end

end RHTower.Sieve
