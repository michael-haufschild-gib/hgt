import GaloisForLFunctions.RHTower.SigmaBlockContraction

/-!
# The σ-ladder contraction

Summing the per-block σ-contraction over the geometric ladder
`Y_j = x₁·(2Q)^j`:

`∑_{x₁ < n ≤ x₁(2Q)^J} |R(n)|(1/n − 1/(n+1))
   ≤ a·(log(x₁(2Q)^J) − log x₁) − (a − ε')·(ρ/3)·J
     + a·∑_{j<J} 6/(x₁(2Q)^j)`,

a full unit of gain per block against a geometrically summable error.  The
junk-absorption hypothesis propagates up the ladder because the block base
grows by the factor `2Q ≥ 2` while `log(Q·Y)` grows only by `log(2Q)`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

set_option maxHeartbeats 1000000 in
theorem sigma_ladder_contraction {a δ ρ κ : ℝ} {Q x₀ x₁ : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hQ1 : 1 ≤ Q)
    (hQ : 40 / δ + 2 < Real.log Q)
    (hx₁1 : 1 ≤ x₁) (hx₀x₁ : x₀ ≤ x₁) (hx₁ρ : 2 / ρ ≤ (x₁ : ℝ))
    (hε'a : δ + ρ * (Real.log (1 / ρ) + 3) + κ ≤ a)
    (hratio : ∀ t : ℕ, x₀ ≤ t → |psiRemainder t| ≤ a * t)
    (hjunk1 : ∀ t : ℕ, x₁ < t →
      2 * Real.sqrt t * Real.log t ≤ κ / 2 * t)
    (hbase0 : Real.log ((Q * x₁ : ℕ) : ℝ) + 1 ≤ κ / 2 * x₁)
    (hbase : Real.log ((2 * Q : ℕ) : ℝ) ≤ κ / 2 * x₁) :
    ∀ J : ℕ,
    ∑ n ∈ Finset.Ioc x₁ (x₁ * (2 * Q) ^ J),
        |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
      ≤ a * (Real.log ((x₁ * (2 * Q) ^ J : ℕ) : ℝ) - Real.log x₁)
        - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3) * J
        + a * ∑ j ∈ Finset.range J, 6 / ((x₁ * (2 * Q) ^ j : ℕ) : ℝ) := by
  -- ladder base positivity
  have hYpos : ∀ j : ℕ, 1 ≤ x₁ * (2 * Q) ^ j := by
    intro j
    have h1 : 0 < (2 * Q) ^ j := pow_pos (by omega) j
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hx₁Y : ∀ j : ℕ, x₁ ≤ x₁ * (2 * Q) ^ j := by
    intro j
    exact Nat.le_mul_of_pos_right x₁ (pow_pos (by omega) j)
  -- junk-absorption propagates up the ladder
  have hgrow : ∀ j : ℕ,
      Real.log ((Q * (x₁ * (2 * Q) ^ j) : ℕ) : ℝ) + 1
        ≤ κ / 2 * ((x₁ * (2 * Q) ^ j : ℕ) : ℝ) := by
    intro j
    induction j with
    | zero =>
      simpa using hbase0
    | succ j ih =>
      have hYj1 : (1 : ℝ) ≤ ((x₁ * (2 * Q) ^ j : ℕ) : ℝ) := by
        exact_mod_cast hYpos j
      have heq : Q * (x₁ * (2 * Q) ^ (j + 1))
          = (Q * (x₁ * (2 * Q) ^ j)) * (2 * Q) := by
        ring
      have hA0 : Q * (x₁ * (2 * Q) ^ j) ≠ 0 := by
        have h := hYpos j
        exact Nat.mul_ne_zero (by omega) (by omega)
      have hlogsplit : Real.log ((Q * (x₁ * (2 * Q) ^ (j + 1)) : ℕ) : ℝ)
          = Real.log ((Q * (x₁ * (2 * Q) ^ j) : ℕ) : ℝ)
            + Real.log ((2 * Q : ℕ) : ℝ) := by
        rw [heq, Nat.cast_mul,
          Real.log_mul (Nat.cast_ne_zero.2 hA0) (Nat.cast_ne_zero.2 (by omega))]
      have hx₁R : (1 : ℝ) ≤ (x₁ : ℝ) := by exact_mod_cast hx₁1
      have hx₁Yj : (x₁ : ℝ) ≤ ((x₁ * (2 * Q) ^ j : ℕ) : ℝ) := by
        exact_mod_cast hx₁Y j
      have hcast2 : ((x₁ * (2 * Q) ^ (j + 1) : ℕ) : ℝ)
          = 2 * Q * ((x₁ * (2 * Q) ^ j : ℕ) : ℝ) := by
        push_cast
        ring
      have hQR : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
      rw [hlogsplit, hcast2]
      have h1 : Real.log ((2 * Q : ℕ) : ℝ) ≤ κ / 2 * x₁ := hbase
      have h2 : κ / 2 * x₁ ≤ κ / 2 * ((x₁ * (2 * Q) ^ j : ℕ) : ℝ) := by
        apply mul_le_mul_of_nonneg_left hx₁Yj (by positivity)
      have h5 : 0 ≤ κ * ((Q : ℝ) - 1) * ((x₁ * (2 * Q) ^ j : ℕ) : ℝ) :=
        mul_nonneg (mul_nonneg hκ (by linarith)) (by linarith)
      nlinarith [ih, h1, h2, h5]
  -- the ladder induction
  intro J
  induction J with
  | zero =>
    simp [sub_self]
  | succ J ih =>
    set Y : ℕ := x₁ * (2 * Q) ^ J with hY
    have hYY : x₁ * (2 * Q) ^ (J + 1) = 2 * Q * Y := by
      rw [hY]
      ring
    -- split the ladder
    have hx₁Y' : x₁ ≤ Y := hx₁Y J
    have hY2QY : Y ≤ 2 * Q * Y :=
      Nat.le_mul_of_pos_left Y (by omega)
    have hsplit : Finset.Ioc x₁ (x₁ * (2 * Q) ^ (J + 1))
        = Finset.Ioc x₁ Y ∪ Finset.Ioc Y (2 * Q * Y) := by
      rw [hYY, Finset.Ioc_union_Ioc_eq_Ioc hx₁Y' hY2QY]
    have hdisj : Disjoint (Finset.Ioc x₁ Y) (Finset.Ioc Y (2 * Q * Y)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_Ioc] at hx hx'
      omega
    rw [hsplit, Finset.sum_union hdisj]
    -- per-block junk hypothesis at base `Y`
    have hjunkY : ∀ t : ℕ, Y < t →
        Real.log ((Q * Y : ℕ) : ℝ) + 1
          + 2 * Real.sqrt t * Real.log t ≤ κ * t := by
      intro t ht
      have h1 := hgrow J
      have h2 := hjunk1 t (by omega)
      have h3 : (Y : ℝ) ≤ t := by exact_mod_cast le_of_lt ht
      have h4 : κ / 2 * (Y : ℝ) ≤ κ / 2 * t := by
        apply mul_le_mul_of_nonneg_left h3 (by positivity)
      rw [hY] at *
      linarith [h1, h2, h4]
    -- per-block contraction
    have hblock := sigma_block_contraction ha hδ hρ0 hρ1 hκ (hYpos J) hQ1 hQ
      (le_trans hx₀x₁ hx₁Y') (le_trans hx₁ρ (by exact_mod_cast hx₁Y'))
      hε'a hratio hjunkY
    -- assemble
    have hlogtel : Real.log ((2 * Q * Y : ℕ) : ℝ)
        = Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) := by
      rw [hYY]
    have hsum_succ : ∑ j ∈ Finset.range (J + 1),
        6 / ((x₁ * (2 * Q) ^ j : ℕ) : ℝ)
        = (∑ j ∈ Finset.range J, 6 / ((x₁ * (2 * Q) ^ j : ℕ) : ℝ))
          + 6 / ((Y : ℕ) : ℝ) := by
      rw [Finset.sum_range_succ, hY]
    have e1 : a * (Real.log ((Y : ℕ) : ℝ) - Real.log x₁)
        + a * (Real.log ((2 * Q * Y : ℕ) : ℝ) - Real.log Y)
        = a * (Real.log ((2 * Q * Y : ℕ) : ℝ) - Real.log x₁) := by
      ring
    have e2 : (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3) * J
        + (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
        = (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
          * ((J : ℝ) + 1) := by
      ring
    have e3 : a * ((∑ j ∈ Finset.range J,
        6 / ((x₁ * (2 * Q) ^ j : ℕ) : ℝ)) + 6 / ((Y : ℕ) : ℝ))
        = a * (∑ j ∈ Finset.range J, 6 / ((x₁ * (2 * Q) ^ j : ℕ) : ℝ))
          + a * (6 / Y) := by
      ring
    rw [show ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 from by push_cast; ring]
    calc (∑ n ∈ Finset.Ioc x₁ Y,
          |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)))
        + ∑ n ∈ Finset.Ioc Y (2 * Q * Y),
            |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        ≤ (a * (Real.log ((Y : ℕ) : ℝ) - Real.log x₁)
            - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3) * J
            + a * ∑ j ∈ Finset.range J, 6 / ((x₁ * (2 * Q) ^ j : ℕ) : ℝ))
          + (a * (Real.log ((2 * Q * Y : ℕ) : ℝ) - Real.log Y)
            - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
            + a * (6 / Y)) := by
          exact add_le_add ih hblock
      _ = a * (Real.log ((2 * Q * Y : ℕ) : ℝ) - Real.log x₁)
          - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
            * ((J : ℝ) + 1)
          + a * ((∑ j ∈ Finset.range J,
              6 / ((x₁ * (2 * Q) ^ j : ℕ) : ℝ)) + 6 / ((Y : ℕ) : ℝ)) := by
          ring
      _ = a * (Real.log ((x₁ * (2 * Q) ^ (J + 1) : ℕ) : ℝ) - Real.log x₁)
          - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
            * ((J : ℝ) + 1)
          + a * ∑ j ∈ Finset.range (J + 1),
              6 / ((x₁ * (2 * Q) ^ j : ℕ) : ℝ) := by
          rw [hlogtel, hsum_succ]

end RHTower
