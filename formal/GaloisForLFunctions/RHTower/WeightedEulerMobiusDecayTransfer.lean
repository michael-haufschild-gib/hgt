import GaloisForLFunctions.RHTower.PrimeLambertMobiusInversion

/-!
# Möbius decay transfer for the weighted Lambert transform

Card `weighted-euler-tangent-global-graph-decoupling`, equations (13)–(14):
Möbius inversion of the FE Lambert transform,

`G(z) = Σ_{n ≥ 1} μ(n) n H(nz)`,

converts exponential decay of `H` along a ray into the same exponential decay
of the underlying first coefficient `G`.  This file proves the discrete,
quantitative form of that transfer against the corpus inversion
(`weightedLambertMobius_inversion`): if the coefficients `a` decay
geometrically (which validates the rearrangement) and every weighted Lambert
value obeys `‖H(n)‖ ≤ D ρⁿ` with `ρ ≤ 1/2`, then

`‖a 1‖ ≤ 4 D ρ`.

Applied at `a_x(k) = F_A(kx) − e^{-kx}F_A(-kx)` with `ρ = e^{-σ'x}`, this is
exactly the card's step from the oversampled bound (8a) to the Fourier–Borel
decay (14).  Everything is unconditional.
-/

noncomputable section

namespace RHTower

open scoped BigOperators

/-- The positive-integer geometric-derivative tail is dominated by the full
natural-number series `ρ/(1-ρ)²`. -/
theorem tsum_pnat_coe_mul_geometric_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∑' n : ℕ+, ((n : ℕ) : ℝ) * ρ ^ (n : ℕ) ≤ ρ / (1 - ρ) ^ 2 := by
  have hnorm : ‖ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1
  have hnat : Summable fun m : ℕ => (m : ℝ) * ρ ^ m := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
    exact h.congr fun m => by simp [pow_one]
  have hpnat : Summable fun n : ℕ+ => ((n : ℕ) : ℝ) * ρ ^ (n : ℕ) :=
    hnat.comp_injective PNat.coe_injective
  have hle : (∑' n : ℕ+, ((n : ℕ) : ℝ) * ρ ^ (n : ℕ))
      ≤ ∑' m : ℕ, (m : ℝ) * ρ ^ m :=
    Summable.tsum_le_tsum_of_inj (fun n : ℕ+ => (n : ℕ)) PNat.coe_injective
      (fun m _ => mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hρ0 m))
      (fun n => le_rfl) hpnat hnat
  rw [tsum_coe_mul_geometric_of_norm_lt_one hnorm] at hle
  exact hle

/-- **Möbius decay transfer** (card equations (13)–(14), discrete form): a
geometrically decaying coefficient sequence whose weighted Lambert transform
is exponentially small has an exponentially small first coefficient, with the
explicit constant `4`. -/
theorem norm_first_le_of_weightedLambert_decay
    (a : ℕ+ → ℂ) {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n : ℕ+, ‖a n‖ ≤ C * r ^ (n : ℕ))
    {D ρ : ℝ} (hD : 0 ≤ D) (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (hH : ∀ n : ℕ+, ‖weightedLambertTransform a n‖ ≤ D * ρ ^ (n : ℕ)) :
    ‖a 1‖ ≤ 4 * D * ρ := by
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρhalf (by norm_num)
  have hpair := weightedLambertMobiusPair_summable_of_geometric a C r hC hr0 hr1 ha
  have hinv := weightedLambertMobius_inversion a hpair
  -- the summable majorant `n ↦ D · n ρⁿ`
  have hnorm : ‖ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1
  have hnat : Summable fun m : ℕ => (m : ℝ) * ρ ^ m := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
    exact h.congr fun m => by simp [pow_one]
  have hpnat : Summable fun n : ℕ+ => ((n : ℕ) : ℝ) * ρ ^ (n : ℕ) :=
    hnat.comp_injective PNat.coe_injective
  have hmajor : Summable fun n : ℕ+ => D * (((n : ℕ) : ℝ) * ρ ^ (n : ℕ)) :=
    hpnat.mul_left D
  -- termwise domination of the Möbius series
  have hterm : ∀ n : ℕ+,
      ‖(ArithmeticFunction.moebius (n : ℕ) : ℂ) * ((n : ℕ+) : ℂ) *
        weightedLambertTransform a n‖
      ≤ D * (((n : ℕ) : ℝ) * ρ ^ (n : ℕ)) := by
    intro n
    have hmu : ‖(ArithmeticFunction.moebius (n : ℕ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (n : ℕ))
    have hcast : ‖((n : ℕ+) : ℂ)‖ = ((n : ℕ) : ℝ) := by
      simp
    calc ‖(ArithmeticFunction.moebius (n : ℕ) : ℂ) * ((n : ℕ+) : ℂ) *
          weightedLambertTransform a n‖
        = ‖(ArithmeticFunction.moebius (n : ℕ) : ℂ)‖ * ‖((n : ℕ+) : ℂ)‖ *
            ‖weightedLambertTransform a n‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * ((n : ℕ) : ℝ) * (D * ρ ^ (n : ℕ)) := by
          rw [hcast]
          gcongr
          exact hH n
      _ = D * (((n : ℕ) : ℝ) * ρ ^ (n : ℕ)) := by ring
  have hnormsum : Summable fun n : ℕ+ =>
      ‖(ArithmeticFunction.moebius (n : ℕ) : ℂ) * ((n : ℕ+) : ℂ) *
        weightedLambertTransform a n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmajor
  -- assemble
  calc ‖a 1‖
      = ‖∑' n : ℕ+, (ArithmeticFunction.moebius (n : ℕ) : ℂ) *
          ((n : ℕ+) : ℂ) * weightedLambertTransform a n‖ := by rw [hinv]
    _ ≤ ∑' n : ℕ+, ‖(ArithmeticFunction.moebius (n : ℕ) : ℂ) *
          ((n : ℕ+) : ℂ) * weightedLambertTransform a n‖ :=
        norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ+, D * (((n : ℕ) : ℝ) * ρ ^ (n : ℕ)) :=
        hnormsum.tsum_le_tsum hterm hmajor
    _ = D * ∑' n : ℕ+, ((n : ℕ) : ℝ) * ρ ^ (n : ℕ) := tsum_mul_left
    _ ≤ D * (ρ / (1 - ρ) ^ 2) :=
        mul_le_mul_of_nonneg_left (tsum_pnat_coe_mul_geometric_le hρ0 hρ1) hD
    _ ≤ 4 * D * ρ := by
        have hquarter : (1/4 : ℝ) ≤ (1 - ρ) ^ 2 := by nlinarith
        have : ρ / (1 - ρ) ^ 2 ≤ 4 * ρ := by
          calc ρ / (1 - ρ) ^ 2 ≤ ρ / (1/4) :=
                div_le_div_of_nonneg_left hρ0 (by norm_num) hquarter
            _ = 4 * ρ := by ring
        calc D * (ρ / (1 - ρ) ^ 2) ≤ D * (4 * ρ) :=
              mul_le_mul_of_nonneg_left this hD
          _ = 4 * D * ρ := by ring

end RHTower
