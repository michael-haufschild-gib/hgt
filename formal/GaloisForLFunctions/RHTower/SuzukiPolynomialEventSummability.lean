import GaloisForLFunctions.RHTower.SuzukiOrbitWeightSummability
import GaloisForLFunctions.RHTower.SuzukiOnePrimeFractionalCarrier

/-!
# `(8)`: polynomial event summability on the valuation lattice

A polynomial weight of degree `κ` is square summable against an event clock of logarithmic type `Q`
exactly when `2κ` exceeds `d + 2σQ`.  The lattice side of that statement needs no shell counting:
each coordinate factor `1+|νᵢ|` is at most `1+|ν|₁`, so the whole product is at most `(1+|ν|₁)^d`
and the weight is dominated by the `d`-fold product of a one-dimensional summable weight.
-/

open Filter Set
open scoped ENNReal

noncomputable section

namespace RHTower

/-- The rank product formula for an arbitrary coordinate weight. -/
theorem tsum_prod_coord_fin (g : ℤ → ℝ≥0∞) (n : ℕ) :
    (∑' ν : Fin n → ℤ, ∏ i, g (ν i)) = (∑' m : ℤ, g m) ^ n := by
  induction n with
  | zero =>
      haveI : Subsingleton (Fin 0 → ℤ) := ⟨fun f g => funext fun i => i.elim0⟩
      haveI : Unique (Fin 0 → ℤ) := uniqueOfSubsingleton (0 : Fin 0 → ℤ)
      rw [tsum_eq_single default (fun b hb => absurd (Subsingleton.elim b default) hb), pow_zero]
      simp
  | succ k ih =>
      have hre : (∑' ν : Fin (k + 1) → ℤ, ∏ i, g (ν i))
          = ∑' q : ℤ × (Fin k → ℤ), ∏ i, g ((consValuationEquiv k q : Fin (k + 1) → ℤ) i) :=
        ((consValuationEquiv k).tsum_eq (fun ν : Fin (k + 1) → ℤ => ∏ i, g (ν i))).symm
      have hterm : (∑' q : ℤ × (Fin k → ℤ),
            ∏ i, g ((consValuationEquiv k q : Fin (k + 1) → ℤ) i))
          = ∑' q : ℤ × (Fin k → ℤ), g q.1 * ∏ i, g (q.2 i) := by
        refine tsum_congr fun q => ?_
        rw [Fin.prod_univ_succ, consValuationEquiv_apply]
        simp only [Fin.cons_zero, Fin.cons_succ]
      have hsplit : (∑' q : ℤ × (Fin k → ℤ), g q.1 * ∏ i, g (q.2 i))
          = ∑' (a : ℤ) (v : Fin k → ℤ), g a * ∏ i, g (v i) := ENNReal.tsum_prod'
      have hinner : ∀ a : ℤ, (∑' v : Fin k → ℤ, g a * ∏ i, g (v i))
          = g a * ∑' v : Fin k → ℤ, ∏ i, g (v i) := fun a => ENNReal.tsum_mul_left
      rw [hre, hterm, hsplit, tsum_congr hinner, ENNReal.tsum_mul_right, ih, pow_succ]
      ring

/-- One-dimensional polynomial summability. -/
theorem summable_int_one_add_abs_rpow {γ : ℝ} (hγ : 1 < γ) :
    Summable fun n : ℤ => (1 + |(n : ℝ)|) ^ (-γ) := by
  have hnat : Summable fun n : ℕ => (1 + (n : ℝ)) ^ (-γ) := by
    have hbase : Summable fun n : ℕ => ((n : ℝ)) ^ (-γ) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hshift : Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-γ) :=
      (summable_nat_add_iff 1).mpr hbase
    refine hshift.congr fun n => ?_
    push_cast
    ring_nf
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hnat.congr fun n => ?_
    rw [Int.cast_natCast, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  · refine hnat.congr fun n => ?_
    rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]

/-- The one-dimensional mass is finite in `ℝ≥0∞`. -/
theorem tsum_ofReal_int_one_add_abs_rpow_ne_top {γ : ℝ} (hγ : 1 < γ) :
    (∑' n : ℤ, ENNReal.ofReal ((1 + |(n : ℝ)|) ^ (-γ))) ≠ ⊤ := by
  have h := summable_int_one_add_abs_rpow hγ
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) h]
  exact ENNReal.ofReal_ne_top

/-- Every coordinate factor is dominated by the `ℓ¹` length. -/
theorem prod_one_add_abs_le {d : ℕ} (ν : Fin d → ℤ) :
    (∏ i, (1 + |((ν i : ℤ) : ℝ)|)) ≤ (1 + (orbitLength ν : ℝ)) ^ d := by
  have hle : ∀ i : Fin d, (1 + |((ν i : ℤ) : ℝ)|) ≤ 1 + (orbitLength ν : ℝ) := by
    intro i
    have hmem : (ν i).natAbs ≤ orbitLength ν := by
      rw [orbitLength]
      exact Finset.single_le_sum (f := fun p => (ν p).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have habs : |((ν i : ℤ) : ℝ)| = ((ν i).natAbs : ℝ) := by
      simp [Int.cast_abs]
    rw [habs]
    have : ((ν i).natAbs : ℝ) ≤ (orbitLength ν : ℝ) := by exact_mod_cast hmem
    linarith
  calc (∏ i, (1 + |((ν i : ℤ) : ℝ)|))
      ≤ ∏ _i : Fin d, (1 + (orbitLength ν : ℝ)) := by
        refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hle i)
    _ = (1 + (orbitLength ν : ℝ)) ^ d := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The lattice weight is summable exactly past the rank.** -/
theorem summable_orbitLength_rpow_neg {d : ℕ} {β : ℝ} (hβ : (d : ℝ) < β) :
    Summable fun ν : Fin d → ℤ => (1 + (orbitLength ν : ℝ)) ^ (-β) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    haveI : Subsingleton (Fin 0 → ℤ) := ⟨fun f g => funext fun i => i.elim0⟩
    haveI : Finite (Fin 0 → ℤ) := Finite.of_subsingleton
    exact summable_of_hasFiniteSupport (Set.toFinite _)
  · have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    set γ : ℝ := β / d with hγdef
    have hγ : 1 < γ := by
      rw [hγdef, lt_div_iff₀ hd0]
      linarith
    have hγ0 : 0 < γ := lt_trans zero_lt_one hγ
    -- pointwise domination by the coordinate product
    have hdom : ∀ ν : Fin d → ℤ,
        (1 + (orbitLength ν : ℝ)) ^ (-β) ≤ ∏ i, (1 + |((ν i : ℤ) : ℝ)|) ^ (-γ) := by
      intro ν
      have hpos : (0 : ℝ) < 1 + (orbitLength ν : ℝ) := by positivity
      have hprodpos : (0 : ℝ) < ∏ i, (1 + |((ν i : ℤ) : ℝ)|) := by
        refine Finset.prod_pos fun i _ => by positivity
      have hprod : (∏ i, (1 + |((ν i : ℤ) : ℝ)|)) ≤ (1 + (orbitLength ν : ℝ)) ^ d :=
        prod_one_add_abs_le ν
      have hsplit : (∏ i, (1 + |((ν i : ℤ) : ℝ)|) ^ (-γ))
          = (∏ i, (1 + |((ν i : ℤ) : ℝ)|)) ^ (-γ) := by
        rw [← Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
      rw [hsplit]
      have hanti : ((1 + (orbitLength ν : ℝ)) ^ d) ^ (-γ)
          ≤ (∏ i, (1 + |((ν i : ℤ) : ℝ)|)) ^ (-γ) :=
        Real.rpow_le_rpow_of_nonpos hprodpos hprod (by linarith)
      refine le_trans (le_of_eq ?_) hanti
      rw [← Real.rpow_natCast (1 + (orbitLength ν : ℝ)) d, ← Real.rpow_mul hpos.le]
      congr 1
      rw [hγdef]
      field_simp
    -- the product is summable in `ℝ≥0∞`
    have hmass : (∑' ν : Fin d → ℤ,
        ENNReal.ofReal (∏ i, (1 + |((ν i : ℤ) : ℝ)|) ^ (-γ))) ≠ ⊤ := by
      have hcongr : ∀ ν : Fin d → ℤ,
          ENNReal.ofReal (∏ i, (1 + |((ν i : ℤ) : ℝ)|) ^ (-γ))
            = ∏ i, ENNReal.ofReal ((1 + |((ν i : ℤ) : ℝ)|) ^ (-γ)) := by
        intro ν
        rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
      rw [tsum_congr hcongr,
        tsum_prod_coord_fin (fun m : ℤ => ENNReal.ofReal ((1 + |((m : ℤ) : ℝ)|) ^ (-γ))) d]
      exact ENNReal.pow_ne_top (tsum_ofReal_int_one_add_abs_rpow_ne_top hγ)
    have hsummable : Summable fun ν : Fin d → ℤ => ∏ i, (1 + |((ν i : ℤ) : ℝ)|) ^ (-γ) := by
      have h := ENNReal.summable_toReal hmass
      refine h.congr fun ν => ?_
      rw [ENNReal.toReal_ofReal (by positivity)]
    exact Summable.of_nonneg_of_le (fun ν => by positivity) hdom hsummable

/-- The squared fractional weight is the lattice power `(1+|ν|₁)^{-2κ}`. -/
theorem fractionalPolynomialOrbitWeight_sq {d : ℕ} (κ : ℝ) (ν : Fin d → ℤ) :
    fractionalPolynomialOrbitWeight κ ν ^ 2 = (1 + (orbitLength ν : ℝ)) ^ (-(2 * κ)) := by
  have hpos : (0 : ℝ) < 1 + (orbitLength ν : ℝ) := by positivity
  rw [fractionalPolynomialOrbitWeight, inv_pow, ← Real.rpow_natCast
    ((1 + (orbitLength ν : ℝ)) ^ κ) 2, ← Real.rpow_mul hpos.le, ← Real.rpow_neg hpos.le]
  congr 1
  push_cast
  ring

/-- **`(8)` (first half): the polynomial weight is square summable past the rank.** -/
theorem summable_fractionalPolynomialOrbitWeight_sq {d : ℕ} {κ : ℝ} (hκ : (d : ℝ) < 2 * κ) :
    Summable fun ν : Fin d → ℤ => fractionalPolynomialOrbitWeight κ ν ^ 2 := by
  refine (summable_orbitLength_rpow_neg (β := 2 * κ) hκ).congr fun ν => ?_
  exact (fractionalPolynomialOrbitWeight_sq κ ν).symm

/-- `(3)`: an event clock has finite logarithmic type when it is eventually dominated by a fixed
multiple of the logarithmic shell index. -/
def HasFiniteLogType {d : ℕ} (τ : (Fin d → ℤ) → ℝ) : Prop :=
  ∃ Q : ℝ, 0 ≤ Q ∧ ∀ᶠ ν in Filter.cofinite, τ ν ≤ Q * Real.log (2 + (orbitLength ν : ℝ))

set_option maxHeartbeats 1000000 in
/-- **`(8)`, `(12)`, `(13)`: polynomial event summability.**  A clock of logarithmic type `Q` is
absorbed by every polynomial weight whose doubled degree exceeds `d + 2σQ`. -/
theorem summable_fractionalWeight_sq_mul_exp {d : ℕ} {κ σ Q : ℝ}
    {τ : (Fin d → ℤ) → ℝ} (hσ : 0 ≤ σ) (hQ : 0 ≤ Q)
    (hτ : ∀ᶠ ν in Filter.cofinite, τ ν ≤ Q * Real.log (2 + (orbitLength ν : ℝ)))
    (hκ : (d : ℝ) + 2 * σ * Q < 2 * κ) :
    Summable fun ν : Fin d → ℤ =>
      fractionalPolynomialOrbitWeight κ ν ^ 2 * Real.exp (2 * σ * τ ν) := by
  have hβ : (d : ℝ) < 2 * κ - 2 * σ * Q := by linarith
  have hmaj : Summable fun ν : Fin d → ℤ =>
      (2 : ℝ) ^ (2 * σ * Q) * (1 + (orbitLength ν : ℝ)) ^ (-(2 * κ - 2 * σ * Q)) :=
    (summable_orbitLength_rpow_neg hβ).mul_left _
  refine Summable.of_norm_bounded_eventually hmaj ?_
  filter_upwards [hτ] with ν hν
  have hL : (0 : ℝ) ≤ (orbitLength ν : ℝ) := by positivity
  have hpos : (0 : ℝ) < 1 + (orbitLength ν : ℝ) := by linarith
  have hpos2 : (0 : ℝ) < 2 + (orbitLength ν : ℝ) := by linarith
  have hnn : (0 : ℝ) ≤ fractionalPolynomialOrbitWeight κ ν ^ 2 * Real.exp (2 * σ * τ ν) := by
    have := fractionalPolynomialOrbitWeight_pos κ ν
    positivity
  rw [Real.norm_of_nonneg hnn, fractionalPolynomialOrbitWeight_sq]
  -- the clock factor
  have hexp : Real.exp (2 * σ * τ ν) ≤ (2 + (orbitLength ν : ℝ)) ^ (2 * σ * Q) := by
    have hstep : 2 * σ * τ ν ≤ 2 * σ * Q * Real.log (2 + (orbitLength ν : ℝ)) := by
      have h2σ : (0 : ℝ) ≤ 2 * σ := by linarith
      nlinarith [hν, h2σ]
    calc Real.exp (2 * σ * τ ν) ≤ Real.exp (2 * σ * Q * Real.log (2 + (orbitLength ν : ℝ))) :=
          Real.exp_le_exp.mpr hstep
      _ = (2 + (orbitLength ν : ℝ)) ^ (2 * σ * Q) := by
          rw [Real.rpow_def_of_pos hpos2]
          congr 1
          ring
  have hshift : (2 + (orbitLength ν : ℝ)) ^ (2 * σ * Q)
      ≤ (2 : ℝ) ^ (2 * σ * Q) * (1 + (orbitLength ν : ℝ)) ^ (2 * σ * Q) := by
    have hle : (2 : ℝ) + (orbitLength ν : ℝ) ≤ 2 * (1 + (orbitLength ν : ℝ)) := by linarith
    calc (2 + (orbitLength ν : ℝ)) ^ (2 * σ * Q)
        ≤ (2 * (1 + (orbitLength ν : ℝ))) ^ (2 * σ * Q) :=
          Real.rpow_le_rpow (by linarith) hle (by positivity)
      _ = (2 : ℝ) ^ (2 * σ * Q) * (1 + (orbitLength ν : ℝ)) ^ (2 * σ * Q) :=
          Real.mul_rpow (by norm_num) hpos.le
  have hcomb : (1 + (orbitLength ν : ℝ)) ^ (-(2 * κ)) * (1 + (orbitLength ν : ℝ)) ^ (2 * σ * Q)
      = (1 + (orbitLength ν : ℝ)) ^ (-(2 * κ - 2 * σ * Q)) := by
    rw [← Real.rpow_add hpos]
    congr 1
    ring
  calc (1 + (orbitLength ν : ℝ)) ^ (-(2 * κ)) * Real.exp (2 * σ * τ ν)
      ≤ (1 + (orbitLength ν : ℝ)) ^ (-(2 * κ))
          * ((2 : ℝ) ^ (2 * σ * Q) * (1 + (orbitLength ν : ℝ)) ^ (2 * σ * Q)) := by
        refine mul_le_mul_of_nonneg_left (le_trans hexp hshift) ?_
        positivity
    _ = (2 : ℝ) ^ (2 * σ * Q)
          * ((1 + (orbitLength ν : ℝ)) ^ (-(2 * κ)) * (1 + (orbitLength ν : ℝ)) ^ (2 * σ * Q)) := by
        ring
    _ = (2 : ℝ) ^ (2 * σ * Q) * (1 + (orbitLength ν : ℝ)) ^ (-(2 * κ - 2 * σ * Q)) := by
        rw [hcomb]

/-- **`(8)`: both halves at once, from finite logarithmic type.** -/
theorem summable_polynomialEventCarrier {d : ℕ} {σ : ℝ} {τ : (Fin d → ℤ) → ℝ}
    (hσ : 0 ≤ σ) (hτ : HasFiniteLogType τ) :
    ∃ κ : ℝ, 0 < κ ∧
      (Summable fun ν : Fin d → ℤ => fractionalPolynomialOrbitWeight κ ν ^ 2) ∧
      Summable fun ν : Fin d → ℤ =>
        fractionalPolynomialOrbitWeight κ ν ^ 2 * Real.exp (2 * σ * τ ν) := by
  obtain ⟨Q, hQ, hbound⟩ := hτ
  refine ⟨((d : ℝ) + 2 * σ * Q + 1) / 2, by positivity, ?_, ?_⟩
  · refine summable_fractionalPolynomialOrbitWeight_sq ?_
    have h : (0 : ℝ) ≤ 2 * σ * Q := by positivity
    rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  · refine summable_fractionalWeight_sq_mul_exp hσ hQ hbound ?_
    rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    linarith

end RHTower
