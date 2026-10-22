import GaloisForLFunctions.RHTower.Suzuki.SuzukiOrbitWeightSummability
import GaloisForLFunctions.HTGeometry.FlatVolterraDecay

/-!
# Polynomial orbit weights are square summable against logarithmic events

A finite-logarithmic-recurrence aperture has event times bounded by `Q log (2 + |ν|₁)`, so the
event factor `e^{2στ(ν)}` is at most a fixed power of `1 + |ν|₁`.  A polynomial weight
`(1 + |ν|₁)^{-κ}` therefore stays square summable as soon as the surviving exponent beats twice the
rank: the coordinatewise bound

`(1 + |ν|₁)^{-m} ≤ ∏_j (1 + |ν_j|)^{-2}`   for `m ≥ 2d`

turns the lattice sum into a rank power of the one-dimensional sum `∑_{n ∈ ℤ} (1+|n|)^{-2}`.
-/

open Filter
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- The one-dimensional coordinate mass of the quadratic weight. -/
theorem tsum_inv_one_add_natAbs_sq_ne_top :
    (∑' n : ℤ, ENNReal.ofReal (1 / ((1 + (n.natAbs : ℝ)) ^ 2))) ≠ ⊤ := by
  have hsummable : Summable fun n : ℤ => 1 / ((1 + (n.natAbs : ℝ)) ^ 2) := by
    have hbase : Summable fun k : ℕ => 1 / ((1 + (k : ℝ)) ^ 2) := by
      have h : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 :=
        GaloisForLFunctions.HTGeometry.summable_inv_succ_sq_flatVolterraDecay
      refine h.congr fun k => ?_
      ring_nf
    refine (Summable.of_nat_of_neg (f := fun n : ℤ => 1 / ((1 + (n.natAbs : ℝ)) ^ 2)) ?_ ?_)
    · refine hbase.congr fun k => ?_
      simp
    · refine hbase.congr fun k => ?_
      simp
  have hnn : ∀ n : ℤ, 0 ≤ 1 / ((1 + (n.natAbs : ℝ)) ^ 2) := fun n => by positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsummable]
  exact ENNReal.ofReal_ne_top

/-- The rank product of the quadratic coordinate mass is finite. -/
theorem tsum_prod_inv_one_add_natAbs_sq_ne_top (d : ℕ) :
    (∑' ν : Fin d → ℤ, ∏ j : Fin d,
        ENNReal.ofReal (1 / ((1 + ((ν j).natAbs : ℝ)) ^ 2))) ≠ ⊤ := by
  induction d with
  | zero =>
      haveI : Subsingleton (Fin 0 → ℤ) := ⟨fun f g => funext fun i => i.elim0⟩
      haveI : Unique (Fin 0 → ℤ) := uniqueOfSubsingleton (0 : Fin 0 → ℤ)
      rw [tsum_eq_single default (fun b hb => absurd (Subsingleton.elim b default) hb)]
      simp
  | succ k ih =>
      have hre : (∑' ν : Fin (k + 1) → ℤ,
            ∏ j : Fin (k + 1), ENNReal.ofReal (1 / ((1 + ((ν j).natAbs : ℝ)) ^ 2)))
          = ∑' q : ℤ × (Fin k → ℤ), ∏ j : Fin (k + 1),
              ENNReal.ofReal (1 / ((1 + (((consValuationEquiv k q) j).natAbs : ℝ)) ^ 2)) :=
        ((consValuationEquiv k).tsum_eq (fun ν : Fin (k + 1) → ℤ =>
          ∏ j : Fin (k + 1), ENNReal.ofReal (1 / ((1 + ((ν j).natAbs : ℝ)) ^ 2)))).symm
      have hterm : ∀ q : ℤ × (Fin k → ℤ),
          (∏ j : Fin (k + 1),
              ENNReal.ofReal (1 / ((1 + (((consValuationEquiv k q) j).natAbs : ℝ)) ^ 2)))
            = ENNReal.ofReal (1 / ((1 + ((q.1).natAbs : ℝ)) ^ 2))
              * ∏ j : Fin k, ENNReal.ofReal (1 / ((1 + ((q.2 j).natAbs : ℝ)) ^ 2)) := by
        intro q
        rw [Fin.prod_univ_succ, consValuationEquiv_apply, Fin.cons_zero]
        refine congrArg _ (Finset.prod_congr rfl fun j _ => ?_)
        rw [Fin.cons_succ]
      rw [hre, tsum_congr hterm, ENNReal.tsum_prod']
      have hinner : ∀ a : ℤ,
          (∑' v : Fin k → ℤ, ENNReal.ofReal (1 / ((1 + (a.natAbs : ℝ)) ^ 2))
              * ∏ j : Fin k, ENNReal.ofReal (1 / ((1 + ((v j).natAbs : ℝ)) ^ 2)))
            = ENNReal.ofReal (1 / ((1 + (a.natAbs : ℝ)) ^ 2))
              * ∑' v : Fin k → ℤ, ∏ j : Fin k,
                ENNReal.ofReal (1 / ((1 + ((v j).natAbs : ℝ)) ^ 2)) :=
        fun a => ENNReal.tsum_mul_left
      rw [tsum_congr hinner, ENNReal.tsum_mul_right]
      exact ENNReal.mul_ne_top tsum_inv_one_add_natAbs_sq_ne_top ih

/-- **The polynomial lattice mass is finite** as soon as the exponent is twice the rank. -/
theorem tsum_inv_pow_orbitLength_fin_ne_top {d m : ℕ} (hm : 2 * d ≤ m) :
    (∑' ν : Fin d → ℤ, ENNReal.ofReal (1 / ((1 + (orbitLength ν : ℝ)) ^ m))) ≠ ⊤ := by
  have hmajor : ∀ ν : Fin d → ℤ,
      ENNReal.ofReal (1 / ((1 + (orbitLength ν : ℝ)) ^ m))
        ≤ ∏ j : Fin d, ENNReal.ofReal (1 / ((1 + ((ν j).natAbs : ℝ)) ^ 2)) := by
    intro ν
    have hprod : (∏ j : Fin d, ((1 + ((ν j).natAbs : ℝ)) ^ 2))
        ≤ (1 + (orbitLength ν : ℝ)) ^ m := by
      have hcoord : ∀ j : Fin d, ((1 + ((ν j).natAbs : ℝ)) ^ 2)
          ≤ (1 + (orbitLength ν : ℝ)) ^ 2 := by
        intro j
        have hle : ((ν j).natAbs : ℝ) ≤ (orbitLength ν : ℝ) := by
          have : (ν j).natAbs ≤ orbitLength ν := by
            rw [orbitLength]
            exact Finset.single_le_sum (f := fun p : Fin d => (ν p).natAbs)
              (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
          exact_mod_cast this
        have h0 : (0:ℝ) ≤ 1 + ((ν j).natAbs : ℝ) := by positivity
        exact pow_le_pow_left₀ h0 (by linarith) 2
      have hstep : (∏ j : Fin d, ((1 + ((ν j).natAbs : ℝ)) ^ 2))
          ≤ ∏ _j : Fin d, ((1 + (orbitLength ν : ℝ)) ^ 2) := by
        refine Finset.prod_le_prod (fun j _ => ?_) (fun j _ => hcoord j)
        have h0 : (0:ℝ) ≤ 1 + ((ν j).natAbs : ℝ) := by positivity
        exact pow_nonneg h0 2
      have hconst : (∏ _j : Fin d, ((1 + (orbitLength ν : ℝ)) ^ 2))
          = (1 + (orbitLength ν : ℝ)) ^ (2 * d) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      have hgrow : (1 + (orbitLength ν : ℝ)) ^ (2 * d) ≤ (1 + (orbitLength ν : ℝ)) ^ m :=
        pow_le_pow_right₀ (by
          have h0 : (0:ℝ) ≤ (orbitLength ν : ℝ) := by positivity
          linarith) hm
      rw [hconst] at hstep
      linarith
    have hpos : (0:ℝ) < ∏ j : Fin d, ((1 + ((ν j).natAbs : ℝ)) ^ 2) := by
      refine Finset.prod_pos ?_
      intro j _
      positivity
    have hle : 1 / ((1 + (orbitLength ν : ℝ)) ^ m)
        ≤ ∏ j : Fin d, (1 / ((1 + ((ν j).natAbs : ℝ)) ^ 2)) := by
      rw [Finset.prod_div_distrib, Finset.prod_const_one]
      apply div_le_div_of_nonneg_left one_pos.le hpos hprod
    calc ENNReal.ofReal (1 / ((1 + (orbitLength ν : ℝ)) ^ m))
        ≤ ENNReal.ofReal (∏ j : Fin d, (1 / ((1 + ((ν j).natAbs : ℝ)) ^ 2))) :=
          ENNReal.ofReal_le_ofReal hle
      _ = ∏ j : Fin d, ENNReal.ofReal (1 / ((1 + ((ν j).natAbs : ℝ)) ^ 2)) := by
          rw [ENNReal.ofReal_prod_of_nonneg]
          intro j _
          positivity
  exact ne_top_of_le_ne_top (tsum_prod_inv_one_add_natAbs_sq_ne_top d)
    (ENNReal.tsum_le_tsum hmajor)

/-- **`(8)`, `(13)`: a polynomial orbit weight is square summable against the logarithmic event
factor.** -/
theorem summable_inv_pow_orbitLength {d m : ℕ} (hm : 2 * d ≤ m) :
    Summable fun ν : Fin d → ℤ => 1 / ((1 + (orbitLength ν : ℝ)) ^ m) := by
  have hnn : ∀ ν : Fin d → ℤ, 0 ≤ 1 / ((1 + (orbitLength ν : ℝ)) ^ m) := fun ν => by positivity
  have hfin := tsum_inv_pow_orbitLength_fin_ne_top hm
  have hcoe : ∀ ν : Fin d → ℤ,
      ENNReal.ofReal (1 / ((1 + (orbitLength ν : ℝ)) ^ m))
        = ((Real.toNNReal (1 / ((1 + (orbitLength ν : ℝ)) ^ m)) : NNReal) : ℝ≥0∞) :=
    fun ν => rfl
  rw [tsum_congr hcoe] at hfin
  have hsum := (ENNReal.tsum_coe_ne_top_iff_summable).mp hfin
  have hreal := NNReal.summable_coe.mpr hsum
  refine hreal.congr fun ν => ?_
  exact Real.coe_toNNReal _ (hnn ν)

/-- **`(14)`: the polynomial weight has bounded generator ratios.** -/
theorem polynomial_weight_ratio_le {d : ℕ} (κ : ℕ) (ν s : Fin d → ℤ) :
    (1 + (orbitLength (ν + s) : ℝ)) ^ κ
      ≤ (1 + (orbitLength ν : ℝ)) ^ κ * (1 + (orbitLength s : ℝ)) ^ κ := by
  have hsub : orbitLength (ν + s) ≤ orbitLength ν + orbitLength s := orbitLength_add_le ν s
  have hsubR : (orbitLength (ν + s) : ℝ) ≤ (orbitLength ν : ℝ) + (orbitLength s : ℝ) := by
    exact_mod_cast hsub
  have hprod : (1 + (orbitLength (ν + s) : ℝ))
      ≤ (1 + (orbitLength ν : ℝ)) * (1 + (orbitLength s : ℝ)) := by
    have h1 : (0:ℝ) ≤ (orbitLength ν : ℝ) := by positivity
    have h2 : (0:ℝ) ≤ (orbitLength s : ℝ) := by positivity
    nlinarith [hsubR, h1, h2]
  have h0 : (0:ℝ) ≤ 1 + (orbitLength (ν + s) : ℝ) := by positivity
  calc (1 + (orbitLength (ν + s) : ℝ)) ^ κ
      ≤ ((1 + (orbitLength ν : ℝ)) * (1 + (orbitLength s : ℝ))) ^ κ :=
        pow_le_pow_left₀ h0 hprod κ
    _ = (1 + (orbitLength ν : ℝ)) ^ κ * (1 + (orbitLength s : ℝ)) ^ κ := by
        rw [mul_pow]

/-- **`(8)`, `(12)`, `(13)`: the polynomial carrier is square summable against a logarithmic event
family.**  A logarithmic event bound costs `n` powers, and the surviving exponent `m ≥ 2d` keeps the
lattice sum finite. -/
theorem summable_polynomial_carrier {d n m : ℕ} (hm : 2 * d ≤ m) {σ : ℝ}
    (τ : (Fin d → ℤ) → ℝ)
    (hbound : ∀ ν, 2 * σ * τ ν ≤ (n : ℝ) * Real.log (2 + (orbitLength ν : ℝ))) :
    Summable fun ν : Fin d → ℤ =>
      (1 / (1 + (orbitLength ν : ℝ)) ^ (n + m)) * Real.exp (2 * σ * τ ν) := by
  have hbase := (summable_inv_pow_orbitLength (d := d) (m := m) hm).mul_left ((2:ℝ) ^ n)
  refine Summable.of_nonneg_of_le (fun ν => ?_) (fun ν => ?_) hbase
  · positivity
  · set L : ℝ := (orbitLength ν : ℝ) with hL
    have hL0 : (0:ℝ) ≤ L := by rw [hL]; positivity
    have hpos2 : (0:ℝ) < 2 + L := by linarith
    have hpos1 : (0:ℝ) < 1 + L := by linarith
    have hexp : Real.exp (2 * σ * τ ν) ≤ (2 + L) ^ n := by
      have hstep : Real.exp (2 * σ * τ ν) ≤ Real.exp ((n : ℝ) * Real.log (2 + L)) :=
        Real.exp_le_exp.mpr (hbound ν)
      have hval : Real.exp ((n : ℝ) * Real.log (2 + L)) = (2 + L) ^ n := by
        rw [mul_comm, Real.exp_mul, Real.exp_log hpos2, ← Real.rpow_natCast (2 + L) n]
      linarith [hval ▸ hstep]
    have hshift : (2 + L) ^ n ≤ 2 ^ n * (1 + L) ^ n := by
      have hle : (2 + L) ≤ 2 * (1 + L) := by linarith
      calc (2 + L) ^ n ≤ (2 * (1 + L)) ^ n := pow_le_pow_left₀ (by linarith) hle n
        _ = 2 ^ n * (1 + L) ^ n := by rw [mul_pow]
    have hsplit : (1 + L) ^ (n + m) = (1 + L) ^ n * (1 + L) ^ m := by rw [pow_add]
    have hposn : (0:ℝ) < (1 + L) ^ n := by positivity
    have hposm : (0:ℝ) < (1 + L) ^ m := by positivity
    calc (1 / (1 + L) ^ (n + m)) * Real.exp (2 * σ * τ ν)
        ≤ (1 / (1 + L) ^ (n + m)) * (2 ^ n * (1 + L) ^ n) := by
          have hle := le_trans hexp hshift
          have hposinv : (0:ℝ) < 1 / (1 + L) ^ (n + m) := by positivity
          nlinarith [hle, hposinv]
      _ = 2 ^ n * (1 / (1 + L) ^ m) := by
          rw [hsplit]
          field_simp

end

end RHTower
