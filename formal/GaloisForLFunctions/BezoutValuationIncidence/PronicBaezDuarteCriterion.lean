import GaloisForLFunctions.BezoutValuationIncidence.VasyuninReciprocityForAllModuliFromPronicCovariance
import GaloisForLFunctions.RHTower.BaezDuarteCriterionHardDirection

/-!
# The Báez-Duarte criterion as a pronic energy of prefix discrepancies

For a real row `c` on `[1, N]` the Báez-Duarte residual `1_{(0,1]} - Σ_n c(n) ρ_{1/n}` has squared
norm

`1 - 2 Σ_n c(n) log n / n + Σ_{n,m} c(n) c(m) bdGram(1/n, 1/m)`.

By the Vasyunin formula `n m bdGram(1/n, 1/m) = Σ_M (M mod n)(M mod m) w(M)` and the pronic mean
`Σ_M (M mod n) w(M) = log n`, with `w(M) = 1/(M(M+1))` of total mass one, this is the pronic energy

`Σ_M (1 - Σ_n c(n)(M mod n)/n)² w(M) = Σ_M (1 + L_N(M, c))² / (M(M+1))`

of the prefix discrepancy `L_N(M, c) = -Σ_n c(n) {M/n}`, shifted by one. With the Báez-Duarte criterion
this gives an exact equivalence in the objects of the theory:

**The Riemann hypothesis holds iff for every `ε > 0` some finite row `c` has
`Σ_{M ≥ 1} (1 + L_N(M, c))²/(M(M+1)) < ε`.**

The receiver of the theory bounds the pronic energy of the centered Möbius prefix. This criterion asks
for the opposite extremal problem: approximating the constant `-1` by prefix discrepancies in pronic
energy.
-/

open Finset Filter Topology RHTower
open scoped BigOperators InnerProductSpace

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The prefix discrepancy in residue form: `L_N(M, c) = -Σ_n c(n)(M mod n)/n`. -/
theorem sievePrefixDiscrepancy_eq_neg_residue (N M : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy N M c = -∑ n ∈ Icc 1 N, c n * ((M % n : ℕ) : ℝ) / n := by
  rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum, sievedFractSum_eq_residueCombination,
    DeletionPeriodCovariance.residueCombination]

/-- The discrete Báez-Duarte Gram is the Vasyunin second moment over `n m`. -/
theorem bdGram_inv_nat_eq_secondMoment {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    bdGram ((n : ℝ)⁻¹) ((m : ℝ)⁻¹) = vasyuninSecondMoment n m / ((n : ℝ) * m) := by
  rw [← one_div, ← one_div, bdGram_inv_nat_eq_vasyunin hn hm, vasyuninSecondMoment]

/-- **The Báez-Duarte residual norm is the pronic energy of `1 + L_N(·, c)`.** -/
theorem norm_sq_bdResidual_eq_pronicEnergy (N : ℕ) (c : ℕ → ℝ) :
    HasSum (fun M : ℕ => (1 + sievePrefixDiscrepancy N M c) ^ 2 / ((M : ℝ) * ((M : ℝ) + 1)))
      (‖bdTarget - ∑ n ∈ Icc 1 N, (c n : ℂ) • bdGen ((n : ℝ)⁻¹)‖ ^ 2) := by
  classical
  have hS : ∀ n ∈ Icc 1 N, 1 ≤ n := fun n hn => (mem_Icc.mp hn).1
  -- the residual norm as a quadratic form in `c`
  have hnorm : ‖bdTarget - ∑ n ∈ Icc 1 N, (c n : ℂ) • bdGen ((n : ℝ)⁻¹)‖ ^ 2 =
      1 - 2 * ∑ n ∈ Icc 1 N, c n * (Real.log n / n) +
        ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, c n * c m * (vasyuninSecondMoment n m / ((n : ℝ) * m)) := by
    have hexp := norm_sq_sub_combination (fun j : Icc 1 N => bdGen (((j : ℕ) : ℝ)⁻¹)) bdTarget
      (fun j : Icc 1 N => ((c j : ℝ) : ℂ))
    rw [norm_bdTarget, one_pow] at hexp
    rw [← Finset.sum_coe_sort (Icc 1 N)]
    rw [show ‖bdTarget - ∑ j : Icc 1 N, ((c j : ℝ) : ℂ) • bdGen (((j : ℕ) : ℝ)⁻¹)‖ ^ 2 =
      ‖bdTarget - ∑ j : Icc 1 N, ((c j : ℝ) : ℂ) • bdGen (((j : ℕ) : ℝ)⁻¹)‖ ^ (2 : ℕ) from rfl, hexp]
    have hpair : RCLike.re (∑ i : Icc 1 N, (starRingEnd ℂ) (((c i : ℝ) : ℂ)) *
        inner ℂ (bdGen (((i : ℕ) : ℝ)⁻¹)) bdTarget) = ∑ n ∈ Icc 1 N, c n * (Real.log n / n) := by
      rw [← Finset.sum_coe_sort (Icc 1 N), map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hS i i.2
      rw [inner_bdGen_bdTarget (by positivity) (inv_le_one_of_one_le₀ hi), Complex.conj_ofReal,
        ← Complex.ofReal_mul]
      show (c i * -((((i : ℕ) : ℝ))⁻¹ * Real.log (((i : ℕ) : ℝ))⁻¹)) = _
      rw [Real.log_inv]
      ring
    have hgram : RCLike.re (∑ i : Icc 1 N, ∑ j : Icc 1 N, (starRingEnd ℂ) (((c i : ℝ) : ℂ)) *
        ((c j : ℝ) : ℂ) * inner ℂ (bdGen (((i : ℕ) : ℝ)⁻¹)) (bdGen (((j : ℕ) : ℝ)⁻¹))) =
        ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, c n * c m * (vasyuninSecondMoment n m / ((n : ℝ) * m)) := by
      rw [← Finset.sum_coe_sort (Icc 1 N), map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_coe_sort (Icc 1 N), map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_bdGen_eq_bdGram, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        bdGram_inv_nat_eq_secondMoment (hS i i.2) (hS j j.2)]
      rfl
    rw [hpair, hgram]
  rw [hnorm]
  -- the pronic energy expanded into moments
  set w : ℕ → ℝ := fun M => 1 / ((M : ℝ) * ((M : ℝ) + 1))
  have hw : HasSum w 1 := RHTower.hasSum_pm_reciprocal_weight
  have hmean : HasSum (fun M : ℕ => ∑ n ∈ Icc 1 N, c n * ((M % n : ℕ) : ℝ) / n * w M)
      (∑ n ∈ Icc 1 N, c n * (Real.log n / n)) := by
    refine hasSum_sum fun n hn => ?_
    have h := (hasSum_natMod_pronic (hS n hn)).mul_left (c n / n)
    rw [show c n * (Real.log n / n) = c n / n * Real.log n by ring]
    exact h.congr_fun fun M => by simp only [w]; ring
  have hsecond : HasSum (fun M : ℕ => ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
      c n * c m / ((n : ℝ) * m) * (((M % n : ℕ) : ℝ) * ((M % m : ℕ) : ℝ) / ((M : ℝ) * ((M : ℝ) + 1))))
      (∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, c n * c m * (vasyuninSecondMoment n m / ((n : ℝ) * m))) := by
    refine hasSum_sum fun n hn => hasSum_sum fun m hm => ?_
    have h := (hasSum_natMod_mul_natMod_vasyunin (hS n hn) (hS m hm)).mul_left
      (c n * c m / ((n : ℝ) * m))
    rw [show c n * c m * (vasyuninSecondMoment n m / ((n : ℝ) * m)) =
      c n * c m / ((n : ℝ) * m) * vasyuninSecondMoment n m by ring]
    exact h
  have htot := (hw.sub (hmean.mul_left 2)).add hsecond
  refine htot.congr_fun fun M => ?_
  rw [sievePrefixDiscrepancy_eq_neg_residue]
  have hA1 : ∑ n ∈ Icc 1 N, c n * ((M % n : ℕ) : ℝ) / n * w M =
      (∑ n ∈ Icc 1 N, c n * ((M % n : ℕ) : ℝ) / n) * w M := by rw [sum_mul]
  have hA2 : ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, c n * c m / ((n : ℝ) * m) *
      (((M % n : ℕ) : ℝ) * ((M % m : ℕ) : ℝ) / ((M : ℝ) * ((M : ℝ) + 1))) =
      (∑ n ∈ Icc 1 N, c n * ((M % n : ℕ) : ℝ) / n) ^ 2 * w M := by
    rw [sq, sum_mul_sum, sum_mul]
    refine sum_congr rfl fun n hn => ?_
    rw [sum_mul]
    refine sum_congr rfl fun m hm => ?_
    have hn0 : (n : ℝ) ≠ 0 := by have := hS n hn; positivity
    have hm0 : (m : ℝ) ≠ 0 := by have := hS m hm; positivity
    simp only [w]
    field_simp
  rw [hA1, hA2]
  simp only [w]
  ring

/-- **The pronic Báez-Duarte criterion.** The Riemann hypothesis holds iff the constant `-1` is a
pronic-energy limit of prefix discrepancies of finite rows. -/
theorem riemannHypothesis_iff_pronic_prefix_energy :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (c : ℕ → ℝ),
      ∑' M : ℕ, (1 + sievePrefixDiscrepancy N M c) ^ 2 / ((M : ℝ) * ((M : ℝ) + 1)) < ε := by
  constructor
  · intro hRH ε hε
    obtain ⟨N, δ, -, -, hlt⟩ := exists_bdRiesz_norm_lt_of_rh hRH (Real.sqrt_pos.mpr hε)
    refine ⟨N, bdRieszCoeff N δ, ?_⟩
    rw [(norm_sq_bdResidual_eq_pronicEnergy N (bdRieszCoeff N δ)).tsum_eq]
    have h0 := norm_nonneg (bdTarget - ∑ n ∈ Icc 1 N, (bdRieszCoeff N δ n : ℂ) • bdGen ((n : ℝ)⁻¹))
    calc ‖bdTarget - ∑ n ∈ Icc 1 N, (bdRieszCoeff N δ n : ℂ) • bdGen ((n : ℝ)⁻¹)‖ ^ 2
        < Real.sqrt ε ^ 2 := pow_lt_pow_left₀ hlt h0 two_ne_zero
      _ = ε := Real.sq_sqrt hε.le
  · intro h
    refine riemannHypothesis_of_bdDistDiscrete_reciprocalWitnesses fun k => ?_
    have hk : (0 : ℝ) < 1 / ((k + 1 : ℕ) : ℝ) := by positivity
    obtain ⟨N, c, hc⟩ := h _ (pow_pos hk 2)
    refine ⟨N, ?_⟩
    rw [(norm_sq_bdResidual_eq_pronicEnergy N c).tsum_eq] at hc
    have hle := bdDistDiscrete_le_norm_sub_sum N c
    have hnorm : ‖bdTarget - ∑ n ∈ Icc 1 N, (c n : ℂ) • bdGen ((n : ℝ)⁻¹)‖ < 1 / ((k + 1 : ℕ) : ℝ) :=
      lt_of_pow_lt_pow_left₀ 2 hk.le hc
    exact lt_of_le_of_lt hle hnorm

end

end GaloisForLFunctions.BezoutValuationIncidence
