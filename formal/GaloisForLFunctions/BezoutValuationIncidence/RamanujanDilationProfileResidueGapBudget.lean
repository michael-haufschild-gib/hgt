import GaloisForLFunctions.BezoutValuationIncidence.PronicResidueGapEnergyAndPrimePairDistance
import GaloisForLFunctions.BezoutValuationIncidence.DilationProfileIntegerJumpCoupling

/-!
# Residue-gap bounds for rational Ramanujan dilation profiles

The existing floor expansion writes the scaled primitive `p * A_r(n / p)` as
an exact finite Möbius-weighted sum of residue modes. The pronic residue-gap
bound therefore applies to the actual rational dilation profile, with explicit
cofactor cost `card(r.divisorsAntidiagonal) * sum (moebius x.2)^2 * x.1`.

The integer-dilation Gram identity identifies the scaled distance with
`(p + q) * G(r,r) - 2 * sqrt(p) * sqrt(q) * Phi_r(p/q)`. Subtracting the radial
scale mismatch gives a quantitative bound for the profile defect itself.
All public results have data parameters only. The bounds control a pairwise
profile distance; summing a signed prime-pair packet requires further estimates.
-/

open Finset RHTower ArithmeticFunction
open scoped BigOperators
namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- Explicit cofactor cost in the residue expansion of the original dilation profile. -/
def ramanujanDilationResidueBudget (r : ℕ) : ℝ :=
  (r.divisorsAntidiagonal.card : ℝ) *
    ∑ x ∈ r.divisorsAntidiagonal, (moebius x.2 : ℝ) ^ 2 * x.1

private theorem scaled_primitive_eq_residues {r : ℕ} (hr : 1 < r) (p n : ℕ) :
    (p : ℝ) * (pmRamanujanPrimitive r (n / p)).re =
      -∑ x ∈ r.divisorsAntidiagonal,
        (moebius x.2 : ℝ) * ((n % (p * x.1) : ℕ) : ℝ) := by
  have hmu : (∑ x ∈ r.divisorsAntidiagonal, (moebius x.2 : ℝ)) = 0 := by
    have h := congrArg Complex.re (pm_mobius_antidiagonal_sum r)
    simpa only [if_neg (by omega : r ≠ 1), Complex.re_sum,
      Complex.intCast_re, Complex.zero_re] using h
  rw [pmRamanujanPrimitive_eq_floor, Complex.re_sum, mul_sum]
  have ht (x : ℕ × ℕ) :
      (p : ℝ) * ((x.1 : ℂ) * (moebius x.2 : ℂ) * (((n / p) / x.1 : ℕ) : ℂ)).re =
        (moebius x.2 : ℝ) * ((n : ℝ) - ((n % (p * x.1) : ℕ) : ℝ)) := by
    rw [Nat.div_div_eq_div_mul]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.intCast_re,
      Complex.natCast_im, Complex.intCast_im, mul_zero, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    have hm : ((n % (p * x.1) : ℕ) : ℝ) +
        (p : ℝ) * x.1 * ((n / (p * x.1) : ℕ) : ℝ) = n := by
      exact_mod_cast Nat.mod_add_div n (p * x.1)
    linear_combination (moebius x.2 : ℝ) * hm
  rw [sum_congr rfl (fun x _ => ht x)]
  simp_rw [mul_sub]
  rw [sum_sub_distrib, ← sum_mul, hmu, zero_mul, zero_sub]

private theorem residue_sq_bound {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (n : ℕ) :
    (((n % p : ℕ) : ℝ) - ((n % q : ℕ) : ℝ)) ^ 2 ≤ ((p : ℝ) + q) ^ 2 := by
  have hpmod : ((n % p : ℕ) : ℝ) ≤ p := by exact_mod_cast (Nat.mod_lt n hp).le
  have hqmod : ((n % q : ℕ) : ℝ) ≤ q := by exact_mod_cast (Nat.mod_lt n hq).le
  have hp0 : (0 : ℝ) ≤ (n % p : ℕ) := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ (n % q : ℕ) := Nat.cast_nonneg _
  have ha : 0 ≤ (p : ℝ) + q - (((n % p : ℕ) : ℝ) - ((n % q : ℕ) : ℝ)) := by linarith
  have hb : 0 ≤ (p : ℝ) + q + (((n % p : ℕ) : ℝ) - ((n % q : ℕ) : ℝ)) := by linarith
  nlinarith [mul_nonneg ha hb]

private theorem residue_gap_summable {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    Summable (residueGapPronicTerm p q) := by
  have h := summable_div_pronicSeq_of_bounded (fun n =>
    show |(((n % p : ℕ) : ℝ) - ((n % q : ℕ) : ℝ)) ^ 2| ≤ ((p : ℝ) + q) ^ 2 from
      by rw [abs_of_nonneg (sq_nonneg _)]; exact residue_sq_bound hp hq n)
  unfold residueGapPronicTerm
  simpa only [cast_pronicSeq_eq] using h

private theorem hasSum_dilation_gram {r : ℕ} (hr : 1 < r) (p q : ℕ) :
    HasSum (fun n : ℕ => (pmRamanujanPrimitive r (n / p)).re *
      (pmRamanujanPrimitive r (n / q)).re / ((n : ℝ) * ((n : ℝ) + 1)))
      (ramanujanIntegerDilationGram r p q) := by
  have hb (d n : ℕ) : |(pmRamanujanPrimitive r (n / d)).re| ≤ pmRamanujanPrimitiveBound r :=
    (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)
  have h := summable_div_pronicSeq_of_bounded (fun n =>
    show |(pmRamanujanPrimitive r (n / p)).re * (pmRamanujanPrimitive r (n / q)).re| ≤
        pmRamanujanPrimitiveBound r ^ 2 from by
      rw [abs_mul, sq]
      exact mul_le_mul (hb p n) (hb q n) (abs_nonneg _) (sum_nonneg fun _ _ => norm_nonneg _))
  simpa only [ramanujanIntegerDilationGram, cast_pronicSeq_eq] using h.hasSum

private theorem hasSum_scaled_dilation_distance {r p q : ℕ}
    (hr : 1 < r) (hp : 0 < p) (hq : 0 < q) :
    HasSum (fun n : ℕ =>
      ((p : ℝ) * (pmRamanujanPrimitive r (n / p)).re -
        (q : ℝ) * (pmRamanujanPrimitive r (n / q)).re) ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1)))
      (((p : ℝ) + q) * pmRamanujanPrimitiveGram r r -
        2 * Real.sqrt p * Real.sqrt q * pmRamanujanDilationProfile r hr ((p : ℝ) / q)) := by
  have hs := (((hasSum_dilation_gram hr p p).mul_left ((p : ℝ) ^ 2)).add
    ((hasSum_dilation_gram hr q q).mul_left ((q : ℝ) ^ 2))).sub
      ((hasSum_dilation_gram hr p q).mul_left (2 * (p : ℝ) * q))
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hqR : (q : ℝ) ≠ 0 := by positivity
  have hpp := pmRamanujanDilationProfile_eq_integerDilationGram hr hp hp
  rw [div_self hpR, pmRamanujanDilationProfile_one,
    Real.mul_self_sqrt (Nat.cast_nonneg p)] at hpp
  have hqq := pmRamanujanDilationProfile_eq_integerDilationGram hr hq hq
  rw [div_self hqR, pmRamanujanDilationProfile_one,
    Real.mul_self_sqrt (Nat.cast_nonneg q)] at hqq
  have hpq := pmRamanujanDilationProfile_eq_integerDilationGram hr hp hq
  have hc : 2 * (p : ℝ) * q * ramanujanIntegerDilationGram r p q =
      2 * Real.sqrt p * Real.sqrt q * pmRamanujanDilationProfile r hr ((p : ℝ) / q) := by
    rw [hpq]
    calc
      _ = 2 * (Real.sqrt p) ^ 2 * (Real.sqrt q) ^ 2 * ramanujanIntegerDilationGram r p q := by
        rw [Real.sq_sqrt (Nat.cast_nonneg p), Real.sq_sqrt (Nat.cast_nonneg q)]
      _ = _ := by ring
  have he : (p : ℝ) ^ 2 * ramanujanIntegerDilationGram r p p +
      (q : ℝ) ^ 2 * ramanujanIntegerDilationGram r q q -
      2 * (p : ℝ) * q * ramanujanIntegerDilationGram r p q =
      ((p : ℝ) + q) * pmRamanujanPrimitiveGram r r -
        2 * Real.sqrt p * Real.sqrt q * pmRamanujanDilationProfile r hr ((p : ℝ) / q) := by
    rw [hc]
    have hpp' := congrArg (fun x : ℝ => (p : ℝ) * x) hpp
    have hqq' := congrArg (fun x : ℝ => (q : ℝ) * x) hqq
    nlinarith
  rw [he] at hs
  exact hs.congr_fun (fun n => by ring)

private theorem scaled_primitive_gap_sq_le {r : ℕ} (hr : 1 < r) (p q n : ℕ) :
    ((p : ℝ) * (pmRamanujanPrimitive r (n / p)).re -
      (q : ℝ) * (pmRamanujanPrimitive r (n / q)).re) ^ 2 ≤
      (r.divisorsAntidiagonal.card : ℝ) *
        ∑ x ∈ r.divisorsAntidiagonal, (moebius x.2 : ℝ) ^ 2 *
          (((n % (p * x.1) : ℕ) : ℝ) - ((n % (q * x.1) : ℕ) : ℝ)) ^ 2 := by
  have hd : (p : ℝ) * (pmRamanujanPrimitive r (n / p)).re -
      (q : ℝ) * (pmRamanujanPrimitive r (n / q)).re =
      -∑ x ∈ r.divisorsAntidiagonal, (moebius x.2 : ℝ) *
        (((n % (p * x.1) : ℕ) : ℝ) - ((n % (q * x.1) : ℕ) : ℝ)) := by
    rw [scaled_primitive_eq_residues hr, scaled_primitive_eq_residues hr]
    simp_rw [mul_sub]
    rw [sum_sub_distrib]
    ring
  rw [hd, neg_sq]
  have h := Finset.sum_mul_sq_le_sq_mul_sq r.divisorsAntidiagonal
    (fun _ => (1 : ℝ)) (fun x => (moebius x.2 : ℝ) *
      (((n % (p * x.1) : ℕ) : ℝ) - ((n % (q * x.1) : ℕ) : ℝ)))
  simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, mul_pow] using h


/-- Dilating both moduli multiplies the explicit residue-gap budget by that scale. -/
theorem residueGapPronicBudget_mul (p q : ℕ) (d : ℕ+) :
    residueGapPronicBudget (p * d) (q * d) = (d : ℝ) * residueGapPronicBudget p q := by
  have hpd : p * (d : ℕ) = q * d ↔ p = q := by
    constructor
    · exact fun h => mul_right_cancel₀ d.ne_zero h
    · exact fun h => congrArg (fun n : ℕ => n * d) h
  have hmin : min (p * (d : ℕ)) (q * d) = min p q * d := by
    rcases le_total p q with h | h
    · rw [min_eq_left h, min_eq_left (Nat.mul_le_mul_right (d : ℕ) h)]
    · rw [min_eq_right h, min_eq_right (Nat.mul_le_mul_right (d : ℕ) h)]
  have hmax : max (p * (d : ℕ)) (q * d) = max p q * d := by
    rcases le_total p q with h | h
    · rw [max_eq_right h, max_eq_right (Nat.mul_le_mul_right (d : ℕ) h)]
    · rw [max_eq_left h, max_eq_left (Nat.mul_le_mul_right (d : ℕ) h)]
  simp only [residueGapPronicBudget, hpd, hmin, hmax]
  split_ifs
  · ring
  · rw [← Nat.mul_sub_right_distrib, Nat.mul_div_mul_right _ _ d.pos]
    push_cast
    have hdR : (d : ℝ) ≠ 0 := by positivity
    field_simp

private theorem scaled_distance_le_budgets {r : ℕ} (hr : 1 < r) (p q : ℕ+) :
    ((p : ℝ) + q) * pmRamanujanPrimitiveGram r r -
      2 * Real.sqrt p * Real.sqrt q * pmRamanujanDilationProfile r hr ((p : ℝ) / q) ≤
      ramanujanDilationResidueBudget r * residueGapPronicBudget p q := by
  have hs : HasSum (fun n : ℕ => ∑ x ∈ r.divisorsAntidiagonal,
      (moebius x.2 : ℝ) ^ 2 * residueGapPronicTerm (p * x.1) (q * x.1) n)
      (∑ x ∈ r.divisorsAntidiagonal,
        (moebius x.2 : ℝ) ^ 2 * residueGapPronicEnergy (p * x.1) (q * x.1)) := by
    apply hasSum_sum
    intro x hx
    have hx0 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
    exact (residue_gap_summable (Nat.mul_pos p.pos hx0) (Nat.mul_pos q.pos hx0)).hasSum.mul_left _
  have he := hasSum_scaled_dilation_distance hr p.pos q.pos
  have h := Summable.tsum_le_tsum (fun n => by
      have hb := div_le_div_of_nonneg_right (scaled_primitive_gap_sq_le hr p q n)
        (show (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) by positivity)
      simpa only [mul_div_assoc, sum_div, residueGapPronicTerm] using hb)
    he.summable (hs.mul_left (r.divisorsAntidiagonal.card : ℝ)).summable
  rw [he.tsum_eq, (hs.mul_left (r.divisorsAntidiagonal.card : ℝ)).tsum_eq] at h
  apply h.trans
  unfold ramanujanDilationResidueBudget
  rw [mul_assoc, sum_mul]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro x hx
  have hx0 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
  have hb := residueGapPronicEnergy_le_budget
    ⟨(p : ℕ) * x.1, Nat.mul_pos p.pos hx0⟩ ⟨(q : ℕ) * x.1, Nat.mul_pos q.pos hx0⟩
  change residueGapPronicEnergy ((p : ℕ) * x.1) ((q : ℕ) * x.1) ≤
    residueGapPronicBudget ((p : ℕ) * x.1) ((q : ℕ) * x.1) at hb
  have hscale := residueGapPronicBudget_mul (p : ℕ) (q : ℕ) ⟨x.1, hx0⟩
  change residueGapPronicBudget ((p : ℕ) * x.1) ((q : ℕ) * x.1) =
    (x.1 : ℝ) * residueGapPronicBudget p q at hscale
  rw [hscale] at hb
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (sq_nonneg (moebius x.2 : ℝ))

/-- The original scaled primitive is a finite Möbius-weighted sum of residue modes. -/
theorem scaled_pmRamanujanPrimitive_eq_residues (r p n : ℕ) :
    (p : ℝ) * (pmRamanujanPrimitive (r + 2) (n / p)).re =
      -∑ x ∈ (r + 2).divisorsAntidiagonal,
        (moebius x.2 : ℝ) * ((n % (p * x.1) : ℕ) : ℝ) :=
  scaled_primitive_eq_residues (by omega) p n

/-- The scaled primitive distance sums exactly to the original rational profile defect. -/
theorem hasSum_scaled_pmRamanujanPrimitive_distance (r : ℕ) (p q : ℕ+) :
    HasSum (fun n : ℕ =>
      ((p : ℝ) * (pmRamanujanPrimitive (r + 2) (n / p)).re -
        (q : ℝ) * (pmRamanujanPrimitive (r + 2) (n / q)).re) ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1)))
      (((p : ℝ) + q) * pmRamanujanPrimitiveGram (r + 2) (r + 2) -
        2 * Real.sqrt p * Real.sqrt q *
          pmRamanujanDilationProfile (r + 2) (by omega) ((p : ℝ) / q)) :=
  hasSum_scaled_dilation_distance (by omega) p.pos q.pos

/-- The original rational dilation profile has an explicit residue-gap budget at every scale. -/
theorem ramanujanDilationProfile_gap_budget (r : ℕ) (p q : ℕ+) :
    0 ≤ ((p : ℝ) + q) * pmRamanujanPrimitiveGram (r + 2) (r + 2) -
      2 * Real.sqrt p * Real.sqrt q *
        pmRamanujanDilationProfile (r + 2) (by omega) ((p : ℝ) / q) ∧
    ((p : ℝ) + q) * pmRamanujanPrimitiveGram (r + 2) (r + 2) -
      2 * Real.sqrt p * Real.sqrt q *
        pmRamanujanDilationProfile (r + 2) (by omega) ((p : ℝ) / q) ≤
      ramanujanDilationResidueBudget (r + 2) * residueGapPronicBudget p q := by
  constructor
  · rw [← (hasSum_scaled_dilation_distance (by omega : 1 < r + 2) p.pos q.pos).tsum_eq]
    exact tsum_nonneg fun n => div_nonneg (sq_nonneg _) (by positivity)
  · exact scaled_distance_le_budgets (by omega) p q

/-- Removing the radial scale mismatch gives a quantitative bound for the profile defect itself. -/
theorem ramanujanDilationProfile_defect_le_gap_budget (r : ℕ) (p q : ℕ+) :
    0 ≤ pmRamanujanPrimitiveGram (r + 2) (r + 2) -
      pmRamanujanDilationProfile (r + 2) (by omega) ((p : ℝ) / q) ∧
    2 * Real.sqrt p * Real.sqrt q *
        (pmRamanujanPrimitiveGram (r + 2) (r + 2) -
          pmRamanujanDilationProfile (r + 2) (by omega) ((p : ℝ) / q)) ≤
      ramanujanDilationResidueBudget (r + 2) * residueGapPronicBudget p q -
        (Real.sqrt p - Real.sqrt q) ^ 2 * pmRamanujanPrimitiveGram (r + 2) (r + 2) := by
  constructor
  · apply sub_nonneg.mpr
    exact (le_abs_self _).trans (abs_pmRamanujanDilationProfile_le (by omega)
      (div_pos (by positivity) (by positivity)))
  · have h := (ramanujanDilationProfile_gap_budget r p q).2
    have hp := Real.sq_sqrt (show (0 : ℝ) ≤ p by positivity)
    have hq := Real.sq_sqrt (show (0 : ℝ) ≤ q by positivity)
    have hpG := congrArg (fun x : ℝ => x * pmRamanujanPrimitiveGram (r + 2) (r + 2)) hp
    have hqG := congrArg (fun x : ℝ => x * pmRamanujanPrimitiveGram (r + 2) (r + 2)) hq
    nlinarith

end
end GaloisForLFunctions.BezoutValuationIncidence
