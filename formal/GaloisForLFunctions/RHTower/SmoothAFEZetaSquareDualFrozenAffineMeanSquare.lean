import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualFrozenMass
import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquareInfinite

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

/-- Positive-index frozen dual coefficient with a retained center phase. -/
def smoothAFEZetaSquareDualFrozenNatCoefficient
    (N : ℕ) (center : ℝ) (k : ℕ) : ℂ :=
  if k = 0 then 0
  else ((k.divisors.card : ℂ) *
    (k : ℂ) ^ (linePt center - 1) *
      smoothAFEZetaSquareDualWeight (N : ℝ) ((k : ℝ) * (N : ℝ)))

@[simp] theorem smoothAFEZetaSquareDualFrozenNatCoefficient_zero
    (N : ℕ) (center : ℝ) :
    smoothAFEZetaSquareDualFrozenNatCoefficient N center 0 = 0 := by
  simp [smoothAFEZetaSquareDualFrozenNatCoefficient]

@[simp] theorem smoothAFEZetaSquareDualFrozenNatCoefficient_succ
    (N : ℕ) (center : ℝ) (n : ℕ) :
    smoothAFEZetaSquareDualFrozenNatCoefficient N center (n + 1) =
      ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (linePt center - 1) *
          smoothAFEZetaSquareDualWeight (N : ℝ)
            ((n + 1 : ℝ) * (N : ℝ)) := by
  simp [smoothAFEZetaSquareDualFrozenNatCoefficient]

theorem norm_smoothAFEZetaSquareDualFrozenNatCoefficient_succ_sq_eq_plainMass
    (N : ℕ) (center : ℝ) (n : ℕ) :
    ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center (n + 1)‖ ^ 2 =
      smoothAFEZetaSquareDualFrozenPlainMass N n := by
  have hx : 0 < (n + 1 : ℝ) := by positivity
  rw [smoothAFEZetaSquareDualFrozenNatCoefficient_succ,
    norm_mul, norm_mul, Complex.norm_natCast,
    norm_natSucc_cpow_linePt_sub_one_dualMass]
  unfold smoothAFEZetaSquareDualFrozenPlainMass
    smoothAFEZetaSquareDualFrozenWeightedMass
  have hpow : ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 =
      1 / (n + 1 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hx.le]
    rw [show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num]
    rw [Real.rpow_neg_one]
    exact inv_eq_one_div _
  rw [mul_pow, mul_pow, hpow]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem natSucc_mul_norm_smoothAFEZetaSquareDualFrozenNatCoefficient_sq_eq_weightedMass
    (N : ℕ) (center : ℝ) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) *
        ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center (n + 1)‖ ^ 2 =
      smoothAFEZetaSquareDualFrozenWeightedMass N n := by
  rw [norm_smoothAFEZetaSquareDualFrozenNatCoefficient_succ_sq_eq_plainMass]
  unfold smoothAFEZetaSquareDualFrozenPlainMass
  have hx : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hx]

private theorem summable_norm_smoothAFEZetaSquareDualFrozenNatCoefficient
    {N : ℕ} (hN : 4 ≤ N) (center : ℝ) :
    Summable (fun k : ℕ =>
      ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center k‖) := by
  obtain ⟨K, hK, hweight⟩ :=
    exists_norm_smoothAFEZetaSquareDualWeight_le_invScale
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let A : ℝ := K * (1 + (N : ℝ)) ^ 2 / (N : ℝ)
  have hbase := summable_card_divisors_div_natSucc_rpow_three_halves
  have hsucc : Summable (fun n : ℕ =>
      ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center (n + 1)‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (hbase.mul_left A)
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hY : 0 < (n + 1 : ℝ) * (N : ℝ) := mul_pos hn hNpos
    have hw0 := hweight (N : ℝ) hY
    have hw : ‖smoothAFEZetaSquareDualWeight (N : ℝ)
        ((n + 1 : ℝ) * (N : ℝ))‖ ≤
        K * (1 + (N : ℝ)) ^ 2 / ((n + 1 : ℝ) * (N : ℝ)) := by
      simpa [abs_of_pos hNpos] using hw0
    rw [smoothAFEZetaSquareDualFrozenNatCoefficient_succ,
      norm_mul, norm_mul, Complex.norm_natCast,
      norm_natSucc_cpow_linePt_sub_one_dualMass]
    calc
      ((n + 1).divisors.card : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            ‖smoothAFEZetaSquareDualWeight (N : ℝ)
              ((n + 1 : ℝ) * (N : ℝ))‖ ≤
        ((n + 1).divisors.card : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            (K * (1 + (N : ℝ)) ^ 2 /
              ((n + 1 : ℝ) * (N : ℝ))) := by gcongr
      _ = A * (((n + 1).divisors.card : ℝ) /
          (n + 1 : ℝ) ^ (3 / 2 : ℝ)) := by
        dsimp only [A]
        have hp : (n + 1 : ℝ) ^ (3 / 2 : ℝ) =
            (n + 1 : ℝ) ^ (1 / 2 : ℝ) * (n + 1 : ℝ) := by
          rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring,
            Real.rpow_add hn, Real.rpow_one]
        rw [Real.rpow_neg hn.le, hp]
        field_simp [hn.ne', hNpos.ne']
  apply (summable_nat_add_iff (f := fun k : ℕ =>
    ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center k‖) 1).mp
  simpa using hsucc

private theorem summable_smoothAFEZetaSquareDualFrozenMasses
    {N : ℕ} (hN : 4 ≤ N) :
    Summable (smoothAFEZetaSquareDualFrozenPlainMass N) ∧
      Summable (smoothAFEZetaSquareDualFrozenWeightedMass N) := by
  obtain ⟨K, hK, hhigh⟩ :=
    exists_norm_smoothAFEZetaSquareDualWeight_frozen_high_le
  have hbaseSq : Summable (fun k : ℕ =>
      (((k + 1).divisors.card : ℝ) ^ 2) /
        ((k + 1 : ℕ) : ℝ) ^ 2) := by
    apply (RHTower.Sieve.summable_divisorSquare_div_sq.comp_injective
      Nat.succ_injective).congr
    intro k
    norm_cast
  have hbaseCube : Summable (fun k : ℕ =>
      (((k + 1).divisors.card : ℝ) ^ 2) /
        ((k + 1 : ℕ) : ℝ) ^ 3) := by
    apply (RHTower.Sieve.summable_divisorSquare_div_cube.comp_injective
      Nat.succ_injective).congr
    intro k
    norm_cast
  have hW : Summable (smoothAFEZetaSquareDualFrozenWeightedMass N) := by
    refine Summable.of_nonneg_of_le
      (fun k => by unfold smoothAFEZetaSquareDualFrozenWeightedMass; positivity)
      (fun k => ?_)
      (hbaseSq.mul_left (16 * K ^ 2 * (N : ℝ) ^ 2))
    have hw := hhigh hN (show 1 ≤ k + 1 by omega)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hw 2
    unfold smoothAFEZetaSquareDualFrozenWeightedMass
    calc
      (((k + 1).divisors.card : ℝ) ^ 2) *
          ‖smoothAFEZetaSquareDualWeight (N : ℝ)
            (((k + 1 : ℕ) : ℝ) * (N : ℝ))‖ ^ 2 ≤
        (((k + 1).divisors.card : ℝ) ^ 2) *
          (4 * K * (N : ℝ) / ((k + 1 : ℕ) : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (16 * K ^ 2 * (N : ℝ) ^ 2) *
          ((((k + 1).divisors.card : ℝ) ^ 2) /
            ((k + 1 : ℕ) : ℝ) ^ 2) := by ring
  have hP : Summable (smoothAFEZetaSquareDualFrozenPlainMass N) := by
    refine Summable.of_nonneg_of_le
      (fun k => by
        unfold smoothAFEZetaSquareDualFrozenPlainMass
          smoothAFEZetaSquareDualFrozenWeightedMass
        positivity)
      (fun k => ?_)
      (hbaseCube.mul_left (16 * K ^ 2 * (N : ℝ) ^ 2))
    have hw := hhigh hN (show 1 ≤ k + 1 by omega)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hw 2
    unfold smoothAFEZetaSquareDualFrozenPlainMass
      smoothAFEZetaSquareDualFrozenWeightedMass
    calc
      ((((k + 1).divisors.card : ℝ) ^ 2) *
          ‖smoothAFEZetaSquareDualWeight (N : ℝ)
            (((k + 1 : ℕ) : ℝ) * (N : ℝ))‖ ^ 2) /
          ((k + 1 : ℕ) : ℝ) ≤
        ((((k + 1).divisors.card : ℝ) ^ 2) *
          (4 * K * (N : ℝ) / ((k + 1 : ℕ) : ℝ)) ^ 2) /
          ((k + 1 : ℕ) : ℝ) := by gcongr
      _ = (16 * K ^ 2 * (N : ℝ) ^ 2) *
          ((((k + 1).divisors.card : ℝ) ^ 2) /
            ((k + 1 : ℕ) : ℝ) ^ 3) := by ring
  exact ⟨hP, hW⟩

theorem summable_smoothAFEZetaSquareDualFrozenNatCoefficient_affine_masses
    {N : ℕ} (hN : 4 ≤ N) (center : ℝ) :
    Summable (fun k : ℕ =>
      ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center k‖) ∧
    Summable (fun k : ℕ =>
      ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center k‖ ^ 2) ∧
    Summable (fun k : ℕ => (k : ℝ) *
      ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center k‖ ^ 2) := by
  obtain ⟨hP, hW⟩ := summable_smoothAFEZetaSquareDualFrozenMasses hN
  constructor
  · exact summable_norm_smoothAFEZetaSquareDualFrozenNatCoefficient hN center
  constructor
  · apply (summable_nat_add_iff (f := fun k : ℕ =>
      ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center k‖ ^ 2) 1).mp
    exact hP.congr (fun n =>
      (norm_smoothAFEZetaSquareDualFrozenNatCoefficient_succ_sq_eq_plainMass
        N center n).symm)
  · apply (summable_nat_add_iff (f := fun k : ℕ => (k : ℝ) *
      ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center k‖ ^ 2) 1).mp
    exact hW.congr (fun n =>
      (natSucc_mul_norm_smoothAFEZetaSquareDualFrozenNatCoefficient_sq_eq_weightedMass
        N center n).symm)

theorem tsum_norm_smoothAFEZetaSquareDualFrozenNatCoefficient_sq_eq_plainMass
    {N : ℕ} (hN : 4 ≤ N) (center : ℝ) :
    (∑' k : ℕ,
      ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center k‖ ^ 2) =
      ∑' n : ℕ, smoothAFEZetaSquareDualFrozenPlainMass N n := by
  have hsum :=
    (summable_smoothAFEZetaSquareDualFrozenNatCoefficient_affine_masses hN center).2.1
  have hsplit := hsum.sum_add_tsum_nat_add 1
  calc
    (∑' k : ℕ,
      ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center k‖ ^ 2) =
        ∑' n : ℕ,
          ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center (n + 1)‖ ^ 2 := by
      rw [← hsplit]
      simp
    _ = ∑' n : ℕ, smoothAFEZetaSquareDualFrozenPlainMass N n := by
      apply tsum_congr
      intro n
      exact norm_smoothAFEZetaSquareDualFrozenNatCoefficient_succ_sq_eq_plainMass
        N center n

theorem tsum_weighted_norm_smoothAFEZetaSquareDualFrozenNatCoefficient_sq_eq_weightedMass
    {N : ℕ} (hN : 4 ≤ N) (center : ℝ) :
    (∑' k : ℕ, (k : ℝ) *
      ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center k‖ ^ 2) =
      ∑' n : ℕ, smoothAFEZetaSquareDualFrozenWeightedMass N n := by
  have hsum :=
    (summable_smoothAFEZetaSquareDualFrozenNatCoefficient_affine_masses hN center).2.2
  have hsplit := hsum.sum_add_tsum_nat_add 1
  calc
    (∑' k : ℕ, (k : ℝ) *
      ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center k‖ ^ 2) =
        ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) *
          ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center (n + 1)‖ ^ 2 := by
      rw [← hsplit]
      simp
    _ = ∑' n : ℕ, smoothAFEZetaSquareDualFrozenWeightedMass N n := by
      apply tsum_congr
      intro n
      exact natSucc_mul_norm_smoothAFEZetaSquareDualFrozenNatCoefficient_sq_eq_weightedMass
        N center n

/-- Infinite affine mean square for the frozen square-dual source. -/
theorem exists_integral_normSq_smoothAFEZetaSquareDualFrozenLSeries_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N : ℕ} {center H : ℝ},
      4 ≤ N → 1 ≤ H →
      (∫ y in Set.Icc (-H) H,
        ‖LSeries (smoothAFEZetaSquareDualFrozenNatCoefficient N center)
          ((y : ℝ) * I)‖ ^ 2) ≤
        5 * Real.pi * Real.exp 1 *
            (B * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3) +
          (5 * Real.pi / 2) *
            (B * (1 + Real.log (N : ℝ)) ^ 4) * H := by
  obtain ⟨B, hB, hmass⟩ := exists_tsum_smoothAFEZetaSquareDualFrozenMasses_le
  refine ⟨B, hB, ?_⟩
  intro N center H hN hH
  obtain ⟨habs, hplain, hweighted⟩ :=
    summable_smoothAFEZetaSquareDualFrozenNatCoefficient_affine_masses hN center
  have hmv :=
    RHTower.Sieve.integral_Icc_normSq_LSeries_le_general_affine_infinite
      (a := smoothAFEZetaSquareDualFrozenNatCoefficient N center)
      (smoothAFEZetaSquareDualFrozenNatCoefficient_zero N center) 0
      (by simpa using habs) (by simpa using hplain) (by simpa using hweighted) hH
  have hmv' :
      (∫ y in Set.Icc (-H) H,
        ‖LSeries (smoothAFEZetaSquareDualFrozenNatCoefficient N center)
          ((y : ℝ) * I)‖ ^ 2) ≤
        5 * Real.pi * Real.exp 1 *
          (∑' k : ℕ, (k : ℝ) *
            ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center k‖ ^ 2) +
        (5 * Real.pi / 2) *
          (∑' k : ℕ,
            ‖smoothAFEZetaSquareDualFrozenNatCoefficient N center k‖ ^ 2) * H := by
    simpa using hmv
  obtain ⟨hweightedMass, hplainMass⟩ := hmass hN
  rw [tsum_norm_smoothAFEZetaSquareDualFrozenNatCoefficient_sq_eq_plainMass hN center,
    tsum_weighted_norm_smoothAFEZetaSquareDualFrozenNatCoefficient_sq_eq_weightedMass hN center]
    at hmv'
  exact hmv'.trans (by gcongr)

private theorem smoothAFEZetaSquareDualFrozenLSeries_term_succ
    (N : ℕ) (center y : ℝ) (n : ℕ) :
    LSeries.term (smoothAFEZetaSquareDualFrozenNatCoefficient N center)
        ((y : ℝ) * I) (n + 1) =
      ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (linePt (center - y) - 1) *
          smoothAFEZetaSquareDualWeight (N : ℝ)
            ((n + 1 : ℝ) * (N : ℝ)) := by
  have hn : (n + 1 : ℕ) ≠ 0 := by omega
  have hnC : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn,
    smoothAFEZetaSquareDualFrozenNatCoefficient_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  have hphase :
      (n + 1 : ℂ) ^ (linePt center - 1) /
          (n + 1 : ℂ) ^ ((y : ℝ) * I) =
        (n + 1 : ℂ) ^ (linePt (center - y) - 1) := by
    rw [← Complex.cpow_sub _ _ hnC]
    congr 1
    simp only [linePt]
    push_cast
    ring
  calc
    (((n + 1).divisors.card : ℂ) *
          (n + 1 : ℂ) ^ (linePt center - 1) *
            smoothAFEZetaSquareDualWeight (N : ℝ)
              ((n + 1 : ℝ) * (N : ℝ))) /
        (n + 1 : ℂ) ^ ((y : ℝ) * I) =
      ((n + 1).divisors.card : ℂ) *
        ((n + 1 : ℂ) ^ (linePt center - 1) /
          (n + 1 : ℂ) ^ ((y : ℝ) * I)) *
          smoothAFEZetaSquareDualWeight (N : ℝ)
            ((n + 1 : ℝ) * (N : ℝ)) := by ring
    _ = ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (linePt (center - y) - 1) *
          smoothAFEZetaSquareDualWeight (N : ℝ)
            ((n + 1 : ℝ) * (N : ℝ)) := by rw [hphase]

theorem smoothAFEZetaSquareDualFrozenLSeries_eq_sourceField
    {N : ℕ} (hN : 4 ≤ N) (center y : ℝ) :
    LSeries (smoothAFEZetaSquareDualFrozenNatCoefficient N center)
        ((y : ℝ) * I) =
      smoothAFEZetaSquareDualSourceField (N : ℝ) (N : ℝ) (center - y) := by
  let a : ℕ → ℂ := smoothAFEZetaSquareDualFrozenNatCoefficient N center
  let s : ℂ := (y : ℝ) * I
  have habs : Summable (fun k : ℕ => ‖a k‖) :=
    (summable_smoothAFEZetaSquareDualFrozenNatCoefficient_affine_masses hN center).1
  have hterm : Summable (fun k : ℕ => LSeries.term a s k) := by
    rw [← summable_norm_iff]
    refine habs.congr (fun k => ?_)
    rw [LSeries.norm_term_eq]
    by_cases hk : k = 0
    · simp [hk, a]
    · simp [hk, s]
  have hsplit := hterm.sum_add_tsum_nat_add 1
  calc
    LSeries (smoothAFEZetaSquareDualFrozenNatCoefficient N center)
        ((y : ℝ) * I) = ∑' k : ℕ, LSeries.term a s k := by rfl
    _ = ∑' n : ℕ, LSeries.term a s (n + 1) := by
      rw [← hsplit]
      simp [a, s]
    _ = ∑' n : ℕ, ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (linePt (center - y) - 1) *
          smoothAFEZetaSquareDualWeight (N : ℝ)
            ((n + 1 : ℝ) * (N : ℝ)) := by
      apply tsum_congr
      intro n
      exact smoothAFEZetaSquareDualFrozenLSeries_term_succ N center y n
    _ = smoothAFEZetaSquareDualSourceField
        (N : ℝ) (N : ℝ) (center - y) := rfl

theorem exists_integral_normSq_smoothAFEZetaSquareDualFrozenSourceField_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N : ℕ} {center H : ℝ},
      4 ≤ N → 1 ≤ H →
      (∫ t in Set.Icc (center - H) (center + H),
        ‖smoothAFEZetaSquareDualSourceField
          (N : ℝ) (N : ℝ) t‖ ^ 2) ≤
        5 * Real.pi * Real.exp 1 *
            (B * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3) +
          (5 * Real.pi / 2) *
            (B * (1 + Real.log (N : ℝ)) ^ 4) * H := by
  obtain ⟨B, hB, hmv⟩ := exists_integral_normSq_smoothAFEZetaSquareDualFrozenLSeries_le
  refine ⟨B, hB, ?_⟩
  intro N center H hN hH
  have hbound := hmv (center := center) hN hH
  have heq : (fun y : ℝ =>
      ‖LSeries (smoothAFEZetaSquareDualFrozenNatCoefficient N center)
        ((y : ℝ) * I)‖ ^ 2) =
      (fun y : ℝ => ‖smoothAFEZetaSquareDualSourceField
        (N : ℝ) (N : ℝ) (center - y)‖ ^ 2) := by
    funext y
    rw [smoothAFEZetaSquareDualFrozenLSeries_eq_sourceField hN]
  rw [heq] at hbound
  have hleft : center - H ≤ center + H := by linarith
  have hreflect :
      (∫ y in Set.Icc (-H) H,
        ‖smoothAFEZetaSquareDualSourceField
          (N : ℝ) (N : ℝ) (center - y)‖ ^ 2) =
      ∫ t in Set.Icc (center - H) (center + H),
        ‖smoothAFEZetaSquareDualSourceField
          (N : ℝ) (N : ℝ) t‖ ^ 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -H ≤ H)]
    rw [intervalIntegral.integral_comp_sub_left
      (fun t : ℝ => ‖smoothAFEZetaSquareDualSourceField
        (N : ℝ) (N : ℝ) t‖ ^ 2) center]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hleft]
    congr 1
    all_goals ring
  rw [← hreflect]
  exact hbound

end RHTower
