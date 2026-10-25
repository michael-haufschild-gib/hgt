import GaloisForLFunctions.BezoutValuationIncidence.TheCentredVaughanPoleHasPositiveFiniteEnergy
import GaloisForLFunctions.RHTower.PrimeWinningFaceAugmentation
import Mathlib.Data.Matrix.Basic

/-!
Two finite Euler factors separate the actual centered prefix from the pole
correction on their first two cells. This determinant certifies independence
of the limiting rows and supplies the shared actual infinite Vaughan Gram.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- A finite set of Euler factors bounds the positive reciprocal density from above. -/
theorem pmPowerDampedDivisorDensity_re_le_prime_product {ε : ℝ} (hε : 0 < ε)
    (S : Finset Nat.Primes) :
    (pmPowerDampedDivisorDensity ε).re ≤
      ∏ p ∈ S, (1 - ((p : ℕ) : ℝ) ^ (-(1 + ε))) := by
  classical
  let f : Nat.Primes → ℝ := fun p => 1 - ((p : ℕ) : ℝ) ^ (-(1 + ε))
  have hf (p : Nat.Primes) : 0 ≤ f p ∧ f p ≤ 1 := by
    have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.property.one_lt.le
    exact ⟨sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos hp1
      (by linarith only [hε])), sub_le_self _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)⟩
  have hprod := hasProd_one_sub_primeCpow_neg
    (w := 1 + (ε : ℂ)) (by simpa only [Complex.add_re, Complex.one_re, Complex.ofReal_re] using
      (by linarith only [hε] : (1 : ℝ) < 1 + ε))
  change Tendsto (fun F : Finset Nat.Primes =>
    ∏ p ∈ F, (1 - ((p : ℕ) : ℂ) ^ (-(1 + (ε : ℂ))))) atTop
      (𝓝 (riemannZeta (1 + (ε : ℂ)))⁻¹) at hprod
  have heq (F : Finset Nat.Primes) :
      (∏ p ∈ F, (1 - ((p : ℕ) : ℂ) ^ (-(1 + (ε : ℂ))))) = ((∏ p ∈ F, f p : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    apply prod_congr rfl
    intro p _
    dsimp only [f]
    rw [Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ))]
    push_cast
    rfl
  have hlim : Tendsto (fun F : Finset Nat.Primes => ∏ p ∈ F, f p) atTop
      (𝓝 (pmPowerDampedDivisorDensity ε).re) := by
    have h := (Complex.continuous_re.tendsto _).comp hprod
    simpa only [Function.comp_def, heq, Complex.ofReal_re,
      pmPowerDampedDivisorDensity, one_div] using h
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop S] with F hSF
  rw [← prod_sdiff hSF]
  exact (mul_le_mul_of_nonneg_right
    (prod_le_one (fun p _ => (hf p).1) (fun p _ => (hf p).2))
    (prod_nonneg fun p _ => (hf p).1)).trans_eq (one_mul _)

/-- The first two prime factors suffice for a strict two-cell separation estimate. -/
theorem pmPowerDampedDivisorDensity_re_le_two_three {ε : ℝ} (hε : 0 < ε) :
    (pmPowerDampedDivisorDensity ε).re ≤
      (1 - (2 : ℝ) ^ (-ε) / 2) * (1 - (3 : ℝ) ^ (-ε) / 3) := by
  let p₂ : Nat.Primes := ⟨2, Nat.prime_two⟩
  let p₃ : Nat.Primes := ⟨3, by norm_num⟩
  have hp : p₂ ≠ p₃ := by intro h; have := congrArg Subtype.val h; norm_num [p₂, p₃] at this
  have hmem : p₂ ∉ ({p₃} : Finset Nat.Primes) := by
    simpa only [mem_singleton] using hp
  have h := pmPowerDampedDivisorDensity_re_le_prime_product hε {p₂, p₃}
  rw [prod_insert hmem, prod_singleton] at h
  change (pmPowerDampedDivisorDensity ε).re ≤
    (1 - (2 : ℝ) ^ (-(1 + ε))) * (1 - (3 : ℝ) ^ (-(1 + ε))) at h
  rw [show -(1 + ε) = -ε - 1 by ring,
    Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0),
    Real.rpow_sub_one (by norm_num : (3 : ℝ) ≠ 0)] at h
  exact h

/-- At a prime, the active correction is one half of the missing reciprocal local factor. -/
theorem pmActiveSawtoothComponent_prime (ε : ℝ) {p : ℕ} (hp : p.Prime) :
    pmActiveSawtoothComponent ε p =
      (1 / 2 : ℝ) * (p : ℝ) ^ (-ε) * (1 - 1 / (p : ℝ)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [pmActiveSawtoothComponent, pmPowerDampedDivisorCoeff_prime ε hp,
    pmPowerDampedDivisorCoeff_prime (1 + ε) hp,
    show -(1 + ε) = -ε - 1 by ring, Real.rpow_sub_one hp0]
  ring

/-- The second centered-prefix cell uses only the coefficient at prime two. -/
theorem pmPowerDampedCenteredDivisorPrefix_two (ε : ℝ) :
    pmPowerDampedCenteredDivisorPrefix ε 2 =
      2 - (2 : ℝ) ^ (-ε) - 2 * (pmPowerDampedDivisorDensity ε).re := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pmPowerDampedCenteredDivisorPrefix_succ,
    pmPowerDampedCenteredDivisorPrefix_one]
  simp only [pmPowerDampedCenteredDivisorCoeff, pmPowerDampedDivisorCoeff_one,
    show (1 : ℕ) + 1 = 2 from rfl, pmPowerDampedDivisorCoeff_prime ε Nat.prime_two]
  norm_num only [Nat.cast_ofNat]
  ring

/-- The second active increment compares the local factors at primes two and three. -/
theorem addDiff_pmActiveSawtoothComponent_two (ε : ℝ) :
    addDiff (pmActiveSawtoothComponent ε) 2 =
      (3 : ℝ) ^ (-ε) / 3 - (2 : ℝ) ^ (-ε) / 4 := by
  rw [addDiff, show (2 : ℕ) + 1 = 3 from rfl,
    pmActiveSawtoothComponent_prime ε (by norm_num : Nat.Prime 3),
    pmActiveSawtoothComponent_prime ε Nat.prime_two]
  norm_num only [Nat.cast_ofNat]
  ring

/-- The actual prefix and centered pole have a uniformly positive first two-cell determinant. -/
theorem pmPowerDampedPrefix_pole_two_cell_determinant_lower {ε : ℝ} (hε : 0 < ε) :
    ((2 : ℝ) ^ (-ε)) ^ 2 / 36 ≤
      pmPowerDampedCenteredDivisorPrefix ε 1 * (-addDiff (pmActiveSawtoothComponent ε) 2) -
        pmPowerDampedCenteredDivisorPrefix ε 2 * (-addDiff (pmActiveSawtoothComponent ε) 1) := by
  let a : ℝ := (2 : ℝ) ^ (-ε)
  let b : ℝ := (3 : ℝ) ^ (-ε)
  let ρ : ℝ := (pmPowerDampedDivisorDensity ε).re
  have ha0 : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hb0 : 0 ≤ b := Real.rpow_nonneg (by norm_num) _
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr hε.le)
  have hba : b ≤ a := Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num) (neg_nonpos.mpr hε.le)
  have hρ : ρ ≤ (1 - a / 2) * (1 - b / 3) := pmPowerDampedDivisorDensity_re_le_two_three hε
  have hc : 0 ≤ 3 * a / 4 - b / 3 := by linarith only [hba, ha0]
  have heuler := mul_le_mul_of_nonneg_right (sub_le_sub_left hρ 1) hc
  have hpositive : 0 ≤ 5 * a ^ 2 * (1 - a) +
      (a - b) * ((8 - 4 * a) * b + 2 * a + 5 * a ^ 2) := by
    have h1 : 0 ≤ 1 - a := sub_nonneg.mpr ha1
    have h2 : 0 ≤ a - b := sub_nonneg.mpr hba
    have h3 : 0 ≤ 8 - 4 * a := by linarith only [ha1]
    positivity
  have hid : 72 * ((1 - (1 - a / 2) * (1 - b / 3)) *
      (3 * a / 4 - b / 3) - a ^ 2 / 4 - a ^ 2 / 36) =
        5 * a ^ 2 * (1 - a) + (a - b) * ((8 - 4 * a) * b + 2 * a + 5 * a ^ 2) := by ring
  have hpoly : a ^ 2 / 36 ≤ (1 - ρ) * (3 * a / 4 - b / 3) - a ^ 2 / 4 := by
    linarith only [heuler, hpositive, hid]
  rw [pmPowerDampedCenteredDivisorPrefix_one, pmPowerDampedCenteredDivisorCoeff,
    pmPowerDampedDivisorCoeff_one, pmPowerDampedCenteredDivisorPrefix_two,
    addDiff_pmActiveSawtoothComponent_one, addDiff_pmActiveSawtoothComponent_two]
  change a ^ 2 / 36 ≤ (1 - ρ) * (-(b / 3 - a / 4)) - (2 - a - 2 * ρ) * (-(a / 4))
  convert hpoly using 1
  ring

/-- No nonzero combination of the actual prefix and centered pole vanishes even on their first two cells. -/
theorem pmPowerDampedPrefix_pole_independent_two_cells {ε x y : ℝ} (hε : 0 < ε)
    (h1 : x * pmPowerDampedCenteredDivisorPrefix ε 1 +
      y * (-addDiff (pmActiveSawtoothComponent ε) 1) = 0)
    (h2 : x * pmPowerDampedCenteredDivisorPrefix ε 2 +
      y * (-addDiff (pmActiveSawtoothComponent ε) 2) = 0) : x = 0 ∧ y = 0 := by
  have hdet : 0 < pmPowerDampedCenteredDivisorPrefix ε 1 *
      (-addDiff (pmActiveSawtoothComponent ε) 2) -
        pmPowerDampedCenteredDivisorPrefix ε 2 * (-addDiff (pmActiveSawtoothComponent ε) 1) :=
    (by positivity : 0 < ((2 : ℝ) ^ (-ε)) ^ 2 / 36).trans_le
      (pmPowerDampedPrefix_pole_two_cell_determinant_lower hε)
  have hxmul : x * (pmPowerDampedCenteredDivisorPrefix ε 1 *
      (-addDiff (pmActiveSawtoothComponent ε) 2) -
        pmPowerDampedCenteredDivisorPrefix ε 2 * (-addDiff (pmActiveSawtoothComponent ε) 1)) = 0 := by
    linear_combination (-addDiff (pmActiveSawtoothComponent ε) 2) * h1 -
      (-addDiff (pmActiveSawtoothComponent ε) 1) * h2
  have hx : x = 0 := (mul_eq_zero.mp hxmul).resolve_right hdet.ne'
  rw [hx, zero_mul, zero_add, addDiff_pmActiveSawtoothComponent_one] at h1
  exact ⟨hx, (mul_eq_zero.mp h1).resolve_right (neg_ne_zero.mpr (by positivity))⟩

private theorem weighted_pair_minor_identity (s : Finset ℕ) (w f g : ℕ → ℝ) :
    (∑ m ∈ s, ∑ n ∈ s, w m * w n * (f m * g n - g m * f n) ^ 2) =
      2 * ((∑ n ∈ s, w n * f n ^ 2) * (∑ n ∈ s, w n * g n ^ 2) -
        (∑ n ∈ s, w n * f n * g n) ^ 2) := by
  calc
    _ = ∑ m ∈ s, ∑ n ∈ s,
        ((w m * f m ^ 2) * (w n * g n ^ 2) +
          (w m * g m ^ 2) * (w n * f n ^ 2) -
            2 * (w m * f m * g m) * (w n * f n * g n)) := by
      apply sum_congr rfl
      intro m _
      apply sum_congr rfl
      intro n _
      ring
    _ = (∑ n ∈ s, w n * f n ^ 2) * (∑ n ∈ s, w n * g n ^ 2) +
        (∑ n ∈ s, w n * g n ^ 2) * (∑ n ∈ s, w n * f n ^ 2) -
          2 * (∑ n ∈ s, w n * f n * g n) * (∑ n ∈ s, w n * f n * g n) := by
      simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← sum_mul]
    _ = _ := by ring

/-- Two positive cells give a lower bound for the full pronic Gram determinant. -/
theorem pronic_gram_determinant_lower_two_cells (f g : ℕ → ℝ) {T : ℕ} (hT : 2 ≤ T) :
    (f 1 * g 2 - g 1 * f 2) ^ 2 / 12 ≤
      (∑ n ∈ Icc 1 T, f n ^ 2 / (pronicSeq n : ℝ)) *
        (∑ n ∈ Icc 1 T, g n ^ 2 / (pronicSeq n : ℝ)) -
          (∑ n ∈ Icc 1 T, f n * g n / (pronicSeq n : ℝ)) ^ 2 := by
  let w : ℕ → ℝ := fun n => 1 / (pronicSeq n : ℝ)
  have hsub : ({1, 2} : Finset ℕ) ⊆ Icc 1 T := by
    intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl <;> simp only [mem_Icc] <;> omega
  have hnonneg (m n : ℕ) : 0 ≤ w m * w n * (f m * g n - g m * f n) ^ 2 := by
    dsimp only [w]
    positivity
  have hrestrict :
      (∑ m ∈ ({1, 2} : Finset ℕ), ∑ n ∈ ({1, 2} : Finset ℕ),
        w m * w n * (f m * g n - g m * f n) ^ 2) ≤
      ∑ m ∈ Icc 1 T, ∑ n ∈ Icc 1 T, w m * w n * (f m * g n - g m * f n) ^ 2 := by
    calc
      _ ≤ ∑ m ∈ ({1, 2} : Finset ℕ), ∑ n ∈ Icc 1 T,
          w m * w n * (f m * g n - g m * f n) ^ 2 :=
        sum_le_sum fun m _ => sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hnonneg m n)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub
        (fun m _ _ => sum_nonneg fun n _ => hnonneg m n)
  have hsmall : (∑ m ∈ ({1, 2} : Finset ℕ), ∑ n ∈ ({1, 2} : Finset ℕ),
      w m * w n * (f m * g n - g m * f n) ^ 2) = (f 1 * g 2 - g 1 * f 2) ^ 2 / 6 := by
    norm_num [w, pronicSeq]
    ring
  have hlarge : (∑ m ∈ Icc 1 T, ∑ n ∈ Icc 1 T,
      w m * w n * (f m * g n - g m * f n) ^ 2) =
      2 * ((∑ n ∈ Icc 1 T, f n ^ 2 / (pronicSeq n : ℝ)) *
        (∑ n ∈ Icc 1 T, g n ^ 2 / (pronicSeq n : ℝ)) -
          (∑ n ∈ Icc 1 T, f n * g n / (pronicSeq n : ℝ)) ^ 2) := by
    simpa only [w, one_div, div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc] using
      weighted_pair_minor_identity (Icc 1 T) w f g
  rw [hsmall, hlarge] at hrestrict
  linarith only [hrestrict]

/-- The prefix-pole Gram has a positive determinant at every horizon containing two cells. -/
theorem pmPowerDampedPrefix_pole_pronic_gram_determinant_lower {ε : ℝ} (hε : 0 < ε)
    {T : ℕ} (hT : 2 ≤ T) :
    ((2 : ℝ) ^ (-ε)) ^ 4 / 15552 ≤
      (∑ n ∈ Icc 1 T, pmPowerDampedCenteredDivisorPrefix ε n ^ 2 / (pronicSeq n : ℝ)) *
        (∑ n ∈ Icc 1 T, (-addDiff (pmActiveSawtoothComponent ε) n) ^ 2 / (pronicSeq n : ℝ)) -
          (∑ n ∈ Icc 1 T, pmPowerDampedCenteredDivisorPrefix ε n *
            (-addDiff (pmActiveSawtoothComponent ε) n) / (pronicSeq n : ℝ)) ^ 2 := by
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ ((2 : ℝ) ^ (-ε)) ^ 2 / 36)
    (pmPowerDampedPrefix_pole_two_cell_determinant_lower hε) 2
  calc
    _ = (((2 : ℝ) ^ (-ε)) ^ 2 / 36) ^ 2 / 12 := by ring
    _ ≤ (pmPowerDampedCenteredDivisorPrefix ε 1 * (-addDiff (pmActiveSawtoothComponent ε) 2) -
        pmPowerDampedCenteredDivisorPrefix ε 2 * (-addDiff (pmActiveSawtoothComponent ε) 1)) ^ 2 / 12 :=
      div_le_div_of_nonneg_right hsquare (by norm_num)
    _ ≤ _ := by
      simpa only [mul_comm] using pronic_gram_determinant_lower_two_cells
        (pmPowerDampedCenteredDivisorPrefix ε) (fun n => -addDiff (pmActiveSawtoothComponent ε) n) hT

/-- The actual centered prefix and centered pole form an independent pair of sequences. -/
theorem pmPowerDampedPrefix_pole_linearIndependent {ε : ℝ} (hε : 0 < ε) :
    LinearIndependent ℝ ![pmPowerDampedCenteredDivisorPrefix ε,
      fun n => -addDiff (pmActiveSawtoothComponent ε) n] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have he (n : ℕ) : c 0 * pmPowerDampedCenteredDivisorPrefix ε n +
      c 1 * (-addDiff (pmActiveSawtoothComponent ε) n) = 0 := by
    have h : (∑ k : Fin 2, c k *
        ![pmPowerDampedCenteredDivisorPrefix ε,
          fun n => -addDiff (pmActiveSawtoothComponent ε) n] k n) = 0 := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
        congrArg (fun f : ℕ → ℝ => f n) hc
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    exact h
  obtain ⟨h0, h1⟩ := pmPowerDampedPrefix_pole_independent_two_cells hε (he 1) (he 2)
  fin_cases i
  · exact h0
  · exact h1

/-- The five rows approached by centered Vaughan pieces when both cutoffs diverge. -/
def pmPronicVaughanLimitFrame (ε : ℝ) : Fin 5 → ℕ → ℝ :=
  ![pmPowerDampedCenteredDivisorPrefix ε, pmPowerDampedCenteredDivisorPrefix ε,
    -pmPowerDampedCenteredDivisorPrefix ε, 0,
    fun n => -addDiff (pmActiveSawtoothComponent ε) n]

/-- The infinite pronic pairings of the five limiting Vaughan rows. -/
def pmPronicVaughanLimitGram (ε : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => ∑' n : ℕ,
    pmPronicVaughanLimitFrame ε i n * pmPronicVaughanLimitFrame ε j n / (pronicSeq n : ℝ)

/-- The five limiting rows span precisely the actual prefix and centered pole. -/
theorem span_pmPronicVaughanLimitFrame (ε : ℝ) :
    Submodule.span ℝ (Set.range (pmPronicVaughanLimitFrame ε)) =
      Submodule.span ℝ (Set.range ![pmPowerDampedCenteredDivisorPrefix ε,
        fun n => -addDiff (pmActiveSawtoothComponent ε) n]) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.subset_span ⟨(0 : Fin 2), rfl⟩
    · exact Submodule.subset_span ⟨(0 : Fin 2), rfl⟩
    · exact Submodule.neg_mem _ (Submodule.subset_span ⟨(0 : Fin 2), rfl⟩)
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨(1 : Fin 2), rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.subset_span ⟨(0 : Fin 5), rfl⟩
    · exact Submodule.subset_span ⟨(4 : Fin 5), rfl⟩

/-- The limiting Vaughan rows have exact dimension two at every positive damping. -/
theorem finrank_span_pmPronicVaughanLimitFrame {ε : ℝ} (hε : 0 < ε) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (pmPronicVaughanLimitFrame ε))) = 2 := by
  rw [span_pmPronicVaughanLimitFrame,
    finrank_span_eq_card (pmPowerDampedPrefix_pole_linearIndependent hε), Fintype.card_fin]

#print axioms pmPowerDampedPrefix_pole_linearIndependent
#print axioms span_pmPronicVaughanLimitFrame
#print axioms finrank_span_pmPronicVaughanLimitFrame
#print axioms pmPowerDampedDivisorDensity_re_le_prime_product
#print axioms pmPowerDampedDivisorDensity_re_le_two_three
#print axioms pmActiveSawtoothComponent_prime
#print axioms pmPowerDampedCenteredDivisorPrefix_two
#print axioms addDiff_pmActiveSawtoothComponent_two
#print axioms pmPowerDampedPrefix_pole_two_cell_determinant_lower
#print axioms pmPowerDampedPrefix_pole_independent_two_cells
#print axioms pronic_gram_determinant_lower_two_cells
#print axioms pmPowerDampedPrefix_pole_pronic_gram_determinant_lower
end GaloisForLFunctions.BezoutValuationIncidence
