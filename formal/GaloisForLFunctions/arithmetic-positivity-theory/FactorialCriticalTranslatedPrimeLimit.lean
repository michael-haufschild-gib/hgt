import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeAdmission
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalTranslatedCorrelationLimit

/-! Complete prime limits of translated finite factorial patterns.
The reciprocal and direct scale moments give a uniform actual-source majorant;
complete-prime dominated convergence then retains every prime power and harmonic. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- A complete-prime majorant depending on the fixed pattern, not its translation. -/
def factorialCriticalTranslatedPrimeConstant (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  12 * (∑ j ∈ S, |b j|) *
    (8 * (∑ j ∈ S, |b j|) + 14 * ∑ j ∈ S, ((j+1 : ℕ) : ℝ) * |b j|)

/-- The reciprocal scale moment cancels growth of the direct scale moment. -/
theorem criticalFactorialPrimeConstant_translated_le (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) :
    criticalFactorialPrimeConstant (S.image (fun j => n+j)) (fun q => b (q-n)) ≤
      factorialCriticalTranslatedPrimeConstant S b := by
  classical
  let N : ℝ := ((n+1 : ℕ) : ℝ)
  let B : ℝ := ∑ j ∈ S, |b j|
  let W : ℝ := ∑ j ∈ S, ((j+1 : ℕ) : ℝ) * |b j|
  let D : ℝ := ∑ j ∈ S, |b j| / ((n+j+1 : ℕ) : ℝ)
  let M : ℝ := ∑ j ∈ S, ((n+j+1 : ℕ) : ℝ) * |b j|
  have hN : 0 < N := by dsimp only [N]; positivity
  have hN1 : 1 ≤ N := by dsimp only [N]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hD : D ≤ B/N := by
    dsimp only [D, B]
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro j hj
    have hjN : N ≤ ((n+j+1 : ℕ) : ℝ) := by
      dsimp only [N]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) j]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < ((n+j+1 : ℕ) : ℝ)) hN).mpr
    exact mul_le_mul_of_nonneg_left hjN (abs_nonneg _)
  have hMle : M ≤ N*W := by
    dsimp only [M, W]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjN : ((n+j+1 : ℕ) : ℝ) ≤ N * ((j+1 : ℕ) : ℝ) := by
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have heq : ((n+j+1 : ℕ) : ℝ) = N + (j : ℝ) := by dsimp only [N]; push_cast; ring
      rw [heq]
      push_cast
      nlinarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hjN (abs_nonneg (b j))
  have hL : 8*B + 14*M ≤ N*(8*B+14*W) := by
    have hBN : B ≤ N*B := by nlinarith
    nlinarith
  have himage (f : ℕ → ℝ → ℝ) :
      (∑ q ∈ S.image (fun j => n+j), f q (b (q-n))) = ∑ j ∈ S, f (n+j) (b j) := by
    rw [Finset.sum_image]
    · simp only [Nat.add_sub_cancel_left]
    · intro i hi j hj hij
      exact Nat.add_left_cancel hij
  unfold criticalFactorialPrimeConstant
  rw [himage (fun q x => |x| / ((q+1 : ℕ) : ℝ)), himage (fun _ x => |x|),
    himage (fun q x => ((q+1 : ℕ) : ℝ) * |x|)]
  change (12*D)*(8*B+14*M) ≤ 12*B*(8*B+14*W)
  calc (12*D)*(8*B+14*M) ≤ (12*(B/N))*(N*(8*B+14*W)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hD (by norm_num)) hL
        (by positivity) (by positivity)
    _ = 12*B*(8*B+14*W) := by field_simp [ne_of_gt hN]


/-- The actual finite pattern gains a dilation power uniformly in its translation. -/
theorem factorialCriticalTranslatedCorrelation_bound
    (S : Finset ℕ) (b : ℕ → ℝ) (n r : ℕ) (hr : 0 < r) :
    |factorialCriticalTranslatedCorrelation S b n r| ≤
      factorialCriticalTranslatedPrimeConstant S b / (r : ℝ) := by
  have h := critical_factorial_physical_correlation_bound
    (S.image (fun j => n+j)) (fun q => b (q-n)) (r-1)
  rw [Nat.sub_add_cancel (show 1 ≤ r by omega)] at h
  exact h.trans (div_le_div_of_nonneg_right
    (criticalFactorialPrimeConstant_translated_le S b n) (Nat.cast_nonneg r))

private def translatedPrimePhysicalAtom (S : Finset ℕ) (b : ℕ → ℝ) (n r : ℕ) : ℝ :=
  if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
    factorialCriticalTranslatedCorrelation S b n r else 0

private def translatedPrimeAtom (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) : ℝ :=
  if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
    factorialCriticalTranslatedCorrelationLimit S b r else 0

private theorem translated_prime_atom_tendsto (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) :
    Tendsto (fun n => translatedPrimePhysicalAtom S b n r) atTop
      (𝓝 (translatedPrimeAtom S b r)) := by
  by_cases hr : 2 ≤ r
  · simpa only [translatedPrimePhysicalAtom, translatedPrimeAtom, if_pos hr] using
      (factorialCriticalTranslatedCorrelation_tendsto S b r (by omega)).const_mul
        ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ))
  · simp only [translatedPrimePhysicalAtom, translatedPrimeAtom, if_neg hr]
    exact tendsto_const_nhds

private theorem translated_prime_atom_bound (S : Finset ℕ) (b : ℕ → ℝ) (n r : ℕ) :
    ‖translatedPrimePhysicalAtom S b n r‖ ≤
      factorialCriticalTranslatedPrimeConstant S b * envelopePrimeMajorant (3 / 2) r := by
  by_cases hr : 2 ≤ r
  · have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hc := factorialCriticalTranslatedCorrelation_bound S b n r (by omega)
    simp only [translatedPrimePhysicalAtom, envelopePrimeMajorant, if_pos hr,
      show (3 / 2 : ℝ) + 1 / 2 = 2 by norm_num, Real.rpow_two,
      norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hrp.le)]
    calc (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
          |factorialCriticalTranslatedCorrelation S b n r|
        ≤ (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
          (factorialCriticalTranslatedPrimeConstant S b / (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hc
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hrp.le)
      _ = factorialCriticalTranslatedPrimeConstant S b *
          ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ 2) := by ring
  · simp [translatedPrimePhysicalAtom, envelopePrimeMajorant, hr]

/-- The complete logarithmic prime channel of the actual translated finite pattern. -/
def factorialCriticalTranslatedPrimeEnergy (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' r : ℕ, (if 2 ≤ r then
    (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ) else 0) *
      ∫ x : ℝ, criticalFactorialSource (S.image (fun j => n+j)) (fun q => b (q-n)) x *
        criticalFactorialSource (S.image (fun j => n+j)) (fun q => b (q-n)) (x - Real.log (r : ℝ))

/-- The limiting pattern prime channel retains every prime power and harmonic. -/
def factorialCriticalTranslatedPrimeLimit (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑' r : ℕ, if 2 ≤ r then (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
    factorialCriticalTranslatedCorrelationLimit S b r else 0

private theorem translated_prime_energy_eq (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) :
    factorialCriticalTranslatedPrimeEnergy S b n = ∑' r, translatedPrimePhysicalAtom S b n r := by
  unfold factorialCriticalTranslatedPrimeEnergy
  apply tsum_congr
  intro r
  by_cases hr : 2 ≤ r
  · have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    have hs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrp
    have hc : (∫ x : ℝ,
        criticalFactorialSource (S.image (fun j => n+j)) (fun q => b (q-n)) x *
        criticalFactorialSource (S.image (fun j => n+j)) (fun q => b (q-n)) (x - Real.log (r : ℝ))) =
        (Real.sqrt (r : ℝ))⁻¹ * factorialCriticalTranslatedCorrelation S b n r :=
      criticalFactorialSource_correlation_eq _ _ hr1
    simp only [translatedPrimePhysicalAtom, if_pos hr]
    rw [hc]
    have hfac : ((ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt (r : ℝ)) *
        (Real.sqrt (r : ℝ))⁻¹ = (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) := by
      have hsq := Real.sq_sqrt hrp.le
      field_simp [ne_of_gt hs, ne_of_gt hrp]
      linear_combination -((ArithmeticFunction.vonMangoldt r : ℝ)) * hsq
    rw [← mul_assoc, hfac]
  · simp [translatedPrimePhysicalAtom, hr]

/-- Absolute convergence of the complete limiting pattern prime channel. -/
theorem summable_factorialCriticalTranslatedPrimeLimit_atoms (S : Finset ℕ) (b : ℕ → ℝ) :
    Summable (fun r : ℕ => |if 2 ≤ r then
      (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
        factorialCriticalTranslatedCorrelationLimit S b r else 0|) := by
  have hbound (r : ℕ) : ‖translatedPrimeAtom S b r‖ ≤
      factorialCriticalTranslatedPrimeConstant S b * envelopePrimeMajorant (3 / 2) r :=
    le_of_tendsto (translated_prime_atom_tendsto S b r).norm
      (Eventually.of_forall fun n => translated_prime_atom_bound S b n r)
  have h : Summable (fun r => ‖translatedPrimeAtom S b r‖) :=
    (summable_canonicalPrimeMajorant.mul_left (factorialCriticalTranslatedPrimeConstant S b)).of_nonneg_of_le
      (fun _ => norm_nonneg _) hbound
  simpa only [translatedPrimeAtom, Real.norm_eq_abs] using h

/-- The actual complete prime channel converges for every fixed finite real pattern. -/
theorem factorialCriticalTranslatedPrimeEnergy_tendsto (S : Finset ℕ) (b : ℕ → ℝ) :
    Tendsto (factorialCriticalTranslatedPrimeEnergy S b) atTop
      (𝓝 (factorialCriticalTranslatedPrimeLimit S b)) := by
  have h := tendsto_tsum_of_dominated_convergence
    (summable_canonicalPrimeMajorant.mul_left (factorialCriticalTranslatedPrimeConstant S b))
    (translated_prime_atom_tendsto S b)
    (Eventually.of_forall fun n r => translated_prime_atom_bound S b n r)
  change Tendsto (fun n => ∑' r, translatedPrimePhysicalAtom S b n r) atTop
    (𝓝 (factorialCriticalTranslatedPrimeLimit S b)) at h
  exact h.congr (fun n => (translated_prime_energy_eq S b n).symm)

end GaloisForLFunctions.ArithmeticPositivityTheory
