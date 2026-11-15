import Mathlib.RingTheory.RootsOfUnity.Complex
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheAverageRowIsBlindToTheTarget

/-!
# A nonprincipal filter recovers the local target

Multiplying the complete sextic row by `ρ(1 − ρY)` removes its geometric
denominator. The result is cubic in `ρ`, with constant coefficient
`−(1 − R)⁻¹ηX`. Averaging over the six phases therefore retains this target
coefficient and cancels all remaining terms, wherever `Y⁶ ≠ 1`.

The filter has exact mean-square cost `1 + ‖Y‖²`; its Cauchy–Schwarz bound is
attained by the conjugate filter. Signed finite row sums can be combined before
extraction, and affine reconstruction recovers finite products of the original
reciprocal Euler factors `1 − ηX`, with their phases intact.
-/

noncomputable section
open Complex Finset
open scoped Classical ComplexConjugate
namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

private theorem sum_sextic_power {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6) {k : ℕ}
    (hk : ¬ 6 ∣ k) : ∑ i ∈ range 6, (ζ ^ i) ^ k = 0 := by
  have hn : ζ ^ k ≠ 1 := fun h => hk ((hζ.pow_eq_one_iff_dvd _).mp h)
  have hp : (ζ ^ k) ^ 6 = 1 := by
    rw [← pow_mul, Nat.mul_comm k 6, pow_mul, hζ.pow_eq_one, one_pow]
  simp_rw [← pow_mul, Nat.mul_comm _ k, pow_mul]
  rw [geom_sum_eq hn, hp, sub_self, zero_div]

/-- Multiplication by `ρ(1 − ρY)` removes the row's geometric denominator and
turns its reciprocal target mode into the constant coefficient. -/
theorem target_weight_rowLocalSum (Q R η X Y V ρ : ℂ) (hρ : ρ ≠ 0)
    (hY : 1 - ρ * Y ≠ 0) :
    ρ * (1 - ρ * Y) * rowLocalSum Q R η X Y V ρ =
      (-(1 - R)⁻¹ * η * X) +
      ((1 - V)⁻¹ + (1 - R)⁻¹ *
        (R * (1 - Q⁻¹) * (1 - V)⁻¹ - η * (Q - 1) * X * Y * V * (1 - V)⁻¹ +
          η * X * Y)) * ρ +
      (Y - Y * (1 - V)⁻¹ + (1 - R)⁻¹ *
        (Y * R - Y * R * (1 - Q⁻¹) * (1 - V)⁻¹ +
          η * (Q - 1) * X * Y ^ 2 * V * (1 - V)⁻¹)) * ρ ^ 2 -
      ((1 - R)⁻¹ * Y ^ 2 * R) * ρ ^ 3 := by
  unfold rowLocalSum
  field_simp [hρ, hY]
  ring

/-- Away from the six geometric poles, the extraction identity holds throughout
the meromorphic continuation domain, including `‖Y‖ ≥ 1`. -/
theorem target_weight_average_rowLocalSum {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (Q R η X Y V : ℂ) (hY : Y ^ 6 ≠ 1) :
    (1 / 6 : ℂ) * ∑ i ∈ range 6,
      ζ ^ i * (1 - ζ ^ i * Y) * rowLocalSum Q R η X Y V (ζ ^ i) =
        -(1 - R)⁻¹ * η * X := by
  have hz : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hy : ∀ i : ℕ, 1 - ζ ^ i * Y ≠ 0 := by
    intro i heq
    have he : ζ ^ i * Y = 1 := (sub_eq_zero.mp heq).symm
    have hh := congrArg (fun z : ℂ => z ^ 6) he
    rw [mul_pow, ← pow_mul, Nat.mul_comm i 6, pow_mul, hζ.pow_eq_one,
      one_pow, one_mul, one_pow] at hh
    exact hY hh
  have hs1 := sum_sextic_power hζ (k := 1) (by norm_num)
  have hs2 := sum_sextic_power hζ (k := 2) (by norm_num)
  have hs3 := sum_sextic_power hζ (k := 3) (by norm_num)
  simp only [pow_one] at hs1
  simp_rw [target_weight_rowLocalSum Q R η X Y V _ (pow_ne_zero _ hz) (hy _)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, hs1, hs2, hs3, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Nat.cast_ofNat, mul_zero, add_zero, sub_zero]
  ring

/-- Removing the completion denominator from the nonprincipal extraction
recovers the original local target coefficient `ηX`. -/
theorem target_extracted_rowLocalSum {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (Q R η X Y V : ℂ) (hY : Y ^ 6 ≠ 1) (hR : 1 - R ≠ 0) :
    -(1 - R) * ((1 / 6 : ℂ) * ∑ i ∈ range 6,
      ζ ^ i * (1 - ζ ^ i * Y) * rowLocalSum Q R η X Y V (ζ ^ i)) = η * X := by
  rw [target_weight_average_rowLocalSum hζ Q R η X Y V hY]
  field_simp

/-- The nonprincipal filter has mean-square cost `1 + ‖Y‖²` exactly. -/
theorem sum_sq_norm_target_weight {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6) (Y : ℂ) :
    ∑ i ∈ range 6, ‖ζ ^ i * (1 - ζ ^ i * Y)‖ ^ 2 = 6 * (1 + ‖Y‖ ^ 2) := by
  have hn : ‖ζ‖ = 1 := hζ.norm'_eq_one (by norm_num)
  have hs : ∑ i ∈ range 6, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by norm_num)
  have hre : ∑ i ∈ range 6, (ζ ^ i * Y).re = 0 := by
    rw [← Complex.re_sum, ← Finset.sum_mul, hs, zero_mul, Complex.zero_re]
  have hw (i : ℕ) : ‖ζ ^ i * (1 - ζ ^ i * Y)‖ ^ 2 =
      1 + ‖Y‖ ^ 2 - 2 * (ζ ^ i * Y).re := by
    rw [norm_mul, norm_pow, hn, one_pow, one_mul, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_sub]
    simp only [Complex.normSq_eq_norm_sq, norm_one, norm_mul, norm_pow, hn,
      one_pow, one_mul, Complex.conj_re]
  simp_rw [hw]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hre]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat,
    mul_zero, sub_zero]

/-- Sextic target extraction is bounded in mean-square norm, with an explicit
constant valid for every complex `Y` and every six-row input. -/
theorem norm_target_extraction_sq_le {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (Y : ℂ) (f : ℕ → ℂ) :
    6 * ‖(1 / 6 : ℂ) * ∑ i ∈ range 6, ζ ^ i * (1 - ζ ^ i * Y) * f i‖ ^ 2 ≤
      (1 + ‖Y‖ ^ 2) * ∑ i ∈ range 6, ‖f i‖ ^ 2 := by
  let w : ℕ → ℂ := fun i => ζ ^ i * (1 - ζ ^ i * Y)
  have hn : ‖∑ i ∈ range 6, w i * f i‖ ≤
      ∑ i ∈ range 6, ‖w i‖ * ‖f i‖ := by
    simpa only [norm_mul] using norm_sum_le (range 6) (fun i => w i * f i)
  have hsq : ‖∑ i ∈ range 6, w i * f i‖ ^ 2 ≤
      6 * (1 + ‖Y‖ ^ 2) * ∑ i ∈ range 6, ‖f i‖ ^ 2 := by
    calc
      _ ≤ (∑ i ∈ range 6, ‖w i‖ * ‖f i‖) ^ 2 := by gcongr
      _ ≤ (∑ i ∈ range 6, ‖w i‖ ^ 2) * ∑ i ∈ range 6, ‖f i‖ ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = _ := by rw [sum_sq_norm_target_weight hζ Y]
  change 6 * ‖(1 / 6 : ℂ) * ∑ i ∈ range 6, w i * f i‖ ^ 2 ≤ _
  rw [norm_mul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  nlinarith only [hsq]

/-- The cost is attained by the conjugate filter, so its uniform mean-square
bound cannot be improved without using additional structure of the rows. -/
theorem target_extraction_conj_weight {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6) (Y : ℂ) :
    (1 / 6 : ℂ) * ∑ i ∈ range 6,
      (ζ ^ i * (1 - ζ ^ i * Y)) * conj (ζ ^ i * (1 - ζ ^ i * Y)) =
      (1 + ‖Y‖ ^ 2 : ℝ) := by
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_sum, sum_sq_norm_target_weight hζ Y]
  push_cast
  ring

/-- The actual local rows obey the target-mode lower energy bound. -/
theorem target_rowLocalSum_energy {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (Q R η X Y V : ℂ) (hY : Y ^ 6 ≠ 1) :
    6 * ‖(1 - R)⁻¹ * η * X‖ ^ 2 ≤
      (1 + ‖Y‖ ^ 2) * ∑ i ∈ range 6, ‖rowLocalSum Q R η X Y V (ζ ^ i)‖ ^ 2 := by
  have h := norm_target_extraction_sq_le hζ Y (fun i => rowLocalSum Q R η X Y V (ζ ^ i))
  rw [target_weight_average_rowLocalSum hζ Q R η X Y V hY] at h
  simpa only [neg_mul, norm_neg] using h

/-- The primitive sixth root with argument `π/3`, used to read the row phases. -/
def targetSixthRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / 6)

private theorem targetSixthRoot_primitive : IsPrimitiveRoot targetSixthRoot 6 :=
  Complex.isPrimitiveRoot_exp 6 (by norm_num)

/-- Nonprincipal extraction of six phase values, normalized as an average. -/
def targetPhaseReadout (Y : ℂ) (f : ℂ → ℂ) : ℂ :=
  (1 / 6 : ℂ) * ∑ i ∈ range 6,
    targetSixthRoot ^ i * (1 - targetSixthRoot ^ i * Y) * f (targetSixthRoot ^ i)

/-- The canonical phase readout recovers the reciprocal target mode of the
complete local series on its geometric pole-free domain. -/
theorem targetPhaseReadout_rowLocalSum (Q R η X Y V : ℂ) (hY : Y ^ 6 ≠ 1) :
    targetPhaseReadout Y (rowLocalSum Q R η X Y V) = -(1 - R)⁻¹ * η * X :=
  target_weight_average_rowLocalSum targetSixthRoot_primitive Q R η X Y V hY

/-- The canonical readout preserves a literal local Euler coefficient once the
completion denominator has been removed. -/
theorem targetPhaseReadout_recovers_target (Q R η X Y V : ℂ)
    (hY : Y ^ 6 ≠ 1) (hR : 1 - R ≠ 0) :
    -(1 - R) * targetPhaseReadout Y (rowLocalSum Q R η X Y V) = η * X :=
  target_extracted_rowLocalSum targetSixthRoot_primitive Q R η X Y V hY hR

/-- Sharp mean-square bound for the fixed phase readout. -/
theorem norm_targetPhaseReadout_sq_le (Y : ℂ) (f : ℂ → ℂ) :
    6 * ‖targetPhaseReadout Y f‖ ^ 2 ≤
      (1 + ‖Y‖ ^ 2) * ∑ i ∈ range 6, ‖f (targetSixthRoot ^ i)‖ ^ 2 :=
  norm_target_extraction_sq_le targetSixthRoot_primitive Y (fun i => f (targetSixthRoot ^ i))

/-- Signed combinations of actual completed rows may be formed before phase
extraction; the output retains the same signed combination of target coefficients. -/
theorem targetPhaseReadout_signed_rows {α : Type*} (s : Finset α)
    (c Q R η X V : α → ℂ) (Y : ℂ) (hY : Y ^ 6 ≠ 1)
    (hR : ∀ a ∈ s, 1 - R a ≠ 0) :
    targetPhaseReadout Y (fun ρ => ∑ a ∈ s,
      -(c a * (1 - R a)) * rowLocalSum (Q a) (R a) (η a) (X a) Y (V a) ρ) =
        ∑ a ∈ s, c a * η a * X a := by
  unfold targetPhaseReadout
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  have he := target_extracted_rowLocalSum targetSixthRoot_primitive
    (Q a) (R a) (η a) (X a) Y (V a) hY (hR a ha)
  calc
    _ = c a * (-(1 - R a) * ((1 / 6 : ℂ) * ∑ i ∈ range 6,
      targetSixthRoot ^ i * (1 - targetSixthRoot ^ i * Y) *
        rowLocalSum (Q a) (R a) (η a) (X a) Y (V a) (targetSixthRoot ^ i))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [he]; ring

/-- Affine reconstruction gives the original local reciprocal Euler factor. -/
theorem targetPhaseReadout_recovers_eulerFactor (Q R η X Y V : ℂ)
    (hY : Y ^ 6 ≠ 1) (hR : 1 - R ≠ 0) :
    1 + (1 - R) * targetPhaseReadout Y (rowLocalSum Q R η X Y V) = 1 - η * X := by
  have h := targetPhaseReadout_recovers_target Q R η X Y V hY hR
  linear_combination -h

/-- Finite products of reconstructed local rows retain every target Euler factor
and its phase. No limiting Euler-product estimate is used. -/
theorem prod_targetPhaseReadout_eulerFactor {α : Type*} (s : Finset α)
    (Q R η X Y V : α → ℂ) (hY : ∀ a ∈ s, Y a ^ 6 ≠ 1)
    (hR : ∀ a ∈ s, 1 - R a ≠ 0) :
    ∏ a ∈ s, (1 + (1 - R a) * targetPhaseReadout (Y a)
      (rowLocalSum (Q a) (R a) (η a) (X a) (Y a) (V a))) =
        ∏ a ∈ s, (1 - η a * X a) := by
  exact Finset.prod_congr rfl fun a ha =>
    targetPhaseReadout_recovers_eulerFactor (Q a) (R a) (η a) (X a) (Y a) (V a)
      (hY a ha) (hR a ha)

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

