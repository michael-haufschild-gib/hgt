import GaloisForLFunctions.RHTower.Sieve.MaynardDerivativeCountDuality
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedPolylogEnergy

/-!
# Literal low-ordinate derivative receiver

The low-ordinate giant seam has one over-height zeta/log atom.  Excising it before Montgomery
leaves an unraised complementary product.  Its exact coefficient energy uses divisor moment
order `2w`, not the raised-factor order `2(w+1)`.  This module proves that sharper energy law,
constructs the nonempty erase-one-factor complement, and composes both with the full `T/C`
Kuzmin--Landau gain on an arbitrary separated finite set.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **Sharp unraised grouped energy.**  A product of `w` literal Heath--Brown blocks has
coefficient square-energy bounded by length times a fixed logarithm of exponent
`2w + 2^(2w) - 1`.  The extra `+1` in the generic raised-factor theorem is absent. -/
theorem sum_normSq_heathBrownGrouped_le_fixed_polylog
    {ι : Type*} [Fintype ι]
    (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ) :
    ∑ j : Fin (groupedDyadicUpper q),
        ‖groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2 ≤
      (groupedDyadicUpper q : ℝ) *
        (1 + Real.log (groupedDyadicUpper q : ℝ)) ^
          (2 * Fintype.card ι +
            (2 ^ (2 * Fintype.card ι) - 1)) := by
  let U : ℕ := groupedDyadicUpper q
  let W : ℝ := 1 + Real.log (U : ℝ)
  let w : ℕ := Fintype.card ι
  have hU : 1 ≤ U := one_le_groupedDyadicUpper q
  have hW0 : 0 ≤ W := by
    dsimp [W]
    have hUR : (1 : ℝ) ≤ U := by exact_mod_cast hU
    linarith [Real.log_nonneg hUR]
  have hfactor : ∀ i n,
      ‖arithmeticDyadicBlock (heathBrownFactorBase L X (kind i)) (q i) n‖ ≤ W := by
    simpa [U, W] using norm_heathBrownGroupedFactorBlock_le L X kind q
  have hpoint : ∀ j : Fin U,
      ‖groupedDyadicCoeffVector
        (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2 ≤
        W ^ (2 * w) * ((((j : ℕ) + 1).divisors.card : ℝ) ^ (2 * w)) := by
    intro j
    have hnorm := norm_groupedDyadicProduct_le_divisors_mul_pow
      (fun i => heathBrownFactorBase L X (kind i)) q hW0 hfactor ((j : ℕ) + 1)
    have hnorm' :
        ‖groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q j‖ ≤
          (((((j : ℕ) + 1).divisors.card : ℝ) * W) ^ w) := by
      simpa [groupedDyadicCoeffVector, complexCoeff_apply, w] using hnorm
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm' 2
    calc
      ‖groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2 ≤
          ((((((j : ℕ) + 1).divisors.card : ℝ) * W) ^ w) ^ 2) := hsq
      _ = W ^ (2 * w) * ((((j : ℕ) + 1).divisors.card : ℝ) ^ (2 * w)) := by
        rw [← pow_mul, mul_pow]
        ring
  have hsum := sum_fin_card_divisors_pow_le_polylog (2 * w) U hU
  have hsumPoint := Finset.sum_le_sum
    fun j (_hj : j ∈ (Finset.univ : Finset (Fin U))) => hpoint j
  calc
    ∑ j : Fin (groupedDyadicUpper q),
        ‖groupedDyadicCoeffVector
          (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2 =
        ∑ j : Fin U,
          ‖groupedDyadicCoeffVector
            (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2 := by rfl
    _ ≤ ∑ j : Fin U,
        W ^ (2 * w) * ((((j : ℕ) + 1).divisors.card : ℝ) ^ (2 * w)) := hsumPoint
    _ = W ^ (2 * w) *
        ∑ j : Fin U, ((((j : ℕ) + 1).divisors.card : ℝ) ^ (2 * w)) := by
      rw [Finset.mul_sum]
    _ ≤ W ^ (2 * w) *
        ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ (2 ^ (2 * w) - 1)) := by
      exact mul_le_mul_of_nonneg_left hsum (pow_nonneg hW0 _)
    _ = (U : ℝ) * (1 + Real.log (U : ℝ)) ^
          (2 * w + (2 ^ (2 * w) - 1)) := by
      rw [show W = 1 + Real.log (U : ℝ) by rfl, pow_add]
      ring
    _ = (groupedDyadicUpper q : ℝ) *
        (1 + Real.log (groupedDyadicUpper q : ℝ)) ^
          (2 * Fintype.card ι +
            (2 ^ (2 * Fintype.card ι) - 1)) := by
      dsimp only [U, w]

/-- Removing one coordinate from a genuine Heath--Brown box leaves a nonempty factor family.
This matters because grouped Montgomery is stated for a nonempty index type. -/
theorem heathBrownBoxFactor_complement_nonempty
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m) :
    Nonempty {i : HeathBrownBoxFactorIndex k box.m //
      i ∈ (Finset.univ.erase j)} := by
  let I := HeathBrownBoxFactorIndex k box.m
  have hcard : 1 < Fintype.card I := by
    change 1 < Fintype.card (HeathBrownBoxFactorIndex k (box.1 : ℕ))
    rw [card_heathBrownBoxFactorIndex box.1.isLt]
    have hdiff : 1 ≤ k - box.m := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero.mpr box.1.isLt)
    omega
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hcard
  by_cases hja : j = a
  · refine ⟨⟨b, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ b⟩⟩⟩
    intro hbj
    exact hab (hja.symm.trans hbj.symm)
  · exact ⟨⟨a, Finset.mem_erase.mpr ⟨fun haj => hja haj.symm, Finset.mem_univ a⟩⟩⟩

/-- Norm factorization of a literal box into one distinguished atom and its erase-complement. -/
theorem norm_heathBrownBox_core_eq_factor_mul_complement
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m) (s : ℂ) :
    ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖ =
      ‖heathBrownBoxFactorValue L X k box s j‖ *
        ‖∏ i : {i : HeathBrownBoxFactorIndex k box.m //
            i ∈ (Finset.univ.erase j)},
          LSeries (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X
              (heathBrownBoxFactorKind k box.m i))
            (heathBrownBoxFactorExponent box.a box.b box.q i))) s‖ := by
  let z : HeathBrownBoxFactorIndex k box.m → ℂ := fun i =>
    heathBrownBoxFactorValue L X k box s i
  have hfull : (∏ i, z i) =
      heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s := by
    simpa [z, heathBrownBoxFactorValue] using
      heathBrownBoxFactorProduct_eq_core L X k box.m box.a box.b box.q s
  have herase : z j * ∏ i ∈ (Finset.univ.erase j), z i = ∏ i, z i := by
    exact Finset.mul_prod_erase Finset.univ z (Finset.mem_univ j)
  rw [← hfull, ← herase, norm_mul]
  congr 1
  rw [Complex.norm_prod]
  simpa [z, heathBrownBoxFactorValue] using
    (Finset.prod_attach (Finset.univ.erase j) (fun i => ‖z i‖)).symm

/-- **Literal derivative-excised Montgomery count with closed coefficient energy.**  The selected
atom may vary in size across ordinates; only its uniform Kuzmin--Landau upper bound is used.  No
amplitude coloring remains, and every analytic cost is explicit. -/
theorem derivativeExcised_montgomery_heathBrownBox_fixedPolylog
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    {c : ℝ} (hc : 0 <= c)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta H : ℝ}
    (hdelta : 0 < delta) (hH : 0 <= H)
    (hgap : ∀ i, lam i + delta <= lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 <= lam r ∧ lam r + delta / 2 <= H)
    {D N T0 C alpha : ℝ}
    (hD : 0 < D) (hN : 0 < N) (hT0 : 0 < T0) (hC : 0 < C)
    (hlong : ∀ r ∈ S,
      ‖heathBrownBoxFactorValue L X k box
          ((c : ℂ) + (lam r : ℝ) * Complex.I) j‖ <=
        C / T0 * N ^ (1 - c))
    (hlarge : ∀ r ∈ S, D ^ (alpha - c) <=
      ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
        ((c : ℂ) + (lam r : ℝ) * Complex.I)‖) :
    let I := {i : HeathBrownBoxFactorIndex k box.m //
      i ∈ (Finset.univ.erase j)}
    let kind : I → HeathBrownFactorKind := fun i =>
      heathBrownBoxFactorKind k box.m i
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent box.a box.b box.q i
    let U : ℕ := groupedDyadicUpper q
    let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
    (S.card : ℝ) *
        (((T0 / C) * D ^ (alpha - c) * N ^ (c - 1)) ^ 2) <=
      (H + 4 * (U : ℝ) * (1 + Real.log U)) *
        (1 / delta + 2 * Real.log U) *
        (((groupedDyadicLower q : ℝ) ^ (-c)) ^ 2 *
          ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ E)) := by
  let I := {i : HeathBrownBoxFactorIndex k box.m //
    i ∈ (Finset.univ.erase j)}
  let kind : I → HeathBrownFactorKind := fun i =>
    heathBrownBoxFactorKind k box.m i
  let q : I → ℕ := fun i =>
    heathBrownBoxFactorExponent box.a box.b box.q i
  let U : ℕ := groupedDyadicUpper q
  let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
  let G : ℝ := (U : ℝ) * (1 + Real.log (U : ℝ)) ^ E
  letI : Nonempty I := heathBrownBoxFactor_complement_nonempty box j
  have henergy : ∑ n : Fin (groupedDyadicUpper q),
      ‖groupedDyadicCoeffVector
        (fun i => heathBrownFactorBase L X (kind i)) q n‖ ^ 2 <= G := by
    simpa [G, U, E, I, kind, q] using
      sum_normSq_heathBrownGrouped_le_fixed_polylog L X kind q
  have hlarge' : ∀ r ∈ S, D ^ (alpha - c) <=
      ‖heathBrownBoxFactorValue L X k box
          ((c : ℂ) + (lam r : ℝ) * Complex.I) j‖ *
        ‖∏ i : I, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i)))
            ((c : ℂ) + (lam r : ℝ) * Complex.I)‖ := by
    intro r hr
    have hfactor := norm_heathBrownBox_core_eq_factor_mul_complement box j
      ((c : ℂ) + (lam r : ℝ) * Complex.I)
    calc
      D ^ (alpha - c) <=
          ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
            ((c : ℂ) + (lam r : ℝ) * Complex.I)‖ := hlarge r hr
      _ = ‖heathBrownBoxFactorValue L X k box
            ((c : ℂ) + (lam r : ℝ) * Complex.I) j‖ *
          ‖∏ i : I, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (kind i)) (q i)))
              ((c : ℂ) + (lam r : ℝ) * Complex.I)‖ := by
        simpa [I, kind, q, Finset.prod_attach] using hfactor
  have hcount := derivativeExcised_montgomery_heathBrown_grouped_finset
    L X kind q hc henergy hdelta hH hgap hband hD hN hT0 hC
      (fun r => ‖heathBrownBoxFactorValue L X k box
        ((c : ℂ) + (lam r : ℝ) * Complex.I) j‖)
      hlong hlarge'
  simpa [I, kind, q, U, E, G] using hcount

end RHTower.Sieve
