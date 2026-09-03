import GaloisForLFunctions.RHTower.Sieve.MenonRouteTMoebiusDyadicPolynomialFrequency
import GaloisForLFunctions.RHTower.Sieve.MaynardLongFactorExclusion
import GaloisForLFunctions.RHTower.Sieve.MaynardLongFactorAbsorption

/-!
# Menon's medium Mobius factor with arbitrary logarithmic saving

The polynomial-frequency dyadic Mobius estimate is specialized to a literal Mobius coordinate of
a Heath--Brown box.  The factor exponent and truncation cutoff remain unchanged.
-/

namespace RHTower.Sieve

open Filter Finset

noncomputable section

/-- Every sufficiently late dyadic Mobius coordinate in a Heath--Brown box has arbitrary
logarithmic saving on every Perron line `c >= 1`, uniformly for frequencies through the
twenty-fourth power of its length. -/
theorem eventually_norm_heathBrownBoxFactorValue_moebius_le_rpow_mul_log_rpow_neg_pow_twentyFour
    (A : ℝ) :
    ∀ᶠ q : ℕ in atTop, ∀ (L X k : ℕ) (box : HeathBrownBoxChoice L X k)
        (i : HeathBrownBoxFactorIndex k box.m) (c tau : ℝ),
      1 ≤ c →
      heathBrownBoxFactorKind k box.m i = .moebius →
      heathBrownBoxFactorExponent box.a box.b box.q i = q →
      2 ^ q ≤ L →
      |tau| ≤ (((2 ^ q : ℕ) : ℝ)) ^ (24 : ℕ) →
      ‖heathBrownBoxFactorValue L X k box
          ((c : ℂ) + (tau : ℝ) * Complex.I) i‖ ≤
        (((2 ^ q : ℕ) : ℝ)) ^ (1 - c) *
          (Real.log (((2 ^ q : ℕ) : ℝ))) ^ (-A) := by
  filter_upwards [
    eventually_norm_LSeries_truncatedMoebius_dyadic_le_rpow_mul_log_rpow_neg_pow_twentyFour A]
    with q hq
  intro L X k box i c tau hc hkind hexponent hqL htau
  rcases i with i | i
  · have hai : box.a i = q := by
      simpa [heathBrownBoxFactorExponent] using hexponent
    subst q
    simpa [heathBrownBoxFactorValue, heathBrownBoxFactorKind,
      heathBrownBoxFactorExponent, heathBrownFactorBase] using
      hq L c tau hc hqL htau
  · rcases i with i | i <;> simp [heathBrownBoxFactorKind] at hkind

/-- Abscissa-one specialization of the full Perron-half-plane factor estimate. -/
theorem eventually_norm_heathBrownBoxFactorValue_moebius_le_log_rpow_neg_pow_twentyFour
    (A : ℝ) :
    ∀ᶠ q : ℕ in atTop, ∀ (L X k : ℕ) (box : HeathBrownBoxChoice L X k)
        (i : HeathBrownBoxFactorIndex k box.m) (tau : ℝ),
      heathBrownBoxFactorKind k box.m i = .moebius →
      heathBrownBoxFactorExponent box.a box.b box.q i = q →
      2 ^ q ≤ L →
      |tau| ≤ (((2 ^ q : ℕ) : ℝ)) ^ (24 : ℕ) →
      ‖heathBrownBoxFactorValue L X k box
          ((1 : ℂ) + (tau : ℝ) * Complex.I) i‖ ≤
        (Real.log (((2 ^ q : ℕ) : ℝ))) ^ (-A) := by
  filter_upwards [
    eventually_norm_heathBrownBoxFactorValue_moebius_le_rpow_mul_log_rpow_neg_pow_twentyFour A]
    with q hq
  intro L X k box i tau hkind hexponent hqL htau
  simpa using hq L X k box i 1 tau (by norm_num) hkind hexponent hqL htau

/-- A real power distributes across a finite product of cast natural lengths. -/
theorem prod_natCast_rpow_eq_natCast_prod_rpow
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) (beta : ℝ) :
    (∏ i ∈ s, ((f i : ℕ) : ℝ) ^ beta) =
      (((∏ i ∈ s, f i : ℕ) : ℝ) ^ beta) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg (f i)) (Nat.cast_nonneg (∏ j ∈ s, f j)), ih]

/-- The selected Mobius saving propagates through the full literal box on every Perron line.
The selected factor and its erase-complement recombine to the exact full lower support edge. -/
theorem eventually_norm_heathBrownDyadicCoreProduct_of_medium_moebius_le_rpow
    (A : ℝ) :
    ∀ᶠ q : ℕ in atTop, ∀ (L X k : ℕ) (box : HeathBrownBoxChoice L X k)
        (i : HeathBrownBoxFactorIndex k box.m) (c tau : ℝ),
      1 ≤ X →
      1 ≤ c →
      heathBrownBoxFactorKind k box.m i = .moebius →
      heathBrownBoxFactorExponent box.a box.b box.q i = q →
      2 ^ q ≤ L →
      |tau| ≤ (((2 ^ q : ℕ) : ℝ)) ^ (24 : ℕ) →
      ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
          ((c : ℂ) + (tau : ℝ) * Complex.I)‖ ≤
        ((groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^ (1 - c) *
          (Real.log (((2 ^ q : ℕ) : ℝ))) ^ (-A) *
            maynardLongPolylogEnvelope X := by
  filter_upwards [
    eventually_norm_heathBrownBoxFactorValue_moebius_le_rpow_mul_log_rpow_neg_pow_twentyFour A]
    with q hfactor
  intro L X k box i c tau hX hc hkind hexponent hqL htau
  let length : HeathBrownBoxFactorIndex k box.m → ℕ := fun j =>
    2 ^ heathBrownBoxFactorExponent box.a box.b box.q j
  let z : HeathBrownBoxFactorIndex k box.m → ℂ := fun j =>
    heathBrownBoxFactorValue L X k box
      ((c : ℂ) + (tau : ℝ) * Complex.I) j
  have hi : i ∈ (Finset.univ : Finset (HeathBrownBoxFactorIndex k box.m)) :=
    Finset.mem_univ i
  have hselected : ‖z i‖ ≤
      ((length i : ℕ) : ℝ) ^ (1 - c) *
        (Real.log (((2 ^ q : ℕ) : ℝ))) ^ (-A) := by
    simpa only [z, length, hexponent] using
      hfactor L X k box i c tau hc hkind hexponent hqL htau
  have hcomplementRaw := norm_heathBrownBoxFactorValue_prod_erase_le_trivial
    L X k box (sigma := c) (by linarith) tau i
  have hconstant :
      (∏ j ∈ (Finset.univ.erase i),
          heathBrownFactorTrivialConstant
            (heathBrownBoxFactorKind k box.m j)
            (heathBrownBoxFactorExponent box.a box.b box.q j)) ≤
        maynardLongPolylogEnvelope X := by
    change heathBrownComplementTrivialConstant box i ≤
      maynardLongPolylogEnvelope X
    rw [heathBrownComplementTrivialConstant_eq]
    split_ifs
    · exact one_le_maynardLongPolylogEnvelope X
    · exact heathBrown_log_trivialConstant_le_polylogEnvelope box hX
  have hcomplement : ‖∏ j ∈ (Finset.univ.erase i), z j‖ ≤
      maynardLongPolylogEnvelope X *
        (((∏ j ∈ (Finset.univ.erase i), length j : ℕ) : ℝ) ^ (1 - c)) := by
    have hraw : ‖∏ j ∈ (Finset.univ.erase i), z j‖ ≤
        (∏ j ∈ (Finset.univ.erase i),
          heathBrownFactorTrivialConstant
            (heathBrownBoxFactorKind k box.m j)
            (heathBrownBoxFactorExponent box.a box.b box.q j)) *
          (((∏ j ∈ (Finset.univ.erase i), length j : ℕ) : ℝ) ^ (1 - c)) := by
      simpa [z, length] using hcomplementRaw
    exact hraw.trans (mul_le_mul_of_nonneg_right hconstant (by positivity))
  have hlength :
      ((length i : ℕ) : ℝ) ^ (1 - c) *
          (((∏ j ∈ (Finset.univ.erase i), length j : ℕ) : ℝ) ^ (1 - c)) =
        ((groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^ (1 - c) := by
    rw [← Real.mul_rpow (Nat.cast_nonneg (length i))
      (Nat.cast_nonneg (∏ j ∈ (Finset.univ.erase i), length j))]
    rw [← Nat.cast_mul]
    congr 2
    calc
      length i * ∏ j ∈ (Finset.univ.erase i), length j =
          ∏ j, length j := Finset.mul_prod_erase Finset.univ length hi
      _ = groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) := by
        simp [length, groupedDyadicLower]
  have hfull : (∏ j, z j) =
      heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
        ((c : ℂ) + (tau : ℝ) * Complex.I) := by
    simpa [z, heathBrownBoxFactorValue] using
      heathBrownBoxFactorProduct_eq_core L X k box.m box.a box.b box.q
        ((c : ℂ) + (tau : ℝ) * Complex.I)
  rw [← hfull, ← Finset.mul_prod_erase Finset.univ z hi, norm_mul]
  calc
    ‖z i‖ * ‖∏ j ∈ Finset.univ.erase i, z j‖ ≤
        (((length i : ℕ) : ℝ) ^ (1 - c) *
          (Real.log (((2 ^ q : ℕ) : ℝ))) ^ (-A)) *
        (maynardLongPolylogEnvelope X *
          (((∏ j ∈ (Finset.univ.erase i), length j : ℕ) : ℝ) ^ (1 - c))) :=
      mul_le_mul hselected hcomplement (norm_nonneg _) (by positivity)
    _ = ((groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^ (1 - c) *
          (Real.log (((2 ^ q : ℕ) : ℝ))) ^ (-A) *
            maynardLongPolylogEnvelope X := by
      rw [← hlength]
      ring

/-- At abscissa one, the selected Mobius saving propagates through the full literal box.  The
entire erase-complement costs at most the packet's unique logarithmic envelope. -/
theorem eventually_norm_heathBrownDyadicCoreProduct_of_medium_moebius_le
    (A : ℝ) :
    ∀ᶠ q : ℕ in atTop, ∀ (L X k : ℕ) (box : HeathBrownBoxChoice L X k)
        (i : HeathBrownBoxFactorIndex k box.m) (tau : ℝ),
      1 ≤ X →
      heathBrownBoxFactorKind k box.m i = .moebius →
      heathBrownBoxFactorExponent box.a box.b box.q i = q →
      2 ^ q ≤ L →
      |tau| ≤ (((2 ^ q : ℕ) : ℝ)) ^ (24 : ℕ) →
      ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
          ((1 : ℂ) + (tau : ℝ) * Complex.I)‖ ≤
        (Real.log (((2 ^ q : ℕ) : ℝ))) ^ (-A) * maynardLongPolylogEnvelope X := by
  filter_upwards [
    eventually_norm_heathBrownBoxFactorValue_moebius_le_log_rpow_neg_pow_twentyFour A]
    with q hfactor
  intro L X k box i tau hX hkind hexponent hqL htau
  let z : HeathBrownBoxFactorIndex k box.m → ℂ := fun j =>
    heathBrownBoxFactorValue L X k box
      ((1 : ℂ) + (tau : ℝ) * Complex.I) j
  have hi : i ∈ (Finset.univ : Finset (HeathBrownBoxFactorIndex k box.m)) :=
    Finset.mem_univ i
  have hselected : ‖z i‖ ≤
      (Real.log (((2 ^ q : ℕ) : ℝ))) ^ (-A) := by
    simpa only [z] using hfactor L X k box i tau hkind hexponent hqL htau
  have hcomplementRaw := norm_heathBrownBoxFactorValue_prod_erase_le_trivial
    L X k box (sigma := (1 : ℝ)) (by norm_num) tau i
  have hcomplement : ‖∏ j ∈ (Finset.univ.erase i), z j‖ ≤
      maynardLongPolylogEnvelope X := by
    have hraw : ‖∏ j ∈ (Finset.univ.erase i), z j‖ ≤
        heathBrownComplementTrivialConstant box i := by
      simpa [z, heathBrownComplementTrivialConstant] using hcomplementRaw
    refine hraw.trans ?_
    rw [heathBrownComplementTrivialConstant_eq]
    split_ifs
    · exact one_le_maynardLongPolylogEnvelope X
    · exact heathBrown_log_trivialConstant_le_polylogEnvelope box hX
  have hfull : (∏ j, z j) =
      heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
        ((1 : ℂ) + (tau : ℝ) * Complex.I) := by
    simpa [z, heathBrownBoxFactorValue] using
      heathBrownBoxFactorProduct_eq_core L X k box.m box.a box.b box.q
        ((1 : ℂ) + (tau : ℝ) * Complex.I)
  rw [← hfull, ← Finset.mul_prod_erase Finset.univ z hi, norm_mul]
  exact mul_le_mul hselected hcomplement (norm_nonneg _) (by positivity)

end

end RHTower.Sieve
