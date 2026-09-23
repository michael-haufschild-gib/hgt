import GaloisForLFunctions.RHTower.Sieve.MaynardDerivativeCountDuality
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedPolylogEnergy
import GaloisForLFunctions.RHTower.Sieve.MaynardZeroExponentTrimming
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability

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
    have hdiff : 1 ≤ k - (box.1 : ℕ) := by
      have hm : (box.1 : ℕ) < k := box.1.isLt
      omega
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
  let comp : Finset (HeathBrownBoxFactorIndex k box.m) := Finset.univ.erase j
  let I := ↥comp
  letI : Fintype I := Subtype.fintype fun i => i ∈ comp
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
    simpa [G, U, E, I, comp, kind, q] using
      sum_normSq_heathBrownGrouped_le_fixed_polylog L X kind q
  have hlarge' : ∀ r ∈ S, D ^ (alpha - c) <=
      ‖heathBrownBoxFactorValue L X k box
          ((c : ℂ) + (lam r : ℝ) * Complex.I) j‖ *
        ‖∏ i : I, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i)))
            ((c : ℂ) + (lam r : ℝ) * Complex.I)‖ := by
    intro r hr
    let s : ℂ := (c : ℂ) + (lam r : ℝ) * Complex.I
    let z : HeathBrownBoxFactorIndex k box.m → ℂ := fun i =>
      heathBrownBoxFactorValue L X k box s i
    have hfull : (∏ i, z i) =
        heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s := by
      simpa [z, heathBrownBoxFactorValue] using
        heathBrownBoxFactorProduct_eq_core L X k box.m box.a box.b box.q s
    have herase : z j * ∏ i ∈ (Finset.univ.erase j), z i = ∏ i, z i :=
      Finset.mul_prod_erase Finset.univ z (Finset.mem_univ j)
    have hlocal :
        (∏ i : I, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (kind i)) (q i))) s) =
          ∏ i ∈ (Finset.univ.erase j), z i := by
      symm
      simpa [I, comp, kind, q, z, heathBrownBoxFactorValue] using
        (Finset.prod_subtype (F := inferInstance) (Finset.univ.erase j)
          (fun i => Iff.rfl) (fun i => z i))
    have hfactorLocal :
        ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖ =
          ‖z j‖ *
            ‖∏ i : I, LSeries
              (complexCoeff (arithmeticDyadicBlock
                (heathBrownFactorBase L X (kind i)) (q i))) s‖ := by
      rw [← hfull, ← herase, norm_mul, hlocal]
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
        simpa [s, z] using hfactorLocal
  have hcount := derivativeExcised_montgomery_heathBrown_grouped_finset
    L X kind q hc henergy hdelta hH hgap hband hD hN hT0 hC
      (fun r => ‖heathBrownBoxFactorValue L X k box
        ((c : ℂ) + (lam r : ℝ) * Complex.I) j‖)
      hlong hlarge'
  simpa [I, comp, kind, q, U, E, G] using hcount

/-- Exact height-term normalization after derivative excision.  All dependence on Perron
abscissa `c`, excised length `r`, and total length `tau` cancels to the canonical exponent. -/
theorem derivativeComplement_height_power_identity
    {T C tau r s alpha c : ℝ}
    (hT : 0 < T) (hC : 0 < C) (htau : tau = r + s) :
    (C ^ 2 * T ^ maynardDerivativeComplementHeightExponent tau alpha s) *
        (((T / C) * (T ^ tau) ^ (alpha - c) *
          (T ^ r) ^ (c - 1)) ^ 2) =
      T * (T ^ s) ^ (1 - 2 * c) := by
  rw [← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le]
  rw [pow_two]
  dsimp only [maynardDerivativeComplementHeightExponent]
  rw [htau]
  field_simp [hC.ne']
  simp_rw [← Real.rpow_natCast]
  simp_rw [← Real.rpow_mul hT.le]
  nth_rewrite 2 [← Real.rpow_one T]
  rw [← Real.rpow_add hT, ← Real.rpow_add hT, ← Real.rpow_add hT]
  congr 1
  norm_num
  ring

/-- Exact length-term normalization after derivative excision. -/
theorem derivativeComplement_length_power_identity
    {T C tau r s alpha c : ℝ}
    (hT : 0 < T) (hC : 0 < C) (htau : tau = r + s) :
    (C ^ 2 * T ^ maynardDerivativeComplementLengthExponent tau alpha) *
        (((T / C) * (T ^ tau) ^ (alpha - c) *
          (T ^ r) ^ (c - 1)) ^ 2) =
      (T ^ s) ^ (2 - 2 * c) := by
  rw [← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le]
  rw [pow_two]
  dsimp only [maynardDerivativeComplementLengthExponent]
  rw [htau]
  field_simp [hC.ne']
  simp_rw [← Real.rpow_natCast]
  simp_rw [← Real.rpow_mul hT.le]
  rw [← Real.rpow_add hT, ← Real.rpow_add hT, ← Real.rpow_add hT]
  congr 1
  norm_num
  ring

/-- **Canonicalization of the literal derivative count.**  Once analytic width and energy costs
are collected in `P`, the exact finite-set inequality becomes the two canonical powers used by
the `2/25` seam reserve.  This theorem proves the cancellation rather than assuming an exponent
heuristic. -/
theorem derivativeExcised_count_to_canonical_powers
    {R P T C tau r s alpha c : ℝ}
    (hT : 0 < T) (hC : 0 < C)
    (htau : tau = r + s)
    (hcount :
      R * (((T / C) * (T ^ tau) ^ (alpha - c) *
          (T ^ r) ^ (c - 1)) ^ 2) <=
        P * (T * (T ^ s) ^ (1 - 2 * c) +
          (T ^ s) ^ (2 - 2 * c))) :
    R <= (C ^ 2 * P) *
      (T ^ maynardDerivativeComplementHeightExponent tau alpha s +
        T ^ maynardDerivativeComplementLengthExponent tau alpha) := by
  let V : ℝ := (T / C) * (T ^ tau) ^ (alpha - c) *
    (T ^ r) ^ (c - 1)
  let B : ℝ := (C ^ 2 * P) *
    (T ^ maynardDerivativeComplementHeightExponent tau alpha s +
      T ^ maynardDerivativeComplementLengthExponent tau alpha)
  have hV : 0 < V := by
    dsimp only [V]
    positivity
  have hheight := derivativeComplement_height_power_identity hT hC htau
      (alpha := alpha) (c := c)
  have hlength := derivativeComplement_length_power_identity hT hC htau
      (alpha := alpha) (c := c)
  have hnormalize : B * V ^ 2 =
      P * (T * (T ^ s) ^ (1 - 2 * c) +
        (T ^ s) ^ (2 - 2 * c)) := by
    calc
      B * V ^ 2 = P *
          ((C ^ 2 * T ^ maynardDerivativeComplementHeightExponent tau alpha s) *
              V ^ 2 +
            (C ^ 2 * T ^ maynardDerivativeComplementLengthExponent tau alpha) *
              V ^ 2) := by
        dsimp only [B]
        ring
      _ = P * (T * (T ^ s) ^ (1 - 2 * c) +
          (T ^ s) ^ (2 - 2 * c)) := by
        rw [show V = (T / C) * (T ^ tau) ^ (alpha - c) *
          (T ^ r) ^ (c - 1) by rfl, hheight, hlength]
  have hscaled : R * V ^ 2 <= B * V ^ 2 := by
    rw [hnormalize]
    simpa only [V] using hcount
  exact (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hV)).mp hscaled

/-- The erase-complement lower edge is exactly `T` raised to its dyadic logarithmic mass. -/
theorem heathBrownBoxFactor_complement_lower_eq_rpow
    {L X k : ℕ} {T : ℝ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m) (hT : 1 < T) :
    let I := {i : HeathBrownBoxFactorIndex k box.m //
      i ∈ (Finset.univ.erase j)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent box.a box.b box.q i
    ((groupedDyadicLower q : ℕ) : ℝ) =
      T ^ ∑ i ∈ (Finset.univ.erase j),
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i) := by
  dsimp only
  simp only [groupedDyadicLower]
  rw [← Finset.prod_subtype (Finset.univ.erase j)
    (fun _ => Iff.rfl)
    (fun i => 2 ^ heathBrownBoxFactorExponent box.a box.b box.q i)]
  exact cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent
    hT (heathBrownBoxFactorExponent box.a box.b box.q)
      (Finset.univ.erase j)

/-- Exact additive decomposition of box length into distinguished factor and erase-complement. -/
theorem heathBrownBox_totalExponent_eq_factor_add_complement
    {L X k : ℕ} {T : ℝ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m) :
    heathBrownBoxTotalExponent L X k T box =
      dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q j) +
        ∑ i ∈ (Finset.univ.erase j),
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q i) := by
  change (∑ i : HeathBrownBoxFactorIndex k box.m,
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i)) = _
  rw [add_comm]
  exact (Finset.sum_erase_add (Finset.univ)
    (fun i => dyadicLogExponent T
      (heathBrownBoxFactorExponent box.a box.b box.q i))
    (Finset.mem_univ j)).symm

/-- At base `T>1`, zero dyadic logarithmic mass is equivalent to exponent zero. -/
theorem dyadicLogExponent_eq_zero_iff
    {T : ℝ} (hT : 1 < T) (q : ℕ) :
    dyadicLogExponent T q = 0 ↔ q = 0 := by
  constructor
  · intro hq
    have hr := rpow_dyadicLogExponent hT q
    rw [hq, Real.rpow_zero] at hr
    have hnat : 2 ^ q = 1 := by exact_mod_cast hr.symm
    simpa using (Nat.pow_eq_one.mp hnat)
  · rintro rfl
    simp [dyadicLogExponent, Real.logb]

/-- Zero complement mass forces every retained dyadic exponent to be zero. -/
theorem heathBrownBox_complement_factorExponent_eq_zero_of_mass_eq_zero
    {L X k : ℕ} {T : ℝ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m) (hT : 1 < T)
    (hzero : (∑ i ∈ (Finset.univ.erase j),
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i)) = 0) :
    ∀ i ∈ (Finset.univ.erase j),
      heathBrownBoxFactorExponent box.a box.b box.q i = 0 := by
  intro i hi
  have hterm : dyadicLogExponent T
      (heathBrownBoxFactorExponent box.a box.b box.q i) = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ha => dyadicLogExponent_nonneg hT
        (heathBrownBoxFactorExponent box.a box.b box.q a))).mp hzero i hi
  exact (dyadicLogExponent_eq_zero_iff hT _).mp hterm

/-- **Zero-mass complement classification.**  For a nonzero literal box, the entire zero-mass
erase-complement is the constant Dirichlet polynomial `1`.  Thus the unique zero-reserve case is
not a genuine complementary large-value problem: all ordinate dependence lies in the one
distinguished zeta/log factor. -/
theorem heathBrownBox_complement_value_eq_one_of_mass_eq_zero
    {L X k : ℕ} {T : ℝ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hL : 1 <= L) (hX : 1 <= X) (hlog : 1 <= box.q)
    (hT : 1 < T)
    (hzero : (∑ i ∈ (Finset.univ.erase j),
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i)) = 0)
    (z : ℂ) :
    (∏ i : {i : HeathBrownBoxFactorIndex k box.m //
        i ∈ (Finset.univ.erase j)},
      LSeries (complexCoeff (arithmeticDyadicBlock
        (heathBrownFactorBase L X (heathBrownBoxFactorKind k box.m i))
        (heathBrownBoxFactorExponent box.a box.b box.q i))) z) = 1 := by
  apply Finset.prod_eq_one
  intro i _hi
  simpa [heathBrownBoxFactorValue] using
    heathBrownBoxFactorValue_eq_one_of_exponent_eq_zero
      box hL hX hlog z i
        (heathBrownBox_complement_factorExponent_eq_zero_of_mass_eq_zero
          box j hT hzero i i.property)

/-- Fixed width of every degree-60 erase-complement. -/
def maynardLowOrdinateComplementWidthConstant : ℝ := ((2 ^ 120 : ℕ) : ℝ)

/-- Fixed unraised divisor-moment exponent of every degree-60 erase-complement. -/
def maynardLowOrdinateComplementPolylogExponent : ℕ :=
  2 * 120 + (2 ^ (2 * 120) - 1)

theorem maynardLowOrdinateComplementWidthConstant_one_le :
    1 <= maynardLowOrdinateComplementWidthConstant := by
  dsimp only [maynardLowOrdinateComplementWidthConstant]
  exact_mod_cast Nat.one_le_two_pow

/-- The erase-complement retains at most all `120` degree-60 coordinates. -/
theorem heathBrownBoxFactor_complement_card_le_oneTwenty
    {L X : ℕ} (box : HeathBrownBoxChoice L X 60)
    (j : HeathBrownBoxFactorIndex 60 box.m) :
    Fintype.card {i : HeathBrownBoxFactorIndex 60 box.m //
      i ∈ (Finset.univ.erase j)} <= 120 := by
  rw [Fintype.card_coe]
  exact (Finset.card_le_univ _).trans
    (by simpa using card_heathBrownBoxFactorIndex_le_two_mul box)

theorem heathBrownBoxFactor_complement_polylogExponent_le
    {L X : ℕ} (box : HeathBrownBoxChoice L X 60)
    (j : HeathBrownBoxFactorIndex 60 box.m) :
    let I := {i : HeathBrownBoxFactorIndex 60 box.m //
      i ∈ (Finset.univ.erase j)}
    2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1) <=
      maynardLowOrdinateComplementPolylogExponent := by
  let I := {i : HeathBrownBoxFactorIndex 60 box.m //
    i ∈ (Finset.univ.erase j)}
  have hw : Fintype.card I <= 120 := by
    dsimp only [I]
    rw [Fintype.card_coe]
    exact (Finset.card_le_univ _).trans
      (by simpa using card_heathBrownBoxFactorIndex_le_two_mul box)
  have hdouble : 2 * Fintype.card I <= 2 * 120 := Nat.mul_le_mul_left 2 hw
  have hpow : 2 ^ (2 * Fintype.card I) <= 2 ^ (2 * 120) :=
    Nat.pow_le_pow_right (by norm_num) hdouble
  dsimp only [maynardLowOrdinateComplementPolylogExponent]
  exact Nat.add_le_add hdouble (Nat.sub_le_sub_right hpow 1)

/-- Exact dyadic width gives a uniform constant comparison between complement upper and lower
edges. -/
theorem heathBrownBoxFactor_complement_upper_le_width_mul_lower
    {L X : ℕ} (box : HeathBrownBoxChoice L X 60)
    (j : HeathBrownBoxFactorIndex 60 box.m) :
    let I := {i : HeathBrownBoxFactorIndex 60 box.m //
      i ∈ (Finset.univ.erase j)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent box.a box.b box.q i
    (groupedDyadicUpper q : ℝ) <=
      maynardLowOrdinateComplementWidthConstant *
        (groupedDyadicLower q : ℝ) := by
  dsimp only
  let I := {i : HeathBrownBoxFactorIndex 60 box.m //
    i ∈ (Finset.univ.erase j)}
  let q : I → ℕ := fun i =>
    heathBrownBoxFactorExponent box.a box.b box.q i
  let w : ℕ := Fintype.card I
  have hw : w <= 120 := heathBrownBoxFactor_complement_card_le_oneTwenty box j
  have hpow : 2 ^ w <= 2 ^ 120 := Nat.pow_le_pow_right (by norm_num) hw
  have hwidth := groupedDyadicUpper_eq_lower_mul_twoPow q
  change (groupedDyadicUpper q : ℝ) <=
    maynardLowOrdinateComplementWidthConstant * (groupedDyadicLower q : ℝ)
  rw [hwidth, Nat.cast_mul]
  dsimp only [maynardLowOrdinateComplementWidthConstant]
  have hpowR : ((2 ^ w : ℕ) : ℝ) <= ((2 ^ 120 : ℕ) : ℝ) := by
    exact_mod_cast hpow
  calc
    (groupedDyadicLower q : ℝ) * ((2 ^ w : ℕ) : ℝ) <=
        (groupedDyadicLower q : ℝ) * ((2 ^ 120 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hpowR (by positivity)
    _ = ((2 ^ 120 : ℕ) : ℝ) * (groupedDyadicLower q : ℝ) := by ring

/-- Generic Montgomery width-energy factor in canonical derivative-complement form.  It is a
pure inequality: fixed multiplicative width converts the height term and length term into exactly
the two powers appearing in the derivative-count duality. -/
theorem montgomery_unraised_factor_le_canonical
    {H T U A W c : ℝ} {E : ℕ} {delta : ℝ}
    (hT : 1 <= T) (hH : H <= 3 * T)
    (hdelta : 1 <= delta)
    (hA : 1 <= A) (hU : 1 <= U) (hW : 1 <= W)
    (hwidth : U <= W * A) :
    (H + 4 * U * (1 + Real.log U)) *
        (1 / delta + 2 * Real.log U) *
        (A ^ (-2 * c) *
          (U * (1 + Real.log U) ^ E)) <=
      (12 * W ^ 2 * (1 + Real.log U) ^ (E + 2)) *
        (T * A ^ (1 - 2 * c) + A ^ (2 - 2 * c)) := by
  let Z : ℝ := A ^ (-2 * c)
  let Q : ℝ := 1 + Real.log U
  have hT0 : 0 <= T := zero_le_one.trans hT
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hW0 : 0 <= W := zero_le_one.trans hW
  have hlog0 : 0 <= Real.log U := Real.log_nonneg hU
  have hQ : 1 <= Q := by dsimp only [Q]; linarith
  have hQ0 : 0 <= Q := zero_le_one.trans hQ
  have hdelta0 : 0 < delta := zero_lt_one.trans_le hdelta
  have hinv : delta⁻¹ <= 1 := (inv_le_one₀ hdelta0).2 hdelta
  have hsecond : 1 / delta + 2 * Real.log U <= 3 * Q := by
    rw [one_div]
    dsimp only [Q]
    linarith
  have hUL : U * Q <= (W * A) * Q :=
    mul_le_mul_of_nonneg_right hwidth hQ0
  have hWL : 1 <= W * Q := one_le_mul_of_one_le_of_one_le hW hQ
  have hthreeT : 3 * T <= 4 * W * Q * T := by
    have hcoef : (3 : ℝ) <= 4 * (W * Q) := by nlinarith
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcoef hT0
  have hfirst : H + 4 * U * Q <= 4 * W * Q * (T + A) := by
    have hfourRaw := mul_le_mul_of_nonneg_left hUL
      (show (0 : ℝ) <= 4 by norm_num)
    have hfour : 4 * U * Q <= 4 * (W * A) * Q := by
      simpa [mul_assoc] using hfourRaw
    calc
      H + 4 * U * Q <= 3 * T + 4 * (W * A) * Q := by
        exact add_le_add hH hfour
      _ <= 4 * W * Q * T + 4 * W * Q * A := by
        have hsecondTerm : 4 * (W * A) * Q = 4 * W * Q * A := by ring
        rw [hsecondTerm]
        exact add_le_add hthreeT le_rfl
      _ = 4 * W * Q * (T + A) := by ring
  have hZ0 : 0 <= Z := Real.rpow_nonneg hA0.le _
  have henergy : U * Q ^ E <= (W * A) * Q ^ E :=
    mul_le_mul_of_nonneg_right hwidth (pow_nonneg hQ0 E)
  have hraw :
      (H + 4 * U * Q) * (1 / delta + 2 * Real.log U) *
          (Z * (U * Q ^ E)) <=
        (4 * W * Q * (T + A)) * (3 * Q) *
          (Z * ((W * A) * Q ^ E)) := by
    exact mul_le_mul
      (mul_le_mul hfirst hsecond
        (by positivity) (by positivity))
      (mul_le_mul_of_nonneg_left henergy hZ0)
      (mul_nonneg hZ0 (by positivity))
      (by positivity)
  have hZA : Z * A = A ^ (1 - 2 * c) := by
    dsimp only [Z]
    calc
      A ^ (-2 * c) * A = A ^ (-2 * c) * A ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = A ^ ((-2 * c) + 1) := by rw [← Real.rpow_add hA0]
      _ = A ^ (1 - 2 * c) := by congr 1; ring
  have hZA2 : Z * A ^ (2 : ℕ) = A ^ (2 - 2 * c) := by
    dsimp only [Z]
    rw [← Real.rpow_natCast, ← Real.rpow_add hA0]
    congr 1
    norm_num
    ring
  calc
    (H + 4 * U * (1 + Real.log U)) *
        (1 / delta + 2 * Real.log U) *
        (A ^ (-2 * c) * (U * (1 + Real.log U) ^ E)) =
      (H + 4 * U * Q) * (1 / delta + 2 * Real.log U) *
        (Z * (U * Q ^ E)) := by rfl
    _ <= (4 * W * Q * (T + A)) * (3 * Q) *
          (Z * ((W * A) * Q ^ E)) := hraw
    _ = (12 * W ^ 2 * Q ^ (E + 2)) *
        (T * (Z * A) + Z * A ^ (2 : ℕ)) := by
      rw [pow_add]
      ring
    _ = (12 * W ^ 2 * Q ^ (E + 2)) *
        (T * A ^ (1 - 2 * c) + A ^ (2 - 2 * c)) := by
      rw [hZA, hZA2]
    _ = (12 * W ^ 2 * (1 + Real.log U) ^ (E + 2)) *
        (T * A ^ (1 - 2 * c) + A ^ (2 - 2 * c)) := by rfl

/-- Squaring a real power is exact at a positive dyadic lower edge. -/
theorem rpow_neg_sq_eq_rpow_neg_two_mul
    {A c : ℝ} (hA : 0 < A) :
    (A ^ (-c)) ^ 2 = A ^ (-2 * c) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hA.le]
  congr 1
  norm_num
  ring

/-- **Closed analytic-to-canonical bridge.**  A literal derivative-excised Montgomery count,
with a fixed-width unraised complement and its exact base-`T` length, lands in the two canonical
derivative-complement powers.  Every width, energy, and Kuzmin--Landau constant remains explicit;
there is no amplitude discretization or hidden exponent loss. -/
theorem derivativeExcised_montgomery_to_canonical
    {R H T U A W C tau r s alpha c delta : ℝ} {E : ℕ}
    (hT : 1 <= T) (hH : H <= 3 * T)
    (hdelta : 1 <= delta)
    (hA : 1 <= A) (hU : 1 <= U) (hW : 1 <= W)
    (hwidth : U <= W * A) (hC : 0 < C)
    (htau : tau = r + s) (hAeq : A = T ^ s)
    (hcount :
      R * (((T / C) * (T ^ tau) ^ (alpha - c) *
          (T ^ r) ^ (c - 1)) ^ 2) <=
        (H + 4 * U * (1 + Real.log U)) *
          (1 / delta + 2 * Real.log U) *
          (((A ^ (-c)) ^ 2) *
            (U * (1 + Real.log U) ^ E))) :
    R <=
      (C ^ 2 * (12 * W ^ 2 * (1 + Real.log U) ^ (E + 2))) *
        (T ^ maynardDerivativeComplementHeightExponent tau alpha s +
          T ^ maynardDerivativeComplementLengthExponent tau alpha) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hfactor := montgomery_unraised_factor_le_canonical
    hT hH hdelta hA hU hW hwidth (c := c) (E := E)
  have hpow : (A ^ (-c)) ^ 2 = A ^ (-2 * c) :=
    rpow_neg_sq_eq_rpow_neg_two_mul (zero_lt_one.trans_le hA)
  have hcount' :
      R * (((T / C) * (T ^ tau) ^ (alpha - c) *
          (T ^ r) ^ (c - 1)) ^ 2) <=
        (12 * W ^ 2 * (1 + Real.log U) ^ (E + 2)) *
          (T * (T ^ s) ^ (1 - 2 * c) +
            (T ^ s) ^ (2 - 2 * c)) := by
    calc
      R * (((T / C) * (T ^ tau) ^ (alpha - c) *
          (T ^ r) ^ (c - 1)) ^ 2) <=
          (H + 4 * U * (1 + Real.log U)) *
            (1 / delta + 2 * Real.log U) *
            (A ^ (-2 * c) *
              (U * (1 + Real.log U) ^ E)) := by
        simpa only [hpow] using hcount
      _ <= (12 * W ^ 2 * (1 + Real.log U) ^ (E + 2)) *
          (T * A ^ (1 - 2 * c) + A ^ (2 - 2 * c)) := hfactor
      _ = (12 * W ^ 2 * (1 + Real.log U) ^ (E + 2)) *
          (T * (T ^ s) ^ (1 - 2 * c) +
            (T ^ s) ^ (2 - 2 * c)) := by rw [hAeq]
  exact derivativeExcised_count_to_canonical_powers hT0 hC htau hcount'

/-- **Literal degree-60 box receiver.**  Excising one distinguished atom from a Heath--Brown
box, applying the sharp unraised Montgomery energy, and using exact dyadic length geometry gives
the canonical derivative-complement count.  This closes the former giant-seam conversion at
finite-set level; only the displayed fixed polylogarithmic cost remains to absorb. -/
theorem derivativeExcised_montgomery_heathBrownBox_to_canonical
    {L X : ℕ} (box : HeathBrownBoxChoice L X 60)
    (j : HeathBrownBoxFactorIndex 60 box.m)
    {c : ℝ} (hc : 0 <= c)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta H : ℝ}
    {T C alpha : ℝ}
    (hdelta : 1 <= delta) (hH0 : 0 <= H) (hH : H <= 3 * T)
    (hgap : ∀ i, lam i + delta <= lam (i + 1))
    (hband : ∀ n ∈ S, delta / 2 <= lam n ∧ lam n + delta / 2 <= H)
    (hT : 1 < T) (hC : 0 < C)
    (hlong : ∀ n ∈ S,
      ‖heathBrownBoxFactorValue L X 60 box
          ((c : ℂ) + (lam n : ℝ) * Complex.I) j‖ <=
        C / T *
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) ^
            (1 - c))
    (hlarge : ∀ n ∈ S,
      (((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ)) ^
          (alpha - c) <=
        ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
          ((c : ℂ) + (lam n : ℝ) * Complex.I)‖) :
    let I := {i : HeathBrownBoxFactorIndex 60 box.m //
      i ∈ (Finset.univ.erase j)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent box.a box.b box.q i
    let U : ℝ := (groupedDyadicUpper q : ℝ)
    let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
    let tau : ℝ := heathBrownBoxTotalExponent L X 60 T box
    let s : ℝ := ∑ i ∈ (Finset.univ.erase j),
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i)
    (S.card : ℝ) <=
      (C ^ 2 * (12 * maynardLowOrdinateComplementWidthConstant ^ 2 *
        (1 + Real.log U) ^ (E + 2))) *
        (T ^ maynardDerivativeComplementHeightExponent tau alpha s +
          T ^ maynardDerivativeComplementLengthExponent tau alpha) := by
  let comp : Finset (HeathBrownBoxFactorIndex 60 box.m) := Finset.univ.erase j
  let I := ↥comp
  letI : Fintype I := Subtype.fintype fun i => i ∈ comp
  let q : I → ℕ := fun i =>
    heathBrownBoxFactorExponent box.a box.b box.q i
  let U : ℝ := (groupedDyadicUpper q : ℝ)
  let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
  let tau : ℝ := heathBrownBoxTotalExponent L X 60 T box
  let r : ℝ := dyadicLogExponent T
    (heathBrownBoxFactorExponent box.a box.b box.q j)
  let s : ℝ := ∑ i ∈ (Finset.univ.erase j),
    dyadicLogExponent T
      (heathBrownBoxFactorExponent box.a box.b box.q i)
  let A : ℝ := (groupedDyadicLower q : ℝ)
  let W : ℝ := maynardLowOrdinateComplementWidthConstant
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hdeltaPos : 0 < delta := zero_lt_one.trans_le hdelta
  have hD : 0 <
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
    exact_mod_cast one_le_groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q)
  have hN : 0 <
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) := by
    positivity
  have hcount := derivativeExcised_montgomery_heathBrownBox_fixedPolylog
    box j hc hdeltaPos hH0 hgap hband hD hN hTpos hC hlong hlarge
  have hDpow :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) =
        T ^ tau := by
    dsimp only [tau]
    simpa [heathBrownBoxTotalExponent, groupedDyadicLower] using
      (cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent hT
        (heathBrownBoxFactorExponent box.a box.b box.q)
        (Finset.univ : Finset (HeathBrownBoxFactorIndex 60 box.m)))
  have hNpow :
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) =
        T ^ r := by
    dsimp only [r]
    exact (rpow_dyadicLogExponent hT
      (heathBrownBoxFactorExponent box.a box.b box.q j)).symm
  have hApow : A = T ^ s := by
    dsimp only [A, s, q, I, comp]
    exact heathBrownBoxFactor_complement_lower_eq_rpow box j hT
  have htau : tau = r + s := by
    dsimp only [tau, r, s]
    exact heathBrownBox_totalExponent_eq_factor_add_complement box j
  have hA : 1 <= A := by
    dsimp only [A]
    exact_mod_cast one_le_groupedDyadicLower q
  have hU : 1 <= U := by
    dsimp only [U]
    exact_mod_cast one_le_groupedDyadicUpper q
  have hW : 1 <= W := by
    exact maynardLowOrdinateComplementWidthConstant_one_le
  have hwidth : U <= W * A := by
    dsimp only [U, W, A, q, I, comp]
    exact heathBrownBoxFactor_complement_upper_le_width_mul_lower box j
  have hcount' :
      (S.card : ℝ) * (((T / C) * (T ^ tau) ^ (alpha - c) *
          (T ^ r) ^ (c - 1)) ^ 2) <=
        (H + 4 * U * (1 + Real.log U)) *
          (1 / delta + 2 * Real.log U) *
          (((A ^ (-c)) ^ 2) *
            (U * (1 + Real.log U) ^ E)) := by
    simpa only [I, comp, q, U, E, A, hDpow, hNpow] using hcount
  have hcanonical := derivativeExcised_montgomery_to_canonical
    hT.le hH hdelta hA hU hW hwidth hC htau hApow hcount'
  simpa only [I, comp, q, U, E, tau, r, s, W] using hcanonical

/-- **Uniform fixed-cost absorption for the derivative receiver.**  The actual Kuzmin--Landau
constant `C <= 600 log T`, degree-60 complement width, sharp unraised energy exponent, and any
fixed receiver logarithm together cost at most `T^(1/25)`.  The astronomically large divisor
moment exponent is harmless because it is fixed independently of `T`. -/
theorem eventually_maynardLowOrdinateDerivative_fixedCost_absorbed (q : ℕ) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ C U : ℝ, ∀ E : ℕ,
      0 <= C → C <= 600 * Real.log T →
      1 <= U → U <= maynardLowOrdinateComplementWidthConstant * T ^ (8 : ℕ) →
      E <= maynardLowOrdinateComplementPolylogExponent →
      (2 * (C ^ 2 * (12 * maynardLowOrdinateComplementWidthConstant ^ 2 *
          (1 + Real.log U) ^ (E + 2)))) * (Real.log T) ^ q <=
        T ^ (1 / 25 : ℝ) := by
  let W : ℝ := maynardLowOrdinateComplementWidthConstant
  let E0 : ℕ := maynardLowOrdinateComplementPolylogExponent + 2
  let B0 : ℝ := 9 + |Real.log W|
  let K0 : ℝ := 24 * 600 ^ 2 * W ^ 2 * B0 ^ E0
  let eps : ℝ := 1 / 50
  have heps : 0 < eps := by norm_num [eps]
  have hW : 1 <= W := maynardLowOrdinateComplementWidthConstant_one_le
  have hWpos : 0 < W := zero_lt_one.trans_le hW
  have hB0 : 1 <= B0 := by
    dsimp only [B0]
    linarith [abs_nonneg (Real.log W)]
  have hK0 : 0 < K0 := by
    dsimp only [K0]
    positivity
  have hconst : ∀ᶠ T : ℝ in Filter.atTop, K0 <= T ^ eps :=
    (tendsto_rpow_atTop heps).eventually_ge_atTop K0
  filter_upwards [RHTower.burnolEventually_log_pow_le_rpow heps (q + E0 + 2),
    hconst, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (1 : ℝ)] with T hlogPow hconstT hlogT hT
  intro C U E hC0 hC hU hUscale hE
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hlog0 : 0 <= Real.log T := zero_le_one.trans hlogT
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hT8pos : 0 < T ^ (8 : ℕ) := pow_pos hTpos _
  have hlogU : Real.log U <= Real.log W + 8 * Real.log T := by
    calc
      Real.log U <= Real.log (W * T ^ (8 : ℕ)) :=
        Real.log_le_log hUpos hUscale
      _ = Real.log W + Real.log (T ^ (8 : ℕ)) := by
        rw [Real.log_mul hWpos.ne' hT8pos.ne']
      _ = Real.log W + 8 * Real.log T := by
        rw [Real.log_pow]
        norm_num
  have hbase : 1 + Real.log U <= B0 * Real.log T := by
    have hlogW : Real.log W <= |Real.log W| * Real.log T := by
      calc
        Real.log W <= |Real.log W| := le_abs_self _
        _ <= |Real.log W| * Real.log T := by
          nlinarith [abs_nonneg (Real.log W)]
    dsimp only [B0]
    nlinarith
  have hbase1 : 1 <= 1 + Real.log U := by
    linarith [Real.log_nonneg hU]
  have hBLog1 : 1 <= B0 * Real.log T :=
    one_le_mul_of_one_le_of_one_le hB0 hlogT
  have hE2 : E + 2 <= E0 := by
    dsimp only [E0]
    omega
  have hpowBase : (1 + Real.log U) ^ (E + 2) <=
      (B0 * Real.log T) ^ E0 := by
    calc
      (1 + Real.log U) ^ (E + 2) <= (B0 * Real.log T) ^ (E + 2) :=
        pow_le_pow_left₀ (zero_le_one.trans hbase1) hbase _
      _ <= (B0 * Real.log T) ^ E0 := pow_le_pow_right₀ hBLog1 hE2
  have hCsq : C ^ 2 <= (600 * Real.log T) ^ 2 :=
    pow_le_pow_left₀ hC0 hC 2
  have hpoly :
      (2 * (C ^ 2 * (12 * W ^ 2 *
          (1 + Real.log U) ^ (E + 2)))) * (Real.log T) ^ q <=
        K0 * (Real.log T) ^ (q + E0 + 2) := by
    calc
      (2 * (C ^ 2 * (12 * W ^ 2 *
          (1 + Real.log U) ^ (E + 2)))) * (Real.log T) ^ q <=
        (2 * ((600 * Real.log T) ^ 2 *
          (12 * W ^ 2 * (B0 * Real.log T) ^ E0))) *
            (Real.log T) ^ q := by gcongr
      _ = K0 * (Real.log T) ^ (q + E0 + 2) := by
        dsimp only [K0]
        rw [show (600 * Real.log T) ^ 2 =
          600 ^ 2 * (Real.log T) ^ 2 by rw [mul_pow]]
        rw [show (B0 * Real.log T) ^ E0 =
          B0 ^ E0 * (Real.log T) ^ E0 by rw [mul_pow]]
        rw [show (Real.log T) ^ (q + E0 + 2) =
          (Real.log T) ^ q * (Real.log T) ^ E0 *
            (Real.log T) ^ 2 by rw [pow_add, pow_add]]
        ring
  have hpowNonneg : 0 <= T ^ eps := Real.rpow_nonneg hTpos.le _
  calc
    (2 * (C ^ 2 * (12 * W ^ 2 *
        (1 + Real.log U) ^ (E + 2)))) * (Real.log T) ^ q <=
      K0 * (Real.log T) ^ (q + E0 + 2) := hpoly
    _ <= T ^ eps * T ^ eps :=
      mul_le_mul hconstT hlogPow (pow_nonneg hlog0 _) hpowNonneg
    _ = T ^ (1 / 25 : ℝ) := by
      rw [← Real.rpow_add hTpos]
      dsimp only [eps]
      congr 1
      norm_num

/-- A window-relevant degree-60 complement has upper edge at most the fixed width times `T^(8 : ℕ)`.
This derives the scale needed by fixed-cost absorption from box geometry; it is not an added
analytic hypothesis. -/
theorem windowRelevant_heathBrownBox_complement_upper_le_width_mul_T8
    {L X : ℕ} {T mu N0 : ℝ} (box : HeathBrownBoxChoice L X 60)
    (j : HeathBrownBoxFactorIndex 60 box.m)
    (hT : 1 < T) (hmu : mu <= 8)
    (hXscale : (X : ℝ) <= T ^ mu)
    (hbox : IsHeathBrownBoxWindowRelevant N0 X 60 box) :
    let I := {i : HeathBrownBoxFactorIndex 60 box.m //
      i ∈ (Finset.univ.erase j)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent box.a box.b box.q i
    (groupedDyadicUpper q : ℝ) <=
      maynardLowOrdinateComplementWidthConstant * T ^ (8 : ℕ) := by
  let comp : Finset (HeathBrownBoxFactorIndex 60 box.m) := Finset.univ.erase j
  let I := ↥comp
  letI : Fintype I := Subtype.fintype fun i => i ∈ comp
  let q : I → ℕ := fun i =>
    heathBrownBoxFactorExponent box.a box.b box.q i
  let A : ℝ := (groupedDyadicLower q : ℝ)
  let tau : ℝ := heathBrownBoxTotalExponent L X 60 T box
  let r : ℝ := dyadicLogExponent T
    (heathBrownBoxFactorExponent box.a box.b box.q j)
  let s : ℝ := ∑ i ∈ (Finset.univ.erase j),
    dyadicLogExponent T
      (heathBrownBoxFactorExponent box.a box.b box.q i)
  have htau : tau = r + s := by
    dsimp only [tau, r, s]
    exact heathBrownBox_totalExponent_eq_factor_add_complement box j
  have hr0 : 0 <= r := by
    dsimp only [r]
    exact dyadicLogExponent_nonneg hT _
  have hstau : s <= tau := by linarith
  have htaumu : tau <= mu :=
    windowRelevant_heathBrownBox_totalExponent_le hT hXscale box hbox
  have hs8 : s <= 8 := hstau.trans (htaumu.trans hmu)
  have hApow : A = T ^ s := by
    dsimp only [A, s, q, I, comp]
    exact heathBrownBoxFactor_complement_lower_eq_rpow box j hT
  have hA8 : A <= T ^ (8 : ℕ) := by
    rw [hApow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hT.le hs8
  have hwidth := heathBrownBoxFactor_complement_upper_le_width_mul_lower box j
  change (groupedDyadicUpper q : ℝ) <=
    maynardLowOrdinateComplementWidthConstant * T ^ (8 : ℕ)
  calc
    (groupedDyadicUpper q : ℝ) <=
        maynardLowOrdinateComplementWidthConstant * A := by
      simpa [A, q, I, comp] using hwidth
    _ <= maynardLowOrdinateComplementWidthConstant * T ^ (8 : ℕ) :=
      mul_le_mul_of_nonneg_left hA8
        (zero_le_one.trans maynardLowOrdinateComplementWidthConstant_one_le)

end RHTower.Sieve
