/-
Affine branches of the lower cusps adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.CuspAveragesAndBesselMellin

/-!
# Affine branches of the lower cusps

Unit lower cusps are indexed by a primary ideal and a coprime affine coordinate; the unit cusp
series is a sum of the affine branches `affineLowerTerm`. Principal residue fibers, the
once-ramified cusp scale and the scaled ramified cusp matrices.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid

/-- A unit and an elementary row operation preserve the integral level-three rows. -/
def unitLowerRowEquiv (u : Oˣ) : PrimitiveRow ≃ PrimitiveRow where
  toFun r := ⟨![(u : O) * r.1 0, r.1 1 - r.1 0], by
    change IsCoprime ((u : O) * r.1 0) (r.1 1 - r.1 0) ∧
      (3 : O) ∣ (u : O) * r.1 0 ∧ (3 : O) ∣ r.1 1 - r.1 0 - 1
    refine ⟨?_, r.2.2.1.mul_left _, ?_⟩
    · obtain ⟨a, b, hab⟩ := r.2.1
      refine ⟨(a + b) * (↑u⁻¹ : O), b, ?_⟩
      calc
        _ = (a + b) * (((↑u⁻¹ : O) * (u : O)) * r.1 0) + b * (r.1 1 - r.1 0) := by ring
        _ = (a + b) * r.1 0 + b * (r.1 1 - r.1 0) := by simp
        _ = 1 := by linear_combination hab
    · convert dvd_sub r.2.2.2 r.2.2.1 using 1 <;> ring⟩
  invFun r := ⟨![(↑u⁻¹ : O) * r.1 0, r.1 1 + (↑u⁻¹ : O) * r.1 0], by
    change IsCoprime ((↑u⁻¹ : O) * r.1 0) (r.1 1 + (↑u⁻¹ : O) * r.1 0) ∧
      (3 : O) ∣ (↑u⁻¹ : O) * r.1 0 ∧ (3 : O) ∣ r.1 1 + (↑u⁻¹ : O) * r.1 0 - 1
    refine ⟨?_, r.2.2.1.mul_left _, ?_⟩
    · obtain ⟨a, b, hab⟩ := r.2.1
      refine ⟨a * (u : O) - b, b, ?_⟩
      calc
        _ = a * (((u : O) * (↑u⁻¹ : O)) * r.1 0) + b * r.1 1 := by ring
        _ = 1 := by simpa using hab
    · convert dvd_add r.2.2.2 (r.2.2.1.mul_left (↑u⁻¹ : O)) using 1 <;> ring⟩
  left_inv r := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [← mul_assoc]
  right_inv r := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [← mul_assoc]

/-- Index a unit lower cusp by a primary ideal and one coprime affine coordinate. -/
def unitLowerDataEquiv (u : Oˣ) : OppositeData ≃ PrimitiveRow :=
  oppositeDataEquiv.trans (unitLowerRowEquiv u)

lemma unitLowerDataEquiv_row (u : Oˣ) (p : OppositeData) :
    (unitLowerDataEquiv u p).1 =
      ![-3 * (u : O) * p.2.1, primaryIdealGenerator p.1.1 + 3 * p.2.1] := by
  funext i
  fin_cases i <;> simp [unitLowerDataEquiv, unitLowerRowEquiv, oppositeDataEquiv,
    oppositeDataToPrimitive, Equiv.ofBijective_apply] <;> ring

lemma unitLowerDenominator_primary (p : OppositeData) :
    lambda ^ 2 ∣ primaryIdealGenerator p.1.1 + 3 * p.2.1 - 1 := by
  convert dvd_add (primaryIdealGenerator_spec p.1.1 p.1.2).2
    (lambda_sq_dvd_three.mul_right p.2.1) using 1 <;> ring

lemma unitLower_row_phase (u : Oˣ) (p : OppositeData) :
    (cosetCharacter (primitiveRowEquiv.symm (unitLowerDataEquiv u p)))⁻¹ =
      ringComplex (symbol (u : O) (primaryIdealGenerator p.1.1 + 3 * p.2.1)) *
        ringComplex (symbol (primaryIdealGenerator p.1.1 + 3 * p.2.1) (primaryIdealGenerator p.1.1)) := by
  rw [inverse_cosetCharacter_eq_row_symbol, primitiveRowEquiv_symm_row, unitLowerDataEquiv_row]
  change ringComplex (symbol (-3 * (u : O) * p.2.1) (primaryIdealGenerator p.1.1 + 3 * p.2.1)) = _
  rw [symbol_congr (show primaryIdealGenerator p.1.1 + 3 * p.2.1 ∣
    -3 * (u : O) * p.2.1 - (u : O) * primaryIdealGenerator p.1.1 from ⟨-(u : O), by ring⟩),
    symbol_mul_numerator, map_mul,
    symbol_reciprocity _ _ (primaryIdealGenerator_spec p.1.1 p.1.2).2 (unitLowerDenominator_primary p)]

lemma rowOperator_lowerCusp (t : O) (r : Fin 2 → ℂ) :
    rowOperator (integralComplexMatrix (lowerCuspMatrix t)) r = ![r 0 + ringComplex t * r 1, r 1] := by
  rw [rowOperator_apply]
  funext i
  fin_cases i <;> simp [integralComplexMatrix, lowerCuspMatrix, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two, mul_comm]

/-- A primary affine branch of a lower-cusp Eisenstein series. -/
def affineLowerTerm (q r : O) (z : ℂ) (v : ℝ) (s : ℂ) (a d : O) : ℂ :=
  (ringComplex (symbol r d) * ringComplex (symbol d a)) *
    ((v / (‖ringComplex (q * a) * z + ringComplex d‖ ^ 2 +
      ‖ringComplex (q * a)‖ ^ 2 * v ^ 2) : ℝ) : ℂ) ^ s

lemma unitLower_summand (u : Oˣ) (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (p : OppositeData) :
    summand (integralComplexMatrix (lowerCuspMatrix (u : O)) * upperSection z v hv) s
      (primitiveRowEquiv.symm (unitLowerDataEquiv u p)) =
      affineLowerTerm (u : O) (u : O) z v s (primaryIdealGenerator p.1.1)
        (primaryIdealGenerator p.1.1 + 3 * p.2.1) := by
  let r : Fin 2 → ℂ := ![ringComplex ((u : O) * primaryIdealGenerator p.1.1),
    ringComplex (primaryIdealGenerator p.1.1 + 3 * p.2.1)]
  have hr : rowOperator (integralComplexMatrix (lowerCuspMatrix (u : O)))
      (embeddedRow (primitiveRowEquiv.symm (unitLowerDataEquiv u p))) = r := by
    rw [embeddedRow, primitiveRowEquiv_symm_row, unitLowerDataEquiv_row, rowOperator_lowerCusp]
    funext i
    fin_cases i <;> simp [r, map_mul, map_add] <;> ring
  have hr0 : r ≠ 0 := by
    intro hh
    exact ringComplex_ne_zero (mul_ne_zero u.ne_zero p.1.2) (congrFun hh 0)
  have hp := heightDenominator_pos z v hv r hr0
  rw [summand, ← rowOperator_mul, hr, rowEnergy_upperSection, unitLower_row_phase]
  change _ = _ * ((v / heightDenominator z v r : ℝ) : ℂ) ^ s
  rw [show ((v / heightDenominator z v r : ℝ) : ℂ) =
    (((heightDenominator z v r / v : ℝ) : ℂ))⁻¹ by simp only [Complex.ofReal_div, inv_div],
    inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le), Complex.cpow_neg]

/-- The unit cusp series is a sum of the native affine branches. -/
theorem unitLowerEisenstein_eq_rows (u : Oˣ) (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) :
    eisenstein (integralComplexMatrix (lowerCuspMatrix (u : O)) * upperSection z v hv) s =
      ∑' p : OppositeData, affineLowerTerm (u : O) (u : O) z v s (primaryIdealGenerator p.1.1)
        (primaryIdealGenerator p.1.1 + 3 * p.2.1) := by
  let e := (unitLowerDataEquiv u).trans primitiveRowEquiv.symm
  change (∑' x : CuspCosets, summand _ s x) = _
  rw [← e.tsum_eq (fun x => summand _ s x)]
  exact tsum_congr (unitLower_summand u z v hv s)

lemma affineLowerTerm_eq_shifted (q r : O) (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ)
    (a d : O) (ha : a ≠ 0) (hq : q ≠ 0) :
    affineLowerTerm q r z v s a d =
      (ringComplex (symbol r d) * ringComplex (symbol d a) *
        ((‖ringComplex (q * a)‖ ^ 2 : ℝ) : ℂ) ^ (-s)) *
          shiftedHeightKernel v s (ringComplex d / ringComplex (q * a)) z := by
  rw [affineLowerTerm, rowHeight_eq_shiftedHeightKernel z v hv s (q * a) d (mul_ne_zero hq ha)]
  ring

lemma affineLowerTerm_integrable (q r : O) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (a d : O) (ha : a ≠ 0) (hq : q ≠ 0) :
    Integrable (fun z => affineLowerTerm q r z v s a d) := by
  simp_rw [affineLowerTerm_eq_shifted q r _ v hv s a d ha hq]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma affineLowerTerm_fourier_integral (q r : O) (v : ℝ) (hv : 0 < v) (s freq : ℂ)
    (a d : O) (ha : a ≠ 0) (hq : q ≠ 0) :
    (∫ z : ℂ, affineLowerTerm q r z v s a d * tracePhase (-freq * z)) =
      ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (freq * v)) *
        ((‖ringComplex (q * a)‖ ^ 2 : ℝ) : ℂ) ^ (-s) *
          ((ringComplex (symbol r d) * ringComplex (symbol d a)) *
            tracePhase (freq * ringComplex d / ringComplex (q * a))) := by
  simp_rw [affineLowerTerm_eq_shifted q r _ v hv s a d ha hq, mul_assoc]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    traceIntegral_shiftedHeightKernel v hv s (ringComplex d / ringComplex (q * a)) freq]
  ring

/-- A principal residue fiber is the affine lattice represented by its chosen residue. -/
def principalResidueFiberMap (q : O) (r : O ⧸ Ideal.span {q}) (n : O) :
    ((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}) := by
  refine ⟨principalResidueRep q r + q * n, ?_⟩
  change Ideal.Quotient.mk _ (principalResidueRep q r + q * n) = r
  rw [map_add, map_mul, principalResidueRep_spec,
    show Ideal.Quotient.mk (Ideal.span {q}) q = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton q)), zero_mul, add_zero]

def principalResidueFiberEquiv (q : O) (hq : q ≠ 0) (r : O ⧸ Ideal.span {q}) :
    O ≃ ((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}) := Equiv.ofBijective
  (principalResidueFiberMap q r) (by
    constructor
    · intro m n he
      exact mul_left_cancel₀ hq (add_left_cancel (congrArg Subtype.val he))
    · rintro ⟨x, hx⟩
      change Ideal.Quotient.mk (Ideal.span {q}) x = r at hx
      have hd : q ∣ x - principalResidueRep q r := Ideal.mem_span_singleton.mp
        ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (hx.trans (principalResidueRep_spec q r).symm))
      obtain ⟨n, hn⟩ := hd
      refine ⟨n, Subtype.ext ?_⟩
      change principalResidueRep q r + q * n = x
      linear_combination -hn)

lemma finite_index_period_shift (q : O) (hq : q ≠ 0) (r : O ⧸ Ideal.span {q}) (n : O) (z : ℂ) :
    z + 3 * ringComplex (principalResidueRep q r + q * n) / ringComplex q =
      (z + 3 * ringComplex n) + 3 * ringComplex (principalResidueRep q r) / ringComplex q := by
  simp only [map_add, map_mul]
  field_simp [ringComplex_ne_zero hq] <;> ring

/-- A lattice enlarged by a principal denominator covers the plane with multiplicity equal to its norm. -/
lemma finite_index_period_lintegral (q : O) (hq : q ≠ 0) (f : ℂ → ℝ≥0∞) :
    (∑' n : O, ∫⁻ z in periodDomain, f (z + 3 * ringComplex n / ringComplex q)) =
      (Ideal.absNorm (Ideal.span {q}) : ℝ≥0∞) * (∫⁻ z : ℂ, f z) := by
  letI : Finite (O ⧸ Ideal.span {q}) := (Ideal.span {q}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr hq)
  letI : Fintype (O ⧸ Ideal.span {q}) := Fintype.ofFinite _
  let I : O → ℝ≥0∞ := fun n => ∫⁻ z in periodDomain, f (z + 3 * ringComplex n / ringComplex q)
  have hinner (r : O ⧸ Ideal.span {q}) :
      (∑' n : ((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}), I n.1) = ∫⁻ z : ℂ, f z := by
    rw [← (principalResidueFiberEquiv q hq r).tsum_eq]
    change (∑' n : O, ∫⁻ z in periodDomain,
      f (z + 3 * ringComplex (principalResidueRep q r + q * n) / ringComplex q)) = _
    simp_rw [finite_index_period_shift q hq]
    rw [← lintegral_eq_period_lintegrals (fun z =>
      f (z + 3 * ringComplex (principalResidueRep q r) / ringComplex q))]
    exact lintegral_add_right_eq_self f _
  change (∑' n : O, I n) = _
  rw [← ENNReal.tsum_fiberwise I (Ideal.Quotient.mk (Ideal.span {q}))]
  simp only [hinner, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  change (Fintype.card (O ⧸ Ideal.span {q}) : ℝ≥0∞) = (Nat.card (O ⧸ Ideal.span {q}) : ℝ≥0∞)
  rw [Nat.card_eq_fintype_card]

lemma finite_index_period_integrals_summable (q : O) (hq : q ≠ 0) (f : ℂ → ℂ) (hf : Integrable f) :
    Summable (fun n : O => ∫ z in periodDomain, f (z + 3 * ringComplex n / ringComplex q)) := by
  apply Summable.of_enorm
  apply ne_of_lt
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => enorm_integral_le_lintegral_enorm _))
  rw [finite_index_period_lintegral q hq (fun z => ‖f z‖ₑ)]
  exact ENNReal.mul_lt_top (by simp) hf.hasFiniteIntegral

/-- Unfold the finite-index lattice, retaining its exact covering multiplicity. -/
theorem finite_index_period_unfold (q : O) (hq : q ≠ 0) (f : ℂ → ℂ) (hf : Integrable f) :
    (∑' n : O, ∫ z in periodDomain, f (z + 3 * ringComplex n / ringComplex q)) =
      (Ideal.absNorm (Ideal.span {q}) : ℂ) * (∫ z : ℂ, f z) := by
  letI : Finite (O ⧸ Ideal.span {q}) := (Ideal.span {q}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr hq)
  letI : Fintype (O ⧸ Ideal.span {q}) := Fintype.ofFinite _
  let I : O → ℂ := fun n => ∫ z in periodDomain, f (z + 3 * ringComplex n / ringComplex q)
  have hinner (r : O ⧸ Ideal.span {q}) :
      (∑' n : ((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}), I n.1) = ∫ z : ℂ, f z := by
    rw [← (principalResidueFiberEquiv q hq r).tsum_eq]
    change (∑' n : O, ∫ z in periodDomain,
      f (z + 3 * ringComplex (principalResidueRep q r + q * n) / ringComplex q)) = _
    simp_rw [finite_index_period_shift q hq]
    rw [← integral_eq_period_integrals _ (hf.comp_add_right _)]
    exact integral_add_right_eq_self f _
  have hs := (finite_index_period_integrals_summable q hq f hf).hasSum.tsum_fiberwise
    (Ideal.Quotient.mk (Ideal.span {q}))
  change HasSum (fun r => ∑' n : ((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}), I n.1) (∑' n, I n) at hs
  change (∑' n : O, I n) = _
  rw [← hs.tsum_eq]
  simp only [hinner, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  change (Fintype.card (O ⧸ Ideal.span {q}) : ℂ) = (Nat.card (O ⧸ Ideal.span {q}) : ℂ)
  rw [Nat.card_eq_fintype_card]

lemma affineCuspTwistedCoefficient_add (h h1 q a k x m : O) (u : Oˣ) (n : ℕ)
    (ha : a ≠ 0) (hap : lambda ^ 2 ∣ a - 1) (hq : q ≠ 0)
    (hh : h = q * h1) (hk : 3 * k = h1 + ramifiedArithmeticPhase u n * a) :
    (ringComplex (symbol ((u : O) * lambda ^ n) (a + 3 * (x + a * m))) *
      ringComplex (symbol (a + 3 * (x + a * m)) a)) *
        tracePhase (ninthCuspFrequency h * ringComplex (a + 3 * (x + a * m)) / ringComplex (q * a)) =
    (ringComplex (symbol ((u : O) * lambda ^ n) (a + 3 * x)) * ringComplex (symbol (a + 3 * x) a)) *
      tracePhase (ninthCuspFrequency h * ringComplex (a + 3 * x) / ringComplex (q * a)) := by
  rw [affineCuspGaussTerm_factor h h1 q a k (x + a * m) u n ha hap hq hh hk,
    affineCuspGaussTerm_factor h h1 q a k x u n ha hap hq hh hk,
    symbol_congr (show a ∣ x + a * m - x from ⟨m, by ring⟩),
    residueAdditive_three_congr k a (x + a * m) x ha ⟨m, by ring⟩]

lemma affineLowerTerm_weighted_translate (h h1 q a k x m : O) (u : Oˣ) (n : ℕ)
    (ha : a ≠ 0) (hap : lambda ^ 2 ∣ a - 1) (hq : q ≠ 0)
    (hh : h = q * h1) (hk : 3 * k = h1 + ramifiedArithmeticPhase u n * a)
    (z : ℂ) (v : ℝ) (s : ℂ) :
    affineLowerTerm q ((u : O) * lambda ^ n) z v s a (a + 3 * (x + a * m)) *
        tracePhase (-ninthCuspFrequency h * z) =
      affineLowerTerm q ((u : O) * lambda ^ n) (z + 3 * ringComplex m / ringComplex q) v s a (a + 3 * x) *
        tracePhase (-ninthCuspFrequency h * (z + 3 * ringComplex m / ringComplex q)) := by
  let c1 := ringComplex (symbol ((u : O) * lambda ^ n) (a + 3 * (x + a * m))) *
    ringComplex (symbol (a + 3 * (x + a * m)) a)
  let c0 := ringComplex (symbol ((u : O) * lambda ^ n) (a + 3 * x)) * ringComplex (symbol (a + 3 * x) a)
  let B := ninthCuspFrequency h * ringComplex (a + 3 * x) / ringComplex (q * a)
  let Q := ninthCuspFrequency h * (3 * ringComplex m / ringComplex q)
  have harg : ninthCuspFrequency h * ringComplex (a + 3 * (x + a * m)) / ringComplex (q * a) = B + Q := by
    dsimp [B, Q]
    simp only [map_add, map_mul, map_ofNat]
    field_simp [ringComplex_ne_zero hq, ringComplex_ne_zero ha] <;> ring
  have he := affineCuspTwistedCoefficient_add h h1 q a k x m u n ha hap hq hh hk
  change c1 * tracePhase (ninthCuspFrequency h * ringComplex (a + 3 * (x + a * m)) / ringComplex (q * a)) =
    c0 * tracePhase B at he
  rw [harg, AddChar.map_add_eq_mul] at he
  have heB : tracePhase B ≠ 0 := Complex.exp_ne_zero _
  have hmult : c1 * tracePhase Q = c0 := by
    apply mul_right_cancel₀ heB
    calc
      _ = c1 * (tracePhase B * tracePhase Q) := by ring
      _ = _ := he
  have hsolve : c1 = c0 * tracePhase (-Q) := by
    rw [← hmult, mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, mul_one]
  have hrow : ringComplex (q * a) * z + ringComplex (a + 3 * (x + a * m)) =
      ringComplex (q * a) * (z + 3 * ringComplex m / ringComplex q) + ringComplex (a + 3 * x) := by
    simp only [map_add, map_mul, map_ofNat]
    field_simp [ringComplex_ne_zero hq] <;> ring
  change c1 * ((v / (‖ringComplex (q * a) * z + ringComplex (a + 3 * (x + a * m))‖ ^ 2 +
    ‖ringComplex (q * a)‖ ^ 2 * v ^ 2) : ℝ) : ℂ) ^ s * tracePhase (-ninthCuspFrequency h * z) = _
  rw [hsolve, hrow]
  unfold affineLowerTerm
  rw [show -ninthCuspFrequency h * (z + 3 * ringComplex m / ringComplex q) =
      -Q + (-ninthCuspFrequency h * z) by dsimp [Q]; ring, AddChar.map_add_eq_mul]
  dsimp only [c0]
  ring

lemma affineLowerIntegral_sum_translate (h h1 q a k x : O) (u : Oˣ) (n : ℕ)
    (ha : a ≠ 0) (hap : lambda ^ 2 ∣ a - 1) (hq : q ≠ 0)
    (hh : h = q * h1) (hk : 3 * k = h1 + ramifiedArithmeticPhase u n * a)
    (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re) :
    (∑' m : O, ∫ z in periodDomain,
      affineLowerTerm q ((u : O) * lambda ^ n) z v s a (a + 3 * (x + a * m)) *
        tracePhase (-ninthCuspFrequency h * z)) =
      (Ideal.absNorm (Ideal.span {q}) : ℂ) *
        ∫ z : ℂ, affineLowerTerm q ((u : O) * lambda ^ n) z v s a (a + 3 * x) *
          tracePhase (-ninthCuspFrequency h * z) := by
  have hint := trace_mul_integrable (fun z => affineLowerTerm q ((u : O) * lambda ^ n) z v s a (a + 3 * x))
    (affineLowerTerm_integrable q _ v hv s hs a (a + 3 * x) ha hq) (ninthCuspFrequency h)
  rw [← finite_index_period_unfold q hq _ hint]
  apply tsum_congr
  intro m
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => affineLowerTerm_weighted_translate h h1 q a k x m u n ha hap hq hh hk z v s)

/-- Horizontal Fourier integral of an affine ramified row. -/
def affineLowerFourierTerm (q r h : O) (v : ℝ) (s : ℂ) (a x : O) : ℂ :=
  ∫ z in periodDomain, affineLowerTerm q r z v s a (a + 3 * x) * tracePhase (-ninthCuspFrequency h * z)

lemma affineCuspFrequency_lift (h1 : O) (u : Oˣ) (n : ℕ) (I : GoodIdeal)
    (hfreq : (3 : O) ∣ h1 + ramifiedArithmeticPhase u n) :
    ∃ k : O, 3 * k = h1 + ramifiedArithmeticPhase u n * primaryIdealGenerator I.1 := by
  have hd := dvd_add hfreq ((three_dvd_primary_sub_one _
    (primaryIdealGenerator_spec I.1 I.2).2).mul_left (ramifiedArithmeticPhase u n))
  have he : (3 : O) ∣ h1 + ramifiedArithmeticPhase u n * primaryIdealGenerator I.1 := by
    convert hd using 1 <;> ring
  obtain ⟨k, hk⟩ := he
  exact ⟨k, hk.symm⟩

lemma affineDenominator_fourier (h h1 q a k : O) (u : Oˣ) (n : ℕ)
    (ha : a ≠ 0) (hap : lambda ^ 2 ∣ a - 1) (hq : q ≠ 0)
    (hh : h = q * h1) (hk : 3 * k = h1 + ramifiedArithmeticPhase u n * a)
    (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (hsum : Summable (fun x : CoprimeElement a => affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s a x.1)) :
    (∑' x : CoprimeElement a, affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s a x.1) =
      (Ideal.absNorm (Ideal.span {q}) : ℂ) *
        ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (ninthCuspFrequency h * v)) *
          ((‖ringComplex (q * a)‖ ^ 2 : ℝ) : ℂ) ^ (-s) * ramifiedAffineGauss h q a u n := by
  let F : CoprimeElement a → ℂ := fun x => affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s a x.1
  let e := cubicResidueElementEquiv a ha
  have hp : Summable (fun p : CubicUnitResidue a × O => F (e p)) := e.summable_iff.mpr hsum
  change (∑' x, F x) = _
  rw [← e.tsum_eq F, hp.tsum_prod]
  change (∑' x : CubicUnitResidue a, ∑' m : O,
    affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s a (principalResidueRep a x.1 + a * m)) = _
  have hinner (x : CubicUnitResidue a) :
      (∑' m : O, affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s a
        (principalResidueRep a x.1 + a * m)) =
      ((Ideal.absNorm (Ideal.span {q}) : ℂ) *
        ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (ninthCuspFrequency h * v)) *
          ((‖ringComplex (q * a)‖ ^ 2 : ℝ) : ℂ) ^ (-s)) *
        ((ringComplex (symbol ((u : O) * lambda ^ n) (a + 3 * principalResidueRep a x.1)) *
          ringComplex (symbol (a + 3 * principalResidueRep a x.1) a)) *
            tracePhase (ninthCuspFrequency h * ringComplex (a + 3 * principalResidueRep a x.1) / ringComplex (q * a))) := by
    unfold affineLowerFourierTerm
    rw [affineLowerIntegral_sum_translate h h1 q a k _ u n ha hap hq hh hk v hv s hs,
      affineLowerTerm_fourier_integral q _ v hv s _ a _ ha hq]
    ring
  simp_rw [hinner]
  rw [tsum_mul_left]
  rfl

lemma affineCusp_norm_factor (q : O) (s : ℂ) (I : GoodIdeal) :
    ((‖ringComplex (q * primaryIdealGenerator I.1)‖ ^ 2 : ℝ) : ℂ) ^ (-s) =
      ((‖ringComplex q‖ ^ 2 : ℝ) : ℂ) ^ (-s) * unramifiedNormWeight s I.1 := by
  rw [unramifiedNormWeight_of_good s _ I.2, map_mul, norm_mul, mul_pow, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (sq_nonneg _) (sq_nonneg _),
    ringComplex_norm_sq_eq_absNorm_span (primaryIdealGenerator I.1),
    (primaryIdealGenerator_spec I.1 I.2).1, Complex.ofReal_natCast]

/-- Every active affine cusp branch is one unramified Gauss series with an explicit scale. -/
theorem affineCusp_branch_fourier (h h1 q : O) (u : Oˣ) (n : ℕ) (hq : q ≠ 0)
    (hh : h = q * h1) (hfreq : (3 : O) ∣ h1 + ramifiedArithmeticPhase u n)
    (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (hsum : Summable (fun p : OppositeData => affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s
      (primaryIdealGenerator p.1.1) p.2.1)) :
    (∑' p : OppositeData, affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s
      (primaryIdealGenerator p.1.1) p.2.1) =
      (Ideal.absNorm (Ideal.span {q}) : ℂ) * ((‖ringComplex q‖ ^ 2 : ℝ) : ℂ) ^ (-s) *
        ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (ninthCuspFrequency h * v)) *
          tracePhase (ninthCuspFrequency h / ringComplex q) *
            unramifiedCubicGaussSeries s (3 * ((u : O) * lambda ^ n) ^ 2 * h1) := by
  rw [hsum.tsum_sigma]
  have hI (I : GoodIdeal) :
      (∑' x : CoprimeElement (primaryIdealGenerator I.1), affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s
        (primaryIdealGenerator I.1) x.1) =
      ((Ideal.absNorm (Ideal.span {q}) : ℂ) * ((‖ringComplex q‖ ^ 2 : ℝ) : ℂ) ^ (-s) *
        ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (ninthCuspFrequency h * v)) *
          tracePhase (ninthCuspFrequency h / ringComplex q)) *
        (unramifiedNormWeight s I.1 *
          cubicUnitGaussSum (3 * ((u : O) * lambda ^ n) ^ 2 * h1) (primaryIdealGenerator I.1)) := by
    obtain ⟨k, hk⟩ := affineCuspFrequency_lift h1 u n I hfreq
    rw [affineDenominator_fourier h h1 q _ k u n I.2 (primaryIdealGenerator_spec I.1 I.2).2
      hq hh hk v hv s hs (hsum.sigma_factor I),
      ramifiedAffineGauss_eq_unramified h h1 q _ k u n I.2 (primaryIdealGenerator_spec I.1 I.2).2 hq hh hk,
      affineCusp_norm_factor]
    ring
  simp_rw [hI]
  rw [tsum_mul_left]
  rfl

lemma hasSum_unitLowerIntegrals (u : Oˣ) (v : ℝ) (hv : 0 < v) (s : ℂ) (h : O) (hs : 2 < s.re) :
    HasSum (fun p : OppositeData => affineLowerFourierTerm (u : O) (u : O) h v s
      (primaryIdealGenerator p.1.1) p.2.1)
      (∫ z in periodDomain, eisenstein (integralComplexMatrix (lowerCuspMatrix (u : O)) * upperSection z v hv) s *
        tracePhase (-ninthCuspFrequency h * z)) := by
  let e := (unitLowerDataEquiv u).trans primitiveRowEquiv.symm
  have he := e.hasSum_iff.mpr (hasSum_integral_fixed_left_Eisenstein
    (integralComplexMatrix (lowerCuspMatrix (u : O))) v hv s (ninthCuspFrequency h) hs)
  apply he.congr_fun
  intro p
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only [affineLowerFourierTerm, e, Equiv.trans_apply, Function.comp_apply]
    rw [unitLower_summand])

/-- The actual unit-cusp Eisenstein coefficient equals its unramified Gauss series. -/
theorem unitLowerEisenstein_fourier (u : Oˣ) (h h1 : O) (hh : h = (u : O) * h1)
    (hfreq : (3 : O) ∣ h1 + ramifiedArithmeticPhase u 0)
    (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    (∫ z in periodDomain, eisenstein (integralComplexMatrix (lowerCuspMatrix (u : O)) * upperSection z v hv) s *
        tracePhase (-ninthCuspFrequency h * z)) =
      ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (ninthCuspFrequency h * v)) *
        tracePhase (ninthCuspFrequency h / ringComplex (u : O)) *
          unramifiedCubicGaussSeries s (3 * (u : O) ^ 2 * h1) := by
  have hsum := hasSum_unitLowerIntegrals u v hv s h hs
  rw [← hsum.tsum_eq]
  have he := affineCusp_branch_fourier h h1 (u : O) u 0 u.ne_zero hh hfreq v hv s (by linarith)
    (by simpa only [pow_zero, mul_one] using hsum.summable)
  simpa only [pow_zero, mul_one, norm_ringComplex_unit, one_pow, Complex.ofReal_one, Complex.one_cpow,
    Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top, Nat.cast_one, one_mul] using he

/-- The diagonal matrix of an Eisenstein unit preserves heights. -/
def unitCuspDiagonal (u : Oˣ) : SL(2, O) :=
  ⟨!![(u : O), 0; 0, (↑u⁻¹ : O)], by simp [Matrix.det_fin_two]⟩

lemma rowOperator_unitDiagonal (u : Oˣ) (r : Fin 2 → ℂ) :
    rowOperator (integralComplexMatrix (unitCuspDiagonal u)) r =
      ![ringComplex (u : O) * r 0, ringComplex (↑u⁻¹ : O) * r 1] := by
  rw [rowOperator_apply]
  funext i
  fin_cases i <;> simp [integralComplexMatrix, unitCuspDiagonal, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two, mul_comm]

lemma rowEnergy_complex_smul (c : ℂ) (r : Fin 2 → ℂ) :
    rowEnergy (c • r) = ‖c‖ ^ 2 * rowEnergy r := by
  simp only [rowEnergy, Pi.smul_apply, norm_smul, mul_pow, mul_add]

/-- Absorb a unit diagonal into the cubic numerator while leaving the affine height unchanged. -/
lemma diagonal_unit_summand (u t : Oˣ) (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (p : OppositeData) :
    summand (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (t : O)) * upperSection z v hv) s
      (primitiveRowEquiv.symm (unitLowerDataEquiv (u⁻¹ ^ 2 * t) p)) =
      affineLowerTerm (t : O) ((↑u⁻¹ : O) ^ 2 * (t : O)) z v s (primaryIdealGenerator p.1.1)
        (primaryIdealGenerator p.1.1 + 3 * p.2.1) := by
  let r : Fin 2 → ℂ := ![ringComplex ((t : O) * primaryIdealGenerator p.1.1),
    ringComplex (primaryIdealGenerator p.1.1 + 3 * p.2.1)]
  have hunit : ringComplex (u : O) * ringComplex (↑u⁻¹ : O) = 1 := by
    rw [← map_mul]
    simp
  have hr : rowOperator (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (t : O)))
      (embeddedRow (primitiveRowEquiv.symm (unitLowerDataEquiv (u⁻¹ ^ 2 * t) p))) =
        ringComplex (↑u⁻¹ : O) • r := by
    rw [← rowOperator_mul, embeddedRow, primitiveRowEquiv_symm_row, unitLowerDataEquiv_row,
      rowOperator_unitDiagonal, rowOperator_lowerCusp]
    funext i
    fin_cases i
    · change ringComplex (u : O) * ringComplex (-3 * (↑(u⁻¹ ^ 2 * t) : O) * p.2.1) +
        ringComplex (t : O) * (ringComplex (↑u⁻¹ : O) *
          ringComplex (primaryIdealGenerator p.1.1 + 3 * p.2.1)) =
        ringComplex (↑u⁻¹ : O) * ringComplex ((t : O) * primaryIdealGenerator p.1.1)
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, map_neg, map_add, map_ofNat]
      linear_combination -3 * ringComplex (↑u⁻¹ : O) * ringComplex (t : O) * ringComplex p.2.1 * hunit
    · simp [r]
  have hr0 : r ≠ 0 := by
    intro hh
    exact ringComplex_ne_zero (mul_ne_zero t.ne_zero p.1.2) (congrFun hh 0)
  have hp := heightDenominator_pos z v hv r hr0
  rw [summand, ← rowOperator_mul, hr, map_smul, rowEnergy_complex_smul,
    norm_ringComplex_unit, one_pow, one_mul, rowEnergy_upperSection, unitLower_row_phase]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  change _ = _ * ((v / heightDenominator z v r : ℝ) : ℂ) ^ s
  rw [show ((v / heightDenominator z v r : ℝ) : ℂ) =
    (((heightDenominator z v r / v : ℝ) : ℂ))⁻¹ by simp only [Complex.ofReal_div, inv_div],
    inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le), Complex.cpow_neg]

lemma hasSum_diagonal_unit_integrals (u t : Oˣ) (v : ℝ) (hv : 0 < v) (s : ℂ) (h : O) (hs : 2 < s.re) :
    HasSum (fun p : OppositeData => affineLowerFourierTerm (t : O) ((↑u⁻¹ : O) ^ 2 * (t : O)) h v s
      (primaryIdealGenerator p.1.1) p.2.1)
      (∫ z in periodDomain, eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
        integralComplexMatrix (lowerCuspMatrix (t : O)) * upperSection z v hv) s *
          tracePhase (-ninthCuspFrequency h * z)) := by
  let e := (unitLowerDataEquiv (u⁻¹ ^ 2 * t)).trans primitiveRowEquiv.symm
  have he := e.hasSum_iff.mpr (hasSum_integral_fixed_left_Eisenstein
    (integralComplexMatrix (unitCuspDiagonal u) * integralComplexMatrix (lowerCuspMatrix (t : O)))
      v hv s (ninthCuspFrequency h) hs)
  apply he.congr_fun
  intro p
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only [affineLowerFourierTerm, e, Equiv.trans_apply, Function.comp_apply]
    rw [diagonal_unit_summand])

/-- A unit diagonal changes the cubic Gauss frequency through its fourth inverse power. -/
theorem diagonal_unit_eisenstein_fourier (u t : Oˣ) (h h1 : O)
    (hh : h = (t : O) * h1) (hfreq : (3 : O) ∣ h1 + ramifiedArithmeticPhase (u⁻¹ ^ 2 * t) 0)
    (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    (∫ z in periodDomain, eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (t : O)) * upperSection z v hv) s *
        tracePhase (-ninthCuspFrequency h * z)) =
      ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (ninthCuspFrequency h * v)) *
        tracePhase (ninthCuspFrequency h / ringComplex (t : O)) *
          unramifiedCubicGaussSeries s (3 * ((↑u⁻¹ : O) ^ 2 * (t : O)) ^ 2 * h1) := by
  have hsum := hasSum_diagonal_unit_integrals u t v hv s h hs
  rw [← hsum.tsum_eq]
  have he := affineCusp_branch_fourier h h1 (t : O) (u⁻¹ ^ 2 * t) 0 t.ne_zero hh hfreq v hv s (by linarith)
    (by simpa only [pow_zero, mul_one, Units.val_mul, Units.val_pow_eq_pow_val] using hsum.summable)
  simpa only [pow_zero, mul_one, Units.val_mul, Units.val_pow_eq_pow_val,
    norm_ringComplex_unit, one_pow, Complex.ofReal_one, Complex.one_cpow,
    Ideal.span_singleton_eq_top.mpr t.isUnit, Ideal.absNorm_top, Nat.cast_one, one_mul] using he

/-- The six units are the signed powers of the primitive cubic root. -/
lemma unit_eq_sign_omega (u : Oˣ) :
    ∃ j : Fin 3, (u : O) = omega ^ j.val ∨ (u : O) = -(omega ^ j.val) := by
  letI : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : O) = omega := rfl
  have hu : u ∈ ([1, -1, η, -η, η ^ 2, -η ^ 2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with h | h | h | h | h | h
  · exact ⟨0, Or.inl (by simp [h])⟩
  · exact ⟨0, Or.inr (by simp [h])⟩
  · exact ⟨1, Or.inl (by simp [h, hη])⟩
  · exact ⟨1, Or.inr (by simp [h, hη])⟩
  · exact ⟨2, Or.inl (by simp [h, hη])⟩
  · exact ⟨2, Or.inr (by simp [h, hη])⟩

abbrev HalfPrimary := {b : O // lambda ∣ b - 1}

lemma halfPrimary_omega_pow (j : ℕ) : lambda ∣ omega ^ j - 1 := by
  simpa only [lambda_def, one_pow] using sub_dvd_pow_sub_pow omega (1 : O) j

lemma halfPrimary_not_negative (j : ℕ) : ¬lambda ∣ -(omega ^ j) - 1 := by
  intro h
  apply lambda_not_dvd_two
  convert dvd_neg.mpr (dvd_add h (halfPrimary_omega_pow j)) using 1 <;> ring

lemma halfPrimary_not_dvd (b : HalfPrimary) : ¬lambda ∣ b.1 := by
  intro h
  apply residue_lambda_prime.2.1
  apply isUnit_of_dvd_one
  convert dvd_sub h b.2 using 1 <;> ring

/-- Congruence modulo the ramified prime leaves exactly three primary associates. -/
def halfPrimaryFromIdeal (p : Fin 3 × GoodIdeal) : HalfPrimary :=
  ⟨omega ^ p.1.val * primaryIdealGenerator p.2.1, by
    have ha : lambda ∣ primaryIdealGenerator p.2.1 - 1 :=
      (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans (primaryIdealGenerator_spec p.2.1 p.2.2).2
    convert dvd_add ((halfPrimary_omega_pow p.1.val).mul_right (primaryIdealGenerator p.2.1)) ha
      using 1 <;> ring⟩

lemma halfPrimaryFromIdeal_injective : Function.Injective halfPrimaryFromIdeal := by
  intro p q hpq
  have he : omega ^ p.1.val * primaryIdealGenerator p.2.1 =
      omega ^ q.1.val * primaryIdealGenerator q.2.1 := congrArg Subtype.val hpq
  have hunit (j : Fin 3) : IsUnit (omega ^ j.val) := (omega_primitive.isUnit (by decide)).pow _
  have hi : p.2 = q.2 := by
    apply Subtype.ext
    have hs := congrArg (fun z : O => (Ideal.span {z} : Ideal O)) he
    simpa only [Ideal.span_singleton_mul_left_unit (hunit p.1),
      Ideal.span_singleton_mul_left_unit (hunit q.1),
      (primaryIdealGenerator_spec p.2.1 p.2.2).1,
      (primaryIdealGenerator_spec q.2.1 q.2.2).1] using hs
  have hj : p.1 = q.1 := by
    apply Fin.ext
    apply omega_primitive.pow_inj p.1.isLt q.1.isLt
    rw [hi] at he
    exact mul_right_cancel₀ q.2.2 he
  exact Prod.ext hj hi

lemma halfPrimaryFromIdeal_surjective : Function.Surjective halfPrimaryFromIdeal := by
  intro b
  let I : GoodIdeal := ⟨Ideal.span {b.1},
    (primaryIdealGenerator_span_ne_zero_iff b.1).mpr (halfPrimary_not_dvd b)⟩
  have hs : Associated (primaryIdealGenerator I.1) b.1 :=
    Ideal.span_singleton_eq_span_singleton.mp (primaryIdealGenerator_spec I.1 I.2).1
  obtain ⟨u, hu⟩ := hs
  have he : (u : O) * primaryIdealGenerator I.1 = b.1 := by simpa only [mul_comm] using hu
  have hup : lambda ∣ (u : O) - 1 := by
    have ha : lambda ∣ primaryIdealGenerator I.1 - 1 :=
      (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans (primaryIdealGenerator_spec I.1 I.2).2
    have hd := dvd_sub b.2 (ha.mul_left (u : O))
    rw [← he] at hd
    convert hd using 1 <;> ring
  obtain ⟨j, hj | hj⟩ := unit_eq_sign_omega u
  · exact ⟨(j, I), Subtype.ext (by simpa only [halfPrimaryFromIdeal, hj] using he)⟩
  · exact (halfPrimary_not_negative j.val (by simpa only [hj] using hup)).elim

def halfPrimaryIdealEquiv : (Fin 3 × GoodIdeal) ≃ HalfPrimary :=
  Equiv.ofBijective halfPrimaryFromIdeal
    ⟨halfPrimaryFromIdeal_injective, halfPrimaryFromIdeal_surjective⟩

/-- The once-ramified scale and its complementary divisor of three. -/
def onceCuspScale (u : Oˣ) : O := (u : O) * traceLambda

def onceCuspComplement (u : Oˣ) : O := -(↑u⁻¹ : O) * traceLambda

lemma traceLambda_square : traceLambda ^ 2 = (-3 : O) := by
  rw [traceLambda_eq_unit_mul_lambda, mul_pow, lambda_sq_eq]
  calc
    _ = -3 * omega ^ 3 := by ring
    _ = -3 := by rw [omega_primitive.pow_eq_one]; ring

lemma onceCusp_scale_complement (u : Oˣ) : onceCuspScale u * onceCuspComplement u = 3 := by
  calc
    _ = -((u : O) * (↑u⁻¹ : O)) * traceLambda ^ 2 := by
      unfold onceCuspScale onceCuspComplement
      ring
    _ = 3 := by simp [traceLambda_square]

lemma onceCusp_scale_ne_zero (u : Oˣ) : onceCuspScale u ≠ 0 := by
  intro h
  have he := onceCusp_scale_complement u
  rw [h, zero_mul] at he
  exact (by norm_num : (0 : O) ≠ 3) he

lemma onceCusp_scale_lambda (u : Oˣ) : (3 : O) ∣ onceCuspScale u * lambda := by
  refine ⟨(u : O) * omega ^ 2, ?_⟩
  calc
    _ = -(u : O) * omega * lambda ^ 2 := by
      rw [onceCuspScale, traceLambda_eq_unit_mul_lambda]
      ring
    _ = _ := by rw [lambda_sq_eq]; ring

lemma onceCusp_complement_lambda (u : Oˣ) : lambda ∣ onceCuspComplement u := by
  refine ⟨(↑u⁻¹ : O) * omega, ?_⟩
  rw [onceCuspComplement, traceLambda_eq_unit_mul_lambda]
  ring

lemma onceCusp_scale_coprime (u : Oˣ) (d : O) (hd : lambda ^ 2 ∣ d - 1) :
    IsCoprime (onceCuspScale u) d := by
  apply (isCoprime_mul_unit_left_left u.isUnit _ _).mpr
  apply (primary_coprime_three d hd).symm.of_isCoprime_of_dvd_left
  refine ⟨-traceLambda, ?_⟩
  linear_combination traceLambda_square

lemma isCoprime_right_congr_of_dvd (a b c : O) (h : a ∣ b - c) :
    IsCoprime a b ↔ IsCoprime a c := by
  obtain ⟨k, hk⟩ := h
  constructor
  · rintro ⟨r, t, ht⟩
    exact ⟨r + t * k, t, by linear_combination ht - t * hk⟩
  · rintro ⟨r, t, ht⟩
    exact ⟨r - t * k, t, by linear_combination ht + t * hk⟩

lemma unitLowerDenominator_coprime (p : OppositeData) :
    IsCoprime (primaryIdealGenerator p.1.1) (primaryIdealGenerator p.1.1 + 3 * p.2.1) := by
  apply (isCoprime_right_congr_of_dvd (primaryIdealGenerator p.1.1)
    (primaryIdealGenerator p.1.1 + 3 * p.2.1) (3 * p.2.1) ⟨1, by ring⟩).mpr
  exact (primary_coprime_three _ (primaryIdealGenerator_spec p.1.1 p.1.2).2).mul_right p.2.2

abbrev OnceRamifiedData := Fin 3 × OppositeData

/-- Each once-ramified row consists of one of three primary associates and a primary denominator. -/
def onceRamifiedToPrimitive (u : Oˣ) (p : OnceRamifiedData) : PrimitiveRow := by
  let a := primaryIdealGenerator p.2.1.1
  let b := omega ^ p.1.val * a
  let d := a + 3 * p.2.2.1
  refine ⟨![onceCuspScale u * (b - d), d], ?_⟩
  change IsCoprime (onceCuspScale u * (b - d)) d ∧
    (3 : O) ∣ onceCuspScale u * (b - d) ∧ (3 : O) ∣ d - 1
  have hd : lambda ^ 2 ∣ d - 1 := unitLowerDenominator_primary p.2
  refine ⟨?_, ?_, three_dvd_primary_sub_one d hd⟩
  · apply (onceCusp_scale_coprime u d hd).mul_left
    apply IsCoprime.symm
    apply (isCoprime_right_congr_of_dvd d (b - d) b ⟨-1, by ring⟩).mpr
    exact ((isCoprime_mul_unit_left_left ((omega_primitive.isUnit (by decide)).pow _) _ _).mpr
      (unitLowerDenominator_coprime p.2)).symm
  · have hb : lambda ∣ b - 1 := (halfPrimaryFromIdeal (p.1, p.2.1)).2
    have hd' : lambda ∣ d - 1 := (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans hd
    have hbd : lambda ∣ b - d := by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub hb hd'
    obtain ⟨k, hk⟩ := hbd
    rw [hk, ← mul_assoc]
    exact (onceCusp_scale_lambda u).mul_right k

lemma onceRamifiedToPrimitive_injective (u : Oˣ) : Function.Injective (onceRamifiedToPrimitive u) := by
  rintro ⟨j, I, x, hx⟩ ⟨k, J, y, hy⟩ he
  have hd : primaryIdealGenerator I.1 + 3 * x = primaryIdealGenerator J.1 + 3 * y :=
    congrFun (congrArg Subtype.val he) 1
  have hc : onceCuspScale u * (omega ^ j.val * primaryIdealGenerator I.1 -
      (primaryIdealGenerator I.1 + 3 * x)) =
      onceCuspScale u * (omega ^ k.val * primaryIdealGenerator J.1 -
        (primaryIdealGenerator J.1 + 3 * y)) := congrFun (congrArg Subtype.val he) 0
  have hb := mul_left_cancel₀ (onceCusp_scale_ne_zero u) hc
  have hi : (j, I) = (k, J) := halfPrimaryFromIdeal_injective (Subtype.ext (by
    change omega ^ j.val * primaryIdealGenerator I.1 = omega ^ k.val * primaryIdealGenerator J.1
    linear_combination hb + hd))
  obtain rfl : j = k := congrArg Prod.fst hi
  obtain rfl : I = J := congrArg Prod.snd hi
  have hxy : x = y := mul_left_cancel₀ (by norm_num : (3 : O) ≠ 0) (add_left_cancel hd)
  subst y
  rfl

lemma onceRamifiedToPrimitive_surjective (u : Oˣ) : Function.Surjective (onceRamifiedToPrimitive u) := by
  intro r
  obtain ⟨k, hk⟩ := r.2.2.1
  let d := r.1 1
  have hdp : lambda ^ 2 ∣ d - 1 := lambda_sq_dvd_three.trans r.2.2.2
  let b : HalfPrimary := ⟨onceCuspComplement u * k + d, by
    have hh := dvd_add ((onceCusp_complement_lambda u).mul_right k)
      ((dvd_pow_self lambda (by decide : 2 ≠ 0)).trans hdp)
    convert hh using 1 <;> ring⟩
  let p := halfPrimaryIdealEquiv.symm b
  have hp : omega ^ p.1.val * primaryIdealGenerator p.2.1 = b.1 :=
    congrArg Subtype.val (halfPrimaryIdealEquiv.apply_symm_apply b)
  have hr : onceCuspScale u * (b.1 - d) = r.1 0 := by
    change onceCuspScale u * (onceCuspComplement u * k + d - d) = _
    rw [add_sub_cancel_right, ← mul_assoc, onceCusp_scale_complement, ← hk]
  have had : IsCoprime (primaryIdealGenerator p.2.1) d := by
    have h0 : IsCoprime (b.1 - d) d :=
      (hr ▸ r.2.1).of_isCoprime_of_dvd_left (dvd_mul_left _ _)
    have hb : IsCoprime b.1 d := by
      apply IsCoprime.symm
      exact (isCoprime_right_congr_of_dvd d (b.1 - d) b.1 ⟨-1, by ring⟩).mp h0.symm
    rw [← hp] at hb
    exact hb.of_isCoprime_of_dvd_left (dvd_mul_left _ _)
  have hda : (3 : O) ∣ d - primaryIdealGenerator p.2.1 := by
    have hh := dvd_sub r.2.2.2
      (three_dvd_primary_sub_one _ (primaryIdealGenerator_spec p.2.1 p.2.2).2)
    simpa only [sub_sub_sub_cancel_right] using hh
  obtain ⟨x, hx⟩ := hda
  have hd : d = primaryIdealGenerator p.2.1 + 3 * x := by linear_combination hx
  have hax : IsCoprime (primaryIdealGenerator p.2.1) x := by
    have hh : IsCoprime (primaryIdealGenerator p.2.1) (3 * x) :=
      (isCoprime_right_congr_of_dvd (primaryIdealGenerator p.2.1) d (3 * x)
        ⟨1, by linear_combination hd⟩).mp had
    exact hh.of_isCoprime_of_dvd_right (dvd_mul_left _ _)
  refine ⟨(p.1, ⟨p.2, x, hax⟩), Subtype.ext ?_⟩
  funext i
  fin_cases i
  · change onceCuspScale u * (omega ^ p.1.val * primaryIdealGenerator p.2.1 -
      (primaryIdealGenerator p.2.1 + 3 * x)) = r.1 0
    rw [← hd, hp, hr]
  · exact hd.symm

def onceRamifiedDataEquiv (u : Oˣ) : OnceRamifiedData ≃ PrimitiveRow :=
  Equiv.ofBijective (onceRamifiedToPrimitive u)
    ⟨onceRamifiedToPrimitive_injective u, onceRamifiedToPrimitive_surjective u⟩

lemma onceRamified_row_phase (u : Oˣ) (p : OnceRamifiedData) :
    (cosetCharacter (primitiveRowEquiv.symm (onceRamifiedDataEquiv u p)))⁻¹ =
      ringComplex (symbol (onceCuspScale u * omega ^ p.1.val)
        (primaryIdealGenerator p.2.1.1 + 3 * p.2.2.1)) *
      ringComplex (symbol (primaryIdealGenerator p.2.1.1 + 3 * p.2.2.1)
        (primaryIdealGenerator p.2.1.1)) := by
  rw [inverse_cosetCharacter_eq_row_symbol, primitiveRowEquiv_symm_row]
  change ringComplex (symbol (onceCuspScale u *
    (omega ^ p.1.val * primaryIdealGenerator p.2.1.1 - (primaryIdealGenerator p.2.1.1 + 3 * p.2.2.1)))
    (primaryIdealGenerator p.2.1.1 + 3 * p.2.2.1)) = _
  rw [symbol_congr (show primaryIdealGenerator p.2.1.1 + 3 * p.2.2.1 ∣
      onceCuspScale u * (omega ^ p.1.val * primaryIdealGenerator p.2.1.1 -
        (primaryIdealGenerator p.2.1.1 + 3 * p.2.2.1)) -
      (onceCuspScale u * omega ^ p.1.val) * primaryIdealGenerator p.2.1.1 from
        ⟨-onceCuspScale u, by ring⟩),
    symbol_mul_numerator, map_mul,
    symbol_reciprocity _ _ (primaryIdealGenerator_spec p.2.1.1 p.2.1.2).2
      (unitLowerDenominator_primary p.2)]

/-- A diagonal unit rescales the row by a norm-one scalar. -/
lemma diagonal_once_summand (u t : Oˣ) (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ)
    (p : OnceRamifiedData) :
    summand (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)) * upperSection z v hv) s
      (primitiveRowEquiv.symm (onceRamifiedDataEquiv (u⁻¹ ^ 2 * t) p)) =
      affineLowerTerm (onceCuspScale t * omega ^ p.1.val)
        ((↑u⁻¹ : O) ^ 2 * (onceCuspScale t * omega ^ p.1.val)) z v s
          (primaryIdealGenerator p.2.1.1) (primaryIdealGenerator p.2.1.1 + 3 * p.2.2.1) := by
  let r : Fin 2 → ℂ := ![ringComplex ((onceCuspScale t * omega ^ p.1.val) * primaryIdealGenerator p.2.1.1),
    ringComplex (primaryIdealGenerator p.2.1.1 + 3 * p.2.2.1)]
  have hscale : (u : O) * onceCuspScale (u⁻¹ ^ 2 * t) = (↑u⁻¹ : O) * onceCuspScale t := by
    simp [onceCuspScale, pow_two, ← mul_assoc]
  have hr : rowOperator (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)))
      (embeddedRow (primitiveRowEquiv.symm (onceRamifiedDataEquiv (u⁻¹ ^ 2 * t) p))) =
        ringComplex (↑u⁻¹ : O) • r := by
    rw [← rowOperator_mul, embeddedRow, primitiveRowEquiv_symm_row,
      rowOperator_unitDiagonal, rowOperator_lowerCusp]
    funext i
    fin_cases i
    · change ringComplex (u : O) * ringComplex (onceCuspScale (u⁻¹ ^ 2 * t) *
        (omega ^ p.1.val * primaryIdealGenerator p.2.1.1 -
          (primaryIdealGenerator p.2.1.1 + 3 * p.2.2.1))) +
        ringComplex (onceCuspScale t) * (ringComplex (↑u⁻¹ : O) *
          ringComplex (primaryIdealGenerator p.2.1.1 + 3 * p.2.2.1)) =
        ringComplex (↑u⁻¹ : O) *
          ringComplex ((onceCuspScale t * omega ^ p.1.val) * primaryIdealGenerator p.2.1.1)
      rw [map_mul, ← mul_assoc, ← map_mul, hscale]
      simp only [map_mul, map_sub]
      ring
    · rfl
  have hr0 : r ≠ 0 := by
    intro hh
    exact ringComplex_ne_zero (mul_ne_zero (mul_ne_zero (onceCusp_scale_ne_zero t)
      (pow_ne_zero _ (omega_primitive.isUnit (by decide)).ne_zero)) p.2.1.2) (congrFun hh 0)
  have hp := heightDenominator_pos z v hv r hr0
  rw [summand, ← rowOperator_mul, hr, map_smul, rowEnergy_complex_smul,
    norm_ringComplex_unit, one_pow, one_mul, rowEnergy_upperSection, onceRamified_row_phase]
  have hphase : onceCuspScale (u⁻¹ ^ 2 * t) * omega ^ p.1.val =
      (↑u⁻¹ : O) ^ 2 * (onceCuspScale t * omega ^ p.1.val) := by
    simp only [onceCuspScale, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hphase]
  change _ = _ * ((v / heightDenominator z v r : ℝ) : ℂ) ^ s
  rw [show ((v / heightDenominator z v r : ℝ) : ℂ) =
    (((heightDenominator z v r / v : ℝ) : ℂ))⁻¹ by simp only [Complex.ofReal_div, inv_div],
    inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le), Complex.cpow_neg]

lemma hasSum_diagonal_once_integrals (u t : Oˣ) (v : ℝ) (hv : 0 < v) (s : ℂ) (h : O) (hs : 2 < s.re) :
    HasSum (fun p : OnceRamifiedData => affineLowerFourierTerm (onceCuspScale t * omega ^ p.1.val)
      ((↑u⁻¹ : O) ^ 2 * (onceCuspScale t * omega ^ p.1.val)) h v s
        (primaryIdealGenerator p.2.1.1) p.2.2.1)
      (∫ z in periodDomain, eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
        integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)) * upperSection z v hv) s *
          tracePhase (-ninthCuspFrequency h * z)) := by
  let e := (onceRamifiedDataEquiv (u⁻¹ ^ 2 * t)).trans primitiveRowEquiv.symm
  have he := e.hasSum_iff.mpr (hasSum_integral_fixed_left_Eisenstein
    (integralComplexMatrix (unitCuspDiagonal u) * integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)))
      v hv s (ninthCuspFrequency h) hs)
  apply he.congr_fun
  intro p
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only [affineLowerFourierTerm, e, Equiv.trans_apply, Function.comp_apply]
    rw [diagonal_once_summand])

def cuspOmegaUnit : Oˣ := (omega_primitive.isUnit (by decide)).unit

lemma cuspOmegaUnit_val : (cuspOmegaUnit : O) = omega :=
  (omega_primitive.isUnit (by decide)).unit_spec

/-- The unit part of the once-ramified cubic numerator. -/
def onceCuspArithmeticUnit (u t : Oˣ) (j : Fin 3) : Oˣ :=
  u⁻¹ ^ 2 * t * (-cuspOmegaUnit) * cuspOmegaUnit ^ j.val

lemma onceCuspArithmeticUnit_spec (u t : Oˣ) (j : Fin 3) :
    (onceCuspArithmeticUnit u t j : O) * lambda =
      (↑u⁻¹ : O) ^ 2 * (onceCuspScale t * omega ^ j.val) := by
  simp only [onceCuspArithmeticUnit, onceCuspScale, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, cuspOmegaUnit_val, traceLambda_eq_unit_mul_lambda]
  ring

lemma onceCusp_q_norm (t : Oˣ) (j : Fin 3) :
    ‖ringComplex (onceCuspScale t * omega ^ j.val)‖ ^ 2 = 3 := by
  have hw : ‖ringComplex omega‖ = 1 := by
    rw [← cuspOmegaUnit_val]
    exact norm_ringComplex_unit cuspOmegaUnit
  simp only [onceCuspScale, map_mul, norm_mul, norm_ringComplex_unit, one_mul,
    map_pow, norm_pow, hw, one_pow, mul_one]
  rw [← norm_pow, ← map_pow, traceLambda_square]
  norm_num [map_ofNat]

lemma onceCusp_q_absNorm (t : Oˣ) (j : Fin 3) :
    Ideal.absNorm (Ideal.span {onceCuspScale t * omega ^ j.val}) = 3 := by
  have hh := onceCusp_q_norm t j
  rw [ringComplex_norm_sq_eq_absNorm_span] at hh
  exact_mod_cast hh

/-- An active once-ramified branch has norm-three scale and one unramified Gauss series. -/
theorem diagonal_once_branch_fourier (u t : Oˣ) (j : Fin 3) (h h1 : O)
    (hh : h = (onceCuspScale t * omega ^ j.val) * h1)
    (hfreq : (3 : O) ∣ h1 + ramifiedArithmeticPhase (onceCuspArithmeticUnit u t j) 1)
    (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    (∑' p : OppositeData, affineLowerFourierTerm (onceCuspScale t * omega ^ j.val)
      ((↑u⁻¹ : O) ^ 2 * (onceCuspScale t * omega ^ j.val)) h v s
        (primaryIdealGenerator p.1.1) p.2.1) =
      (3 : ℂ) * (3 : ℂ) ^ (-s) *
        ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (ninthCuspFrequency h * v)) *
          tracePhase (ninthCuspFrequency h / ringComplex (onceCuspScale t * omega ^ j.val)) *
            unramifiedCubicGaussSeries s (3 * ((↑u⁻¹ : O) ^ 2 * (onceCuspScale t * omega ^ j.val)) ^ 2 * h1) := by
  have hsum := (hasSum_diagonal_once_integrals u t v hv s h hs).summable.prod_factor j
  have hq := mul_ne_zero (onceCusp_scale_ne_zero t)
    (pow_ne_zero j.val (omega_primitive.isUnit (by decide)).ne_zero)
  have he := affineCusp_branch_fourier h h1 (onceCuspScale t * omega ^ j.val)
    (onceCuspArithmeticUnit u t j) 1 hq hh hfreq v hv s (by linarith)
      (by simpa only [pow_one, onceCuspArithmeticUnit_spec] using hsum)
  simpa only [pow_one, onceCuspArithmeticUnit_spec, onceCusp_q_norm, onceCusp_q_absNorm,
    Nat.cast_ofNat, Complex.ofReal_ofNat] using he

/-- Residue weights survive lattice unfolding as their finite sum. -/
theorem quotient_weighted_period_unfold (q : O) (hq : q ≠ 0)
    (ψ : (O ⧸ Ideal.span {q}) → ℂ) (f : ℂ → ℂ) (hf : Integrable f) :
    (∑' n : O, ψ (Ideal.Quotient.mk (Ideal.span {q}) n) *
      ∫ z in periodDomain, f (z + 3 * ringComplex n / ringComplex q)) =
      (∑' r : O ⧸ Ideal.span {q}, ψ r) * (∫ z : ℂ, f z) := by
  letI : Finite (O ⧸ Ideal.span {q}) := (Ideal.span {q}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr hq)
  letI : Fintype (O ⧸ Ideal.span {q}) := Fintype.ofFinite _
  let I : O → ℂ := fun n => ∫ z in periodDomain, f (z + 3 * ringComplex n / ringComplex q)
  have hs : Summable (fun n : O => ψ (Ideal.Quotient.mk (Ideal.span {q}) n) * I n) := by
    apply (((finite_index_period_integrals_summable q hq f hf).norm).mul_left ‖ψ‖).of_norm_bounded
    intro n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_le_pi_norm ψ _) (norm_nonneg _)
  have hinner (r : O ⧸ Ideal.span {q}) :
      (∑' n : ((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),
        ψ (Ideal.Quotient.mk (Ideal.span {q}) n.1) * I n.1) = ψ r * (∫ z : ℂ, f z) := by
    have heval (n : ((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r})) :
        Ideal.Quotient.mk (Ideal.span {q}) n.1 = r := n.2
    simp_rw [heval]
    rw [tsum_mul_left, ← (principalResidueFiberEquiv q hq r).tsum_eq]
    congr 1
    change (∑' n : O, ∫ z in periodDomain,
      f (z + 3 * ringComplex (principalResidueRep q r + q * n) / ringComplex q)) = _
    simp_rw [finite_index_period_shift q hq]
    rw [← integral_eq_period_integrals _ (hf.comp_add_right _)]
    exact integral_add_right_eq_self f _
  rw [← (hs.hasSum.tsum_fiberwise (Ideal.Quotient.mk (Ideal.span {q}))).tsum_eq]
  change (∑' r : O ⧸ Ideal.span {q}, ∑' n : ((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),
    ψ (Ideal.Quotient.mk (Ideal.span {q}) n.1) * I n.1) = _
  simp_rw [hinner]
  exact tsum_mul_right

theorem character_weighted_period_unfold (q : O) (hq : q ≠ 0)
    (ψ : AddChar (O ⧸ Ideal.span {q}) ℂ) (f : ℂ → ℂ) (hf : Integrable f) :
    (∑' n : O, ψ (Ideal.Quotient.mk (Ideal.span {q}) n) *
      ∫ z in periodDomain, f (z + 3 * ringComplex n / ringComplex q)) =
      if ψ = 1 then (Ideal.absNorm (Ideal.span {q}) : ℂ) * (∫ z : ℂ, f z) else 0 := by
  letI : Finite (O ⧸ Ideal.span {q}) := (Ideal.span {q}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr hq)
  letI : Fintype (O ⧸ Ideal.span {q}) := Fintype.ofFinite _
  rw [quotient_weighted_period_unfold q hq ψ f hf, tsum_fintype]
  split_ifs with hψ
  · rw [AddChar.sum_eq_card_of_eq_one hψ]
    congr 1
    change (Fintype.card (O ⧸ Ideal.span {q}) : ℂ) = (Nat.card (O ⧸ Ideal.span {q}) : ℂ)
    rw [Nat.card_eq_fintype_card]
  · rw [AddChar.sum_eq_zero_of_ne_one hψ, zero_mul]

lemma residueTraceQuotientChar_eq_one (q : O) (hq : q ≠ 0) (ell : O) :
    residueTraceQuotientChar ell q hq = 1 ↔ q ∣ ell := by
  constructor
  · intro he
    by_contra hn
    exact residueTraceQuotientChar_ne_one q ell hq hn he
  · intro hd
    rw [residueTraceQuotientChar_mulShift,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd), AddChar.mulShift_zero]

lemma residueTraceQuotientChar_phase (q : O) (hq : q ≠ 0) (ell x : O) :
    residueTraceQuotientChar ell q hq (Ideal.Quotient.mk (Ideal.span {q}) x) =
      tracePhase (ringComplex (ell * x) / (ringComplex q * ringComplex traceLambda)) := by
  rw [residueTraceQuotientChar_mk]
  unfold residueAdditive cuspFrequency
  congr 1
  simp only [map_mul, map_ofNat]
  field_simp [ringComplex_ne_zero hq, ringComplex_ne_zero traceLambda_ne_zero] <;> ring

/-- A translated affine row acquires precisely the residue character of its combined frequency. -/
lemma affineCusp_general_weighted_translate (h q a ell x m : O) (u : Oˣ) (n : ℕ)
    (hap : lambda ^ 2 ∣ a - 1) (hq : q ≠ 0)
    (hell : 3 * ell = h + ramifiedArithmeticPhase u n * q * a) (z : ℂ) (v : ℝ) (s : ℂ) :
    affineLowerTerm q ((u : O) * lambda ^ n) z v s a (a + 3 * (x + a * m)) *
      tracePhase (-ninthCuspFrequency h * z) =
      residueTraceQuotientChar ell q hq (Ideal.Quotient.mk (Ideal.span {q}) m) *
        (affineLowerTerm q ((u : O) * lambda ^ n) (z + 3 * ringComplex m / ringComplex q) v s a (a + 3 * x) *
          tracePhase (-ninthCuspFrequency h * (z + 3 * ringComplex m / ringComplex q))) := by
  let A := cuspFrequency (ramifiedArithmeticPhase u n) * ringComplex (a * m)
  let delta := 3 * ringComplex m / ringComplex q
  have hchar : ringComplex (symbol ((u : O) * lambda ^ n) (a + 3 * (x + a * m))) =
      ringComplex (symbol ((u : O) * lambda ^ n) (a + 3 * x)) * tracePhase A := by
    have hd : lambda ^ 2 ∣ a + 3 * x - 1 := by
      convert dvd_add hap (lambda_sq_dvd_three.mul_right x) using 1 <;> ring
    convert ramified_symbol_primary_affine u n (a + 3 * x) (a * m) hd using 1 <;> ring
  have hden : symbol (a + 3 * (x + a * m)) a = symbol (a + 3 * x) a :=
    symbol_congr ⟨3 * m, by ring⟩
  have hrow : ringComplex (q * a) * z + ringComplex (a + 3 * (x + a * m)) =
      ringComplex (q * a) * (z + delta) + ringComplex (a + 3 * x) := by
    dsimp only [delta]
    simp only [map_add, map_mul, map_ofNat]
    field_simp [ringComplex_ne_zero hq] <;> ring
  have hell' : ringComplex ell =
      (ringComplex h + ringComplex (ramifiedArithmeticPhase u n) * ringComplex q * ringComplex a) / 3 := by
    apply (eq_div_iff (by norm_num : (3 : ℂ) ≠ 0)).mpr
    have he := congrArg ringComplex hell
    simp only [map_mul, map_add, map_ofNat] at he
    linear_combination he
  have harg : A + ninthCuspFrequency h * delta =
      ringComplex (ell * m) / (ringComplex q * ringComplex traceLambda) := by
    dsimp only [A, delta, ninthCuspFrequency, cuspFrequency]
    simp only [map_mul]
    rw [hell']
    field_simp [ringComplex_ne_zero hq, ringComplex_ne_zero traceLambda_ne_zero] <;> ring
  have hphase : tracePhase A * tracePhase (-ninthCuspFrequency h * z) =
      residueTraceQuotientChar ell q hq (Ideal.Quotient.mk (Ideal.span {q}) m) *
        tracePhase (-ninthCuspFrequency h * (z + delta)) := by
    rw [residueTraceQuotientChar_phase, ← harg, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  unfold affineLowerTerm
  rw [hchar, hden, hrow]
  change _ = residueTraceQuotientChar ell q hq (Ideal.Quotient.mk (Ideal.span {q}) m) *
    ((ringComplex (symbol ((u : O) * lambda ^ n) (a + 3 * x)) * ringComplex (symbol (a + 3 * x) a)) *
      ((v / (‖ringComplex (q * a) * (z + delta) + ringComplex (a + 3 * x)‖ ^ 2 +
        ‖ringComplex (q * a)‖ ^ 2 * v ^ 2) : ℝ) : ℂ) ^ s *
          tracePhase (-ninthCuspFrequency h * (z + delta)))
  linear_combination
    (ringComplex (symbol ((u : O) * lambda ^ n) (a + 3 * x)) * ringComplex (symbol (a + 3 * x) a) *
      ((v / (‖ringComplex (q * a) * (z + delta) + ringComplex (a + 3 * x)‖ ^ 2 +
        ‖ringComplex (q * a)‖ ^ 2 * v ^ 2) : ℝ) : ℂ) ^ s) * hphase

lemma affineCusp_masked_inner (h q a ell x : O) (u : Oˣ) (n : ℕ)
    (ha : a ≠ 0) (hap : lambda ^ 2 ∣ a - 1) (hq : q ≠ 0)
    (hell : 3 * ell = h + ramifiedArithmeticPhase u n * q * a)
    (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re) :
    (∑' m : O, ∫ z in periodDomain,
      affineLowerTerm q ((u : O) * lambda ^ n) z v s a (a + 3 * (x + a * m)) *
        tracePhase (-ninthCuspFrequency h * z)) =
      if q ∣ ell then (Ideal.absNorm (Ideal.span {q}) : ℂ) *
        (∫ z : ℂ, affineLowerTerm q ((u : O) * lambda ^ n) z v s a (a + 3 * x) *
          tracePhase (-ninthCuspFrequency h * z)) else 0 := by
  have hint := trace_mul_integrable
    (fun z => affineLowerTerm q ((u : O) * lambda ^ n) z v s a (a + 3 * x))
    (affineLowerTerm_integrable q ((u : O) * lambda ^ n) v hv s hs a (a + 3 * x) ha hq)
    (ninthCuspFrequency h)
  simp_rw [affineCusp_general_weighted_translate h q a ell x _ u n hap hq hell, integral_const_mul]
  rw [character_weighted_period_unfold q hq (residueTraceQuotientChar ell q hq) _ hint]
  simp only [residueTraceQuotientChar_eq_one]

/-- Nontrivial residue characters cancel every inactive denominator fiber. -/
lemma affineDenominator_zero (h h1 q a : O) (u : Oˣ) (n : ℕ)
    (ha : a ≠ 0) (hap : lambda ^ 2 ∣ a - 1) (hq : q ≠ 0) (hh : h = q * h1)
    (hbase : (3 : O) ∣ h + ramifiedArithmeticPhase u n * q)
    (hfreq : ¬(3 : O) ∣ h1 + ramifiedArithmeticPhase u n)
    (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (hsum : Summable (fun x : CoprimeElement a => affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s a x.1)) :
    (∑' x : CoprimeElement a, affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s a x.1) = 0 := by
  have hdiv : (3 : O) ∣ h + ramifiedArithmeticPhase u n * q * a := by
    have ht := dvd_add hbase ((three_dvd_primary_sub_one a hap).mul_left (ramifiedArithmeticPhase u n * q))
    convert ht using 1 <;> ring
  obtain ⟨ell, hell⟩ := hdiv
  have hell' : 3 * ell = h + ramifiedArithmeticPhase u n * q * a := hell.symm
  have hne : ¬q ∣ ell := by
    rintro ⟨b, hb⟩
    have he : q * (3 * b) = q * (h1 + ramifiedArithmeticPhase u n * a) := by
      rw [hb, hh] at hell'
      linear_combination hell'
    have hc := mul_left_cancel₀ hq he
    have ht : (3 : O) ∣ h1 + ramifiedArithmeticPhase u n * a := ⟨b, hc.symm⟩
    apply hfreq
    convert dvd_sub ht ((three_dvd_primary_sub_one a hap).mul_left (ramifiedArithmeticPhase u n))
      using 1 <;> ring
  let F : CoprimeElement a → ℂ := fun x => affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s a x.1
  let e := cubicResidueElementEquiv a ha
  have hp : Summable (fun p : CubicUnitResidue a × O => F (e p)) := e.summable_iff.mpr hsum
  change (∑' x, F x) = 0
  rw [← e.tsum_eq F, hp.tsum_prod]
  change (∑' x : CubicUnitResidue a, ∑' m : O,
    affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s a (principalResidueRep a x.1 + a * m)) = 0
  have hinner (x : CubicUnitResidue a) :
      (∑' m : O, affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s a
        (principalResidueRep a x.1 + a * m)) = 0 := by
    unfold affineLowerFourierTerm
    rw [affineCusp_masked_inner h q a ell _ u n ha hap hq hell' v hv s hs, if_neg hne]
  simp only [hinner, tsum_zero]

/-- The affine Fourier formula includes exact cancellation of inactive residue classes. -/
theorem affineCusp_branch_fourier_masked (h h1 q : O) (u : Oˣ) (n : ℕ) (hq : q ≠ 0)
    (hh : h = q * h1) (hbase : (3 : O) ∣ h + ramifiedArithmeticPhase u n * q)
    (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (hsum : Summable (fun p : OppositeData => affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s
      (primaryIdealGenerator p.1.1) p.2.1)) :
    (∑' p : OppositeData, affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s
      (primaryIdealGenerator p.1.1) p.2.1) =
      if (3 : O) ∣ h1 + ramifiedArithmeticPhase u n then
        (Ideal.absNorm (Ideal.span {q}) : ℂ) * ((‖ringComplex q‖ ^ 2 : ℝ) : ℂ) ^ (-s) *
          ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (ninthCuspFrequency h * v)) *
            tracePhase (ninthCuspFrequency h / ringComplex q) *
              unramifiedCubicGaussSeries s (3 * ((u : O) * lambda ^ n) ^ 2 * h1) else 0 := by
  split_ifs with hfreq
  · exact affineCusp_branch_fourier h h1 q u n hq hh hfreq v hv s hs hsum
  · rw [hsum.tsum_sigma]
    trans ∑' I : GoodIdeal, (0 : ℂ)
    · apply tsum_congr
      intro I
      exact affineDenominator_zero h h1 q _ u n I.2
        (primaryIdealGenerator_spec I.1 I.2).2 hq hh hbase hfreq v hv s hs (hsum.sigma_factor I)
    · exact tsum_zero

/-- The once-ramified cusp has exactly three affine Fourier branches. -/
theorem diagonal_once_eisenstein_fourier (u t : Oˣ) (h : O) (h1 : Fin 3 → O)
    (hh : ∀ j, h = (onceCuspScale t * omega ^ j.val) * h1 j)
    (hbase : ∀ j, (3 : O) ∣ h + ramifiedArithmeticPhase (onceCuspArithmeticUnit u t j) 1 *
      (onceCuspScale t * omega ^ j.val))
    (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    (∫ z in periodDomain, eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)) * upperSection z v hv) s *
        tracePhase (-ninthCuspFrequency h * z)) =
      ∑ j : Fin 3, if (3 : O) ∣ h1 j + ramifiedArithmeticPhase (onceCuspArithmeticUnit u t j) 1 then
        (3 : ℂ) * (3 : ℂ) ^ (-s) *
          ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (ninthCuspFrequency h * v)) *
            tracePhase (ninthCuspFrequency h / ringComplex (onceCuspScale t * omega ^ j.val)) *
              unramifiedCubicGaussSeries s
                (3 * ((↑u⁻¹ : O) ^ 2 * (onceCuspScale t * omega ^ j.val)) ^ 2 * h1 j) else 0 := by
  have hsum := hasSum_diagonal_once_integrals u t v hv s h hs
  rw [← hsum.tsum_eq, hsum.summable.tsum_prod, tsum_fintype]
  apply Finset.sum_congr rfl
  intro j hj
  have hq := mul_ne_zero (onceCusp_scale_ne_zero t)
    (pow_ne_zero j.val (omega_primitive.isUnit (by decide)).ne_zero)
  have he := affineCusp_branch_fourier_masked h (h1 j) (onceCuspScale t * omega ^ j.val)
    (onceCuspArithmeticUnit u t j) 1 hq (hh j) (hbase j) v hv s (by linarith)
      (by simpa only [pow_one, onceCuspArithmeticUnit_spec] using hsum.summable.prod_factor j)
  simpa only [pow_one, onceCuspArithmeticUnit_spec, onceCusp_q_norm, onceCusp_q_absNorm,
    Nat.cast_ofNat, Complex.ofReal_ofNat] using he

/-- A continuous horizontal parametrization preserves compact domination of the Eisenstein rows. -/
theorem hasSum_integral_fixed_left_Eisenstein_comp (a : SL(2, ℂ)) (v : ℝ) (hv : 0 < v)
    (τ : ℂ → ℂ) (hτ : Continuous τ) (s freq : ℂ) (hs : 2 < s.re) :
    HasSum (fun x : CuspCosets => ∫ z in periodDomain,
      summand (a * upperSection (τ z) v hv) s x * tracePhase (-freq * z))
      (∫ z in periodDomain, eisenstein (a * upperSection (τ z) v hv) s * tracePhase (-freq * z)) := by
  letI : Countable CuspCosets := (rowCoordinates_injective.comp cosetRow_injective).countable
  letI := periodDomain_finiteMeasure
  have hc : Continuous (fun z : ℂ => rowBound (a * upperSection (τ z) v hv)) :=
    (continuous_const.mul (continuous_const.add (continuous_inverse_fixed_left_operator a v hv).norm)).comp hτ
  let R : ℝ := ∑ i : Fin 2, ‖periodBasis i‖
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image hc.continuousOn
  let C := max 1 B
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hbound (z : ℂ) (hz : z ∈ periodDomain) : rowBound (a * upperSection (τ z) v hv) ≤ C := by
    apply (hB ?_).trans (le_max_right _ _)
    exact ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using norm_mem_periodDomain z hz, rfl⟩
  let M : CuspCosets → ℝ := fun x => C ^ (2 * s.re) * ‖rowCoordinates (cosetRow x)‖ ^ (-(2 * s.re))
  have hM : Summable M := ((summable_integer_four_rpow (2 * s.re) (by linarith)).comp_injective
    (rowCoordinates_injective.comp cosetRow_injective)).mul_left _
  have hmajor (z : ℂ) (hz : z ∈ periodDomain) (x : CuspCosets) :
      ‖summand (a * upperSection (τ z) v hv) s x‖ ≤ M x := by
    apply (norm_summand_bound (a * upperSection (τ z) v hv) s (by linarith) x).trans
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (rowBound_pos _).le (hbound z hz) (by linarith)) (by positivity)
  have hchar : Continuous (fun z : ℂ => tracePhase (-freq * z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2 * Real.pi * Complex.I *
      ((-freq * z) + starRingEnd ℂ (-freq * z))))
    fun_prop
  exact hasSum_integral_of_dominated_convergence (μ := volume.restrict periodDomain)
    (fun (x : CuspCosets) (_ : ℂ) => M x)
    (fun x => (((continuous_fixed_left_summand a v hv s x).comp hτ).mul hchar).aestronglyMeasurable.restrict)
    (fun x => (ae_restrict_mem periodDomain_measurable).mono fun z hz => by
      simpa only [Pi.mul_apply, norm_mul, tracePhase_norm, mul_one] using hmajor z hz x)
    (Eventually.of_forall fun _ => hM) (integrable_const (∑' x, M x))
    (Eventually.of_forall fun z => (summable_summand (a * upperSection (τ z) v hv) s hs).hasSum.mul_right
      (tracePhase (-freq * z)))

lemma ninthCuspFrequency_three (h : O) : ninthCuspFrequency (3 * h) = cuspFrequency h := by
  simp only [ninthCuspFrequency, cuspFrequency, map_mul, map_ofNat]
  ring

/-- Scaling both cusp coordinates moves the factor three into the affine denominator. -/
lemma affineLowerTerm_scale_three (q r : O) (z : ℂ) (v : ℝ) (hv : 0 ≤ v) (s : ℂ) (a d : O) :
    affineLowerTerm q r (3 * z) (3 * v) s a d = (3 : ℂ) ^ s * affineLowerTerm (3 * q) r z v s a d := by
  have hq : ringComplex ((3 * q) * a) = 3 * ringComplex (q * a) := by
    simp only [map_mul, map_ofNat]
    ring
  have he : ‖ringComplex (q * a) * (3 * z) + ringComplex d‖ ^ 2 +
      ‖ringComplex (q * a)‖ ^ 2 * (3 * v) ^ 2 =
      ‖ringComplex ((3 * q) * a) * z + ringComplex d‖ ^ 2 +
        ‖ringComplex ((3 * q) * a)‖ ^ 2 * v ^ 2 := by
    rw [hq, show ringComplex (q * a) * (3 * z) = 3 * ringComplex (q * a) * z by ring]
    norm_num [norm_mul] <;> ring
  let D := ‖ringComplex ((3 * q) * a) * z + ringComplex d‖ ^ 2 +
    ‖ringComplex ((3 * q) * a)‖ ^ 2 * v ^ 2
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  rw [affineLowerTerm, affineLowerTerm, he]
  change _ * (((3 * v / D : ℝ) : ℂ) ^ s) = _
  have hp : ((3 : ℂ) * ((v / D : ℝ) : ℂ)) ^ s = (3 : ℂ) ^ s * ((v / D : ℝ) : ℂ) ^ s := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 3) (div_nonneg hv hD) s
  rw [show ((3 * v / D : ℝ) : ℂ) = (3 : ℂ) * ((v / D : ℝ) : ℂ) by push_cast; ring, hp]
  ring

lemma affineDenominator_nodiv_zero (h q a : O) (u : Oˣ) (n : ℕ)
    (ha : a ≠ 0) (hap : lambda ^ 2 ∣ a - 1) (hq : q ≠ 0)
    (hbase : (3 : O) ∣ h + ramifiedArithmeticPhase u n * q) (hfreq : ¬q ∣ h)
    (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (hsum : Summable (fun x : CoprimeElement a => affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s a x.1)) :
    (∑' x : CoprimeElement a, affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s a x.1) = 0 := by
  have hdiv : (3 : O) ∣ h + ramifiedArithmeticPhase u n * q * a := by
    convert dvd_add hbase ((three_dvd_primary_sub_one a hap).mul_left (ramifiedArithmeticPhase u n * q))
      using 1 <;> ring
  obtain ⟨ell, hell⟩ := hdiv
  have hne : ¬q ∣ ell := by
    intro hqell
    apply hfreq
    have hqe : q ∣ h + ramifiedArithmeticPhase u n * q * a := by
      rw [hell]
      exact hqell.mul_left 3
    convert dvd_sub hqe (show q ∣ ramifiedArithmeticPhase u n * q * a from
      ⟨ramifiedArithmeticPhase u n * a, by ring⟩) using 1 <;> ring
  let F : CoprimeElement a → ℂ := fun x => affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s a x.1
  let e := cubicResidueElementEquiv a ha
  have hp : Summable (fun p : CubicUnitResidue a × O => F (e p)) := e.summable_iff.mpr hsum
  change (∑' x, F x) = 0
  rw [← e.tsum_eq F, hp.tsum_prod]
  change (∑' x : CubicUnitResidue a, ∑' m : O,
    affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s a (principalResidueRep a x.1 + a * m)) = 0
  have hinner (x : CubicUnitResidue a) :
      (∑' m : O, affineLowerFourierTerm q ((u : O) * lambda ^ n) h v s a
        (principalResidueRep a x.1 + a * m)) = 0 := by
    unfold affineLowerFourierTerm
    rw [affineCusp_masked_inner h q a ell _ u n ha hap hq hell.symm v hv s hs, if_neg hne]
  simp only [hinner, tsum_zero]

/-- All arithmetic factors of a scaled affine branch, including its exact support. -/
def scaledAffineGaussSeries (q : O) (u : Oˣ) (n : ℕ) (h : O) (s : ℂ) : ℂ :=
  if hh : q ∣ h then
    let k := Classical.choose hh
    if (3 : O) ∣ k + ramifiedArithmeticPhase u n then
      (Ideal.absNorm (Ideal.span {3 * q}) : ℂ) * ((‖ringComplex (3 * q)‖ ^ 2 : ℝ) : ℂ) ^ (-s) *
        tracePhase (cuspFrequency h / ringComplex (3 * q)) *
          unramifiedCubicGaussSeries s (3 * ((u : O) * lambda ^ n) ^ 2 * k)
    else 0
  else 0

/-- Scaling by three makes the period congruence automatic at every frequency. -/
theorem scaledAffine_branch_fourier (q : O) (u : Oˣ) (n : ℕ) (h : O) (hq : q ≠ 0)
    (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (hsum : Summable (fun p : OppositeData => affineLowerFourierTerm (3 * q) ((u : O) * lambda ^ n)
      (3 * h) v s (primaryIdealGenerator p.1.1) p.2.1)) :
    (∑' p : OppositeData, affineLowerFourierTerm (3 * q) ((u : O) * lambda ^ n)
      (3 * h) v s (primaryIdealGenerator p.1.1) p.2.1) =
      ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (cuspFrequency h * v)) * scaledAffineGaussSeries q u n h s := by
  have h3 : (3 : O) ≠ 0 := by norm_num
  have hbase : (3 : O) ∣ 3 * h + ramifiedArithmeticPhase u n * (3 * q) :=
    ⟨h + ramifiedArithmeticPhase u n * q, by ring⟩
  by_cases hh : q ∣ h
  · rw [scaledAffineGaussSeries, dif_pos hh]
    have hk : 3 * h = (3 * q) * Classical.choose hh := by
      linear_combination 3 * Classical.choose_spec hh
    rw [affineCusp_branch_fourier_masked (3 * h) (Classical.choose hh) (3 * q) u n
      (mul_ne_zero h3 hq) hk hbase v hv s hs hsum, ninthCuspFrequency_three]
    dsimp only
    split_ifs <;> ring
  · rw [scaledAffineGaussSeries, dif_neg hh, mul_zero, hsum.tsum_sigma]
    have hn : ¬(3 * q) ∣ 3 * h := by
      rintro ⟨x, hx⟩
      apply hh
      refine ⟨x, mul_left_cancel₀ h3 ?_⟩
      linear_combination hx
    trans ∑' I : GoodIdeal, (0 : ℂ)
    · apply tsum_congr
      intro I
      exact affineDenominator_nodiv_zero (3 * h) (3 * q) _ u n I.2
        (primaryIdealGenerator_spec I.1 I.2).2 (mul_ne_zero h3 hq) hbase hn v hv s hs
          (hsum.sigma_factor I)
    · exact tsum_zero

lemma hasSum_scaled_unit_integrals (u t : Oˣ) (v : ℝ) (hv : 0 < v) (s : ℂ) (h : O) (hs : 2 < s.re) :
    HasSum (fun p : OppositeData => (3 : ℂ) ^ s *
      affineLowerFourierTerm (3 * (t : O)) ((↑u⁻¹ : O) ^ 2 * (t : O)) (3 * h) v s
        (primaryIdealGenerator p.1.1) p.2.1)
      (∫ z in periodDomain, eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
        integralComplexMatrix (lowerCuspMatrix (t : O)) * upperSection (3 * z) (3 * v) (by positivity)) s *
          tracePhase (-cuspFrequency h * z)) := by
  let e := (unitLowerDataEquiv (u⁻¹ ^ 2 * t)).trans primitiveRowEquiv.symm
  have he := e.hasSum_iff.mpr (hasSum_integral_fixed_left_Eisenstein_comp
    (integralComplexMatrix (unitCuspDiagonal u) * integralComplexMatrix (lowerCuspMatrix (t : O)))
      (3 * v) (by positivity) (fun z => 3 * z) (by fun_prop) s (cuspFrequency h) hs)
  apply he.congr_fun
  intro p
  rw [affineLowerFourierTerm, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only [e, Equiv.trans_apply, Function.comp_apply]
    rw [diagonal_unit_summand, affineLowerTerm_scale_three _ _ z v hv.le,
      ninthCuspFrequency_three]
    ring)

lemma hasSum_scaled_once_integrals (u t : Oˣ) (v : ℝ) (hv : 0 < v) (s : ℂ) (h : O) (hs : 2 < s.re) :
    HasSum (fun p : OnceRamifiedData => (3 : ℂ) ^ s *
      affineLowerFourierTerm (3 * (onceCuspScale t * omega ^ p.1.val))
        ((↑u⁻¹ : O) ^ 2 * (onceCuspScale t * omega ^ p.1.val)) (3 * h) v s
          (primaryIdealGenerator p.2.1.1) p.2.2.1)
      (∫ z in periodDomain, eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
        integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)) *
          upperSection (3 * z) (3 * v) (by positivity)) s * tracePhase (-cuspFrequency h * z)) := by
  let e := (onceRamifiedDataEquiv (u⁻¹ ^ 2 * t)).trans primitiveRowEquiv.symm
  have he := e.hasSum_iff.mpr (hasSum_integral_fixed_left_Eisenstein_comp
    (integralComplexMatrix (unitCuspDiagonal u) * integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)))
      (3 * v) (by positivity) (fun z => 3 * z) (by fun_prop) s (cuspFrequency h) hs)
  apply he.congr_fun
  intro p
  rw [affineLowerFourierTerm, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only [e, Equiv.trans_apply, Function.comp_apply]
    rw [diagonal_once_summand, affineLowerTerm_scale_three _ _ z v hv.le,
      ninthCuspFrequency_three]
    ring)

lemma summable_of_summable_const_mul {ι : Type*} (c : ℂ) (hc : c ≠ 0) (f : ι → ℂ)
    (hs : Summable (fun i => c * f i)) : Summable f := by
  have hh := hs.mul_left c⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hh

/-- The scaled unit-cusp coefficient is explicit at every frequency. -/
theorem scaled_unit_eisenstein_fourier (u t : Oˣ) (v : ℝ) (hv : 0 < v) (s : ℂ) (h : O) (hs : 2 < s.re) :
    (∫ z in periodDomain, eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (t : O)) * upperSection (3 * z) (3 * v) (by positivity)) s *
        tracePhase (-cuspFrequency h * z)) =
      (3 : ℂ) ^ s * ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (cuspFrequency h * v)) *
        scaledAffineGaussSeries (t : O) (u⁻¹ ^ 2 * t) 0 h s := by
  have he := hasSum_scaled_unit_integrals u t v hv s h hs
  have h3 : (3 : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hsum := summable_of_summable_const_mul _ h3 _ he.summable
  rw [← he.tsum_eq, tsum_mul_left]
  have hf := scaledAffine_branch_fourier (t : O) (u⁻¹ ^ 2 * t) 0 h t.ne_zero v hv s
    (by linarith) (by simpa only [pow_zero, mul_one, Units.val_mul, Units.val_pow_eq_pow_val] using hsum)
  simp only [pow_zero, mul_one, Units.val_mul, Units.val_pow_eq_pow_val] at hf
  rw [hf]
  ring

/-- Three explicit Gauss series give every scaled once-ramified cusp coefficient. -/
theorem scaled_once_eisenstein_fourier (u t : Oˣ) (v : ℝ) (hv : 0 < v) (s : ℂ) (h : O) (hs : 2 < s.re) :
    (∫ z in periodDomain, eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)) *
        upperSection (3 * z) (3 * v) (by positivity)) s * tracePhase (-cuspFrequency h * z)) =
      (3 : ℂ) ^ s * ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (cuspFrequency h * v)) *
        ∑ j : Fin 3, scaledAffineGaussSeries (onceCuspScale t * omega ^ j.val) (onceCuspArithmeticUnit u t j) 1 h s := by
  have he := hasSum_scaled_once_integrals u t v hv s h hs
  have h3 : (3 : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hsum := summable_of_summable_const_mul _ h3 _ he.summable
  rw [← he.tsum_eq, tsum_mul_left, hsum.tsum_prod, tsum_fintype]
  have hj (j : Fin 3) :
      (∑' p : OppositeData, affineLowerFourierTerm (3 * (onceCuspScale t * omega ^ j.val))
        ((↑u⁻¹ : O) ^ 2 * (onceCuspScale t * omega ^ j.val)) (3 * h) v s
          (primaryIdealGenerator p.1.1) p.2.1) =
        ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (cuspFrequency h * v)) *
          scaledAffineGaussSeries (onceCuspScale t * omega ^ j.val) (onceCuspArithmeticUnit u t j) 1 h s := by
    have hq := mul_ne_zero (onceCusp_scale_ne_zero t)
      (pow_ne_zero j.val (omega_primitive.isUnit (by decide)).ne_zero)
    have hf := scaledAffine_branch_fourier (onceCuspScale t * omega ^ j.val) (onceCuspArithmeticUnit u t j) 1
      h hq v hv s (by linarith)
        (by simpa only [pow_one, onceCuspArithmeticUnit_spec] using hsum.prod_factor j)
    simpa only [pow_one, onceCuspArithmeticUnit_spec] using hf
  simp_rw [hj]
  rw [← Finset.mul_sum]
  ring

def coprimeElementShift (a k : O) : CoprimeElement a ≃ CoprimeElement a where
  toFun x := ⟨x.1 + a * k,
    (isCoprime_right_congr_of_dvd a (x.1 + a * k) x.1 ⟨k, by ring⟩).mpr x.2⟩
  invFun x := ⟨x.1 - a * k,
    (isCoprime_right_congr_of_dvd a (x.1 - a * k) x.1 ⟨-k, by ring⟩).mpr x.2⟩
  left_inv x := Subtype.ext (add_sub_cancel_right _ _)
  right_inv x := Subtype.ext (sub_add_cancel _ _)

def oppositeDataShift (k : O) : OppositeData ≃ OppositeData :=
  Equiv.sigmaCongrRight (fun I => coprimeElementShift (primaryIdealGenerator I.1) k)

lemma oppositeDataShift_fst (k : O) (p : OppositeData) : (oppositeDataShift k p).1 = p.1 := rfl

lemma oppositeDataShift_snd (k : O) (p : OppositeData) :
    (oppositeDataShift k p).2.1 = p.2.1 + primaryIdealGenerator p.1.1 * k := rfl

lemma affineLowerTerm_scaled_period (q : O) (u : Oˣ) (n : ℕ) (a x m : O)
    (hap : lambda ^ 2 ∣ a - 1) (z : ℂ) (v : ℝ) (s : ℂ) :
    affineLowerTerm (3 * q) ((u : O) * lambda ^ n) (z + 3 * ringComplex m) v s a (a + 3 * x) =
      affineLowerTerm (3 * q) ((u : O) * lambda ^ n) z v s a (a + 3 * (x + a * (3 * q * m))) := by
  have hd (y : O) : (3 : O) ∣ a + 3 * y - 1 := by
    convert dvd_add (three_dvd_primary_sub_one a hap) (dvd_mul_right (3 : O) y) using 1 <;> ring
  have hchar : symbol ((u : O) * lambda ^ n) (a + 3 * x) =
      symbol ((u : O) * lambda ^ n) (a + 3 * (x + a * (3 * q * m))) :=
    ramified_symbol_congr_mod_nine u n _ _ (hd x) (hd _) ⟨-a * q * m, by ring⟩
  have hden : symbol (a + 3 * x) a = symbol (a + 3 * (x + a * (3 * q * m))) a :=
    symbol_congr ⟨-9 * q * m, by ring⟩
  have hrow : ringComplex ((3 * q) * a) * (z + 3 * ringComplex m) + ringComplex (a + 3 * x) =
      ringComplex ((3 * q) * a) * z + ringComplex (a + 3 * (x + a * (3 * q * m))) := by
    simp only [map_add, map_mul, map_ofNat]
    ring
  simp only [affineLowerTerm, hchar, hden, hrow]

lemma affineRowSeries_scaled_period (q : O) (u : Oˣ) (n : ℕ) (z : ℂ) (v : ℝ) (s : ℂ) (m : O) :
    (∑' p : OppositeData, affineLowerTerm (3 * q) ((u : O) * lambda ^ n)
      (z + 3 * ringComplex m) v s (primaryIdealGenerator p.1.1) (primaryIdealGenerator p.1.1 + 3 * p.2.1)) =
    ∑' p : OppositeData, affineLowerTerm (3 * q) ((u : O) * lambda ^ n)
      z v s (primaryIdealGenerator p.1.1) (primaryIdealGenerator p.1.1 + 3 * p.2.1) := by
  let F : OppositeData → ℂ := fun p => affineLowerTerm (3 * q) ((u : O) * lambda ^ n)
    z v s (primaryIdealGenerator p.1.1) (primaryIdealGenerator p.1.1 + 3 * p.2.1)
  rw [← (oppositeDataShift (3 * q * m)).tsum_eq F]
  apply tsum_congr
  intro p
  exact affineLowerTerm_scaled_period q u n _ p.2.1 m (primaryIdealGenerator_spec p.1.1 p.1.2).2 z v s

lemma diagonal_unit_eisenstein_rows (u t : Oˣ) (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (t : O)) * upperSection z v hv) s =
      ∑' p : OppositeData, affineLowerTerm (t : O) ((↑u⁻¹ : O) ^ 2 * (t : O)) z v s
        (primaryIdealGenerator p.1.1) (primaryIdealGenerator p.1.1 + 3 * p.2.1) := by
  let e := (unitLowerDataEquiv (u⁻¹ ^ 2 * t)).trans primitiveRowEquiv.symm
  change (∑' x : CuspCosets, summand _ s x) = _
  rw [← e.tsum_eq]
  exact tsum_congr (diagonal_unit_summand u t z v hv s)

lemma scaled_unit_eisenstein_period (u t : Oˣ) (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (m : O) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u) * integralComplexMatrix (lowerCuspMatrix (t : O)) *
      upperSection (3 * (z + 3 * ringComplex m)) (3 * v) (by positivity)) s =
    eisenstein (integralComplexMatrix (unitCuspDiagonal u) * integralComplexMatrix (lowerCuspMatrix (t : O)) *
      upperSection (3 * z) (3 * v) (by positivity)) s := by
  simp_rw [diagonal_unit_eisenstein_rows, affineLowerTerm_scale_three _ _ _ v hv.le, tsum_mul_left]
  congr 1
  have he := affineRowSeries_scaled_period (t : O) (u⁻¹ ^ 2 * t) 0 z v s m
  simpa only [pow_zero, mul_one, Units.val_mul, Units.val_pow_eq_pow_val] using he

def unitCuspUpper (b : O) : SL(2, O) := ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

lemma unitCuspUpper_section (b : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    integralComplexMatrix (unitCuspUpper b) * upperSection z v hv =
      upperSection (z + ringComplex b) v hv := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [unitCuspUpper, integralComplexMatrix, upperSection, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv, add_mul]

/-- Bruhat factorization of a rational cusp followed by a unit lower cusp. -/
lemma rational_cusp_lower_factor (u : Oˣ) (n : ℤ) :
    rationalEmbedding ModularGroup.S * unitCuspUpper (n : O) * lowerCuspMatrix (u : O) =
      unitCuspDiagonal (-u) * lowerCuspMatrix (-(u : O) * (1 + (n : O) * (u : O))) *
        unitCuspUpper (↑u⁻¹ : O) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hu : (u : O) * (↑u⁻¹ : O) = 1 := by simp
  fin_cases i <;> fin_cases j <;>
    simp [rationalEmbedding, ModularGroup.coe_S, unitCuspUpper, lowerCuspMatrix, unitCuspDiagonal,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination -(n : O) * hu

lemma rational_unipotent_upper (n : ℕ) : rationalEmbedding (ModularGroup.T ^ n) = unitCuspUpper (n : O) := by
  rw [← rationalUnipotent_nat]
  apply Subtype.ext
  rw [rationalUnipotent_embedding]
  rfl

lemma rational_cusp_lower_section (u : Oˣ) (n : ℕ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    rationalComplex ModularGroup.S * rationalComplex (ModularGroup.T ^ n) *
      integralComplexMatrix (lowerCuspMatrix (u : O)) * upperSection z v hv =
      integralComplexMatrix (unitCuspDiagonal (-u)) *
        integralComplexMatrix (lowerCuspMatrix (-(u : O) * (1 + (n : O) * (u : O)))) *
          upperSection (z + ringComplex (↑u⁻¹ : O)) v hv := by
  have hm := congrArg integralComplexMatrix (rational_cusp_lower_factor u (n : ℤ))
  simp only [map_mul, Int.cast_natCast] at hm
  have hu : integralComplexMatrix (unitCuspUpper (n : O)) = rationalComplex (ModularGroup.T ^ n) := by
    rw [← rational_unipotent_upper]
    rfl
  rw [hu] at hm
  change rationalComplex ModularGroup.S * rationalComplex (ModularGroup.T ^ n) *
    integralComplexMatrix (lowerCuspMatrix (u : O)) = _ at hm
  rw [hm, mul_assoc, unitCuspUpper_section]

def onceRamifiedDataShift (t : Oˣ) (m : O) : OnceRamifiedData ≃ OnceRamifiedData where
  toFun p := (p.1, oppositeDataShift (3 * (onceCuspScale t * omega ^ p.1.val) * m) p.2)
  invFun p := (p.1, (oppositeDataShift (3 * (onceCuspScale t * omega ^ p.1.val) * m)).symm p.2)
  left_inv p := by
    change (p.1, (oppositeDataShift _).symm (oppositeDataShift _ p.2)) = p
    rw [Equiv.symm_apply_apply]
  right_inv p := by
    change (p.1, oppositeDataShift _ ((oppositeDataShift _).symm p.2)) = p
    rw [Equiv.apply_symm_apply]

lemma diagonal_once_eisenstein_rows (u t : Oˣ) (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)) * upperSection z v hv) s =
      ∑' p : OnceRamifiedData, affineLowerTerm (onceCuspScale t * omega ^ p.1.val)
        ((↑u⁻¹ : O) ^ 2 * (onceCuspScale t * omega ^ p.1.val)) z v s
          (primaryIdealGenerator p.2.1.1) (primaryIdealGenerator p.2.1.1 + 3 * p.2.2.1) := by
  let e := (onceRamifiedDataEquiv (u⁻¹ ^ 2 * t)).trans primitiveRowEquiv.symm
  change (∑' x : CuspCosets, summand _ s x) = _
  rw [← e.tsum_eq]
  exact tsum_congr (diagonal_once_summand u t z v hv s)

lemma scaled_once_eisenstein_period (u t : Oˣ) (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (m : O) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)) *
        upperSection (3 * (z + 3 * ringComplex m)) (3 * v) (by positivity)) s =
    eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)) *
        upperSection (3 * z) (3 * v) (by positivity)) s := by
  simp_rw [diagonal_once_eisenstein_rows, affineLowerTerm_scale_three _ _ _ v hv.le, tsum_mul_left]
  congr 1
  let F : OnceRamifiedData → ℂ := fun p => affineLowerTerm (3 * (onceCuspScale t * omega ^ p.1.val))
    ((↑u⁻¹ : O) ^ 2 * (onceCuspScale t * omega ^ p.1.val)) z v s
      (primaryIdealGenerator p.2.1.1) (primaryIdealGenerator p.2.1.1 + 3 * p.2.2.1)
  rw [← (onceRamifiedDataShift t m).tsum_eq F]
  apply tsum_congr
  intro p
  dsimp only [F, onceRamifiedDataShift, Equiv.coe_fn_mk]
  simp only [oppositeDataShift_fst, oppositeDataShift_snd]
  have he := affineLowerTerm_scaled_period (onceCuspScale t * omega ^ p.1.val)
    (onceCuspArithmeticUnit u t p.1) 1 _ p.2.2.1 m (primaryIdealGenerator_spec p.2.1.1 p.2.1.2).2 z v s
  simpa only [pow_one, onceCuspArithmeticUnit_spec] using he

lemma hyperbolicEisenstein_fixed_upper (g : SL(2, ℂ)) (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) :
    hyperbolicEisenstein s (g • upperPoint z v hv) = eisenstein (g * upperSection z v hv) s := rfl

/-- The four projected cusps become three unit branches and one once-ramified cusp. -/
theorem rationalSourceEisenstein_primitive_lower_four (u t : Oˣ)
    (hu : (u : O) ^ 2 + (u : O) + 1 = 0) (ht : -(u : O) * (1 + 2 * (u : O)) = onceCuspScale t)
    (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    rationalSourceEisenstein s (integralComplexMatrix (lowerCuspMatrix (u : O)) • upperPoint z v hv) =
      (4 : ℂ)⁻¹ * (eisenstein (integralComplexMatrix (lowerCuspMatrix (u : O)) * upperSection z v hv) s +
        eisenstein (integralComplexMatrix (unitCuspDiagonal (-u)) *
          integralComplexMatrix (lowerCuspMatrix (-(u : O))) * upperSection (z + ringComplex (↑u⁻¹ : O)) v hv) s +
        eisenstein (integralComplexMatrix (unitCuspDiagonal (-u)) *
          integralComplexMatrix (lowerCuspMatrix 1) * upperSection (z + ringComplex (↑u⁻¹ : O)) v hv) s +
        eisenstein (integralComplexMatrix (unitCuspDiagonal (-u)) *
          integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)) *
            upperSection (z + ringComplex (↑u⁻¹ : O)) v hv) s) := by
  have hu1 : -(u : O) * (1 + (u : O)) = 1 := by linear_combination -hu
  have h0 := rational_cusp_lower_section u 0 z v hv
  have h1 := rational_cusp_lower_section u 1 z v hv
  have h2 := rational_cusp_lower_section u 2 z v hv
  simp only [Nat.cast_zero, zero_mul, add_zero, mul_one, pow_zero, map_one] at h0
  simp only [Nat.cast_one, one_mul, pow_one, hu1] at h1
  simp only [Nat.cast_ofNat, ht] at h2
  rw [rationalSourceEisenstein_four_cusps s hs, fourCuspAverage]
  simp only [map_mul, ← mul_smul, hyperbolicEisenstein_fixed_upper, ← mul_assoc]
  rw [h0, h1, h2]

lemma unitCuspDiagonal_one : unitCuspDiagonal 1 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [unitCuspDiagonal]

lemma integrable_scaled_cusp_eisenstein (g : SL(2, ℂ)) (v : ℝ) (hv : 0 < v)
    (s : ℂ) (hs : 2 < s.re) (b : ℂ) (h : O) :
    IntegrableOn (fun z : ℂ => eisenstein (g * upperSection (3 * z + b) (3 * v) (by positivity)) s *
      tracePhase (-cuspFrequency h * z)) periodDomain := by
  have hcoord : Continuous (fun z : ℂ => (⟨(3 * z + b, 3 * v), by positivity⟩ : UpperCoordinates)) := by fun_prop
  have hu : Continuous (fun z : ℂ => upperPoint (3 * z + b) (3 * v) (by positivity)) :=
    upperCoordinatesHomeomorph.continuous.comp hcoord
  have hf := (hyperbolicEisenstein_continuous s hs).comp ((continuous_hyperbolic_action g).comp hu)
  apply periodDomain_continuous_integrable
  exact hf.mul (tracePhase_continuous.comp (continuous_const.mul continuous_id))

lemma scaled_unit_eisenstein_fourier_shift (u t : Oˣ) (v : ℝ) (hv : 0 < v) (s : ℂ) (h : O)
    (hs : 2 < s.re) (b : ℂ) :
    (∫ z in periodDomain, eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (t : O)) * upperSection (3 * z + b) (3 * v) (by positivity)) s *
        tracePhase (-cuspFrequency h * z)) =
      tracePhase (cuspFrequency h * (b / 3)) *
        ((3 : ℂ) ^ s * ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (cuspFrequency h * v)) *
          scaledAffineGaussSeries (t : O) (u⁻¹ ^ 2 * t) 0 h s) := by
  have he := period_fourier_translation
    (fun z => eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (t : O)) * upperSection (3 * z) (3 * v) (by positivity)) s)
    (fun m z => scaled_unit_eisenstein_period u t z v hv s m) h (b / 3)
  simp_rw [show ∀ z : ℂ, 3 * (z + b / 3) = 3 * z + b by intro z; ring] at he
  rw [scaled_unit_eisenstein_fourier u t v hv s h hs] at he
  exact he

lemma scaled_once_eisenstein_fourier_shift (u t : Oˣ) (v : ℝ) (hv : 0 < v) (s : ℂ) (h : O)
    (hs : 2 < s.re) (b : ℂ) :
    (∫ z in periodDomain, eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)) *
        upperSection (3 * z + b) (3 * v) (by positivity)) s * tracePhase (-cuspFrequency h * z)) =
      tracePhase (cuspFrequency h * (b / 3)) *
        ((3 : ℂ) ^ s * ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (cuspFrequency h * v)) *
          ∑ j : Fin 3, scaledAffineGaussSeries (onceCuspScale t * omega ^ j.val) (onceCuspArithmeticUnit u t j) 1 h s) := by
  have he := period_fourier_translation
    (fun z => eisenstein (integralComplexMatrix (unitCuspDiagonal u) *
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)) *
        upperSection (3 * z) (3 * v) (by positivity)) s)
    (fun m z => scaled_once_eisenstein_period u t z v hv s m) h (b / 3)
  simp_rw [show ∀ z : ℂ, 3 * (z + b / 3) = 3 * z + b by intro z; ring] at he
  rw [scaled_once_eisenstein_fourier u t v hv s h hs] at he
  exact he

/-- Six unramified Gauss branches describe a projected ramified cusp. -/
def ramifiedCuspGaussSeries (u t : Oˣ) (h : O) (s : ℂ) : ℂ :=
  (4 : ℂ)⁻¹ * (scaledAffineGaussSeries (u : O) u 0 h s +
    tracePhase (cuspFrequency h * (ringComplex (↑u⁻¹ : O) / 3)) *
      (scaledAffineGaussSeries (-(u : O)) ((-u)⁻¹ ^ 2 * (-u)) 0 h s +
        scaledAffineGaussSeries 1 ((-u)⁻¹ ^ 2) 0 h s +
          ∑ j : Fin 3, scaledAffineGaussSeries (onceCuspScale t * omega ^ j.val)
            (onceCuspArithmeticUnit (-u) t j) 1 h s))

/-- Every Fourier coefficient of the scaled ramified source has an explicit six-branch factorization. -/
theorem ramifiedSourceEisenstein_scaled_fourier (u t : Oˣ)
    (hu : (u : O) ^ 2 + (u : O) + 1 = 0) (ht : -(u : O) * (1 + 2 * (u : O)) = onceCuspScale t)
    (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) (h : O) :
    (∫ z in periodDomain, rationalSourceEisenstein s
      (integralComplexMatrix (lowerCuspMatrix (u : O)) • upperPoint (3 * z) (3 * v) (by positivity)) *
        tracePhase (-cuspFrequency h * z)) =
      (3 : ℂ) ^ s * ((v : ℂ) ^ (2 - s) * sourceFourierKernel s (cuspFrequency h * v)) *
        ramifiedCuspGaussSeries u t h s := by
  let b := ringComplex (↑u⁻¹ : O)
  let f0 : ℂ → ℂ := fun z => eisenstein (integralComplexMatrix (lowerCuspMatrix (u : O)) *
    upperSection (3 * z) (3 * v) (by positivity)) s * tracePhase (-cuspFrequency h * z)
  let f1 : ℂ → ℂ := fun z => eisenstein (integralComplexMatrix (unitCuspDiagonal (-u)) *
    integralComplexMatrix (lowerCuspMatrix (-(u : O))) * upperSection (3 * z + b) (3 * v) (by positivity)) s *
      tracePhase (-cuspFrequency h * z)
  let f2 : ℂ → ℂ := fun z => eisenstein (integralComplexMatrix (unitCuspDiagonal (-u)) *
    integralComplexMatrix (lowerCuspMatrix 1) * upperSection (3 * z + b) (3 * v) (by positivity)) s *
      tracePhase (-cuspFrequency h * z)
  let f3 : ℂ → ℂ := fun z => eisenstein (integralComplexMatrix (unitCuspDiagonal (-u)) *
    integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)) *
      upperSection (3 * z + b) (3 * v) (by positivity)) s * tracePhase (-cuspFrequency h * z)
  have hi0 : IntegrableOn f0 periodDomain := by
    simpa only [f0, add_zero] using integrable_scaled_cusp_eisenstein
      (integralComplexMatrix (lowerCuspMatrix (u : O))) v hv s hs 0 h
  have hi1 : IntegrableOn f1 periodDomain := integrable_scaled_cusp_eisenstein _ v hv s hs b h
  have hi2 : IntegrableOn f2 periodDomain := integrable_scaled_cusp_eisenstein _ v hv s hs b h
  have hi3 : IntegrableOn f3 periodDomain := integrable_scaled_cusp_eisenstein _ v hv s hs b h
  have hpoint (z : ℂ) : rationalSourceEisenstein s
      (integralComplexMatrix (lowerCuspMatrix (u : O)) • upperPoint (3 * z) (3 * v) (by positivity)) *
        tracePhase (-cuspFrequency h * z) = (4 : ℂ)⁻¹ * (f0 z + f1 z + f2 z + f3 z) := by
    rw [rationalSourceEisenstein_primitive_lower_four u t hu ht _ _ _ s hs]
    dsimp only [f0, f1, f2, f3, b]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul,
    integral_add (f := fun z => f0 z + f1 z + f2 z) (g := f3) ((hi0.add hi1).add hi2) hi3,
    integral_add (f := fun z => f0 z + f1 z) (g := f2) (hi0.add hi1) hi2,
    integral_add (f := f0) (g := f1) hi0 hi1]
  have h0 := scaled_unit_eisenstein_fourier 1 u v hv s h hs
  simp only [unitCuspDiagonal_one, map_one, one_mul, inv_one, one_pow] at h0
  have h1 := scaled_unit_eisenstein_fourier_shift (-u) (-u) v hv s h hs b
  have h2 := scaled_unit_eisenstein_fourier_shift (-u) 1 v hv s h hs b
  have h3 := scaled_once_eisenstein_fourier_shift (-u) t v hv s h hs b
  simp only [Units.val_neg] at h1
  simp only [Units.val_one, mul_one] at h2
  change (4 : ℂ)⁻¹ * ((∫ z in periodDomain, f0 z) + (∫ z in periodDomain, f1 z) +
    (∫ z in periodDomain, f2 z) + (∫ z in periodDomain, f3 z)) = _
  rw [h0, h1, h2, h3]
  unfold ramifiedCuspGaussSeries
  dsimp only [b]
  ring

/-- Compact support of a height-strip test after an arbitrary hyperbolic translation. -/
def arbitraryCuspCompact (M : SL(2, ℂ)) (a b : ℝ) : Set HyperbolicSpace :=
  (fun w => M • w) '' cuspIntervalHull a b

lemma arbitraryCuspCompact_isCompact (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a) :
    IsCompact (arbitraryCuspCompact M a b) :=
  (cuspIntervalHull_isCompact a b ha).image (continuous_hyperbolic_action M)

lemma arbitraryCusp_projection_bound (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a) :
    Measure.map (fun w => integralOrbitProjection globalKubotaKernel (M • w))
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) ≤
        (kernelCompactMultiplicity (arbitraryCuspCompact M a b)
          (arbitraryCuspCompact_isCompact M a b ha) : ℝ≥0∞) • integralQuotientVolume globalKubotaKernel := by
  have hmap := (measurePreserving_smul M hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul M) (cuspPeriodStrip a b)
  change Measure.map ((integralOrbitProjection globalKubotaKernel) ∘ (fun w : HyperbolicSpace => M • w)) _ ≤ _
  rw [← Measure.map_map (measurable_integralOrbitProjection _) (measurable_const_smul M), hmap.map_eq]
  apply le_trans _ (kernelCompactMultiplicity_spec _ (arbitraryCuspCompact_isCompact M a b ha))
  apply Measure.map_mono _ (measurable_integralOrbitProjection _)
  exact Measure.restrict_mono_set hyperbolicVolume (Set.image_mono (cuspPeriodStrip_subset_intervalHull a b))

lemma arbitraryCusp_quasiMeasurePreserving (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a) :
    Measure.QuasiMeasurePreserving (fun w => integralOrbitProjection globalKubotaKernel (M • w))
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) (integralQuotientVolume globalKubotaKernel) :=
  ⟨(measurable_integralOrbitProjection _).comp (measurable_const_smul M),
    Measure.absolutelyContinuous_of_le_smul (arbitraryCusp_projection_bound M a b ha)⟩

/-- Compact multiplicity gives a bounded pullback without a quotient action of the translating matrix. -/
def arbitraryCuspPullback (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a) :
    KernelQuotientL2 →L[ℂ] Lp ℂ 2 (hyperbolicVolume.restrict (cuspPeriodStrip a b)) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun w => integralOrbitProjection globalKubotaKernel (M • w))
    ⟨(measurable_integralOrbitProjection _).comp (measurable_const_smul M), rfl⟩).toContinuousLinearMap.comp
      (dominatedComplexL2 (by simp) (arbitraryCusp_projection_bound M a b ha))

lemma arbitraryCuspPullback_ae (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a) (F : KernelQuotientL2) :
    arbitraryCuspPullback M a b ha F =ᵐ[hyperbolicVolume.restrict (cuspPeriodStrip a b)]
      fun w => F (integralOrbitProjection globalKubotaKernel (M • w)) := by
  have hm : MeasurePreserving (fun w => integralOrbitProjection globalKubotaKernel (M • w))
      (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      (Measure.map (fun w => integralOrbitProjection globalKubotaKernel (M • w))
        (hyperbolicVolume.restrict (cuspPeriodStrip a b))) :=
    ⟨(measurable_integralOrbitProjection _).comp (measurable_const_smul M), rfl⟩
  exact (Lp.coeFn_compMeasurePreserving _ hm).trans (hm.quasiMeasurePreserving.ae_eq_comp
    (dominatedComplexL2_ae (by simp) (arbitraryCusp_projection_bound M a b ha) F))

def arbitraryCuspQuotientCompact (M : SL(2, ℂ)) (a b : ℝ) : Set KernelQuotient :=
  integralOrbitProjection globalKubotaKernel '' arbitraryCuspCompact M a b

lemma arbitraryCuspQuotientCompact_isCompact (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a) :
    IsCompact (arbitraryCuspQuotientCompact M a b) :=
  (arbitraryCuspCompact_isCompact M a b ha).image (continuous_integralOrbitProjection _)

lemma arbitraryCusp_mem_compact (M : SL(2, ℂ)) (a b : ℝ) (w : HyperbolicSpace)
    (hw : w ∈ cuspPeriodStrip a b) :
    integralOrbitProjection globalKubotaKernel (M • w) ∈ arbitraryCuspQuotientCompact M a b :=
  ⟨M • w, ⟨w, cuspPeriodStrip_subset_intervalHull a b hw, rfl⟩, rfl⟩

def arbitraryCuspHeightFourier (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) : KernelQuotientL2 →L[ℂ] ℂ :=
  (innerSL ℂ ((cuspIntervalWeightedFourier_memLp a b ha ρ h).toLp
    (fun w => star (cuspWeightedFourierPhase ρ h w)))).comp (arbitraryCuspPullback M a b ha)

lemma arbitraryCuspHeightFourier_integral (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (F : KernelQuotientL2) :
    arbitraryCuspHeightFourier M a b ha ρ h F = ∫ w in cuspPeriodStrip a b,
      F (integralOrbitProjection globalKubotaKernel (M • w)) * cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume := by
  change inner ℂ _ (arbitraryCuspPullback M a b ha F) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (cuspIntervalWeightedFourier_memLp a b ha ρ h),
    arbitraryCuspPullback_ae M a b ha F] with w hw hp
  rw [RCLike.inner_apply, hw, hp]
  simp only [starRingEnd_apply, star_star]

lemma arbitraryCuspHeightFourier_restrict (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (F : KernelQuotientL2) :
    arbitraryCuspHeightFourier M a b ha ρ h
      (kernelMassRestrictionCLM (arbitraryCuspQuotientCompact M a b)
        (arbitraryCuspQuotientCompact_isCompact M a b ha).measurableSet F) =
      arbitraryCuspHeightFourier M a b ha ρ h F := by
  rw [arbitraryCuspHeightFourier_integral, arbitraryCuspHeightFourier_integral]
  have he := (arbitraryCusp_quasiMeasurePreserving M a b ha).ae_eq_comp
    (kernelMassRestriction_coe _ (arbitraryCuspQuotientCompact_isCompact M a b ha).measurableSet F)
  apply integral_congr_ae
  filter_upwards [he, ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  exact congrArg (fun z : ℂ => z * cuspWeightedFourierPhase ρ h w)
    (hw.trans (Set.indicator_of_mem (arbitraryCusp_mem_compact M a b w hwm) _))

def arbitraryCuspHeightFamily (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (s : ℂ) : ℂ :=
  arbitraryCuspHeightFourier M a b ha ρ h
    (kernelLocalCorrectedSeed (arbitraryCuspQuotientCompact M a b)
      (arbitraryCuspQuotientCompact_isCompact M a b ha) 2 3 (by norm_num) (by norm_num) s)

lemma arbitraryCuspHeightFamily_analyticAt (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (s : ℂ) (hs : 1 < s.re) (hi : 0 < s.im) :
    AnalyticAt ℂ (arbitraryCuspHeightFamily M a b ha ρ h) s :=
  (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (arbitraryCuspHeightFourier M a b ha ρ h) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _ (arbitraryCuspQuotientCompact_isCompact M a b ha)
        2 3 (by norm_num) (by norm_num) s hs.ne' hi.ne') rfl

lemma arbitraryCuspHeightFamily_residue_limit (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    Tendsto (fun s : ℂ => (s - 4 / 3) * arbitraryCuspHeightFamily M a b ha ρ h s)
      (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (arbitraryCuspHeightFourier M a b ha ρ h cubicEisensteinResidue)) := by
  have he := (arbitraryCuspHeightFourier M a b ha ρ h).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit _ (arbitraryCuspQuotientCompact_isCompact M a b ha))
  simpa only [Function.comp_def, map_smul, smul_eq_mul, arbitraryCuspHeightFourier_restrict,
    arbitraryCuspHeightFamily] using he

lemma arbitraryCuspHeightFamily_initial (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im) :
    arbitraryCuspHeightFamily M a b ha ρ h s = ∫ w in cuspPeriodStrip a b,
      hyperbolicEisenstein s (M • w) * cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume := by
  rw [arbitraryCuspHeightFamily, arbitraryCuspHeightFourier_integral]
  have he := (arbitraryCusp_quasiMeasurePreserving M a b ha).ae_eq_comp
    (cubicEisensteinLocalFamily_initial_ae _ (arbitraryCuspQuotientCompact_isCompact M a b ha) s hs hi)
  apply integral_congr_ae
  filter_upwards [he, ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  dsimp only [Function.comp_def] at hw
  rw [hw, Set.indicator_of_mem (arbitraryCusp_mem_compact M a b w hwm), kernelQuotientEisenstein_mk]

lemma arbitraryCuspHeightFourier_residual_integral (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    arbitraryCuspHeightFourier M a b ha ρ h cubicEisensteinResidue = ∫ w in cuspPeriodStrip a b,
      cubicResidualFunction (M • w) * cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume := by
  rw [arbitraryCuspHeightFourier_integral]
  have he := (measurePreserving_smul M hyperbolicVolume).quasiMeasurePreserving.ae_eq_comp
    cubicEisensteinResidue_continuous_representative
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae he] with w hw
  exact congrArg (fun z : ℂ => z * cuspWeightedFourierPhase ρ h w) hw

abbrev RationalFourCusp := Unit ⊕ (Unit ⊕ (Unit ⊕ Unit))

def rationalFourCuspRep : RationalFourCusp → SL(2, ℤ)
  | .inl _ => 1
  | .inr (.inl _) => ModularGroup.S
  | .inr (.inr (.inl _)) => ModularGroup.S * ModularGroup.T
  | .inr (.inr (.inr _)) => ModularGroup.S * ModularGroup.T ^ 2

lemma fourCuspAverage_eq_sum (f : HyperbolicSpace → ℂ) (M : SL(2, ℂ)) (w : HyperbolicSpace) :
    fourCuspAverage f (M • w) =
      (4 : ℂ)⁻¹ * ∑ i : RationalFourCusp, f ((rationalComplex (rationalFourCuspRep i) * M) • w) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, rationalFourCuspRep, map_one, one_mul, one_smul,
    mul_smul, fourCuspAverage]
  ring

lemma cuspStrip_integrable_continuous (a b : ℝ) (ha : 0 < a)
    (f : HyperbolicSpace → ℂ) (hf : Continuous f) :
    IntegrableOn f (cuspPeriodStrip a b) hyperbolicVolume :=
  (hf.continuousOn.integrableOn_compact (cuspIntervalHull_isCompact a b ha)).mono_set
    (cuspPeriodStrip_subset_intervalHull a b)

lemma fourCuspAverage_weighted_integral (f : HyperbolicSpace → ℂ) (hf : Continuous f)
    (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a) (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    (∫ w in cuspPeriodStrip a b, fourCuspAverage f (M • w) * cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume) =
      (4 : ℂ)⁻¹ * ∑ i : RationalFourCusp, ∫ w in cuspPeriodStrip a b,
        f ((rationalComplex (rationalFourCuspRep i) * M) • w) * cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume := by
  have hi (i : RationalFourCusp) : IntegrableOn
      (fun w => f ((rationalComplex (rationalFourCuspRep i) * M) • w) * cuspWeightedFourierPhase ρ h w)
      (cuspPeriodStrip a b) hyperbolicVolume :=
    cuspStrip_integrable_continuous a b ha _ ((hf.comp (continuous_hyperbolic_action _)).mul
      (cuspWeightedFourierPhase_continuous ρ h))
  simp_rw [fourCuspAverage_eq_sum, mul_assoc, Finset.sum_mul]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]

def sourceArbitraryHeightFamily (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (s : ℂ) : ℂ :=
  (4 : ℂ)⁻¹ * ∑ i : RationalFourCusp,
    arbitraryCuspHeightFamily (rationalComplex (rationalFourCuspRep i) * M) a b ha ρ h s

def sourceArbitraryHeightFourier (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) : KernelQuotientL2 →L[ℂ] ℂ :=
  (4 : ℂ)⁻¹ • ∑ i : RationalFourCusp,
    arbitraryCuspHeightFourier (rationalComplex (rationalFourCuspRep i) * M) a b ha ρ h

lemma sourceArbitraryHeightFamily_analyticAt (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (s : ℂ) (hs : 1 < s.re) (hi : 0 < s.im) :
    AnalyticAt ℂ (sourceArbitraryHeightFamily M a b ha ρ h) s := by
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro i hi'
  exact arbitraryCuspHeightFamily_analyticAt _ a b ha ρ h s hs hi

lemma sourceArbitraryHeightFamily_residue_limit (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    Tendsto (fun s : ℂ => (s - 4 / 3) * sourceArbitraryHeightFamily M a b ha ρ h s)
      (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (sourceArbitraryHeightFourier M a b ha ρ h cubicEisensteinResidue)) := by
  have he := (tendsto_finsetSum Finset.univ (fun i _ =>
    arbitraryCuspHeightFamily_residue_limit (rationalComplex (rationalFourCuspRep i) * M) a b ha ρ h)).const_mul ((4 : ℂ)⁻¹)
  convert he using 1
  · funext s
    rw [sourceArbitraryHeightFamily, ← Finset.mul_sum]
    ring
  · simp only [sourceArbitraryHeightFourier, _root_.smul_apply, _root_.sum_apply, smul_eq_mul]

lemma sourceArbitraryHeightFamily_initial (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) (s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im) :
    sourceArbitraryHeightFamily M a b ha ρ h s = ∫ w in cuspPeriodStrip a b,
      rationalSourceEisenstein s (M • w) * cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume := by
  simp_rw [rationalSourceEisenstein_four_cusps s (by linarith)]
  rw [fourCuspAverage_weighted_integral _ (hyperbolicEisenstein_continuous s (by linarith)) M a b ha ρ h]
  unfold sourceArbitraryHeightFamily
  congr 1
  apply Finset.sum_congr rfl
  intro i hi'
  exact arbitraryCuspHeightFamily_initial _ a b ha ρ h s hs hi

lemma sourceArbitraryHeightFourier_residual_integral (M : SL(2, ℂ)) (a b : ℝ) (ha : 0 < a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : O) :
    sourceArbitraryHeightFourier M a b ha ρ h cubicEisensteinResidue = ∫ w in cuspPeriodStrip a b,
      cubicSourceResidualFunction (M • w) * cuspWeightedFourierPhase ρ h w ∂hyperbolicVolume := by
  simp_rw [cubicSourceResidualFunction_four_cusps]
  rw [fourCuspAverage_weighted_integral _ cubicResidualFunction_continuous M a b ha ρ h]
  simp only [sourceArbitraryHeightFourier, _root_.smul_apply, _root_.sum_apply, smul_eq_mul,
    arbitraryCuspHeightFourier_residual_integral]

/-- Finite Gauss-series identities pass to residues through the native scalar continuation theorem. -/
theorem finite_unramified_residue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (index : ι → O) (coefficient : ι → ℂ → ℂ)
    (hc : ∀ i s, 1 < s.re → AnalyticAt ℂ (coefficient i) s)
    (f : ℂ → ℂ) (R : ℂ) (hf : ∀ s, 1 < s.re → 0 < s.im → AnalyticAt ℂ f s)
    (hlim : Tendsto (fun s : ℂ => (s - 4 / 3) * f s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 R))
    (hinit : ∀ s : ℂ, 4 < s.re → 0 < s.im →
      f s = ∑ i, coefficient i s * unramifiedCubicGaussSeries s (index i)) :
    R = ∑ i, coefficient i (4 / 3) * unramifiedGaussResidue (index i) := by
  let H : ι → ℂ → ℂ := fun i s => cuspWhittakerHeightFactor s (3 * index i)
  let G : ι → ℂ → ℂ := fun i s => rationalCuspFamily (3 * index i) oppositeSource 2 3
    (by norm_num) (by norm_num) s
  let D : ℂ → ℂ := fun s => ∏ i, H i s
  let E : ι → ℂ → ℂ := fun i s => ∏ j ∈ Finset.univ.erase i, H j s
  let Bsum : ℂ → ℂ := fun s => ∑ i, coefficient i s * G i s * E i s
  let R1 : ℂ := ∑ i, coefficient i (4 / 3) *
    rationalCuspFourier (3 * index i) oppositeSource cubicEisensteinResidue * E i (4 / 3)
  have hH (i : ι) (s : ℂ) (hs : 1 < s.re) : AnalyticAt ℂ (H i) s :=
    cuspWhittakerHeightFactor_analyticAt (3 * index i) s hs
  have hD (s : ℂ) (hs : 1 < s.re) : AnalyticAt ℂ D s :=
    Finset.analyticAt_fun_prod _ (fun i _ => hH i s hs)
  have hE (i : ι) (s : ℂ) (hs : 1 < s.re) : AnalyticAt ℂ (E i) s :=
    Finset.analyticAt_fun_prod _ (fun j _ => hH j s hs)
  have hprod (i : ι) (s : ℂ) : H i s * E i s = D s :=
    Finset.mul_prod_erase Finset.univ (fun j => H j s) (Finset.mem_univ i)
  have hT : AnalyticOnNhd ℂ Bsum {s : ℂ | 1 < s.re ∧ 0 < s.im} := by
    intro s hs
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact ((hc i s hs.1).mul (rationalCuspFamily_analyticAt_nonreal (3 * index i)
      oppositeSource 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')).mul (hE i s hs.1)
  have hTR : Tendsto (fun s : ℂ => (s - 4 / 3) * Bsum s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 R1) := by
    have hi (i : ι) := (((hc i (4 / 3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      (rationalCuspFamily_residue_limit (3 * index i) oppositeSource 2 3 (by norm_num) (by norm_num))).mul
        ((hE i (4 / 3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    convert tendsto_finsetSum Finset.univ (fun i _ => hi i) using 1
    · funext s
      dsimp only [Bsum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi'
      dsimp only [G]
      ring
    · rfl
  have he := cuspScalarResidue_cross f Bsum (fun _ => 1) D R R1
    (fun s hs => hf s hs.1 hs.2) hT (fun _ _ => analyticAt_const)
    (fun s hs => hD s hs.1) continuousAt_const (hD (4 / 3) (by norm_num)).continuousAt hlim hTR (by
      intro s hs hi
      rw [hinit s hs hi, Finset.sum_mul, mul_one]
      apply Finset.sum_congr rfl
      intro i hi'
      dsimp only [G]
      rw [rationalCuspFamily_opposite_initial (index i) s hs hi, ← hprod i s]
      ring)
  have hDn : D (4 / 3) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => cuspWhittakerHeightFactor_center_ne_zero (3 * index i))
  apply mul_right_cancel₀ hDn
  rw [he, mul_one, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  change coefficient i (4 / 3) * rationalCuspFourier (3 * index i) oppositeSource cubicEisensteinResidue *
    E i (4 / 3) = coefficient i (4 / 3) *
      (rationalCuspFourier (3 * index i) oppositeSource cubicEisensteinResidue / H i (4 / 3)) * D (4 / 3)
  rw [← hprod i (4 / 3)]
  field_simp [show H i (4 / 3) ≠ 0 from cuspWhittakerHeightFactor_center_ne_zero (3 * index i)]

def scaledAffineGaussIndex (q : O) (u : Oˣ) (n : ℕ) (h : O) : O :=
  if hh : q ∣ h then 3 * ((u : O) * lambda ^ n) ^ 2 * Classical.choose hh else 0

def scaledAffineGaussWeight (q : O) (u : Oˣ) (n : ℕ) (h : O) (s : ℂ) : ℂ :=
  if hh : q ∣ h then
    if (3 : O) ∣ Classical.choose hh + ramifiedArithmeticPhase u n then
      (Ideal.absNorm (Ideal.span {3 * q}) : ℂ) * ((‖ringComplex (3 * q)‖ ^ 2 : ℝ) : ℂ) ^ (-s) *
        tracePhase (cuspFrequency h / ringComplex (3 * q))
    else 0
  else 0

lemma scaledAffineGaussSeries_factor (q : O) (u : Oˣ) (n : ℕ) (h : O) (s : ℂ) :
    scaledAffineGaussSeries q u n h s =
      scaledAffineGaussWeight q u n h s * unramifiedCubicGaussSeries s (scaledAffineGaussIndex q u n h) := by
  unfold scaledAffineGaussSeries scaledAffineGaussWeight scaledAffineGaussIndex
  dsimp only
  split_ifs <;> simp_all only [zero_mul]

lemma scaledAffineGaussWeight_analyticAt (q : O) (hq : q ≠ 0) (u : Oˣ) (n : ℕ) (h : O) (s : ℂ) :
    AnalyticAt ℂ (scaledAffineGaussWeight q u n h) s := by
  unfold scaledAffineGaussWeight
  split_ifs
  · apply AnalyticAt.mul _ analyticAt_const
    apply analyticAt_const.mul
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    apply Eventually.of_forall
    intro z
    exact differentiableAt_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr (ringComplex_ne_zero (mul_ne_zero (by norm_num) hq))))))
  · exact analyticAt_const
  · exact analyticAt_const

abbrev RamifiedSixBranch := Unit ⊕ (Unit ⊕ (Unit ⊕ Fin 3))

def ramifiedSixIndex (u t : Oˣ) (h : O) : RamifiedSixBranch → O
  | .inl _ => scaledAffineGaussIndex (u : O) u 0 h
  | .inr (.inl _) => scaledAffineGaussIndex (-(u : O)) ((-u)⁻¹ ^ 2 * (-u)) 0 h
  | .inr (.inr (.inl _)) => scaledAffineGaussIndex 1 ((-u)⁻¹ ^ 2) 0 h
  | .inr (.inr (.inr j)) => scaledAffineGaussIndex (onceCuspScale t * omega ^ j.val)
      (onceCuspArithmeticUnit (-u) t j) 1 h

def ramifiedSixWeight (u t : Oˣ) (h : O) (i : RamifiedSixBranch) (s : ℂ) : ℂ :=
  let phase := tracePhase (cuspFrequency h * (ringComplex (↑u⁻¹ : O) / 3))
  match i with
  | .inl _ => (4 : ℂ)⁻¹ * scaledAffineGaussWeight (u : O) u 0 h s
  | .inr (.inl _) => (4 : ℂ)⁻¹ * phase * scaledAffineGaussWeight (-(u : O)) ((-u)⁻¹ ^ 2 * (-u)) 0 h s
  | .inr (.inr (.inl _)) => (4 : ℂ)⁻¹ * phase * scaledAffineGaussWeight 1 ((-u)⁻¹ ^ 2) 0 h s
  | .inr (.inr (.inr j)) => (4 : ℂ)⁻¹ * phase *
      scaledAffineGaussWeight (onceCuspScale t * omega ^ j.val) (onceCuspArithmeticUnit (-u) t j) 1 h s

lemma ramifiedSixWeight_analyticAt (u t : Oˣ) (h : O) (i : RamifiedSixBranch) (s : ℂ) :
    AnalyticAt ℂ (ramifiedSixWeight u t h i) s := by
  rcases i with i | i
  · exact analyticAt_const.mul (scaledAffineGaussWeight_analyticAt _ u.ne_zero _ _ _ _)
  rcases i with i | i
  · exact analyticAt_const.mul (scaledAffineGaussWeight_analyticAt _ (neg_ne_zero.mpr u.ne_zero) _ _ _ _)
  rcases i with i | j
  · exact analyticAt_const.mul (scaledAffineGaussWeight_analyticAt _ one_ne_zero _ _ _ _)
  · exact analyticAt_const.mul (scaledAffineGaussWeight_analyticAt _
      (mul_ne_zero (onceCusp_scale_ne_zero t) (pow_ne_zero _ (omega_primitive.isUnit (by decide)).ne_zero)) _ _ _ _)

lemma ramifiedCuspGaussSeries_eq_six (u t : Oˣ) (h : O) (s : ℂ) :
    ramifiedCuspGaussSeries u t h s =
      ∑ i : RamifiedSixBranch, ramifiedSixWeight u t h i s * unramifiedCubicGaussSeries s (ramifiedSixIndex u t h i) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, ramifiedSixWeight, ramifiedSixIndex,
    ramifiedCuspGaussSeries, scaledAffineGaussSeries_factor, Fin.sum_univ_three]
  ring

def ramifiedArithmeticResidue (u t : Oˣ) (h : O) : ℂ :=
  ∑ i : RamifiedSixBranch, ramifiedSixWeight u t h i (4 / 3) * unramifiedGaussResidue (ramifiedSixIndex u t h i)

def cuspTripleDilation : SL(2, ℂ) :=
  complexDiagonal (Real.sqrt 3 : ℂ) (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne')

lemma cuspTripleDilation_action (z : ℂ) (v : ℝ) (hv : 0 < v) :
    cuspTripleDilation • upperPoint z v hv = upperPoint (3 * z) (3 * v) (by positivity) := by
  rw [cuspTripleDilation, complexDiagonal_action]
  have hp : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_cast
    norm_num
  have hn : Complex.normSq (Real.sqrt 3 : ℂ) = 3 := by
    simp [Complex.normSq_apply, Real.sq_sqrt]
  simp only [hp, hn]

def scaledRamifiedCuspMatrix (u : Oˣ) : SL(2, ℂ) :=
  integralComplexMatrix (lowerCuspMatrix (u : O)) * cuspTripleDilation

lemma scaledRamifiedCuspMatrix_action (u : Oˣ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    scaledRamifiedCuspMatrix u • upperPoint z v hv =
      integralComplexMatrix (lowerCuspMatrix (u : O)) • upperPoint (3 * z) (3 * v) (by positivity) := by
  rw [scaledRamifiedCuspMatrix, mul_smul, cuspTripleDilation_action]

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
