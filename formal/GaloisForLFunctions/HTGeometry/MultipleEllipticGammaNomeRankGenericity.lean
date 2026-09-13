import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaPeriodRankDichotomy
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.LinearAlgebra.Span.TensorProduct
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Nome rank and genericity for multiple elliptic gamma functions

This module identifies augmented rational period rank with rank of the generated nome group
modulo torsion. It also proves that, for at least two periods, the differentially algebraic
exceptional locus is Lebesgue null and meagre, while the hypertranscendental locus is full
measure and comeagre inside the upper-half-plane parameter domain.
-/

open Filter Set Topology Function Complex MeasureTheory
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher HTGeometry

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

noncomputable section

/-- Positive rational coefficients, used to enumerate rational affine directions. -/
def MultipleEllipticGammaPositiveRat : Type := {q : ℚ // 0 < q}

instance : Countable MultipleEllipticGammaPositiveRat := Subtype.countable

/-- Real-linear relation between the imaginary parts of the first two periods. -/
def multipleEllipticGammaPairImaginaryRelationMap {n : ℕ} (h : 2 ≤ n)
    (b : MultipleEllipticGammaPositiveRat × MultipleEllipticGammaPositiveRat) :
    (Fin n → ℂ) →ₗ[ℝ] ℝ where
  toFun τ := (b.2.1 : ℝ) * (τ ⟨0, by omega⟩).im -
    (b.1.1 : ℝ) * (τ ⟨1, by omega⟩).im
  map_add' x y := by simp; ring
  map_smul' c x := by simp; ring

/-- The rational-affine exceptional locus in the space of `n` period tuples. -/
def multipleEllipticGammaRationalAffinePeriodLocus (n : ℕ) : Set (Fin n → ℂ) :=
  {τ | MultipleEllipticGammaLiesOnRationalAffineLine τ}

theorem pairImaginaryRelationMap_ker_ne_top {n : ℕ} (h : 2 ≤ n)
    (b : MultipleEllipticGammaPositiveRat × MultipleEllipticGammaPositiveRat) :
    LinearMap.ker (multipleEllipticGammaPairImaginaryRelationMap h b) ≠ ⊤ := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let x : Fin n → ℂ := fun i => if i = i0 then Complex.I else 0
  intro htop
  have hx : x ∈ LinearMap.ker (multipleEllipticGammaPairImaginaryRelationMap h b) := by
    rw [htop]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker] at hx
  have hi : i1 ≠ i0 := by
    intro heq
    have := congrArg Fin.val heq
    simp [i0, i1] at this
  have hbpos : (0 : ℝ) < (b.2.1 : ℝ) := by exact_mod_cast b.2.2
  have hz : (b.2.1 : ℝ) = 0 := by
    simpa [multipleEllipticGammaPairImaginaryRelationMap, x, i0, i1, hi] using hx
  exact hbpos.ne' hz

theorem rationalAffinePeriodLocus_subset_pairRelations {n : ℕ} (h : 2 ≤ n) :
    multipleEllipticGammaRationalAffinePeriodLocus n ⊆
      ⋃ b : MultipleEllipticGammaPositiveRat × MultipleEllipticGammaPositiveRat,
        (LinearMap.ker (multipleEllipticGammaPairImaginaryRelationMap h b) :
          Set (Fin n → ℂ)) := by
  intro τ hτ
  rcases hτ with ⟨ω, hω, a, b, hb, hab⟩
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let q : MultipleEllipticGammaPositiveRat × MultipleEllipticGammaPositiveRat :=
    (⟨b i0, hb i0⟩, ⟨b i1, hb i1⟩)
  apply Set.mem_iUnion.mpr ⟨q, ?_⟩
  change multipleEllipticGammaPairImaginaryRelationMap h q τ = 0
  have h0 := congrArg Complex.im (hab i0)
  have h1 := congrArg Complex.im (hab i1)
  simp [i0, i1] at h0 h1
  simp [multipleEllipticGammaPairImaginaryRelationMap, q, i0, i1, h0, h1]
  ring

theorem multipleEllipticGammaRationalAffinePeriodLocus_measure_zero {n : ℕ}
    (h : 2 ≤ n) :
    volume (multipleEllipticGammaRationalAffinePeriodLocus n) = 0 := by
  apply measure_mono_null (rationalAffinePeriodLocus_subset_pairRelations h)
  apply measure_iUnion_null
  intro b
  exact Measure.addHaar_submodule volume _
    (pairImaginaryRelationMap_ker_ne_top h b)

theorem multipleEllipticGammaRationalAffinePeriodLocus_isMeagre {n : ℕ}
    (h : 2 ≤ n) :
    IsMeagre (multipleEllipticGammaRationalAffinePeriodLocus n) := by
  apply IsMeagre.mono (rationalAffinePeriodLocus_subset_pairRelations h)
  apply isMeagre_iUnion
  intro b
  have hclosed : IsClosed
      (LinearMap.ker (multipleEllipticGammaPairImaginaryRelationMap h b) :
        Set (Fin n → ℂ)) :=
    Submodule.closed_of_finiteDimensional _
  apply IsNowhereDense.isMeagre
  rw [hclosed.isNowhereDense_iff]
  by_contra hinterior
  have hnonempty : (interior
      (LinearMap.ker (multipleEllipticGammaPairImaginaryRelationMap h b) :
        Set (Fin n → ℂ))).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hinterior
  exact pairImaginaryRelationMap_ker_ne_top h b
    (Submodule.eq_top_of_nonempty_interior' _ hnonempty)

/-! ## Nome relations -/

/-- The nome as a unit of the complex numbers. -/
def multipleEllipticGammaNomeUnit (τ : ℂ) : ℂˣ :=
  Units.mk0 (ellipticNome τ) (ellipticNome_ne_zero τ)

/-- Exponent vectors map onto the multiplicative subgroup generated by the nomes. -/
def multipleEllipticGammaNomeExponentHom {ι : Type} [Fintype ι]
    (τ : ι → ℂ) : Multiplicative (ι → ℤ) →* ℂˣ where
  toFun n := ∏ i, multipleEllipticGammaNomeUnit (τ i) ^ n.toAdd i
  map_one' := by
    change (∏ i, multipleEllipticGammaNomeUnit (τ i) ^ (0 : ℤ)) = 1
    simp
  map_mul' n m := by
    change (∏ i, multipleEllipticGammaNomeUnit (τ i) ^ (n.toAdd i + m.toAdd i)) =
      (∏ i, multipleEllipticGammaNomeUnit (τ i) ^ n.toAdd i) *
        ∏ i, multipleEllipticGammaNomeUnit (τ i) ^ m.toAdd i
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact zpow_add (multipleEllipticGammaNomeUnit (τ i)) (n.toAdd i) (m.toAdd i)

/-- The multiplicative subgroup generated by the nomes. -/
def multipleEllipticGammaNomeGroup {ι : Type} [Fintype ι]
    (τ : ι → ℂ) : Subgroup ℂˣ :=
  (multipleEllipticGammaNomeExponentHom τ).range

theorem multipleEllipticGammaNomeExponentHom_coe {ι : Type} [Fintype ι]
    (τ : ι → ℂ) (n : ι → ℤ) :
    ((multipleEllipticGammaNomeExponentHom τ (Multiplicative.ofAdd n) : ℂˣ) : ℂ) =
      Complex.exp ((2 * Real.pi * Complex.I) *
        ∑ i, (n i : ℂ) * τ i) := by
  change (Units.coeHom ℂ) (∏ i, multipleEllipticGammaNomeUnit (τ i) ^ n i) = _
  rw [map_prod, Finset.mul_sum, Complex.exp_sum]
  simp only [map_zpow, multipleEllipticGammaNomeUnit]
  apply Finset.prod_congr rfl
  intro i hi
  change ellipticNome (τ i) ^ n i =
    Complex.exp ((2 * Real.pi * Complex.I) * ((n i : ℂ) * τ i))
  rw [show (2 * (Real.pi : ℂ) * I) * ((n i : ℂ) * τ i) =
      (n i : ℂ) * ((2 * (Real.pi : ℂ) * I) * τ i) by ring,
    Complex.exp_int_mul]
  rfl

/-- A monomial in the nomes is torsion exactly when its additive period combination is rational. -/
theorem multipleEllipticGammaNomeExponent_isOfFinOrder_iff {ι : Type} [Fintype ι]
    (τ : ι → ℂ) (n : ι → ℤ) :
    IsOfFinOrder
      (multipleEllipticGammaNomeExponentHom τ (Multiplicative.ofAdd n)) ↔
      ∃ r : ℚ, ∑ i, (n i : ℂ) * τ i = (r : ℂ) := by
  let S : ℂ := ∑ i, (n i : ℂ) * τ i
  let c : ℂ := 2 * Real.pi * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  constructor
  · intro hfin
    obtain ⟨m, hmpos, hm⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    have hmexp : Complex.exp (c * S) ^ m = 1 := by
      have hcoe := congrArg (fun u : ℂˣ => (u : ℂ)) hm
      simpa [S, c, multipleEllipticGammaNomeExponentHom_coe] using hcoe
    rw [← Complex.exp_nat_mul] at hmexp
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hmexp
    have hms : (m : ℂ) * S = (k : ℂ) := by
      apply mul_left_cancel₀ hc
      calc
        c * ((m : ℂ) * S) = (m : ℂ) * (c * S) := by ring
        _ = (k : ℂ) * c := hk
        _ = c * (k : ℂ) := by ring
    refine ⟨(k : ℚ) / (m : ℚ), ?_⟩
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
    change S = (((k : ℚ) / (m : ℚ) : ℚ) : ℂ)
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    apply (eq_div_iff hm0).2
    simpa [mul_comm] using hms
  · rintro ⟨r, hr⟩
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨r.den, r.den_pos, ?_⟩
    apply Units.ext
    change ((multipleEllipticGammaNomeExponentHom τ
      (Multiplicative.ofAdd n) : ℂˣ) : ℂ) ^ r.den = 1
    rw [multipleEllipticGammaNomeExponentHom_coe, ← Complex.exp_nat_mul]
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨r.num, ?_⟩
    have hrden : (r.den : ℂ) * (r : ℂ) = (r.num : ℂ) := by
      rw [Rat.cast_def]
      field_simp
    rw [hr]
    calc
      (r.den : ℂ) * ((2 * (Real.pi : ℂ) * I) * (r : ℂ)) =
          ((r.den : ℂ) * (r : ℂ)) * (2 * (Real.pi : ℂ) * I) := by ring
      _ = (r.num : ℂ) * (2 * (Real.pi : ℂ) * I) := by rw [hrden]

/-- The augmented rational period space. -/
def multipleEllipticGammaAugmentedPeriodSpace {ι : Type} (τ : ι → ℂ) :
    Submodule ℚ ℂ :=
  Submodule.span ℚ (insert (1 : ℂ) (Set.range τ))

/-- The unit period as a vector in the augmented period space. -/
def multipleEllipticGammaUnitPeriodVector {ι : Type} (τ : ι → ℂ) :
    multipleEllipticGammaAugmentedPeriodSpace τ :=
  ⟨1, Submodule.subset_span (Set.mem_insert 1 (Set.range τ))⟩

/-- The rational unit-period line inside the augmented period space. -/
def multipleEllipticGammaUnitPeriodLine {ι : Type} (τ : ι → ℂ) :
    Submodule ℚ (multipleEllipticGammaAugmentedPeriodSpace τ) :=
  ℚ ∙ multipleEllipticGammaUnitPeriodVector τ

/-- Torsion-free nome rank: rational dimension remaining after the unit-period line is removed. -/
def multipleEllipticGammaNomeTorsionFreeRank {ι : Type} [Fintype ι]
    (τ : ι → ℂ) : ℕ :=
  Module.finrank ℚ
    (multipleEllipticGammaAugmentedPeriodSpace τ ⧸
      multipleEllipticGammaUnitPeriodLine τ)

theorem multipleEllipticGammaUnitPeriodVector_ne_zero {ι : Type} (τ : ι → ℂ) :
    multipleEllipticGammaUnitPeriodVector τ ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  exact one_ne_zero this

/-- Exact equality between augmented additive rank and torsion-free nome rank. -/
theorem multipleEllipticGamma_nomeTorsionFreeRank_add_one {ι : Type} [Fintype ι]
    (τ : ι → ℂ) :
    multipleEllipticGammaNomeTorsionFreeRank τ + 1 =
      multipleEllipticGammaAugmentedPeriodRank τ := by
  let A := multipleEllipticGammaAugmentedPeriodSpace τ
  haveI : Module.Finite ℚ A :=
    Module.Finite.span_of_finite ℚ ((Set.finite_range τ).insert 1)
  have hline : Module.finrank ℚ (multipleEllipticGammaUnitPeriodLine τ) = 1 := by
    exact finrank_span_singleton (multipleEllipticGammaUnitPeriodVector_ne_zero τ)
  have hquot :=
    (multipleEllipticGammaUnitPeriodLine τ).finrank_quotient_add_finrank
  rw [hline] at hquot
  exact hquot

theorem multipleEllipticGamma_nomeTorsionFreeRank_eq_augmentedPeriodRank_sub_one
    {ι : Type} [Fintype ι] (τ : ι → ℂ) :
    multipleEllipticGammaNomeTorsionFreeRank τ =
      multipleEllipticGammaAugmentedPeriodRank τ - 1 := by
  have h := multipleEllipticGamma_nomeTorsionFreeRank_add_one τ
  omega

/-- Rational exponent relations modulo the unit period. -/
def multipleEllipticGammaNomeRationalRelationMap {ι : Type} [Fintype ι]
    (τ : ι → ℂ) :
    (ι → ℚ) →ₗ[ℚ] ℂ ⧸ (ℚ ∙ (1 : ℂ)) :=
  (ℚ ∙ (1 : ℂ)).mkQ.comp (Fintype.linearCombination ℚ τ)

def multipleEllipticGammaNomeRationalRelationSpace {ι : Type} [Fintype ι]
    (τ : ι → ℂ) : Submodule ℚ (ι → ℚ) :=
  LinearMap.ker (multipleEllipticGammaNomeRationalRelationMap τ)

theorem mem_multipleEllipticGammaNomeRationalRelationSpace_iff
    {ι : Type} [Fintype ι] (τ : ι → ℂ) (r : ι → ℚ) :
    r ∈ multipleEllipticGammaNomeRationalRelationSpace τ ↔
      ∃ q : ℚ, ∑ i, (r i : ℂ) * τ i = (q : ℂ) := by
  rw [multipleEllipticGammaNomeRationalRelationSpace, LinearMap.mem_ker,
    multipleEllipticGammaNomeRationalRelationMap, LinearMap.comp_apply,
    Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton,
    Fintype.linearCombination_apply]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    simpa [Algebra.smul_def, mul_comm] using hq.symm
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    simpa [Algebra.smul_def, mul_comm] using hq.symm

theorem differentialAlgebraicOver_multipleEllipticGammaMero_iff_nomeRank_eq_one
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    DifferentialAlgebraicOver (RatFunc ℂ) (multipleEllipticGammaMero τ hτ) ↔
      multipleEllipticGammaNomeTorsionFreeRank τ = 1 := by
  rw [differentialAlgebraicOver_multipleEllipticGammaMero_iff_augmentedPeriodRank_eq_two]
  have h := multipleEllipticGamma_nomeTorsionFreeRank_add_one τ
  omega

theorem differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_nomeRank_eq_one
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero τ hτ) ↔
      multipleEllipticGammaNomeTorsionFreeRank τ = 1 := by
  rw [differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_augmentedPeriodRank_eq_two]
  have h := multipleEllipticGamma_nomeTorsionFreeRank_add_one τ
  omega

theorem hypertranscendentalOver_multipleEllipticGammaMero_iff_two_le_nomeRank
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    HypertranscendentalOver (RatFunc ℂ) (multipleEllipticGammaMero τ hτ) ↔
      2 ≤ multipleEllipticGammaNomeTorsionFreeRank τ := by
  rw [hypertranscendentalOver_multipleEllipticGammaMero_iff_three_le_augmentedPeriodRank]
  have h := multipleEllipticGamma_nomeTorsionFreeRank_add_one τ
  omega

theorem hypertranscendentalOver_multipleEllipticGammaLogDerivMero_iff_two_le_nomeRank
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    HypertranscendentalOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero τ hτ) ↔
      2 ≤ multipleEllipticGammaNomeTorsionFreeRank τ := by
  rw [hypertranscendentalOver_multipleEllipticGammaLogDerivMero_iff_three_le_augmentedPeriodRank]
  have h := multipleEllipticGamma_nomeTorsionFreeRank_add_one τ
  omega

/-! ## Exact exceptional and generic loci -/

def multipleEllipticGammaUpperHalfPeriodLocus (n : ℕ) : Set (Fin n → ℂ) :=
  {τ | ∀ i, 0 < (τ i).im}

def multipleEllipticGammaDifferentialAlgebraicPeriodLocus (n : ℕ) :
    Set (Fin n → ℂ) :=
  {τ | ∃ hτ : ∀ i, 0 < (τ i).im,
    DifferentialAlgebraicOver (RatFunc ℂ) (multipleEllipticGammaMero τ hτ)}

def multipleEllipticGammaHypertranscendentalPeriodLocus (n : ℕ) :
    Set (Fin n → ℂ) :=
  {τ | ∃ hτ : ∀ i, 0 < (τ i).im,
    HypertranscendentalOver (RatFunc ℂ) (multipleEllipticGammaMero τ hτ)}

theorem multipleEllipticGammaDifferentialAlgebraicPeriodLocus_eq
    {n : ℕ} (h : 1 ≤ n) :
    multipleEllipticGammaDifferentialAlgebraicPeriodLocus n =
      multipleEllipticGammaRationalAffinePeriodLocus n ∩
        multipleEllipticGammaUpperHalfPeriodLocus n := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp h
  ext τ
  constructor
  · rintro ⟨hτ, hda⟩
    have hminor :
        ¬ MultipleEllipticGammaHasRankThreeMinor τ :=
      (differentialAlgebraicOver_multipleEllipticGammaMero_iff_not_rankThreeMinor
        τ hτ).mp hda
    exact ⟨
      (liesOnRationalAffineLine_iff_not_rankThreeMinor τ hτ).mpr hminor,
      hτ⟩
  · rintro ⟨hline, hτ⟩
    refine ⟨hτ, ?_⟩
    apply (differentialAlgebraicOver_multipleEllipticGammaMero_iff_not_rankThreeMinor
      τ hτ).mpr
    exact (liesOnRationalAffineLine_iff_not_rankThreeMinor τ hτ).mp hline

theorem multipleEllipticGammaDifferentialAlgebraicPeriodLocus_measure_zero
    {n : ℕ} (h : 2 ≤ n) :
    volume (multipleEllipticGammaDifferentialAlgebraicPeriodLocus n) = 0 := by
  rw [multipleEllipticGammaDifferentialAlgebraicPeriodLocus_eq (by omega)]
  exact measure_mono_null inter_subset_left
    (multipleEllipticGammaRationalAffinePeriodLocus_measure_zero h)

theorem multipleEllipticGammaDifferentialAlgebraicPeriodLocus_isMeagre
    {n : ℕ} (h : 2 ≤ n) :
    IsMeagre (multipleEllipticGammaDifferentialAlgebraicPeriodLocus n) := by
  rw [multipleEllipticGammaDifferentialAlgebraicPeriodLocus_eq (by omega)]
  exact (multipleEllipticGammaRationalAffinePeriodLocus_isMeagre h).inter

theorem multipleEllipticGammaHypertranscendentalPeriodLocus_eq
    {n : ℕ} (_h : 1 ≤ n) :
    multipleEllipticGammaHypertranscendentalPeriodLocus n =
      multipleEllipticGammaUpperHalfPeriodLocus n \
        multipleEllipticGammaDifferentialAlgebraicPeriodLocus n := by
  ext τ
  constructor
  · rintro ⟨hτ, hht⟩
    refine ⟨hτ, ?_⟩
    rintro ⟨hτ', hda⟩
    have hda' : DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaMero τ hτ) := by
      simpa using hda
    exact hht hda'
  · rintro ⟨hτ, hnot⟩
    refine ⟨hτ, ?_⟩
    intro hda
    exact hnot ⟨hτ, hda⟩

theorem multipleEllipticGammaHypertranscendentalPeriodLocus_ae_upperHalf
    {n : ℕ} (h : 2 ≤ n) :
    multipleEllipticGammaHypertranscendentalPeriodLocus n =ᵐ[volume]
      multipleEllipticGammaUpperHalfPeriodLocus n := by
  rw [multipleEllipticGammaHypertranscendentalPeriodLocus_eq (by omega)]
  apply ae_eq_set.mpr
  constructor
  · simp
  · apply measure_mono_null
      (show multipleEllipticGammaUpperHalfPeriodLocus n \
          (multipleEllipticGammaUpperHalfPeriodLocus n \
            multipleEllipticGammaDifferentialAlgebraicPeriodLocus n) ⊆
          multipleEllipticGammaDifferentialAlgebraicPeriodLocus n by aesop)
    exact multipleEllipticGammaDifferentialAlgebraicPeriodLocus_measure_zero h

theorem multipleEllipticGammaUpperHalfPeriodLocus_isOpen (n : ℕ) :
    IsOpen (multipleEllipticGammaUpperHalfPeriodLocus n) := by
  rw [show multipleEllipticGammaUpperHalfPeriodLocus n =
      Set.pi Set.univ (fun _ : Fin n => {z : ℂ | 0 < z.im}) by
    ext τ
    simp [multipleEllipticGammaUpperHalfPeriodLocus]]
  exact isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_lt continuous_const Complex.continuous_im

abbrev MultipleEllipticGammaUpperHalfPeriodTuple (n : ℕ) : Type :=
  multipleEllipticGammaUpperHalfPeriodLocus n

def multipleEllipticGammaDifferentialAlgebraicLocusWithinUpperHalf (n : ℕ) :
    Set (MultipleEllipticGammaUpperHalfPeriodTuple n) :=
  Subtype.val ⁻¹' multipleEllipticGammaDifferentialAlgebraicPeriodLocus n

theorem multipleEllipticGammaDifferentialAlgebraicLocusWithinUpperHalf_isMeagre
    {n : ℕ} (h : 2 ≤ n) :
    IsMeagre (multipleEllipticGammaDifferentialAlgebraicLocusWithinUpperHalf n) := by
  exact
    (multipleEllipticGammaDifferentialAlgebraicPeriodLocus_isMeagre h).preimage_of_isOpenMap
      continuous_subtype_val
      (multipleEllipticGammaUpperHalfPeriodLocus_isOpen n).isOpenEmbedding_subtypeVal.isOpenMap

theorem multipleEllipticGammaHypertranscendentalLocusWithinUpperHalf_comeagre
    {n : ℕ} (h : 2 ≤ n) :
    (multipleEllipticGammaDifferentialAlgebraicLocusWithinUpperHalf n)ᶜ ∈
      residual (MultipleEllipticGammaUpperHalfPeriodTuple n) :=
  multipleEllipticGammaDifferentialAlgebraicLocusWithinUpperHalf_isMeagre h

def multipleEllipticGammaPeriodVector {ι : Type} [Fintype ι]
    (τ : ι → ℂ) (i : ι) : multipleEllipticGammaAugmentedPeriodSpace τ :=
  ⟨τ i, Submodule.subset_span (Set.mem_insert_of_mem 1 (Set.mem_range_self i))⟩

def multipleEllipticGammaNomePeriodQuotientMap {ι : Type} [Fintype ι]
    (τ : ι → ℂ) :
    (ι → ℚ) →ₗ[ℚ]
      multipleEllipticGammaAugmentedPeriodSpace τ ⧸
        multipleEllipticGammaUnitPeriodLine τ :=
  (multipleEllipticGammaUnitPeriodLine τ).mkQ.comp
    (Fintype.linearCombination ℚ (multipleEllipticGammaPeriodVector τ))

theorem multipleEllipticGammaNomePeriodQuotientMap_surjective
    {ι : Type} [Fintype ι] (τ : ι → ℂ) :
    Function.Surjective (multipleEllipticGammaNomePeriodQuotientMap τ) := by
  rw [← LinearMap.range_eq_top, multipleEllipticGammaNomePeriodQuotientMap,
    LinearMap.range_comp, Fintype.range_linearCombination,
    Submodule.map_mkQ_eq_top]
  apply top_unique
  rintro ⟨z, hz⟩ _
  let S : Submodule ℚ (multipleEllipticGammaAugmentedPeriodSpace τ) :=
    multipleEllipticGammaUnitPeriodLine τ ⊔
      Submodule.span ℚ (Set.range (multipleEllipticGammaPeriodVector τ))
  change (⟨z, hz⟩ : multipleEllipticGammaAugmentedPeriodSpace τ) ∈ S
  suffices ∃ hz' : z ∈ multipleEllipticGammaAugmentedPeriodSpace τ,
      (⟨z, hz'⟩ : multipleEllipticGammaAugmentedPeriodSpace τ) ∈ S by
    rcases this with ⟨hz', hzS⟩
    exact hzS
  refine Submodule.span_induction
    (p := fun x _ => ∃ hx : x ∈ multipleEllipticGammaAugmentedPeriodSpace τ,
      (⟨x, hx⟩ : multipleEllipticGammaAugmentedPeriodSpace τ) ∈ S)
    ?_ ?_ ?_ ?_ hz
  · intro x hx
    rcases hx with rfl | hx
    · refine ⟨Submodule.subset_span (Set.mem_insert 1 (Set.range τ)), ?_⟩
      apply Submodule.mem_sup_left
      exact Submodule.mem_span_singleton_self _
    · rcases hx with ⟨i, rfl⟩
      refine ⟨Submodule.subset_span
        (Set.mem_insert_of_mem (1 : ℂ) (Set.mem_range_self i)), ?_⟩
      apply Submodule.mem_sup_right
      exact Submodule.subset_span (Set.mem_range_self i)
  · exact ⟨Submodule.zero_mem _, Submodule.zero_mem S⟩
  · rintro x y hx hy ⟨hxA, hxS⟩ ⟨hyA, hyS⟩
    refine ⟨Submodule.add_mem _ hxA hyA, ?_⟩
    exact Submodule.add_mem S hxS hyS
  · rintro q x hx ⟨hxA, hxS⟩
    refine ⟨Submodule.smul_mem _ q hxA, ?_⟩
    exact Submodule.smul_mem S q hxS

theorem mem_ker_multipleEllipticGammaNomePeriodQuotientMap_iff
    {ι : Type} [Fintype ι] (τ : ι → ℂ) (r : ι → ℚ) :
    r ∈ LinearMap.ker (multipleEllipticGammaNomePeriodQuotientMap τ) ↔
      ∃ q : ℚ, ∑ i, (r i : ℂ) * τ i = (q : ℂ) := by
  rw [LinearMap.mem_ker, multipleEllipticGammaNomePeriodQuotientMap,
    LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    multipleEllipticGammaUnitPeriodLine, Submodule.mem_span_singleton,
    Fintype.linearCombination_apply]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    have hval := congrArg Subtype.val hq
    simpa [multipleEllipticGammaPeriodVector, multipleEllipticGammaUnitPeriodVector,
      Algebra.smul_def, mul_comm] using hval.symm
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    simpa [multipleEllipticGammaPeriodVector, multipleEllipticGammaUnitPeriodVector,
      Algebra.smul_def, mul_comm] using hq.symm

theorem ker_multipleEllipticGammaNomePeriodQuotientMap
    {ι : Type} [Fintype ι] (τ : ι → ℂ) :
    LinearMap.ker (multipleEllipticGammaNomePeriodQuotientMap τ) =
      multipleEllipticGammaNomeRationalRelationSpace τ := by
  ext r
  rw [mem_ker_multipleEllipticGammaNomePeriodQuotientMap_iff,
    mem_multipleEllipticGammaNomeRationalRelationSpace_iff]

theorem multipleEllipticGamma_nomeRank_add_relationRank
    {ι : Type} [Fintype ι] (τ : ι → ℂ) :
    multipleEllipticGammaNomeTorsionFreeRank τ +
        Module.finrank ℚ (multipleEllipticGammaNomeRationalRelationSpace τ) =
      Fintype.card ι := by
  have h := (multipleEllipticGammaNomePeriodQuotientMap τ).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
      (multipleEllipticGammaNomePeriodQuotientMap_surjective τ),
    finrank_top, ker_multipleEllipticGammaNomePeriodQuotientMap,
    Module.finrank_fintype_fun_eq_card] at h
  exact h

def multipleEllipticGammaNomeTorsionFreeQuotientHom
    {ι : Type} [Fintype ι] (τ : ι → ℂ) :
    Multiplicative (ι → ℤ) →*
      multipleEllipticGammaNomeGroup τ ⧸
        CommGroup.torsion (multipleEllipticGammaNomeGroup τ) :=
  (QuotientGroup.mk' (CommGroup.torsion (multipleEllipticGammaNomeGroup τ))).comp
    (multipleEllipticGammaNomeExponentHom τ).rangeRestrict

theorem multipleEllipticGammaNomeTorsionFreeQuotientHom_surjective
    {ι : Type} [Fintype ι] (τ : ι → ℂ) :
    Function.Surjective (multipleEllipticGammaNomeTorsionFreeQuotientHom τ) :=
  (QuotientGroup.mk'_surjective _).comp
    (multipleEllipticGammaNomeExponentHom τ).rangeRestrict_surjective

def multipleEllipticGammaNomeIntegralRelationMap
    {ι : Type} [Fintype ι] (τ : ι → ℂ) :
    (ι → ℤ) →ₗ[ℤ]
      Additive (multipleEllipticGammaNomeGroup τ ⧸
        CommGroup.torsion (multipleEllipticGammaNomeGroup τ)) :=
  (multipleEllipticGammaNomeTorsionFreeQuotientHom τ).toAdditive.toIntLinearMap

def multipleEllipticGammaNomeIntegralRelationSpace
    {ι : Type} [Fintype ι] (τ : ι → ℂ) : Submodule ℤ (ι → ℤ) :=
  LinearMap.ker (multipleEllipticGammaNomeIntegralRelationMap τ)

theorem mem_multipleEllipticGammaNomeIntegralRelationSpace_iff
    {ι : Type} [Fintype ι] (τ : ι → ℂ) (n : ι → ℤ) :
    n ∈ multipleEllipticGammaNomeIntegralRelationSpace τ ↔
      ∃ r : ℚ, ∑ i, (n i : ℂ) * τ i = (r : ℂ) := by
  rw [multipleEllipticGammaNomeIntegralRelationSpace, LinearMap.mem_ker]
  change (QuotientGroup.mk'
      (CommGroup.torsion ((multipleEllipticGammaNomeExponentHom τ).range)))
      ((multipleEllipticGammaNomeExponentHom τ).rangeRestrict
        (Multiplicative.ofAdd n)) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [CommGroup.mem_torsion]
  change IsOfFinOrder
      ((multipleEllipticGammaNomeExponentHom τ).rangeRestrict
        (Multiplicative.ofAdd n)) ↔ _
  rw [← Submonoid.isOfFinOrder_coe]
  exact multipleEllipticGammaNomeExponent_isOfFinOrder_iff τ n

def multipleEllipticGammaIntegerExponentCastMap {ι : Type} [Fintype ι] :
    (ι → ℤ) →ₗ[ℤ] (ι → ℚ) where
  toFun n i := (n i : ℚ)
  map_add' n m := by ext i; simp
  map_smul' z n := by ext i; simp

theorem multipleEllipticGammaIntegerExponentCastMap_injective
    {ι : Type} [Fintype ι] :
    Function.Injective (multipleEllipticGammaIntegerExponentCastMap (ι := ι)) := by
  intro n m h
  ext i
  have hi := congrFun h i
  change (n i : ℚ) = (m i : ℚ) at hi
  exact_mod_cast hi

def multipleEllipticGammaNomeIntegralRelationLattice
    {ι : Type} [Fintype ι] (τ : ι → ℂ) : Submodule ℤ (ι → ℚ) :=
  Submodule.map (multipleEllipticGammaIntegerExponentCastMap (ι := ι))
    (multipleEllipticGammaNomeIntegralRelationSpace τ)

theorem multipleEllipticGammaIntegerCast_mem_rationalRelationSpace_iff
    {ι : Type} [Fintype ι] (τ : ι → ℂ) (n : ι → ℤ) :
    multipleEllipticGammaIntegerExponentCastMap n ∈
        multipleEllipticGammaNomeRationalRelationSpace τ ↔
      n ∈ multipleEllipticGammaNomeIntegralRelationSpace τ := by
  rw [mem_multipleEllipticGammaNomeRationalRelationSpace_iff,
    mem_multipleEllipticGammaNomeIntegralRelationSpace_iff]
  simp only [multipleEllipticGammaIntegerExponentCastMap]
  norm_cast

theorem span_multipleEllipticGammaNomeIntegralRelationLattice
    {ι : Type} [Fintype ι] (τ : ι → ℂ) :
    Submodule.span ℚ
        (multipleEllipticGammaNomeIntegralRelationLattice τ : Set (ι → ℚ)) =
      multipleEllipticGammaNomeRationalRelationSpace τ := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    rcases hx with ⟨n, hn, rfl⟩
    exact (multipleEllipticGammaIntegerCast_mem_rationalRelationSpace_iff τ n).mpr hn
  · intro r hr
    let D := IsLocalization.commonDenom (nonZeroDivisors ℤ) Finset.univ r
    let n : ι → ℤ := fun i =>
      IsLocalization.integerMultiple (nonZeroDivisors ℤ) Finset.univ r
        ⟨i, Finset.mem_univ i⟩
    have hDn (i : ι) : (n i : ℚ) = ((D : ℤ) : ℚ) * r i := by
      have h := IsLocalization.map_integerMultiple
        (nonZeroDivisors ℤ) Finset.univ r ⟨i, Finset.mem_univ i⟩
      change (n i : ℚ) = (D : ℤ) • r i at h
      rw [zsmul_eq_mul] at h
      exact h
    have hD0z : (D : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero D
    have hD0q : ((D : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hD0z
    have hn : n ∈ multipleEllipticGammaNomeIntegralRelationSpace τ := by
      rw [mem_multipleEllipticGammaNomeIntegralRelationSpace_iff]
      rcases (mem_multipleEllipticGammaNomeRationalRelationSpace_iff τ r).mp hr with ⟨q, hq⟩
      refine ⟨((D : ℤ) : ℚ) * q, ?_⟩
      simp_rw [show ∀ i, (n i : ℂ) = ((D : ℤ) : ℂ) * (r i : ℂ) by
        intro i
        exact_mod_cast hDn i]
      calc
        ∑ x, (((D : ℤ) : ℂ) * (r x : ℂ)) * τ x =
            ((D : ℤ) : ℂ) * ∑ x, (r x : ℂ) * τ x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (((D : ℤ) : ℚ) * q : ℚ) := by rw [hq]; norm_num
    have hcast : multipleEllipticGammaIntegerExponentCastMap n ∈
        multipleEllipticGammaNomeIntegralRelationLattice τ :=
      Submodule.mem_map_of_mem hn
    have hrscale : (((D : ℤ) : ℚ)⁻¹) •
        multipleEllipticGammaIntegerExponentCastMap n = r := by
      funext i
      change ((D : ℤ) : ℚ)⁻¹ * (n i : ℚ) = r i
      rw [hDn i]
      calc
        ((D : ℤ) : ℚ)⁻¹ * (((D : ℤ) : ℚ) * r i) =
            (((D : ℤ) : ℚ)⁻¹ * ((D : ℤ) : ℚ)) * r i := by ring
        _ = r i := by rw [inv_mul_cancel₀ hD0q, one_mul]
    rw [← hrscale]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hcast)

theorem multipleEllipticGamma_integralRelationLattice_finrank
    {ι : Type} [Fintype ι] (τ : ι → ℂ) :
    Module.finrank ℤ (multipleEllipticGammaNomeIntegralRelationLattice τ) =
      Module.finrank ℤ (multipleEllipticGammaNomeIntegralRelationSpace τ) := by
  rw [multipleEllipticGammaNomeIntegralRelationLattice,
    ← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj
    ((multipleEllipticGammaIntegerExponentCastMap_injective (ι := ι)).comp
      Subtype.val_injective)

theorem multipleEllipticGamma_integralRelationRank_eq_rationalRelationRank
    {ι : Type} [Fintype ι] (τ : ι → ℂ) :
    Module.finrank ℤ (multipleEllipticGammaNomeIntegralRelationSpace τ) =
      Module.finrank ℚ (multipleEllipticGammaNomeRationalRelationSpace τ) := by
  letI : Module.Finite ℤ
      (multipleEllipticGammaNomeIntegralRelationLattice τ) := by
    rw [multipleEllipticGammaNomeIntegralRelationLattice,
      ← LinearMap.range_domRestrict]
    infer_instance
  letI : Module.Finite ℤ
      (Submodule.span ℤ
        (multipleEllipticGammaNomeIntegralRelationLattice τ : Set (ι → ℚ))) := by
    rw [Submodule.span_eq]
    infer_instance
  have hspan := Submodule.finrank_span_eq_finrank_span ℤ ℚ
    (multipleEllipticGammaNomeIntegralRelationLattice τ : Set (ι → ℚ))
  calc
    Module.finrank ℤ (multipleEllipticGammaNomeIntegralRelationSpace τ) =
        Module.finrank ℤ (multipleEllipticGammaNomeIntegralRelationLattice τ) :=
      (multipleEllipticGamma_integralRelationLattice_finrank τ).symm
    _ = Module.finrank ℤ
        (Submodule.span ℤ
          (multipleEllipticGammaNomeIntegralRelationLattice τ : Set (ι → ℚ))) := by
      rw [Submodule.span_eq]
    _ = Module.finrank ℚ
        (Submodule.span ℚ
          (multipleEllipticGammaNomeIntegralRelationLattice τ : Set (ι → ℚ))) :=
      hspan.symm
    _ = Module.finrank ℚ (multipleEllipticGammaNomeRationalRelationSpace τ) := by
      rw [span_multipleEllipticGammaNomeIntegralRelationLattice]

theorem multipleEllipticGamma_nomeGroupModTorsion_finrank_eq_nomeRank
    {ι : Type} [Fintype ι] (τ : ι → ℂ) :
    Module.finrank ℤ
        (Additive (multipleEllipticGammaNomeGroup τ ⧸
          CommGroup.torsion (multipleEllipticGammaNomeGroup τ))) =
      multipleEllipticGammaNomeTorsionFreeRank τ := by
  have hsurj : Function.Surjective
      (multipleEllipticGammaNomeIntegralRelationMap τ) :=
    multipleEllipticGammaNomeTorsionFreeQuotientHom_surjective τ
  have hInt :=
    (LinearMap.ker (multipleEllipticGammaNomeIntegralRelationMap τ)).finrank_quotient_add_finrank
  have hequiv :=
    (LinearMap.quotKerEquivOfSurjective
      (multipleEllipticGammaNomeIntegralRelationMap τ) hsurj).finrank_eq
  rw [hequiv, Module.finrank_fintype_fun_eq_card] at hInt
  have hRat := multipleEllipticGamma_nomeRank_add_relationRank τ
  have hRelations :=
    multipleEllipticGamma_integralRelationRank_eq_rationalRelationRank τ
  change Module.finrank ℤ
      (Additive (multipleEllipticGammaNomeGroup τ ⧸
        CommGroup.torsion (multipleEllipticGammaNomeGroup τ))) +
      Module.finrank ℤ (multipleEllipticGammaNomeIntegralRelationSpace τ) =
        Fintype.card ι at hInt
  omega

theorem multipleEllipticGamma_nomeGroupModTorsion_finrank_add_one
    {ι : Type} [Fintype ι] (τ : ι → ℂ) :
    Module.finrank ℤ
        (Additive (multipleEllipticGammaNomeGroup τ ⧸
          CommGroup.torsion (multipleEllipticGammaNomeGroup τ))) + 1 =
      multipleEllipticGammaAugmentedPeriodRank τ := by
  rw [multipleEllipticGamma_nomeGroupModTorsion_finrank_eq_nomeRank,
    multipleEllipticGamma_nomeTorsionFreeRank_add_one]


end

end GaloisForLFunctions
