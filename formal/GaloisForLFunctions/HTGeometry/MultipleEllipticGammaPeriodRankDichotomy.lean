import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCommonStepNilpotence
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFacewiseRankThreeMinor

/-!
# Exact period-rank dichotomy for multiple elliptic Gamma functions

Every finite nonempty upper-half-plane period family has one of two exhaustive phases.  If no two
periods form a rationally independent triple with the unit period, all periods lie on one rational
affine line and admit a common positive translation step modulo integers; common-step nilpotence
makes the multiple elliptic Gamma differentially algebraic.  A rank-three minor gives the
complementary hypertranscendental phase.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The unit period and one upper-half-plane period are rationally independent. -/
theorem linearIndependent_rat_one_of_im_pos {ω : ℂ} (hω : 0 < ω.im) :
    LinearIndependent ℚ ![(1 : ℂ), ω] := by
  have hR := linearIndependent_one_of_im_pos hω
  have hcast : Function.Injective (fun q : ℚ => q • (1 : ℝ)) := by
    intro a b hab
    exact Rat.cast_injective (α := ℝ)
      (by simpa only [Rat.smul_one_eq_cast] using hab)
  exact hR.restrict_scalars hcast

omit [Fintype ι] [DecidableEq ι] in
/-- An upper-half-plane period family lies on one rational affine line when all periods are
rational affine combinations of one upper-half-plane direction, with positive directional
coefficient. -/
def MultipleEllipticGammaLiesOnRationalAffineLine
    (τ : ι → ℂ) : Prop :=
  ∃ ω : ℂ, 0 < ω.im ∧
    ∃ a b : ι → ℚ, (∀ i, 0 < b i) ∧
      ∀ i, τ i = (a i : ℂ) + (b i : ℂ) * ω

omit [Fintype ι] [DecidableEq ι] in
/-- Kato's rational-ray condition for a period family. -/
def MultipleEllipticGammaLiesOnRationalRay
    (τ : ι → ℂ) : Prop :=
  ∃ ω : ℂ, 0 < ω.im ∧
    ∃ c : ι → ℚ, ∀ i, τ i = (c i : ℂ) * ω

omit [Fintype ι] [DecidableEq ι] in
/-- Absence of a rank-three minor puts every period on one rational affine line through a chosen
upper-half-plane period. -/
theorem exists_rationalAffineLine_of_not_rankThreeMinor
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hminor : ¬ MultipleEllipticGammaHasRankThreeMinor τ) :
    ∃ ω : ℂ, 0 < ω.im ∧
      ∃ a b : ι → ℚ, (∀ i, 0 < b i) ∧
        ∀ i, τ i = (a i : ℂ) + (b i : ℂ) * ω := by
  let i0 : ι := Classical.choice ‹Nonempty ι›
  let ω := τ i0
  have hω : 0 < ω.im := hτ i0
  have hpair : LinearIndependent ℚ ![(1 : ℂ), ω] :=
    linearIndependent_rat_one_of_im_pos hω
  have hrepr : ∀ i : ι, ∃ a b : ℚ, 0 < b ∧
      τ i = (a : ℂ) + (b : ℂ) * ω := by
    intro i
    by_cases hi : i = i0
    · subst i
      exact ⟨0, 1, by norm_num, by simp [ω]⟩
    · have hnot : ¬ LinearIndependent ℚ ![(1 : ℂ), ω, τ i] := by
        intro hlin
        exact hminor ⟨i0, i, Ne.symm hi, hlin⟩
      have hv :
          ![(1 : ℂ), ω, τ i] = Fin.snoc ![(1 : ℂ), ω] (τ i) := by
        funext j
        fin_cases j <;> rfl
      have hmem : τ i ∈ Submodule.span ℚ (Set.range ![(1 : ℂ), ω]) := by
        by_contra hnotmem
        apply hnot
        rw [hv, linearIndependent_finSnoc]
        exact ⟨hpair, hnotmem⟩
      obtain ⟨c, hc⟩ :=
        (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
      have heq :
          (c 0 : ℂ) + (c 1 : ℂ) * ω = τ i := by
        simpa [Fin.sum_univ_two, Algebra.smul_def] using hc
      have him := congrArg Complex.im heq
      norm_num [mul_im] at him
      have hb : 0 < c 1 := by
        have hbReal : 0 < (c 1 : ℝ) := by
          nlinarith [hτ i, hω]
        exact_mod_cast hbReal
      exact ⟨c 0, c 1, hb, heq.symm⟩
  choose a b hb hab using hrepr
  exact ⟨ω, hω, a, b, hb, hab⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **Arbitrary-family compactness law.** For any nonempty index type, finite or infinite, absence
of a two-period rank-three witness is equivalent to containment of the entire period family in one
rational affine line. -/
theorem liesOnRationalAffineLine_iff_not_rankThreeMinor
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    MultipleEllipticGammaLiesOnRationalAffineLine τ ↔
      ¬ MultipleEllipticGammaHasRankThreeMinor τ := by
  constructor
  · rintro ⟨ω, hω, a, b, hb, hab⟩ ⟨q, r, hqr, hlin⟩
    let w : Fin 2 → ℂ := ![(1 : ℂ), ω]
    have hone : (1 : ℂ) ∈ Submodule.span ℚ (Set.range w) :=
      Submodule.subset_span ⟨0, by simp [w]⟩
    have hωmem : ω ∈ Submodule.span ℚ (Set.range w) :=
      Submodule.subset_span ⟨1, by simp [w]⟩
    have hq : τ q ∈ Submodule.span ℚ (Set.range w) := by
      rw [hab q]
      simpa [Algebra.smul_def] using
        (Submodule.add_mem _
          (Submodule.smul_mem _ (a q) hone)
          (Submodule.smul_mem _ (b q) hωmem))
    have hr : τ r ∈ Submodule.span ℚ (Set.range w) := by
      rw [hab r]
      simpa [Algebra.smul_def] using
        (Submodule.add_mem _
          (Submodule.smul_mem _ (a r) hone)
          (Submodule.smul_mem _ (b r) hωmem))
    have hsub :
        Submodule.span ℚ
            (Set.range (ellipticGammaSourcePeriods (τ q) (τ r))) ≤
          Submodule.span ℚ (Set.range w) := by
      apply Submodule.span_le.mpr
      rintro x ⟨j, rfl⟩
      fin_cases j
      · simpa [ellipticGammaSourcePeriods] using hone
      · simpa [ellipticGammaSourcePeriods] using hq
      · simpa [ellipticGammaSourcePeriods] using hr
    haveI : Module.Finite ℚ (Submodule.span ℚ (Set.range w)) :=
      Module.Finite.span_of_finite ℚ (Set.finite_range w)
    have hle := Submodule.finrank_mono hsub
    have hsource :
        Module.finrank ℚ
            (Submodule.span ℚ
              (Set.range (ellipticGammaSourcePeriods (τ q) (τ r)))) = 3 := by
      simpa using finrank_span_eq_card hlin
    have hw : Module.finrank ℚ (Submodule.span ℚ (Set.range w)) = 2 := by
      simpa [w] using
        finrank_span_eq_card (linearIndependent_rat_one_of_im_pos hω)
    omega
  · intro hminor
    exact exists_rationalAffineLine_of_not_rankThreeMinor τ hτ hminor

omit [Fintype ι] [DecidableEq ι] in
/-- A rational ray is a special rational affine line; positive imaginary parts force all rational
ray coefficients to be positive. -/
theorem liesOnRationalAffineLine_of_liesOnRationalRay
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hray : MultipleEllipticGammaLiesOnRationalRay τ) :
    MultipleEllipticGammaLiesOnRationalAffineLine τ := by
  obtain ⟨ω, hω, c, hc⟩ := hray
  refine ⟨ω, hω, 0, c, ?_, ?_⟩
  · intro i
    have hi := congrArg Complex.im (hc i)
    norm_num [mul_im] at hi
    have hcReal : 0 < (c i : ℝ) := by
      nlinarith [hτ i, hω]
    exact_mod_cast hcReal
  · intro i
    simpa using hc i

/-- A finite positive rational affine period family admits one common positive step modulo the
unit period. -/
theorem exists_commonStep_of_rationalAffineLine
    (τ : ι → ℂ) (ω : ℂ) (hω : 0 < ω.im)
    (a b : ι → ℚ) (hb : ∀ i, 0 < b i)
    (hτ : ∀ i, τ i = (a i : ℂ) + (b i : ℂ) * ω) :
    ∃ β : ℂ, 0 < β.im ∧
      Nonempty (MultipleEllipticGammaCommonStep τ β) := by
  let n : ι → ℕ := fun i => (a i).den * (b i).den
  let A : ι → ℤ := fun i => (a i).num * ((b i).den : ℤ)
  let B : ι → ℕ := fun i => (b i).num.natAbs * (a i).den
  let C : ι → ℕ := fun i => ∏ j ∈ Finset.univ.erase i, B j
  let P : ℕ := ∏ i, B i
  have hn : ∀ i, 0 < n i := fun i =>
    Nat.mul_pos (a i).pos (b i).pos
  have hB : ∀ i, 0 < B i := fun i =>
    Nat.mul_pos (Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr (hb i))))
      (a i).pos
  have hC : ∀ i, 0 < C i := by
    intro i
    exact Finset.prod_pos fun j hj => hB j
  have hP : 0 < P := Finset.prod_pos fun i hi => hB i
  have hscaled : ∀ i,
      (n i : ℂ) * τ i = (A i : ℂ) + (B i : ℂ) * ω := by
    intro i
    rw [hτ i]
    have hbnum : 0 < (b i).num := Rat.num_pos.mpr (hb i)
    have hbnat : ((b i).num.natAbs : ℤ) = (b i).num :=
      Int.natAbs_of_nonneg hbnum.le
    have hbnatC : (((b i).num.natAbs : ℕ) : ℂ) = ((b i).num : ℂ) := by
      simpa using congrArg (fun z : ℤ => (z : ℂ)) hbnat
    dsimp [n, A, B]
    rw [Rat.cast_def, Rat.cast_def]
    push_cast
    field_simp [(a i).den_nz, (b i).den_nz]
    rw [hbnatC]
    ring
  refine ⟨(P : ℂ) * ω, ?_, ?_⟩
  · norm_num [mul_im]
    have hPReal : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
    exact mul_pos hPReal hω
  · refine ⟨
      { multiple := fun i => n i * C i
        multiple_pos := fun i => Nat.mul_pos (hn i) (hC i)
        offset := fun i => -(A i * (C i : ℤ))
        step_eq := ?_ }⟩
    intro i
    have hprod : B i * C i = P := by
      dsimp [C, P]
      exact Finset.mul_prod_erase Finset.univ B (Finset.mem_univ i)
    have hprodC : (B i : ℂ) * (C i : ℂ) = (P : ℂ) := by
      exact_mod_cast hprod
    have hs := congrArg (fun z : ℂ => (C i : ℂ) * z) (hscaled i)
    push_cast
    rw [← hprodC]
    linear_combination -hs

/-- Failure of every rank-three minor produces the common step used by hierarchy nilpotence. -/
theorem exists_commonStep_of_not_rankThreeMinor
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hminor : ¬ MultipleEllipticGammaHasRankThreeMinor τ) :
    ∃ β : ℂ, 0 < β.im ∧
      Nonempty (MultipleEllipticGammaCommonStep τ β) := by
  obtain ⟨ω, hω, a, b, hb, hab⟩ :=
    exists_rationalAffineLine_of_not_rankThreeMinor τ hτ hminor
  exact exists_commonStep_of_rationalAffineLine τ ω hω a b hb hab

/-! ## The intrinsic augmented period rank -/

/-- Rational rank of the period family after adjoining the unit translation. -/
def multipleEllipticGammaAugmentedPeriodRank (τ : ι → ℂ) : ℕ :=
  Module.finrank ℚ (Submodule.span ℚ (insert (1 : ℂ) (Set.range τ)))

omit [DecidableEq ι] in
/-- One rank-three minor forces augmented rational period rank at least three. -/
theorem rankThreeMinor_implies_three_le_augmentedPeriodRank
    (τ : ι → ℂ) (hminor : MultipleEllipticGammaHasRankThreeMinor τ) :
    3 ≤ multipleEllipticGammaAugmentedPeriodRank τ := by
  obtain ⟨q, r, hqr, hlin⟩ := hminor
  let v : Fin 3 → ℂ := ellipticGammaSourcePeriods (τ q) (τ r)
  have hsub : Set.range v ⊆ insert (1 : ℂ) (Set.range τ) := by
    rintro x ⟨j, rfl⟩
    fin_cases j <;> simp [v, ellipticGammaSourcePeriods]
  have hmono : Submodule.span ℚ (Set.range v) ≤
      Submodule.span ℚ (insert (1 : ℂ) (Set.range τ)) :=
    Submodule.span_mono hsub
  haveI : Module.Finite ℚ
      (Submodule.span ℚ (insert (1 : ℂ) (Set.range τ))) :=
    Module.Finite.span_of_finite ℚ ((Set.finite_range τ).insert 1)
  calc
    3 = Module.finrank ℚ (Submodule.span ℚ (Set.range v)) := by
      symm
      simpa [v] using finrank_span_eq_card hlin
    _ ≤ multipleEllipticGammaAugmentedPeriodRank τ :=
      Submodule.finrank_mono hmono

omit [Fintype ι] [DecidableEq ι] in
/-- If no rank-three minor exists, the augmented rational period rank is at most two. -/
theorem augmentedPeriodRank_le_two_of_not_rankThreeMinor
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hminor : ¬ MultipleEllipticGammaHasRankThreeMinor τ) :
    multipleEllipticGammaAugmentedPeriodRank τ ≤ 2 := by
  obtain ⟨ω, hω, a, b, hb, hab⟩ :=
    exists_rationalAffineLine_of_not_rankThreeMinor τ hτ hminor
  let w : Fin 2 → ℂ := ![(1 : ℂ), ω]
  have hone : (1 : ℂ) ∈ Submodule.span ℚ (Set.range w) :=
    Submodule.subset_span ⟨0, by simp [w]⟩
  have hωmem : ω ∈ Submodule.span ℚ (Set.range w) :=
    Submodule.subset_span ⟨1, by simp [w]⟩
  have hgen : insert (1 : ℂ) (Set.range τ) ⊆
      Submodule.span ℚ (Set.range w) := by
    intro x hx
    rcases hx with rfl | ⟨i, rfl⟩
    · exact hone
    · rw [hab i]
      simpa [Algebra.smul_def] using
        (Submodule.add_mem _
          (Submodule.smul_mem _ (a i) hone)
          (Submodule.smul_mem _ (b i) hωmem))
  have hspan : Submodule.span ℚ (insert (1 : ℂ) (Set.range τ)) ≤
      Submodule.span ℚ (Set.range w) :=
    Submodule.span_le.mpr hgen
  haveI : Module.Finite ℚ (Submodule.span ℚ (Set.range w)) :=
    Module.Finite.span_of_finite ℚ (Set.finite_range w)
  calc
    multipleEllipticGammaAugmentedPeriodRank τ ≤
        Module.finrank ℚ (Submodule.span ℚ (Set.range w)) :=
      Submodule.finrank_mono hspan
    _ = 2 := by
      simpa [w] using
        finrank_span_eq_card (linearIndependent_rat_one_of_im_pos hω)

omit [DecidableEq ι] in
/-- The unit period and any upper-half-plane period force augmented rank at least two. -/
theorem two_le_augmentedPeriodRank
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    2 ≤ multipleEllipticGammaAugmentedPeriodRank τ := by
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  let v : Fin 2 → ℂ := ![(1 : ℂ), τ i₀]
  have hsub : Set.range v ⊆ insert (1 : ℂ) (Set.range τ) := by
    rintro x ⟨j, rfl⟩
    fin_cases j <;> simp [v]
  have hmono : Submodule.span ℚ (Set.range v) ≤
      Submodule.span ℚ (insert (1 : ℂ) (Set.range τ)) :=
    Submodule.span_mono hsub
  haveI : Module.Finite ℚ
      (Submodule.span ℚ (insert (1 : ℂ) (Set.range τ))) :=
    Module.Finite.span_of_finite ℚ ((Set.finite_range τ).insert 1)
  calc
    2 = Module.finrank ℚ (Submodule.span ℚ (Set.range v)) := by
      symm
      simpa [v] using
        finrank_span_eq_card (linearIndependent_rat_one_of_im_pos (hτ i₀))
    _ ≤ multipleEllipticGammaAugmentedPeriodRank τ :=
      Submodule.finrank_mono hmono

omit [DecidableEq ι] in
/-- **Finite-minor principle.** Augmented period rank is at least three exactly when one pair of
parameters already witnesses it together with the unit period. -/
theorem three_le_augmentedPeriodRank_iff_rankThreeMinor
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    3 ≤ multipleEllipticGammaAugmentedPeriodRank τ ↔
      MultipleEllipticGammaHasRankThreeMinor τ := by
  constructor
  · intro hrank
    by_contra hminor
    have hle :=
      augmentedPeriodRank_le_two_of_not_rankThreeMinor τ hτ hminor
    omega
  · exact rankThreeMinor_implies_three_le_augmentedPeriodRank τ

omit [DecidableEq ι] in
/-- The only possible low-rank phase is exact augmented rank two. -/
theorem augmentedPeriodRank_eq_two_iff_not_rankThreeMinor
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaAugmentedPeriodRank τ = 2 ↔
      ¬ MultipleEllipticGammaHasRankThreeMinor τ := by
  constructor
  · intro hrank hminor
    have hthree :=
      rankThreeMinor_implies_three_le_augmentedPeriodRank τ hminor
    omega
  · intro hminor
    exact Nat.le_antisymm
      (augmentedPeriodRank_le_two_of_not_rankThreeMinor τ hτ hminor)
      (two_le_augmentedPeriodRank τ hτ)

/-- **Exact raw-function phase law.** Differential algebraicity is equivalent to absence of a
rank-three period minor. -/
theorem differentialAlgebraicOver_multipleEllipticGammaMero_iff_not_rankThreeMinor
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    DifferentialAlgebraicOver (RatFunc ℂ) (multipleEllipticGammaMero τ hτ) ↔
      ¬ MultipleEllipticGammaHasRankThreeMinor τ := by
  constructor
  · intro hda hminor
    exact (hypertranscendentalOver_multipleEllipticGammaMero_of_rankThreeMinor
      τ hτ hminor)
        (differentialAlgebraicOver_rationalCoordinateField_of_ratFunc hda)
  · intro hminor
    obtain ⟨β, hβ, ⟨hcommon⟩⟩ :=
      exists_commonStep_of_not_rankThreeMinor τ hτ hminor
    exact differentialAlgebraicOver_multipleEllipticGammaMero_of_commonStep
      τ hτ β hβ hcommon

/-- **Exact logarithmic-derivative phase law.** Differential algebraicity is equivalent to absence
of a rank-three period minor. -/
theorem differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_not_rankThreeMinor
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero τ hτ) ↔
      ¬ MultipleEllipticGammaHasRankThreeMinor τ := by
  constructor
  · intro hda hminor
    exact (hypertranscendentalOver_multipleEllipticGammaLogDerivMero_of_rankThreeMinor
      τ hτ hminor)
        (differentialAlgebraicOver_rationalCoordinateField_of_ratFunc hda)
  · intro hminor
    obtain ⟨β, hβ, ⟨hcommon⟩⟩ :=
      exists_commonStep_of_not_rankThreeMinor τ hτ hminor
    exact differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_of_commonStep
      τ hτ β hβ hcommon

/-- Raw multiple elliptic Gamma is hypertranscendental exactly on the rank-three-minor phase. -/
theorem hypertranscendentalOver_multipleEllipticGammaMero_iff_rankThreeMinor
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    HypertranscendentalOver (RatFunc ℂ) (multipleEllipticGammaMero τ hτ) ↔
      MultipleEllipticGammaHasRankThreeMinor τ := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_multipleEllipticGammaMero_iff_not_rankThreeMinor]
  tauto

/-- The logarithmic derivative is hypertranscendental exactly on the rank-three-minor phase. -/
theorem hypertranscendentalOver_multipleEllipticGammaLogDerivMero_iff_rankThreeMinor
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    HypertranscendentalOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero τ hτ) ↔
      MultipleEllipticGammaHasRankThreeMinor τ := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_not_rankThreeMinor]
  tauto

/-- **Exact raw rank law.** Raw multiple elliptic Gamma is differentially algebraic precisely at
augmented rational period rank two. -/
theorem differentialAlgebraicOver_multipleEllipticGammaMero_iff_augmentedPeriodRank_eq_two
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    DifferentialAlgebraicOver (RatFunc ℂ) (multipleEllipticGammaMero τ hτ) ↔
      multipleEllipticGammaAugmentedPeriodRank τ = 2 := by
  rw [differentialAlgebraicOver_multipleEllipticGammaMero_iff_not_rankThreeMinor τ hτ,
    augmentedPeriodRank_eq_two_iff_not_rankThreeMinor τ hτ]

/-- **Exact logarithmic-derivative rank law.** The logarithmic derivative is differentially
algebraic precisely at augmented rational period rank two. -/
theorem differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_augmentedPeriodRank_eq_two
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero τ hτ) ↔
      multipleEllipticGammaAugmentedPeriodRank τ = 2 := by
  rw [differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_not_rankThreeMinor τ hτ,
    augmentedPeriodRank_eq_two_iff_not_rankThreeMinor τ hτ]

/-- **Exact raw hypertranscendence rank law.** Raw multiple elliptic Gamma is
hypertranscendental precisely when augmented rational period rank is at least three. -/
theorem hypertranscendentalOver_multipleEllipticGammaMero_iff_three_le_augmentedPeriodRank
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    HypertranscendentalOver (RatFunc ℂ) (multipleEllipticGammaMero τ hτ) ↔
      3 ≤ multipleEllipticGammaAugmentedPeriodRank τ := by
  rw [hypertranscendentalOver_multipleEllipticGammaMero_iff_rankThreeMinor τ hτ,
    three_le_augmentedPeriodRank_iff_rankThreeMinor τ hτ]

/-- **Exact logarithmic-derivative hypertranscendence rank law.** The logarithmic derivative is
hypertranscendental precisely when augmented rational period rank is at least three. -/
theorem
    hypertranscendentalOver_multipleEllipticGammaLogDerivMero_iff_three_le_augmentedPeriodRank
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    HypertranscendentalOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero τ hτ) ↔
      3 ≤ multipleEllipticGammaAugmentedPeriodRank τ := by
  rw [hypertranscendentalOver_multipleEllipticGammaLogDerivMero_iff_rankThreeMinor τ hτ,
    three_le_augmentedPeriodRank_iff_rankThreeMinor τ hτ]

/-! ## Arbitrary period families through their finite subfamilies -/

/-- Restriction of an arbitrary period family to a finite set of labels. -/
def multipleEllipticGammaFiniteSubfamily
    {κ : Type} (τ : κ → ℂ) (S : Finset κ) : ↥S → ℂ :=
  fun i => τ i.1

omit [Fintype ι] [DecidableEq ι] in
/-- Two labels form an edge of the rank-three obstruction graph when they are distinct and their
periods, together with the unit period, are rationally linearly independent. -/
def MultipleEllipticGammaRankThreeEdge
    (τ : ι → ℂ) (q r : ι) : Prop :=
  q ≠ r ∧
    LinearIndependent ℚ (ellipticGammaSourcePeriods (τ q) (τ r))

omit [Fintype ι] [DecidableEq ι] in
/-- The rank-three obstruction relation is symmetric, so it defines an undirected graph. -/
theorem rankThreeEdge_symm
    (τ : ι → ℂ) {q r : ι}
    (h : MultipleEllipticGammaRankThreeEdge τ q r) :
    MultipleEllipticGammaRankThreeEdge τ r q := by
  refine ⟨h.1.symm, ?_⟩
  let e : Fin 3 → Fin 3 := ![0, 2, 1]
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [e] at hij ⊢
  have hcomp := h.2.comp e he
  convert hcomp using 1
  funext i
  fin_cases i <;> rfl

omit [Fintype ι] [DecidableEq ι] in
/-- A finite section contains a rank-three graph edge exactly when its restricted period family
has a rank-three minor. -/
def MultipleEllipticGammaFiniteSectionContainsRankThreeEdge
    (τ : ι → ℂ) (S : Finset ι) : Prop :=
  MultipleEllipticGammaHasRankThreeMinor
    (multipleEllipticGammaFiniteSubfamily τ S)

omit [Fintype ι] [DecidableEq ι] in
/-- The rank-three-minor predicate is precisely existence of an edge in the obstruction graph. -/
theorem hasRankThreeMinor_iff_exists_rankThreeEdge
    (τ : ι → ℂ) :
    MultipleEllipticGammaHasRankThreeMinor τ ↔
      ∃ q r : ι, MultipleEllipticGammaRankThreeEdge τ q r :=
  Iff.rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Containing a rank-three edge is upward closed among finite sections. -/
theorem finiteSectionContainsRankThreeEdge_mono
    (τ : ι → ℂ) {S T : Finset ι} (hST : S ⊆ T) :
    MultipleEllipticGammaFiniteSectionContainsRankThreeEdge τ S →
      MultipleEllipticGammaFiniteSectionContainsRankThreeEdge τ T := by
  classical
  rintro ⟨q, r, hqr, hlin⟩
  let qT : ↥T := ⟨q.1, hST q.2⟩
  let rT : ↥T := ⟨r.1, hST r.2⟩
  refine ⟨qT, rT, ?_, ?_⟩
  · intro h
    apply hqr
    apply Subtype.ext
    simpa [qT, rT] using congrArg Subtype.val h
  · simpa [multipleEllipticGammaFiniteSubfamily, qT, rT] using hlin

omit [Fintype ι] [DecidableEq ι] in
/-- **Exact rank-three-graph law for a nonempty finite section.** Raw and logarithmic-derivative
multiple elliptic Gamma functions are differentially algebraic exactly on graph-independent
sections and hypertranscendental exactly on sections containing an edge. -/
theorem multipleEllipticGamma_nonemptyFiniteSection_exactRankThreeGraphLaw
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (S : Finset ι) (hS : S.Nonempty) :
    (DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaMero
          (multipleEllipticGammaFiniteSubfamily τ S)
          (fun i => hτ i.1)) ↔
      ¬ MultipleEllipticGammaFiniteSectionContainsRankThreeEdge τ S) ∧
    (DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero
          (multipleEllipticGammaFiniteSubfamily τ S)
          (fun i => hτ i.1)) ↔
      ¬ MultipleEllipticGammaFiniteSectionContainsRankThreeEdge τ S) ∧
    (HypertranscendentalOver (RatFunc ℂ)
        (multipleEllipticGammaMero
          (multipleEllipticGammaFiniteSubfamily τ S)
          (fun i => hτ i.1)) ↔
      MultipleEllipticGammaFiniteSectionContainsRankThreeEdge τ S) ∧
    (HypertranscendentalOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero
          (multipleEllipticGammaFiniteSubfamily τ S)
          (fun i => hτ i.1)) ↔
      MultipleEllipticGammaFiniteSectionContainsRankThreeEdge τ S) := by
  classical
  obtain ⟨i, hi⟩ := hS
  letI : Nonempty ↥S := ⟨⟨i, hi⟩⟩
  exact ⟨
    differentialAlgebraicOver_multipleEllipticGammaMero_iff_not_rankThreeMinor
      (multipleEllipticGammaFiniteSubfamily τ S) (fun j => hτ j.1),
    differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_not_rankThreeMinor
      (multipleEllipticGammaFiniteSubfamily τ S) (fun j => hτ j.1),
    hypertranscendentalOver_multipleEllipticGammaMero_iff_rankThreeMinor
      (multipleEllipticGammaFiniteSubfamily τ S) (fun j => hτ j.1),
    hypertranscendentalOver_multipleEllipticGammaLogDerivMero_iff_rankThreeMinor
      (multipleEllipticGammaFiniteSubfamily τ S) (fun j => hτ j.1)⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **Cardinality-free complete phase profile.** For every ambient period family and every finite
section, including the empty terminal section, the rank-three obstruction graph decides both raw
and logarithmic-derivative differential algebraicity and hypertranscendence exactly. -/
theorem multipleEllipticGamma_everyFiniteSection_exactRankThreeGraphLaw
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (S : Finset ι) :
    (DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaMero
          (multipleEllipticGammaFiniteSubfamily τ S)
          (fun i => hτ i.1)) ↔
      ¬ MultipleEllipticGammaFiniteSectionContainsRankThreeEdge τ S) ∧
    (DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero
          (multipleEllipticGammaFiniteSubfamily τ S)
          (fun i => hτ i.1)) ↔
      ¬ MultipleEllipticGammaFiniteSectionContainsRankThreeEdge τ S) ∧
    (HypertranscendentalOver (RatFunc ℂ)
        (multipleEllipticGammaMero
          (multipleEllipticGammaFiniteSubfamily τ S)
          (fun i => hτ i.1)) ↔
      MultipleEllipticGammaFiniteSectionContainsRankThreeEdge τ S) ∧
    (HypertranscendentalOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero
          (multipleEllipticGammaFiniteSubfamily τ S)
          (fun i => hτ i.1)) ↔
      MultipleEllipticGammaFiniteSectionContainsRankThreeEdge τ S) := by
  classical
  by_cases hS : S.Nonempty
  · exact multipleEllipticGamma_nonemptyFiniteSection_exactRankThreeGraphLaw
      τ hτ S hS
  · letI : IsEmpty ↥S := ⟨fun i => hS ⟨i.1, i.2⟩⟩
    have hnoEdge :
        ¬ MultipleEllipticGammaFiniteSectionContainsRankThreeEdge τ S := by
      rintro ⟨q, r, hqr, hlin⟩
      exact isEmptyElim q
    let β : ℂ := Complex.I
    have hβ : 0 < β.im := by norm_num [β]
    let hcommon :
        MultipleEllipticGammaCommonStep
          (multipleEllipticGammaFiniteSubfamily τ S) β :=
      { multiple := fun i => isEmptyElim i
        multiple_pos := fun i => isEmptyElim i
        offset := fun i => isEmptyElim i
        step_eq := fun i => isEmptyElim i }
    have hraw :
        DifferentialAlgebraicOver (RatFunc ℂ)
          (multipleEllipticGammaMero
            (multipleEllipticGammaFiniteSubfamily τ S)
            (fun i => hτ i.1)) :=
      differentialAlgebraicOver_multipleEllipticGammaMero_of_commonStep
        (multipleEllipticGammaFiniteSubfamily τ S) (fun i => hτ i.1)
        β hβ hcommon
    have hlog :
        DifferentialAlgebraicOver (RatFunc ℂ)
          (multipleEllipticGammaLogDerivMero
            (multipleEllipticGammaFiniteSubfamily τ S)
            (fun i => hτ i.1)) :=
      differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_of_commonStep
        (multipleEllipticGammaFiniteSubfamily τ S) (fun i => hτ i.1)
        β hβ hcommon
    exact ⟨
      ⟨fun _ => hnoEdge, fun _ => hraw⟩,
      ⟨fun _ => hnoEdge, fun _ => hlog⟩,
      ⟨fun h => False.elim (h hraw), fun h => False.elim (hnoEdge h)⟩,
      ⟨fun h => False.elim (h hlog), fun h => False.elim (hnoEdge h)⟩⟩

omit [Fintype ι] [DecidableEq ι] in
/-- An arbitrary, possibly infinite, upper-half-plane period family lies in the rational-affine
phase exactly when every nonempty finite subfamily gives differentially algebraic raw and
logarithmic-derivative multiple elliptic Gamma functions. -/
theorem allFiniteSubfamilies_differentialAlgebraic_iff_not_rankThreeMinor
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    (∀ (S : Finset ι), S.Nonempty →
      DifferentialAlgebraicOver (RatFunc ℂ)
          (multipleEllipticGammaMero
            (multipleEllipticGammaFiniteSubfamily τ S)
            (fun i => hτ i.1)) ∧
        DifferentialAlgebraicOver (RatFunc ℂ)
          (multipleEllipticGammaLogDerivMero
            (multipleEllipticGammaFiniteSubfamily τ S)
            (fun i => hτ i.1))) ↔
      ¬ MultipleEllipticGammaHasRankThreeMinor τ := by
  classical
  constructor
  · intro hall hminor
    obtain ⟨q, r, hqr, hlin⟩ := hminor
    let S : Finset ι := {q, r}
    let qS : ↥S := ⟨q, by simp [S]⟩
    let rS : ↥S := ⟨r, by simp [S]⟩
    letI : Nonempty ↥S := ⟨qS⟩
    have hlocalMinor :
        MultipleEllipticGammaHasRankThreeMinor
          (multipleEllipticGammaFiniteSubfamily τ S) := by
      refine ⟨qS, rS, ?_, ?_⟩
      · intro h
        exact hqr (congrArg Subtype.val h)
      · simpa [multipleEllipticGammaFiniteSubfamily, qS, rS] using hlin
    have hS : S.Nonempty := ⟨q, by simp [S]⟩
    have hda := (hall S hS).1
    have hlocalNoMinor :=
      (differentialAlgebraicOver_multipleEllipticGammaMero_iff_not_rankThreeMinor
        (multipleEllipticGammaFiniteSubfamily τ S)
        (fun i => hτ i.1)).1 hda
    exact hlocalNoMinor hlocalMinor
  · intro hminor S hS
    obtain ⟨i, hi⟩ := hS
    letI : Nonempty ↥S := ⟨⟨i, hi⟩⟩
    have hlocalMinor :
        ¬ MultipleEllipticGammaHasRankThreeMinor
          (multipleEllipticGammaFiniteSubfamily τ S) := by
      rintro ⟨q, r, hqr, hlin⟩
      apply hminor
      refine ⟨q.1, r.1, ?_, ?_⟩
      · intro h
        apply hqr
        exact Subtype.ext h
      · simpa [multipleEllipticGammaFiniteSubfamily] using hlin
    exact ⟨
      (differentialAlgebraicOver_multipleEllipticGammaMero_iff_not_rankThreeMinor
        (multipleEllipticGammaFiniteSubfamily τ S)
        (fun j => hτ j.1)).2 hlocalMinor,
      (differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_not_rankThreeMinor
        (multipleEllipticGammaFiniteSubfamily τ S)
        (fun j => hτ j.1)).2 hlocalMinor⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **Infinite-family finite-section law.** A possibly infinite period family lies on one rational
affine line exactly when every standard finite-order function drawn from it, together with its
logarithmic derivative, is differentially algebraic. -/
theorem liesOnRationalAffineLine_iff_allFiniteSubfamilies_differentialAlgebraic
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    MultipleEllipticGammaLiesOnRationalAffineLine τ ↔
      ∀ (S : Finset ι), S.Nonempty →
        DifferentialAlgebraicOver (RatFunc ℂ)
            (multipleEllipticGammaMero
              (multipleEllipticGammaFiniteSubfamily τ S)
              (fun i => hτ i.1)) ∧
          DifferentialAlgebraicOver (RatFunc ℂ)
            (multipleEllipticGammaLogDerivMero
              (multipleEllipticGammaFiniteSubfamily τ S)
              (fun i => hτ i.1)) := by
  rw [allFiniteSubfamilies_differentialAlgebraic_iff_not_rankThreeMinor τ hτ]
  exact liesOnRationalAffineLine_iff_not_rankThreeMinor τ hτ

omit [Fintype ι] [DecidableEq ι] in
/-- A rank-three pair in an arbitrary period family forces the hypertranscendental phase on every
finite subfamily containing that pair. -/
theorem rankThreeMinor_persists_to_all_finite_supersets
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hminor : MultipleEllipticGammaHasRankThreeMinor τ) :
    ∃ q r : ι, q ≠ r ∧
      LinearIndependent ℚ (ellipticGammaSourcePeriods (τ q) (τ r)) ∧
        ∀ (S : Finset ι), q ∈ S → r ∈ S →
          HypertranscendentalOver (RatFunc ℂ)
              (multipleEllipticGammaMero
                (multipleEllipticGammaFiniteSubfamily τ S)
                (fun i => hτ i.1)) ∧
            HypertranscendentalOver (RatFunc ℂ)
              (multipleEllipticGammaLogDerivMero
                (multipleEllipticGammaFiniteSubfamily τ S)
                (fun i => hτ i.1)) := by
  classical
  obtain ⟨q, r, hqr, hlin⟩ := hminor
  refine ⟨q, r, hqr, hlin, ?_⟩
  intro S hq hr
  let qS : ↥S := ⟨q, hq⟩
  let rS : ↥S := ⟨r, hr⟩
  letI : Nonempty ↥S := ⟨qS⟩
  have hlocalMinor :
      MultipleEllipticGammaHasRankThreeMinor
        (multipleEllipticGammaFiniteSubfamily τ S) := by
    refine ⟨qS, rS, ?_, ?_⟩
    · intro h
      exact hqr (congrArg Subtype.val h)
    · simpa [multipleEllipticGammaFiniteSubfamily, qS, rS] using hlin
  exact ⟨
    (hypertranscendentalOver_multipleEllipticGammaMero_iff_rankThreeMinor
      (multipleEllipticGammaFiniteSubfamily τ S)
      (fun i => hτ i.1)).2 hlocalMinor,
    (hypertranscendentalOver_multipleEllipticGammaLogDerivMero_iff_rankThreeMinor
      (multipleEllipticGammaFiniteSubfamily τ S)
      (fun i => hτ i.1)).2 hlocalMinor⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **Exact arbitrary-family finite-section dichotomy.** Every nonempty period family, with no
finiteness or countability assumption on its labels, has exactly one global phase: one rational
affine line makes all nonempty finite sections differentially algebraic, while a rank-three pair
makes every finite section containing that pair hypertranscendental. -/
theorem multipleEllipticGamma_arbitraryPeriodFamily_exactFiniteSectionLaw
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    (((MultipleEllipticGammaLiesOnRationalAffineLine τ) ∧
        ∀ (S : Finset ι), S.Nonempty →
          DifferentialAlgebraicOver (RatFunc ℂ)
              (multipleEllipticGammaMero
                (multipleEllipticGammaFiniteSubfamily τ S)
                (fun i => hτ i.1)) ∧
            DifferentialAlgebraicOver (RatFunc ℂ)
              (multipleEllipticGammaLogDerivMero
                (multipleEllipticGammaFiniteSubfamily τ S)
                (fun i => hτ i.1))) ∨
      ∃ q r : ι, q ≠ r ∧
        LinearIndependent ℚ (ellipticGammaSourcePeriods (τ q) (τ r)) ∧
          ∀ (S : Finset ι), q ∈ S → r ∈ S →
            HypertranscendentalOver (RatFunc ℂ)
                (multipleEllipticGammaMero
                  (multipleEllipticGammaFiniteSubfamily τ S)
                  (fun i => hτ i.1)) ∧
              HypertranscendentalOver (RatFunc ℂ)
                (multipleEllipticGammaLogDerivMero
                  (multipleEllipticGammaFiniteSubfamily τ S)
                  (fun i => hτ i.1))) ∧
      ¬ (MultipleEllipticGammaLiesOnRationalAffineLine τ ∧
          MultipleEllipticGammaHasRankThreeMinor τ) := by
  constructor
  · by_cases hminor : MultipleEllipticGammaHasRankThreeMinor τ
    · right
      exact rankThreeMinor_persists_to_all_finite_supersets τ hτ hminor
    · left
      exact ⟨
        (liesOnRationalAffineLine_iff_not_rankThreeMinor τ hτ).2 hminor,
        (allFiniteSubfamilies_differentialAlgebraic_iff_not_rankThreeMinor
          τ hτ).2 hminor⟩
  · rintro ⟨hline, hminor⟩
    exact (liesOnRationalAffineLine_iff_not_rankThreeMinor τ hτ).1 hline hminor

omit [Fintype ι] [DecidableEq ι] in
/-- Every nonempty finite section of an arbitrary period family is in the differentially
algebraic phase. -/
def MultipleEllipticGammaAllFiniteSectionsDifferentialAlgebraic
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) : Prop :=
  ∀ (S : Finset ι), S.Nonempty →
    DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaMero
          (multipleEllipticGammaFiniteSubfamily τ S)
          (fun i => hτ i.1)) ∧
      DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero
          (multipleEllipticGammaFiniteSubfamily τ S)
          (fun i => hτ i.1))

omit [Fintype ι] [DecidableEq ι] in
/-- One rank-three pair forces every finite section containing it into the
hypertranscendental phase. -/
def MultipleEllipticGammaHasPersistentFiniteSectionHypertranscendence
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) : Prop :=
  ∃ q r : ι, q ≠ r ∧
    LinearIndependent ℚ (ellipticGammaSourcePeriods (τ q) (τ r)) ∧
      ∀ (S : Finset ι), q ∈ S → r ∈ S →
        HypertranscendentalOver (RatFunc ℂ)
            (multipleEllipticGammaMero
              (multipleEllipticGammaFiniteSubfamily τ S)
              (fun i => hτ i.1)) ∧
          HypertranscendentalOver (RatFunc ℂ)
            (multipleEllipticGammaLogDerivMero
              (multipleEllipticGammaFiniteSubfamily τ S)
              (fun i => hτ i.1))

omit [Fintype ι] [DecidableEq ι] in
/-- **Cardinality-free universal period-family law.** This includes every index type, including the
empty terminal family: exactly one rational-affine/all-finite-DA phase or persistent two-point
hypertranscendental phase occurs. -/
theorem multipleEllipticGamma_everyPeriodFamily_exactFiniteSectionLaw
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    (((MultipleEllipticGammaLiesOnRationalAffineLine τ) ∧
        MultipleEllipticGammaAllFiniteSectionsDifferentialAlgebraic τ hτ) ∨
      MultipleEllipticGammaHasPersistentFiniteSectionHypertranscendence τ hτ) ∧
      ¬ (MultipleEllipticGammaLiesOnRationalAffineLine τ ∧
          MultipleEllipticGammaHasRankThreeMinor τ) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hEmpty =>
      letI : IsEmpty ι := hEmpty
      constructor
      · left
        refine ⟨?_, ?_⟩
        · refine ⟨Complex.I, by norm_num, (fun i => isEmptyElim i),
            (fun i => isEmptyElim i), ?_, ?_⟩
          · intro i
            exact isEmptyElim i
          · intro i
            exact isEmptyElim i
        · intro S hS
          obtain ⟨i, hi⟩ := hS
          exact isEmptyElim i
      · rintro ⟨hline, ⟨q, r, hqr, hlin⟩⟩
        exact isEmptyElim q
  | inr hNonempty =>
      letI : Nonempty ι := hNonempty
      simpa [MultipleEllipticGammaAllFiniteSectionsDifferentialAlgebraic,
        MultipleEllipticGammaHasPersistentFiniteSectionHypertranscendence] using
        multipleEllipticGamma_arbitraryPeriodFamily_exactFiniteSectionLaw τ hτ

omit [Fintype ι] [DecidableEq ι] in
/-- Kato's rational-ray hypothesis always lies in the differentially algebraic phase. -/
theorem differentialAlgebraicOver_multipleEllipticGamma_of_rationalRay
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hray : MultipleEllipticGammaLiesOnRationalRay τ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (multipleEllipticGammaMero τ hτ) ∧
      DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero τ hτ) := by
  have hline :=
    liesOnRationalAffineLine_of_liesOnRationalRay τ hτ hray
  have hminor :=
    (liesOnRationalAffineLine_iff_not_rankThreeMinor τ hτ).1 hline
  exact ⟨
    (differentialAlgebraicOver_multipleEllipticGammaMero_iff_not_rankThreeMinor
      τ hτ).2 hminor,
    (differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_not_rankThreeMinor
      τ hτ).2 hminor⟩

/-- The two-period vector `(i, 1+i)`, which lies on a rational affine line but not on a rational
ray. -/
def multipleEllipticGammaNonRationalDAExample : Fin 2 → ℂ :=
  ![Complex.I, 1 + Complex.I]

/-- Both periods in the explicit non-rational example lie in the upper half-plane. -/
theorem multipleEllipticGammaNonRationalDAExample_im_pos :
    ∀ i, 0 < (multipleEllipticGammaNonRationalDAExample i).im := by
  intro i
  fin_cases i <;> norm_num [multipleEllipticGammaNonRationalDAExample]

/-- The explicit non-rational example lies on the rational affine line generated by `i`. -/
theorem multipleEllipticGammaNonRationalDAExample_liesOnRationalAffineLine :
    MultipleEllipticGammaLiesOnRationalAffineLine
      multipleEllipticGammaNonRationalDAExample := by
  refine ⟨Complex.I, by norm_num,
    ![(0 : ℚ), 1], ![(1 : ℚ), 1], ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;>
      norm_num [multipleEllipticGammaNonRationalDAExample]

/-- The explicit rational-affine example does not satisfy the rational-ray condition. -/
theorem multipleEllipticGammaNonRationalDAExample_not_liesOnRationalRay :
    ¬ MultipleEllipticGammaLiesOnRationalRay
      multipleEllipticGammaNonRationalDAExample := by
  rintro ⟨ω, hω, c, hc⟩
  have h0 := hc (0 : Fin 2)
  have h1 := hc (1 : Fin 2)
  simp [multipleEllipticGammaNonRationalDAExample] at h0 h1
  have hcross :
      (c 0 : ℂ) * (1 + Complex.I) = (c 1 : ℂ) * Complex.I := by
    rw [h1, h0]
    ring
  have hre := congrArg Complex.re hcross
  norm_num [mul_re] at hre
  have hc0 : c 0 = 0 := by
    exact_mod_cast hre
  rw [hc0] at h0
  norm_num at h0

/-- Both the raw two-period function and its logarithmic derivative in the explicit non-rational
example are differentially algebraic. -/
theorem multipleEllipticGammaNonRationalDAExample_differentialAlgebraic :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaMero
          multipleEllipticGammaNonRationalDAExample
          multipleEllipticGammaNonRationalDAExample_im_pos) ∧
      DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero
          multipleEllipticGammaNonRationalDAExample
          multipleEllipticGammaNonRationalDAExample_im_pos) := by
  have hminor :=
    (liesOnRationalAffineLine_iff_not_rankThreeMinor
      multipleEllipticGammaNonRationalDAExample
      multipleEllipticGammaNonRationalDAExample_im_pos).1
        multipleEllipticGammaNonRationalDAExample_liesOnRationalAffineLine
  exact ⟨
    (differentialAlgebraicOver_multipleEllipticGammaMero_iff_not_rankThreeMinor
      multipleEllipticGammaNonRationalDAExample
      multipleEllipticGammaNonRationalDAExample_im_pos).2 hminor,
    (differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_not_rankThreeMinor
      multipleEllipticGammaNonRationalDAExample
      multipleEllipticGammaNonRationalDAExample_im_pos).2 hminor⟩

/-- **Facewise exact rank law.** Every nonempty deletion face obeys the same rank-two versus
rank-at-least-three dichotomy, simultaneously for the raw face and its logarithmic derivative. -/
theorem multipleEllipticGammaFace_exactPeriodRankLaw
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι)
    (hJ : Jᶜ.Nonempty) :
    (DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaFaceMero τ hτ J) ↔
      multipleEllipticGammaAugmentedPeriodRank
        (multipleEllipticGammaFaceParameters τ J) = 2) ∧
    (DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) ↔
      multipleEllipticGammaAugmentedPeriodRank
        (multipleEllipticGammaFaceParameters τ J) = 2) ∧
    (HypertranscendentalOver (RatFunc ℂ)
        (multipleEllipticGammaFaceMero τ hτ J) ↔
      3 ≤ multipleEllipticGammaAugmentedPeriodRank
        (multipleEllipticGammaFaceParameters τ J)) ∧
    (HypertranscendentalOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) ↔
      3 ≤ multipleEllipticGammaAugmentedPeriodRank
        (multipleEllipticGammaFaceParameters τ J)) := by
  letI : Nonempty (MultipleEllipticGammaFaceIndex J) := by
    obtain ⟨i, hi⟩ := hJ
    exact ⟨⟨i, by simpa using hi⟩⟩
  exact ⟨
    by
      simpa [multipleEllipticGammaFaceMero] using
        differentialAlgebraicOver_multipleEllipticGammaMero_iff_augmentedPeriodRank_eq_two
          (multipleEllipticGammaFaceParameters τ J) (fun i => hτ i),
    differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_augmentedPeriodRank_eq_two
      (multipleEllipticGammaFaceParameters τ J) (fun i => hτ i),
    by
      simpa [multipleEllipticGammaFaceMero] using
        hypertranscendentalOver_multipleEllipticGammaMero_iff_three_le_augmentedPeriodRank
          (multipleEllipticGammaFaceParameters τ J) (fun i => hτ i),
    hypertranscendentalOver_multipleEllipticGammaLogDerivMero_iff_three_le_augmentedPeriodRank
      (multipleEllipticGammaFaceParameters τ J) (fun i => hτ i)⟩

/-- **All-parameter period-rank dichotomy.** Every finite nonempty upper-half-plane period family
lies in exactly one of two phases. At augmented rank two, both the raw function and logarithmic
derivative are differentially algebraic; at augmented rank at least three, both are
hypertranscendental. -/
theorem multipleEllipticGamma_exactPeriodRankDichotomy
    [Nonempty ι] (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    (((multipleEllipticGammaAugmentedPeriodRank τ = 2) ∧
        DifferentialAlgebraicOver (RatFunc ℂ) (multipleEllipticGammaMero τ hτ) ∧
        DifferentialAlgebraicOver (RatFunc ℂ)
          (multipleEllipticGammaLogDerivMero τ hτ)) ∨
      ((3 ≤ multipleEllipticGammaAugmentedPeriodRank τ) ∧
        HypertranscendentalOver (RatFunc ℂ) (multipleEllipticGammaMero τ hτ) ∧
        HypertranscendentalOver (RatFunc ℂ)
          (multipleEllipticGammaLogDerivMero τ hτ))) ∧
      ¬ ((multipleEllipticGammaAugmentedPeriodRank τ = 2) ∧
          3 ≤ multipleEllipticGammaAugmentedPeriodRank τ) := by
  constructor
  · by_cases hminor : MultipleEllipticGammaHasRankThreeMinor τ
    · right
      exact ⟨
        rankThreeMinor_implies_three_le_augmentedPeriodRank τ hminor,
        (hypertranscendentalOver_multipleEllipticGammaMero_iff_rankThreeMinor
          τ hτ).2 hminor,
        (hypertranscendentalOver_multipleEllipticGammaLogDerivMero_iff_rankThreeMinor
          τ hτ).2 hminor⟩
    · left
      exact ⟨
        (augmentedPeriodRank_eq_two_iff_not_rankThreeMinor τ hτ).2 hminor,
        (differentialAlgebraicOver_multipleEllipticGammaMero_iff_not_rankThreeMinor
          τ hτ).2 hminor,
        (differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_iff_not_rankThreeMinor
          τ hτ).2 hminor⟩
  · omega

end

end GaloisForLFunctions
