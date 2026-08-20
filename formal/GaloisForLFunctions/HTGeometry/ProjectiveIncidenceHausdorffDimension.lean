import GaloisForLFunctions.HTGeometry.ComplexAffineAlgebraicStratificationFinite
import GaloisForLFunctions.HTGeometry.ExpandedEvaluationAlgebraicRankDefect
import GaloisForLFunctions.HTGeometry.ProjectiveAffineChartGlobalIncidenceDimension
import GaloisForLFunctions.HTGeometry.ProjectiveIncidenceProjection
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Hausdorff dimension of projected projective incidence

This module discharges the proper-projection and smooth-stratification interface used by the
expanded evaluation argument.  It flattens each affine projective chart to one complex polynomial
space, transfers the proved Krull bound to a finite regular stratification there, and projects the
chart by a smooth coordinate map.  The finite chart cover gives the Hausdorff-dimension bound for
the literal rank-defect locus.  Its already-proved affine algebraicity then upgrades a
zero-codimension stratification to the required positive codimension.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

theorem finrank_complex_pi
    {σ : Type*} [Fintype σ] :
    Module.finrank ℝ (σ → ℂ) = 2 * Fintype.card σ := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, Nat.mul_comm]

/-- Evaluation commutes with the equivalence between a polynomial ring on a sum and an iterated
polynomial ring. -/
private theorem eval_sumAlgEquiv
    {σ τ : Type*}
    (w : (σ ⊕ τ) → ℂ) (p : MvPolynomial (σ ⊕ τ) ℂ) :
    MvPolynomial.eval₂ (MvPolynomial.eval (w ∘ Sum.inr)) (w ∘ Sum.inl)
        (MvPolynomial.sumAlgEquiv ℂ σ τ p) =
      MvPolynomial.eval w p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simpa using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
      change MvPolynomial.eval₂ (MvPolynomial.eval (w ∘ Sum.inr)) (w ∘ Sum.inl)
          (MvPolynomial.sumAlgEquiv ℂ σ τ p) = MvPolynomial.eval w p at hp
      rcases i with i | i
      · simp [hp]
      · simp [hp]

/-- The single polynomial-coordinate type obtained by flattening packet and projective-chart
variables. -/
abbrev projectiveChartFlatVar
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (j : κ × Fin (q + 1)) :=
  (row × Fin n) ⊕ projectiveChartVar j

/-- The affine-chart incidence ideal transported to the flattened polynomial ring. -/
def projectiveChartFlatIncidenceIdeal
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ)) :
    Ideal (MvPolynomial (projectiveChartFlatVar (row := row) q n j) ℂ) :=
  (projectiveChartGlobalIncidenceIdeal q n z j exponent).comap
    (MvPolynomial.sumAlgEquiv ℂ (row × Fin n) (projectiveChartVar j)).toRingEquiv

/-- The complex zero locus of the flattened affine-chart incidence ideal. -/
def projectiveChartFlatIncidenceSet
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ)) :
    Set (projectiveChartFlatVar (row := row) q n j → ℂ) :=
  MvPolynomial.zeroLocus ℂ
    (projectiveChartFlatIncidenceIdeal q n z j exponent)

/-- Points of the flattened zero locus are exactly packet/chart incidence pairs. -/
theorem mem_projectiveChartFlatIncidenceSet_iff
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (w : projectiveChartFlatVar (row := row) q n j → ℂ) :
    w ∈ projectiveChartFlatIncidenceSet q n z j exponent ↔
      IsProjectiveChartIncidencePoint q n z j exponent
        (w ∘ Sum.inr) (w ∘ Sum.inl) := by
  let E := MvPolynomial.sumAlgEquiv ℂ (row × Fin n) (projectiveChartVar j)
  let evNested : MvPolynomial (row × Fin n) (projectiveChartCoefficientRing j) →+* ℂ :=
    MvPolynomial.eval₂Hom (MvPolynomial.eval (w ∘ Sum.inr)) (w ∘ Sum.inl)
  rw [projectiveChartFlatIncidenceSet, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro hw b
    let p := E.symm (projectiveChartGlobalRowPolynomial q n z j exponent b)
    have hp : p ∈ projectiveChartFlatIncidenceIdeal q n z j exponent := by
      change E p ∈ projectiveChartGlobalIncidenceIdeal q n z j exponent
      rw [E.apply_symm_apply]
      exact Ideal.subset_span (Set.mem_range_self b)
    have hwp := hw p hp
    have heval := eval_sumAlgEquiv w p
    change evNested (E p) = MvPolynomial.eval w p at heval
    rw [E.apply_symm_apply] at heval
    exact heval.trans hwp
  · intro hpoint p hp
    change E p ∈ projectiveChartGlobalIncidenceIdeal q n z j exponent at hp
    have hgen : projectiveChartGlobalIncidenceIdeal q n z j exponent ≤
        RingHom.ker evNested := by
      rw [projectiveChartGlobalIncidenceIdeal, Ideal.span_le]
      rintro _ ⟨b, rfl⟩
      exact RingHom.mem_ker.mpr (hpoint b)
    have hz : evNested (E p) = 0 := RingHom.mem_ker.mp (hgen hp)
    have heval := eval_sumAlgEquiv w p
    change evNested (E p) = MvPolynomial.eval w p at heval
    exact heval ▸ hz

theorem projectiveChartFlatIncidenceIdeal_map_sumAlgEquiv
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ)) :
    (projectiveChartFlatIncidenceIdeal q n z j exponent).map
        (MvPolynomial.sumAlgEquiv ℂ (row × Fin n) (projectiveChartVar j)).toRingEquiv =
      projectiveChartGlobalIncidenceIdeal q n z j exponent := by
  unfold projectiveChartFlatIncidenceIdeal
  exact Ideal.map_comap_eq_self_of_equiv
    (MvPolynomial.sumAlgEquiv ℂ (row × Fin n) (projectiveChartVar j)).toRingEquiv _

/-- Flattening the iterated incidence ring preserves its Krull dimension. -/
theorem ringKrullDim_projectiveChartFlatIncidenceRing
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ)) :
    ringKrullDim
        (MvPolynomial (projectiveChartFlatVar (row := row) q n j) ℂ ⧸
          projectiveChartFlatIncidenceIdeal q n z j exponent) =
      ringKrullDim (projectiveChartGlobalIncidenceRing q n z j exponent) := by
  let E := MvPolynomial.sumAlgEquiv ℂ (row × Fin n) (projectiveChartVar j)
  let Q := Ideal.quotientEquiv
    (projectiveChartFlatIncidenceIdeal q n z j exponent)
    (projectiveChartGlobalIncidenceIdeal q n z j exponent)
    E.toRingEquiv
    (projectiveChartFlatIncidenceIdeal_map_sumAlgEquiv q n z j exponent).symm
  exact Q.ringKrullDim

/-- A chart Krull bound gives a finite regular stratification of the flattened incidence set.
The chart-coordinate dimension is added to the packet codimension because it is eliminated by the
subsequent projection. -/
theorem projectiveChartFlatIncidenceSet_finiteRegularStratification_of_krullDim
    {row κ : Type} [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
    (q n c : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (hchart : ringKrullDim (projectiveChartGlobalIncidenceRing q n z j exponent) +
        (c : WithBot ℕ∞) ≤ (Fintype.card row * n : ℕ)) :
    Nonempty (FiniteRegularStratification
      (projectiveChartFlatIncidenceSet q n z j exponent)
      (2 * (c + Fintype.card (projectiveChartVar j)))) := by
  let k := Fintype.card (projectiveChartVar j)
  let I := projectiveChartFlatIncidenceIdeal q n z j exponent
  let S := projectiveChartFlatIncidenceSet q n z j exponent
  have hS : IsComplexAffineAlgebraicSet S := by
    exact ⟨I, rfl⟩
  have hIJ : I ≤ MvPolynomial.vanishingIdeal ℂ S := by
    exact MvPolynomial.le_vanishingIdeal_zeroLocus I
  have hdim_mono :
      ringKrullDim
          (MvPolynomial (projectiveChartFlatVar (row := row) q n j) ℂ ⧸
            MvPolynomial.vanishingIdeal ℂ S) ≤
        ringKrullDim
          (MvPolynomial (projectiveChartFlatVar (row := row) q n j) ℂ ⧸ I) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hIJ)
      (Ideal.Quotient.factor_surjective hIJ)
  have hchartFlat :
      ringKrullDim
          (MvPolynomial (projectiveChartFlatVar (row := row) q n j) ℂ ⧸ I) +
          (c : WithBot ℕ∞) ≤
        (Fintype.card row * n : ℕ) := by
    rw [ringKrullDim_projectiveChartFlatIncidenceRing]
    exact hchart
  have hdim :
      ringKrullDim
          (MvPolynomial (projectiveChartFlatVar (row := row) q n j) ℂ ⧸
            MvPolynomial.vanishingIdeal ℂ S) + (c + k : ℕ) ≤
        (Fintype.card (projectiveChartFlatVar (row := row) q n j) : ℕ) := by
    have hcard : Fintype.card (projectiveChartFlatVar (row := row) q n j) =
        Fintype.card row * n + k := by
      simp [projectiveChartFlatVar, k]
    rw [hcard]
    calc
      _ ≤ ringKrullDim
            (MvPolynomial (projectiveChartFlatVar (row := row) q n j) ℂ ⧸ I) +
            (c + k : ℕ) := by
              simpa [add_comm] using
                add_le_add_right hdim_mono ((c + k : ℕ) : WithBot ℕ∞)
      _ = (ringKrullDim
            (MvPolynomial (projectiveChartFlatVar (row := row) q n j) ℂ ⧸ I) + c) + k := by
              push_cast
              ac_rfl
      _ ≤ (Fintype.card row * n : ℕ) + k := by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right hchartFlat (k : WithBot ℕ∞)
      _ = ((Fintype.card row * n + k : ℕ) : WithBot ℕ∞) := by push_cast; rfl
  simpa only [S, k] using
    complexAffineAlgebraicSet_finiteRegularStratification_of_krullDim S hS hdim

/-- The chart Krull bound implies the expected real Hausdorff-dimension bound on the flattened
incidence variety. -/
theorem dimH_projectiveChartFlatIncidenceSet_le_of_krullDim
    {row κ : Type} [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
    (q n c : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (hchart : ringKrullDim (projectiveChartGlobalIncidenceRing q n z j exponent) +
        (c : WithBot ℕ∞) ≤ (Fintype.card row * n : ℕ)) :
    dimH (projectiveChartFlatIncidenceSet q n z j exponent) ≤
      (2 * (Fintype.card row * n - c) : ℕ) := by
  let k := Fintype.card (projectiveChartVar j)
  obtain ⟨strata⟩ :=
    projectiveChartFlatIncidenceSet_finiteRegularStratification_of_krullDim
      q n c z j exponent hchart
  calc
    dimH (projectiveChartFlatIncidenceSet q n z j exponent) ≤
        (Module.finrank ℝ (projectiveChartFlatVar (row := row) q n j → ℂ) -
          2 * (c + k) : ℕ) := strata.dimH_le_finrank_sub
    _ = (2 * (Fintype.card row * n - c) : ℕ) := by
      congr 1
      rw [finrank_complex_pi]
      simp only [projectiveChartFlatVar, Fintype.card_sum, Fintype.card_prod,
        Fintype.card_fin]
      omega

/-- Forget the projective-chart coordinates and retain the packet coordinates. -/
def projectiveChartFlatPacketProjection
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (j : κ × Fin (q + 1))
    (w : projectiveChartFlatVar (row := row) q n j → ℂ) :
    row × Fin n → ℂ :=
  w ∘ Sum.inl

/-- The image of the flattened chart incidence set is the literal chart incidence projection. -/
theorem projectiveChartFlatPacketProjection_image
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ)) :
    projectiveChartFlatPacketProjection q n j ''
        projectiveChartFlatIncidenceSet q n z j exponent =
      {y | ∃ x : projectiveChartVar j → ℂ,
        IsProjectiveChartIncidencePoint q n z j exponent x y} := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w ∘ Sum.inr,
      (mem_projectiveChartFlatIncidenceSet_iff q n z j exponent w).mp hw⟩
  · rintro ⟨x, hx⟩
    let w : projectiveChartFlatVar (row := row) q n j → ℂ := Sum.elim y x
    refine ⟨w, ?_, ?_⟩
    · apply (mem_projectiveChartFlatIncidenceSet_iff q n z j exponent w).mpr
      simpa only [w, Function.comp_def, Sum.elim_inr, Sum.elim_inl] using hx
    · funext i
      rfl

/-- Smooth coordinate projection cannot increase the Hausdorff dimension of one affine chart. -/
theorem dimH_projectiveChartIncidenceProjection_le_of_krullDim
    {row κ : Type} [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
    (q n c : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (hchart : ringKrullDim (projectiveChartGlobalIncidenceRing q n z j exponent) +
        (c : WithBot ℕ∞) ≤ (Fintype.card row * n : ℕ)) :
    dimH {y | ∃ x : projectiveChartVar j → ℂ,
        IsProjectiveChartIncidencePoint q n z j exponent x y} ≤
      (2 * (Fintype.card row * n - c) : ℕ) := by
  let f := projectiveChartFlatPacketProjection (row := row) q n j
  have hf : ContDiff ℝ 1 f := by
    apply contDiff_pi'
    intro i
    exact contDiff_apply ℝ ℂ (Sum.inl i)
  rw [← projectiveChartFlatPacketProjection_image q n z j exponent]
  exact (hf.contDiffOn.dimH_image_le convex_univ (subset_univ _)).trans
    (dimH_projectiveChartFlatIncidenceSet_le_of_krullDim
      q n c z j exponent hchart)

/-- The finite standard projective-chart cover preserves the uniform Hausdorff-dimension bound. -/
theorem dimH_projectiveChartIncidenceProjection_union_le_of_krullDim
    {row κ : Type} [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
    (q n c : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (hcharts : ∀ j : κ × Fin (q + 1),
      ringKrullDim (projectiveChartGlobalIncidenceRing q n z j exponent) +
        (c : WithBot ℕ∞) ≤ (Fintype.card row * n : ℕ)) :
    dimH (projectiveChartIncidenceProjection q n z exponent) ≤
      (2 * (Fintype.card row * n - c) : ℕ) := by
  have hset : projectiveChartIncidenceProjection q n z exponent =
      ⋃ j : κ × Fin (q + 1),
        {y | ∃ x : projectiveChartVar j → ℂ,
          IsProjectiveChartIncidencePoint q n z j exponent x y} := by
    ext y
    simp only [projectiveChartIncidenceProjection, mem_setOf_eq, mem_iUnion]
  rw [hset, dimH_iUnion]
  exact iSup_le fun j =>
    dimH_projectiveChartIncidenceProjection_le_of_krullDim
      q n c z j exponent (hcharts j)

/-- **Projected incidence stratification from chart Krull bounds.**

This is the unconditional replacement for the former proper-projection/Whitney input.  When the
claimed codimension exceeds packet dimension, the chart stratifications force every incidence
chart to be empty; otherwise the global Hausdorff bound upgrades the target's algebraic
stratification. -/
noncomputable def projectiveChartIncidenceProjection_finiteRegularStratification_of_krullDim
    {row κ : Type}
    [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ)) (c : ℕ)
    (hcharts : ∀ j : κ × Fin (q + 1),
      ringKrullDim (projectiveChartGlobalIncidenceRing q n z j exponent) +
        (c : WithBot ℕ∞) ≤ (Fintype.card row * n : ℕ)) :
    FiniteRegularStratification
      (projectiveChartIncidenceProjection q n z exponent) (2 * c) := by
  by_cases hc : 2 * c ≤ Module.finrank ℝ (row × Fin n → ℂ)
  · have hbad : IsComplexAffineAlgebraicSet
        (projectiveChartIncidenceProjection q n z exponent) := by
      rw [← expandedDifferentialEvaluationRankDefect_eq_projectiveChartIncidenceProjection]
      exact isComplexAffineAlgebraicSet_expandedDifferentialEvaluationRankDefect
        q n z exponent
    let strata := Classical.choice
      (complexAffineAlgebraicSet_finiteRegularStratification_zero
        (projectiveChartIncidenceProjection q n z exponent) hbad)
    apply strata.of_dimH_le hc
    calc
      dimH (projectiveChartIncidenceProjection q n z exponent) ≤
          (2 * (Fintype.card row * n - c) : ℕ) :=
        dimH_projectiveChartIncidenceProjection_union_le_of_krullDim
          q n c z exponent hcharts
      _ = (Module.finrank ℝ (row × Fin n → ℂ) - 2 * c : ℕ) := by
        congr 1
        rw [finrank_complex_pi]
        simp only [Fintype.card_prod, Fintype.card_fin]
        omega
  · have htarget : Module.finrank ℝ (row × Fin n → ℂ) < 2 * c :=
      Nat.lt_of_not_ge hc
    have hempty : projectiveChartIncidenceProjection q n z exponent = ∅ := by
      ext y
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨j, x, hincidence⟩
      let w : projectiveChartFlatVar (row := row) q n j → ℂ := Sum.elim y x
      have hw : w ∈ projectiveChartFlatIncidenceSet q n z j exponent := by
        apply (mem_projectiveChartFlatIncidenceSet_iff q n z j exponent w).mpr
        simpa only [w, Function.comp_def, Sum.elim_inr, Sum.elim_inl] using hincidence
      obtain ⟨strata⟩ :=
        projectiveChartFlatIncidenceSet_finiteRegularStratification_of_krullDim
          q n c z j exponent (hcharts j)
      have hsource : Module.finrank ℝ (projectiveChartFlatVar (row := row) q n j → ℂ) <
          2 * (c + Fintype.card (projectiveChartVar j)) := by
        rw [finrank_complex_pi] at htarget ⊢
        simp only [projectiveChartFlatVar, Fintype.card_sum, Fintype.card_prod,
          Fintype.card_fin] at htarget ⊢
        omega
      have hsourceEmpty := strata.eq_empty_of_finrank_lt_codim hsource
      rw [hsourceEmpty] at hw
      exact hw
    rw [hempty]
    apply finiteRegularStratification_of_regular
    intro y hy
    simp at hy

/-- The project's proved chart bound gives the expanded rank defect its exact real codimension,
without any classical input structure. -/
noncomputable def expandedDifferentialEvaluationRankDefect_finiteRegularStratification_unconditional
    {row κ : Type}
    [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (q + 1)) + q < Fintype.card row) :
    FiniteRegularStratification
      (expandedDifferentialEvaluationRankDefect q n z exponent)
      (2 * (Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1)) := by
  let c := Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1
  rw [expandedDifferentialEvaluationRankDefect_eq_projectiveChartIncidenceProjection]
  exact projectiveChartIncidenceProjection_finiteRegularStratification_of_krullDim
    q n z exponent c (fun j =>
      projectiveChartGlobalIncidenceRing_evaluationCodimension
        q n z hz j exponent hexponent hrows)

end

end GaloisForLFunctions.HTGeometry
