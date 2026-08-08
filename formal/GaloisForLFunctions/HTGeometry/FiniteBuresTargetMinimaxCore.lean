import GaloisForLFunctions.HTGeometry.ReturnExcisedOptimalDesignCoareaLaw
import GaloisForLFunctions.HTGeometry.ComplexIntegralGram
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder
import Mathlib.Topology.Sion

/-!
# Finite Bures target minimax core

This module proves the exact finite-target Sion exchange behind complete-incidence
Bures geometry. The target-law simplex is compact; the positive-definite reporter
cone is deliberately left noncompact. Rank-one occupied rays, their convex
mixtures, operator-convex inversion, all order bounds, and the concrete maximum
over occupied targets are derived without full-rank assumptions.
-/

open Filter MeasureTheory Matrix Set
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def finiteBuresTargetRay {n : ℕ} (v : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vecMulVec v (star v)

def finiteBuresTargetMixture {C : Type*} [Fintype C] {n : ℕ}
    (p : C → ℝ) (target : C → Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ c, p c • finiteBuresTargetRay (target c)

def finiteBuresSourcePairing {n : ℕ}
    (C A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ((C * A).trace).re

def finiteBuresTargetPairing {n : ℕ}
    (M A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ((M * A⁻¹).trace).re

def finiteBuresTargetLeverage {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℝ :=
  (star v ⬝ᵥ (A⁻¹ *ᵥ v)).re

def finiteBuresSaddleValue {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) (p : C → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (finiteBuresSourcePairing source A + ∑ c, p c * finiteBuresTargetLeverage A (target c)) / 2

theorem finiteBuresTargetRay_posSemidef {n : ℕ} (v : Fin n → ℂ) :
    (finiteBuresTargetRay v).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star v

theorem finiteBuresTargetMixture_posSemidef
    {C : Type*} [Fintype C] {n : ℕ}
    {p : C → ℝ} (hp : p ∈ stdSimplex ℝ C)
    (target : C → Fin n → ℂ) :
    (finiteBuresTargetMixture p target).PosSemidef := by
  classical
  unfold finiteBuresTargetMixture
  apply Matrix.posSemidef_sum Finset.univ
  intro c _
  exact (finiteBuresTargetRay_posSemidef (target c)).smul (hp.1 c)

theorem continuous_finiteBuresTargetMixture
    {C : Type*} [Fintype C] {n : ℕ}
    (target : C → Fin n → ℂ) :
    Continuous (fun p : C → ℝ => finiteBuresTargetMixture p target) := by
  unfold finiteBuresTargetMixture
  fun_prop

theorem finiteBuresTargetRay_pairing_eq_leverage
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    finiteBuresTargetPairing (finiteBuresTargetRay v) A = finiteBuresTargetLeverage A v := by
  unfold finiteBuresTargetPairing finiteBuresTargetRay finiteBuresTargetLeverage
  rw [Matrix.trace_mul_comm]
  apply congrArg Complex.re
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Pi.star_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem finiteBuresTargetMixture_pairing_eq_average
    {C : Type*} [Fintype C] {n : ℕ}
    (p : C → ℝ) (target : C → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    finiteBuresTargetPairing (finiteBuresTargetMixture p target) A =
      ∑ c, p c * finiteBuresTargetLeverage A (target c) := by
  classical
  unfold finiteBuresTargetPairing finiteBuresTargetMixture
  rw [Matrix.sum_mul, Matrix.trace_sum]
  simp_rw [Matrix.smul_mul, Matrix.trace_smul]
  rw [Complex.re_sum]
  simp only [Complex.smul_re, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro c _
  have hr := finiteBuresTargetRay_pairing_eq_leverage A (target c)
  unfold finiteBuresTargetPairing at hr
  rw [hr]

theorem finiteBuresSaddleValue_eq_halfSum_mixture
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) (p : C → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    finiteBuresSaddleValue source target p A =
      (finiteBuresSourcePairing source A + finiteBuresTargetPairing (finiteBuresTargetMixture p target) A) / 2 := by
  rw [finiteBuresSaddleValue, finiteBuresTargetMixture_pairing_eq_average]

theorem finiteBuresConvex_posDefMatrices {n : ℕ} :
    Convex ℝ {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef} := by
  intro A hA B hB a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hB
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hA
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbPos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  exact (hA.smul haPos).add (hB.smul hbPos)

theorem finiteBuresRe_trace_mul_mono_of_posSemidef
    {n : ℕ} {M X Y : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.PosSemidef) (hXY : X ≤ Y) :
    ((M * X).trace).re ≤ ((M * Y).trace).re := by
  have hdiff : (Y - X).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hXY)
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hdiff.nonneg
  have hfactor : Y - X = D.conjTranspose * D := by
    simpa only [Matrix.star_eq_conjTranspose] using hD
  have hPSD : (D * M * D.conjTranspose).PosSemidef :=
    hM.mul_mul_conjTranspose_same D
  have htrace : 0 ≤ (D * M * D.conjTranspose).trace := hPSD.trace_nonneg
  have hre : 0 ≤ ((D * M * D.conjTranspose).trace).re :=
    (RCLike.nonneg_iff.mp htrace).1
  have heq :
      (M * (Y - X)).trace = (D * M * D.conjTranspose).trace := by
    rw [hfactor, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have hreEq := congrArg Complex.re heq
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hreEq
  linarith

theorem finiteBuresConvexOn_targetPairing
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.PosSemidef) :
    ConvexOn ℝ {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef}
      (finiteBuresTargetPairing M) := by
  letI : CStarAlgebra (Matrix (Fin n) (Fin n) ℂ) := {}
  refine ⟨finiteBuresConvex_posDefMatrices, ?_⟩
  intro A hA B hB a b ha hb hab
  have hInv := CStarAlgebra.convexOn_ringInverse.2
    hA.isStrictlyPositive hB.isStrictlyPositive ha hb hab
  rw [← Matrix.nonsing_inv_eq_ringInverse,
    ← Matrix.nonsing_inv_eq_ringInverse,
    ← Matrix.nonsing_inv_eq_ringInverse] at hInv
  have hmono := finiteBuresRe_trace_mul_mono_of_posSemidef hM hInv
  unfold finiteBuresTargetPairing
  simpa [Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_smul, Complex.add_re] using hmono

theorem finiteBuresConvexOn_sourcePairing
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ) :
    ConvexOn ℝ {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef}
      (finiteBuresSourcePairing source) := by
  refine ⟨finiteBuresConvex_posDefMatrices, ?_⟩
  intro A _ B _ a b _ _ _
  unfold finiteBuresSourcePairing
  simp [Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_smul, Complex.add_re]

theorem finiteBuresConvexOn_saddleValue_right
    {C : Type*} [Fintype C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ}
    {target : C → Fin n → ℂ} {p : C → ℝ}
    (hp : p ∈ stdSimplex ℝ C) :
    ConvexOn ℝ {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef}
      (finiteBuresSaddleValue source target p) := by
  rw [show finiteBuresSaddleValue source target p = fun A =>
      (finiteBuresSourcePairing source A + finiteBuresTargetPairing (finiteBuresTargetMixture p target) A) / 2 by
    funext A
    exact finiteBuresSaddleValue_eq_halfSum_mixture source target p A]
  have hs := finiteBuresConvexOn_sourcePairing source
  have ht := finiteBuresConvexOn_targetPairing (finiteBuresTargetMixture_posSemidef hp target)
  refine ⟨finiteBuresConvex_posDefMatrices, ?_⟩
  intro A hA B hB a b ha hb hab
  have hs' := hs.2 hA hB ha hb hab
  have ht' := ht.2 hA hB ha hb hab
  simp only [smul_eq_mul] at hs' ht' ⊢
  linarith

theorem finiteBuresAffine_saddleValue_left
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ∀ p q : C → ℝ, ∀ a b : ℝ, a + b = 1 →
      finiteBuresSaddleValue source target (a • p + b • q) A =
        a * finiteBuresSaddleValue source target p A +
          b * finiteBuresSaddleValue source target q A := by
  classical
  intro p q a b hab
  unfold finiteBuresSaddleValue
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsum :
      (∑ x, (a * p x + b * q x) * finiteBuresTargetLeverage A (target x)) =
        a * (∑ x, p x * finiteBuresTargetLeverage A (target x)) +
          b * (∑ x, q x * finiteBuresTargetLeverage A (target x)) := by
    calc
      (∑ x, (a * p x + b * q x) * finiteBuresTargetLeverage A (target x)) =
          ∑ x, (a * (p x * finiteBuresTargetLeverage A (target x)) +
            b * (q x * finiteBuresTargetLeverage A (target x))) := by
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = (∑ x, a * (p x * finiteBuresTargetLeverage A (target x))) +
          ∑ x, b * (q x * finiteBuresTargetLeverage A (target x)) :=
        Finset.sum_add_distrib
      _ = a * (∑ x, p x * finiteBuresTargetLeverage A (target x)) +
          b * (∑ x, q x * finiteBuresTargetLeverage A (target x)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
  rw [hsum]
  have hsource : finiteBuresSourcePairing source A =
      a * finiteBuresSourcePairing source A + b * finiteBuresSourcePairing source A := by
    calc
      finiteBuresSourcePairing source A = (a + b) * finiteBuresSourcePairing source A := by rw [hab]; simp
      _ = a * finiteBuresSourcePairing source A + b * finiteBuresSourcePairing source A := by ring
  linear_combination hsource / 2

theorem finiteBuresConvexOn_saddleValue_left
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ConvexOn ℝ (stdSimplex ℝ C)
      (fun p => finiteBuresSaddleValue source target p A) := by
  refine ⟨convex_stdSimplex ℝ C, ?_⟩
  intro p _ q _ a b ha hb hab
  simpa [smul_eq_mul] using
    (finiteBuresAffine_saddleValue_left source target A p q a b hab).le

theorem finiteBuresConcaveOn_saddleValue_left
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ConcaveOn ℝ (stdSimplex ℝ C)
      (fun p => finiteBuresSaddleValue source target p A) := by
  refine ⟨convex_stdSimplex ℝ C, ?_⟩
  intro p _ q _ a b ha hb hab
  simpa [smul_eq_mul] using
    (finiteBuresAffine_saddleValue_left source target A p q a b hab).ge

theorem finiteBuresContinuous_saddleValue_left
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun p : C → ℝ => finiteBuresSaddleValue source target p A) := by
  unfold finiteBuresSaddleValue
  fun_prop

theorem finiteBuresContinuousWithinAt_matrix_inv_of_posDef
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ContinuousWithinAt (fun B : Matrix (Fin n) (Fin n) ℂ => B⁻¹)
      {B : Matrix (Fin n) (Fin n) ℂ | B.PosDef} A := by
  have hdetUnit : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hdet : A.det ≠ 0 := isUnit_iff_ne_zero.mp hdetUnit
  have hscalar : ContinuousAt Ring.inverse A.det := by
    rw [show Ring.inverse = Inv.inv from
      funext fun z : ℂ => Ring.inverse_eq_inv z]
    exact continuousAt_inv₀ hdet
  exact (continuousAt_matrix_inv A hscalar).continuousWithinAt

theorem finiteBuresContinuous_sourcePairing
    {n : ℕ} (source : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (finiteBuresSourcePairing source) := by
  change Continuous (fun A : Matrix (Fin n) (Fin n) ℂ =>
    ((source * A).trace).re)
  have hmul : Continuous
      (fun A : Matrix (Fin n) (Fin n) ℂ => source * A) :=
    continuous_const.matrix_mul continuous_id
  have htrace : Continuous
      (fun A : Matrix (Fin n) (Fin n) ℂ => (source * A).trace) :=
    hmul.matrix_trace
  exact Complex.continuous_re.comp htrace

theorem finiteBuresContinuousOn_targetPairing
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ContinuousOn (finiteBuresTargetPairing M)
      {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef} := by
  let S : Set (Matrix (Fin n) (Fin n) ℂ) := {A | A.PosDef}
  change ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ =>
    ((M * A⁻¹).trace).re) S
  have hInv : ContinuousOn
      (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) S := by
    intro A hA
    exact finiteBuresContinuousWithinAt_matrix_inv_of_posDef hA
  have hPair := finiteBuresContinuous_sourcePairing M
  have hcomp := hPair.comp_continuousOn hInv
  exact hcomp

theorem finiteBuresContinuousOn_saddleValue_right
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) (p : C → ℝ) :
    ContinuousOn (finiteBuresSaddleValue source target p)
      {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef} := by
  rw [show finiteBuresSaddleValue source target p = fun A =>
      (finiteBuresSourcePairing source A + finiteBuresTargetPairing (finiteBuresTargetMixture p target) A) / 2 by
    funext A
    exact finiteBuresSaddleValue_eq_halfSum_mixture source target p A]
  exact ((finiteBuresContinuous_sourcePairing source).continuousOn.add
    (finiteBuresContinuousOn_targetPairing (finiteBuresTargetMixture p target))).div_const 2

theorem finiteBuresSourcePairing_nonneg
    {n : ℕ} {source A : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef) (hA : A.PosDef) :
    0 ≤ finiteBuresSourcePairing source A := by
  have hzeroA : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ A :=
    Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  have hmono := finiteBuresRe_trace_mul_mono_of_posSemidef hsource hzeroA
  simpa [finiteBuresSourcePairing] using hmono

theorem finiteBuresTargetLeverage_nonneg
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (v : Fin n → ℂ) :
    0 ≤ finiteBuresTargetLeverage A v := by
  exact hA.inv.posSemidef.re_dotProduct_nonneg v

theorem finiteBuresSaddleValue_nonneg
    {C : Type*} [Fintype C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    {target : C → Fin n → ℂ} {p : C → ℝ}
    (hp : p ∈ stdSimplex ℝ C)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    0 ≤ finiteBuresSaddleValue source target p A := by
  have hsum : 0 ≤ ∑ c, p c * finiteBuresTargetLeverage A (target c) :=
    Finset.sum_nonneg fun c _ =>
      mul_nonneg (hp.1 c) (finiteBuresTargetLeverage_nonneg hA (target c))
  unfold finiteBuresSaddleValue
  exact div_nonneg (add_nonneg (finiteBuresSourcePairing_nonneg hsource hA) hsum)
    (by norm_num)

def finiteBuresReporterValueSet
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) (p : C → ℝ) : Set ℝ :=
  {q | ∃ A : Matrix (Fin n) (Fin n) ℂ,
    A.PosDef ∧ q = finiteBuresSaddleValue source target p A}

def finiteBuresMixtureValue
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) (p : C → ℝ) : ℝ :=
  sInf (finiteBuresReporterValueSet source target p)

def finiteBuresMixtureValueSet
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) : Set ℝ :=
  {q | ∃ p ∈ stdSimplex ℝ C, q = finiteBuresMixtureValue source target p}

def finiteBuresDualCapacity
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) : ℝ :=
  sSup (finiteBuresMixtureValueSet source target)

def finiteBuresSimplexValueSet
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) : Set ℝ :=
  {q | ∃ p ∈ stdSimplex ℝ C, q = finiteBuresSaddleValue source target p A}

def finiteBuresReporterWorstValue
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup (finiteBuresSimplexValueSet source target A)

def finiteBuresReporterWorstValueSet
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) : Set ℝ :=
  {q | ∃ A : Matrix (Fin n) (Fin n) ℂ,
    A.PosDef ∧ q = finiteBuresReporterWorstValue source target A}

def finiteBuresPrimalCapacity
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) : ℝ :=
  sInf (finiteBuresReporterWorstValueSet source target)

theorem finiteBuresReporterValueSet_nonempty
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) (p : C → ℝ) :
    (finiteBuresReporterValueSet source target p).Nonempty := by
  exact ⟨finiteBuresSaddleValue source target p 1, 1, Matrix.PosDef.one, rfl⟩

theorem finiteBuresReporterValueSet_bddBelow
    {C : Type*} [Fintype C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) {p : C → ℝ}
    (hp : p ∈ stdSimplex ℝ C) :
    BddBelow (finiteBuresReporterValueSet source target p) := by
  refine ⟨0, ?_⟩
  rintro q ⟨A, hA, rfl⟩
  exact finiteBuresSaddleValue_nonneg hsource hp hA

theorem finiteBuresMixtureValueSet_nonempty
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) :
    (finiteBuresMixtureValueSet source target).Nonempty := by
  classical
  let c : C := Classical.choice inferInstance
  exact ⟨finiteBuresMixtureValue source target (Pi.single c 1),
    Pi.single c 1, single_mem_stdSimplex ℝ c, rfl⟩

theorem finiteBuresMixtureValueSet_bddAbove
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    BddAbove (finiteBuresMixtureValueSet source target) := by
  have hcompact : IsCompact (stdSimplex ℝ C) := isCompact_stdSimplex ℝ C
  have hcontinuous : ContinuousOn
      (fun p : C → ℝ => finiteBuresSaddleValue source target p 1)
      (stdSimplex ℝ C) :=
    (finiteBuresContinuous_saddleValue_left source target 1).continuousOn
  obtain ⟨K, hK⟩ := hcompact.bddAbove_image hcontinuous
  refine ⟨K, ?_⟩
  rintro q ⟨p, hp, rfl⟩
  calc
    finiteBuresMixtureValue source target p ≤ finiteBuresSaddleValue source target p 1 := by
      unfold finiteBuresMixtureValue
      exact csInf_le (finiteBuresReporterValueSet_bddBelow hsource target hp)
        ⟨1, Matrix.PosDef.one, rfl⟩
    _ ≤ K := hK ⟨p, hp, rfl⟩

theorem finiteBuresSimplexValueSet_nonempty
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (finiteBuresSimplexValueSet source target A).Nonempty := by
  classical
  let c : C := Classical.choice inferInstance
  exact ⟨finiteBuresSaddleValue source target (Pi.single c 1) A,
    Pi.single c 1, single_mem_stdSimplex ℝ c, rfl⟩

theorem finiteBuresSimplexValueSet_bddAbove
    {C : Type*} [Fintype C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    BddAbove (finiteBuresSimplexValueSet source target A) := by
  have hcompact : IsCompact (stdSimplex ℝ C) := isCompact_stdSimplex ℝ C
  have hcontinuous : ContinuousOn
      (fun p : C → ℝ => finiteBuresSaddleValue source target p A)
      (stdSimplex ℝ C) :=
    (finiteBuresContinuous_saddleValue_left source target A).continuousOn
  obtain ⟨K, hK⟩ := hcompact.bddAbove_image hcontinuous
  refine ⟨K, ?_⟩
  rintro q ⟨p, hp, rfl⟩
  exact hK ⟨p, hp, rfl⟩

theorem finiteBuresReporterWorstValueSet_nonempty
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) :
    (finiteBuresReporterWorstValueSet source target).Nonempty := by
  exact ⟨finiteBuresReporterWorstValue source target 1,
    1, Matrix.PosDef.one, rfl⟩

theorem finiteBuresReporterWorstValueSet_bddBelow
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    BddBelow (finiteBuresReporterWorstValueSet source target) := by
  classical
  let c : C := Classical.choice inferInstance
  let p : C → ℝ := Pi.single c 1
  have hp : p ∈ stdSimplex ℝ C := single_mem_stdSimplex ℝ c
  refine ⟨0, ?_⟩
  rintro q ⟨A, hA, rfl⟩
  unfold finiteBuresReporterWorstValue
  calc
    0 ≤ finiteBuresSaddleValue source target p A :=
      finiteBuresSaddleValue_nonneg hsource hp hA
    _ ≤ sSup (finiteBuresSimplexValueSet source target A) :=
      le_csSup (finiteBuresSimplexValueSet_bddAbove source target A)
        ⟨p, hp, rfl⟩

theorem finiteBuresIsLUB_neg_functionValues_of_isGLB
    {X : Type*} {S : Set X} {g : X → ℝ} {a : ℝ}
    (h : IsGLB {q : ℝ | ∃ x ∈ S, g x = q} a) :
    IsLUB {q : ℝ | ∃ x ∈ S, -g x = q} (-a) := by
  constructor
  · rintro q ⟨x, hx, rfl⟩
    exact neg_le_neg (h.1 ⟨x, hx, rfl⟩)
  · intro b hb
    have hlow : -b ∈ lowerBounds {q : ℝ | ∃ x ∈ S, g x = q} := by
      rintro q ⟨x, hx, rfl⟩
      have hbx : -g x ≤ b := hb ⟨x, hx, rfl⟩
      linarith
    have hab := h.2 hlow
    linarith

theorem finiteBuresIsGLB_neg_functionValues_of_isLUB
    {X : Type*} {S : Set X} {g : X → ℝ} {a : ℝ}
    (h : IsLUB {q : ℝ | ∃ x ∈ S, g x = q} a) :
    IsGLB {q : ℝ | ∃ x ∈ S, -g x = q} (-a) := by
  constructor
  · rintro q ⟨x, hx, rfl⟩
    exact neg_le_neg (h.1 ⟨x, hx, rfl⟩)
  · intro b hb
    have hupp : -b ∈ upperBounds {q : ℝ | ∃ x ∈ S, g x = q} := by
      rintro q ⟨x, hx, rfl⟩
      have hbx : b ≤ -g x := hb ⟨x, hx, rfl⟩
      linarith
    have hab := h.2 hupp
    linarith

/-- Sion exchange for the additive source--target reporter problem.  The
positive-reporter side is noncompact; only the finite probability simplex is
compact. -/
theorem finiteBuresPrimalCapacity_eq_dualCapacity
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ}
    (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    finiteBuresPrimalCapacity source target = finiteBuresDualCapacity source target := by
  classical
  let X : Set (C → ℝ) := stdSimplex ℝ C
  let Y : Set (Matrix (Fin n) (Fin n) ℂ) := {A | A.PosDef}
  let f : (C → ℝ) → Matrix (Fin n) (Fin n) ℂ → ℝ :=
    fun p A => -finiteBuresSaddleValue source target p A
  have hXne : X.Nonempty := by
    let c : C := Classical.choice inferInstance
    exact ⟨Pi.single c 1, single_mem_stdSimplex ℝ c⟩
  have hXcompact : IsCompact X := isCompact_stdSimplex ℝ C
  have hXconvex : Convex ℝ X := convex_stdSimplex ℝ C
  have hYconvex : Convex ℝ Y := finiteBuresConvex_posDefMatrices
  have hfy : ∀ A ∈ Y,
      LowerSemicontinuousOn (fun p : C → ℝ => f p A) X := by
    intro A hA
    have hcont : ContinuousOn
        (fun p : C → ℝ => -finiteBuresSaddleValue source target p A) X :=
      (finiteBuresContinuous_saddleValue_left source target A).neg.continuousOn
    exact hcont.lowerSemicontinuousOn
  have hfy' : ∀ A ∈ Y,
      QuasiconvexOn ℝ X (fun p : C → ℝ => f p A) := by
    intro A hA
    exact (finiteBuresConcaveOn_saddleValue_left source target A).neg.quasiconvexOn
  have hfx : ∀ p ∈ X,
      UpperSemicontinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => f p A) Y := by
    intro p hp
    exact (finiteBuresContinuousOn_saddleValue_right source target p).neg.upperSemicontinuousOn
  have hfx' : ∀ p ∈ X,
      QuasiconcaveOn ℝ Y
        (fun A : Matrix (Fin n) (Fin n) ℂ => f p A) := by
    intro p hp
    exact (finiteBuresConvexOn_saddleValue_right hp).neg.quasiconcaveOn
  have hsup_y : ∀ p ∈ X,
      IsLUB {q : ℝ | ∃ A ∈ Y, f p A = q}
        (-finiteBuresMixtureValue source target p) := by
    intro p hp
    have hglb : IsGLB (finiteBuresReporterValueSet source target p)
        (finiteBuresMixtureValue source target p) := by
      exact isGLB_csInf (finiteBuresReporterValueSet_nonempty source target p)
        (finiteBuresReporterValueSet_bddBelow hsource target hp)
    have hglb' : IsGLB
        {q : ℝ | ∃ A ∈ Y, finiteBuresSaddleValue source target p A = q}
        (finiteBuresMixtureValue source target p) := by
      simpa [finiteBuresReporterValueSet, Y, eq_comm] using hglb
    have hneg := finiteBuresIsLUB_neg_functionValues_of_isGLB hglb'
    simpa [f, Y, finiteBuresReporterValueSet] using hneg
  have hinf_sup : IsGLB
      {q : ℝ | ∃ p ∈ X, -finiteBuresMixtureValue source target p = q}
      (-finiteBuresDualCapacity source target) := by
    have hlub : IsLUB (finiteBuresMixtureValueSet source target)
        (finiteBuresDualCapacity source target) := by
      exact isLUB_csSup (finiteBuresMixtureValueSet_nonempty source target)
        (finiteBuresMixtureValueSet_bddAbove hsource target)
    have hlub' : IsLUB
        {q : ℝ | ∃ p ∈ X, finiteBuresMixtureValue source target p = q}
        (finiteBuresDualCapacity source target) := by
      simpa [finiteBuresMixtureValueSet, X, eq_comm] using hlub
    have hneg := finiteBuresIsGLB_neg_functionValues_of_isLUB hlub'
    simpa [X, finiteBuresDualCapacity, finiteBuresMixtureValueSet] using hneg
  have hinf_x : ∀ A ∈ Y,
      IsGLB {q : ℝ | ∃ p ∈ X, f p A = q}
        (-finiteBuresReporterWorstValue source target A) := by
    intro A hA
    have hlub : IsLUB (finiteBuresSimplexValueSet source target A)
        (finiteBuresReporterWorstValue source target A) := by
      exact isLUB_csSup (finiteBuresSimplexValueSet_nonempty source target A)
        (finiteBuresSimplexValueSet_bddAbove source target A)
    have hlub' : IsLUB
        {q : ℝ | ∃ p ∈ X, finiteBuresSaddleValue source target p A = q}
        (finiteBuresReporterWorstValue source target A) := by
      simpa [finiteBuresSimplexValueSet, X, eq_comm] using hlub
    have hneg := finiteBuresIsGLB_neg_functionValues_of_isLUB hlub'
    simpa [f, X, finiteBuresSimplexValueSet] using hneg
  have hsup_inf : IsLUB
      {q : ℝ | ∃ A ∈ Y, -finiteBuresReporterWorstValue source target A = q}
      (-finiteBuresPrimalCapacity source target) := by
    have hglb : IsGLB (finiteBuresReporterWorstValueSet source target)
        (finiteBuresPrimalCapacity source target) := by
      exact isGLB_csInf (finiteBuresReporterWorstValueSet_nonempty source target)
        (finiteBuresReporterWorstValueSet_bddBelow hsource target)
    have hglb' : IsGLB
        {q : ℝ | ∃ A ∈ Y, finiteBuresReporterWorstValue source target A = q}
        (finiteBuresPrimalCapacity source target) := by
      simpa [finiteBuresReporterWorstValueSet, Y, eq_comm] using hglb
    have hneg := finiteBuresIsLUB_neg_functionValues_of_isGLB hglb'
    simpa [Y, finiteBuresPrimalCapacity, finiteBuresReporterWorstValueSet] using hneg
  have hminimax : -finiteBuresDualCapacity source target =
      -finiteBuresPrimalCapacity source target := by
    exact Sion.minimax hXne hXcompact hfy hfy' hYconvex hfx hfx'
      hXconvex
      (fun p => -finiteBuresMixtureValue source target p) hsup_y
      (-finiteBuresDualCapacity source target) hinf_sup
      (fun A => -finiteBuresReporterWorstValue source target A) hinf_x
      (-finiteBuresPrimalCapacity source target) hsup_inf
  linarith

def finiteBuresTargetMaximum
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun c => finiteBuresTargetLeverage A (target c))

theorem finiteBuresTargetLeverage_le_targetMaximum
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) (c : C) :
    finiteBuresTargetLeverage A (target c) ≤ finiteBuresTargetMaximum A target := by
  exact Finset.le_sup' (fun i => finiteBuresTargetLeverage A (target i))
    (Finset.mem_univ c)

theorem finiteBuresTargetAverage_le_targetMaximum
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {p : C → ℝ} (hp : p ∈ stdSimplex ℝ C)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) :
    (∑ c, p c * finiteBuresTargetLeverage A (target c)) ≤ finiteBuresTargetMaximum A target := by
  calc
    (∑ c, p c * finiteBuresTargetLeverage A (target c)) ≤
        ∑ c, p c * finiteBuresTargetMaximum A target := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left
        (finiteBuresTargetLeverage_le_targetMaximum A target c) (hp.1 c)
    _ = finiteBuresTargetMaximum A target := by
      rw [← Finset.sum_mul, hp.2, one_mul]

theorem finiteBuresExists_targetLeverage_eq_targetMaximum
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) :
    ∃ c : C, finiteBuresTargetMaximum A target = finiteBuresTargetLeverage A (target c) := by
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_sup'
    Finset.univ_nonempty (fun i => finiteBuresTargetLeverage A (target i))
  exact ⟨c, hc⟩

theorem finiteBuresReporterWorstValue_eq_halfSumMaximum
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    finiteBuresReporterWorstValue source target A =
      (finiteBuresSourcePairing source A + finiteBuresTargetMaximum A target) / 2 := by
  classical
  have hnonempty := finiteBuresSimplexValueSet_nonempty source target A
  have hbdd := finiteBuresSimplexValueSet_bddAbove source target A
  apply le_antisymm
  · apply csSup_le hnonempty
    rintro q ⟨p, hp, rfl⟩
    unfold finiteBuresSaddleValue
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith [finiteBuresTargetAverage_le_targetMaximum hp A target]
  · obtain ⟨c, hc⟩ := finiteBuresExists_targetLeverage_eq_targetMaximum A target
    let p : C → ℝ := Pi.single c 1
    have hp : p ∈ stdSimplex ℝ C := single_mem_stdSimplex ℝ c
    have havg : (∑ i, p i * finiteBuresTargetLeverage A (target i)) =
        finiteBuresTargetMaximum A target := by
      rw [hc]
      unfold p
      rw [Finset.sum_eq_single c]
      · simp
      · intro i _ hic
        simp [Pi.single_eq_of_ne hic]
      · simp
    apply le_csSup hbdd
    refine ⟨p, hp, ?_⟩
    unfold finiteBuresSaddleValue
    rw [havg]

theorem finiteBuresPrimalCapacity_eq_halfSumMaximumInfimum
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) :
    finiteBuresPrimalCapacity source target =
      sInf {q : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℂ,
        A.PosDef ∧
          q = (finiteBuresSourcePairing source A + finiteBuresTargetMaximum A target) / 2} := by
  unfold finiteBuresPrimalCapacity finiteBuresReporterWorstValueSet
  congr 2
  ext q
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, finiteBuresReporterWorstValue_eq_halfSumMaximum source target A⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, (finiteBuresReporterWorstValue_eq_halfSumMaximum source target A).symm⟩

theorem finiteBuresMatrix_inv_real_smul
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) {c : ℝ} (hc : 0 < c) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  letI : Invertible (c : ℂ) := invertibleOfNonzero hcC
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  rw [show c • A = (c : ℂ) • A by rfl]
  rw [A.inv_smul (c : ℂ) hdet]
  ext i j
  simp [invOf_eq_inv]

theorem finiteBuresSourcePairing_real_smul
    {n : ℕ} (source A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) :
    finiteBuresSourcePairing source (c • A) =
      c * finiteBuresSourcePairing source A := by
  unfold finiteBuresSourcePairing
  rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]
  rfl

theorem finiteBuresTargetLeverage_real_smul
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) {c : ℝ} (hc : 0 < c) (v : Fin n → ℂ) :
    finiteBuresTargetLeverage (c • A) v =
      c⁻¹ * finiteBuresTargetLeverage A v := by
  unfold finiteBuresTargetLeverage
  rw [finiteBuresMatrix_inv_real_smul hA hc]
  simp [Matrix.smul_mulVec]

theorem finiteBuresTargetMaximum_real_smul
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef)
    {c : ℝ} (hc : 0 < c) (target : C → Fin n → ℂ) :
    finiteBuresTargetMaximum (c • A) target =
      c⁻¹ * finiteBuresTargetMaximum A target := by
  unfold finiteBuresTargetMaximum
  apply le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
      (fun i => finiteBuresTargetLeverage (c • A) (target i))
    intro i hi
    rw [finiteBuresTargetLeverage_real_smul hA hc]
    exact mul_le_mul_of_nonneg_left
      (Finset.le_sup' (fun j => finiteBuresTargetLeverage A (target j)) hi)
      (inv_nonneg.mpr hc.le)
  · obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup'
      Finset.univ_nonempty (fun j => finiteBuresTargetLeverage A (target j))
    rw [hmax, ← finiteBuresTargetLeverage_real_smul hA hc]
    exact Finset.le_sup' (fun j => finiteBuresTargetLeverage (c • A) (target j)) hi

theorem finiteBuresHalfSumMaximum_real_smul
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef)
    {c : ℝ} (hc : 0 < c) (target : C → Fin n → ℂ) :
    (finiteBuresSourcePairing source (c • A) +
        finiteBuresTargetMaximum (c • A) target) / 2 =
      (c * finiteBuresSourcePairing source A +
        c⁻¹ * finiteBuresTargetMaximum A target) / 2 := by
  rw [finiteBuresSourcePairing_real_smul,
    finiteBuresTargetMaximum_real_smul hA hc]

def finiteBuresScaleHalfSet (x y : ℝ) : Set ℝ :=
  {q | ∃ c : ℝ, 0 < c ∧ q = (c * x + c⁻¹ * y) / 2}

theorem finiteBuresSqrt_mul_le_scaled_half
    {x y c : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 < c) :
    Real.sqrt (x * y) ≤ (c * x + c⁻¹ * y) / 2 := by
  have hcx : 0 ≤ c * x := mul_nonneg hc.le hx
  have hicy : 0 ≤ c⁻¹ * y := mul_nonneg (inv_nonneg.mpr hc.le) hy
  have hprod : (c * x) * (c⁻¹ * y) = x * y := by
    calc
      (c * x) * (c⁻¹ * y) = (c * c⁻¹) * (x * y) := by ring
      _ = x * y := by rw [mul_inv_cancel₀ hc.ne', one_mul]
  have hsquare : Real.sqrt (x * y) ^ 2 = (c * x) * (c⁻¹ * y) := by
    rw [Real.sq_sqrt (mul_nonneg hx hy), hprod]
  have hamgm := two_mul_le_add_of_sq_le_mul hcx hicy hsquare.le
  linarith

theorem finiteBuresScaleHalfSet_nonempty (x y : ℝ) : (finiteBuresScaleHalfSet x y).Nonempty := by
  refine ⟨(x + y) / 2, 1, by norm_num, ?_⟩
  simp

theorem finiteBuresScaleHalfSet_bddBelow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    BddBelow (finiteBuresScaleHalfSet x y) := by
  refine ⟨Real.sqrt (x * y), ?_⟩
  rintro q ⟨c, hc, rfl⟩
  exact finiteBuresSqrt_mul_le_scaled_half hx hy hc

theorem finiteBuresSInf_scaleHalfSet_eq_sqrt_mul
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    sInf (finiteBuresScaleHalfSet x y) = Real.sqrt (x * y) := by
  apply le_antisymm
  · rw [Real.sInf_le_iff (finiteBuresScaleHalfSet_bddBelow hx hy) (finiteBuresScaleHalfSet_nonempty x y)]
    intro ε hε
    rcases eq_or_lt_of_le hx with rfl | hxpos
    · let c := (y + 1) / ε
      have hy1 : 0 < y + 1 := by linarith
      have hc : 0 < c := div_pos hy1 hε
      refine ⟨(c * 0 + c⁻¹ * y) / 2, ⟨c, hc, rfl⟩, ?_⟩
      have hcy : c⁻¹ * y < ε := by
        rw [inv_mul_eq_div, div_lt_iff₀ hc]
        dsimp [c]
        field_simp [hε.ne']
        linarith
      have hcy0 : 0 ≤ c⁻¹ * y := mul_nonneg (inv_nonneg.mpr hc.le) hy
      simp only [zero_mul, zero_add, zero_mul, Real.sqrt_zero]
      linarith
    · rcases eq_or_lt_of_le hy with rfl | hypos
      · let c := ε / (x + 1)
        have hx1 : 0 < x + 1 := by linarith
        have hc : 0 < c := div_pos hε hx1
        refine ⟨(c * x + c⁻¹ * 0) / 2, ⟨c, hc, rfl⟩, ?_⟩
        have hcx : c * x < ε := by
          dsimp [c]
          rw [div_mul_eq_mul_div, div_lt_iff₀ hx1]
          nlinarith
        simp only [mul_zero, add_zero, Real.sqrt_zero]
        linarith
      · let c := Real.sqrt y / Real.sqrt x
        have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
        have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
        have hc : 0 < c := div_pos hsy hsx
        refine ⟨Real.sqrt (x * y), ⟨c, hc, ?_⟩, by linarith⟩
        symm
        calc
          (c * x + c⁻¹ * y) / 2 = Real.sqrt x * Real.sqrt y := by
            dsimp [c]
            field_simp [hsx.ne', hsy.ne']
            nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]
          _ = Real.sqrt (x * y) := (Real.sqrt_mul hx y).symm
  · apply le_csInf (finiteBuresScaleHalfSet_nonempty x y)
    intro q hq
    rcases hq with ⟨c, hc, rfl⟩
    exact finiteBuresSqrt_mul_le_scaled_half hx hy hc

def finiteBuresHalfSumMaximumValueSet
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) : Set ℝ :=
  {q | ∃ A : Matrix (Fin n) (Fin n) ℂ, A.PosDef ∧
    q = (finiteBuresSourcePairing source A + finiteBuresTargetMaximum A target) / 2}

def finiteBuresRootProductValueSet
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) : Set ℝ :=
  {q | ∃ A : Matrix (Fin n) (Fin n) ℂ, A.PosDef ∧
    q = Real.sqrt (finiteBuresSourcePairing source A * finiteBuresTargetMaximum A target)}

def finiteBuresProductMaximumValueSet
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) : Set ℝ :=
  {q | ∃ A : Matrix (Fin n) (Fin n) ℂ, A.PosDef ∧
    q = finiteBuresSourcePairing source A * finiteBuresTargetMaximum A target}

theorem finiteBuresTargetMaximum_nonneg
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef)
    (target : C → Fin n → ℂ) :
    0 ≤ finiteBuresTargetMaximum A target := by
  obtain ⟨c, hc⟩ := finiteBuresExists_targetLeverage_eq_targetMaximum A target
  rw [hc]
  exact finiteBuresTargetLeverage_nonneg hA (target c)

theorem finiteBuresHalfSumMaximumValueSet_nonempty
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) :
    (finiteBuresHalfSumMaximumValueSet source target).Nonempty := by
  refine ⟨(finiteBuresSourcePairing source 1 + finiteBuresTargetMaximum 1 target) / 2,
    1, Matrix.PosDef.one, rfl⟩

theorem finiteBuresHalfSumMaximumValueSet_bddBelow
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ} (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    BddBelow (finiteBuresHalfSumMaximumValueSet source target) := by
  refine ⟨0, ?_⟩
  rintro q ⟨A, hA, rfl⟩
  have hx := finiteBuresSourcePairing_nonneg hsource hA
  have hy := finiteBuresTargetMaximum_nonneg hA target
  linarith

theorem finiteBuresRootProductValueSet_nonempty
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) :
    (finiteBuresRootProductValueSet source target).Nonempty := by
  refine ⟨Real.sqrt (finiteBuresSourcePairing source 1 * finiteBuresTargetMaximum 1 target),
    1, Matrix.PosDef.one, rfl⟩

theorem finiteBuresRootProductValueSet_bddBelow
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) :
    BddBelow (finiteBuresRootProductValueSet source target) := by
  refine ⟨0, ?_⟩
  rintro q ⟨A, hA, rfl⟩
  exact Real.sqrt_nonneg _

theorem finiteBuresProductMaximumValueSet_nonempty
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) :
    (finiteBuresProductMaximumValueSet source target).Nonempty := by
  refine ⟨finiteBuresSourcePairing source 1 * finiteBuresTargetMaximum 1 target,
    1, Matrix.PosDef.one, rfl⟩

theorem finiteBuresProductMaximumValueSet_bddBelow
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ} (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    BddBelow (finiteBuresProductMaximumValueSet source target) := by
  refine ⟨0, ?_⟩
  rintro q ⟨A, hA, rfl⟩
  exact mul_nonneg (finiteBuresSourcePairing_nonneg hsource hA)
    (finiteBuresTargetMaximum_nonneg hA target)

theorem finiteBuresSInf_halfSumMaximumValueSet_eq_sInf_rootProductValueSet
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ} (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    sInf (finiteBuresHalfSumMaximumValueSet source target) =
      sInf (finiteBuresRootProductValueSet source target) := by
  let H := finiteBuresHalfSumMaximumValueSet source target
  let R := finiteBuresRootProductValueSet source target
  have hHne : H.Nonempty := finiteBuresHalfSumMaximumValueSet_nonempty source target
  have hHb : BddBelow H := finiteBuresHalfSumMaximumValueSet_bddBelow hsource target
  have hRne : R.Nonempty := finiteBuresRootProductValueSet_nonempty source target
  have hRb : BddBelow R := finiteBuresRootProductValueSet_bddBelow source target
  apply le_antisymm
  · apply le_csInf hRne
    intro r hr
    rcases hr with ⟨A, hA, rfl⟩
    let x := finiteBuresSourcePairing source A
    let y := finiteBuresTargetMaximum A target
    have hx : 0 ≤ x := finiteBuresSourcePairing_nonneg hsource hA
    have hy : 0 ≤ y := finiteBuresTargetMaximum_nonneg hA target
    have hsubset : finiteBuresScaleHalfSet x y ⊆ H := by
      rintro q ⟨c, hc, rfl⟩
      refine ⟨c • A, hA.smul hc, ?_⟩
      exact (finiteBuresHalfSumMaximum_real_smul source hA hc target).symm
    calc
      sInf H ≤ sInf (finiteBuresScaleHalfSet x y) := by
        apply le_csInf (finiteBuresScaleHalfSet_nonempty x y)
        intro q hq
        exact csInf_le hHb (hsubset hq)
      _ = Real.sqrt (x * y) := finiteBuresSInf_scaleHalfSet_eq_sqrt_mul hx hy
  · apply le_csInf hHne
    intro q hq
    rcases hq with ⟨A, hA, rfl⟩
    have hx := finiteBuresSourcePairing_nonneg hsource hA
    have hy := finiteBuresTargetMaximum_nonneg hA target
    have hroot : Real.sqrt (finiteBuresSourcePairing source A * finiteBuresTargetMaximum A target) ∈ R :=
      ⟨A, hA, rfl⟩
    exact (csInf_le hRb hroot).trans
      (by simpa using finiteBuresSqrt_mul_le_scaled_half hx hy (show (0 : ℝ) < 1 by norm_num))

theorem finiteBuresProductMaximumValueSet_eq_sq_image_rootProductValueSet
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ} (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    finiteBuresProductMaximumValueSet source target =
      (fun r : ℝ => r ^ 2) '' finiteBuresRootProductValueSet source target := by
  ext q
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨Real.sqrt (finiteBuresSourcePairing source A * finiteBuresTargetMaximum A target),
      ⟨A, hA, rfl⟩, ?_⟩
    exact Real.sq_sqrt (mul_nonneg (finiteBuresSourcePairing_nonneg hsource hA)
      (finiteBuresTargetMaximum_nonneg hA target))
  · rintro ⟨r, ⟨A, hA, rfl⟩, rfl⟩
    refine ⟨A, hA, ?_⟩
    exact Real.sq_sqrt (mul_nonneg (finiteBuresSourcePairing_nonneg hsource hA)
      (finiteBuresTargetMaximum_nonneg hA target))

theorem finiteBuresSInf_productMaximumValueSet_eq_sq_sInf_rootProductValueSet
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ} (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    sInf (finiteBuresProductMaximumValueSet source target) =
      sInf (finiteBuresRootProductValueSet source target) ^ 2 := by
  let R := finiteBuresRootProductValueSet source target
  have hRne : R.Nonempty := finiteBuresRootProductValueSet_nonempty source target
  have hRb : BddBelow R := finiteBuresRootProductValueSet_bddBelow source target
  have hmono : MonotoneOn (fun r : ℝ => r ^ 2) R := by
    intro a ha b hb hab
    have ha0 : 0 ≤ a := by
      rcases ha with ⟨A, hA, rfl⟩
      exact Real.sqrt_nonneg _
    have hb0 : 0 ≤ b := by
      rcases hb with ⟨A, hA, rfl⟩
      exact Real.sqrt_nonneg _
    exact (sq_le_sq₀ ha0 hb0).2 hab
  have hmap : sInf R ^ 2 = sInf ((fun r : ℝ => r ^ 2) '' R) :=
    MonotoneOn.map_csInf_of_continuousWithinAt
      ((continuous_pow 2).continuousAt.continuousWithinAt) hmono hRne hRb
  rw [finiteBuresProductMaximumValueSet_eq_sq_image_rootProductValueSet hsource target]
  exact hmap.symm

def finiteBuresRootProductCapacity
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) : ℝ :=
  sInf (finiteBuresRootProductValueSet source target)

def finiteBuresProductCapacity
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (source : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) : ℝ :=
  sInf (finiteBuresProductMaximumValueSet source target)

theorem finiteBuresPrimalCapacity_eq_rootProductCapacity
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ} (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    finiteBuresPrimalCapacity source target =
      finiteBuresRootProductCapacity source target := by
  rw [finiteBuresPrimalCapacity_eq_halfSumMaximumInfimum]
  exact (finiteBuresSInf_halfSumMaximumValueSet_eq_sInf_rootProductValueSet
    hsource target)

theorem finiteBuresProductCapacity_eq_primalCapacity_sq
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ} (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    finiteBuresProductCapacity source target =
      finiteBuresPrimalCapacity source target ^ 2 := by
  unfold finiteBuresProductCapacity
  rw [finiteBuresSInf_productMaximumValueSet_eq_sq_sInf_rootProductValueSet
    hsource target]
  rw [finiteBuresPrimalCapacity_eq_rootProductCapacity hsource target]
  rfl

theorem finiteBuresProductCapacity_eq_dualCapacity_sq
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {source : Matrix (Fin n) (Fin n) ℂ} (hsource : source.PosSemidef)
    (target : C → Fin n → ℂ) :
    finiteBuresProductCapacity source target =
      finiteBuresDualCapacity source target ^ 2 := by
  rw [finiteBuresProductCapacity_eq_primalCapacity_sq hsource target,
    finiteBuresPrimalCapacity_eq_dualCapacity hsource target]

theorem finiteBuresPositiveWeight_targetLeverage_eq_targetMaximum
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {p : C → ℝ} (hp : p ∈ stdSimplex ℝ C)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ)
    (haverage : (∑ i, p i * finiteBuresTargetLeverage A (target i)) =
      finiteBuresTargetMaximum A target)
    (c : C) (hpc : 0 < p c) :
    finiteBuresTargetLeverage A (target c) = finiteBuresTargetMaximum A target := by
  apply le_antisymm (finiteBuresTargetLeverage_le_targetMaximum A target c)
  by_contra hnot
  have hlt : finiteBuresTargetLeverage A (target c) < finiteBuresTargetMaximum A target :=
    lt_of_not_ge hnot
  have hgap_nonneg : ∀ i : C,
      0 ≤ p i * (finiteBuresTargetMaximum A target - finiteBuresTargetLeverage A (target i)) := by
    intro i
    exact mul_nonneg (hp.1 i)
      (sub_nonneg.mpr (finiteBuresTargetLeverage_le_targetMaximum A target i))
  have hgap_sum :
      (∑ i, p i * (finiteBuresTargetMaximum A target - finiteBuresTargetLeverage A (target i))) = 0 := by
    calc
      (∑ i, p i * (finiteBuresTargetMaximum A target - finiteBuresTargetLeverage A (target i))) =
          finiteBuresTargetMaximum A target * (∑ i, p i) -
            ∑ i, p i * finiteBuresTargetLeverage A (target i) := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hp.2, haverage]; ring
  have htermpos : 0 < p c *
      (finiteBuresTargetMaximum A target - finiteBuresTargetLeverage A (target c)) :=
    mul_pos hpc (sub_pos.mpr hlt)
  have htermle : p c *
      (finiteBuresTargetMaximum A target - finiteBuresTargetLeverage A (target c)) ≤
      ∑ i, p i * (finiteBuresTargetMaximum A target - finiteBuresTargetLeverage A (target i)) := by
    exact Finset.single_le_sum (fun i _ => hgap_nonneg i) (Finset.mem_univ c)
  rw [hgap_sum] at htermle
  linarith

end

end GaloisForLFunctions.HTGeometry
