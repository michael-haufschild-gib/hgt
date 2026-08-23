import GaloisForLFunctions.HTGeometry.BlockDiagonalDeterminant
import GaloisForLFunctions.RHTower.ExponentialPolynomialIntervalMoments
import GaloisForLFunctions.RHTower.ResidueModeMultiplicityBlock

/-!
# Exact rank of finite residue-mode operators

For finitely many distinct pole nodes, each nonzero top Laurent coefficient gives an invertible
anti-triangular local block.  Their dependent block diagonal is invertible.  Compactly supported
inputs on the positive logarithmic half-line realize every input-moment vector, while the complete
exponential-polynomial output family stays linearly independent after restriction to `t < 0`.
Therefore the residue-mode operator has exact rank equal to the sum of pole multiplicities.
-/

namespace RHTower

open Complex Matrix Set
open scoped BigOperators

noncomputable section

abbrev FiniteResidueSlot {r : ℕ} (m : Fin r → ℕ) :=
  Σ i : Fin r, Fin (m i + 1)

/-- Actual pole multiplicities when `m i` records the top polynomial degree. -/
abbrev finiteResidueMultiplicity {r : ℕ} (m : Fin r → ℕ) : Fin r → ℕ :=
  fun i => m i + 1

/-- Canonical equivalence between pole-local slots and the confluent finite indexing. -/
def finiteResidueSlotEquiv {r : ℕ} (m : Fin r → ℕ) :
    FiniteResidueSlot m ≃ Fin (∑ i, (m i + 1)) :=
  (toLex : (Σ i : Fin r, Fin (m i + 1)) ≃
      Lex (Σ i : Fin r, Fin (m i + 1))).trans
    (GaloisForLFunctions.gammaJetSlotOrderIso
      (fun i => m i + 1)).toEquiv.symm

@[simp] theorem gammaJetSlotNode_finiteResidueSlotEquiv
    {r : ℕ} (m : Fin r → ℕ) (k : FiniteResidueSlot m) :
    GaloisForLFunctions.gammaJetSlotNode (fun i => m i + 1)
      (finiteResidueSlotEquiv m k) = k.1 := by
  rw [GaloisForLFunctions.gammaJetSlotNode, finiteResidueSlotEquiv]
  change ((GaloisForLFunctions.gammaJetSlotOrderIso (fun i => m i + 1))
    ((GaloisForLFunctions.gammaJetSlotOrderIso (fun i => m i + 1)).symm
      (toLex k))).1 = k.1
  rw [OrderIso.apply_symm_apply]
  rfl

@[simp] theorem gammaJetSlotOrder_finiteResidueSlotEquiv
    {r : ℕ} (m : Fin r → ℕ) (k : FiniteResidueSlot m) :
    GaloisForLFunctions.gammaJetSlotOrder (fun i => m i + 1)
      (finiteResidueSlotEquiv m k) = k.2.val := by
  rw [GaloisForLFunctions.gammaJetSlotOrder, finiteResidueSlotEquiv]
  change ((GaloisForLFunctions.gammaJetSlotOrderIso (fun i => m i + 1))
    ((GaloisForLFunctions.gammaJetSlotOrderIso (fun i => m i + 1)).symm
      (toLex k))).2.val = k.2.val
  rw [OrderIso.apply_symm_apply]
  rfl

def finiteResidueCoeffMatrix {r : ℕ} (m : Fin r → ℕ)
    (a : ∀ i, Fin (m i + 1) → ℂ) :
    Matrix (FiniteResidueSlot m) (FiniteResidueSlot m) ℂ :=
  Matrix.blockDiagonal' fun i => residueModeCoeffMatrix (m i) (a i)

theorem residueModeCoeffMatrix_det_ne_zero
    (m : ℕ) (a : Fin (m + 1) → ℂ) (ha : a (Fin.last m) ≠ 0) :
    (residueModeCoeffMatrix m a).det ≠ 0 := by
  have hu : IsUnit (residueModeCoeffMatrix m a) :=
    Matrix.mulVec_injective_iff_isUnit.mp
      (residueModeCoeffMatrix_mulVec_injective m a ha)
  exact ((residueModeCoeffMatrix m a).isUnit_iff_isUnit_det.mp hu).ne_zero

theorem finiteResidueCoeffMatrix_det_ne_zero
    {r : ℕ} (m : Fin r → ℕ) (a : ∀ i, Fin (m i + 1) → ℂ)
    (ha : ∀ i, a i (Fin.last (m i)) ≠ 0) :
    (finiteResidueCoeffMatrix m a).det ≠ 0 := by
  rw [finiteResidueCoeffMatrix,
    GaloisForLFunctions.HTGeometry.det_blockDiagonal']
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    residueModeCoeffMatrix_det_ne_zero (m i) (a i) (ha i)

theorem finiteResidueCoeffMatrix_isUnit
    {r : ℕ} (m : Fin r → ℕ) (a : ∀ i, Fin (m i + 1) → ℂ)
    (ha : ∀ i, a i (Fin.last (m i)) ≠ 0) :
    IsUnit (finiteResidueCoeffMatrix m a) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact finiteResidueCoeffMatrix_det_ne_zero m a ha

theorem finiteResidueCoeffMatrix_mulVec_surjective
    {r : ℕ} (m : Fin r → ℕ) (a : ∀ i, Fin (m i + 1) → ℂ)
    (ha : ∀ i, a i (Fin.last (m i)) ≠ 0) :
    Function.Surjective (finiteResidueCoeffMatrix m a).mulVec :=
  Matrix.mulVec_surjective_iff_isUnit.mpr
    (finiteResidueCoeffMatrix_isUnit m a ha)

def finiteResidueSlotMode {r : ℕ} (lambda : Fin r → ℂ) (m : Fin r → ℕ)
    (k : FiniteResidueSlot m) : ℂ → ℂ :=
  exponentialPolynomialMode lambda (fun i => m i + 1)
    (finiteResidueSlotEquiv m k)

theorem finiteResidueSlotMode_apply
    {r : ℕ} (lambda : Fin r → ℂ) (m : Fin r → ℕ)
    (k : FiniteResidueSlot m) (t : ℂ) :
    finiteResidueSlotMode lambda m k t =
      t ^ k.2.val * Complex.exp (lambda k.1 * t) := by
  rw [finiteResidueSlotMode, exponentialPolynomialMode,
    gammaJetSlotNode_finiteResidueSlotEquiv,
    gammaJetSlotOrder_finiteResidueSlotEquiv]

theorem contDiff_finiteResidueSlotMode
    {r : ℕ} (lambda : Fin r → ℂ) (m : Fin r → ℕ)
    (k : FiniteResidueSlot m) (n : ℕ) :
    ContDiff ℂ n (finiteResidueSlotMode lambda m k) := by
  exact contDiff_exponentialPolynomialMode lambda (fun i => m i + 1)
    (finiteResidueSlotEquiv m k) n

theorem finiteResidueSlotMode_linearIndependent
    {r : ℕ} {lambda : Fin r → ℂ} (hlambda : Function.Injective lambda)
    (m : Fin r → ℕ) :
    LinearIndependent ℂ (finiteResidueSlotMode lambda m) := by
  exact (exponentialPolynomialMode_linearIndependent hlambda
    (fun i => m i + 1)).comp
      (finiteResidueSlotEquiv m) (finiteResidueSlotEquiv m).injective

def finiteResidueOutputSynthesis {r : ℕ} (lambda : Fin r → ℂ) (m : Fin r → ℕ) :
    (FiniteResidueSlot m → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun c := fun t => ∑ k, c k * finiteResidueSlotMode lambda m k t
  map_add' c d := by
    funext t
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' q c := by
    funext t
    change (∑ k, (q * c k) * finiteResidueSlotMode lambda m k t) =
      q * ∑ k, c k * finiteResidueSlotMode lambda m k t
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem finiteResidueOutputSynthesis_injective
    {r : ℕ} {lambda : Fin r → ℂ} (hlambda : Function.Injective lambda)
    (m : Fin r → ℕ) :
    Function.Injective (finiteResidueOutputSynthesis lambda m) := by
  intro c d hcd
  have hLI := finiteResidueSlotMode_linearIndependent hlambda m
  rw [Fintype.linearIndependent_iff] at hLI
  apply sub_eq_zero.mp
  apply funext
  apply hLI (c - d)
  funext t
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
  change (∑ k, (c k - d k) * finiteResidueSlotMode lambda m k t) = 0
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr (congrFun hcd t)

/-- Output synthesis restricted to the logarithmic leakage half-line `t < 0`. -/
def finiteResidueNegativeOutputSynthesis
    {r : ℕ} (lambda : Fin r → ℂ) (m : Fin r → ℕ) :
    (FiniteResidueSlot m → ℂ) →ₗ[ℂ] ({t : ℝ // t < 0} → ℂ) where
  toFun c := fun t => ∑ k, c k * finiteResidueSlotMode lambda m k (t.1 : ℂ)
  map_add' c d := by
    funext t
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' q c := by
    funext t
    change (∑ k, (q * c k) * finiteResidueSlotMode lambda m k (t.1 : ℂ)) =
      q * ∑ k, c k * finiteResidueSlotMode lambda m k (t.1 : ℂ)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem finiteResidueNegativeOutputSynthesis_injective
    {r : ℕ} {lambda : Fin r → ℂ} (hlambda : Function.Injective lambda)
    (m : Fin r → ℕ) :
    Function.Injective (finiteResidueNegativeOutputSynthesis lambda m) := by
  intro c d hcd
  let F : ℂ → ℂ := fun z => ∑ k, (c k - d k) * finiteResidueSlotMode lambda m k z
  have hdiff : Differentiable ℂ F := by
    apply Differentiable.fun_sum
    intro k _
    exact (differentiable_const _).mul
      ((contDiff_finiteResidueSlotMode lambda m k 1).differentiable (by norm_num))
  let t0 : ℝ := -(3 : ℝ) / 2
  let delta : ℝ := 1 / 2
  have hdelta : 0 < delta := by norm_num [delta]
  have hae : ∀ᵐ s : ℝ ∂(MeasureTheory.volume.restrict
      (Set.Ioo (t0 - delta) (t0 + delta))), F (s : ℂ) = 0 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with s hs
    have hsneg : s < 0 := by
      rcases hs with ⟨_, hs⟩
      dsimp [t0, delta] at hs
      linarith
    have ht := congrFun hcd (⟨s, hsneg⟩ : {t : ℝ // t < 0})
    dsimp only [finiteResidueNegativeOutputSynthesis] at ht
    dsimp only [F]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr ht
  have hFzero : ∀ z : ℂ, F z = 0 := fun z =>
    GaloisForLFunctions.HTGeometry.entire_eq_zero_of_ae_vanishing_on_real_interval
      hdiff hdelta hae z
  have hLI := finiteResidueSlotMode_linearIndependent hlambda m
  rw [Fintype.linearIndependent_iff] at hLI
  apply sub_eq_zero.mp
  apply funext
  apply hLI (c - d)
  funext z
  simpa [F, Pi.smul_apply, smul_eq_mul] using hFzero z

def finiteResidueInputMoment {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ)
    (g : ℝ → ℂ) : FiniteResidueSlot m → ℂ :=
  fun k => exponentialPolynomialMoment (fun i => Complex.I * z i)
    (fun i => m i + 1) g (finiteResidueSlotEquiv m k)

theorem finiteResidueInputMoment_surjective_on_interval
    {r : ℕ} {z : Fin r → ℂ} (hz : Function.Injective z)
    (m : Fin r → ℕ) {a b : ℝ} (hab : a < b) :
    Function.Surjective (finiteResidueInputMoment z m) := by
  have hnodes : Function.Injective (fun i => Complex.I * z i) := by
    intro i j hij
    exact hz (mul_left_cancel₀ Complex.I_ne_zero hij)
  intro y
  let yFin : Fin (∑ i, (m i + 1)) → ℂ := fun k => y ((finiteResidueSlotEquiv m).symm k)
  obtain ⟨g, hg⟩ :=
    exponentialPolynomialMoment_surjective hnodes (fun i => m i + 1) hab yFin
  refine ⟨g, ?_⟩
  funext k
  simpa [finiteResidueInputMoment, yFin] using congrFun hg (finiteResidueSlotEquiv m k)

theorem finiteResidueInputMoment_surjective
    {r : ℕ} {z : Fin r → ℂ} (hz : Function.Injective z)
    (m : Fin r → ℕ) :
    Function.Surjective (finiteResidueInputMoment z m) :=
  finiteResidueInputMoment_surjective_on_interval hz m (a := 1) (b := 2) (by norm_num)

def finiteResidueInputCoefficient
    {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ)
    (a : ∀ i, Fin (m i + 1) → ℂ) (g : ℝ → ℂ) : FiniteResidueSlot m → ℂ :=
  (finiteResidueCoeffMatrix m a).mulVec (finiteResidueInputMoment z m g)

theorem finiteResidueInputCoefficient_surjective_on_interval
    {r : ℕ} {z : Fin r → ℂ} (hz : Function.Injective z)
    (m : Fin r → ℕ) (a : ∀ i, Fin (m i + 1) → ℂ)
    (ha : ∀ i, a i (Fin.last (m i)) ≠ 0)
    {u v : ℝ} (huv : u < v) :
    Function.Surjective (finiteResidueInputCoefficient z m a) := by
  intro y
  obtain ⟨x, hx⟩ := finiteResidueCoeffMatrix_mulVec_surjective m a ha y
  obtain ⟨g, hg⟩ := finiteResidueInputMoment_surjective_on_interval hz m huv x
  refine ⟨g, ?_⟩
  rw [finiteResidueInputCoefficient, hg, hx]

theorem finiteResidueInputCoefficient_surjective
    {r : ℕ} {z : Fin r → ℂ} (hz : Function.Injective z)
    (m : Fin r → ℕ) (a : ∀ i, Fin (m i + 1) → ℂ)
    (ha : ∀ i, a i (Fin.last (m i)) ≠ 0) :
    Function.Surjective (finiteResidueInputCoefficient z m a) :=
  finiteResidueInputCoefficient_surjective_on_interval hz m a ha (by norm_num : (1 : ℝ) < 2)

def finiteResidueModeOperator
    {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ)
    (a : ∀ i, Fin (m i + 1) → ℂ) (g : ℝ → ℂ) : ℂ → ℂ :=
  finiteResidueOutputSynthesis (fun i => -Complex.I * z i) m
    (finiteResidueInputCoefficient z m a g)

theorem finiteResidueModeOperator_span_range
    {r : ℕ} {z : Fin r → ℂ} (hz : Function.Injective z)
    (m : Fin r → ℕ) (a : ∀ i, Fin (m i + 1) → ℂ)
    (ha : ∀ i, a i (Fin.last (m i)) ≠ 0)
    {u v : ℝ} (huv : u < v) :
    Submodule.span ℂ (Set.range (finiteResidueModeOperator z m a)) =
      (finiteResidueOutputSynthesis (fun i => -Complex.I * z i) m).range := by
  have hcoeff := finiteResidueInputCoefficient_surjective_on_interval hz m a ha huv
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro f ⟨g, rfl⟩
    exact ⟨finiteResidueInputCoefficient z m a g, rfl⟩
  · rintro f ⟨c, rfl⟩
    obtain ⟨g, hg⟩ := hcoeff c
    apply Submodule.subset_span
    refine ⟨g, ?_⟩
    simp only [finiteResidueModeOperator, hg]

theorem finiteResidueModeOperator_rank
    {r : ℕ} {z : Fin r → ℂ} (hz : Function.Injective z)
    (m : Fin r → ℕ) (a : ∀ i, Fin (m i + 1) → ℂ)
    (ha : ∀ i, a i (Fin.last (m i)) ≠ 0)
    {u v : ℝ} (huv : u < v) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (finiteResidueModeOperator z m a))) =
      ∑ i, (m i + 1) := by
  rw [finiteResidueModeOperator_span_range hz m a ha huv]
  have hnodes : Function.Injective (fun i => -Complex.I * z i) := by
    intro i j hij
    exact hz (mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) hij)
  rw [LinearMap.finrank_range_of_inj
    (finiteResidueOutputSynthesis_injective hnodes m)]
  simp [FiniteResidueSlot]

/-- Finite residue-mode operator on the actual logarithmic output half-line `t < 0`. -/
def finiteResidueNegativeModeOperator
    {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ)
    (a : ∀ i, Fin (m i + 1) → ℂ) (g : ℝ → ℂ) : {t : ℝ // t < 0} → ℂ :=
  finiteResidueNegativeOutputSynthesis (fun i => -Complex.I * z i) m
    (finiteResidueInputCoefficient z m a g)

theorem finiteResidueNegativeModeOperator_apply
    {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ)
    (a : ∀ i, Fin (m i + 1) → ℂ) (g : ℝ → ℂ) (t : {t : ℝ // t < 0}) :
    finiteResidueNegativeModeOperator z m a g t =
      ∑ k, finiteResidueInputCoefficient z m a g k *
        (t.1 : ℂ) ^ k.2.val * Complex.exp ((-Complex.I * z k.1) * (t.1 : ℂ)) := by
  simp only [finiteResidueNegativeModeOperator, finiteResidueNegativeOutputSynthesis,
    finiteResidueSlotMode_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem finiteResidueNegativeModeOperator_span_range
    {r : ℕ} {z : Fin r → ℂ} (hz : Function.Injective z)
    (m : Fin r → ℕ) (a : ∀ i, Fin (m i + 1) → ℂ)
    (ha : ∀ i, a i (Fin.last (m i)) ≠ 0) :
    Submodule.span ℂ (Set.range (finiteResidueNegativeModeOperator z m a)) =
      (finiteResidueNegativeOutputSynthesis (fun i => -Complex.I * z i) m).range := by
  have hcoeff := finiteResidueInputCoefficient_surjective hz m a ha
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro f ⟨g, rfl⟩
    exact ⟨finiteResidueInputCoefficient z m a g, rfl⟩
  · rintro f ⟨c, rfl⟩
    obtain ⟨g, hg⟩ := hcoeff c
    apply Submodule.subset_span
    refine ⟨g, ?_⟩
    simp only [finiteResidueNegativeModeOperator, hg]

/-- Exact total rank on `t < 0`: an order-`mᵢ+1` pole contributes precisely `mᵢ+1` modes. -/
theorem finiteResidueNegativeModeOperator_rank
    {r : ℕ} {z : Fin r → ℂ} (hz : Function.Injective z)
    (m : Fin r → ℕ) (a : ∀ i, Fin (m i + 1) → ℂ)
    (ha : ∀ i, a i (Fin.last (m i)) ≠ 0) :
    Module.finrank ℂ
        (Submodule.span ℂ (Set.range (finiteResidueNegativeModeOperator z m a))) =
      ∑ i, (m i + 1) := by
  rw [finiteResidueNegativeModeOperator_span_range hz m a ha]
  have hnodes : Function.Injective (fun i => -Complex.I * z i) := by
    intro i j hij
    exact hz (mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) hij)
  rw [LinearMap.finrank_range_of_inj
    (finiteResidueNegativeOutputSynthesis_injective hnodes m)]
  simp [FiniteResidueSlot]

end

end RHTower
