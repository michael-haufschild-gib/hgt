import GaloisForLFunctions.HTGeometry.PrimeValuationFusion
import GaloisForLFunctions.HTGeometry.CompactTailDensePrimeValuationMaster
import GaloisForLFunctions.HTGeometry.TailDenseObservableFieldClassification

/-!
# Tail-complete prime-valuation fusion representation

A cofinally tail-dense profile makes the homogeneous source coordinate algebra visible without
loss in prime valuation.  Each homogeneous layer maps linearly into its matching prime-power
column, its kernel is exactly the constraint vanishing space, and source multiplication is the
prime-local fusion product.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction MvPolynomial

noncomputable section

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 80000

/-- Linear valuation representation of one homogeneous source layer. -/
def homogeneousConstraintValuationLinearMap
    {σ : Type*} (x : Nat.Primes → σ → ℂ) (m : ℕ) :
    homogeneousSubmodule σ ℂ m →ₗ[ℂ] ArithmeticFunction ℂ where
  toFun Q := arithmeticOfPrimePowerColumn (m - 1) fun p =>
    eval (x p) Q.1
  map_add' Q R := by
    rw [← arithmeticOfPrimePowerColumn_add]
    congr 1
    funext p
    simp
  map_smul' z Q := by
    rw [smul_arithmeticOfPrimePowerColumn]
    congr 1
    funext p
    simp

@[simp]
theorem homogeneousConstraintValuationLinearMap_apply
    {σ : Type*} (x : Nat.Primes → σ → ℂ) (m : ℕ)
    (Q : homogeneousSubmodule σ ℂ m) :
    homogeneousConstraintValuationLinearMap x m Q =
      homogeneousConstraintValuationCarrier x m Q :=
  rfl

/-- **Tail-complete faithfulness.**  The kernel of the valuation representation in every
homogeneous degree is exactly the reduced homogeneous constraint relation space. -/
theorem homogeneousConstraintValuationLinearMap_ker_eq_constraintVanishing
    {σ : Type*} [Fintype σ]
    (x : Nat.Primes → σ → ℂ) (K : Set (σ → ℂ))
    (hx : CofiniteTailDenseOn x K) (m : ℕ) :
    LinearMap.ker (homogeneousConstraintValuationLinearMap x m) =
      homogeneousConstraintVanishingSubmodule K m := by
  ext Q
  rw [LinearMap.mem_ker]
  change homogeneousConstraintValuationCarrier x m Q = 0 ↔
    Q ∈ homogeneousConstraintVanishingSubmodule K m
  constructor
  · intro hzero
    have heval : ∀ p, eval (x p) Q.1 = 0 := by
      intro p
      have hp := DFunLike.congr_fun hzero ((p : ℕ) ^ (m - 1 + 1))
      simpa [homogeneousConstraintValuationCarrier] using hp
    apply (cofiniteTailDenseOn_mvPolynomial_eval_support_finite_iff x K hx Q.1).mp
    simp [heval]
  · intro hvanish
    have heval : ∀ p, eval (x p) Q.1 = 0 := by
      intro p
      exact hvanish (x p) (hx.1 ⟨p, rfl⟩)
    ext n
    by_cases hpow : ∃ p : Nat.Primes, n = (p : ℕ) ^ (m - 1 + 1)
    · obtain ⟨p, rfl⟩ := hpow
      simp [homogeneousConstraintValuationCarrier, heval]
    · simp [homogeneousConstraintValuationCarrier,
        arithmeticOfPrimePowerColumn, hpow]

/-- Every homogeneous coordinate layer is linearly isomorphic to its actual prime-valuation
image.  The quotient is by the complete reduced constraint kernel, not by a chosen presentation. -/
def tailCompleteHomogeneousConstraintValuationEquivRange
    {σ : Type*} [Fintype σ]
    (x : Nat.Primes → σ → ℂ) (K : Set (σ → ℂ))
    (hx : CofiniteTailDenseOn x K) (m : ℕ) :
    (homogeneousSubmodule σ ℂ m ⧸
        homogeneousConstraintVanishingSubmodule K m) ≃ₗ[ℂ]
      LinearMap.range (homogeneousConstraintValuationLinearMap x m) := by
  rw [← homogeneousConstraintValuationLinearMap_ker_eq_constraintVanishing x K hx m]
  exact (homogeneousConstraintValuationLinearMap x m).quotKerEquivRange

/-- **Faithful graded fusion representation.**  On positive degrees, multiplication in the
source homogeneous coordinate algebra is transported exactly to prime-valuation fusion. -/
theorem tailCompleteHomogeneousConstraintValuation_map_mul
    {σ : Type*} (x : Nat.Primes → σ → ℂ)
    (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (Q : homogeneousSubmodule σ ℂ m)
    (R : homogeneousSubmodule σ ℂ n) :
    primeValuationFusion (m - 1) (n - 1)
        (homogeneousConstraintValuationLinearMap x m Q)
        (homogeneousConstraintValuationLinearMap x n R) =
      homogeneousConstraintValuationLinearMap x (m + n)
        (homogeneousObservableMul Q R) := by
  simpa only [homogeneousConstraintValuationLinearMap_apply] using
    homogeneousConstraintValuationCarrier_mul x m n hm hn Q R

/-- The complete all-order shifted-jet fusion law for the faithful source representation. -/
theorem tailCompleteHomogeneousConstraintValuation_map_mul_jet
    {σ : Type*} (x : Nat.Primes → σ → ℂ)
    (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (Q : homogeneousSubmodule σ ℂ m)
    (R : homogeneousSubmodule σ ℂ n)
    (a b : ℂ) (k : ℕ) :
    homogeneousConstraintValuationJet x (m + n)
        (homogeneousObservableMul Q R) (a + b) k =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) •
          primeValuationFusion (m - 1) (n - 1)
            (homogeneousConstraintValuationJet x m Q a i)
            (homogeneousConstraintValuationJet x n R b (k - i)) :=
  homogeneousConstraintValuationJet_mul_binomial x m n hm hn Q R a b k

/-- **Grassmann meet law.**  For a tail-complete source, two observable fields generated by a
common independent block and two independent complementary blocks intersect in exactly the field
of the common source block.  Together with the order law, this is the basis-decomposition form of
finite observable-subspace lattice faithfulness. -/
theorem cofiniteTailDenseOn_observableShiftField_threeBlock_inf
    {V A B C : Type*} [TopologicalSpace V]
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty (A ⊕ (B ⊕ C))]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : A → V → ℂ) (g : B → V → ℂ) (h : C → V → ℂ)
    (hf : ∀ i, Continuous (f i))
    (hg : ∀ j, Continuous (g j))
    (hh : ∀ k, Continuous (h k))
    (hlinear : LinearIndependent ℂ
      (fun q => fun v : K => Sum.elim f (Sum.elim g h) q v.1))
    (a : ℂ) :
    tailDenseObservableShiftField x (Sum.elim f g) a ⊓
        tailDenseObservableShiftField x (Sum.elim f h) a =
      tailDenseObservableShiftField x f a := by
  let F : A ⊕ (B ⊕ C) → V → ℂ := Sum.elim f (Sum.elim g h)
  have hF : ∀ q, Continuous (F q) := by
    intro q
    rcases q with i | q
    · exact hf i
    · rcases q with j | k
      · exact hg j
      · exact hh k
  have hDI := cofiniteTailDenseOn_observableShiftCarrier_differentialIndependent
    x K hx F hF (by simpa only [F] using hlinear) a
  let ca : A → arithmeticFunctionRationalCoordinateField := fun i =>
    tailDenseObservableShiftCarrier x (f i) a
  let cb : B → arithmeticFunctionRationalCoordinateField := fun j =>
    tailDenseObservableShiftCarrier x (g j) a
  let cc : C → arithmeticFunctionRationalCoordinateField := fun k =>
    tailDenseObservableShiftCarrier x (h k) a
  have hblocks : GaloisForLFunctions.DifferentialIndependent
      finitePrimeRationalCoefficientField (Sum.elim ca (Sum.elim cb cc)) := by
    have hfun :
        (fun q => tailDenseObservableShiftCarrier x (F q) a) =
          Sum.elim ca (Sum.elim cb cc) := by
      funext q
      rcases q with i | q
      · rfl
      · rcases q with j | k <;> rfl
    rw [hfun] at hDI
    exact hDI
  have hmeet := GaloisForLFunctions.differentialIndependent_threeBlock_differentialAdjoin_inf
    ca cb cc hblocks
  have hab :
      (fun q => tailDenseObservableShiftCarrier x (Sum.elim f g q) a) =
        Sum.elim ca cb := by
    funext q
    rcases q with i | j <;> rfl
  have hac :
      (fun q => tailDenseObservableShiftCarrier x (Sum.elim f h q) a) =
        Sum.elim ca cc := by
    funext q
    rcases q with i | k <;> rfl
  unfold tailDenseObservableShiftField
  rw [hab, hac]
  exact hmeet

end

end GaloisForLFunctions.HTGeometry
