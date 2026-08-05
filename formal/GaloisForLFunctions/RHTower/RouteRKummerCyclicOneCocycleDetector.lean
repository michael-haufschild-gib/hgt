import GaloisForLFunctions.HTGeometry.LowDegreeHochschildFaceFlatness
import GaloisForLFunctions.RHTower.MobiusThetaSourceDaggerMinimalBoundaryLaw

/-!
# Kummer cyclic one-cocycle detector for Route R

The existing two-leg product residue detects the retained rational-adelic prime atom but is not a
Hochschild cocycle.  This module constructs the missing boundary-compatible detector.

The logarithmic rational-scaling weight defines a genuine derivation of the exact crossed product
and its minimal unitization.  Pairing this derivation with the zero-adele trace gives a cyclic
Hochschild one-cocycle.  It annihilates every pure degree-two Hochschild boundary and evaluates the
retained ordinary-prime atom exactly as `-log p`, hence never erases it.

No divisor, Xi zero, critical-line premise, completion, or fixed-ideal preservation is used.
-/

open Complex
open GaloisForLFunctions.RHTower
open scoped TensorProduct

namespace RHTower

noncomputable section

/-! ## Logarithmic Kummer derivation -/

/-- Archimedean logarithmic weight of a nonzero rational scaling. -/
def ccmRationalAdelicKummerLogWeight
    (k : CCMRationalAdelicScaling) : ℂ :=
  (Real.log |(((k.val : CCMRationalUnit) : ℚ) : ℝ)| : ℂ)

theorem ccmRationalAdelicKummerLogWeight_mul
    (k l : CCMRationalAdelicScaling) :
    ccmRationalAdelicKummerLogWeight (k * l) =
      ccmRationalAdelicKummerLogWeight k +
        ccmRationalAdelicKummerLogWeight l := by
  have hkq : (((k.val : CCMRationalUnit) : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast Units.ne_zero k.val
  have hlq : (((l.val : CCMRationalUnit) : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast Units.ne_zero l.val
  rw [ccmRationalAdelicKummerLogWeight,
    ccmRationalAdelicKummerLogWeight,
    ccmRationalAdelicKummerLogWeight,
    ccmRationalAdelicScaling_mul_val]
  push_cast
  rw [abs_mul, Real.log_mul (abs_ne_zero.mpr hkq) (abs_ne_zero.mpr hlq),
    Complex.ofReal_add]

theorem ccmRationalAdelicKummerLogWeight_inv
    (k : CCMRationalAdelicScaling) :
    ccmRationalAdelicKummerLogWeight k⁻¹ =
      -ccmRationalAdelicKummerLogWeight k := by
  rw [ccmRationalAdelicKummerLogWeight,
    ccmRationalAdelicKummerLogWeight,
    ccmRationalAdelicScaling_inv_val]
  push_cast
  rw [abs_inv, Real.log_inv, Complex.ofReal_neg]

/-- Coefficientwise logarithmic derivation on the exact nonunital crossed product. -/
def ccmRationalAdelicKummerDerivationNonunital :
    CCMRationalAdelicAlgebraicCrossedProduct →ₗ[ℂ]
      CCMRationalAdelicAlgebraicCrossedProduct :=
  Finsupp.lsum ℂ fun k =>
    ccmRationalAdelicKummerLogWeight k • Finsupp.lsingle k

@[simp]
theorem ccmRationalAdelicKummerDerivationNonunital_single
    (k : CCMRationalAdelicScaling)
    (a : CCMRationalAdelicBruhatSimpleTensor) :
    ccmRationalAdelicKummerDerivationNonunital (Finsupp.single k a) =
      Finsupp.single k (ccmRationalAdelicKummerLogWeight k • a) := by
  simp [ccmRationalAdelicKummerDerivationNonunital]

/-- Leibniz law on the exact nonunital rational-adelic crossed product. -/
theorem ccmRationalAdelicKummerDerivationNonunital_mul
    (F H : CCMRationalAdelicAlgebraicCrossedProduct) :
    ccmRationalAdelicKummerDerivationNonunital (F * H) =
      ccmRationalAdelicKummerDerivationNonunital F * H +
        F * ccmRationalAdelicKummerDerivationNonunital H := by
  have hpure (k : CCMRationalAdelicScaling)
      (a : CCMRationalAdelicBruhatSimpleTensor)
      (H : CCMRationalAdelicAlgebraicCrossedProduct) :
      ccmRationalAdelicKummerDerivationNonunital
          ((Finsupp.single k a : CCMRationalAdelicAlgebraicCrossedProduct) * H) =
        ccmRationalAdelicKummerDerivationNonunital (Finsupp.single k a) * H +
          Finsupp.single k a *
            ccmRationalAdelicKummerDerivationNonunital H := by
    induction H using Finsupp.induction with
    | zero => simp
    | @single_add l b H hl hb hH =>
        have hpure2 :
            ccmRationalAdelicKummerDerivationNonunital
                ((Finsupp.single k a :
                    CCMRationalAdelicAlgebraicCrossedProduct) *
                  Finsupp.single l b) =
              ccmRationalAdelicKummerDerivationNonunital
                    (Finsupp.single k a) * Finsupp.single l b +
                Finsupp.single k a *
                  ccmRationalAdelicKummerDerivationNonunital
                    (Finsupp.single l b) := by
          have hcore :
              ccmRationalAdelicKummerLogWeight (k * l) • (a * k • b) =
                (ccmRationalAdelicKummerLogWeight k • a) * (k • b) +
                  a * (k • (ccmRationalAdelicKummerLogWeight l • b)) := by
            rw [ccmRationalAdelicKummerLogWeight_mul, add_smul]
            congr 1
            · exact (smul_mul_assoc
                (ccmRationalAdelicKummerLogWeight k) a (k • b)).symm
            · change ccmRationalAdelicKummerLogWeight l •
                    (a * ccmRationalAdelicBruhatScaling k b) =
                  a * ccmRationalAdelicBruhatScaling k
                    (ccmRationalAdelicKummerLogWeight l • b)
              rw [(ccmRationalAdelicBruhatScaling k).map_smul]
              exact (mul_smul_comm
                (ccmRationalAdelicKummerLogWeight l) a
                (ccmRationalAdelicBruhatScaling k b)).symm
          simpa only [ccmRationalAdelicCrossedProduct_single_mul_single,
            ccmRationalAdelicKummerDerivationNonunital_single,
            Finsupp.single_add] using
              congrArg (Finsupp.single (k * l)) hcore
        simp only [ccmRationalAdelicCrossedProduct_mul_add, map_add,
          hpure2, hH]
        abel
  induction F using Finsupp.induction with
  | zero => simp
  | @single_add k a F hk ha hF =>
      simp only [ccmRationalAdelicCrossedProduct_add_mul, map_add,
        hpure, hF]
      abel

/-- Unitized logarithmic Kummer derivation; it kills the adjoined scalar unit. -/
def ccmRationalAdelicKummerDerivation :
    CCMRationalAdelicCyclicSourceAlgebra →ₗ[ℂ]
      CCMRationalAdelicCyclicSourceAlgebra where
  toFun x :=
    (ccmRationalAdelicKummerDerivationNonunital x.snd :
      CCMRationalAdelicCyclicSourceAlgebra)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Leibniz law on the actual minimal unitization used by the cyclic source. -/
theorem ccmRationalAdelicKummerDerivation_mul
    (x y : CCMRationalAdelicCyclicSourceAlgebra) :
    ccmRationalAdelicKummerDerivation (x * y) =
      ccmRationalAdelicKummerDerivation x * y +
        x * ccmRationalAdelicKummerDerivation y := by
  change
    (ccmRationalAdelicKummerDerivationNonunital (x * y).snd :
        CCMRationalAdelicCyclicSourceAlgebra) =
      (ccmRationalAdelicKummerDerivationNonunital x.snd :
          CCMRationalAdelicCyclicSourceAlgebra) * y +
        x * (ccmRationalAdelicKummerDerivationNonunital y.snd :
          CCMRationalAdelicCyclicSourceAlgebra)
  apply Unitization.ext
  · simp
  · simp only [Unitization.snd_add, Unitization.snd_mul]
    simp
    rw [ccmRationalAdelicKummerDerivationNonunital_mul]
    module

/-- The zero-adele trace kills the logarithmic derivation: the only coefficient it reads has
scaling weight `log |1| = 0`. -/
theorem ccmRationalAdelicEpsilonZeroNonunital_kummerDerivation
    (F : CCMRationalAdelicAlgebraicCrossedProduct) :
    ccmRationalAdelicEpsilonZeroNonunital
        (ccmRationalAdelicKummerDerivationNonunital F) = 0 := by
  induction F using Finsupp.induction with
  | zero => simp
  | @single_add k a F hk ha hF =>
      rw [map_add, map_add, hF, add_zero]
      by_cases hk1 : k = 1
      · subst k
        rw [ccmRationalAdelicKummerDerivationNonunital_single]
        simp [ccmRationalAdelicKummerLogWeight]
      · rw [ccmRationalAdelicKummerDerivationNonunital_single]
        simp [ccmRationalAdelicEpsilonZeroNonunital_single, hk1]

theorem ccmRationalAdelicEpsilonZero_kummerDerivation
    (x : CCMRationalAdelicCyclicSourceAlgebra) :
    ccmRationalAdelicEpsilonZero
        (ccmRationalAdelicKummerDerivation x) = 0 := by
  change ccmRationalAdelicEpsilonZero
    (ccmRationalAdelicKummerDerivationNonunital x.snd :
      CCMRationalAdelicCyclicSourceAlgebra) = 0
  rw [ccmRationalAdelicEpsilonZero_inr]
  exact ccmRationalAdelicEpsilonZeroNonunital_kummerDerivation x.snd

/-! ## Genuine cyclic one-cocycle -/

private theorem ccmRationalAdelicCyclicSource_smul_mul
    (c : ℂ) (a b : CCMRationalAdelicCyclicSourceAlgebra) :
    (c • a) * b = c • (a * b) := by
  apply Unitization.ext
  · change (c * a.fst) * b.fst = c * (a.fst * b.fst)
    ring
  · change
      (c * a.fst) • b.snd + b.fst • (c • a.snd) +
          (c • a.snd) * b.snd =
        c • (a.fst • b.snd + b.fst • a.snd + a.snd * b.snd)
    rw [smul_mul_assoc]
    module

private theorem ccmRationalAdelicCyclicSource_mul_smul
    (c : ℂ) (a b : CCMRationalAdelicCyclicSourceAlgebra) :
    a * (c • b) = c • (a * b) := by
  apply Unitization.ext
  · change a.fst * (c * b.fst) = c * (a.fst * b.fst)
    ring
  · change
      a.fst • (c • b.snd) + (c * b.fst) • a.snd +
          a.snd * (c • b.snd) =
        c • (a.fst • b.snd + b.fst • a.snd + a.snd * b.snd)
    rw [mul_smul_comm]
    module

/-- Pure-tuple form of the Kummer cyclic one-cocycle
`(a₀,a₁) ↦ ε₀(a₀ ∂log(a₁))`. -/
def ccmRationalAdelicKummerCyclicOneCocycleTuple
    (x : Fin 2 → CCMRationalAdelicCyclicSourceAlgebra) : ℂ :=
  ccmRationalAdelicEpsilonZero
    (x 0 * ccmRationalAdelicKummerDerivation (x 1))

/-- Multilinear form defining the Kummer one-cocycle. -/
def ccmRationalAdelicKummerCyclicOneCocycleMultilinear :
    MultilinearMap ℂ
      (fun _ : Fin 2 => CCMRationalAdelicCyclicSourceAlgebra) ℂ :=
  MultilinearMap.mk' ccmRationalAdelicKummerCyclicOneCocycleTuple
    (by
      intro x j a b
      fin_cases j <;>
        simp [ccmRationalAdelicKummerCyclicOneCocycleTuple,
          Function.update, add_mul, mul_add])
    (by
      intro x j c a
      fin_cases j
      · simp [ccmRationalAdelicKummerCyclicOneCocycleTuple,
          Function.update]
        rw [ccmRationalAdelicCyclicSource_smul_mul, map_smul]
        rfl
      · simp [ccmRationalAdelicKummerCyclicOneCocycleTuple,
          Function.update]
        rw [ccmRationalAdelicCyclicSource_mul_smul c (x 0)
          (ccmRationalAdelicKummerDerivation a), map_smul]
        rfl)

/-- Linear Kummer cyclic one-cocycle on the genuine degree-one cyclic tensor source. -/
def ccmRationalAdelicKummerCyclicOneCocycle :
    CCMRationalAdelicDegreeOneCyclicSource →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ccmRationalAdelicKummerCyclicOneCocycleMultilinear

@[simp]
theorem ccmRationalAdelicKummerCyclicOneCocycle_tprod
    (x : Fin 2 → CCMRationalAdelicCyclicSourceAlgebra) :
    ccmRationalAdelicKummerCyclicOneCocycle
        (PiTensorProduct.tprod ℂ x) =
      ccmRationalAdelicEpsilonZero
        (x 0 * ccmRationalAdelicKummerDerivation (x 1)) := by
  simp [ccmRationalAdelicKummerCyclicOneCocycle,
    ccmRationalAdelicKummerCyclicOneCocycleMultilinear,
    ccmRationalAdelicKummerCyclicOneCocycleTuple]

/-- Cyclic antisymmetry on pure degree-one tensors. -/
theorem ccmRationalAdelicKummerCyclicOneCocycle_cyclic
    (a b : CCMRationalAdelicCyclicSourceAlgebra) :
    ccmRationalAdelicEpsilonZero
        (a * ccmRationalAdelicKummerDerivation b) =
      -ccmRationalAdelicEpsilonZero
        (b * ccmRationalAdelicKummerDerivation a) := by
  have hzero :
      ccmRationalAdelicEpsilonZero
          (ccmRationalAdelicKummerDerivation (a * b)) = 0 :=
    ccmRationalAdelicEpsilonZero_kummerDerivation (a * b)
  rw [ccmRationalAdelicKummerDerivation_mul] at hzero
  rw [map_add, ccmRationalAdelicEpsilonZero_isTrace
    (ccmRationalAdelicKummerDerivation a) b] at hzero
  linear_combination hzero

/-- The Kummer cocycle annihilates every pure degree-two Hochschild boundary
`ab ⊗ c - a ⊗ bc + ca ⊗ b`. -/
theorem ccmRationalAdelicKummerCyclicOneCocycle_boundaryTwoPure
    (a b c : CCMRationalAdelicCyclicSourceAlgebra) :
    ccmRationalAdelicEpsilonZero
          ((a * b) * ccmRationalAdelicKummerDerivation c) -
        ccmRationalAdelicEpsilonZero
          (a * ccmRationalAdelicKummerDerivation (b * c)) +
        ccmRationalAdelicEpsilonZero
          ((c * a) * ccmRationalAdelicKummerDerivation b) = 0 := by
  rw [ccmRationalAdelicKummerDerivation_mul, mul_add, map_add]
  have htrace :
      ccmRationalAdelicEpsilonZero
          (a * (ccmRationalAdelicKummerDerivation b * c)) =
        ccmRationalAdelicEpsilonZero
          ((c * a) * ccmRationalAdelicKummerDerivation b) := by
    calc
      ccmRationalAdelicEpsilonZero
          (a * (ccmRationalAdelicKummerDerivation b * c)) =
          ccmRationalAdelicEpsilonZero
            ((a * ccmRationalAdelicKummerDerivation b) * c) := by
        rw [mul_assoc]
      _ = ccmRationalAdelicEpsilonZero
          (c * (a * ccmRationalAdelicKummerDerivation b)) :=
        ccmRationalAdelicEpsilonZero_isTrace
          (a * ccmRationalAdelicKummerDerivation b) c
      _ = ccmRationalAdelicEpsilonZero
          ((c * a) * ccmRationalAdelicKummerDerivation b) := by
        rw [mul_assoc]
  rw [htrace]
  simp only [mul_assoc]
  ring

/-! ## Exact retained-prime evaluation -/

theorem ccmRationalAdelicKummerLogWeight_primeScaling
    (p : Nat.Primes) :
    ccmRationalAdelicKummerLogWeight
        (ccmRationalAdelicPrimeScaling p) =
      (Real.log (p : ℝ) : ℂ) := by
  rw [ccmRationalAdelicKummerLogWeight,
    ccmRationalAdelicPrimeScaling]
  change (Real.log |(p : ℝ)| : ℂ) = _
  rw [abs_of_nonneg]
  exact_mod_cast Nat.zero_le (p : ℕ)

theorem ccmRationalAdelicKummerDerivation_primeBackward
    (p : Nat.Primes) :
    ccmRationalAdelicKummerDerivation
        (ccmRationalAdelicPrimeCycleBackward p :
          CCMRationalAdelicCyclicSourceAlgebra) =
      -(Real.log (p : ℝ) : ℂ) •
        (ccmRationalAdelicPrimeCycleBackward p :
          CCMRationalAdelicCyclicSourceAlgebra) := by
  change
    (ccmRationalAdelicKummerDerivationNonunital
        (ccmRationalAdelicPrimeCycleBackward p) :
      CCMRationalAdelicCyclicSourceAlgebra) = _
  rw [ccmRationalAdelicPrimeCycleBackward,
    ccmRationalAdelicKummerDerivationNonunital_single,
    ccmRationalAdelicKummerLogWeight_inv,
    ccmRationalAdelicKummerLogWeight_primeScaling]
  apply Unitization.ext <;> simp

theorem ccmRationalAdelicPrimeForwardBackward_epsilonZero
    (p : Nat.Primes) :
    ccmRationalAdelicEpsilonZero
        ((ccmRationalAdelicPrimeCycleForward p :
            CCMRationalAdelicCyclicSourceAlgebra) *
          (ccmRationalAdelicPrimeCycleBackward p :
            CCMRationalAdelicCyclicSourceAlgebra)) = 1 := by
  rw [ccmRationalAdelicCyclicSource_inr_mul]
  rw [ccmRationalAdelicPrimeCycleForward,
    ccmRationalAdelicPrimeCycleBackward,
    ccmRationalAdelicCrossedProduct_single_mul_single]
  rw [ccmRationalAdelicEpsilonZero_inr,
    ccmRationalAdelicEpsilonZeroNonunital_single]
  simp only [mul_inv_cancel, if_true]
  rw [ccmRationalAdelicBruhatZeroEval_mul,
    ccmRationalAdelicBruhatZeroEval_smul]
  simp

/-- Exact cyclic-cocycle value of the retained ordinary-prime atom. -/
theorem ccmRationalAdelicKummerCyclicOneCocycle_primeAtom
    (p : Nat.Primes) :
    ccmRationalAdelicKummerCyclicOneCocycle
        (ccmRationalAdelicOrdinaryPrimeCycleAtom p) =
      -(Real.log (p : ℝ) : ℂ) := by
  rw [ccmRationalAdelicOrdinaryPrimeCycleAtom]
  rw [ccmRationalAdelicKummerCyclicOneCocycle_tprod]
  change ccmRationalAdelicEpsilonZero
      ((ccmRationalAdelicPrimeCycleForward p :
          CCMRationalAdelicCyclicSourceAlgebra) *
        ccmRationalAdelicKummerDerivation
          (ccmRationalAdelicPrimeCycleBackward p :
            CCMRationalAdelicCyclicSourceAlgebra)) = _
  rw [ccmRationalAdelicKummerDerivation_primeBackward,
    ccmRationalAdelicCyclicSource_mul_smul, map_smul,
    ccmRationalAdelicPrimeForwardBackward_epsilonZero,
    smul_eq_mul, mul_one]

/-- The genuine cyclic detector retains every ordinary-prime source atom. -/
theorem ccmRationalAdelicKummerCyclicOneCocycle_primeAtom_ne_zero
    (p : Nat.Primes) :
    ccmRationalAdelicKummerCyclicOneCocycle
        (ccmRationalAdelicOrdinaryPrimeCycleAtom p) ≠ 0 := by
  rw [ccmRationalAdelicKummerCyclicOneCocycle_primeAtom,
    neg_ne_zero, Complex.ofReal_ne_zero]
  exact Real.log_ne_zero_of_pos_of_ne_one
    (by exact_mod_cast p.2.pos) (by exact_mod_cast p.2.ne_one)

end

end RHTower
