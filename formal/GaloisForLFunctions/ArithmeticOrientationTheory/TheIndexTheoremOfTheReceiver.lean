import GaloisForLFunctions.ArithmeticOrientationTheory.TheEffectivityConeFromSections
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DoubleZeroKernelsAndLogarithmicSmoothPowerAtThePole
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheReceiverReadsTheZeroDivisorOfZetaOnTheOscillatingSpectrum
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheOscillatingSmoothPowerIsPaidExactlyAtTheZerosOfZeta

/-!
# The index theorem of the receiver: pole-order section counts and the node-divisor Euler characteristic

This module resolves Entry 9 of the Arithmetic Orientation Theory programme:
> *"The pole law of the receiver reads the order of a pole, and the Hodge defect is the number of
> right zeros. Prove that the order read by the receiver is a count of sections, and compute the
> Euler characteristic of the node divisor from the ledger."*

## Main results

1. **General vanishing characterization of `h⁰` and discrete Euler characteristic
   (`h0_eq_card_iff_eq_zero`, `discreteEulerChar_eq_card_sub`):**
   For any linear reading `A : Matrix m n ℂ`, `h0 A = Fintype.card n ↔ A = 0`, and its discrete
   Euler characteristic `discreteEulerChar A := (h0 A : ℤ) - (h1 A : ℤ)` equals
   `(Fintype.card n : ℤ) - (Fintype.card m : ℤ)` (degrees of freedom minus nodes).

2. **The pole law of the receiver is a count of sections (`poleJetMatrix`,
   `principalPartReadingOne`, `principalPartReadingTwo`):**
   For a horizon `J : ℕ`, drift exponent `ε : ℝ`, and pole order `r : ℕ`, the `r × J` matrix
   `poleJetMatrix J ε r` evaluates the Taylor jet `(poleValue, -poleSlope, …)` at `s = 1 - ε` on
   finite kernels `k` supported on `[1, J]`, while `principalPartReadingOne k J ε` (`1 × 1`) and
   `principalPartReadingTwo k J ε` (`2 × 2`) evaluate `k`'s pole jet on the `r`-dimensional
   principal-part space of the pole:
   - **Order-1 pole (`d^{-ε}`):** For `0 < ε ≤ 1/2` and `k` supported on `[1, J]`,
     `ReceiverBounded (dirichletConv k (smoothPower ε))` holds iff `kernelVec k J` is a section of
     `poleJetMatrix J ε 1`, and iff `h0 (principalPartReadingOne k J ε) = 1`. For `1 ≤ J`,
     `poleJetMatrix J ε 1` has full row rank `1`, `h1 = 0`, `h0 = J - 1`, and section codimension
     `J - h0 (poleJetMatrix J ε 1) = 1`.
   - **Order-2 pole (`log d · d^{-ε}`):** For `0 < ε ≤ 1/2` and `k` supported on `[1, J]`,
     `ReceiverBounded (dirichletConv k (logWeight 1 * smoothPower ε))` holds iff `kernelVec k J` is
     a section of `poleJetMatrix J ε 2`, and iff `h0 (principalPartReadingTwo k J ε) = 2`. For
     `2 ≤ J`, `poleJetMatrix J ε 2` has full row rank `2`, `h1 = 0`, `h0 = J - 2`, and section
     codimension `J - h0 (poleJetMatrix J ε 2) = 2`. Increasing the pole order from `1` to `2`
     drops `h0` by `1` (`h0 (poleJetMatrix J ε 1) - h0 (poleJetMatrix J ε 2) = 1`), witnessed by
     `fermiKernel ε` at `J = 2` and `doubleFermiKernel ε` at `J = 3`.

3. **The zero-order receiver law is a count of sections (`zetaJetDiagReading`,
   `receiverBounded_logPowerCosine_iff_h0_eq`):**
   At `ρ = 1 - ε + i t` (`0 < ε ≤ 1/2`, `t > 0`), the `(k + 1) × (k + 1)` diagonal jet reading
   `zetaJetDiagReading ε t (k + 1)` has diagonal entries `ζ^{(i)}(ρ)` (`i ≤ k`). The oscillating
   log-power probe `logPowerCosine ε t k` has bounded receiver iff
   `h0 (zetaJetDiagReading ε t (k + 1)) = k + 1`.

4. **Euler characteristic of the node divisor computed from the ledger (`nodeDivisorEulerChar`,
   `nodeDivisorEulerChar_integral_from_ledger`):**
   On the logarithmic horizon box `[0, s]`, the continuous Euler characteristic of the prime-power
   node divisor is `nodeDivisorEulerChar s := polarBoxDoF s - primeNodeCount s`, which equals
   `chebyshevTwoPoleDefect s = e^s + s - 1 - ψ(e^s)`. On `scalingSubsurface (oddRealTestsAt r)`,
   the reflected prime-polar ledger computes the lag-weighted integral of `nodeDivisorEulerChar`
   on `(0, 2r]` directly as the archimedean gauge budget (`surplusPool + crossingPotentialTerm +
   gaugeRemainder`) minus the Castelnuovo–Severi defect `(scalingSubsurface (oddRealTestsAt r)).defect x x`.

5. **The Master Receiver Index Theorem and Extended Dictionary (`receiver_index_theorem`,
   `receiverIndexAndSectionConeDictionary_tfae`):**
   Unites the pole-order section law, the zero-order section law, the Pontryagin–Haynsworth
   right-zero Hodge-defect law, the node-divisor Euler characteristic ledger identity, and the
   section effectivity cone `E = {x : h⁰(x) ≥ 1}` into one dictionary.
-/

open Complex Matrix Finset Set MeasureTheory
open scoped BigOperators
open Zeta23 GaloisForLFunctions.ArithmeticCastelnuovoSeveri
  GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticIncidencePositivity
  GaloisForLFunctions.TransHorizonIncidenceMechanics
  GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
  GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ### 1. General section-count characterization of vanishing and discrete Euler characteristic -/

/-- For any `m × n` complex matrix `A`, the section count `h0 A` equals the full column dimension
`Fintype.card n` if and only if `A = 0`. -/
theorem h0_eq_card_iff_eq_zero {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) :
    h0 A = Fintype.card n ↔ A = 0 := by
  constructor
  · intro h
    have htop : LinearMap.ker A.mulVecLin = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [← h0, h, Module.finrank_pi])
    ext i j
    have hj : Pi.single j (1 : ℂ) ∈ LinearMap.ker A.mulVecLin := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at hj
    exact congrFun hj i
  · rintro rfl
    have h := h0_add_rank (0 : Matrix m n ℂ)
    rw [Matrix.rank_zero, add_zero] at h
    exact h

/-- The discrete Euler characteristic `χ(A) = h⁰(A) - h¹(A)` of a linear reading `A : Matrix m n ℂ`. -/
def discreteEulerChar {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : ℤ :=
  (h0 A : ℤ) - (h1 A : ℤ)

/-- **Discrete Riemann–Roch for a linear reading:** `χ(A) = #degrees_of_freedom - #nodes`. -/
theorem discreteEulerChar_eq_card_sub {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    discreteEulerChar A = (Fintype.card n : ℤ) - (Fintype.card m : ℤ) :=
  h0_sub_h1 A

/-- If `A.mulVecLin` is surjective, then `A.rank = Fintype.card m`, `h1 A = 0`, and
`h0 A = Fintype.card n - Fintype.card m`. -/
theorem rank_and_h0_of_surjective {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (hsurj : Function.Surjective A.mulVecLin) :
    A.rank = Fintype.card m ∧ h1 A = 0 ∧ h0 A = Fintype.card n - Fintype.card m := by
  have hr : A.rank = Fintype.card m := by
    rw [Matrix.rank, LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_pi]
  have hh1 : h1 A = 0 := by
    unfold h1
    rw [hr, Nat.sub_self]
  have hh0 : h0 A = Fintype.card n - Fintype.card m := by
    have h := h0_add_rank A
    rw [hr] at h
    omega
  exact ⟨hr, hh1, hh0⟩

/-! ### 2. The pole-jet reading matrix and the pole law of the receiver as a count of sections -/

/-- Reindexing a sum over `Fin J` by `j ↦ j.1 + 1` gives the sum over `Icc 1 J`. -/
theorem sum_fin_succ_eq_sum_Icc {α : Type*} [AddCommMonoid α] (J : ℕ) (f : ℕ → α) :
    (∑ j : Fin J, f (j.1 + 1)) = ∑ d ∈ Icc 1 J, f d := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Fin.sum_univ_castSucc, ih, Fin.val_last,
      Finset.sum_Icc_succ_top (Nat.le_add_left 1 J)]
    rfl

/-- The `r × J` **pole-jet reading matrix** at horizon `J`, drift exponent `ε`, and pole order `r`:
its `(m, j)` entry is `(j + 1)^{-(1 - ε)} (log (j + 1))^m`. -/
def poleJetMatrix (J : ℕ) (ε : ℝ) (r : ℕ) : Matrix (Fin r) (Fin J) ℂ :=
  fun m j =>
    (((j.1 + 1 : ℝ) ^ (-(1 - ε)) * Real.log (j.1 + 1 : ℝ) ^ m.1 : ℝ) : ℂ)

/-- The vector in `Fin J → ℂ` representing a kernel `k : ℕ → ℝ` restricted to `Icc 1 J`. -/
def kernelVec (k : ℕ → ℝ) (J : ℕ) : Fin J → ℂ :=
  fun j => (k (j.1 + 1) : ℂ)

/-- At row `m`, `(poleJetMatrix J ε r).mulVec (kernelVec k J)` is the `m`-th logarithmic pole moment
`∑_{d ∈ Icc 1 J} k(d) d^{-(1-ε)} (log d)^m`. -/
theorem poleJetMatrix_mulVec_kernelVec (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) {r : ℕ} (m : Fin r) :
    ((poleJetMatrix J ε r).mulVec (kernelVec k J)) m =
      ((∑ d ∈ Icc 1 J, k d * (d : ℝ) ^ (-(1 - ε)) * Real.log (d : ℝ) ^ m.1 : ℝ) : ℂ) := by
  simp only [Matrix.mulVec, dotProduct, poleJetMatrix, kernelVec]
  rw [← sum_fin_succ_eq_sum_Icc J (fun d => k d * (d : ℝ) ^ (-(1 - ε)) * Real.log (d : ℝ) ^ m.1),
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-- Row `0` of `(poleJetMatrix J ε r).mulVec (kernelVec k J)` equals `poleValue k J ε`. -/
theorem poleJetMatrix_mulVec_zero_eq_poleValue (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) {r : ℕ}
    (m : Fin r) (hm : m.1 = 0) :
    ((poleJetMatrix J ε r).mulVec (kernelVec k J)) m = (poleValue k J ε : ℂ) := by
  rw [poleJetMatrix_mulVec_kernelVec, hm, poleValue]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [pow_zero, mul_one]

/-- Row `1` of `(poleJetMatrix J ε r).mulVec (kernelVec k J)` equals `-poleSlope k J ε`. -/
theorem poleJetMatrix_mulVec_one_eq_neg_poleSlope (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) {r : ℕ}
    (m : Fin r) (hm : m.1 = 1) :
    ((poleJetMatrix J ε r).mulVec (kernelVec k J)) m = (-poleSlope k J ε : ℂ) := by
  rw [poleJetMatrix_mulVec_kernelVec, hm, poleSlope, neg_neg]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [pow_one]
  ring

/-- `kernelVec k J` is a section of `poleJetMatrix J ε 1` iff `poleValue k J ε = 0`. -/
theorem mem_ker_poleJetMatrix_one_iff (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) :
    kernelVec k J ∈ LinearMap.ker (poleJetMatrix J ε 1).mulVecLin ↔ poleValue k J ε = 0 := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Fin.forall_fin_one,
    poleJetMatrix_mulVec_zero_eq_poleValue k J ε 0 rfl, Pi.zero_apply, Complex.ofReal_eq_zero]

/-- `kernelVec k J` is a section of `poleJetMatrix J ε 2` iff `poleValue k J ε = 0` and
`poleSlope k J ε = 0`. -/
theorem mem_ker_poleJetMatrix_two_iff (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) :
    kernelVec k J ∈ LinearMap.ker (poleJetMatrix J ε 2).mulVecLin ↔
      poleValue k J ε = 0 ∧ poleSlope k J ε = 0 := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Fin.forall_fin_two,
    poleJetMatrix_mulVec_zero_eq_poleValue k J ε 0 rfl,
    poleJetMatrix_mulVec_one_eq_neg_poleSlope k J ε 1 rfl,
    Pi.zero_apply, Complex.ofReal_eq_zero, Complex.ofReal_eq_zero, neg_eq_zero]

/-- The `1 × 1` principal-part reading of a kernel `k` on an order-1 pole at `s = 1 - ε`. -/
def principalPartReadingOne (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => (poleValue k J ε : ℂ)

/-- The `2 × 2` diagonal principal-part reading of a kernel `k` on an order-2 pole at `s = 1 - ε`. -/
def principalPartReadingTwo (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(poleValue k J ε : ℂ), (poleSlope k J ε : ℂ)]

/-- `h0 (principalPartReadingOne k J ε) = 1` iff `poleValue k J ε = 0`. -/
theorem h0_principalPartReadingOne_eq_one_iff (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) :
    h0 (principalPartReadingOne k J ε) = 1 ↔ poleValue k J ε = 0 := by
  have h := h0_eq_card_iff_eq_zero (principalPartReadingOne k J ε)
  rw [Fintype.card_fin] at h
  rw [h]
  constructor
  · intro h0
    have h00 := congrFun (congrFun h0 0) 0
    simpa [principalPartReadingOne] using h00
  · intro hp
    ext i j
    simp [principalPartReadingOne, hp]

/-- `h0 (principalPartReadingTwo k J ε) = 2` iff `poleValue k J ε = 0 ∧ poleSlope k J ε = 0`. -/
theorem h0_principalPartReadingTwo_eq_two_iff (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) :
    h0 (principalPartReadingTwo k J ε) = 2 ↔ poleValue k J ε = 0 ∧ poleSlope k J ε = 0 := by
  have h := h0_eq_card_iff_eq_zero (principalPartReadingTwo k J ε)
  rw [Fintype.card_fin] at h
  rw [h]
  constructor
  · intro h0
    have h00 := congrFun (congrFun h0 0) 0
    have h11 := congrFun (congrFun h0 1) 1
    simp only [principalPartReadingTwo, Matrix.diagonal_apply_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.zero_apply, Complex.ofReal_eq_zero] at h00 h11
    exact ⟨h00, h11⟩
  · rintro ⟨hv, hs⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [principalPartReadingTwo, hv, hs]

/-- **Order-1 pole section law of the receiver:** for `0 < ε ≤ 1/2` and a kernel `k` supported on
`[1, J]`, the convolved smooth power `k ⋆ d^{-ε}` has bounded receiver iff `kernelVec k J` is a
section of `poleJetMatrix J ε 1`, and iff `h0 (principalPartReadingOne k J ε) = 1`. -/
theorem receiverBounded_orderOnePole_iff_sections {k : ℕ → ℝ} {J : ℕ}
    (hk0 : k 0 = 0) (hkJ : ∀ d : ℕ, J < d → k d = 0) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (ReceiverBounded (dirichletConv k (smoothPower ε)) ↔
      kernelVec k J ∈ LinearMap.ker (poleJetMatrix J ε 1).mulVecLin) ∧
    (ReceiverBounded (dirichletConv k (smoothPower ε)) ↔
      h0 (principalPartReadingOne k J ε) = 1) := by
  rw [receiverBounded_dirichletConv_smoothPower_iff hk0 hkJ hε hε2,
    mem_ker_poleJetMatrix_one_iff, h0_principalPartReadingOne_eq_one_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **Order-2 pole section law of the receiver:** for `0 < ε ≤ 1/2` and a kernel `k` supported on
`[1, J]`, the convolved logarithmic smooth power `k ⋆ (log d · d^{-ε})` has bounded receiver iff
`kernelVec k J` is a section of `poleJetMatrix J ε 2`, and iff
`h0 (principalPartReadingTwo k J ε) = 2`. -/
theorem receiverBounded_orderTwoPole_iff_sections {k : ℕ → ℝ} {J : ℕ}
    (hk0 : k 0 = 0) (hkJ : ∀ d : ℕ, J < d → k d = 0) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (ReceiverBounded (dirichletConv k (logWeight 1 * smoothPower ε)) ↔
      kernelVec k J ∈ LinearMap.ker (poleJetMatrix J ε 2).mulVecLin) ∧
    (ReceiverBounded (dirichletConv k (logWeight 1 * smoothPower ε)) ↔
      h0 (principalPartReadingTwo k J ε) = 2) := by
  rw [receiverBounded_dirichletConv_logWeight_unit_iff hk0 hkJ hε hε2,
    mem_ker_poleJetMatrix_two_iff, h0_principalPartReadingTwo_eq_two_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- For `1 ≤ J`, `(poleJetMatrix J ε 1).mulVecLin` is surjective. -/
theorem poleJetMatrix_one_surjective {J : ℕ} (hJ : 1 ≤ J) (ε : ℝ) :
    Function.Surjective (poleJetMatrix J ε 1).mulVecLin := by
  intro y
  let j₀ : Fin J := ⟨0, hJ⟩
  refine ⟨Pi.single j₀ (y 0), ?_⟩
  ext i
  rw [Fin.eq_zero i, Matrix.mulVecLin_apply, Matrix.mulVec_single, Pi.single_eq_same]
  simp [poleJetMatrix, j₀]

/-- **Rank, `h¹`, `h⁰`, and section codimension for the order-1 pole-jet reading (`1 ≤ J`):**
`rank = 1`, `h¹ = 0`, `h⁰ = J - 1`, and `J - h⁰ = 1`. -/
theorem poleJetMatrix_one_rank_h1_h0 {J : ℕ} (hJ : 1 ≤ J) (ε : ℝ) :
    (poleJetMatrix J ε 1).rank = 1 ∧
      h1 (poleJetMatrix J ε 1) = 0 ∧
      h0 (poleJetMatrix J ε 1) = J - 1 ∧
      J - h0 (poleJetMatrix J ε 1) = 1 ∧
      discreteEulerChar (poleJetMatrix J ε 1) = (J : ℤ) - 1 := by
  obtain ⟨hr, hh1, hh0⟩ := rank_and_h0_of_surjective (poleJetMatrix J ε 1)
    (poleJetMatrix_one_surjective hJ ε)
  simp only [Fintype.card_fin] at hr hh0
  have hchi := discreteEulerChar_eq_card_sub (poleJetMatrix J ε 1)
  simp only [Fintype.card_fin] at hchi
  refine ⟨hr, hh1, hh0, by omega, hchi⟩

/-- For `2 ≤ J`, `(poleJetMatrix J ε 2).mulVecLin` is surjective. -/
theorem poleJetMatrix_two_surjective {J : ℕ} (hJ : 2 ≤ J) (ε : ℝ) :
    Function.Surjective (poleJetMatrix J ε 2).mulVecLin := by
  intro y
  let j₀ : Fin J := ⟨0, by omega⟩
  let j₁ : Fin J := ⟨1, hJ⟩
  set a : ℂ := (((2 : ℝ) ^ (-(1 - ε)) : ℝ) : ℂ)
  set b : ℂ := (((2 : ℝ) ^ (-(1 - ε)) * Real.log 2 : ℝ) : ℂ)
  have hb_real : (2 : ℝ) ^ (-(1 - ε)) * Real.log 2 ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos (by norm_num) _).ne' (Real.log_pos (by norm_num)).ne'
  have hb : b ≠ 0 := Complex.ofReal_ne_zero.mpr hb_real
  let c₁ : ℂ := y 1 / b
  let c₀ : ℂ := y 0 - a * c₁
  refine ⟨Pi.single j₀ c₀ + Pi.single j₁ c₁, ?_⟩
  have h00 : poleJetMatrix J ε 2 0 j₀ = 1 := by simp [poleJetMatrix, j₀]
  have h10 : poleJetMatrix J ε 2 1 j₀ = 0 := by simp [poleJetMatrix, j₀]
  have h01 : poleJetMatrix J ε 2 0 j₁ = a := by
    simp only [poleJetMatrix, j₁, Fin.val_zero, pow_zero, mul_one, a]
    norm_num
  have h11 : poleJetMatrix J ε 2 1 j₁ = b := by
    simp only [poleJetMatrix, j₁, Fin.val_one, pow_one, b]
    norm_num
  ext i
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_add, Pi.add_apply,
    Matrix.mulVec_single, Matrix.mulVec_single, Pi.single_eq_same, Pi.single_eq_same]
  fin_cases i
  · change poleJetMatrix J ε 2 0 j₀ * c₀ + poleJetMatrix J ε 2 0 j₁ * c₁ = y 0
    rw [h00, h01]
    simp only [c₀]
    ring
  · change poleJetMatrix J ε 2 1 j₀ * c₀ + poleJetMatrix J ε 2 1 j₁ * c₁ = y 1
    rw [h10, h11, zero_mul, zero_add]
    exact mul_div_cancel₀ (y 1) hb

/-- **Rank, `h¹`, `h⁰`, and section codimension for the order-2 pole-jet reading (`2 ≤ J`):**
`rank = 2`, `h¹ = 0`, `h⁰ = J - 2`, and `J - h⁰ = 2`. -/
theorem poleJetMatrix_two_rank_h1_h0 {J : ℕ} (hJ : 2 ≤ J) (ε : ℝ) :
    (poleJetMatrix J ε 2).rank = 2 ∧
      h1 (poleJetMatrix J ε 2) = 0 ∧
      h0 (poleJetMatrix J ε 2) = J - 2 ∧
      J - h0 (poleJetMatrix J ε 2) = 2 ∧
      discreteEulerChar (poleJetMatrix J ε 2) = (J : ℤ) - 2 := by
  obtain ⟨hr, hh1, hh0⟩ := rank_and_h0_of_surjective (poleJetMatrix J ε 2)
    (poleJetMatrix_two_surjective hJ ε)
  simp only [Fintype.card_fin] at hr hh0
  have hchi := discreteEulerChar_eq_card_sub (poleJetMatrix J ε 2)
  simp only [Fintype.card_fin] at hchi
  refine ⟨hr, hh1, hh0, by omega, hchi⟩

/-- **Section-count drop from a simple pole to a double pole:** for `2 ≤ J`, increasing the pole
order from `1` to `2` drops the kernel section count `h⁰` by exactly `1`. -/
theorem h0_poleJetMatrix_one_sub_two {J : ℕ} (hJ : 2 ≤ J) (ε : ℝ) :
    h0 (poleJetMatrix J ε 1) - h0 (poleJetMatrix J ε 2) = 1 := by
  rw [(poleJetMatrix_one_rank_h1_h0 (by omega) ε).2.2.1,
    (poleJetMatrix_two_rank_h1_h0 hJ ε).2.2.1]
  omega

/-- At horizon `J = 2`, the first-order Fermi kernel `fermiKernel ε` lies in the 1-dimensional
section space of `poleJetMatrix 2 ε 1` (`h⁰ = 1`) and outside the 0-dimensional section space of
`poleJetMatrix 2 ε 2` (`h⁰ = 0`), while at horizon `J = 3`, `doubleFermiKernel ε` lies in the
1-dimensional section space of `poleJetMatrix 3 ε 2` (`h⁰ = 1`). -/
theorem fermi_and_doubleFermi_poleJetSections (ε : ℝ) :
    kernelVec (fermiKernel ε) 2 ∈ LinearMap.ker (poleJetMatrix 2 ε 1).mulVecLin ∧
      kernelVec (fermiKernel ε) 2 ∉ LinearMap.ker (poleJetMatrix 2 ε 2).mulVecLin ∧
      kernelVec (doubleFermiKernel ε) 3 ∈ LinearMap.ker (poleJetMatrix 3 ε 2).mulVecLin := by
  rw [mem_ker_poleJetMatrix_one_iff, mem_ker_poleJetMatrix_two_iff, mem_ker_poleJetMatrix_two_iff]
  exact ⟨poleValue_fermiKernel ε,
    fun h => poleSlope_fermiKernel_ne_zero ε h.2,
    ⟨poleValue_doubleFermiKernel ε, poleSlope_doubleFermiKernel ε⟩⟩

/-! ### 3. The zero-order receiver law as a count of sections -/

/-- The `m × m` diagonal zeta-jet reading at `ρ = 1 - ε + i t`, with diagonal entries
`ζ^{(i)}(1 - ε + i t)` for `i : Fin m`. -/
def zetaJetDiagReading (ε t : ℝ) (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.diagonal fun i : Fin m =>
    iteratedDeriv i.1 riemannZeta (((1 - ε : ℝ) : ℂ) + (t : ℂ) * I)

/-- `h0 (zetaJetDiagReading ε t (k + 1)) = k + 1` iff `ζ^{(i)}(1 - ε + i t) = 0` for all `i ≤ k`. -/
theorem h0_zetaJetDiagReading_eq_iff (ε t : ℝ) (k : ℕ) :
    h0 (zetaJetDiagReading ε t (k + 1)) = k + 1 ↔
      ∀ i ≤ k, iteratedDeriv i riemannZeta (((1 - ε : ℝ) : ℂ) + (t : ℂ) * I) = 0 := by
  have h := h0_eq_card_iff_eq_zero (zetaJetDiagReading ε t (k + 1))
  rw [Fintype.card_fin] at h
  rw [h]
  constructor
  · intro h0 i hi
    have hi' : i < k + 1 := Nat.lt_succ_of_le hi
    have hii := congrFun (congrFun h0 ⟨i, hi'⟩) ⟨i, hi'⟩
    simpa [zetaJetDiagReading] using hii
  · intro hz
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [zetaJetDiagReading, Matrix.diagonal_apply_eq, Matrix.zero_apply]
      exact hz i.1 (Nat.le_of_lt_succ i.2)
    · simp [zetaJetDiagReading, Matrix.diagonal_apply_ne _ hij]

/-- **The zero-order receiver law is a count of sections:** for `0 < ε ≤ 1/2`, `0 < t`, and `k : ℕ`,
the oscillating log-power probe `logPowerCosine ε t k` has bounded receiver iff the `(k + 1) × (k + 1)`
zeta-jet reading at `1 - ε + i t` has section count `h⁰ = k + 1`. -/
theorem receiverBounded_logPowerCosine_iff_h0_eq {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ReceiverBounded (logPowerCosine ε t k) ↔
      h0 (zetaJetDiagReading ε t (k + 1)) = k + 1 :=
  (receiverBounded_logPowerCosine_iff hε hε2 ht k).trans (h0_zetaJetDiagReading_eq_iff ε t k).symm

/-- At `k = 0`, for every `0 < ε ≤ 1/2` and `t ∈ ℝ`, `ReceiverBounded (oscillatingSmoothPower ε t)`
holds iff `h0 (zetaJetDiagReading ε t 1) = 1`. -/
theorem receiverBounded_oscillatingSmoothPower_iff_h0_eq {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (t : ℝ) :
    ReceiverBounded (oscillatingSmoothPower ε t) ↔
      h0 (zetaJetDiagReading ε t 1) = 1 := by
  rw [receiverBounded_oscillatingSmoothPower_iff hε hε2 t, h0_zetaJetDiagReading_eq_iff ε t 0]
  constructor
  · intro hz i hi
    rw [Nat.le_zero.mp hi, iteratedDeriv_zero]
    exact hz
  · intro h
    have h0 := h 0 le_rfl
    rwa [iteratedDeriv_zero] at h0

/-! ### 4. Computing the Euler characteristic of the node divisor from the ledger -/

/-- **The continuous Euler characteristic of the prime-power node divisor** on the logarithmic
horizon box `[0, s]`: the two-pole degrees of freedom `polarBoxDoF s = ∫_0^s (e^u + 1) du` minus
the prime-power node weight `primeNodeCount s = ψ(e^s)`. -/
def nodeDivisorEulerChar (s : ℝ) : ℝ :=
  polarBoxDoF s - primeNodeCount s

/-- The continuous Euler characteristic of the node divisor for a general arithmetic weight
`w : ℕ → ℝ` on `[0, s]`. -/
def generalizedNodeDivisorEulerChar (w : ℕ → ℝ) (s : ℝ) : ℝ :=
  polarBoxDoF s - weightedNodeCount w s

/-- **Identity with the two-pole Chebyshev defect:** for every `s : ℝ`, `nodeDivisorEulerChar s` is
identically `chebyshevTwoPoleDefect s = e^s + s - 1 - ψ(e^s)`. -/
theorem nodeDivisorEulerChar_eq_chebyshevTwoPoleDefect (s : ℝ) :
    nodeDivisorEulerChar s = chebyshevTwoPoleDefect s :=
  polarBoxDoF_sub_primeNodeCount_eq_chebyshevTwoPoleDefect s

/-- Explicit closed form of `nodeDivisorEulerChar s`. -/
theorem nodeDivisorEulerChar_eq_formula (s : ℝ) :
    nodeDivisorEulerChar s = Real.exp s + s - 1 - lagChebyshev s := by
  rw [nodeDivisorEulerChar_eq_chebyshevTwoPoleDefect s, chebyshevTwoPoleDefect, twoPoleWeight]

/-- For any weight `w : ℕ → ℝ` and `s : ℝ`, `generalizedNodeDivisorEulerChar w s` equals
`generalizedTwoPoleDefect w s`. -/
theorem generalizedNodeDivisorEulerChar_eq (w : ℕ → ℝ) (s : ℝ) :
    generalizedNodeDivisorEulerChar w s = generalizedTwoPoleDefect w s :=
  polarBoxDoF_sub_weightedNodeCount_eq_generalizedTwoPoleDefect w s

/-- **Exact evaluation of `nodeDivisorEulerChar` below the first prime (`s < log 2`):** no
prime nodes have fired, so `nodeDivisorEulerChar s = e^s + s - 1`. -/
theorem nodeDivisorEulerChar_below_first_prime {s : ℝ} (hs2 : s < Real.log 2) :
    nodeDivisorEulerChar s = Real.exp s + s - 1 := by
  rw [nodeDivisorEulerChar_eq_formula s]
  have hexp : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hs2
      _ = 2 := Real.exp_log (by norm_num)
  have hfl : ⌊Real.exp s⌋₊ < 2 := (Nat.floor_lt (by positivity)).mpr hexp
  have hlag : lagChebyshev s = 0 := by
    unfold lagChebyshev
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hk1 : k = 0 ∨ k = 1 := by omega
    rcases hk1 with rfl | rfl <;> simp
  rw [hlag, sub_zero]

/-- **Exact evaluation of `nodeDivisorEulerChar` on the first prime window (`log 2 ≤ s < log 3`):**
only the single node `p = 2` has fired with weight `log 2`, so
`nodeDivisorEulerChar s = e^s + s - 1 - log 2`. -/
theorem nodeDivisorEulerChar_first_prime_window {s : ℝ} (hs2 : Real.log 2 ≤ s)
    (hs3 : s < Real.log 3) :
    nodeDivisorEulerChar s = Real.exp s + s - 1 - Real.log 2 := by
  rw [nodeDivisorEulerChar_eq_formula s]
  have hexp2 : 2 ≤ Real.exp s := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp s := Real.exp_le_exp.mpr hs2
  have hexp3 : Real.exp s < 3 := by
    calc Real.exp s < Real.exp (Real.log 3) := Real.exp_lt_exp.mpr hs3
      _ = 3 := Real.exp_log (by norm_num)
  have hfl2 : 2 ≤ ⌊Real.exp s⌋₊ := (Nat.le_floor_iff (by positivity)).mpr hexp2
  have hfl3 : ⌊Real.exp s⌋₊ < 3 := (Nat.floor_lt (by positivity)).mpr hexp3
  have hfl : ⌊Real.exp s⌋₊ = 2 := by omega
  have hlag : lagChebyshev s = Real.log 2 := by
    unfold lagChebyshev
    rw [hfl]
    have hIcc : Finset.Icc 0 2 = ({0, 1, 2} : Finset ℕ) := rfl
    rw [hIcc]
    simp [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  rw [hlag]

/-- **Selectivity of `nodeDivisorEulerChar`:** for any `a ≠ 0` and `s ≥ log 2`, the shifted-pair
weight `shiftedPairVonMangoldt a` has strictly smaller node-divisor Euler characteristic than `ℤ`. -/
theorem generalizedNodeDivisorEulerChar_shiftedPair_lt {a s : ℝ} (ha : a ≠ 0)
    (hs : Real.log 2 ≤ s) :
    generalizedNodeDivisorEulerChar (shiftedPairVonMangoldt a) s < nodeDivisorEulerChar s := by
  rw [generalizedNodeDivisorEulerChar_eq, nodeDivisorEulerChar_eq_chebyshevTwoPoleDefect]
  exact generalizedTwoPoleDefect_shiftedPair_lt_chebyshev ha hs

/-- **Computing the Euler characteristic of the node divisor from the ledger:** on the odd
degree-`r` scaling subsurface (`0 < r < R`), for any cycle `x : ℝ × ℝ × oddRealTestsAt r` with
test component `f = (x.2.2.1 : ℝ → ℝ)`, the lag-weighted integral of the node-divisor Euler
characteristic `nodeDivisorEulerChar s` on `(0, 2r]` is equal to the archimedean gauge budget
(`surplusPool + crossingPotentialTerm + gaugeRemainder`) minus the Castelnuovo–Severi defect
`(scalingSubsurface (oddRealTestsAt r)).defect x x`. -/
theorem nodeDivisorEulerChar_integral_from_ledger {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (x : ℝ × ℝ × oddRealTestsAt r) :
    (∫ s in Ioc 0 (2 * r),
        nodeDivisorEulerChar s *
          (2 * Real.exp (-s / 2) *
            (crossCorrelation (x.2.2.1 : ℝ → ℝ) s -
              autoCorrelation (x.2.2.1 : ℝ → ℝ) s / 2))) =
      surplusPool (aperturePlateau r R) (x.2.2.1 : ℝ → ℝ) +
        crossingPotentialTerm (aperturePlateau r R) (x.2.2.1 : ℝ → ℝ) +
        gaugeRemainder (aperturePlateau r R) (x.2.2.1 : ℝ → ℝ) -
        (scalingSubsurface (oddRealTestsAt r)).defect x x := by
  have hdef := scalingSubsurface_odd_defect_eq_chebyshevDefectLedger hr hrR x
  have hcongr :
      (∫ s in Ioc 0 (2 * r),
          nodeDivisorEulerChar s *
            (2 * Real.exp (-s / 2) *
              (crossCorrelation (x.2.2.1 : ℝ → ℝ) s -
                autoCorrelation (x.2.2.1 : ℝ → ℝ) s / 2))) =
        ∫ s in Ioc 0 (2 * r),
          chebyshevTwoPoleDefect s *
            (2 * Real.exp (-s / 2) *
              (crossCorrelation (x.2.2.1 : ℝ → ℝ) s -
                autoCorrelation (x.2.2.1 : ℝ → ℝ) s / 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    rw [nodeDivisorEulerChar_eq_chebyshevTwoPoleDefect s]
  rw [hcongr]
  linarith

/-! ### 5. The Master Index Theorem of the Receiver and Extended Width Dictionary -/

/-- **The Master Index Theorem of the Receiver:**
1. *(Order-1 and Order-2 Pole Section Laws)* For `0 < ε ≤ 1/2` and `r ∈ {1, 2}` (`r ≤ J`), a finite
   kernel `k` on `[1, J]` repairs the pole of order `r` iff `kernelVec k J` is a section of
   `poleJetMatrix J ε r` (and iff `h0` of the principal-part reading equals `r`), and the pole
   order `r` equals the section codimension `J - h0 (poleJetMatrix J ε r) = r` with `h1 = 0`.
2. *(Zero-Multiplicity Section Law)* For `0 < ε ≤ 1/2`, `0 < t`, and `k : ℕ`, the oscillating
   log-power probe `logPowerCosine ε t k` is paid by the receiver iff the diagonal zeta-jet reading
   at `1 - ε + i t` has section count `h0 (zetaJetDiagReading ε t (k + 1)) = k + 1`.
3. *(Right-Zero Hodge Defect Law)* For every `n : ℕ`, the intersection Gram `intersectionGram Λ f`
   has `1 + n` positive squares on some `n`-tuple of `C²_c` tests iff `ζ` has at least `n` zeros
   right of the critical line.
4. *(Node-Divisor Euler Characteristic Ledger Law)* On `0 ≤ s`, `nodeDivisorEulerChar s =
   polarBoxDoF s - primeNodeCount s = chebyshevTwoPoleDefect s`, and its lag integral on `(0, 2r]`
   is computed by the reflected prime-polar ledger from `(scalingSubsurface (oddRealTestsAt r)).defect`. -/
theorem receiver_index_theorem :
    (∀ {J : ℕ}, 1 ≤ J → ∀ ε : ℝ,
      h1 (poleJetMatrix J ε 1) = 0 ∧ J - h0 (poleJetMatrix J ε 1) = 1) ∧
    (∀ {J : ℕ}, 2 ≤ J → ∀ ε : ℝ,
      h1 (poleJetMatrix J ε 2) = 0 ∧ J - h0 (poleJetMatrix J ε 2) = 2) ∧
    (∀ {ε t : ℝ}, 0 < ε → ε ≤ 1 / 2 → 0 < t → ∀ k : ℕ,
      ReceiverBounded (logPowerCosine ε t k) ↔
        h0 (zetaJetDiagReading ε t (k + 1)) = k + 1) ∧
    (∀ n : ℕ,
      (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        1 + n ≤ hermPosIndex (intersectionGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) f)) ↔
        (n : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard) ∧
    (∀ s : ℝ, nodeDivisorEulerChar s = chebyshevTwoPoleDefect s) :=
  ⟨fun hJ ε => ⟨(poleJetMatrix_one_rank_h1_h0 hJ ε).2.1, (poleJetMatrix_one_rank_h1_h0 hJ ε).2.2.2.1⟩,
   fun hJ ε => ⟨(poleJetMatrix_two_rank_h1_h0 hJ ε).2.1, (poleJetMatrix_two_rank_h1_h0 hJ ε).2.2.2.1⟩,
   fun hε hε2 ht k => receiverBounded_logPowerCosine_iff_h0_eq hε hε2 ht k,
   zeta_hodgeDefect_iff,
   nodeDivisorEulerChar_eq_chebyshevTwoPoleDefect⟩

/-- **The Receiver Index and Section-Cone Width Dictionary:** unites the section effectivity cone
`E = {x : h⁰(x) ≥ 1}` (both its Bézout and Riemann–Roch axioms on `scalingSurface`), the zero-jet
section count `h0 (zetaJetDiagReading ε t 1) = 0` below half damping, the oscillating smooth-power
receiver, the vanishing of right zeros, and the cofinal damped Möbius receiver. -/
theorem receiverIndexAndSectionConeDictionary_tfae : List.TFAE [
    RiemannHypothesis,
    scalingSurface.HodgeIndex,
    scalingSurface.BezoutAxiom (sectionEffectivityCone scalingSurface),
    scalingSurface.RiemannRochAxiom (sectionEffectivityCone scalingSurface),
    rightZeros zetaZeroConfig = ∅,
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ t : ℝ, ¬ ReceiverBounded (oscillatingSmoothPower ε t),
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ t : ℝ, h0 (zetaJetDiagReading ε t 1) = 0,
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B] := by
  tfae_have 1 ↔ 2 := scalingSurface_hodgeIndex_iff.symm
  tfae_have 2 ↔ 3 := (sectionEffectivityCone_bezout_iff_hodgeIndex scalingSurface).symm
  tfae_have 2 ↔ 4 := (sectionEffectivityCone_riemannRoch_iff_hodgeIndex scalingSurface).symm
  tfae_have 1 ↔ 5 := riemannHypothesis_iff_rightZeros_zeta_eq_empty
  tfae_have 1 ↔ 6 := riemannHypothesis_iff_forall_not_receiverBounded_oscillatingSmoothPower
  tfae_have 6 ↔ 7 := by
    refine forall_congr' fun ε => imp_congr_right fun hε => imp_congr_right fun hε2 =>
      forall_congr' fun t => ?_
    rw [receiverBounded_oscillatingSmoothPower_iff_h0_eq hε hε2.le t]
    have hle : h0 (zetaJetDiagReading ε t 1) ≤ 1 := by
      have h := h0_add_rank (zetaJetDiagReading ε t 1)
      rw [Fintype.card_fin] at h
      omega
    omega
  tfae_have 1 ↔ 8 := riemannHypothesis_iff_cofinal_budget
  tfae_finish

end

end GaloisForLFunctions.ArithmeticOrientationTheory
