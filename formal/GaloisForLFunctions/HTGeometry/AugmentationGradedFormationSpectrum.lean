import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Ring.GeomSum

/-!
# Augmentation-graded formation spectrum

The integral Laurent group algebra is the universal rank-one algebra of finite signed formation
histories.  Powers of `T - 1` are memory orders.  This file proves four laws on one object:

* order-`r` recovery is injective;
* observer response through recovery is exactly the `r`-th forward difference;
* inversion lifts losslessly and acts by `(-1)^r` modulo the next memory order;
* a closed period-`p` relation retains `p` as its first-grade winding residue.

These are the Lean certificates for ULF-TAFM-24.
-/

open scoped LaurentPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open LaurentPolynomial

/-- Universal integral rank-one algebra of finite signed formation histories. -/
abbrev AugmentationFormationAlgebra := LaurentPolynomial ℤ

/-- Order-`r` formation recovery: multiplication by the `r`-th augmentation power. -/
def augmentationFormationBoundary
    (r : ℕ) (P : AugmentationFormationAlgebra) : AugmentationFormationAlgebra :=
  (T 1 - 1) ^ r * P

/-- History-side lift of Laurent inversion through order-`r` recovery. -/
def augmentationHistoryReflection
    (r : ℕ) (P : AugmentationFormationAlgebra) : AugmentationFormationAlgebra :=
  T (-(r : ℤ)) * invert P

/-- Inversion sends the augmentation generator to its unit multiple with one minus sign. -/
lemma invert_augmentationGenerator :
    invert (T 1 - 1 : AugmentationFormationAlgebra) =
      -((T 1 - 1) * T (-1)) := by
  rw [map_sub, invert_T]
  simp only [map_one]
  have hunit :
      (T (1 : ℤ) : AugmentationFormationAlgebra) * T (-1 : ℤ) = 1 := by
    rw [← T_add]
    norm_num
  calc
    (T (-1 : ℤ) : AugmentationFormationAlgebra) - 1 =
        -((1 : AugmentationFormationAlgebra) - T (-1 : ℤ)) := by abel
    _ = -((T (1 : ℤ) - 1) * T (-1 : ℤ)) := by
      congr 1
      rw [sub_mul, hunit, one_mul]

/-- Exact lossless intertwining of inversion and every formation-recovery order. -/
theorem invert_augmentationFormationBoundary
    (r : ℕ) (P : AugmentationFormationAlgebra) :
    invert (augmentationFormationBoundary r P) =
      (-1) ^ r * augmentationFormationBoundary r (augmentationHistoryReflection r P) := by
  rw [augmentationFormationBoundary, map_mul, map_pow, invert_augmentationGenerator]
  rw [show -((T 1 - 1 : AugmentationFormationAlgebra) * T (-1)) =
      (-1) * ((T 1 - 1) * T (-1)) by rw [neg_one_mul]]
  rw [mul_pow, mul_pow, T_pow]
  simp only [augmentationFormationBoundary, augmentationHistoryReflection]
  norm_num
  simp only [mul_assoc]
  rw [T_mul]

/-- Lifted history reflection is an involution at every recovery order. -/
theorem augmentationHistoryReflection_involutive (r : ℕ) :
    Function.Involutive (augmentationHistoryReflection r) := by
  intro P
  rw [augmentationHistoryReflection, augmentationHistoryReflection, map_mul, invert_T,
    LaurentPolynomial.involutive_invert]
  rw [← mul_assoc, ← T_add]
  norm_num

/-- The augmentation generator is nonzero in the integral Laurent algebra. -/
lemma augmentationGenerator_ne_zero :
    (T 1 - 1 : AugmentationFormationAlgebra) ≠ 0 := by
  intro h
  have hone : ((1 : AugmentationFormationAlgebra).coeff 1) = 0 := by
    calc
      ((1 : AugmentationFormationAlgebra).coeff 1) =
          (AddMonoidAlgebra.single (0 : ℤ) (1 : ℤ) :
            AugmentationFormationAlgebra).coeff 1 :=
        congrArg (fun P : AugmentationFormationAlgebra => P.coeff 1)
          LaurentPolynomial.single_zero_one_eq_one.symm
      _ = 0 := by
        rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
        norm_num
  have hc := congrArg (fun P : AugmentationFormationAlgebra => P.coeff 1) h
  change (T 1 : AugmentationFormationAlgebra).coeff 1 -
      (1 : AugmentationFormationAlgebra).coeff 1 = 0 at hc
  rw [T_apply, if_pos rfl, hone] at hc
  norm_num at hc

/-- Every formation-recovery order is information-neutral on finite histories. -/
theorem augmentationFormationBoundary_injective (r : ℕ) :
    Function.Injective (augmentationFormationBoundary r) := by
  intro P Q h
  exact mul_left_cancel₀ (pow_ne_zero r augmentationGenerator_ne_zero) h

/-- Geometric carrier of one closed period-`p` relation. -/
def augmentationCycleCarrier (p : ℕ) : AugmentationFormationAlgebra :=
  ∑ j ∈ Finset.range p, T (j : ℤ)

/-- Closed augmentation observer obtained by evaluation at `T = 1`. -/
def augmentationObserver : AugmentationFormationAlgebra →ₗ[ℤ] ℤ :=
  LaurentPolynomial.leval ℤ (1 : ℤˣ)

/-- Exact recurrence factorisation through the first formation boundary. -/
theorem augmentationCycleClosure_factorization (p : ℕ) :
    (T (p : ℤ) : AugmentationFormationAlgebra) - 1 =
      (T 1 - 1) * augmentationCycleCarrier p := by
  have hT (j : ℕ) :
      (T (1 : ℤ) : AugmentationFormationAlgebra) ^ j = T (j : ℤ) := by
    rw [LaurentPolynomial.T_pow]
    norm_num
  rw [augmentationCycleCarrier, mul_comm, ← hT p]
  simp_rw [← hT]
  exact (geom_sum_mul (T 1 : AugmentationFormationAlgebra) p).symm

/-- A period-`p` carrier retains exactly `p` units under the closed observer. -/
theorem augmentationObserver_cycleCarrier (p : ℕ) :
    augmentationObserver (augmentationCycleCarrier p) = p := by
  rw [augmentationCycleCarrier, map_sum]
  simp only [augmentationObserver, LaurentPolynomial.leval_apply,
    LaurentPolynomial.smeval_T_pow, one_zpow, Units.val_one]
  simp

/-- Finite history/clock pairing. -/
def augmentationObserverPairing
    (P : AugmentationFormationAlgebra) (clock : ℤ → ℤ) : ℤ :=
  P.coeff.sum fun k q => q * clock k

/-- Forward observer-clock difference. -/
def augmentationForwardDifference (clock : ℤ → ℤ) (k : ℤ) : ℤ :=
  clock (k + 1) - clock k

@[simp] lemma augmentationObserverPairing_add
    (P Q : AugmentationFormationAlgebra) (clock : ℤ → ℤ) :
    augmentationObserverPairing (P + Q) clock =
      augmentationObserverPairing P clock + augmentationObserverPairing Q clock := by
  simp [augmentationObserverPairing, Finsupp.sum_add_index, add_mul]

@[simp] lemma augmentationObserverPairing_sub
    (P Q : AugmentationFormationAlgebra) (clock : ℤ → ℤ) :
    augmentationObserverPairing (P - Q) clock =
      augmentationObserverPairing P clock - augmentationObserverPairing Q clock := by
  unfold augmentationObserverPairing
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sum_sub_index]
  intro k a b
  ring

@[simp] lemma augmentationObserverPairing_C_mul_T
    (a n : ℤ) (clock : ℤ → ℤ) :
    augmentationObserverPairing (C a * T n) clock = a * clock n := by
  calc
    augmentationObserverPairing (C a * T n) clock =
        augmentationObserverPairing
          (AddMonoidAlgebra.single n a) clock := by
      rw [LaurentPolynomial.single_eq_C_mul_T]
    _ = a * clock n := by
      unfold augmentationObserverPairing
      rw [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index]
      simp

/-- First-order source--observer Green law. -/
theorem augmentationObserverPairing_boundary_one
    (P : AugmentationFormationAlgebra) (clock : ℤ → ℤ) :
    augmentationObserverPairing (augmentationFormationBoundary 1 P) clock =
      augmentationObserverPairing P (augmentationForwardDifference clock) := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
      simpa only [augmentationFormationBoundary, mul_add,
        augmentationObserverPairing_add] using congrArg₂ (· + ·) hP hQ
  | C_mul_T n a =>
      rw [augmentationFormationBoundary, pow_one, sub_mul, one_mul,
        LaurentPolynomial.T_mul, LaurentPolynomial.mul_T_assoc]
      simp only [augmentationObserverPairing_sub,
        augmentationObserverPairing_C_mul_T, augmentationForwardDifference]
      ring

/-- Iterated forward observer-clock difference. -/
def augmentationIteratedForwardDifference : ℕ → (ℤ → ℤ) → (ℤ → ℤ)
  | 0, clock => clock
  | r + 1, clock =>
      augmentationIteratedForwardDifference r (augmentationForwardDifference clock)

lemma augmentationFormationBoundary_succ
    (r : ℕ) (P : AugmentationFormationAlgebra) :
    augmentationFormationBoundary (r + 1) P =
      augmentationFormationBoundary 1 (augmentationFormationBoundary r P) := by
  simp only [augmentationFormationBoundary, pow_succ, pow_zero, one_mul]
  rw [mul_comm ((T 1 - 1 : AugmentationFormationAlgebra) ^ r) (T 1 - 1)]
  simp only [mul_assoc]

/-- All-order source--observer Green law: recovery order is dual to clock-difference order. -/
theorem augmentationObserverPairing_boundary
    (r : ℕ) (P : AugmentationFormationAlgebra) (clock : ℤ → ℤ) :
    augmentationObserverPairing (augmentationFormationBoundary r P) clock =
      augmentationObserverPairing P
        (augmentationIteratedForwardDifference r clock) := by
  induction r generalizing clock with
  | zero =>
      simp [augmentationFormationBoundary, augmentationIteratedForwardDifference]
  | succ r ih =>
      rw [augmentationFormationBoundary_succ,
        augmentationObserverPairing_boundary_one, ih]
      rfl

lemma augmentationGenerator_dvd_T_sub_one (n : ℤ) :
    (T 1 - 1 : AugmentationFormationAlgebra) ∣ T n - 1 := by
  cases n with
  | ofNat n =>
      have h := sub_one_dvd_pow_sub_one
        (T 1 : AugmentationFormationAlgebra) n
      simpa using h
  | negSucc n =>
      let m : ℕ := n + 1
      have hpos :
          (T 1 - 1 : AugmentationFormationAlgebra) ∣ T (m : ℤ) - 1 := by
        have h := sub_one_dvd_pow_sub_one
          (T 1 : AugmentationFormationAlgebra) m
        simpa using h
      have hunit :
          (T (-(m : ℤ)) : AugmentationFormationAlgebra) * T (m : ℤ) = 1 := by
        rw [← T_add]
        simp
      have heq :
          (T (-(m : ℤ)) : AugmentationFormationAlgebra) - 1 =
            (-T (-(m : ℤ))) * (T (m : ℤ) - 1) := by
        rw [neg_mul, mul_sub, hunit, mul_one]
        abel
      change (T 1 - 1 : AugmentationFormationAlgebra) ∣ T (-(m : ℤ)) - 1
      rw [heq]
      exact dvd_mul_of_dvd_right hpos _

lemma augmentationGenerator_dvd_T_sub_T (m n : ℤ) :
    (T 1 - 1 : AugmentationFormationAlgebra) ∣ T m - T n := by
  have h := augmentationGenerator_dvd_T_sub_one (m - n)
  have heq :
      (T m - T n : AugmentationFormationAlgebra) =
        T n * (T (m - n) - 1) := by
    rw [mul_sub, mul_one, ← T_add]
    congr 2
    omega
  rw [heq]
  exact dvd_mul_of_dvd_right h _

lemma augmentationGenerator_dvd_historyReflection_sub
    (r : ℕ) (P : AugmentationFormationAlgebra) :
    (T 1 - 1 : AugmentationFormationAlgebra) ∣
      augmentationHistoryReflection r P - P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
      have hadd :
          augmentationHistoryReflection r (P + Q) - (P + Q) =
            (augmentationHistoryReflection r P - P) +
              (augmentationHistoryReflection r Q - Q) := by
        simp only [augmentationHistoryReflection, map_add, mul_add]
        abel
      rw [hadd]
      exact dvd_add hP hQ
  | C_mul_T n a =>
      have href :
          augmentationHistoryReflection r (C a * T n) =
            C a * T (-(r : ℤ) - n) := by
        simp only [augmentationHistoryReflection, map_mul, invert_C, invert_T]
        rw [LaurentPolynomial.T_mul, LaurentPolynomial.mul_T_assoc]
        congr 2
        omega
      rw [href, ← mul_sub]
      exact dvd_mul_of_dvd_right
        (augmentationGenerator_dvd_T_sub_T (-(r : ℤ) - n) n) _

/-- Equality modulo an order-`r` formation boundary. -/
def SameModuloAugmentationBoundary
    (r : ℕ) (P Q : AugmentationFormationAlgebra) : Prop :=
  ∃ D, P - Q = augmentationFormationBoundary r D

/-- Laurent inversion acts by `(-1)^r` on the `r`-th associated augmentation grade. -/
theorem augmentationReflection_associatedGraded_parity
    (r : ℕ) (P : AugmentationFormationAlgebra) :
    SameModuloAugmentationBoundary (r + 1)
      (invert (augmentationFormationBoundary r P))
      ((-1 : AugmentationFormationAlgebra) ^ r *
        augmentationFormationBoundary r P) := by
  obtain ⟨D, hD⟩ := augmentationGenerator_dvd_historyReflection_sub r P
  refine ⟨(-1 : AugmentationFormationAlgebra) ^ r * D, ?_⟩
  rw [invert_augmentationFormationBoundary]
  calc
    (-1 : AugmentationFormationAlgebra) ^ r *
          augmentationFormationBoundary r (augmentationHistoryReflection r P) -
        (-1 : AugmentationFormationAlgebra) ^ r *
          augmentationFormationBoundary r P =
        (-1 : AugmentationFormationAlgebra) ^ r * (T 1 - 1) ^ r *
          (augmentationHistoryReflection r P - P) := by
            simp only [augmentationFormationBoundary]
            ring
    _ = (-1 : AugmentationFormationAlgebra) ^ r * (T 1 - 1) ^ r *
          ((T 1 - 1) * D) := by
      rw [hD]
    _ = augmentationFormationBoundary (r + 1)
          ((-1 : AugmentationFormationAlgebra) ^ r * D) := by
      simp only [augmentationFormationBoundary, pow_succ]
      ring

/-- Higher recurrence correction after its first-grade winding residue. -/
def augmentationCycleCurvature : ℕ → AugmentationFormationAlgebra
  | 0 => 0
  | p + 1 => augmentationCycleCurvature p + augmentationCycleCarrier p

/-- Exact closed-recurrence/open-history law: period `p` leaves residue `p` modulo order two. -/
theorem augmentationCycleClosure_firstGradedResidue (p : ℕ) :
    (T (p : ℤ) : AugmentationFormationAlgebra) - 1 =
      (p : AugmentationFormationAlgebra) * (T 1 - 1) +
        (T 1 - 1) ^ 2 * augmentationCycleCurvature p := by
  induction p with
  | zero => simp [augmentationCycleCurvature]
  | succ p ih =>
      have hT :
          (T ((p + 1 : ℕ) : ℤ) : AugmentationFormationAlgebra) =
            T (p : ℤ) * T 1 := by
        rw [← T_add]
        congr 1
      have hcycle :
          (T (p : ℤ) : AugmentationFormationAlgebra) =
            1 + (T 1 - 1) * augmentationCycleCarrier p := by
        calc
          (T (p : ℤ) : AugmentationFormationAlgebra) =
              (T (p : ℤ) - 1) + 1 := by ring
          _ = 1 + (T 1 - 1) * augmentationCycleCarrier p := by
            rw [augmentationCycleClosure_factorization]
            ring
      rw [hT, augmentationCycleCurvature]
      rw [show (T (p : ℤ) : AugmentationFormationAlgebra) * T 1 -
          (1 : AugmentationFormationAlgebra) =
          (T (p : ℤ) - (1 : AugmentationFormationAlgebra)) +
            T (p : ℤ) * (T 1 - (1 : AugmentationFormationAlgebra)) by
              rw [mul_sub, mul_one]
              abel]
      rw [ih, hcycle]
      push_cast
      ring

/-- Diagonal grade energy erases reflection sign, while adjacent-grade polarization retains it. -/
theorem augmentationAdjacentGrade_orientationParity (r : ℕ) (x y : ℤ) :
    (((-1 : ℤ) ^ r * x) ^ 2 = x ^ 2) ∧
      ((-1 : ℤ) ^ r * x) * ((-1 : ℤ) ^ (r + 1) * y) = -(x * y) := by
  have hs : ((-1 : ℤ) ^ r) ^ 2 = 1 := by
    rw [← pow_mul]
    rw [mul_comm r 2, pow_mul]
    norm_num
  constructor
  · rw [mul_pow, hs, one_mul]
  · rw [pow_succ]
    calc
      ((-1 : ℤ) ^ r * x) * ((-1 : ℤ) ^ r * -1 * y) =
          -((((-1 : ℤ) ^ r) ^ 2) * (x * y)) := by ring
      _ = -(x * y) := by rw [hs, one_mul]

end

end GaloisForLFunctions.HTGeometry
