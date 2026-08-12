import Mathlib

/-!
# Connes--Consani cyclic-pair Jacobi calculus

This module formalizes the algebraic operator identities in Section 2 and Section 6 of
Connes--Consani, *Zeta zeros and prolate wave operators: semilocal adelic operators* (2023).

The paper works formally on the polynomial core of an unbounded Jacobi operator.  We encode that
core calculation pointwise on arbitrary sequences.  Consequently every identity below is total
and unconditional: no self-adjoint extension, convergence, positivity, or spectral assumption is
inserted.  The even and odd formulas are obtained by applying the square of the actual
nearest-neighbour Jacobi action to parity-supported sequences; they are not definitions of the
claimed answer.
-/

open Complex

noncomputable section

namespace RHTower

/-- Formal Jacobi action with upper coefficient `a n` and lower coefficient `star (a (n-1))`.
At the left endpoint the nonexistent lower edge is zero. -/
def ccmCyclicJacobiAction (a x : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then a 0 * x 1
  else star (a (n - 1)) * x (n - 1) + a n * x (n + 1)

/-- Number grading on the Jacobi basis. -/
def ccmCyclicNumberAction (x : ℕ → ℂ) (n : ℕ) : ℂ := (n : ℂ) * x n

/-- Pointwise commutator of two formal sequence actions. -/
def ccmFormalCommutator
    (A B : (ℕ → ℂ) → ℕ → ℂ) (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  A (B x) n - B (A x) n

/-- Even-index lift from one parity block to the full Jacobi sequence. -/
def ccmEvenJacobiLift (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  if Even n then x (n / 2) else 0

/-- Odd-index lift from one parity block to the full Jacobi sequence. -/
def ccmOddJacobiLift (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  if Odd n then x (n / 2) else 0

@[simp] theorem ccmEvenJacobiLift_even (x : ℕ → ℂ) (n : ℕ) :
    ccmEvenJacobiLift x (2 * n) = x n := by
  simp [ccmEvenJacobiLift]

@[simp] theorem ccmEvenJacobiLift_odd (x : ℕ → ℂ) (n : ℕ) :
    ccmEvenJacobiLift x (2 * n + 1) = 0 := by
  simp [ccmEvenJacobiLift]

@[simp] theorem ccmOddJacobiLift_even (x : ℕ → ℂ) (n : ℕ) :
    ccmOddJacobiLift x (2 * n) = 0 := by
  simp [ccmOddJacobiLift]

@[simp] theorem ccmOddJacobiLift_odd (x : ℕ → ℂ) (n : ℕ) :
    ccmOddJacobiLift x (2 * n + 1) = x n := by
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp [ccmOddJacobiLift, hdiv]

/-- The Jacobi/number commutator has the signed nearest-neighbour coefficients displayed in
Connes--Consani equation (46), including the left endpoint. -/
theorem ccmCyclicJacobi_number_commutator_zero (a x : ℕ → ℂ) :
    ccmFormalCommutator (ccmCyclicJacobiAction a) ccmCyclicNumberAction x 0 =
      a 0 * x 1 := by
  simp [ccmFormalCommutator, ccmCyclicJacobiAction, ccmCyclicNumberAction]

theorem ccmCyclicJacobi_number_commutator_succ
    (a x : ℕ → ℂ) (n : ℕ) :
    ccmFormalCommutator (ccmCyclicJacobiAction a) ccmCyclicNumberAction x (n + 1) =
      -(star (a n) * x n) + a (n + 1) * x (n + 2) := by
  simp [ccmFormalCommutator, ccmCyclicJacobiAction, ccmCyclicNumberAction]
  ring

/-- Connes--Consani Lemma (47)(i): `[[A,N],N]=A`, pointwise on the full algebraic core. -/
theorem ccmCyclicJacobi_double_number_commutator
    (a x : ℕ → ℂ) (n : ℕ) :
    ccmFormalCommutator
        (fun y => ccmFormalCommutator (ccmCyclicJacobiAction a)
          ccmCyclicNumberAction y)
        ccmCyclicNumberAction x n =
      ccmCyclicJacobiAction a x n := by
  cases n with
  | zero =>
      simp [ccmFormalCommutator, ccmCyclicJacobiAction, ccmCyclicNumberAction]
  | succ n =>
      rw [ccmFormalCommutator]
      rw [ccmCyclicJacobi_number_commutator_succ]
      simp only [ccmCyclicNumberAction]
      rw [ccmCyclicJacobi_number_commutator_succ]
      simp [ccmCyclicJacobiAction]
      ring

/-- Connes--Consani Lemma (47)(iii), left endpoint of
`[A,[A,N]] = diag(2(|a_(n-1)|^2-|a_n|^2))`. -/
theorem ccmCyclicJacobi_double_commutator_zero (a x : ℕ → ℂ) :
    ccmFormalCommutator (ccmCyclicJacobiAction a)
        (fun y => ccmFormalCommutator (ccmCyclicJacobiAction a)
          ccmCyclicNumberAction y) x 0 =
      (-2 * (a 0 * star (a 0))) * x 0 := by
  simp [ccmFormalCommutator, ccmCyclicJacobiAction, ccmCyclicNumberAction]
  ring

/-- Connes--Consani Lemma (47)(iii), every interior Jacobi index. -/
theorem ccmCyclicJacobi_double_commutator_succ
    (a x : ℕ → ℂ) (n : ℕ) :
    ccmFormalCommutator (ccmCyclicJacobiAction a)
        (fun y => ccmFormalCommutator (ccmCyclicJacobiAction a)
          ccmCyclicNumberAction y) x (n + 1) =
      (2 * (star (a n) * a n - a (n + 1) * star (a (n + 1)))) * x (n + 1) := by
  by_cases hn : n = 0
  · subst n
    norm_num [ccmFormalCommutator, ccmCyclicJacobiAction,
      ccmCyclicNumberAction]
    ring
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
    have hnsubC := congrArg (fun k : ℕ => (k : ℂ)) hnsub
    have hncast : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
      push_cast at hnsubC
      calc
        ((n - 1 : ℕ) : ℂ) = ((n - 1 : ℕ) : ℂ) + 1 - 1 := by ring
        _ = (n : ℂ) - 1 := by rw [hnsubC]
    simp [ccmFormalCommutator, ccmCyclicJacobiAction,
      ccmCyclicNumberAction, hn]
    rw [hncast]
    ring

/-- Connes--Consani's formal raising generator
`F₊ = N + (2i)⁻¹[A,N]`. -/
def ccmCyclicRaisingAction (a : ℕ → ℂ) (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  ccmCyclicNumberAction x n + (2 * I)⁻¹ *
    ccmFormalCommutator (ccmCyclicJacobiAction a) ccmCyclicNumberAction x n

/-- Connes--Consani's formal lowering generator
`F₋ = N - (2i)⁻¹[A,N]`. -/
def ccmCyclicLoweringAction (a : ℕ → ℂ) (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  ccmCyclicNumberAction x n - (2 * I)⁻¹ *
    ccmFormalCommutator (ccmCyclicJacobiAction a) ccmCyclicNumberAction x n

/-- Connes--Consani Lemma (47)(ii): `[F₊,F₋] = -iA` on the full algebraic core. -/
theorem ccmCyclic_raising_lowering_commutator
    (a x : ℕ → ℂ) (n : ℕ) :
    ccmFormalCommutator (ccmCyclicRaisingAction a)
        (ccmCyclicLoweringAction a) x n =
      -I * ccmCyclicJacobiAction a x n := by
  cases n with
  | zero =>
      simp [ccmFormalCommutator, ccmCyclicRaisingAction,
        ccmCyclicLoweringAction, ccmCyclicJacobiAction,
        ccmCyclicNumberAction]
      ring
  | succ n =>
      by_cases hn : n = 0
      · subst n
        norm_num [ccmFormalCommutator, ccmCyclicRaisingAction,
          ccmCyclicLoweringAction, ccmCyclicJacobiAction,
          ccmCyclicNumberAction]
        ring
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
        have hnsubC := congrArg (fun k : ℕ => (k : ℂ)) hnsub
        have hncast : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
          push_cast at hnsubC
          calc
            ((n - 1 : ℕ) : ℂ) = ((n - 1 : ℕ) : ℂ) + 1 - 1 := by ring
            _ = (n : ℂ) - 1 := by rw [hnsubC]
        simp [ccmFormalCommutator, ccmCyclicRaisingAction,
          ccmCyclicLoweringAction, ccmCyclicJacobiAction,
          ccmCyclicNumberAction, hn]
        rw [hncast]
        ring

/-- The diagonal discrepancy in Connes--Consani equation (49), with the nonexistent coefficient
at index `-1` interpreted as zero. -/
def ccmCyclicDiscrepancy (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  match n with
  | 0 => I * (a 0 * star (a 0))
  | n + 1 => I * (a (n + 1) * star (a (n + 1)) -
      star (a n) * a n - 2 * ((n + 1 : ℕ) : ℂ))

/-- Connes--Consani Lemma (47)(iv): `[A,F₊] = 2iF₊ + Υ`, including the endpoint. -/
theorem ccmCyclic_jacobi_raising_commutator
    (a x : ℕ → ℂ) (n : ℕ) :
    ccmFormalCommutator (ccmCyclicJacobiAction a)
        (ccmCyclicRaisingAction a) x n =
      2 * I * ccmCyclicRaisingAction a x n +
        ccmCyclicDiscrepancy a n * x n := by
  cases n with
  | zero =>
      simp [ccmFormalCommutator, ccmCyclicRaisingAction,
        ccmCyclicJacobiAction, ccmCyclicNumberAction,
        ccmCyclicDiscrepancy]
      ring_nf
      simp [Complex.I_sq]
  | succ n =>
      by_cases hn : n = 0
      · subst n
        norm_num [ccmFormalCommutator, ccmCyclicRaisingAction,
          ccmCyclicJacobiAction, ccmCyclicNumberAction,
          ccmCyclicDiscrepancy]
        ring_nf
        simp [Complex.I_sq]
        ring
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
        have hnsubC := congrArg (fun k : ℕ => (k : ℂ)) hnsub
        have hncast : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
          push_cast at hnsubC
          calc
            ((n - 1 : ℕ) : ℂ) = ((n - 1 : ℕ) : ℂ) + 1 - 1 := by ring
            _ = (n : ℂ) - 1 := by rw [hnsubC]
        simp [ccmFormalCommutator, ccmCyclicRaisingAction,
          ccmCyclicJacobiAction, ccmCyclicNumberAction,
          ccmCyclicDiscrepancy, hn]
        rw [hncast]
        ring_nf
        simp [Complex.I_sq]

/-- Upper weighted shift appearing in Connes--Consani Lemma (47)(v). -/
def ccmCyclicUpperShiftAction (a x : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * x (n + 1)

/-- Connes--Consani Lemma (47)(v): `F₊ - iA/2 = N - iS`. -/
theorem ccmCyclic_raising_sub_half_jacobi
    (a x : ℕ → ℂ) (n : ℕ) :
    ccmCyclicRaisingAction a x n - (I / 2) * ccmCyclicJacobiAction a x n =
      ccmCyclicNumberAction x n - I * ccmCyclicUpperShiftAction a x n := by
  cases n with
  | zero =>
      simp [ccmCyclicRaisingAction, ccmFormalCommutator,
        ccmCyclicJacobiAction, ccmCyclicNumberAction,
        ccmCyclicUpperShiftAction]
      ring
  | succ n =>
      simp [ccmCyclicRaisingAction, ccmFormalCommutator,
        ccmCyclicJacobiAction, ccmCyclicNumberAction,
        ccmCyclicUpperShiftAction]
      ring

/-- Formal prolate action `-A^2 + lambda^2 N` on the Jacobi polynomial core. -/
def ccmFormalProlateAction (a : ℕ → ℂ) (lambda : ℝ) (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  -ccmCyclicJacobiAction a (ccmCyclicJacobiAction a x) n +
    ((lambda ^ 2 : ℝ) : ℂ) * ccmCyclicNumberAction x n

/-- Connes--Consani Proposition (15), even block at its left endpoint. -/
theorem ccmFormalProlate_even_zero (a : ℕ → ℂ) (lambda : ℝ) (x : ℕ → ℂ) :
    ccmFormalProlateAction a lambda (ccmEvenJacobiLift x) 0 =
      (-(a 0 * star (a 0))) * x 0 - a 0 * a 1 * x 1 := by
  have hzero : ccmEvenJacobiLift x 0 = x 0 := by
    simpa using ccmEvenJacobiLift_even x 0
  have htwo : ccmEvenJacobiLift x 2 = x 1 := by
    simpa using ccmEvenJacobiLift_even x 1
  simp [ccmFormalProlateAction, ccmCyclicJacobiAction,
    ccmCyclicNumberAction, hzero, htwo]
  ring

/-- Connes--Consani Proposition (15), all positive rows of the even Jacobi block. -/
theorem ccmFormalProlate_even_succ
    (a : ℕ → ℂ) (lambda : ℝ) (x : ℕ → ℂ) (n : ℕ) :
    ccmFormalProlateAction a lambda (ccmEvenJacobiLift x) (2 * (n + 1)) =
      -(star (a (2 * n)) * star (a (2 * n + 1))) * x n +
      (-(a (2 * n + 2) * star (a (2 * n + 2))) -
          star (a (2 * n + 1)) * a (2 * n + 1) +
          (((2 * (n + 1) : ℕ) : ℝ) * lambda ^ 2 : ℝ)) * x (n + 1) -
      a (2 * n + 2) * a (2 * n + 3) * x (n + 2) := by
  have h0 : ccmEvenJacobiLift x (2 * n) = x n :=
    ccmEvenJacobiLift_even x n
  have h1 : ccmEvenJacobiLift x (2 * n + 2) = x (n + 1) := by
    rw [show 2 * n + 2 = 2 * (n + 1) by omega]
    exact ccmEvenJacobiLift_even x (n + 1)
  have h2 : ccmEvenJacobiLift x (2 * n + 4) = x (n + 2) := by
    rw [show 2 * n + 4 = 2 * (n + 2) by omega]
    exact ccmEvenJacobiLift_even x (n + 2)
  have hi : 2 * (n + 1) = 2 * n + 2 := by omega
  have hp : 2 * n + 2 - 1 = 2 * n + 1 := by omega
  simp [ccmFormalProlateAction, ccmCyclicJacobiAction,
    ccmCyclicNumberAction, hi, hp, h0, h1, h2]
  ring

/-- Connes--Consani Proposition (16), odd block at its left endpoint. -/
theorem ccmFormalProlate_odd_zero (a : ℕ → ℂ) (lambda : ℝ) (x : ℕ → ℂ) :
    ccmFormalProlateAction a lambda (ccmOddJacobiLift x) 1 =
      (-(star (a 0) * a 0) - a 1 * star (a 1) + (lambda ^ 2 : ℝ)) * x 0 -
        a 1 * a 2 * x 1 := by
  have hone : ccmOddJacobiLift x 1 = x 0 := by
    simpa using ccmOddJacobiLift_odd x 0
  have hthree : ccmOddJacobiLift x 3 = x 1 := by
    simpa using ccmOddJacobiLift_odd x 1
  simp [ccmFormalProlateAction, ccmCyclicJacobiAction,
    ccmCyclicNumberAction, hone, hthree]
  ring

/-- Connes--Consani Proposition (16), all positive rows of the odd Jacobi block. -/
theorem ccmFormalProlate_odd_succ
    (a : ℕ → ℂ) (lambda : ℝ) (x : ℕ → ℂ) (n : ℕ) :
    ccmFormalProlateAction a lambda (ccmOddJacobiLift x) (2 * (n + 1) + 1) =
      -(star (a (2 * n + 1)) * star (a (2 * n + 2))) * x n +
      (-(star (a (2 * n + 2)) * a (2 * n + 2)) -
          a (2 * n + 3) * star (a (2 * n + 3)) +
          (((2 * (n + 1) + 1 : ℕ) : ℝ) * lambda ^ 2 : ℝ)) * x (n + 1) -
      a (2 * n + 3) * a (2 * n + 4) * x (n + 2) := by
  have h0 : ccmOddJacobiLift x (2 * n + 1) = x n :=
    ccmOddJacobiLift_odd x n
  have h1 : ccmOddJacobiLift x (2 * n + 3) = x (n + 1) := by
    rw [show 2 * n + 3 = 2 * (n + 1) + 1 by omega]
    exact ccmOddJacobiLift_odd x (n + 1)
  have h2 : ccmOddJacobiLift x (2 * n + 5) = x (n + 2) := by
    rw [show 2 * n + 5 = 2 * (n + 2) + 1 by omega]
    exact ccmOddJacobiLift_odd x (n + 2)
  have hi : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
  have hp : 2 * n + 2 - 1 = 2 * n + 1 := by omega
  simp [ccmFormalProlateAction, ccmCyclicJacobiAction,
    ccmCyclicNumberAction, hi, hp, h1, h2]
  ring

end RHTower
