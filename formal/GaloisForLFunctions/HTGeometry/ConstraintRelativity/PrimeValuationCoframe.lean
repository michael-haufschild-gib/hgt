import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.GeneralizedPrimeCountermodel

/-!
# The prime-valuation cyclic coframe

Each prime valuation gives a derivation of the generalized-prime algebra, and pairing it with the
identity-coefficient trace gives a cyclic one-cocycle killing the Hochschild boundary.  On the
prime/inverse-prime atoms these cocycles form the identity matrix, so the atoms are linearly
independent in any quotient the cocycles descend through, and the scalar Kummer reader is a single
covector contraction of the whole coframe.

Off the critical line the diagonal physical defect is therefore injective on the prime span: no
finite cross-prime combination can cancel it.
-/

namespace HTGeometry.ConstraintRelativity

section Coframe

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- Induction on the generalized-prime algebra by monomials. -/
theorem primeAlgebra_induction {motive : PrimeAlgebra ι → Prop} (x : PrimeAlgebra ι)
    (h0 : motive 0) (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hsingle : ∀ g c, motive (AddMonoidAlgebra.single g c)) : motive x :=
  Finsupp.induction_linear (motive := fun f => motive (AddMonoidAlgebra.ofCoeff f)) x.coeff
    h0 (fun _ _ hf hg => hadd _ _ hf hg) fun g c => hsingle g c

omit [DecidableEq ι] in
/-- **Theorem 1.1.**  Each prime valuation acts as a derivation. -/
theorem valuationDeriv_mul (ℓ : ι) (x y : PrimeAlgebra ι) :
    valuationDeriv ℓ (x * y) = valuationDeriv ℓ x * y + x * valuationDeriv ℓ y := by
  induction x using primeAlgebra_induction with
  | h0 => simp
  | hadd x z hx hz =>
    rw [add_mul, map_add, hx, hz, map_add, add_mul, add_mul]
    ring
  | hsingle g a =>
    induction y using primeAlgebra_induction with
    | h0 => simp
    | hadd y z hy hz =>
      rw [mul_add, map_add, hy, hz, map_add, mul_add, mul_add]
      ring
    | hsingle h b => exact valuationDeriv_single_mul ℓ g h a b

/-- **Theorem 1.2.**  The trace annihilates every valuation derivation. -/
theorem gradeTrace_valuationDeriv (ℓ : ι) (x : PrimeAlgebra ι) :
    gradeTrace (valuationDeriv ℓ x) = 0 := by
  induction x using primeAlgebra_induction with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | hsingle g a =>
    rw [valuationDeriv_single, gradeTrace_single]
    by_cases hg : g = 0
    · subst hg; simp
    · simp [hg]

/-- **Card `(3)`.**  The valuation cyclic pairing. -/
noncomputable def valuationPairing (ℓ : ι) (a b : PrimeAlgebra ι) : ℂ :=
  gradeTrace (a * valuationDeriv ℓ b)

/-- **Theorem 1.3.**  The pairing is cyclic. -/
theorem valuationPairing_antisymm (ℓ : ι) (a b : PrimeAlgebra ι) :
    valuationPairing ℓ a b + valuationPairing ℓ b a = 0 := by
  have h := gradeTrace_valuationDeriv ℓ (a * b)
  rw [valuationDeriv_mul, map_add] at h
  rw [valuationPairing, valuationPairing, mul_comm b (valuationDeriv ℓ a)]
  linear_combination h

omit [DecidableEq ι] in
/-- **Theorem 1.4.**  The pairing kills the alternating Hochschild boundary. -/
theorem valuationPairing_hochschild (ℓ : ι) (a b c : PrimeAlgebra ι) :
    valuationPairing ℓ (a * b) c - valuationPairing ℓ a (b * c)
      + valuationPairing ℓ (c * a) b = 0 := by
  simp only [valuationPairing, valuationDeriv_mul, mul_add, map_add]
  have h1 : a * (valuationDeriv ℓ b * c) = c * a * valuationDeriv ℓ b := by ring
  rw [h1]
  ring

/-- **Card `(4)`.**  The prime/inverse-prime atom. -/
noncomputable def primeAtom (p : ι) : PrimeAlgebra ι :=
  AddMonoidAlgebra.single (Finsupp.single p (1 : ℤ)) (1 : ℂ)

/-- **Card `(4)`.**  Its inverse leg. -/
noncomputable def primeAtomInv (p : ι) : PrimeAlgebra ι :=
  AddMonoidAlgebra.single (Finsupp.single p (-1 : ℤ)) (1 : ℂ)

/-- **Card `(4)`.**  The atom has trace one. -/
theorem gradeTrace_atom (p : ι) : gradeTrace (primeAtom p * primeAtomInv p) = 1 :=
  gradeTrace_primeAtom p

/-- **Card `(5)`.**  The valuation coframe is the identity matrix on the prime atoms. -/
theorem valuationPairing_atom (ℓ p : ι) :
    valuationPairing ℓ (primeAtom p) (primeAtomInv p) = if ℓ = p then -1 else 0 :=
  valuationPairing_primeAtom p ℓ

end Coframe

/-! ## Coordinatewise independence and the no-cancellation law -/

section Independence

variable {ι M : Type*} [AddCommGroup M] [Module ℂ M]

/-- A family detected by a dual family with identity Gram matrix is linearly independent. -/
theorem linearIndependent_of_dual_identity [DecidableEq ι] (v : ι → M) (f : ι → M →ₗ[ℂ] ℂ)
    (h : ∀ i j, f i (v j) = if i = j then 1 else 0) : LinearIndependent ℂ v := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have := congrArg (f i) hg
  rw [map_sum, map_zero] at this
  simp only [map_smul, smul_eq_mul, h] at this
  rwa [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp [hi]), if_pos rfl,
    mul_one] at this

end Independence

/-! ## The diagonal physical defect -/

section Defect

variable {ι : Type*} [DecidableEq ι]

/-- **Card `(10)`.**  The diagonal physical defect multiplier at drift `a`. -/
noncomputable def defectMultiplier (P : ι → ℝ) (a : ℝ) (ℓ : ι) : ℂ :=
  ((1 - (P ℓ) ^ (2 * a) : ℝ) : ℂ)

omit [DecidableEq ι] in
/-- **Card `(12)`, critical case.**  At zero drift every multiplier vanishes. -/
theorem defectMultiplier_zero (P : ι → ℝ) (ℓ : ι) : defectMultiplier P 0 ℓ = 0 := by
  simp [defectMultiplier]

omit [DecidableEq ι] in
/-- **Card `(12)`, off-line case.**  Off the critical line every multiplier is nonzero. -/
theorem defectMultiplier_ne_zero {P : ι → ℝ} (hP : ∀ i, 1 < P i) {a : ℝ} (ha : a ≠ 0) (ℓ : ι) :
    defectMultiplier P a ℓ ≠ 0 := by
  have hpos : 0 < P ℓ := lt_trans one_pos (hP ℓ)
  have hne : (P ℓ) ^ (2 * a) ≠ 1 := by
    intro hcon
    have hlog : (2 * a) * Real.log (P ℓ) = 0 := by
      rw [← Real.log_rpow hpos, hcon, Real.log_one]
    rcases mul_eq_zero.1 hlog with h | h
    · exact ha (by linarith)
    · exact absurd h (Real.log_pos (hP ℓ)).ne'
  simp only [defectMultiplier, ne_eq, Complex.ofReal_eq_zero]
  intro hcon
  exact hne (by linarith)

/-- **Card `(11)`, `(12)`.**  Off the critical line the diagonal defect is injective on the prime
span: no finite cross-prime combination cancels it. -/
theorem defect_injective_of_ne_zero {P : ι → ℝ} (hP : ∀ i, 1 < P i) {a : ℝ} (ha : a ≠ 0)
    (s : Finset ι) (α : ι → ℂ)
    (hzero : ∀ ℓ : ι, ∑ p ∈ s, α p * (defectMultiplier P a ℓ *
      (if ℓ = p then (-1 : ℂ) else 0)) = 0) :
    ∀ p ∈ s, α p = 0 := by
  classical
  intro p hp
  have h := hzero p
  rw [Finset.sum_eq_single_of_mem p hp (fun j _ hj => by simp [Ne.symm hj])] at h
  rw [if_pos rfl] at h
  have hmul : defectMultiplier P a p ≠ 0 := defectMultiplier_ne_zero hP ha p
  have hkey : α p * defectMultiplier P a p = 0 := by linear_combination -h
  rcases mul_eq_zero.1 hkey with h1 | h1
  · exact h1
  · exact absurd h1 hmul

end Defect

/-! ## The scalar Kummer reader is a covector contraction -/

section ScalarContraction

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Card `(7)`.**  Unique factorization: the total logarithm is the valuation-weighted sum of the
prime logarithms. -/
theorem log_gradeNorm {P : ι → ℝ} (hP : ∀ i, 0 < P i) (g : PrimeGrades ι) :
    Real.log (gradeNorm P g) = ∑ ℓ ∈ g.support, (g ℓ : ℝ) * Real.log (P ℓ) := by
  rw [gradeNorm, Finsupp.prod, Real.log_prod]
  · exact Finset.sum_congr rfl fun ℓ _ => by rw [Real.log_zpow]
  · exact fun ℓ _ => (zpow_pos (hP ℓ) _).ne'

omit [DecidableEq ι] in
theorem smul_single (g : PrimeGrades ι) (c a : ℂ) :
    c • (AddMonoidAlgebra.single g a : PrimeAlgebra ι) = AddMonoidAlgebra.single g (c * a) := by
  have h : ((c • (AddMonoidAlgebra.single g a : PrimeAlgebra ι)).coeff)
      = (AddMonoidAlgebra.single g (c * a) : PrimeAlgebra ι).coeff := by
    rw [AddMonoidAlgebra.coeff_smul, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single,
      Finsupp.smul_single, smul_eq_mul]
  exact congrArg AddMonoidAlgebra.ofCoeff h

omit [DecidableEq ι] in
theorem single_finset_sum {κ : Type*} (g : PrimeGrades ι) (s : Finset κ) (f : κ → ℂ) :
    (AddMonoidAlgebra.single g (∑ i ∈ s, f i) : PrimeAlgebra ι)
      = ∑ i ∈ s, AddMonoidAlgebra.single g (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, AddMonoidAlgebra.single_add]

omit [DecidableEq ι] in
/-- **Card `(8)`.**  The logarithmic derivation is the log-weighted sum of the valuation
derivations. -/
theorem logDeriv_eq_sum_valuationDeriv {P : ι → ℝ} (hP : ∀ i, 0 < P i) (g : PrimeGrades ι)
    (c : ℂ) :
    AddMonoidAlgebra.single g (((Real.log (gradeNorm P g) : ℝ) : ℂ) * c)
      = ∑ ℓ ∈ g.support, ((Real.log (P ℓ) : ℝ) : ℂ) •
          valuationDeriv ℓ (AddMonoidAlgebra.single g c) := by
  have hsum : ∑ ℓ ∈ g.support, ((Real.log (P ℓ) : ℝ) : ℂ) •
      valuationDeriv ℓ (AddMonoidAlgebra.single g c)
      = AddMonoidAlgebra.single g
        ((∑ ℓ ∈ g.support, ((Real.log (P ℓ) : ℝ) : ℂ) * ((g ℓ : ℤ) : ℂ)) * c) := by
    rw [Finset.sum_mul, single_finset_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [valuationDeriv_single, smul_single]
    congr 1
    ring
  rw [hsum, log_gradeNorm hP g]
  congr 2
  push_cast
  exact Finset.sum_congr rfl fun ℓ _ => by ring

omit [DecidableEq ι] in
/-- **Card `(8)`.**  Hence the scalar Kummer pairing is the log covector applied to the valuation
coframe. -/
theorem logPairing_eq_sum {P : ι → ℝ} (hP : ∀ i, 0 < P i) (a : PrimeAlgebra ι)
    (g : PrimeGrades ι) (c : ℂ) :
    gradeTrace (a * AddMonoidAlgebra.single g (((Real.log (gradeNorm P g) : ℝ) : ℂ) * c))
      = ∑ ℓ ∈ g.support, ((Real.log (P ℓ) : ℝ) : ℂ) *
          valuationPairing ℓ a (AddMonoidAlgebra.single g c) := by
  rw [logDeriv_eq_sum_valuationDeriv hP g c, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul]
  rfl

end ScalarContraction

end HTGeometry.ConstraintRelativity
