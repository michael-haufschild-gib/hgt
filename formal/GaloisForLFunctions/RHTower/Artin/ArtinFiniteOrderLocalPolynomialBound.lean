import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerFactor
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Finite-order local characteristic-polynomial control

This module supplies finite-image local-factor control for Artin Euler factors: every
characteristic-polynomial root of a finite-order complex action has norm one, its reversed
characteristic polynomial is root-free in the unit disk, and its inverse has an explicit norm
bound.  A formal inverse or constant term alone supplies none of these facts.
-/

noncomputable section

universe u v w x

namespace GaloisForLFunctions

open scoped Pointwise

variable {W : Type u} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

section PolynomialFactorization

open Polynomial

/-- Reversing `X` gives the constant polynomial one. -/
lemma reverse_X_complex : Polynomial.reverse (X : ℂ[X]) = 1 := by
  change Polynomial.reflect (Polynomial.natDegree (X : ℂ[X])) X = 1
  simp

/-- Reversing the monic linear factor `X - μ` gives `1 - μX`. -/
lemma reverse_X_sub_C (μ : ℂ) :
    Polynomial.reverse (X - C μ) = 1 - C μ * X := by
  simpa [sub_eq_add_neg, reverse_X_complex] using
    (Polynomial.reverse_add_C X (-μ))

/-- The reverse of a split monic complex polynomial is its product of reversed linear root
factors. -/
theorem reverse_eq_prod_roots_one_sub_C_mul_X
    {p : ℂ[X]} (hp : p.Splits) (hmonic : p.Monic) :
    p.reverse = (p.roots.map fun μ => 1 - C μ * X).prod := by
  calc
    p.reverse = (p.roots.map fun μ => X - C μ).prod.reverse :=
      congrArg Polynomial.reverse (hp.eq_prod_roots_of_monic hmonic)
    _ = (p.roots.map fun μ => 1 - C μ * X).prod := by
      induction p.roots using Multiset.induction_on with
      | empty => simp [Polynomial.reverse]
      | cons μ s ih =>
          simp only [Multiset.map_cons, Multiset.prod_cons]
          rw [Polynomial.reverse_mul_of_domain, reverse_X_sub_C, ih]

/-- Evaluation of the reverse of a split monic complex polynomial is the product of the factors
`1 - μz` over its roots. -/
theorem reverse_eval_eq_prod_roots_one_sub_mul
    {p : ℂ[X]} (hp : p.Splits) (hmonic : p.Monic) (z : ℂ) :
    p.reverse.eval z = (p.roots.map fun μ => 1 - μ * z).prod := by
  rw [reverse_eq_prod_roots_one_sub_C_mul_X hp hmonic]
  simp [eval_multiset_prod]

end PolynomialFactorization

/-- Every characteristic-polynomial root of a finite-order complex linear action lies on the unit
circle. -/
theorem finiteOrder_charpoly_root_norm_one
    (A : Module.End ℂ W) {n : ℕ} (hn : n ≠ 0) (hA : A ^ n = 1)
    {μ : ℂ} (hμ : A.charpoly.IsRoot μ) : ‖μ‖ = 1 := by
  have hEigen := (Module.End.hasEigenvalue_iff_isRoot_charpoly A μ).mpr hμ
  obtain ⟨x, hx⟩ := hEigen.exists_hasEigenvector
  have hxpow : μ ^ n • x = 1 • x := by
    rw [← hx.pow_apply n, hA, Module.End.one_apply]
    simp
  have hzero : (μ ^ n - 1) • x = 0 := by
    rw [sub_smul, hxpow]
    simp
  have hμpow : μ ^ n = 1 :=
    sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hx.2)
  exact Complex.norm_eq_one_of_pow_eq_one hμpow hn

/-- The reversed characteristic polynomial of a finite-order complex action is root-free on the
open unit disk. -/
theorem finiteOrder_charpoly_reverse_eval_ne_zero
    (A : Module.End ℂ W) {n : ℕ} (hn : n ≠ 0) (hA : A ^ n = 1)
    {z : ℂ} (hz : ‖z‖ < 1) : A.charpoly.reverse.eval z ≠ 0 := by
  rw [reverse_eval_eq_prod_roots_one_sub_mul
    (IsAlgClosed.splits A.charpoly) A.charpoly_monic z]
  apply Multiset.prod_ne_zero
  intro hzeroMem
  rcases Multiset.mem_map.mp hzeroMem with ⟨μ, hμ, hzero⟩
  have hroot : A.charpoly.IsRoot μ := Polynomial.isRoot_of_mem_roots hμ
  have hμnorm := finiteOrder_charpoly_root_norm_one A hn hA hroot
  have hfactor : 1 - μ * z = 0 := by simpa using hzero
  have hmul : μ * z = 1 := (sub_eq_zero.mp hfactor).symm
  have hznorm : ‖z‖ = 1 := by
    calc
      ‖z‖ = ‖μ‖ * ‖z‖ := by rw [hμnorm, one_mul]
      _ = ‖μ * z‖ := (norm_mul μ z).symm
      _ = ‖(1 : ℂ)‖ := by rw [hmul]
      _ = 1 := norm_one
  exact (ne_of_lt hz) hznorm

/-- A finite-order complex linear action has an explicit reciprocal local-factor bound on the
open unit disk.  Nonvanishing is derived from finite order inside the proof. -/
theorem finiteOrder_charpoly_reverse_eval_norm_inv_le
    (A : Module.End ℂ W) {n : ℕ} (hn : n ≠ 0) (hA : A ^ n = 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(A.charpoly.reverse.eval z)⁻¹‖ ≤ (1 - ‖z‖)⁻¹ ^ Module.finrank ℂ W := by
  have hbasepos : 0 < 1 - ‖z‖ := sub_pos.mpr hz
  have hrootbound : ∀ μ ∈ A.charpoly.roots, 1 - ‖z‖ ≤ ‖1 - μ * z‖ := by
    intro μ hμ
    have hroot : A.charpoly.IsRoot μ := Polynomial.isRoot_of_mem_roots hμ
    have hμnorm := finiteOrder_charpoly_root_norm_one A hn hA hroot
    calc
      1 - ‖z‖ = ‖(1 : ℂ)‖ - ‖μ * z‖ := by
        rw [norm_one, norm_mul, hμnorm, one_mul]
      _ ≤ ‖(1 : ℂ) - μ * z‖ := norm_sub_norm_le _ _
  have hprod : (1 - ‖z‖) ^ A.charpoly.roots.card ≤
      (A.charpoly.roots.map fun μ => ‖1 - μ * z‖).prod := by
    have haux : ∀ m : Multiset ℂ,
        (∀ μ ∈ m, 1 - ‖z‖ ≤ ‖1 - μ * z‖) →
          (1 - ‖z‖) ^ m.card ≤ (m.map fun μ => ‖1 - μ * z‖).prod := by
      intro m
      induction m using Multiset.induction_on with
      | empty => simp
      | cons μ m ih =>
          intro hm
          simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons]
          rw [pow_succ]
          calc
            (1 - ‖z‖) ^ m.card * (1 - ‖z‖) ≤
                (1 - ‖z‖) ^ m.card * ‖1 - μ * z‖ :=
              mul_le_mul_of_nonneg_left (hm μ (by simp)) (pow_nonneg hbasepos.le _)
            _ = ‖1 - μ * z‖ * (1 - ‖z‖) ^ m.card := mul_comm _ _
            _ ≤ ‖1 - μ * z‖ * (m.map fun μ => ‖1 - μ * z‖).prod :=
              mul_le_mul_of_nonneg_left
                (ih fun ν hν => hm ν (by simp [hν])) (norm_nonneg _)
    exact haux _ hrootbound
  have hnorm :
      ‖(A.charpoly.roots.map fun μ => 1 - μ * z).prod‖ =
        (A.charpoly.roots.map fun μ => ‖1 - μ * z‖).prod := by
    change (normHom.toMonoidHom : ℂ →* ℝ)
        (A.charpoly.roots.map fun μ => 1 - μ * z).prod =
      (A.charpoly.roots.map fun μ =>
        (normHom.toMonoidHom : ℂ →* ℝ) (1 - μ * z)).prod
    simpa only [Multiset.map_map, Function.comp_apply] using
      (normHom.toMonoidHom : ℂ →* ℝ).map_multiset_prod
        (A.charpoly.roots.map fun μ => 1 - μ * z)
  have hprod' : (1 - ‖z‖) ^ A.charpoly.roots.card ≤
      ‖(A.charpoly.roots.map fun μ => 1 - μ * z).prod‖ :=
    hprod.trans_eq hnorm.symm
  have hcard : A.charpoly.roots.card = Module.finrank ℂ W := by
    calc
      A.charpoly.roots.card = A.charpoly.natDegree :=
        (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots.symm
      _ = Module.finrank ℂ W := A.charpoly_natDegree
  have hlower : (1 - ‖z‖) ^ Module.finrank ℂ W ≤ ‖A.charpoly.reverse.eval z‖ := by
    calc
      (1 - ‖z‖) ^ Module.finrank ℂ W = (1 - ‖z‖) ^ A.charpoly.roots.card := by rw [hcard]
      _ ≤ ‖(A.charpoly.roots.map fun μ => 1 - μ * z).prod‖ := hprod'
      _ = ‖A.charpoly.reverse.eval z‖ := by
        exact congrArg norm
          (reverse_eval_eq_prod_roots_one_sub_mul
            (IsAlgClosed.splits A.charpoly) A.charpoly_monic z).symm
  have hnormpos : 0 < ‖A.charpoly.reverse.eval z‖ :=
    (pow_pos hbasepos _).trans_le hlower
  have hinv : ‖A.charpoly.reverse.eval z‖⁻¹ ≤
      ((1 - ‖z‖) ^ Module.finrank ℂ W)⁻¹ :=
    (inv_le_inv₀ hnormpos (pow_pos hbasepos _)).mpr hlower
  simpa only [norm_inv, inv_pow] using hinv

/-- On the closed half unit disk, the inverse of a finite-order local characteristic polynomial
differs from one by at most `4 ^ dim W * ‖z‖`. -/
theorem finiteOrder_charpoly_reverse_eval_inv_sub_one_norm_le
    (A : Module.End ℂ W) {n : ℕ} (hn : n ≠ 0) (hA : A ^ n = 1)
    {z : ℂ} (hz : ‖z‖ ≤ (2 : ℝ)⁻¹) :
    ‖(A.charpoly.reverse.eval z)⁻¹ - 1‖ ≤
      (4 : ℝ) ^ Module.finrank ℂ W * ‖z‖ := by
  have hzlt : ‖z‖ < 1 := by
    calc
      ‖z‖ ≤ (2 : ℝ)⁻¹ := hz
      _ < 1 := by norm_num
  have hunit : ∀ μ ∈ A.charpoly.roots, ‖μ‖ = 1 := by
    intro μ hμ
    exact finiteOrder_charpoly_root_norm_one A hn hA
      (Polynomial.isRoot_of_mem_roots hμ)
  have hfactor : ∀ μ ∈ A.charpoly.roots, ‖1 - μ * z‖ ≤ 2 := by
    intro μ hμ
    have hμ := hunit μ hμ
    calc
      ‖1 - μ * z‖ ≤ ‖(1 : ℂ)‖ + ‖μ * z‖ := norm_sub_le _ _
      _ = 1 + ‖z‖ := by rw [norm_one, norm_mul, hμ, one_mul]
      _ ≤ 2 := by nlinarith [hz]
  have hprodNorm : ∀ m : Multiset ℂ,
      (∀ μ ∈ m, ‖μ‖ = 1) →
        ‖(m.map fun μ => 1 - μ * z).prod‖ ≤ (2 : ℝ) ^ m.card := by
    intro m hm
    induction m using Multiset.induction_on with
    | empty => simp
    | cons μ m ih =>
        have hμ : ‖μ‖ = 1 := hm μ (by simp)
        have hm' : ∀ ν ∈ m, ‖ν‖ = 1 := by
          intro ν hν
          exact hm ν (by simp [hν])
        simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
        rw [pow_succ]
        calc
          ‖(1 - μ * z) * (m.map fun ν => 1 - ν * z).prod‖ ≤
              ‖1 - μ * z‖ * ‖(m.map fun ν => 1 - ν * z).prod‖ :=
            norm_mul_le _ _
          _ ≤ 2 * (2 : ℝ) ^ m.card := by
            apply mul_le_mul
            · calc
                ‖1 - μ * z‖ ≤ ‖(1 : ℂ)‖ + ‖μ * z‖ := norm_sub_le _ _
                _ = 1 + ‖z‖ := by rw [norm_one, norm_mul, hμ, one_mul]
                _ ≤ 2 := by nlinarith [hz]
            · exact ih hm'
            · exact norm_nonneg _
            · positivity
          _ = (2 : ℝ) ^ m.card * 2 := by ring
  have hprodDiff : ∀ m : Multiset ℂ,
      (∀ μ ∈ m, ‖μ‖ = 1) →
        ‖(m.map fun μ => 1 - μ * z).prod - 1‖ ≤
          (2 : ℝ) ^ m.card * ‖z‖ := by
    intro m hm
    induction m using Multiset.induction_on with
    | empty => simp
    | cons μ m ih =>
        have hμ : ‖μ‖ = 1 := hm μ (by simp)
        have hm' : ∀ ν ∈ m, ‖ν‖ = 1 := by
          intro ν hν
          exact hm ν (by simp [hν])
        have htailNorm := hprodNorm m hm'
        have htailDiff := ih hm'
        simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
        rw [pow_succ]
        rw [show (1 - μ * z) * (m.map fun ν => 1 - ν * z).prod - 1 =
          ((m.map fun ν => 1 - ν * z).prod - 1) -
            (μ * z) * (m.map fun ν => 1 - ν * z).prod by ring]
        calc
          ‖((m.map fun ν => 1 - ν * z).prod - 1) -
              (μ * z) * (m.map fun ν => 1 - ν * z).prod‖ ≤
              ‖(m.map fun ν => 1 - ν * z).prod - 1‖ +
                ‖(μ * z) * (m.map fun ν => 1 - ν * z).prod‖ :=
            norm_sub_le _ _
          _ ≤ (2 : ℝ) ^ m.card * ‖z‖ +
                ‖μ * z‖ * ‖(m.map fun ν => 1 - ν * z).prod‖ := by
            apply add_le_add htailDiff
            exact norm_mul_le _ _
          _ ≤ (2 : ℝ) ^ m.card * ‖z‖ +
                ‖z‖ * (2 : ℝ) ^ m.card := by
            apply add_le_add le_rfl
            rw [norm_mul, hμ, one_mul]
            exact mul_le_mul_of_nonneg_left htailNorm (norm_nonneg _)
          _ = (2 : ℝ) ^ m.card * 2 * ‖z‖ := by ring
  have hcard : A.charpoly.roots.card = Module.finrank ℂ W := by
    calc
      A.charpoly.roots.card = A.charpoly.natDegree :=
        (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots.symm
      _ = Module.finrank ℂ W := A.charpoly_natDegree
  have hdiff : ‖A.charpoly.reverse.eval z - 1‖ ≤
      (2 : ℝ) ^ Module.finrank ℂ W * ‖z‖ := by
    rw [reverse_eval_eq_prod_roots_one_sub_mul
      (IsAlgClosed.splits A.charpoly) A.charpoly_monic z]
    have hroots := hprodDiff A.charpoly.roots hunit
    simpa only [hcard] using hroots
  have hbasepos : 0 < 1 - ‖z‖ := sub_pos.mpr hzlt
  have hinvbase : (1 - ‖z‖)⁻¹ ≤ (2 : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ hbasepos).mpr
    nlinarith [hz]
  have hinvNorm : ‖(A.charpoly.reverse.eval z)⁻¹‖ ≤
      (2 : ℝ) ^ Module.finrank ℂ W := by
    refine (finiteOrder_charpoly_reverse_eval_norm_inv_le A hn hA hzlt).trans ?_
    exact pow_le_pow_left₀ (by positivity) hinvbase _
  have hnonzero := finiteOrder_charpoly_reverse_eval_ne_zero A hn hA hzlt
  have hid : (A.charpoly.reverse.eval z)⁻¹ - 1 =
      (A.charpoly.reverse.eval z)⁻¹ * (1 - A.charpoly.reverse.eval z) := by
    rw [mul_sub, mul_one, inv_mul_cancel₀ hnonzero]
  calc
    ‖(A.charpoly.reverse.eval z)⁻¹ - 1‖ =
        ‖(A.charpoly.reverse.eval z)⁻¹ * (1 - A.charpoly.reverse.eval z)‖ := by
      rw [hid]
    _ = ‖(A.charpoly.reverse.eval z)⁻¹‖ * ‖A.charpoly.reverse.eval z - 1‖ := by
      rw [norm_mul, norm_sub_rev]
    _ ≤ (2 : ℝ) ^ Module.finrank ℂ W *
        ((2 : ℝ) ^ Module.finrank ℂ W * ‖z‖) := by
      exact mul_le_mul hinvNorm hdiff (norm_nonneg _) (by positivity)
    _ = (4 : ℝ) ^ Module.finrank ℂ W * ‖z‖ := by
      rw [← mul_assoc, ← mul_pow]
      norm_num

section ArithmeticSpecialization

variable {R S G : Type x} {V : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
variable [Algebra.IsInvariant R S G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The actual Frobenius--inertia Artin polynomial is nonzero at every point of the open unit
disk.  This is a finite-image theorem, not an assumed Euler-factor property. -/
theorem frobeniusInertiaEulerPolynomial_eval_ne_zero_of_norm_lt_one
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (ρ : Representation ℂ G V) {z : ℂ} (hz : ‖z‖ < 1) :
    (frobeniusInertiaEulerPolynomial (R := R) Q ρ).eval z ≠ 0 := by
  rw [frobeniusInertiaEulerPolynomial_eq_action]
  exact finiteOrder_charpoly_reverse_eval_ne_zero
    (frobeniusInertiaAction (R := R) Q ρ) Nat.card_pos.ne'
    (frobeniusInertiaAction_pow_natCard_eq_one (R := R) Q ρ) hz

/-- The actual Frobenius--inertia Euler factor has the finite-order reciprocal bound with its
precise inertia-invariant dimension. -/
theorem frobeniusInertiaEulerPolynomial_eval_norm_inv_le_of_norm_lt_one
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (ρ : Representation ℂ G V) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖((frobeniusInertiaEulerPolynomial (R := R) Q ρ).eval z)⁻¹‖ ≤
      (1 - ‖z‖)⁻¹ ^ Module.finrank ℂ
        (Representation.invariants
          ((ρ.comp (MulAction.stabilizer G Q).subtype).comp
            (Q.inertia (MulAction.stabilizer G Q)).subtype)) := by
  rw [frobeniusInertiaEulerPolynomial_eq_action]
  exact finiteOrder_charpoly_reverse_eval_norm_inv_le
    (frobeniusInertiaAction (R := R) Q ρ) Nat.card_pos.ne'
    (frobeniusInertiaAction_pow_natCard_eq_one (R := R) Q ρ) hz

/-- A uniform reciprocal bound for actual Frobenius--inertia Euler factors, depending only on
the ambient representation dimension. -/
theorem frobeniusInertiaEulerPolynomial_eval_norm_inv_le_of_norm_lt_one_finrank
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (ρ : Representation ℂ G V) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖((frobeniusInertiaEulerPolynomial (R := R) Q ρ).eval z)⁻¹‖ ≤
      (1 - ‖z‖)⁻¹ ^ Module.finrank ℂ V := by
  calc
    ‖((frobeniusInertiaEulerPolynomial (R := R) Q ρ).eval z)⁻¹‖ ≤
        (1 - ‖z‖)⁻¹ ^ Module.finrank ℂ
          (Representation.invariants
            ((ρ.comp (MulAction.stabilizer G Q).subtype).comp
              (Q.inertia (MulAction.stabilizer G Q)).subtype)) :=
      frobeniusInertiaEulerPolynomial_eval_norm_inv_le_of_norm_lt_one
        (R := R) Q ρ hz
    _ ≤ (1 - ‖z‖)⁻¹ ^ Module.finrank ℂ V := by
      apply pow_le_pow_right₀
      · exact (one_le_inv₀ (sub_pos.mpr hz)).mpr (sub_le_self _ (norm_nonneg _))
      · exact Submodule.finrank_le _

/-- On the half unit disk, an actual Frobenius--inertia Euler reciprocal differs from one by a
finite-image bound with its precise invariant dimension. -/
theorem frobeniusInertiaEulerPolynomial_eval_inv_sub_one_norm_le_of_norm_le_half
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (ρ : Representation ℂ G V) {z : ℂ} (hz : ‖z‖ ≤ (2 : ℝ)⁻¹) :
    ‖((frobeniusInertiaEulerPolynomial (R := R) Q ρ).eval z)⁻¹ - 1‖ ≤
      (4 : ℝ) ^ Module.finrank ℂ
        (Representation.invariants
          ((ρ.comp (MulAction.stabilizer G Q).subtype).comp
            (Q.inertia (MulAction.stabilizer G Q)).subtype)) * ‖z‖ := by
  rw [frobeniusInertiaEulerPolynomial_eq_action]
  exact finiteOrder_charpoly_reverse_eval_inv_sub_one_norm_le
    (frobeniusInertiaAction (R := R) Q ρ) Nat.card_pos.ne'
    (frobeniusInertiaAction_pow_natCard_eq_one (R := R) Q ρ) hz

/-- A uniform half-unit-disk difference bound for actual Frobenius--inertia Euler reciprocals,
depending only on the ambient representation dimension. -/
theorem frobeniusInertiaEulerPolynomial_eval_inv_sub_one_norm_le_of_norm_le_half_finrank
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (ρ : Representation ℂ G V) {z : ℂ} (hz : ‖z‖ ≤ (2 : ℝ)⁻¹) :
    ‖((frobeniusInertiaEulerPolynomial (R := R) Q ρ).eval z)⁻¹ - 1‖ ≤
      (4 : ℝ) ^ Module.finrank ℂ V * ‖z‖ := by
  calc
    ‖((frobeniusInertiaEulerPolynomial (R := R) Q ρ).eval z)⁻¹ - 1‖ ≤
        (4 : ℝ) ^ Module.finrank ℂ
          (Representation.invariants
            ((ρ.comp (MulAction.stabilizer G Q).subtype).comp
              (Q.inertia (MulAction.stabilizer G Q)).subtype)) * ‖z‖ :=
      frobeniusInertiaEulerPolynomial_eval_inv_sub_one_norm_le_of_norm_le_half
        (R := R) Q ρ hz
    _ ≤ (4 : ℝ) ^ Module.finrank ℂ V * ‖z‖ := by
      apply mul_le_mul_of_nonneg_right
      · exact pow_le_pow_right₀ (by norm_num) (Submodule.finrank_le _)
      · exact norm_nonneg _

end ArithmeticSpecialization

end GaloisForLFunctions
