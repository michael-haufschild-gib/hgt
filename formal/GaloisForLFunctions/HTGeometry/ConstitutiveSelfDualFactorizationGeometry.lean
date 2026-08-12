import Mathlib
import GaloisForLFunctions.HTGeometry.NonnegativeSumCriterionNoGo

/-!
# Self-dual factorization geometry and Cartan-work properness

An exact semantic--lineage recovery pair is not a point: it is canonically parameterized by its
invertible lineage gauge.  Adjoint reversal acts on that gauge by `s ↦ (star s)⁻¹`; its fixed locus
is exactly the balanced subgroup.  The two positive algebraic Gram coordinates are reciprocal, so
they retain the radial gauge while exchanging it under reversal.

The scalar Cartan work `4 sinh(x)^2` is nonnegative, even, and zero only at the balanced point.
For a finite packet, bounded work along every natural depth forces every radial rate to vanish.
This is the unconditional algebraic/properness core of ULF-FFM-2.  It is not an RH statement.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

section ExactRecovery

variable {G : Type*} [Group G]

/-- An exact semantic--lineage factorization of the identity in a group. -/
@[ext]
structure ExactRecoveryFactorization (G : Type*) [Group G] where
  semantic : G
  lineage : G
  recovery : semantic * lineage = 1

/-- Every gauge gives an exact recovery factorization. -/
def ExactRecoveryFactorization.fromGauge (s : G) : ExactRecoveryFactorization G where
  semantic := s⁻¹
  lineage := s
  recovery := inv_mul_cancel s

/-- Exact recovery reconstructs the semantic leg from the lineage leg. -/
theorem ExactRecoveryFactorization.semantic_eq_lineage_inv
    (F : ExactRecoveryFactorization G) : F.semantic = F.lineage⁻¹ := by
  apply mul_right_cancel (b := F.lineage)
  simpa using F.recovery

/-- **Gauge-torsor classification.**  Exact factorizations are canonically equivalent to gauges. -/
def exactRecoveryFactorizationEquiv : ExactRecoveryFactorization G ≃ G where
  toFun F := F.lineage
  invFun := ExactRecoveryFactorization.fromGauge
  left_inv F := by
    apply ExactRecoveryFactorization.ext
    · exact F.semantic_eq_lineage_inv.symm
    · rfl
  right_inv s := rfl

end ExactRecovery

section AdjointReversal

variable {G : Type*} [Group G] [StarMul G]

/-- Adjoint reversal on gauge coordinates. -/
def factorizationGaugeReversal (s : G) : G := (star s)⁻¹

/-- Balanced gauges are fixed by adjoint reversal. -/
def IsAdjointBalancedGauge (s : G) : Prop := star s * s = 1

/-- Positive lineage Gram coordinate in abstract multiplicative form. -/
def lineageGramGauge (s : G) : G := star s * s

/-- Positive semantic Gram coordinate in abstract multiplicative form. -/
def semanticGramGauge (s : G) : G := s⁻¹ * (star s)⁻¹

/-- Swap and adjoint the two recovery legs. -/
def ExactRecoveryFactorization.reverse
    (F : ExactRecoveryFactorization G) : ExactRecoveryFactorization G where
  semantic := star F.lineage
  lineage := star F.semantic
  recovery := by
    rw [← star_mul, F.recovery]
    simp

/-- Adjoint gauge reversal is involutive. -/
theorem factorizationGaugeReversal_involutive (s : G) :
    factorizationGaugeReversal (factorizationGaugeReversal s) = s := by
  simp [factorizationGaugeReversal]

/-- A gauge is fixed by reversal exactly when it is balanced. -/
theorem factorizationGaugeReversal_eq_self_iff (s : G) :
    factorizationGaugeReversal s = s ↔ IsAdjointBalancedGauge s := by
  constructor
  · intro h
    have hs := congrArg (fun x : G => x⁻¹) h
    simp only [factorizationGaugeReversal, inv_inv] at hs
    rw [IsAdjointBalancedGauge, hs]
    simp
  · intro h
    rw [IsAdjointBalancedGauge] at h
    rw [factorizationGaugeReversal]
    apply mul_left_cancel (a := star s)
    simpa using h.symm

/-- The semantic Gram is the inverse of the lineage Gram. -/
theorem semanticGramGauge_eq_lineageGramGauge_inv (s : G) :
    semanticGramGauge s = (lineageGramGauge s)⁻¹ := by
  simp [semanticGramGauge, lineageGramGauge]

/-- **Reciprocal Gram conservation.**  The two leg Grams multiply to the identity. -/
theorem semanticGramGauge_mul_lineageGramGauge (s : G) :
    semanticGramGauge s * lineageGramGauge s = 1 := by
  rw [semanticGramGauge_eq_lineageGramGauge_inv]
  simp

/-- Reversal exchanges the positive lineage and semantic Gram coordinates. -/
theorem lineageGramGauge_reversal_eq_semanticGramGauge (s : G) :
    lineageGramGauge (factorizationGaugeReversal s) = semanticGramGauge s := by
  simp [lineageGramGauge, factorizationGaugeReversal, semanticGramGauge]

/-- Reversal acts on the factorization torsor by gauge reversal. -/
theorem reverse_lineage_eq_gaugeReversal (F : ExactRecoveryFactorization G) :
    F.reverse.lineage = factorizationGaugeReversal F.lineage := by
  change star F.semantic = (star F.lineage)⁻¹
  simp [F.semantic_eq_lineage_inv, star_inv]

/-- Reversing both recovery legs twice returns the original factorization. -/
theorem exactRecoveryFactorization_reverse_reverse (F : ExactRecoveryFactorization G) :
    F.reverse.reverse = F := by
  apply ExactRecoveryFactorization.ext <;> simp [ExactRecoveryFactorization.reverse]

/-- A recovery factorization is self-dual exactly when its lineage gauge is balanced. -/
theorem exactRecoveryFactorization_reverse_fixed_iff (F : ExactRecoveryFactorization G) :
    F.reverse = F ↔ IsAdjointBalancedGauge F.lineage := by
  constructor
  · intro h
    apply (factorizationGaugeReversal_eq_self_iff F.lineage).mp
    rw [← reverse_lineage_eq_gaugeReversal]
    exact congrArg ExactRecoveryFactorization.lineage h
  · intro h
    apply exactRecoveryFactorizationEquiv.injective
    change F.reverse.lineage = F.lineage
    rw [reverse_lineage_eq_gaugeReversal]
    exact (factorizationGaugeReversal_eq_self_iff F.lineage).mpr h

end AdjointReversal

noncomputable section CartanWork

/-- One radial Cartan mode's reciprocal positive work. -/
def cartanModeWork (x : ℝ) : ℝ := 4 * Real.sinh x ^ 2

/-- Reciprocal exponential form of Cartan work. -/
theorem cartanModeWork_add_two (x : ℝ) :
    cartanModeWork x + 2 = Real.exp (2 * x) + Real.exp (-2 * x) := by
  have hmul : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hpos : Real.exp (2 * x) = Real.exp x ^ 2 := by
    rw [show 2 * x = x + x by ring, Real.exp_add, pow_two]
  have hneg : Real.exp (-2 * x) = Real.exp (-x) ^ 2 := by
    rw [show -2 * x = -x + -x by ring, Real.exp_add, pow_two]
  rw [cartanModeWork, Real.sinh_eq, hpos, hneg]
  field_simp
  nlinarith

/-- Cartan work is nonnegative. -/
theorem cartanModeWork_nonneg (x : ℝ) : 0 ≤ cartanModeWork x := by
  exact mul_nonneg (by norm_num) (sq_nonneg _)

/-- Reversal leaves Cartan work invariant. -/
theorem cartanModeWork_neg (x : ℝ) : cartanModeWork (-x) = cartanModeWork x := by
  simp [cartanModeWork]

/-- A mode has zero work exactly at zero radial displacement. -/
theorem cartanModeWork_eq_zero_iff (x : ℝ) : cartanModeWork x = 0 ↔ x = 0 := by
  simp [cartanModeWork, Real.sinh_eq_zero]

/-- **Scalar properness.**  Bounded work along all natural depths forces zero radial rate. -/
theorem eq_zero_of_bounded_cartanModeWork {x : ℝ}
    (h : ∃ C : ℝ, ∀ n : ℕ, cartanModeWork ((n : ℝ) * x) ≤ C) : x = 0 := by
  obtain ⟨C, hC⟩ := h
  have hpos : 2 * x ≤ 0 := by
    apply rate_nonpos_of_eventually_bounded (c := 1) (C := C + 2) (by norm_num)
    filter_upwards [] with n
    have hsum := hC n
    have hid := cartanModeWork_add_two ((n : ℝ) * x)
    have hexp : Real.exp ((n : ℝ) * (2 * x)) ≤ C + 2 := by
      calc
        Real.exp ((n : ℝ) * (2 * x)) = Real.exp (2 * ((n : ℝ) * x)) := by
          congr 1
          ring
        _ ≤ cartanModeWork ((n : ℝ) * x) + 2 := by
          nlinarith [Real.exp_pos (-2 * ((n : ℝ) * x))]
        _ ≤ C + 2 := by linarith
    simpa using hexp
  have hneg : -2 * x ≤ 0 := by
    apply rate_nonpos_of_eventually_bounded (c := 1) (C := C + 2) (by norm_num)
    filter_upwards [] with n
    have hsum := hC n
    have hid := cartanModeWork_add_two ((n : ℝ) * x)
    have hexp : Real.exp ((n : ℝ) * (-2 * x)) ≤ C + 2 := by
      calc
        Real.exp ((n : ℝ) * (-2 * x)) = Real.exp (-2 * ((n : ℝ) * x)) := by
          congr 1
          ring
        _ ≤ cartanModeWork ((n : ℝ) * x) + 2 := by
          nlinarith [Real.exp_pos (2 * ((n : ℝ) * x))]
        _ ≤ C + 2 := by linarith
    simpa using hexp
  linarith

variable {ι : Type*} [Fintype ι]

/-- Work of a finite packet of Cartan modes at depth `t`. -/
def cartanPacketWork (t : ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, cartanModeWork (t * x i)

/-- Finite packet work is nonnegative. -/
theorem cartanPacketWork_nonneg (t : ℝ) (x : ι → ℝ) : 0 ≤ cartanPacketWork t x := by
  exact Finset.sum_nonneg fun i _ => cartanModeWork_nonneg _

/-- Packet work at unit depth vanishes exactly when every mode vanishes. -/
theorem cartanPacketWork_eq_zero_iff (x : ι → ℝ) :
    cartanPacketWork 1 x = 0 ↔ x = 0 := by
  rw [cartanPacketWork, Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h
      funext i
      exact (cartanModeWork_eq_zero_iff (x i)).mp
        (by simpa using h i (Finset.mem_univ i))
    · rintro rfl i hi
      simp [cartanModeWork]
  · intro i hi
    exact cartanModeWork_nonneg _

/-- **Finite packet properness.**  Uniformly bounded work along natural depths selects the zero
radial packet. -/
theorem eq_zero_of_bounded_cartanPacketWork {x : ι → ℝ}
    (h : ∃ C : ℝ, ∀ n : ℕ, cartanPacketWork n x ≤ C) : x = 0 := by
  obtain ⟨C, hC⟩ := h
  funext i
  apply eq_zero_of_bounded_cartanModeWork
  refine ⟨C, fun n => ?_⟩
  apply le_trans
    (Finset.single_le_sum (fun j _ => cartanModeWork_nonneg _) (Finset.mem_univ i))
  simpa [cartanPacketWork] using hC n

end CartanWork

end GaloisForLFunctions.HTGeometry
