import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Trace fibers of a field involution

For a nontrivial involution `σ`, division by `x-σ(x)` identifies the trace
kernel with the fixed subfield, and `x/(x-σ(x))` has trace one. Thus every
trace-one fiber has as many elements as the fixed subfield. The identity
involution instead gives the equation `2u=1`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open scoped Classical

variable {K : Type*} [Field K]

/-- The additive trace attached to a field endomorphism. -/
def involutionTrace (σ : K →+* K) : K →+ K := σ.toAddMonoidHom + AddMonoidHom.id K

/-- Trace is the sum of an element and its conjugate. -/
theorem involutionTrace_apply (σ : K →+* K) (x : K) : involutionTrace σ x = σ x + x := rfl

/-- A nonfixed element of an involution explicitly supplies a trace-one element. -/
theorem involutionTrace_exists_one (σ : K →+* K) (hσ : Function.Involutive σ)
    (x : K) (hx : σ x ≠ x) : ∃ u : K, involutionTrace σ u = 1 := by
  have hη : x - σ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hs : σ (x - σ x) = -(x - σ x) := by rw [map_sub, hσ]; ring
  refine ⟨x / (x - σ x), ?_⟩
  rw [involutionTrace_apply, map_div₀, hs, div_neg, add_comm,
    ← sub_eq_add_neg, ← sub_div, div_self hη]

/-- Scaling by a nonzero trace-zero difference identifies the trace kernel with the fixed field. -/
def involutionTraceKernelEquivFixed (σ : K →+* K) (hσ : Function.Involutive σ)
    (x : K) (hx : σ x ≠ x) : (involutionTrace σ).ker ≃ σ.eqLocusField (RingHom.id K) := by
  let η := x - σ x
  have hη : η ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hs : σ η = -η := by dsimp [η]; rw [map_sub, hσ]; ring
  refine
    { toFun := fun u => ⟨u.val / η, ?_⟩
      invFun := fun a => ⟨η * a.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change σ (u.val / η) = u.val / η
    have hu : σ u.val = -u.val := eq_neg_of_add_eq_zero_left u.property
    rw [map_div₀, hu, hs, neg_div_neg_eq]
  · change σ (η * a.val) + η * a.val = 0
    rw [map_mul, hs, (show σ a.val = a.val from a.property)]
    ring
  · intro u
    apply Subtype.ext
    change η * (u.val / η) = u.val
    field_simp
  · intro a
    apply Subtype.ext
    change (η * a.val) / η = a.val
    field_simp

/-- A nontrivial involution has one trace-one fiber's worth of points per fixed-field element. -/
theorem involution_trace_one_card (σ : K →+* K) (hσ : Function.Involutive σ)
    (hn : ∃ x : K, σ x ≠ x) :
    Nat.card {u : K // σ u + u = 1} = Nat.card (σ.eqLocusField (RingHom.id K)) := by
  obtain ⟨x, hx⟩ := hn
  obtain ⟨u, hu⟩ := involutionTrace_exists_one σ hσ x hx
  have hf := Nat.card_congr ((involutionTrace σ).fiberEquivKer u)
  simp only [Set.preimage, Set.mem_singleton_iff, hu, involutionTrace_apply] at hf
  exact hf.trans (Nat.card_congr (involutionTraceKernelEquivFixed σ hσ x hx))

/-- For the identity involution, trace one has one solution unless the characteristic is two. -/
theorem identity_trace_one_card :
    Nat.card {u : K // u + u = 1} = if (2 : K) = 0 then 0 else 1 := by
  by_cases h2 : (2 : K) = 0
  · rw [if_pos h2]
    apply Nat.card_eq_zero.mpr
    left
    refine ⟨fun u => ?_⟩
    have h : u.val + u.val = 0 := by rw [← two_mul, h2, zero_mul]
    exact zero_ne_one (h.symm.trans u.property)
  · rw [if_neg h2]
    letI : Nonempty {u : K // u + u = 1} := ⟨⟨(2 : K)⁻¹, by
      rw [← two_mul, mul_inv_cancel₀ h2]⟩⟩
    letI : Subsingleton {u : K // u + u = 1} := ⟨fun x y => Subtype.ext (by
      apply mul_left_cancel₀ h2
      rw [two_mul, two_mul, x.property, y.property])⟩
    exact Nat.card_unique

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
