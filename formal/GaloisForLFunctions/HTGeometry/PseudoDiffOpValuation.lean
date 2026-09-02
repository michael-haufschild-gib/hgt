import GaloisForLFunctions.HTGeometry.PseudoDiffOpDegree
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# The discrete valuation of the rational pseudodifferential skew field

The operator order on `PseudoDiffOp K` satisfies the nonarchimedean triangle inequality.  Its
negative, with zero sent to `⊤`, is therefore an honest additive valuation.  This is the valuation
needed to form the completion and valuation lattices in the differential variational building.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

open OreLocalization
open scoped OreLocalization
open scoped nonZeroDivisors

variable {K : Type u} [Field K] [Differential K]

/-- Pseudodifferential order satisfies the strong triangle inequality away from zero, where the
project's finite-valued `ordQ` convention deliberately records `ordQ 0 = 0`. -/
theorem ordQ_add_le_max_of_ne_zero (x y : PseudoDiffOp K)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    ordQ (x + y) ≤ max (ordQ x) (ordQ y) := by
  induction x using OreLocalization.ind with
  | _ r₁ s₁ =>
    induction y using OreLocalization.ind with
    | _ r₂ s₂ =>
      have hs₁ : (s₁ : DiffOp K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s₁.2
      have hs₂ : (s₂ : DiffOp K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s₂.2
      have hr₁ : r₁ ≠ 0 := by
        intro h
        exact hx (by rw [h]; exact OreLocalization.zero_oreDiv s₁)
      have hr₂ : r₂ ≠ 0 := by
        intro h
        exact hy (by rw [h]; exact OreLocalization.zero_oreDiv s₂)
      let a : DiffOp K := oreDenom (s₁ : DiffOp K) s₂
      let b : DiffOp K := oreNum (s₁ : DiffOp K) s₂
      have ha : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp
        (oreDenom (s₁ : DiffOp K) s₂).2
      have hab : a * (s₁ : DiffOp K) = b * (s₂ : DiffOp K) := ore_eq (s₁ : DiffOp K) s₂
      have hb : b ≠ 0 := by
        intro hb
        rw [hb, zero_mul] at hab
        exact (mul_ne_zero ha hs₁) hab
      have hnum : a * r₁ + b * r₂ ≠ 0 := by
        intro hnum
        apply hxy
        rw [oreDiv_add_oreDiv]
        change (a * r₁ + b * r₂) /ₒ (oreDenom (s₁ : DiffOp K) s₂ * s₁) = 0
        rw [hnum]
        exact OreLocalization.zero_oreDiv _
      have hnum' : oreDenom (s₁ : DiffOp K) s₂ • r₁ + oreNum (s₁ : DiffOp K) s₂ • r₂ ≠ 0 := by
        simpa [a, b, Submonoid.smul_def, smul_eq_mul] using hnum
      rw [oreDiv_add_oreDiv, ordQ_oreDiv, if_neg hnum',
        ordQ_oreDiv, if_neg hr₁, ordQ_oreDiv, if_neg hr₂]
      simp only [smul_eq_mul]
      change ((degree (a * r₁ + b * r₂) : ℤ) - (degree (a * (s₁ : DiffOp K)) : ℤ)) ≤
        max ((degree r₁ : ℤ) - (degree (s₁ : DiffOp K) : ℤ))
          ((degree r₂ : ℤ) - (degree (s₂ : DiffOp K) : ℤ))
      have hdegadd : (degree (a * r₁ + b * r₂) : ℤ) ≤
          max (degree (a * r₁) : ℤ) (degree (b * r₂) : ℤ) := by
        exact_mod_cast degree_add_le (a * r₁) (b * r₂)
      have hdegrel : degree a + degree (s₁ : DiffOp K) = degree b + degree (s₂ : DiffOp K) := by
        have h := congrArg degree hab
        rwa [degree_mul ha hs₁, degree_mul hb hs₂] at h
      have hfirst : (degree (a * r₁) : ℤ) - (degree (a * (s₁ : DiffOp K)) : ℤ) =
          (degree r₁ : ℤ) - (degree (s₁ : DiffOp K) : ℤ) := by
        rw [degree_mul ha hr₁, degree_mul ha hs₁]
        push_cast
        ring
      have hsecond : (degree (b * r₂) : ℤ) - (degree (a * (s₁ : DiffOp K)) : ℤ) =
          (degree r₂ : ℤ) - (degree (s₂ : DiffOp K) : ℤ) := by
        rw [degree_mul hb hr₂, degree_mul ha hs₁]
        have hdegrel' : ((degree a : ℕ) : ℤ) + (degree (s₁ : DiffOp K) : ℤ) =
            (degree b : ℤ) + (degree (s₂ : DiffOp K) : ℤ) := by
          exact_mod_cast hdegrel
        push_cast
        linarith
      calc
        (degree (a * r₁ + b * r₂) : ℤ) - (degree (a * (s₁ : DiffOp K)) : ℤ)
            ≤ max (degree (a * r₁) : ℤ) (degree (b * r₂) : ℤ) -
                (degree (a * (s₁ : DiffOp K)) : ℤ) := sub_le_sub_right hdegadd _
        _ = max ((degree (a * r₁) : ℤ) - (degree (a * (s₁ : DiffOp K)) : ℤ))
              ((degree (b * r₂) : ℤ) - (degree (a * (s₁ : DiffOp K)) : ℤ)) := by
                omega
        _ = max ((degree r₁ : ℤ) - (degree (s₁ : DiffOp K) : ℤ))
              ((degree r₂ : ℤ) - (degree (s₂ : DiffOp K) : ℤ)) := by rw [hfirst, hsecond]

/-- Negative pseudodifferential order, with zero assigned infinite additive valuation. -/
def pseudoDiffOpAddValuationValue (x : PseudoDiffOp K) : WithTop ℤ := by
  classical
  letI : DecidableEq (PseudoDiffOp K) := Classical.decEq _
  exact if x = 0 then (⊤ : WithTop ℤ) else (↑(-ordQ x) : WithTop ℤ)

@[simp] theorem pseudoDiffOpAddValuationValue_zero :
    pseudoDiffOpAddValuationValue (0 : PseudoDiffOp K) = ⊤ := by
  classical
  simp [pseudoDiffOpAddValuationValue]

@[simp] theorem pseudoDiffOpAddValuationValue_one :
    pseudoDiffOpAddValuationValue (1 : PseudoDiffOp K) = 0 := by
  classical
  simp [pseudoDiffOpAddValuationValue, one_ne_zero]

theorem pseudoDiffOpAddValuationValue_mul (x y : PseudoDiffOp K) :
    pseudoDiffOpAddValuationValue (x * y) =
      pseudoDiffOpAddValuationValue x + pseudoDiffOpAddValuationValue y := by
  classical
  letI : DecidableEq (PseudoDiffOp K) := Classical.decEq _
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  simp only [pseudoDiffOpAddValuationValue, if_neg hx, if_neg hy, if_neg hxy]
  rw [ordQ_mul x y hx hy]
  norm_cast
  ring

theorem pseudoDiffOpAddValuationValue_add (x y : PseudoDiffOp K) :
    min (pseudoDiffOpAddValuationValue x) (pseudoDiffOpAddValuationValue y) ≤
      pseudoDiffOpAddValuationValue (x + y) := by
  classical
  letI : DecidableEq (PseudoDiffOp K) := Classical.decEq _
  by_cases hxy : x + y = 0
  · simp [pseudoDiffOpAddValuationValue, hxy]
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  have hord := ordQ_add_le_max_of_ne_zero x y hx hy hxy
  have hneg : min (-ordQ x) (-ordQ y) ≤ -ordQ (x + y) := by omega
  simp only [pseudoDiffOpAddValuationValue, if_neg hx, if_neg hy, if_neg hxy]
  exact_mod_cast hneg

/-- The discrete additive valuation `v = -ord_∂` on the rational pseudodifferential skew field. -/
def pseudoDiffOpAddValuation : AddValuation (PseudoDiffOp K) (WithTop ℤ) :=
  AddValuation.of pseudoDiffOpAddValuationValue
    pseudoDiffOpAddValuationValue_zero pseudoDiffOpAddValuationValue_one
    pseudoDiffOpAddValuationValue_add pseudoDiffOpAddValuationValue_mul

@[simp] theorem pseudoDiffOpAddValuation_apply (x : PseudoDiffOp K) :
    pseudoDiffOpAddValuation x = pseudoDiffOpAddValuationValue x := rfl

/-- Multiplicative value group corresponding to the additive group `WithTop ℤ`. -/
abbrev PseudoDiffOpValueGroup := Multiplicative (WithTop ℤ)ᵒᵈ

/-- Multiplicative form of the pseudodifferential valuation. -/
def pseudoDiffOpValuation : Valuation (PseudoDiffOp K) PseudoDiffOpValueGroup :=
  (pseudoDiffOpAddValuation (K := K)).toValuation

/-- Canonical valued topology on the rational pseudodifferential skew field. -/
instance pseudoDiffOpValued : Valued (PseudoDiffOp K) PseudoDiffOpValueGroup :=
  Valued.mk' (pseudoDiffOpValuation (K := K))

/-- Uniform completion for `v = -ord_∂`, carried by mathlib's canonical `WithVal` wrapper.
Mathlib supplies its complete topological ring structure; extending inversion to make the completed
object a division ring is the next building foundation step. -/
abbrev CompletedPseudoDiffOp (K : Type u) [Field K] [Differential K] :=
  UniformSpace.Completion (WithVal (pseudoDiffOpValuation (K := K)))

/-- The monomial operator `∂ⁿ` has exact order `n`. -/
theorem degree_mono_one (n : ℕ) : degree (mono n (1 : K)) = n := by
  apply le_antisymm (degree_mono_le n 1)
  apply le_degree
  simp

theorem mono_one_ne_zero (n : ℕ) : mono n (1 : K) ≠ 0 := by
  intro h
  have := congrArg (fun p : DiffOp K => coeff p n) h
  simp only [coeff_mono_self, coeff_zero] at this
  exact one_ne_zero this

/-- The embedded operator `∂ⁿ` has additive valuation `-n`. -/
theorem pseudoDiffOpAddValuation_numerator_mono_one (n : ℕ) :
    pseudoDiffOpAddValuation
        (numeratorRingHom (mono n (1 : K)) : PseudoDiffOp K) = (↑(-(n : ℤ)) : WithTop ℤ) := by
  classical
  letI : DecidableEq (PseudoDiffOp K) := Classical.decEq _
  have hp : mono n (1 : K) ≠ 0 := mono_one_ne_zero n
  have hq : (numeratorRingHom (mono n (1 : K)) : PseudoDiffOp K) ≠ 0 :=
    fun h => hp (numeratorRingHom_injective (h.trans (map_zero _).symm))
  rw [pseudoDiffOpAddValuation_apply]
  unfold pseudoDiffOpAddValuationValue
  rw [if_neg hq, ordQ_numeratorRingHom, if_neg hp, degree_mono_one]

/-- Every finite integer valuation occurs on a nonzero rational pseudodifferential operator. -/
theorem exists_pseudoDiffOpAddValuation_eq_int (z : ℤ) :
    ∃ x : PseudoDiffOp K, x ≠ 0 ∧ pseudoDiffOpAddValuation x = (z : WithTop ℤ) := by
  cases z with
  | ofNat n =>
      let x : PseudoDiffOp K :=
        (numeratorRingHom (mono n (1 : K)) : PseudoDiffOp K)⁻¹
      have hp : mono n (1 : K) ≠ 0 := mono_one_ne_zero n
      have hq : (numeratorRingHom (mono n (1 : K)) : PseudoDiffOp K) ≠ 0 :=
        fun h => hp (numeratorRingHom_injective (h.trans (map_zero _).symm))
      refine ⟨x, inv_ne_zero hq, ?_⟩
      rw [show pseudoDiffOpAddValuation x =
          -pseudoDiffOpAddValuation
            (numeratorRingHom (mono n (1 : K)) : PseudoDiffOp K) from
        AddValuation.map_inv _]
      rw [pseudoDiffOpAddValuation_numerator_mono_one]
      simp
  | negSucc n =>
      let x : PseudoDiffOp K :=
        numeratorRingHom (mono (n + 1) (1 : K))
      have hp : mono (n + 1) (1 : K) ≠ 0 := mono_one_ne_zero (n + 1)
      have hq : x ≠ 0 :=
        fun h => hp (numeratorRingHom_injective (h.trans (map_zero _).symm))
      refine ⟨x, hq, ?_⟩
      rw [pseudoDiffOpAddValuation_numerator_mono_one]
      rfl

end

end DiffOp

end GaloisForLFunctions.HTGeometry
