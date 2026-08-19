import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphicIsomonodromy

/-!
# Every integer shift of the Bessel order function lies in a two-dimensional span

The order recurrence runs in both directions, so `K_{ν+n}(s)` is for every integer `n` a rational
combination of `K_ν(s)` and `K_{ν+1}(s)`.  Consequently the order derivative is not a rational
combination of *any* finite family of integer shifts.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- Membership in the `ℂ(ν)`-span of the two basic solutions. -/
def InBesselSpan (s : ℝ) (hs : 0 < s) (x : meroField (Set.univ : Set ℂ)) : Prop :=
  ∃ P Q : RatFunc ℂ,
    x = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) P * modifiedBesselKOrderMero s hs
      + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) Q
        * addTranslationMeroEquiv (1 : ℂ) (modifiedBesselKOrderMero s hs)

theorem inBesselSpan_add {s : ℝ} {hs : 0 < s} {x y : meroField (Set.univ : Set ℂ)}
    (hx : InBesselSpan s hs x) (hy : InBesselSpan s hs y) : InBesselSpan s hs (x + y) := by
  obtain ⟨P₁, Q₁, h₁⟩ := hx
  obtain ⟨P₂, Q₂, h₂⟩ := hy
  exact ⟨P₁ + P₂, Q₁ + Q₂, by rw [h₁, h₂, map_add, map_add]; ring⟩

theorem inBesselSpan_smul {s : ℝ} {hs : 0 < s} (c : RatFunc ℂ)
    {x : meroField (Set.univ : Set ℂ)} (hx : InBesselSpan s hs x) :
    InBesselSpan s hs (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) c * x) := by
  obtain ⟨P, Q, h⟩ := hx
  exact ⟨c * P, c * Q, by rw [h, map_mul, map_mul]; ring⟩

theorem inBesselSpan_zero {s : ℝ} {hs : 0 < s} : InBesselSpan s hs 0 :=
  ⟨0, 0, by simp⟩

theorem inBesselSpan_finsetSum {s : ℝ} {hs : 0 < s} {ι : Type*} (T : Finset ι)
    (f : ι → meroField (Set.univ : Set ℂ)) (hf : ∀ i ∈ T, InBesselSpan s hs (f i)) :
    InBesselSpan s hs (∑ i ∈ T, f i) := by
  classical
  induction T using Finset.induction with
  | empty => simpa using inBesselSpan_zero (s := s) (hs := hs)
  | insert a T ha ih =>
      rw [Finset.sum_insert ha]
      exact inBesselSpan_add (hf a (Finset.mem_insert_self a T))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- **Every integer shift of the order function lies in the span of the first two.** -/
theorem inBesselSpan_shift {s : ℝ} (hs : 0 < s) (n : ℤ) :
    InBesselSpan s hs (modifiedBesselKOrderShiftMero s hs (n : ℂ))
      ∧ InBesselSpan s hs (modifiedBesselKOrderShiftMero s hs ((n : ℂ) + 1)) := by
  have hcoeff : ∀ q : ℂ, besselOrderLinearCoeffShiftMero s q
      = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (besselOrderLinearCoeffRat s q) :=
    besselOrderLinearCoeffShiftMero_eq_algebraMap s
  refine Int.induction_on n ?_ ?_ ?_
  · constructor
    · refine ⟨1, 0, ?_⟩
      simp [modifiedBesselKOrderShiftMero_zero]
    · refine ⟨0, 1, ?_⟩
      rw [addTranslationMeroEquiv_modifiedBesselKOrderMero s hs 1]
      simp
  · intro i hi
    obtain ⟨h1, h2⟩ := hi
    push_cast at h1 h2
    refine ⟨by push_cast; exact h2, ?_⟩
    push_cast
    have hrec := modifiedBesselKOrderShiftMero_recurrence s hs ((i : ℂ) + 1)
    have he2 : ((i : ℂ) + 1) - 1 = (i : ℂ) := by ring
    rw [he2, hcoeff] at hrec
    rw [hrec]
    exact inBesselSpan_add h1 (inBesselSpan_smul _ h2)
  · intro i hi
    obtain ⟨h1, h2⟩ := hi
    push_cast at h1 h2
    refine ⟨?_, ?_⟩
    · push_cast
      have hrec := modifiedBesselKOrderShiftMero_recurrence s hs (-(i : ℂ))
      rw [hcoeff] at hrec
      have hdown : modifiedBesselKOrderShiftMero s hs (-(i : ℂ) - 1)
          = modifiedBesselKOrderShiftMero s hs (-(i : ℂ) + 1)
            + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
                (-besselOrderLinearCoeffRat s (-(i : ℂ)))
              * modifiedBesselKOrderShiftMero s hs (-(i : ℂ)) := by
        rw [map_neg]
        linear_combination -hrec
      rw [hdown]
      exact inBesselSpan_add h2 (inBesselSpan_smul _ h1)
    · push_cast
      rw [show (-(i : ℂ) - 1 + 1) = -(i : ℂ) from by ring]
      exact h1

/-- **The order derivative is not a rational combination of any finite family of shifts.** -/
theorem modifiedBesselKOrderMero_deriv_notMem_shift_span {s : ℝ} (hs : 0 < s)
    (T : Finset ℤ) (c : ℤ → RatFunc ℂ) :
    Differential.deriv (modifiedBesselKOrderMero s hs)
      ≠ ∑ n ∈ T, algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (c n)
          * modifiedBesselKOrderShiftMero s hs (n : ℂ) := by
  intro h
  have hspan : InBesselSpan s hs
      (∑ n ∈ T, algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (c n)
        * modifiedBesselKOrderShiftMero s hs (n : ℂ)) :=
    inBesselSpan_finsetSum T _ fun n _ =>
      inBesselSpan_smul _ (inBesselSpan_shift hs n).1
  rw [← h] at hspan
  obtain ⟨P, Q, hPQ⟩ := hspan
  exact modifiedBesselKOrderMero_no_rational_delta_structure hs ⟨P, Q, hPQ⟩

end

end GaloisForLFunctions.HTGeometry
