import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring

/-!
# Certified real derivative curves through order three

Finite sums and products carry explicit value, first, second, and third derivative functions.
Their certificates use ordinary derivatives on a specified parameter domain. On an open domain,
the displayed second and third components equal the actual iterated derivatives.
-/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section

/-- A real curve with three successive derivative functions certified on a domain. -/
structure CubicDerivativeCurve (s : Set ℝ) where
  value : ℝ → ℝ
  first : ℝ → ℝ
  second : ℝ → ℝ
  third : ℝ → ℝ
  has_first : ∀ t ∈ s, HasDerivAt value (first t) t
  has_second : ∀ t ∈ s, HasDerivAt first (second t) t
  has_third : ∀ t ∈ s, HasDerivAt second (third t) t

namespace CubicDerivativeCurve
variable {s : Set ℝ}

/-- Constant curve with all derivative components zero. -/
def constant (c : ℝ) : CubicDerivativeCurve s where
  value := fun _ => c
  first := fun _ => 0
  second := fun _ => 0
  third := fun _ => 0
  has_first := fun t _ => hasDerivAt_const t c
  has_second := fun t _ => hasDerivAt_const t 0
  has_third := fun t _ => hasDerivAt_const t 0

/-- Affine curve with its actual constant first derivative. -/
def affine (a b : ℝ) : CubicDerivativeCurve s where
  value := fun t => a + t * b
  first := fun _ => b
  second := fun _ => 0
  third := fun _ => 0
  has_first := fun t _ => by simpa using ((hasDerivAt_id t).mul_const b).const_add a
  has_second := fun t _ => hasDerivAt_const t b
  has_third := fun t _ => hasDerivAt_const t 0

/-- Sum of certified derivative curves. -/
def add (P Q : CubicDerivativeCurve s) : CubicDerivativeCurve s where
  value := fun t => P.value t + Q.value t
  first := fun t => P.first t + Q.first t
  second := fun t => P.second t + Q.second t
  third := fun t => P.third t + Q.third t
  has_first := fun t ht => (P.has_first t ht).add (Q.has_first t ht)
  has_second := fun t ht => (P.has_second t ht).add (Q.has_second t ht)
  has_third := fun t ht => (P.has_third t ht).add (Q.has_third t ht)

/-- Difference of certified derivative curves. -/
def sub (P Q : CubicDerivativeCurve s) : CubicDerivativeCurve s where
  value := fun t => P.value t - Q.value t
  first := fun t => P.first t - Q.first t
  second := fun t => P.second t - Q.second t
  third := fun t => P.third t - Q.third t
  has_first := fun t ht => (P.has_first t ht).sub (Q.has_first t ht)
  has_second := fun t ht => (P.has_second t ht).sub (Q.has_second t ht)
  has_third := fun t ht => (P.has_third t ht).sub (Q.has_third t ht)

/-- Product with every binomial contribution retained through order three. -/
def mul (P Q : CubicDerivativeCurve s) : CubicDerivativeCurve s where
  value := fun t => P.value t * Q.value t
  first := fun t => P.first t * Q.value t + P.value t * Q.first t
  second := fun t => P.second t * Q.value t + 2 * (P.first t * Q.first t) + P.value t * Q.second t
  third := fun t => P.third t * Q.value t + 3 * (P.second t * Q.first t) +
    3 * (P.first t * Q.second t) + P.value t * Q.third t
  has_first := fun t ht => (P.has_first t ht).mul (Q.has_first t ht)
  has_second := by
    intro t ht
    have h := ((P.has_second t ht).mul (Q.has_first t ht)).add
      ((P.has_first t ht).mul (Q.has_second t ht))
    exact h.congr_deriv (by ring)
  has_third := by
    intro t ht
    have h := (((P.has_third t ht).mul (Q.has_first t ht)).add
      (((P.has_second t ht).mul (Q.has_second t ht)).const_mul 2)).add
      ((P.has_first t ht).mul (Q.has_third t ht))
    exact h.congr_deriv (by ring)

instance : Add (CubicDerivativeCurve s) := ⟨add⟩
instance : Sub (CubicDerivativeCurve s) := ⟨sub⟩
instance : Mul (CubicDerivativeCurve s) := ⟨mul⟩

/-- A finite contraction of certified derivative curves. -/
def sum {ι : Type*} [Fintype ι] (P : ι → CubicDerivativeCurve s) : CubicDerivativeCurve s where
  value := fun t => ∑ i, (P i).value t
  first := fun t => ∑ i, (P i).first t
  second := fun t => ∑ i, (P i).second t
  third := fun t => ∑ i, (P i).third t
  has_first := fun t ht => by
    have h := HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) => (P i).has_first t ht)
    have heq : (∑ i, (P i).value) = fun u => ∑ i, (P i).value u := by
      funext u
      rw [Finset.sum_apply]
    rw [heq] at h
    exact h
  has_second := fun t ht => by
    have h := HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) => (P i).has_second t ht)
    have heq : (∑ i, (P i).first) = fun u => ∑ i, (P i).first u := by
      funext u
      rw [Finset.sum_apply]
    rw [heq] at h
    exact h
  has_third := fun t ht => by
    have h := HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) => (P i).has_third t ht)
    have heq : (∑ i, (P i).second) = fun u => ∑ i, (P i).second u := by
      funext u
      rw [Finset.sum_apply]
    rw [heq] at h
    exact h

@[simp] theorem value_constant (c t : ℝ) : (constant (s := s) c).value t = c := rfl
@[simp] theorem value_affine (a b t : ℝ) : (affine (s := s) a b).value t = a + t * b := rfl
@[simp] theorem value_add (P Q : CubicDerivativeCurve s) (t : ℝ) :
    (P + Q).value t = P.value t + Q.value t := rfl
@[simp] theorem value_sub (P Q : CubicDerivativeCurve s) (t : ℝ) :
    (P - Q).value t = P.value t - Q.value t := rfl
@[simp] theorem value_mul (P Q : CubicDerivativeCurve s) (t : ℝ) :
    (P * Q).value t = P.value t * Q.value t := rfl
@[simp] theorem value_sum {ι : Type*} [Fintype ι] (P : ι → CubicDerivativeCurve s) (t : ℝ) :
    (sum P).value t = ∑ i, (P i).value t := rfl

/-- The second certificate represents the actual iterated derivative on an open domain. -/
theorem iteratedDeriv_two_value (P : CubicDerivativeCurve s) (hs : IsOpen s)
    {t : ℝ} (ht : t ∈ s) : iteratedDeriv 2 P.value t = P.second t := by
  have heq : deriv P.value =ᶠ[𝓝 t] P.first := by
    filter_upwards [hs.mem_nhds ht] with u hu
    exact (P.has_first u hu).deriv
  rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    heq.deriv_eq, (P.has_second t ht).deriv]

/-- The third certificate represents the actual iterated derivative on an open domain. -/
theorem iteratedDeriv_three_value (P : CubicDerivativeCurve s) (hs : IsOpen s)
    {t : ℝ} (ht : t ∈ s) : iteratedDeriv 3 P.value t = P.third t := by
  have heq : iteratedDeriv 2 P.value =ᶠ[𝓝 t] P.second := by
    filter_upwards [hs.mem_nhds ht] with u hu
    exact P.iteratedDeriv_two_value hs hu
  rw [show 3 = 2 + 1 from rfl, iteratedDeriv_succ, heq.deriv_eq, (P.has_third t ht).deriv]

end CubicDerivativeCurve
end
end GaloisForLFunctions.HTGeometry
