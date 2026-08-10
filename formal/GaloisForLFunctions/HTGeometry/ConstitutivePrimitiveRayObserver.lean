import GaloisForLFunctions.HTGeometry.ConstitutivePrimitiveExecutionGenesis
import Mathlib

/-!
# Primitive-ray positive recurrence and open history

Every primitive law generates a positive execution ray.  Projective positive observation is
constant, cyclic grade observation is periodic, and the exact execution grade is strictly
unbounded.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

/-- The resource weight on the `n`-fold ray through `a`. -/
def primitiveRayWeight {α : Type u} (n : ℕ) (a : α → ℕ) : α → ℕ :=
  fun i => n * a i

/-- Projective profile at the primitive base law. -/
def primitiveBaseProfile {α : Type u} (d : ℕ) (a : α → ℕ) : α → ℚ :=
  fun i => (a i : ℚ) / d

/-- Projective profile computed from the `n`-fold execution ray. -/
def primitiveRayProfile {α : Type u} (d : ℕ) (a : α → ℕ) (n : ℕ) : α → ℚ :=
  fun i => ((n * a i : ℕ) : ℚ) / ((n * d : ℕ) : ℚ)

/-- Cyclic observation of exact execution grade. -/
def primitiveRayPhase (q d n : ℕ) : ZMod q :=
  ((n * d : ℕ) : ZMod q)

/-- Paired positive-projective and cyclic-grade observer. -/
def primitiveRayObserver {α : Type u} (q d : ℕ) (a : α → ℕ) (n : ℕ) :
    (α → ℚ) × ZMod q :=
  (primitiveRayProfile d a n, primitiveRayPhase q d n)

/-- Local admission is preserved under ray scaling. -/
theorem primitiveRayWeight_local {α : Type u} [DecidableEq α]
    (H : Finset (Finset α)) (d : ℕ) (a : α → ℕ)
    (hlocal : WeightedLocalRepair H d a) (n : ℕ) :
    WeightedLocalRepair H (n * d) (primitiveRayWeight n a) := by
  intro K hKH
  have h := Nat.mul_le_mul_left n (hlocal K hKH)
  simpa [primitiveRayWeight, Finset.mul_sum] using h

/-- Forget the degree bound on a bounded primitive execution. -/
theorem boundedPrimitiveGeneratedRepair_to_generated {α : Type u} [DecidableEq α]
    (H : Finset (Finset α)) (D : ℕ) {m : ℕ} {a : α → ℕ}
    (h : BoundedPrimitiveGeneratedRepair H D m a) :
    PrimitiveGeneratedRepair H m a := by
  induction h with
  | atom hp _hdegree => exact PrimitiveGeneratedRepair.atom hp
  | combine h₁ h₂ hdom ih₁ ih₂ =>
      exact PrimitiveGeneratedRepair.combine ih₁ ih₂ hdom

/-- Every positive successor point on a primitive ray is generated inside any grammar admitting
the primitive degree. -/
theorem primitiveRay_bounded_succ {α : Type u} [DecidableEq α]
    (H : Finset (Finset α)) (D d : ℕ) (a : α → ℕ)
    (hp : WeightedPrimitiveRepair H d a) (hdD : d ≤ D) (n : ℕ) :
    BoundedPrimitiveGeneratedRepair H D ((n + 1) * d)
      (primitiveRayWeight (n + 1) a) := by
  induction n with
  | zero =>
      have hatom := BoundedPrimitiveGeneratedRepair.atom hp hdD
      convert hatom using 1
      · simp
      · funext i
        simp [primitiveRayWeight]
  | succ n ih =>
      have hcombine := BoundedPrimitiveGeneratedRepair.combine ih
        (BoundedPrimitiveGeneratedRepair.atom hp hdD)
        (a := primitiveRayWeight (n + 2) a) (by
          intro i
          simp [primitiveRayWeight, Nat.add_mul, two_mul, Nat.add_assoc])
      simpa [Nat.add_mul, two_mul, Nat.add_assoc] using hcombine

/-- Positive-index form of bounded primitive-ray generation. -/
theorem primitiveRay_bounded {α : Type u} [DecidableEq α]
    (H : Finset (Finset α)) (D d : ℕ) (a : α → ℕ)
    (hp : WeightedPrimitiveRepair H d a) (hdD : d ≤ D)
    (n : ℕ) (hn : 0 < n) :
    BoundedPrimitiveGeneratedRepair H D (n * d) (primitiveRayWeight n a) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa [Nat.succ_eq_add_one] using primitiveRay_bounded_succ H D d a hp hdD k

/-- Every positive point on a primitive ray lies in the full canonical grammar. -/
theorem primitiveRay_generated {α : Type u} [DecidableEq α]
    (H : Finset (Finset α)) (d : ℕ) (a : α → ℕ)
    (hp : WeightedPrimitiveRepair H d a) (n : ℕ) (hn : 0 < n) :
    PrimitiveGeneratedRepair H (n * d) (primitiveRayWeight n a) :=
  boundedPrimitiveGeneratedRepair_to_generated H d
    (primitiveRay_bounded H d d a hp le_rfl n hn)

/-- Positive projectivization erases all radial execution scale. -/
theorem primitiveRayProfile_eq_base {α : Type u}
    (d : ℕ) (a : α → ℕ) (n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    primitiveRayProfile d a n = primitiveBaseProfile d a := by
  funext i
  change ((n * a i : ℕ) : ℚ) / ((n * d : ℕ) : ℚ) = (a i : ℚ) / d
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  push_cast
  field_simp [hnq, hdq]

/-- Every base projective coordinate is nonnegative. -/
theorem primitiveBaseProfile_nonnegative {α : Type u}
    (d : ℕ) (a : α → ℕ) (hd : 0 < d) (i : α) :
    0 ≤ primitiveBaseProfile d a i := by
  change 0 ≤ (a i : ℚ) / (d : ℚ)
  positivity

/-- Cyclic grade observation returns after `q` execution steps. -/
theorem primitiveRayPhase_period (q d n : ℕ) :
    primitiveRayPhase q d (n + q) = primitiveRayPhase q d n := by
  simp only [primitiveRayPhase, Nat.add_mul, Nat.cast_add, Nat.cast_mul,
    ZMod.natCast_self, zero_mul, add_zero]

/-- The paired projective/cyclic observer is exactly periodic. -/
theorem primitiveRayObserver_period {α : Type u}
    (q d : ℕ) (a : α → ℕ) (n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    primitiveRayObserver q d a (n + q) = primitiveRayObserver q d a n := by
  apply Prod.ext
  · change primitiveRayProfile d a (n + q) = primitiveRayProfile d a n
    rw [primitiveRayProfile_eq_base d a (n + q) hd (by omega),
      primitiveRayProfile_eq_base d a n hd hn]
  · change primitiveRayPhase q d (n + q) = primitiveRayPhase q d n
    exact primitiveRayPhase_period q d n

/-- One positive cyclic period strictly advances exact execution grade. -/
theorem primitiveRay_exactGrade_strict_period
    (q d n : ℕ) (hq : 0 < q) (hd : 0 < d) :
    n * d < (n + q) * d := by
  exact Nat.mul_lt_mul_of_pos_right (by omega) hd

/-- Exact primitive-ray grade escapes every finite bound. -/
theorem primitiveRay_exactGrade_unbounded (d N : ℕ) (hd : 0 < d) :
    ∃ n : ℕ, 0 < n ∧ N < n * d := by
  refine ⟨N + 1, by omega, ?_⟩
  have hscale := Nat.mul_le_mul_left (N + 1) (show 1 ≤ d by omega)
  omega

/-- Exact closed-observer/open-lift law on a primitive execution ray. -/
theorem primitiveRayObserver_openLift {α : Type u}
    (q d : ℕ) (a : α → ℕ) (n : ℕ)
    (hq : 0 < q) (hd : 0 < d) (hn : 0 < n) :
    primitiveRayObserver q d a (n + q) = primitiveRayObserver q d a n ∧
      n * d < (n + q) * d :=
  ⟨primitiveRayObserver_period q d a n hd hn,
    primitiveRay_exactGrade_strict_period q d n hq hd⟩

/-- Closed capstone: legal primitive-ray execution, periodic quotient observation, and open exact
history. -/
theorem primitiveRayObserverMechanism_closed :
    (∀ (α : Type) (_ : DecidableEq α) (H : Finset (Finset α))
      (D d : ℕ) (a : α → ℕ), WeightedPrimitiveRepair H d a → d ≤ D →
        ∀ n, 0 < n →
          BoundedPrimitiveGeneratedRepair H D (n * d) (primitiveRayWeight n a)) ∧
    (∀ (α : Type) (q d : ℕ) (a : α → ℕ) (n : ℕ),
      0 < q → 0 < d → 0 < n →
        primitiveRayObserver q d a (n + q) = primitiveRayObserver q d a n ∧
          n * d < (n + q) * d) ∧
    (∀ d N : ℕ, 0 < d → ∃ n : ℕ, 0 < n ∧ N < n * d) := by
  refine ⟨?_, ?_, primitiveRay_exactGrade_unbounded⟩
  · intro α inst H D d a hp hdD n hn
    letI : DecidableEq α := inst
    exact primitiveRay_bounded H D d a hp hdD n hn
  · exact fun α q d a n hq hd hn =>
      primitiveRayObserver_openLift q d a n hq hd hn

end GaloisForLFunctions.HTGeometry
