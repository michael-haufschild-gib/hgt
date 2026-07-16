import GaloisForLFunctions.HTGeometry.ConicPeriodicMatrixFactorization
import GaloisForLFunctions.HTGeometry.SymmetricAlgebraDerivation
import GaloisForLFunctions.HTGeometry.SymmetricAlgebraAlgebraicIndependence
import Mathlib.LinearAlgebra.Prod
import Mathlib.Logic.Equiv.Nat

/-!
# Two-periodic matrix-factorization horizons

Two linear state actions `A,B` with `BA=AB=F·1` generate a two-periodic grade-raising operator.
The even and odd orbit layers are scaled by powers of `F`.  If the two descendant chains occupy
disjoint grades, vanishing of `F` gives a finite orbit and nonvanishing gives a linearly independent
orbit.  The symmetric observable algebra converts this state-orbit dichotomy into an exact
ordinary differential-algebraicity horizon.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable {K : Type u} {M : Type v}
  [Field K] [AddCommGroup M] [Module K M]

/-- The two parity sectors of a countably graded state space. -/
abbrev TwoPeriodicState (M : Type v) [AddCommGroup M] :=
  (ℕ → M) × (ℕ → M)

/-- A state occupying exactly one grade. -/
def periodicLevel (n : ℕ) (m : M) : ℕ → M :=
  fun k ↦ if k = n then m else 0

/-- Apply one endomorphism independently on every grade. -/
def periodicPointwiseEnd (A : Module.End K M) : Module.End K (ℕ → M) where
  toFun f n := A (f n)
  map_add' f g := by
    funext n
    simp
  map_smul' c f := by
    funext n
    simp

/-- The unilateral grade shift. -/
def periodicUnilateralShift : Module.End K (ℕ → M) where
  toFun f
    | 0 => 0
    | n + 1 => f n
  map_add' f g := by
    funext n
    cases n <;> simp
  map_smul' c f := by
    funext n
    cases n <;> simp

/-- Alternate `A` from the even sector to the odd sector and `B` back to the next even grade. -/
def twoPeriodicFactorizationOperator
    (A B : Module.End K M) : Module.End K (TwoPeriodicState M) where
  toFun s :=
    (periodicUnilateralShift (K := K) (periodicPointwiseEnd (K := K) B s.2),
      periodicPointwiseEnd (K := K) A s.1)
  map_add' s t := by
    apply Prod.ext
    · funext n
      cases n <;> simp [periodicUnilateralShift, periodicPointwiseEnd]
    · funext n
      simp [periodicPointwiseEnd]
  map_smul' c s := by
    apply Prod.ext
    · funext n
      cases n <;> simp [periodicUnilateralShift, periodicPointwiseEnd]
    · funext n
      simp [periodicPointwiseEnd]

@[simp]
theorem periodicPointwiseEnd_level
    (A : Module.End K M) (n : ℕ) (m : M) :
    periodicPointwiseEnd A (periodicLevel n m) =
      periodicLevel n (A m) := by
  funext k
  by_cases h : k = n <;> simp [periodicPointwiseEnd, periodicLevel, h]

@[simp]
theorem periodicUnilateralShift_level (n : ℕ) (m : M) :
    periodicUnilateralShift (K := K) (periodicLevel n m) =
      periodicLevel (n + 1) m := by
  funext k
  cases k with
  | zero => simp [periodicUnilateralShift, periodicLevel]
  | succ k =>
      by_cases h : k = n <;>
        simp [periodicUnilateralShift, periodicLevel, h]

@[simp]
theorem twoPeriodicFactorizationOperator_evenLevel
    (A B : Module.End K M) (n : ℕ) (m : M) :
    twoPeriodicFactorizationOperator A B (periodicLevel n m, 0) =
      (0, periodicLevel n (A m)) := by
  change
    (periodicUnilateralShift (K := K)
        (periodicPointwiseEnd (K := K) B 0),
      periodicPointwiseEnd (K := K) A (periodicLevel n m)) = _
  rw [map_zero, map_zero, periodicPointwiseEnd_level]

@[simp]
theorem twoPeriodicFactorizationOperator_oddLevel
    (A B : Module.End K M) (n : ℕ) (m : M) :
    twoPeriodicFactorizationOperator A B (0, periodicLevel n m) =
      (periodicLevel (n + 1) (B m), 0) := by
  change
    (periodicUnilateralShift (K := K)
        (periodicPointwiseEnd (K := K) B (periodicLevel n m)),
      periodicPointwiseEnd (K := K) A 0) = _
  rw [periodicPointwiseEnd_level, periodicUnilateralShift_level, map_zero]

/-- Exact even and odd orbit formulas for a two-periodic factorization. -/
theorem twoPeriodicFactorizationOperator_orbit
    (A B : Module.End K M) (F : K) (m : M)
    (hBA : B.comp A = F • LinearMap.id) :
    (∀ r : ℕ, (((twoPeriodicFactorizationOperator A B :
        Module.End K (TwoPeriodicState M)) : TwoPeriodicState M → TwoPeriodicState M)^[2 * r])
        (periodicLevel 0 m, 0) =
      (periodicLevel r ((F ^ r) • m), 0)) ∧
    (∀ r : ℕ, (((twoPeriodicFactorizationOperator A B :
        Module.End K (TwoPeriodicState M)) : TwoPeriodicState M → TwoPeriodicState M)^[2 * r + 1])
        (periodicLevel 0 m, 0) =
      (0, periodicLevel r ((F ^ r) • A m))) := by
  let T := twoPeriodicFactorizationOperator A B
  have hpoint : B (A m) = F • m := by
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] using
      LinearMap.congr_fun hBA m
  have hboth : ∀ r : ℕ,
      ((T : TwoPeriodicState M → TwoPeriodicState M)^[2 * r])
          (periodicLevel 0 m, 0) = (periodicLevel r ((F ^ r) • m), 0) ∧
      ((T : TwoPeriodicState M → TwoPeriodicState M)^[2 * r + 1])
          (periodicLevel 0 m, 0) = (0, periodicLevel r ((F ^ r) • A m)) := by
    intro r
    induction r with
    | zero =>
        constructor
        · simp [T]
        · simp [T]
    | succ r ih =>
        constructor
        · rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega,
            Function.iterate_succ_apply', ih.2]
          rw [show T = twoPeriodicFactorizationOperator A B by rfl,
            twoPeriodicFactorizationOperator_oddLevel]
          simp [map_smul, hpoint, pow_succ, smul_smul, mul_comm]
        · rw [show 2 * (r + 1) + 1 = 2 * (r + 1) + 1 by rfl,
            Function.iterate_succ_apply']
          rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega,
            Function.iterate_succ_apply', ih.2]
          rw [show T = twoPeriodicFactorizationOperator A B by rfl,
            twoPeriodicFactorizationOperator_oddLevel,
            twoPeriodicFactorizationOperator_evenLevel]
          simp [map_smul, hpoint, pow_succ, smul_smul, mul_comm]
  exact ⟨fun r ↦ (hboth r).1, fun r ↦ (hboth r).2⟩

/-- Single-grade states with nonzero grade values are linearly independent. -/
theorem periodicLevel_linearIndependent
    (u : ℕ → M) (hu : ∀ n, u n ≠ 0) :
    LinearIndependent K (fun n ↦ periodicLevel n (u n)) := by
  rw [linearIndependent_iff]
  intro l hl
  apply Finsupp.ext
  intro n
  by_cases hnmem : n ∈ l.support
  · rw [Finsupp.linearCombination_apply] at hl
    have hn := congrFun hl n
    simp only [Finsupp.sum, Finset.sum_apply, Pi.zero_apply] at hn
    rw [Finset.sum_eq_single n] at hn
    · have hcoef : l n • u n = 0 := by
        simpa [periodicLevel] using hn
      simpa using (smul_eq_zero.mp hcoef).resolve_right (hu n)
    · intro b _ hbn
      simp [periodicLevel, hbn.symm]
    · intro hnnot
      exact (hnnot hnmem).elim
  · exact Finsupp.notMem_support_iff.mp hnmem

/-- The two parity-separated single-grade families are jointly linearly independent. -/
theorem twoPeriodicLevel_linearIndependent
    (u v : ℕ → M) (hu : ∀ n, u n ≠ 0) (hv : ∀ n, v n ≠ 0) :
    LinearIndependent K (Sum.elim
      (fun n ↦ (periodicLevel n (u n), 0))
      (fun n ↦ (0, periodicLevel n (v n)))) := by
  have hu0 := (periodicLevel_linearIndependent u hu).map'
    (LinearMap.inl K (ℕ → M) (ℕ → M)) (by
      rw [LinearMap.ker_eq_bot]
      exact LinearMap.inl_injective)
  have hv0 := (periodicLevel_linearIndependent v hv).map'
    (LinearMap.inr K (ℕ → M) (ℕ → M)) (by
      rw [LinearMap.ker_eq_bot]
      exact LinearMap.inr_injective)
  apply hu0.sum_type hv0
  apply (LinearMap.disjoint_inl_inr (R := K) (M := ℕ → M) (M₂ := ℕ → M)).mono
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact LinearMap.mem_range_self _ _
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact LinearMap.mem_range_self _ _

/-- Off the factorization hypersurface, the complete two-periodic state orbit is linearly
independent. -/
theorem twoPeriodicFactorizationOperator_orbit_linearIndependent
    (A B : Module.End K M) (F : K) (m : M)
    (hBA : B.comp A = F • LinearMap.id)
    (hm : m ≠ 0) (hF : F ≠ 0) :
    LinearIndependent K (fun n : ℕ ↦
      (((twoPeriodicFactorizationOperator A B : TwoPeriodicState M → TwoPeriodicState M)^[n])
        (periodicLevel 0 m, 0))) := by
  have horbit := twoPeriodicFactorizationOperator_orbit A B F m hBA
  have hAm : A m ≠ 0 := by
    intro hzero
    have hpoint := LinearMap.congr_fun hBA m
    simp only [LinearMap.comp_apply, hzero, map_zero, LinearMap.smul_apply,
      LinearMap.id_apply] at hpoint
    exact hm ((smul_eq_zero.mp hpoint.symm).resolve_left hF)
  let u : ℕ → M := fun r ↦ (F ^ r) • m
  let v : ℕ → M := fun r ↦ (F ^ r) • A m
  have hu : ∀ r, u r ≠ 0 := fun r ↦ smul_ne_zero (pow_ne_zero r hF) hm
  have hv : ∀ r, v r ≠ 0 := fun r ↦ smul_ne_zero (pow_ne_zero r hF) hAm
  have hsum := twoPeriodicLevel_linearIndependent (K := K) u v hu hv
  have hreindex := hsum.comp Equiv.natSumNatEquivNat.symm
    Equiv.natSumNatEquivNat.symm.injective
  have hfamily : (fun n : ℕ ↦
      (((twoPeriodicFactorizationOperator A B : TwoPeriodicState M → TwoPeriodicState M)^[n])
        (periodicLevel 0 m, 0))) =
      (Sum.elim (fun r ↦ (periodicLevel r (u r), 0))
        (fun r ↦ (0, periodicLevel r (v r)))) ∘
          Equiv.natSumNatEquivNat.symm := by
    funext n
    obtain ⟨s, rfl⟩ := Equiv.natSumNatEquivNat.surjective n
    cases s with
    | inl r => simpa [u] using horbit.1 r
    | inr r => simpa [v] using horbit.2 r
  rw [hfamily]
  exact hreindex

end

end GaloisForLFunctions.HTGeometry
