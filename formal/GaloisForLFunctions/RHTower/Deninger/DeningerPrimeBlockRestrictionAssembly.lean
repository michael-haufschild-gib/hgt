import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeBlockGreenSummability
import GaloisForLFunctions.RHTower.Deninger.DeningerGreenFormPullbackTransport

/-!
# Assembly of full prime-packet restrictions

This module gives the source-facing interface for Route L's all-prime Green form.  A family of
bounded local restrictions into complete real Hilbert packet fibres assembles to one bounded map
into their Hilbert direct sum as soon as it satisfies a global Bessel estimate.  The kernel of the
assembled map is exactly the simultaneous local kernel.

Pulling back the full-block prime Green family then gives an unordered operator-norm-summable
source family.  Its global energy is nonnegative, has an exact weighted Parseval formula, and has
radical equal to the simultaneous local kernel.  Consequently the remaining arithmetic theorem
has two irreducible clauses: the Bessel estimate and classification of simultaneous local kernels
as closed middle boundaries.  No scalar packet average or `ℓ¹` majorant is used.
-/

namespace RHTower

open Filter Topology
open scoped ENNReal BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Kp : Nat.Primes → Type*}
  [∀ p, NormedAddCommGroup (Kp p)] [∀ p, InnerProductSpace ℝ (Kp p)]

/-- Pointwise square summability puts all prime-packet restrictions in the Hilbert direct sum. -/
theorem deningerPrimeRestriction_memℓp
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    (x : E) :
    Memℓp (fun p => restriction p x) 2 := by
  exact memℓp_gen (hsummable x)

/-- Linear assembly of all full prime-packet restrictions. -/
def deningerPrimeRestrictionLinearMap
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ)) :
    E →ₗ[ℝ] DeningerHilbertSum Kp where
  toFun x := ⟨fun p => restriction p x,
    deningerPrimeRestriction_memℓp restriction hsummable x⟩
  map_add' := by
    intro x y
    ext p
    simp
  map_smul' := by
    intro c x
    ext p
    simp

@[simp] theorem deningerPrimeRestrictionLinearMap_apply
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    (x : E) (p : Nat.Primes) :
    deningerPrimeRestrictionLinearMap restriction hsummable x p =
      restriction p x := rfl

/-- A Bessel bound on the local restrictions bounds their assembled Hilbert-direct-sum map. -/
theorem deningerPrimeRestrictionLinearMap_norm_le
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) :
    ‖deningerPrimeRestrictionLinearMap restriction hsummable x‖ ≤ C * ‖x‖ := by
  have hleft :
      0 ≤ ‖deningerPrimeRestrictionLinearMap restriction hsummable x‖ := norm_nonneg _
  have hright : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  have hdiag :
      ‖deningerPrimeRestrictionLinearMap restriction hsummable x‖ ^ (2 : ℝ) =
        ∑' p, ‖restriction p x‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := Kp) (by norm_num)
      (deningerPrimeRestrictionLinearMap restriction hsummable x)
  have hpow :
      ‖deningerPrimeRestrictionLinearMap restriction hsummable x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ) := by
    rw [hdiag]
    exact hBessel x
  have hleft2 :
      ‖deningerPrimeRestrictionLinearMap restriction hsummable x‖ ^ (2 : ℝ) =
        ‖deningerPrimeRestrictionLinearMap restriction hsummable x‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hright2 :
      (C * ‖x‖) ^ (2 : ℝ) = (C * ‖x‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hleft2, hright2] at hpow
  have hsqrt := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hleft, Real.sqrt_sq hright] at hsqrt

/-- Bounded comparison assembled from the full family of packet restrictions. -/
def deningerPrimeRestrictionOperator
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ)) :
    E →L[ℝ] DeningerHilbertSum Kp :=
  LinearMap.mkContinuous
    (deningerPrimeRestrictionLinearMap restriction hsummable) C
    (deningerPrimeRestrictionLinearMap_norm_le
      restriction hsummable hC hBessel)

@[simp] theorem deningerPrimeRestrictionOperator_apply
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) (p : Nat.Primes) :
    deningerPrimeRestrictionOperator restriction hsummable hC hBessel x p =
      restriction p x := rfl

/-- The assembled comparison loses exactly the vectors lost by every local restriction. -/
theorem deningerPrimeRestrictionOperator_mem_ker_iff
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) :
    x ∈ LinearMap.ker
        (deningerPrimeRestrictionOperator restriction hsummable hC hBessel).toLinearMap ↔
      ∀ p, restriction p x = 0 := by
  change deningerPrimeRestrictionOperator restriction hsummable hC hBessel x = 0 ↔ _
  constructor
  · intro hx p
    have hp := congrArg (fun y : DeningerHilbertSum Kp => y p) hx
    simpa using hp
  · intro hx
    ext p
    simp [hx p]

/-! ## Pulled-back full-block Green family -/

/-- Local full-packet Green form transported to the arithmetic source. -/
def deningerPrimeRestrictionLocalGreenForm
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (p : Nat.Primes) : E →L[ℝ] E →L[ℝ] ℝ :=
  deningerPullbackGreenForm
    (deningerPrimeRestrictionOperator restriction hsummable hC hBessel)
    (deningerPrimeBlockGreenForm p)

@[simp] theorem deningerPrimeRestrictionLocalGreenForm_apply_apply
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (p : Nat.Primes) (x y : E) :
    deningerPrimeRestrictionLocalGreenForm restriction hsummable hC hBessel p x y =
      deningerPrimeGraphGreenCoefficient p *
        inner ℝ (restriction p x) (restriction p y) := by
  rw [deningerPrimeRestrictionLocalGreenForm,
    deningerPullbackGreenForm_apply_apply, deningerPrimeBlockGreenForm,
    deningerBlockCoordinateGreenForm_apply_apply]
  rfl

variable [∀ p, CompleteSpace (Kp p)]

/-- The source local forms are unordered operator-norm summable under the single Bessel bound. -/
theorem summable_deningerPrimeRestrictionLocalGreenForm
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ)) :
    Summable (deningerPrimeRestrictionLocalGreenForm
      restriction hsummable hC hBessel) :=
  summable_deningerPullbackGreenForm
    (deningerPrimeRestrictionOperator restriction hsummable hC hBessel)
    deningerPrimeBlockGreenForm summable_deningerPrimeBlockGreenForm

/-- Global Green form assembled on the source from all full prime-packet restrictions. -/
def deningerPrimeRestrictionSummedGreenForm
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ)) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑' p, deningerPrimeRestrictionLocalGreenForm
    restriction hsummable hC hBessel p

/-- The source sum is exactly the pullback of the faithful full-block target form. -/
theorem deningerPrimeRestrictionSummedGreenForm_eq
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ)) :
    deningerPrimeRestrictionSummedGreenForm restriction hsummable hC hBessel =
      deningerPullbackGreenForm
        (deningerPrimeRestrictionOperator restriction hsummable hC hBessel)
        deningerPrimeBlockSummedGreenForm :=
  deningerSummedPullbackGreenForm_eq
    (deningerPrimeRestrictionOperator restriction hsummable hC hBessel)
    deningerPrimeBlockGreenForm summable_deningerPrimeBlockGreenForm

/-- Exact weighted Parseval formula for the assembled source energy. -/
theorem deningerPrimeRestrictionSummedGreenForm_self
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) :
    deningerPrimeRestrictionSummedGreenForm restriction hsummable hC hBessel x x =
      ∑' p, deningerPrimeGraphGreenCoefficient p * ‖restriction p x‖ ^ 2 := by
  rw [deningerPrimeRestrictionSummedGreenForm_eq,
    deningerPullbackGreenForm_apply_apply,
    deningerPrimeBlockSummedGreenForm_self]
  rfl

/-- The assembled source energy is nonnegative. -/
theorem deningerPrimeRestrictionSummedGreenForm_nonneg
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) :
    0 ≤ deningerPrimeRestrictionSummedGreenForm restriction hsummable hC hBessel x x := by
  rw [deningerPrimeRestrictionSummedGreenForm_self]
  exact tsum_nonneg fun p => mul_nonneg
    (deningerPrimeGraphGreenCoefficient_pos p).le (sq_nonneg _)

/-- **Simultaneous-kernel radical law.**  The global source energy loses exactly the vectors killed
by every full prime-packet restriction. -/
theorem deningerPrimeRestrictionSummedGreenForm_self_eq_zero_iff
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) :
    deningerPrimeRestrictionSummedGreenForm restriction hsummable hC hBessel x x = 0 ↔
      ∀ p, restriction p x = 0 := by
  let U := deningerPrimeRestrictionOperator restriction hsummable hC hBessel
  calc
    deningerPrimeRestrictionSummedGreenForm restriction hsummable hC hBessel x x = 0 ↔
        deningerPullbackGreenForm U deningerPrimeBlockSummedGreenForm x x = 0 := by
      rw [deningerPrimeRestrictionSummedGreenForm_eq]
    _ ↔ x ∈ LinearMap.ker U.toLinearMap :=
      deningerPullbackGreenForm_self_eq_zero_iff_mem_ker U
        deningerPrimeBlockSummedGreenForm
        deningerPrimeBlockSummedGreenForm_self_eq_zero_iff x
    _ ↔ ∀ p, restriction p x = 0 := by
      exact deningerPrimeRestrictionOperator_mem_ker_iff
        restriction hsummable hC hBessel x

/-- Boundary classification plus the Bessel bound is exactly the full Green-radical theorem. -/
theorem deningerPrimeRestrictionSummedGreenForm_self_eq_zero_iff_mem_boundaries
    (restriction : ∀ p, E →L[ℝ] Kp p)
    (hsummable : ∀ x, Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (boundaries : Submodule ℝ E)
    (hclassifies : ∀ x, (∀ p, restriction p x = 0) ↔ x ∈ boundaries)
    (x : E) :
    deningerPrimeRestrictionSummedGreenForm restriction hsummable hC hBessel x x = 0 ↔
      x ∈ boundaries := by
  rw [deningerPrimeRestrictionSummedGreenForm_self_eq_zero_iff,
    hclassifies]

end

end RHTower
