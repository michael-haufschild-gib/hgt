import GaloisForLFunctions.HTGeometry.ShilovBoundaryMigrationDefect
import Mathlib.RingTheory.LaurentSeries
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Integral and meromorphic parameter towers

The inverse system of power series with transition multiplication by `X`
has zero inverse limit and zero first derived inverse limit. The inverse
of its Roos difference is an explicit coefficientwise finite sum. Replacing
the power-series ring by its Laurent field produces a rank-one inverse
limit, classified by the initial value.

This applies the integral valuation-contraction mechanism of Polo–Rivero,
Lemma 5.3, to the boundary-migration inverse-difference complex. It also
identifies the effect of inverting the parameter before taking the limit.
-/

namespace GaloisForLFunctions.EisensteinDegeneration
open PowerSeries Finset HTGeometry.BoundaryMigration
noncomputable section
variable {K : Type*} [Field K]

/-- The integral tower whose transition is multiplication by the parameter. -/
def parameterBond (_n : ℕ) : PowerSeries K →ₗ[K] PowerSeries K :=
  LinearMap.mulLeft K X

/-- The coefficientwise finite Green series for the integral tower. -/
def parameterTailSum (b : ℕ → PowerSeries K) (n : ℕ) : PowerSeries K :=
  PowerSeries.mk fun k => ∑ j ∈ range (k + 1), coeff (k - j) (b (n + j))

private theorem parameterTailSum_coeff_succ (b : ℕ → PowerSeries K) (n k : ℕ) :
    coeff (k + 1) (parameterTailSum b n) =
      coeff (k + 1) (b n) + coeff k (parameterTailSum b (n + 1)) := by
  simp only [parameterTailSum, coeff_mk]
  rw [sum_range_succ']
  simp only [Nat.add_sub_add_right, Nat.add_zero, Nat.sub_zero]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro j _
  congr 2
  omega

/-- Every forcing sequence has an integral solution to `aₙ − X aₙ₊₁ = bₙ`. -/
theorem parameterTailSum_difference (b : ℕ → PowerSeries K) :
    inverseDifference (fun _ => PowerSeries K) parameterBond (parameterTailSum b) = b := by
  funext n
  apply PowerSeries.ext
  intro k
  change coeff k (parameterTailSum b n - X * parameterTailSum b (n + 1)) = coeff k (b n)
  cases k with
  | zero => simp [parameterTailSum]
  | succ k =>
    rw [map_sub, coeff_succ_X_mul, parameterTailSum_coeff_succ]
    exact add_sub_cancel_right _ _

/-- The integral tower has no nonzero compatible sequence. -/
theorem parameterDifference_injective :
    Function.Injective (inverseDifference (fun _ => PowerSeries K) parameterBond) := by
  intro a b h
  have hc : ∀ k n, coeff k (a n) = coeff k (b n) := by
    intro k
    induction k with
    | zero =>
      intro n
      have hn := congrArg (fun t : ℕ → PowerSeries K => coeff 0 (t n)) h
      change coeff 0 (a n - X * a (n + 1)) = coeff 0 (b n - X * b (n + 1)) at hn
      simpa using hn
    | succ k ih =>
      intro n
      have hn := congrArg (fun t : ℕ → PowerSeries K => coeff (k + 1) (t n)) h
      change coeff (k + 1) (a n - X * a (n + 1)) =
        coeff (k + 1) (b n - X * b (n + 1)) at hn
      rw [map_sub, map_sub, coeff_succ_X_mul, coeff_succ_X_mul, ih (n + 1)] at hn
      exact sub_left_inj.mp hn
  funext n
  exact PowerSeries.ext fun k => hc k n

/-- The Roos difference is surjective even though none of the bonding maps is surjective. -/
theorem parameterDifference_surjective :
    Function.Surjective (inverseDifference (fun _ => PowerSeries K) parameterBond) :=
  fun b => ⟨parameterTailSum b, parameterTailSum_difference b⟩

/-- Unique integral solution of every inhomogeneous compatibility equation. -/
def parameterDifferenceEquiv : (ℕ → PowerSeries K) ≃ₗ[K] (ℕ → PowerSeries K) :=
  LinearEquiv.ofBijective (inverseDifference (fun _ => PowerSeries K) parameterBond)
    ⟨parameterDifference_injective, parameterDifference_surjective⟩

/-- The literal inverse limit is zero. -/
theorem parameterInverseLimit_eq_bot :
    (inverseDifference (fun _ => PowerSeries K) parameterBond).ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr parameterDifference_injective

/-- The first derived inverse limit also vanishes. -/
theorem parameterDerivedLimitOne_subsingleton :
    Subsingleton (DerivedLimitOne (fun _ => PowerSeries K) parameterBond) := by
  change Subsingleton ((ℕ → PowerSeries K) ⧸
    (inverseDifference (fun _ => PowerSeries K) parameterBond).range)
  rw [LinearMap.range_eq_top.mpr parameterDifference_surjective]
  infer_instance

/-- Completion, rather than surjectivity of a transition, removes the derived obstruction. -/
theorem parameterBond_not_surjective (n : ℕ) :
    ¬ Function.Surjective (parameterBond (K := K) n) := by
  intro h
  obtain ⟨f, hf⟩ := h 1
  have hc := congrArg constantCoeff hf
  change constantCoeff (X * f) = constantCoeff 1 at hc
  simp at hc


/-- The same parameter transition after allowing Laurent poles. -/
def laurentParameterBond (_n : ℕ) : LaurentSeries K →ₗ[LaurentSeries K] LaurentSeries K :=
  LinearMap.mulLeft (LaurentSeries K) (HahnSeries.single 1 1)

private theorem laurentParameterStep (a : LaurentSeries K) (n : ℕ) :
    HahnSeries.single 1 1 * (HahnSeries.single (-((n + 1 : ℕ) : ℤ)) 1 * a) =
      HahnSeries.single (-(n : ℤ)) 1 * a := by
  rw [← mul_assoc, HahnSeries.single_mul_single, one_mul,
    show (1 : ℤ) + -((n + 1 : ℕ) : ℤ) = -(n : ℤ) by omega]

/-- Inverting the parameter produces a full Laurent line of compatible families. -/
def laurentParameterInverseLimitEquiv :
    (inverseDifference (fun _ => LaurentSeries K) laurentParameterBond).ker ≃ₗ[LaurentSeries K]
      LaurentSeries K where
  toFun x := x.1 0
  invFun a := ⟨fun n => HahnSeries.single (-(n : ℤ)) 1 * a, by
    funext n
    change HahnSeries.single (-(n : ℤ)) 1 * a -
      HahnSeries.single 1 1 * (HahnSeries.single (-((n + 1 : ℕ) : ℤ)) 1 * a) = 0
    rw [laurentParameterStep, sub_self]⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    change HahnSeries.single (-(n : ℤ)) 1 * x.1 0 = x.1 n
    have hc (j : ℕ) : x.1 j = HahnSeries.single 1 1 * x.1 (j + 1) :=
      sub_eq_zero.mp (congrFun x.2 j)
    induction n with
    | zero => simp [← HahnSeries.C_apply]
    | succ n ih =>
      have hcancel : (HahnSeries.single (-1) (1 : K) : LaurentSeries K) *
          HahnSeries.single 1 1 = 1 := by
        simp [HahnSeries.single_mul_single, ← HahnSeries.C_apply]
      calc
        _ = HahnSeries.single (-1) 1 * (HahnSeries.single (-(n : ℤ)) 1 * x.1 0) := by
          rw [← mul_assoc, HahnSeries.single_mul_single, one_mul,
            show (-1 : ℤ) + -(n : ℤ) = -((n + 1 : ℕ) : ℤ) by omega]
        _ = HahnSeries.single (-1) 1 * x.1 n := by rw [ih]
        _ = x.1 (n + 1) := by rw [hc, ← mul_assoc, hcancel, one_mul]
  right_inv a := by simp [← HahnSeries.C_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The meromorphic inverse limit has rank one over the Laurent field. -/
theorem laurentParameterInverseLimit_finrank :
    Module.finrank (LaurentSeries K)
      (inverseDifference (fun _ => LaurentSeries K) laurentParameterBond).ker = 1 := by
  rw [laurentParameterInverseLimitEquiv.finrank_eq]
  exact Module.finrank_self (LaurentSeries K)

/-- A nonzero Laurent-compatible family exists, although the integral compatible family
space is zero. Thus forming this inverse limit does not commute with inverting the parameter. -/
theorem laurentParameterInverseLimit_nontrivial :
    Nontrivial (inverseDifference (fun _ => LaurentSeries K) laurentParameterBond).ker :=
  laurentParameterInverseLimitEquiv.symm.injective.nontrivial

end
end GaloisForLFunctions.EisensteinDegeneration
