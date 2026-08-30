import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.Nat

/-!
# Bounded logarithmic prime--infinity shear

A rank-one port into a diagonal operator domain splits by an explicit bounded upper shear whenever
the port vector has an admitted inverse image.  Taking that inverse image through the bounded
coordinate multiplier `1 / log p` is the solid-sequence-space specialization.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k X D : Type*}
variable [NontriviallyNormedField k]
variable [NormedAddCommGroup X] [NormedSpace k X]
variable [NormedAddCommGroup D] [NormedSpace k D]

/-- Bounded upper shear `(x,c) |-> (x + c h,c)`. -/
def boundedUpperShear (h : X) : X × k →L[k] X × k :=
  ((ContinuousLinearMap.fst k X k) +
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.snd k X k) h)).prod
    (ContinuousLinearMap.snd k X k)

@[simp]
theorem boundedUpperShear_apply (h : X) (z : X × k) :
    boundedUpperShear h z = (z.1 + z.2 • h, z.2) := by
  rfl

/-- Upper shears with opposite parameters are bounded two-sided inverses. -/
theorem boundedUpperShear_neg_comp (h : X) :
    (boundedUpperShear (-h)).comp (boundedUpperShear h) =
      ContinuousLinearMap.id k (X × k) := by
  ext z <;> simp [boundedUpperShear]

theorem boundedUpperShear_comp_neg (h : X) :
    (boundedUpperShear h).comp (boundedUpperShear (-h)) =
      ContinuousLinearMap.id k (X × k) := by
  simpa only [neg_neg] using boundedUpperShear_neg_comp (-h)

/-- Rank-one extension of an operator on its normed domain.  The norm on `D` may be the graph norm
of an unbounded ambient operator, so this is the bounded map between graph domain and ambient
space used by the paper theorem. -/
def rankOnePortOperator (Lambda : D →L[k] X) (b : X) : D × k →L[k] X × k :=
  ((Lambda.comp (ContinuousLinearMap.fst k D k)) +
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.snd k D k) b)).prod 0

@[simp]
theorem rankOnePortOperator_apply (Lambda : D →L[k] X) (b : X) (z : D × k) :
    rankOnePortOperator Lambda b z = (Lambda z.1 + z.2 • b, 0) := by
  rfl

/-- Exact bounded similarity.  `h` belongs to the graph domain and solves `Lambda h = -b`; both
domain and ambient shears are bounded, preserve the domain by construction, and remove the port. -/
theorem rankOnePortOperator_boundedly_similar_to_split
    (incl : D →L[k] X) (Lambda : D →L[k] X) (b : X) (h : D)
    (hh : Lambda h = -b) (z : D × k) :
    boundedUpperShear (-(incl h))
        (rankOnePortOperator Lambda b (boundedUpperShear h z)) =
      rankOnePortOperator Lambda 0 z := by
  ext <;> simp [hh, add_assoc]

/-- A bounded inverse multiplier from ambient sequence space into the logarithmic graph domain. -/
structure BoundedLogarithmicDomain where
  inclusion : D →L[k] X
  logarithmicOperator : D →L[k] X
  inverseMultiplier : X →L[k] D
  rightInverse : Function.RightInverse inverseMultiplier logarithmicOperator

/-- Unconditional packaged form: every bounded rank-one port splits when the logarithmic domain
carries its bounded inverse multiplier. -/
theorem boundedLogarithmicPrimeInfinityCoupling_splits
    (L : BoundedLogarithmicDomain (k := k) (X := X) (D := D)) (b : X) (z : D × k) :
    boundedUpperShear (-(L.inclusion (-L.inverseMultiplier b)))
        (rankOnePortOperator L.logarithmicOperator b
          (boundedUpperShear (-L.inverseMultiplier b) z)) =
      rankOnePortOperator L.logarithmicOperator 0 z := by
  apply rankOnePortOperator_boundedly_similar_to_split
  simp [L.rightInverse b]

end

section RealPrimeLp

open scoped ENNReal NNReal

/-- Real `ℓ^q` over ordinary-prime coordinates. -/
abbrev RealPrimeLp (q : ℝ≥0∞) := lp (fun _ : Nat.Primes => ℝ) q

/-- The inverse prime-log multiplier is uniformly bounded by `1 / log 2`. -/
theorem norm_inv_primeLog_le_inv_log_two (p : Nat.Primes) :
    ‖(Real.log (p : ℝ))⁻¹‖ ≤ (Real.log 2)⁻¹ := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogp : 0 < Real.log (p : ℝ) :=
    hlog2.trans_le (Real.log_le_log (by norm_num) hp2)
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlogp)]
  simpa only [one_div] using
    one_div_le_one_div_of_le hlog2 (Real.log_le_log (by norm_num) hp2)

/-- Pointwise multiplication by `1 / log p` on every real `ℓ^q`, `1 ≤ q ≤ ∞`. -/
noncomputable def realPrimeLpInverseLogLinear (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    RealPrimeLp q →ₗ[ℝ] RealPrimeLp q where
  toFun x :=
    ⟨fun p => (Real.log (p : ℝ))⁻¹ * x p,
      (lp.memℓp (((Real.log 2)⁻¹ : ℝ) • x)).mono' fun p => by
        change ‖(Real.log (p : ℝ))⁻¹ * x p‖ ≤
          ‖((Real.log 2)⁻¹ : ℝ) * x p‖
        have hCnorm : ‖((Real.log 2)⁻¹ : ℝ)‖ = (Real.log 2)⁻¹ := by
          rw [Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (Real.log_pos one_lt_two).le)]
        rw [norm_mul, norm_mul, hCnorm]
        exact mul_le_mul_of_nonneg_right
          (norm_inv_primeLog_le_inv_log_two p) (norm_nonneg _)⟩
  map_add' x y := by
    apply Subtype.ext
    funext p
    change (Real.log (p : ℝ))⁻¹ * (x p + y p) =
      (Real.log (p : ℝ))⁻¹ * x p + (Real.log (p : ℝ))⁻¹ * y p
    ring
  map_smul' c x := by
    apply Subtype.ext
    funext p
    change (Real.log (p : ℝ))⁻¹ * (c * x p) =
      c * ((Real.log (p : ℝ))⁻¹ * x p)
    ring

theorem realPrimeLpInverseLogLinear_norm_le (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (x : RealPrimeLp q) :
    ‖realPrimeLpInverseLogLinear q x‖ ≤ (Real.log 2)⁻¹ * ‖x‖ := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hlog2 : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (Real.log_pos one_lt_two).le
  calc
    ‖realPrimeLpInverseLogLinear q x‖ ≤ ‖((Real.log 2)⁻¹ : ℝ) • x‖ := by
      apply lp.norm_mono hq0
      intro p
      change ‖(Real.log (p : ℝ))⁻¹ * x p‖ ≤
        ‖((Real.log 2)⁻¹ : ℝ) * x p‖
      have hCnorm : ‖((Real.log 2)⁻¹ : ℝ)‖ = (Real.log 2)⁻¹ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hlog2]
      rw [norm_mul, norm_mul, hCnorm]
      exact mul_le_mul_of_nonneg_right
        (norm_inv_primeLog_le_inv_log_two p) (norm_nonneg _)
    _ ≤ ‖((Real.log 2)⁻¹ : ℝ)‖ * ‖x‖ := lp.norm_const_smul_le hq0 _ _
    _ = (Real.log 2)⁻¹ * ‖x‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hlog2]

/-- Bounded inverse-log coordinate multiplier on real `ℓ^q`. -/
noncomputable def realPrimeLpInverseLogMultiplier (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    RealPrimeLp q →L[ℝ] RealPrimeLp q :=
  (realPrimeLpInverseLogLinear q).mkContinuous (Real.log 2)⁻¹
    (realPrimeLpInverseLogLinear_norm_le q)

/-- Maximal graph domain of multiplication by `log p` on real `ℓ^q`. -/
def realPrimeLpLogGraph (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    Submodule ℝ (RealPrimeLp q × RealPrimeLp q) where
  carrier := {z | ∀ p, z.2 p = Real.log (p : ℝ) * z.1 p}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy p
    change x.2 p + y.2 p = Real.log (p : ℝ) * (x.1 p + y.1 p)
    rw [hx p, hy p]
    ring
  smul_mem' := by
    intro c x hx p
    change c * x.2 p = Real.log (p : ℝ) * (c * x.1 p)
    rw [hx p]
    ring

abbrev RealPrimeLpLogDomain (q : ℝ≥0∞) [Fact (1 ≤ q)] := realPrimeLpLogGraph q

/-- `1 / log p` lands boundedly in the maximal logarithmic graph domain. -/
noncomputable def realPrimeLpLogDomainInverse (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    RealPrimeLp q →L[ℝ] RealPrimeLpLogDomain q :=
  ((realPrimeLpInverseLogMultiplier q).prod (ContinuousLinearMap.id ℝ (RealPrimeLp q))).codRestrict
    (realPrimeLpLogGraph q) (fun x p => by
      change x p = Real.log (p : ℝ) * ((Real.log (p : ℝ))⁻¹ * x p)
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt <|
        Real.log_pos (by exact_mod_cast p.property.one_lt)), one_mul])

/-- Concrete logarithmic graph-domain package for every real `ℓ^q`, `1 ≤ q ≤ ∞`. -/
noncomputable def realPrimeLpBoundedLogarithmicDomain (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    BoundedLogarithmicDomain (k := ℝ) (X := RealPrimeLp q)
      (D := RealPrimeLpLogDomain q) where
  inclusion := (ContinuousLinearMap.fst ℝ (RealPrimeLp q) (RealPrimeLp q)).comp
    (realPrimeLpLogGraph q).subtypeL
  logarithmicOperator := (ContinuousLinearMap.snd ℝ (RealPrimeLp q) (RealPrimeLp q)).comp
    (realPrimeLpLogGraph q).subtypeL
  inverseMultiplier := realPrimeLpLogDomainInverse q
  rightInverse _ := rfl

/-- Every bounded prime--infinity port over real `ℓ^q`, `1 ≤ q ≤ ∞`, is removed by the
explicit bounded inverse-log shear. -/
theorem realPrimeLp_boundedLogarithmicPrimeInfinityCoupling_splits
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (b : RealPrimeLp q)
    (z : RealPrimeLpLogDomain q × ℝ) :
    boundedUpperShear
        (-((realPrimeLpBoundedLogarithmicDomain q).inclusion
          (-(realPrimeLpBoundedLogarithmicDomain q).inverseMultiplier b)))
        (rankOnePortOperator (realPrimeLpBoundedLogarithmicDomain q).logarithmicOperator b
          (boundedUpperShear (-(realPrimeLpBoundedLogarithmicDomain q).inverseMultiplier b) z)) =
      rankOnePortOperator (realPrimeLpBoundedLogarithmicDomain q).logarithmicOperator 0 z := by
  exact boundedLogarithmicPrimeInfinityCoupling_splits
    (realPrimeLpBoundedLogarithmicDomain q) b z

end RealPrimeLp

section RealPrimeC0

open Filter
open scoped ZeroAtInfty

local instance primeDiscreteTopology : TopologicalSpace Nat.Primes := ⊥

local instance boundedLogarithmicPrimeInfinityShearLocalInst1 : DiscreteTopology Nat.Primes := ⟨rfl⟩

/-- Real `c₀` over ordinary-prime coordinates. -/
abbrev RealPrimeC0 := C₀(Nat.Primes, ℝ)

/-- The coordinate function `p ↦ 1 / log p` belongs to real `c₀(P)`. -/
noncomputable def realPrimeC0InverseLog : RealPrimeC0 where
  toFun p := (Real.log (p : ℝ))⁻¹
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [Filter.cocompact_eq_cofinite]
    have hpNat : Tendsto (fun p : Nat.Primes => (p : ℕ)) cofinite atTop := by
      rw [← Nat.cofinite_eq_atTop]
      exact Nat.Primes.coe_nat_injective.tendsto_cofinite
    have hpReal : Tendsto (fun p : Nat.Primes => (p : ℝ)) cofinite atTop :=
      tendsto_natCast_atTop_atTop.comp hpNat
    exact (Real.tendsto_log_atTop.comp hpReal).inv_tendsto_atTop

/-- Pointwise multiplication by `1 / log p` on real `c₀(P)`. -/
noncomputable def realPrimeC0InverseLogLinear : RealPrimeC0 →ₗ[ℝ] RealPrimeC0 where
  toFun x := realPrimeC0InverseLog * x
  map_add' x y := by
    ext p
    simp [mul_add]
  map_smul' c x := by
    ext p
    change realPrimeC0InverseLog p * (c * x p) =
      c * (realPrimeC0InverseLog p * x p)
    ring

/-- Bounded inverse-log coordinate multiplier on real `c₀(P)`. -/
noncomputable def realPrimeC0InverseLogMultiplier : RealPrimeC0 →L[ℝ] RealPrimeC0 :=
  realPrimeC0InverseLogLinear.mkContinuous ‖realPrimeC0InverseLog‖
    (fun x => norm_mul_le realPrimeC0InverseLog x)

/-- Maximal graph domain of multiplication by `log p` on real `c₀(P)`. -/
def realPrimeC0LogGraph : Submodule ℝ (RealPrimeC0 × RealPrimeC0) where
  carrier := {z | ∀ p, z.2 p = Real.log (p : ℝ) * z.1 p}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy p
    change x.2 p + y.2 p = Real.log (p : ℝ) * (x.1 p + y.1 p)
    rw [hx p, hy p]
    ring
  smul_mem' := by
    intro c x hx p
    change c * x.2 p = Real.log (p : ℝ) * (c * x.1 p)
    rw [hx p]
    ring

abbrev RealPrimeC0LogDomain := realPrimeC0LogGraph

/-- `1 / log p` lands boundedly in the maximal `c₀` logarithmic graph domain. -/
noncomputable def realPrimeC0LogDomainInverse :
    RealPrimeC0 →L[ℝ] RealPrimeC0LogDomain :=
  (realPrimeC0InverseLogMultiplier.prod (ContinuousLinearMap.id ℝ RealPrimeC0)).codRestrict
    realPrimeC0LogGraph (fun x p => by
      change x p = Real.log (p : ℝ) * ((Real.log (p : ℝ))⁻¹ * x p)
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt <|
        Real.log_pos (by exact_mod_cast p.property.one_lt)), one_mul])

/-- Concrete logarithmic graph-domain package for real `c₀(P)`. -/
noncomputable def realPrimeC0BoundedLogarithmicDomain :
    BoundedLogarithmicDomain (k := ℝ) (X := RealPrimeC0)
      (D := RealPrimeC0LogDomain) where
  inclusion := (ContinuousLinearMap.fst ℝ RealPrimeC0 RealPrimeC0).comp
    realPrimeC0LogGraph.subtypeL
  logarithmicOperator := (ContinuousLinearMap.snd ℝ RealPrimeC0 RealPrimeC0).comp
    realPrimeC0LogGraph.subtypeL
  inverseMultiplier := realPrimeC0LogDomainInverse
  rightInverse _ := rfl

/-- Every bounded prime--infinity port over real `c₀(P)` is removed by the explicit bounded
inverse-log shear. -/
theorem realPrimeC0_boundedLogarithmicPrimeInfinityCoupling_splits
    (b : RealPrimeC0) (z : RealPrimeC0LogDomain × ℝ) :
    boundedUpperShear
        (-(realPrimeC0BoundedLogarithmicDomain.inclusion
          (-realPrimeC0BoundedLogarithmicDomain.inverseMultiplier b)))
        (rankOnePortOperator realPrimeC0BoundedLogarithmicDomain.logarithmicOperator b
          (boundedUpperShear (-realPrimeC0BoundedLogarithmicDomain.inverseMultiplier b) z)) =
      rankOnePortOperator realPrimeC0BoundedLogarithmicDomain.logarithmicOperator 0 z := by
  exact boundedLogarithmicPrimeInfinityCoupling_splits
    realPrimeC0BoundedLogarithmicDomain b z

end RealPrimeC0

end GaloisForLFunctions.HTGeometry
