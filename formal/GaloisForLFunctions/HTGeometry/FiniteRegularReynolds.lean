import GaloisForLFunctions.HTGeometry.ConstraintRelativity.ReynoldsEnergy
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact finite regular averaging and its preserved variance

The right regular action on the complete finite-group Euclidean space is
unitary. Its normalized operator average is the constant-coordinate mean,
an idempotent contraction whose fixed vectors are exactly the invariant
vectors. The Reynolds displacement identity and the orthogonal norm
splitting retain precisely the complement discarded by averaging.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
open HTGeometry.ConstraintRelativity
noncomputable section
variable {G : Type*} [Group G] [Fintype G]

def finiteRegularUnitary (g : G) : EuclideanSpace ℂ G ≃ₗᵢ[ℂ] EuclideanSpace ℂ G :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.mulRight g).symm

theorem finiteRegularUnitary_apply (g : G) (v : EuclideanSpace ℂ G) (q : G) :
    finiteRegularUnitary g v q=v (q*g) := rfl

theorem finiteRegularUnitary_mul (g h : G) :
    finiteRegularUnitary (g*h)=(finiteRegularUnitary h).trans (finiteRegularUnitary g) := by
  ext v q
  simp only [LinearIsometryEquiv.trans_apply,finiteRegularUnitary_apply,mul_assoc]

def finiteRegularAverage : EuclideanSpace ℂ G →L[ℂ] EuclideanSpace ℂ G :=
  ((Fintype.card G:ℂ)⁻¹) • ∑ g : G, (finiteRegularUnitary g).toContinuousLinearEquiv.toContinuousLinearMap

theorem finiteRegularAverage_eq_reynolds (v : EuclideanSpace ℂ G) :
    finiteRegularAverage v=reynolds finiteRegularUnitary v := by
  simp only [finiteRegularAverage,reynolds,smul_apply,
    sum_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]

theorem finiteRegularAverage_apply (v : EuclideanSpace ℂ G) (q : G) :
    finiteRegularAverage v q=(Fintype.card G:ℂ)⁻¹*∑ r : G, v r := by
  rw [finiteRegularAverage_eq_reynolds]
  change (Fintype.card G:ℂ)⁻¹*(∑ g : G, finiteRegularUnitary g v) q= _
  simp only [WithLp.ofLp_sum,Finset.sum_apply,finiteRegularUnitary_apply]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft q) v

theorem finiteRegularAverage_energy (v : EuclideanSpace ℂ G) :
    (2*(Fintype.card G:ℝ))⁻¹*∑ g : G, ‖finiteRegularUnitary g v-v‖^2=
      ‖v‖^2-‖finiteRegularAverage v‖^2 := by
  have hU : ∀ g h : G, finiteRegularUnitary (g*h)=
      (finiteRegularUnitary h).trans (finiteRegularUnitary g) := finiteRegularUnitary_mul
  have h := reynolds_energy (S := EuclideanSpace ℂ G) finiteRegularUnitary hU v
  simpa only [finiteRegularAverage_eq_reynolds] using h

theorem finiteRegularAverage_idempotent (v : EuclideanSpace ℂ G) :
    finiteRegularAverage (finiteRegularAverage v)=finiteRegularAverage v := by
  ext q
  simp only [finiteRegularAverage_apply,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card G:ℂ)≠0),one_mul]

theorem finiteRegularAverage_fixed_iff (v : EuclideanSpace ℂ G) :
    finiteRegularAverage v=v ↔ ∀ g : G, finiteRegularUnitary g v=v := by
  constructor
  · intro h g
    have hh := reynolds_fixed finiteRegularUnitary finiteRegularUnitary_mul v g
    rw [← finiteRegularAverage_eq_reynolds,h] at hh
    exact hh
  · intro h
    rw [finiteRegularAverage_eq_reynolds,reynolds]
    simp only [h,Finset.sum_const,Finset.card_univ]
    change (Fintype.card G:ℂ)⁻¹ • ((Fintype.card G:ℕ) • v)=v
    rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card G:ℂ)≠0),one_smul]

theorem finiteRegularAverage_norm_decomposition (v : EuclideanSpace ℂ G) :
    ‖finiteRegularAverage v‖^2+‖v-finiteRegularAverage v‖^2=‖v‖^2 := by
  have h := inner_reynolds_self finiteRegularUnitary finiteRegularUnitary_mul v
  rw [← finiteRegularAverage_eq_reynolds] at h
  have hr : ‖finiteRegularAverage v‖^2=(inner ℂ (finiteRegularAverage v) v).re := by
    rw [← h]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
  have hn := norm_sub_sq (𝕜 := ℂ) (finiteRegularAverage v) v
  rw [norm_sub_rev,show RCLike.re (inner ℂ (finiteRegularAverage v) v)=
    (inner ℂ (finiteRegularAverage v) v).re from rfl,← hr] at hn
  linarith

theorem finiteRegularAverage_norm_le (v : EuclideanSpace ℂ G) :
    ‖finiteRegularAverage v‖ ≤ ‖v‖ := by
  have h := finiteRegularAverage_norm_decomposition v
  nlinarith [sq_nonneg ‖v-finiteRegularAverage v‖,norm_nonneg v,norm_nonneg (finiteRegularAverage v)]

end
end GaloisForLFunctions.HTGeometry
