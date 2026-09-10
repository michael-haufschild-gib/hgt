import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuImageLoss
import GaloisForLFunctions.HTGeometry.RatFuncCompositionDegree

/-!
# The exact rational-function survivor of a quadratic endomorphism

The characteristic-two map used by Borisov--Gabber--Vasiu also defines a rational
substitution over any field. Applying the corpus's degree multiplicativity and
image-loss theorems proves that its image fields never stabilize at a finite
stage, while their infinite intersection is exactly the coefficient field.
-/

open Polynomial
noncomputable section

namespace GaloisForLFunctions.HTGeometry
variable {K : Type*} [Field K]

/-- The characteristic-power example, viewed as a rational function over any field. -/
def bgvQuadraticRationalSource : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) (X + X ^ 2)

/-- The source polynomial has degree two in every characteristic. -/
theorem bgv_quadraticPolynomial_degree :
    (X + X ^ 2 : Polynomial K).natDegree = 2 := by
  rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt]
  · simp
  · simp

/-- The corresponding function-field extension has degree two. -/
theorem bgv_quadraticRational_degree :
    ratFuncDegree (bgvQuadraticRationalSource : RatFunc K) = 2 := by
  rw [ratFuncDegree, bgvQuadraticRationalSource, RatFunc.num_algebraMap,
    RatFunc.denom_algebraMap, bgv_quadraticPolynomial_degree, Polynomial.natDegree_one,
    max_eq_left (Nat.zero_le 2)]

/-- No nonconstant-source assumption is needed as input for this explicit family. -/
theorem bgv_quadraticRational_nonconstant :
    ¬ ∃ c : K, bgvQuadraticRationalSource = RatFunc.C c := by
  rintro ⟨c, hc⟩
  change algebraMap (Polynomial K) (RatFunc K) (X + X ^ 2) = RatFunc.C c at hc
  rw [← RatFunc.algebraMap_C] at hc
  have hp := RatFunc.algebraMap_injective K hc
  have h := congrArg Polynomial.natDegree hp
  rw [bgv_quadraticPolynomial_degree, Polynomial.natDegree_C] at h
  omega

/-- Actual quadratic substitution on the rational-function field. -/
def bgvQuadraticRationalMap : RatFunc K →ₐ[K] RatFunc K :=
  ratFuncSubstitutionAlgHom bgvQuadraticRationalSource bgv_quadraticRational_nonconstant

/-- Every nonconstant rational observable doubles its degree under one pullback. -/
theorem bgv_quadraticRationalMap_degree (a : RatFunc K) :
    ratFuncDegree (bgvQuadraticRationalMap a) = ratFuncDegree a * 2 := by
  rw [bgvQuadraticRationalMap, ratFuncDegree_substitution, bgv_quadraticRational_degree]

/-- The complete iteration law includes constants and all numerator-denominator cancellations. -/
theorem bgv_quadraticRationalMap_iterate_degree (n : ℕ) (a : RatFunc K) :
    ratFuncDegree ((bgvQuadraticRationalMap ^ n) a) = ratFuncDegree a * 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [AlgHom.coe_pow, Function.iterate_succ_apply'] at ih ⊢
      rw [bgv_quadraticRationalMap_degree, ih, pow_succ, mul_assoc]

/-- No rational function can pull back to the degree-one coordinate. -/
theorem bgv_quadraticRationalMap_not_surjective :
    ¬ Function.Surjective (bgvQuadraticRationalMap : RatFunc K →ₐ[K] RatFunc K) := by
  intro h
  obtain ⟨a, ha⟩ := h RatFunc.X
  have hd := bgv_quadraticRationalMap_degree a
  rw [ha] at hd
  simp [ratFuncDegree] at hd
  omega

/-- Every finite image is strictly different from its successor. -/
theorem bgv_quadraticRationalMap_no_finite_stabilization (n : ℕ) :
    Set.range (bgvQuadraticRationalMap ^ n : RatFunc K →ₐ[K] RatFunc K) ≠
      Set.range (bgvQuadraticRationalMap ^ (n + 1) : RatFunc K →ₐ[K] RatFunc K) := by
  rw [ne_eq, bgv_field_range_stabilizes_iff]
  exact bgv_quadraticRationalMap_not_surjective

/-- The infinite reversible core is never one of the finite images. -/
theorem bgv_quadraticRationalMap_core_not_finite_stage (n : ℕ) :
    (stableRangeCore (bgvQuadraticRationalMap (K := K)) : Set (RatFunc K)) ≠
      Set.range (bgvQuadraticRationalMap ^ n : RatFunc K →ₐ[K] RatFunc K) := by
  rw [ne_eq, bgv_stableRangeCore_finite_stage_iff]
  exact bgv_quadraticRationalMap_not_surjective

/-- The exact survivor is the coefficient field: every nonconstant observable eventually leaves. -/
theorem bgv_quadraticRationalMap_stableCore :
    stableRangeCore (bgvQuadraticRationalMap (K := K)) = ⊥ := by
  apply le_antisymm
  · intro a ha
    by_contra hc
    have hnc : ¬ ∃ c : K, a = RatFunc.C c := by
      rintro ⟨c, rfl⟩
      exact hc (IntermediateField.algebraMap_mem ⊥ c)
    let N := ratFuncDegree a
    obtain ⟨b, hb⟩ := (mem_stableRangeCore_iff bgvQuadraticRationalMap a).mp ha N
    have hbnc : ¬ ∃ c : K, b = RatFunc.C c := by
      rintro ⟨c, rfl⟩
      apply hnc
      refine ⟨c, ?_⟩
      rw [← hb]
      exact (bgvQuadraticRationalMap ^ N).commutes c
    have hpos := ratFuncDegree_pos_of_not_constant hbnc
    have hdeg := bgv_quadraticRationalMap_iterate_degree N b
    rw [hb] at hdeg
    have hle : 2 ^ N ≤ ratFuncDegree a := by
      rw [hdeg]
      exact Nat.le_mul_of_pos_left _ hpos
    have hlarge := succ_le_two_pow N
    omega
  · exact bot_le

end GaloisForLFunctions.HTGeometry
