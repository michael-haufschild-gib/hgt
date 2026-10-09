import GaloisForLFunctions.HTGeometry.CayleyWienerHopfIndex
import GaloisForLFunctions.HTGeometry.CompactAdjoint
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-
# The Wiener–Hopf index theorem on the line

Let `P₊` be the Hardy projection of `L²(ℝ)` (frequencies `≥ 0`).  The Cayley symbol
`c(w) = (-1 - 2πiw)/(1 - 2πiw)` (`cayleySymbol`) identifies the one-point compactification of the
frequency line with the unit circle `S`.  Every continuous symbol `U ∈ C(S)` defines the
Fourier multiplier `C_U` with symbol `U ∘ c`, and the Wiener–Hopf lift
`T_U = P₊ C_U P₊ + (1 - P₊)`.

* `circleMultiplierHom`: `U ↦ C_U` is a unital `*`-homomorphism `C(S) → B(L²(ℝ))` sending the
  coordinate `z` to the Cayley unitary.
* `compactHankel`: the Hankel operators `P₊ C_U (1 - P₊)` and `(1 - P₊) C_U P₊` are compact for
  every `U`.  The symbols with compact Hankel operators form a closed `*`-subalgebra containing the
  coordinate, hence everything by Stone–Weierstrass.
* `wienerHopfLift_mul`: `T_U T_V = T_{UV} - H₊(U) H₋(V)`; with Atkinson's criterion
  (`isFredholmOp_of_inverse_mod_compact`) every unimodular `T_U` is Fredholm.
* `fredholmIndex_wienerHopfLift_circlePow`: `T_{zⁿ}` is the `n`-th power of the Cayley lift or of
  its adjoint, of index `n`.
* `exists_log_of_unimodular`: a unimodular `U` of winding number `n` is `zⁿ e^{g}` with `g`
  continuous and purely imaginary on `S`.
* `fredholmIndex_wienerHopfLift_eq_circleWinding`: **`ind T_U` is the winding number of `U`**, by
  the homotopy `zⁿ e^{σ g}` and local constancy of the index.
-/

set_option autoImplicit false

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Atkinson's criterion -/

section Atkinson

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Atkinson.**  An operator invertible modulo compact operators is Fredholm. -/
theorem isFredholmOp_of_inverse_mod_compact {T S : E →L[ℂ] E}
    (h1 : IsCompactOperator ⇑(S * T - 1 : E →L[ℂ] E))
    (h2 : IsCompactOperator ⇑(T * S - 1 : E →L[ℂ] E)) :
    IsFredholmOp T := by
  have hST : IsFredholmOp (1 + (S * T - 1)) := isFredholmOp_one_add_compact h1
  have hTS : IsFredholmOp (1 + (T * S - 1)) := isFredholmOp_one_add_compact h2
  rw [add_sub_cancel] at hST hTS
  refine ⟨?_, ?_, ?_⟩
  · have hle : LinearMap.ker (T : E →ₗ[ℂ] E) ≤ LinearMap.ker ((S * T : E →L[ℂ] E) : E →ₗ[ℂ] E) :=
      fun x hx => by
        simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
        rw [mul_apply_eq_comp, hx, map_zero]
    haveI := hST.finiteDimensional_ker
    exact Submodule.finiteDimensional_of_le hle
  · have hle : LinearMap.range ((T * S : E →L[ℂ] E) : E →ₗ[ℂ] E) ≤ LinearMap.range (T : E →ₗ[ℂ] E) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨S x, rfl⟩
    exact (isClosed_and_finiteDimensional_quotient_of_le hle hTS.isClosed_range
      hTS.finiteDimensional_coker).1
  · have hle : LinearMap.range ((T * S : E →L[ℂ] E) : E →ₗ[ℂ] E) ≤ LinearMap.range (T : E →ₗ[ℂ] E) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨S x, rfl⟩
    exact (isClosed_and_finiteDimensional_quotient_of_le hle hTS.isClosed_range
      hTS.finiteDimensional_coker).2

end Atkinson

/-! ## Symbols on the circle -/

/-- The unit circle `|z| = 1` in `ℂ`, the one-point compactification of the frequency line through
the Cayley symbol. -/
abbrev UnitCircle : Set ℂ := Metric.sphere (0 : ℂ) 1

instance : CompactSpace UnitCircle := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)

theorem continuous_cayleySymbol : Continuous cayleySymbol :=
  continuous_const.sub (continuous_const.mul (continuous_fourier_of_integrable' integrable_cayleyKernel))

/-- The Cayley point `c(w)` of a frequency `w`. -/
def cayleyCirclePoint (w : ℝ) : UnitCircle :=
  ⟨cayleySymbol w, by rw [mem_sphere_zero_iff_norm, norm_cayleySymbol]⟩

theorem continuous_cayleyCirclePoint : Continuous cayleyCirclePoint :=
  continuous_cayleySymbol.subtype_mk _

/-- The frequency symbol `w ↦ U(c(w))` of a continuous function on the circle. -/
def circleSymbol (U : C(UnitCircle, ℂ)) (w : ℝ) : ℂ := U (cayleyCirclePoint w)

theorem measurable_circleSymbol (U : C(UnitCircle, ℂ)) : Measurable (circleSymbol U) :=
  (U.continuous.comp continuous_cayleyCirclePoint).measurable

theorem norm_circleSymbol_le (U : C(UnitCircle, ℂ)) (w : ℝ) : ‖circleSymbol U w‖ ≤ ‖U‖ :=
  U.norm_coe_le_norm _

/-- The Fourier multiplier `C_U` with symbol `U ∘ c`. -/
def circleMultiplier (U : C(UnitCircle, ℂ)) : L2Real →L[ℂ] L2Real :=
  fourierMulCLM (measurable_circleSymbol U) (norm_nonneg U) (norm_circleSymbol_le U)

theorem norm_circleMultiplier_le (U : C(UnitCircle, ℂ)) : ‖circleMultiplier U‖ ≤ ‖U‖ :=
  norm_fourierMulCLM_le _ _ _

theorem circleMultiplier_mul (U V : C(UnitCircle, ℂ)) :
    circleMultiplier (U * V) = circleMultiplier U * circleMultiplier V :=
  (fourierMulCLM_comp (measurable_circleSymbol U) (measurable_circleSymbol V)
    (measurable_circleSymbol (U * V)) (norm_nonneg U) (norm_circleSymbol_le U) (norm_nonneg V)
    (norm_circleSymbol_le V) (norm_nonneg (U * V)) (norm_circleSymbol_le (U * V))
    (Filter.Eventually.of_forall fun _ => rfl)).symm

theorem circleMultiplier_add (U V : C(UnitCircle, ℂ)) :
    circleMultiplier (U + V) = circleMultiplier U + circleMultiplier V :=
  fourierMulCLM_add (measurable_circleSymbol U) (measurable_circleSymbol V)
    (measurable_circleSymbol (U + V)) (norm_nonneg U) (norm_circleSymbol_le U) (norm_nonneg V)
    (norm_circleSymbol_le V) (norm_nonneg (U + V)) (norm_circleSymbol_le (U + V))
    (Filter.Eventually.of_forall fun _ => rfl)

theorem circleMultiplier_smul (c : ℂ) (U : C(UnitCircle, ℂ)) :
    circleMultiplier (c • U) = c • circleMultiplier U :=
  fourierMulCLM_smul (measurable_circleSymbol U) (measurable_circleSymbol (c • U)) (norm_nonneg U)
    (norm_circleSymbol_le U) (norm_nonneg (c • U)) (norm_circleSymbol_le (c • U)) c
    (Filter.Eventually.of_forall fun _ => rfl)

theorem circleMultiplier_one : circleMultiplier 1 = 1 :=
  fourierMulCLM_eq_id _ _ _ (Filter.Eventually.of_forall fun _ => rfl)

theorem circleMultiplier_star (U : C(UnitCircle, ℂ)) :
    circleMultiplier (star U) = star (circleMultiplier U) := by
  rw [ContinuousLinearMap.star_eq_adjoint, circleMultiplier, circleMultiplier,
    adjoint_fourierMulCLM (measurable_circleSymbol U) (measurable_circleSymbol (star U))
      (norm_nonneg U) (norm_circleSymbol_le U) (norm_nonneg (star U))
      (norm_circleSymbol_le (star U)) (fun _ => rfl)]

/-- **The Fourier multiplier representation** `C(S¹) → B(L²(ℝ))`, `U ↦ C_{U ∘ c}`. -/
def circleMultiplierHom : C(UnitCircle, ℂ) →⋆ₐ[ℂ] (L2Real →L[ℂ] L2Real) where
  toFun := circleMultiplier
  map_one' := circleMultiplier_one
  map_mul' := circleMultiplier_mul
  map_zero' := by
    have h := circleMultiplier_smul 0 0
    rw [zero_smul, zero_smul] at h
    exact h
  map_add' := circleMultiplier_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, circleMultiplier_smul, circleMultiplier_one,
      Algebra.algebraMap_eq_smul_one]
  map_star' := circleMultiplier_star

theorem continuous_circleMultiplier : Continuous circleMultiplier :=
  AddMonoidHomClass.continuous_of_bound circleMultiplierHom 1 fun U => by
    rw [one_mul]
    exact norm_circleMultiplier_le U

/-- The coordinate `z` of the circle. -/
def circleCoord : C(UnitCircle, ℂ) := ContinuousMap.restrict UnitCircle (ContinuousMap.id ℂ)

theorem circleMultiplier_circleCoord : circleMultiplier circleCoord = cayleyUnitary := by
  rw [cayleyUnitary_eq_fourierMulCLM]
  rfl

/-! ## Hankel operators are compact -/

/-- The Hankel operator `P₊ C_U (1 - P₊)`. -/
def hankelPlus (U : C(UnitCircle, ℂ)) : L2Real →L[ℂ] L2Real :=
  halfProj * circleMultiplier U * (1 - halfProj)

/-- The Hankel operator `(1 - P₊) C_U P₊`. -/
def hankelMinus (U : C(UnitCircle, ℂ)) : L2Real →L[ℂ] L2Real :=
  (1 - halfProj) * circleMultiplier U * halfProj

theorem continuous_hankelPlus : Continuous hankelPlus :=
  (continuous_const.mul continuous_circleMultiplier).mul continuous_const

theorem continuous_hankelMinus : Continuous hankelMinus :=
  (continuous_const.mul continuous_circleMultiplier).mul continuous_const

theorem isCompactOperator_mul_left {A K : L2Real →L[ℂ] L2Real} (hK : IsCompactOperator K) :
    IsCompactOperator (A * K) := hK.clm_comp A

theorem isCompactOperator_mul_right {A K : L2Real →L[ℂ] L2Real} (hK : IsCompactOperator K) :
    IsCompactOperator (K * A) := hK.comp_clm A

theorem one_sub_halfProj_mul_self : (1 - halfProj) * (1 - halfProj) = 1 - halfProj := by
  rw [sub_mul, one_mul, mul_sub, mul_one, halfProj_mul_self, sub_self, sub_zero]

theorem hankelPlus_mul (U V : C(UnitCircle, ℂ)) :
    hankelPlus (U * V) = halfProj * circleMultiplier U * hankelPlus V +
      hankelPlus U * (circleMultiplier V * (1 - halfProj)) := by
  simp only [hankelPlus, circleMultiplier_mul]
  have h : halfProj * (circleMultiplier U * circleMultiplier V) * (1 - halfProj) =
      halfProj * circleMultiplier U * (halfProj + (1 - halfProj)) * circleMultiplier V *
        (1 - halfProj) := by
    rw [add_sub_cancel, mul_one]
    noncomm_ring
  rw [h, ← one_sub_halfProj_mul_self, ← halfProj_mul_self]
  noncomm_ring

theorem hankelMinus_mul (U V : C(UnitCircle, ℂ)) :
    hankelMinus (U * V) = hankelMinus U * (circleMultiplier V * halfProj) +
      (1 - halfProj) * circleMultiplier U * hankelMinus V := by
  simp only [hankelMinus, circleMultiplier_mul]
  have h : (1 - halfProj) * (circleMultiplier U * circleMultiplier V) * halfProj =
      (1 - halfProj) * circleMultiplier U * (halfProj + (1 - halfProj)) * circleMultiplier V *
        halfProj := by
    rw [add_sub_cancel, mul_one]
    noncomm_ring
  rw [h, ← one_sub_halfProj_mul_self, ← halfProj_mul_self]
  noncomm_ring

theorem hankelPlus_star (U : C(UnitCircle, ℂ)) : hankelPlus (star U) = star (hankelMinus U) := by
  simp only [hankelPlus, hankelMinus, circleMultiplier_star, star_mul, star_sub, star_one,
    star_halfProj, mul_assoc]

theorem hankelMinus_star (U : C(UnitCircle, ℂ)) : hankelMinus (star U) = star (hankelPlus U) := by
  simp only [hankelPlus, hankelMinus, circleMultiplier_star, star_mul, star_sub, star_one,
    star_halfProj, mul_assoc]

theorem isCompactOperator_star {K : L2Real →L[ℂ] L2Real} (hK : IsCompactOperator K) :
    IsCompactOperator ⇑(star K) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact isCompactOperator_adjoint_rectangular K hK

/-- **The symbols with compact Hankel operators form a closed star subalgebra.** -/
def compactHankelSymbols : StarSubalgebra ℂ C(UnitCircle, ℂ) where
  carrier := {U | IsCompactOperator (hankelPlus U) ∧ IsCompactOperator (hankelMinus U)}
  mul_mem' {U V} hU hV := by
    refine ⟨?_, ?_⟩
    · rw [hankelPlus_mul]
      exact (isCompactOperator_mul_left hV.1).add (isCompactOperator_mul_right hU.1)
    · rw [hankelMinus_mul]
      exact (isCompactOperator_mul_right hU.2).add (isCompactOperator_mul_left hV.2)
  add_mem' {U V} hU hV := by
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_setOf_eq, hankelPlus, circleMultiplier_add, mul_add, add_mul] at hU hV ⊢
      exact hU.1.add hV.1
    · simp only [Set.mem_setOf_eq, hankelMinus, circleMultiplier_add, mul_add, add_mul] at hU hV ⊢
      exact hU.2.add hV.2
  algebraMap_mem' c := by
    have hPQ : halfProj * (1 - halfProj) = 0 := by rw [mul_sub, mul_one, halfProj_mul_self, sub_self]
    have hQP : (1 - halfProj) * halfProj = 0 := by rw [sub_mul, one_mul, halfProj_mul_self, sub_self]
    have hc : circleMultiplier (algebraMap ℂ C(UnitCircle, ℂ) c) = c • 1 := by
      rw [Algebra.algebraMap_eq_smul_one, circleMultiplier_smul, circleMultiplier_one]
    refine ⟨?_, ?_⟩
    · rw [hankelPlus, hc, mul_smul_comm, mul_one, smul_mul_assoc, hPQ, smul_zero]
      exact isCompactOperator_zero
    · rw [hankelMinus, hc, mul_smul_comm, mul_one, smul_mul_assoc, hQP, smul_zero]
      exact isCompactOperator_zero
  star_mem' {U} hU := by
    refine ⟨?_, ?_⟩
    · change IsCompactOperator (hankelPlus (star U))
      rw [hankelPlus_star]
      exact isCompactOperator_star hU.2
    · change IsCompactOperator (hankelMinus (star U))
      rw [hankelMinus_star]
      exact isCompactOperator_star hU.1

theorem isClosed_compactHankelSymbols :
    IsClosed (compactHankelSymbols : Set C(UnitCircle, ℂ)) :=
  ((isClosed_setOf_isCompactOperator (𝕜₁ := ℂ) (M₁ := L2Real) (M₂ := L2Real)).preimage
    continuous_hankelPlus).inter
  ((isClosed_setOf_isCompactOperator (𝕜₁ := ℂ) (M₁ := L2Real) (M₂ := L2Real)).preimage
    continuous_hankelMinus)

theorem circleCoord_mem_compactHankelSymbols : circleCoord ∈ compactHankelSymbols := by
  refine ⟨?_, ?_⟩
  · change IsCompactOperator (hankelPlus circleCoord)
    rw [hankelPlus, circleMultiplier_circleCoord, halfProj_cayleyUnitary_one_sub]
    exact isCompactOperator_zero
  · change IsCompactOperator (hankelMinus circleCoord)
    rw [hankelMinus, circleMultiplier_circleCoord, one_sub_halfProj_cayleyUnitary_halfProj]
    exact (isCompactOperator_innerRankOne expMinus expPlus).smul (-2 : ℂ)

/-- **Every continuous symbol on the compactified line has compact Hankel operators.** -/
theorem compactHankel (U : C(UnitCircle, ℂ)) :
    IsCompactOperator (hankelPlus U) ∧ IsCompactOperator (hankelMinus U) := by
  have hle : StarAlgebra.elemental ℂ circleCoord ≤ compactHankelSymbols :=
    StarAlgebra.elemental.le_of_mem isClosed_compactHankelSymbols
      circleCoord_mem_compactHankelSymbols
  have htop := ContinuousMap.elemental_id_eq_top (𝕜 := ℂ) UnitCircle
  have hU : U ∈ StarAlgebra.elemental ℂ circleCoord := by
    rw [circleCoord, htop]
    trivial
  exact hle hU

/-! ## Wiener–Hopf lifts -/

/-- **The Wiener–Hopf lift** `T_U = P₊ C_U P₊ + (1 - P₊)` of a symbol `U` on the circle. -/
def wienerHopfLift (U : C(UnitCircle, ℂ)) : L2Real →L[ℂ] L2Real :=
  halfProj * circleMultiplier U * halfProj + (1 - halfProj)

theorem wienerHopfLift_circleCoord : wienerHopfLift circleCoord = cayleyWienerHopf := by
  rw [wienerHopfLift, circleMultiplier_circleCoord]
  rfl

theorem wienerHopfLift_one : wienerHopfLift 1 = 1 := by
  rw [wienerHopfLift, circleMultiplier_one, mul_one, halfProj_mul_self, add_sub_cancel]

/-- `T_U T_V = T_{UV} - H₊(U) H₋(V)`. -/
theorem wienerHopfLift_mul (U V : C(UnitCircle, ℂ)) :
    wienerHopfLift U * wienerHopfLift V = wienerHopfLift (U * V) - hankelPlus U * hankelMinus V := by
  have hP := halfProj_mul_self
  have hQ := one_sub_halfProj_mul_self
  simp only [wienerHopfLift, hankelPlus, hankelMinus, circleMultiplier_mul]
  have hPQ : halfProj * (1 - halfProj) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hQP : (1 - halfProj) * halfProj = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  calc (halfProj * circleMultiplier U * halfProj + (1 - halfProj)) *
        (halfProj * circleMultiplier V * halfProj + (1 - halfProj))
      = halfProj * circleMultiplier U * (halfProj * halfProj) * circleMultiplier V * halfProj +
          halfProj * circleMultiplier U * (halfProj * (1 - halfProj)) +
          (1 - halfProj) * halfProj * circleMultiplier V * halfProj +
          (1 - halfProj) * (1 - halfProj) := by noncomm_ring
    _ = halfProj * circleMultiplier U * halfProj * circleMultiplier V * halfProj + (1 - halfProj) := by
        rw [hP, hPQ, hQP, hQ]
        noncomm_ring
    _ = halfProj * (circleMultiplier U * circleMultiplier V) * halfProj + (1 - halfProj) -
          halfProj * circleMultiplier U * (1 - halfProj) * ((1 - halfProj) * circleMultiplier V * halfProj) := by
        rw [show halfProj * circleMultiplier U * (1 - halfProj) *
            ((1 - halfProj) * circleMultiplier V * halfProj) =
            halfProj * circleMultiplier U * ((1 - halfProj) * (1 - halfProj)) * circleMultiplier V *
              halfProj by noncomm_ring, hQ]
        noncomm_ring

theorem wienerHopfLift_star (U : C(UnitCircle, ℂ)) :
    wienerHopfLift (star U) = star (wienerHopfLift U) := by
  simp only [wienerHopfLift, circleMultiplier_star, star_add, star_mul, star_sub, star_one,
    star_halfProj, mul_assoc]

theorem wienerHopfLift_sub (U V : C(UnitCircle, ℂ)) :
    wienerHopfLift U - wienerHopfLift V = halfProj * circleMultiplier (U - V) * halfProj := by
  have h : circleMultiplier (U - V) = circleMultiplier U - circleMultiplier V := by
    rw [sub_eq_add_neg, circleMultiplier_add, show -V = (-1 : ℂ) • V by simp, circleMultiplier_smul]
    simp [sub_eq_add_neg]
  rw [wienerHopfLift, wienerHopfLift, h]
  noncomm_ring

theorem norm_wienerHopfLift_sub_le (U V : C(UnitCircle, ℂ)) :
    ‖wienerHopfLift U - wienerHopfLift V‖ ≤ ‖U - V‖ := by
  rw [wienerHopfLift_sub]
  have hP : ‖halfProj‖ ≤ 1 :=
    (RHTower.indicatorCutoff_isStarProjection (Ici 0) measurableSet_Ici).norm_le
  calc ‖halfProj * circleMultiplier (U - V) * halfProj‖
      ≤ ‖halfProj‖ * ‖circleMultiplier (U - V)‖ * ‖halfProj‖ := by
        refine (norm_mul_le _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ 1 * ‖U - V‖ * 1 := by
        gcongr
        exact norm_circleMultiplier_le _
    _ = ‖U - V‖ := by ring

theorem continuous_wienerHopfLift : Continuous wienerHopfLift :=
  LipschitzWith.continuous (LipschitzWith.of_dist_le_mul fun U V => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact norm_wienerHopfLift_sub_le U V)

/-- **The Wiener–Hopf lift of a unimodular symbol is Fredholm** (Atkinson, through the compact
Hankel operators). -/
theorem isFredholmOp_wienerHopfLift {U : C(UnitCircle, ℂ)} (hU : star U * U = 1) :
    IsFredholmOp (wienerHopfLift U) := by
  have hU' : U * star U = 1 := by rw [mul_comm]; exact hU
  refine isFredholmOp_of_inverse_mod_compact (S := wienerHopfLift (star U)) ?_ ?_
  · rw [wienerHopfLift_mul, hU, wienerHopfLift_one, sub_sub_cancel_left]
    exact isCompactOperator_mul_right (compactHankel (star U)).1 |>.neg
  · rw [wienerHopfLift_mul, hU', wienerHopfLift_one, sub_sub_cancel_left]
    exact isCompactOperator_mul_right (compactHankel U).1 |>.neg

/-! ## Kernels of composites of surjections -/

section KernelComposite

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- For surjective `B`, `ker (A ∘ B)` is an extension of `ker A` by `ker B`: its rank is the sum. -/
theorem rank_ker_comp_of_surjective (A B : E →ₗ[ℂ] E) (hB : Function.Surjective B) :
    Module.rank ℂ (LinearMap.ker (A ∘ₗ B)) =
      Module.rank ℂ (LinearMap.ker A) + Module.rank ℂ (LinearMap.ker B) := by
  let B' : LinearMap.ker (A ∘ₗ B) →ₗ[ℂ] LinearMap.ker A :=
    B.restrict (p := LinearMap.ker (A ∘ₗ B)) (q := LinearMap.ker A) fun x hx => by
      simpa using hx
  have hsurj : Function.Surjective B' := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hB y
    exact ⟨⟨x, by simpa using hy⟩, rfl⟩
  have hrange : LinearMap.range B' = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hker : Module.rank ℂ (LinearMap.ker B') = Module.rank ℂ (LinearMap.ker B) := by
    refine LinearEquiv.rank_eq ?_
    refine
      { toFun := fun x => ⟨(x : LinearMap.ker (A ∘ₗ B)), by
          have h := x.2
          rw [LinearMap.mem_ker] at h
          exact congrArg Subtype.val h⟩
        invFun := fun x => ⟨⟨x, by simp [LinearMap.mem_ker.mp x.2]⟩, by
          rw [LinearMap.mem_ker]
          ext
          simp [B', LinearMap.mem_ker.mp x.2]⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl
        map_add' := fun x y => rfl
        map_smul' := fun c x => rfl }
  have h := LinearMap.rank_range_add_rank_ker B'
  rw [hrange, rank_top, hker] at h
  rw [← h]

end KernelComposite

/-! ## Powers of the Cayley lift -/

theorem cayleyWienerHopf_pow_mul_star_pow (n : ℕ) :
    cayleyWienerHopf ^ n * star cayleyWienerHopf ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc cayleyWienerHopf ^ (n + 1) * star cayleyWienerHopf ^ (n + 1)
        = cayleyWienerHopf ^ n * (cayleyWienerHopf * star cayleyWienerHopf) *
            star cayleyWienerHopf ^ n := by
          rw [pow_succ, pow_succ']
          noncomm_ring
      _ = 1 := by rw [cayleyWienerHopf_mul_star, mul_one, ih]

theorem surjective_cayleyWienerHopf_pow (n : ℕ) : Function.Surjective (cayleyWienerHopf ^ n) :=
  fun y => ⟨(star cayleyWienerHopf ^ n) y, by
    rw [← mul_apply_eq_comp, cayleyWienerHopf_pow_mul_star_pow, one_apply_eq_self]⟩

theorem rank_ker_cayleyWienerHopf_pow (n : ℕ) :
    Module.rank ℂ (LinearMap.ker ((cayleyWienerHopf ^ n : L2Real →L[ℂ] L2Real) :
      L2Real →ₗ[ℂ] L2Real)) = n := by
  induction n with
  | zero =>
    rw [pow_zero, ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id, LinearMap.ker_id, rank_bot,
      Nat.cast_zero]
  | succ n ih =>
    have hcomp : ((cayleyWienerHopf ^ (n + 1) : L2Real →L[ℂ] L2Real) : L2Real →ₗ[ℂ] L2Real) =
        (cayleyWienerHopf : L2Real →ₗ[ℂ] L2Real) ∘ₗ
          ((cayleyWienerHopf ^ n : L2Real →L[ℂ] L2Real) : L2Real →ₗ[ℂ] L2Real) := by
      rw [pow_succ']
      rfl
    rw [hcomp, rank_ker_comp_of_surjective _ _ (surjective_cayleyWienerHopf_pow n), ih,
      ker_cayleyWienerHopf, ← Module.finrank_eq_rank, finrank_span_singleton expPlus_ne_zero]
    push_cast
    ring

theorem isFredholmOp_cayleyWienerHopf_pow (n : ℕ) :
    IsFredholmOp (cayleyWienerHopf ^ n) ∧ fredholmIndex (cayleyWienerHopf ^ n) = n := by
  have hrank := rank_ker_cayleyWienerHopf_pow n
  have hfd : FiniteDimensional ℂ (LinearMap.ker ((cayleyWienerHopf ^ n : L2Real →L[ℂ] L2Real) :
      L2Real →ₗ[ℂ] L2Real)) :=
    Module.rank_lt_aleph0_iff.mp (by rw [hrank]; exact Cardinal.natCast_lt_aleph0)
  have hrange : LinearMap.range ((cayleyWienerHopf ^ n : L2Real →L[ℂ] L2Real) :
      L2Real →ₗ[ℂ] L2Real) = ⊤ :=
    LinearMap.range_eq_top.mpr (surjective_cayleyWienerHopf_pow n)
  refine ⟨⟨hfd, by rw [hrange]; exact isClosed_univ, by rw [hrange]; infer_instance⟩, ?_⟩
  have hq : Module.finrank ℂ (L2Real ⧸ (⊤ : Submodule ℂ L2Real)) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [fredholmIndex, hrange, hq, Module.finrank_eq_of_rank_eq hrank]
  simp

theorem norm_star_cayleyWienerHopf_pow_apply (n : ℕ) (x : L2Real) :
    ‖(star cayleyWienerHopf ^ n) x‖ = ‖x‖ := by
  have h : star (star cayleyWienerHopf ^ n) * star cayleyWienerHopf ^ n = 1 := by
    rw [star_pow, star_star, cayleyWienerHopf_pow_mul_star_pow]
  have hsq : ‖(star cayleyWienerHopf ^ n) x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    congr 1
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← mul_apply_eq_comp, h, one_apply_eq_self]
  have := norm_nonneg ((star cayleyWienerHopf ^ n) x)
  have := norm_nonneg x
  nlinarith [sq_nonneg (‖(star cayleyWienerHopf ^ n) x‖ - ‖x‖),
    sq_nonneg (‖(star cayleyWienerHopf ^ n) x‖ + ‖x‖)]

theorem isFredholmOp_star_cayleyWienerHopf_pow (n : ℕ) :
    IsFredholmOp (star cayleyWienerHopf ^ n) ∧ fredholmIndex (star cayleyWienerHopf ^ n) = -n := by
  set S := star cayleyWienerHopf ^ n
  have hker : LinearMap.ker (S : L2Real →ₗ[ℂ] L2Real) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have := norm_star_cayleyWienerHopf_pow_apply n x
    rw [show (S : L2Real →ₗ[ℂ] L2Real) x = S x from rfl] at hx
    rw [hx, norm_zero] at this
    exact norm_eq_zero.mp this.symm
  have hclosed : IsClosed (LinearMap.range (S : L2Real →ₗ[ℂ] L2Real) : Set L2Real) := by
    have hiso : Isometry S := AddMonoidHomClass.isometry_of_norm S
      (norm_star_cayleyWienerHopf_pow_apply n)
    exact hiso.isClosedEmbedding.isClosed_range
  set R := LinearMap.range (S : L2Real →ₗ[ℂ] L2Real)
  haveI : CompleteSpace R := hclosed.completeSpace_coe
  haveI : R.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace R
  have horth : Rᗮ = LinearMap.ker ((cayleyWienerHopf ^ n : L2Real →L[ℂ] L2Real) :
      L2Real →ₗ[ℂ] L2Real) := by
    have h := ContinuousLinearMap.orthogonal_range S
    rw [← ContinuousLinearMap.star_eq_adjoint, star_pow, star_star] at h
    exact h
  have hrank := rank_ker_cayleyWienerHopf_pow n
  have hq : Module.finrank ℂ (L2Real ⧸ R) = n := by
    rw [(Submodule.quotientEquivOfIsCompl R Rᗮ (Submodule.isCompl_orthogonal R)).finrank_eq,
      horth, Module.finrank_eq_of_rank_eq hrank]
  have hfdK : FiniteDimensional ℂ (LinearMap.ker ((cayleyWienerHopf ^ n : L2Real →L[ℂ] L2Real) :
      L2Real →ₗ[ℂ] L2Real)) :=
    Module.rank_lt_aleph0_iff.mp (by rw [hrank]; exact Cardinal.natCast_lt_aleph0)
  have hfdO : FiniteDimensional ℂ Rᗮ := horth ▸ hfdK
  have hfd : FiniteDimensional ℂ (L2Real ⧸ R) :=
    (Submodule.quotientEquivOfIsCompl R Rᗮ (Submodule.isCompl_orthogonal R)).symm.finiteDimensional
  refine ⟨⟨by rw [hker]; infer_instance, hclosed, hfd⟩, ?_⟩
  rw [fredholmIndex, hker, finrank_bot, hq]
  simp

/-! ## Lifts of the powers of the coordinate -/

theorem hankelPlus_circleCoord : hankelPlus circleCoord = 0 := by
  rw [hankelPlus, circleMultiplier_circleCoord, halfProj_cayleyUnitary_one_sub]

theorem hankelMinus_star_circleCoord : hankelMinus (star circleCoord) = 0 := by
  rw [hankelMinus_star, hankelPlus_circleCoord, star_zero]

theorem wienerHopfLift_circleCoord_mul (V : C(UnitCircle, ℂ)) :
    wienerHopfLift (circleCoord * V) = cayleyWienerHopf * wienerHopfLift V := by
  rw [← wienerHopfLift_circleCoord, wienerHopfLift_mul, hankelPlus_circleCoord, zero_mul, sub_zero]

theorem wienerHopfLift_mul_star_circleCoord (V : C(UnitCircle, ℂ)) :
    wienerHopfLift (V * star circleCoord) = wienerHopfLift V * star cayleyWienerHopf := by
  rw [← wienerHopfLift_circleCoord, ← wienerHopfLift_star, wienerHopfLift_mul,
    hankelMinus_star_circleCoord, mul_zero, sub_zero]

theorem wienerHopfLift_circleCoord_pow (n : ℕ) :
    wienerHopfLift (circleCoord ^ n) = cayleyWienerHopf ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, wienerHopfLift_one]
  | succ n ih => rw [pow_succ', wienerHopfLift_circleCoord_mul, ih, pow_succ']

theorem wienerHopfLift_star_circleCoord_pow (n : ℕ) :
    wienerHopfLift (star circleCoord ^ n) = star cayleyWienerHopf ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, wienerHopfLift_one]
  | succ n ih => rw [pow_succ, wienerHopfLift_mul_star_circleCoord, ih, pow_succ]

/-- The integer powers `zⁿ` of the coordinate, `z⁻¹ = z̄` on the circle. -/
def circlePow (n : ℤ) : C(UnitCircle, ℂ) :=
  if 0 ≤ n then circleCoord ^ n.toNat else star circleCoord ^ (-n).toNat

/-- **The analytic Wiener–Hopf index of `zⁿ` is `n`.** -/
theorem fredholmIndex_wienerHopfLift_circlePow (n : ℤ) :
    IsFredholmOp (wienerHopfLift (circlePow n)) ∧ fredholmIndex (wienerHopfLift (circlePow n)) = n := by
  unfold circlePow
  split_ifs with hn
  · rw [wienerHopfLift_circleCoord_pow]
    obtain ⟨hF, hI⟩ := isFredholmOp_cayleyWienerHopf_pow n.toNat
    exact ⟨hF, by rw [hI, Int.toNat_of_nonneg hn]⟩
  · rw [wienerHopfLift_star_circleCoord_pow]
    obtain ⟨hF, hI⟩ := isFredholmOp_star_cayleyWienerHopf_pow (-n).toNat
    exact ⟨hF, by rw [hI, Int.toNat_of_nonneg (by omega)]; ring⟩

/-! ## The winding number of a circle symbol -/

/-- The point `e^{iθ}` of the circle. -/
def circleExp (θ : ℝ) : UnitCircle :=
  ⟨Complex.exp (θ * Complex.I), by
    rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]⟩

theorem continuous_circleExp : Continuous circleExp :=
  Continuous.subtype_mk (by fun_prop) _

theorem circleExp_add_two_pi (θ : ℝ) : circleExp (θ + 2 * Real.pi) = circleExp θ := by
  apply Subtype.ext
  change Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I)
  push_cast
  exact Complex.exp_mul_I_periodic θ

theorem exp_arg_mul_I_of_norm_eq_one {x : ℂ} (hx : ‖x‖ = 1) :
    Complex.exp (Complex.arg x * Complex.I) = x := by
  have h := Complex.norm_mul_exp_arg_mul_I x
  rwa [hx, Complex.ofReal_one, one_mul] at h

theorem norm_coe_unitCircle (z : UnitCircle) : ‖(z : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2

theorem circleExp_arg (z : UnitCircle) : circleExp (Complex.arg z) = z :=
  Subtype.ext (exp_arg_mul_I_of_norm_eq_one (norm_coe_unitCircle z))

theorem exists_int_of_circleExp_eq {θ φ : ℝ} (h : circleExp θ = circleExp φ) :
    ∃ k : ℤ, θ = φ + k * (2 * Real.pi) := by
  have h' : Complex.exp (θ * Complex.I) = Complex.exp (φ * Complex.I) := congrArg Subtype.val h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h'
  refine ⟨k, ?_⟩
  have hk' : ((θ : ℂ) - (φ + k * (2 * Real.pi))) * Complex.I = 0 := by
    rw [sub_mul, hk]
    ring
  have := (mul_eq_zero.mp hk').resolve_right Complex.I_ne_zero
  exact_mod_cast sub_eq_zero.mp this

/-- **Descent of continuity along `θ ↦ e^{iθ}`.**  A function on the circle is continuous as soon as
its pull-back to the line is: near `z₀` the map `z ↦ arg z₀ + arg (z z̄₀)` is a continuous section. -/
theorem continuous_of_continuous_comp_circleExp {X : Type*} [TopologicalSpace X]
    {g : UnitCircle → X} (hg : Continuous (g ∘ circleExp)) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro z₀
  let φ : UnitCircle → ℝ := fun z => Complex.arg (z₀ : ℂ) +
    Complex.arg ((z : ℂ) * (starRingEnd ℂ) (z₀ : ℂ))
  have hz₀ : (z₀ : ℂ) * (starRingEnd ℂ) (z₀ : ℂ) = 1 := by
    rw [Complex.mul_conj', norm_coe_unitCircle]
    norm_num
  have hφ : ∀ z, circleExp (φ z) = z := by
    intro z
    apply Subtype.ext
    change Complex.exp (((Complex.arg (z₀ : ℂ) + Complex.arg ((z : ℂ) * (starRingEnd ℂ) (z₀ : ℂ)) :
      ℝ) : ℂ) * Complex.I) = z
    have hw : ‖(z : ℂ) * (starRingEnd ℂ) (z₀ : ℂ)‖ = 1 := by
      rw [norm_mul, Complex.norm_conj, norm_coe_unitCircle, norm_coe_unitCircle, one_mul]
    rw [Complex.ofReal_add, add_mul, Complex.exp_add,
      exp_arg_mul_I_of_norm_eq_one (norm_coe_unitCircle z₀), exp_arg_mul_I_of_norm_eq_one hw,
      mul_left_comm, hz₀, mul_one]
  have hφc : ContinuousAt φ z₀ := by
    refine continuousAt_const.add ((Complex.continuousAt_arg ?_).comp ?_)
    · rw [hz₀]
      exact Complex.one_mem_slitPlane
    · exact (continuous_subtype_val.mul continuous_const).continuousAt
  have hgφ : g = (g ∘ circleExp) ∘ φ := funext fun z => by simp only [Function.comp, hφ z]
  rw [hgφ]
  exact hg.continuousAt.comp hφc

/-! ## Unimodular symbols and their winding numbers -/

theorem star_mul_self_eq_one_iff (U : C(UnitCircle, ℂ)) : star U * U = 1 ↔ ∀ z, ‖U z‖ = 1 := by
  constructor
  · intro h z
    have hz := congrArg (fun V : C(UnitCircle, ℂ) => V z) h
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.one_apply,
      Complex.star_def] at hz
    rw [mul_comm, Complex.mul_conj'] at hz
    have h2 : ‖U z‖ ^ 2 = 1 := by exact_mod_cast hz
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  · intro h
    ext z
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.one_apply,
      Complex.star_def]
    rw [mul_comm, Complex.mul_conj', h z]
    norm_num

/-- The winding number of a symbol around the circle, along `θ ↦ e^{iθ}`, `0 ≤ θ ≤ 2π`. -/
def circleWinding (U : C(UnitCircle, ℂ)) : ℤ :=
  RHTower.windingNumber (fun θ => U (circleExp θ)) 0 (2 * Real.pi)

theorem isLoop_circleSymbol {U : C(UnitCircle, ℂ)} (hU : ∀ z, U z ≠ 0) :
    RHTower.IsLoop (fun θ => U (circleExp θ)) 0 (2 * Real.pi) where
  continuous := U.continuous.comp continuous_circleExp
  nonzero θ := hU _
  closed := by
    rw [← circleExp_add_two_pi 0, zero_add]

theorem circlePow_circleExp (n : ℤ) (θ : ℝ) :
    circlePow n (circleExp θ) = Complex.exp (n * θ * Complex.I) := by
  unfold circlePow
  split_ifs with hn
  · rw [ContinuousMap.coe_pow, Pi.pow_apply]
    change Complex.exp (θ * Complex.I) ^ n.toNat = _
    rw [← Complex.exp_nat_mul]
    congr 1
    have : ((n.toNat : ℕ) : ℂ) = (n : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hn
    rw [this]
    ring
  · rw [ContinuousMap.coe_pow, Pi.pow_apply]
    change (starRingEnd ℂ) (Complex.exp (θ * Complex.I)) ^ (-n).toNat = _
    rw [← Complex.exp_conj, ← Complex.exp_nat_mul]
    congr 1
    have : (((-n).toNat : ℕ) : ℂ) = -(n : ℂ) := by
      have := Int.toNat_of_nonneg (show 0 ≤ -n by omega)
      exact_mod_cast this
    rw [this, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring

theorem norm_circlePow_apply (n : ℤ) (z : UnitCircle) : ‖circlePow n z‖ = 1 := by
  rw [← circleExp_arg z, circlePow_circleExp, show (n : ℂ) * (Complex.arg z : ℝ) * Complex.I =
    ((n * Complex.arg z : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]

/-- **Logarithm of a unimodular symbol.**  A unimodular symbol of winding number `n` is
`zⁿ e^{g}` with `g` continuous and purely imaginary on the circle. -/
theorem exists_log_of_unimodular {U : C(UnitCircle, ℂ)} (hU : ∀ z, ‖U z‖ = 1) :
    ∃ g : C(UnitCircle, ℂ), (∀ z, (g z).re = 0) ∧
      ∀ z, U z = circlePow (circleWinding U) z * Complex.exp (g z) := by
  have hU0 : ∀ z, U z ≠ 0 := fun z h => by simpa [h] using hU z
  set n := circleWinding U
  set γ : ℝ → ℂ := fun θ => U (circleExp θ)
  have hloop := isLoop_circleSymbol hU0
  obtain ⟨hLc, hLe⟩ := RHTower.contLog_spec hloop.continuous hloop.nonzero
  set L := RHTower.contLog γ
  have hγper : ∀ θ, γ (θ + 2 * Real.pi) = γ θ := fun θ => by
    simp only [γ, circleExp_add_two_pi]
  -- the shifted logarithm has the same increments
  have hshift : ∀ θ, L (θ + 2 * Real.pi) - L θ = n * (2 * Real.pi * Complex.I) := by
    intro θ
    have hind := RHTower.contLog_increment_indep (L := L) (L' := fun t => L (t + 2 * Real.pi))
      hLc (hLc.comp (continuous_id.add continuous_const))
      (fun t => by simp only [hLe, circleExp_add_two_pi]) 0 θ
    have hinc : L (2 * Real.pi) - L 0 = n * (2 * Real.pi * Complex.I) :=
      RHTower.contLog_increment hloop hLc hLe
    simp only [zero_add] at hind
    linear_combination hinc - hind
  set M : ℝ → ℂ := fun θ => L θ - n * θ * Complex.I
  have hMc : Continuous M := hLc.sub (by fun_prop)
  have hMper : Function.Periodic M (2 * Real.pi) := by
    intro θ
    simp only [M]
    have := hshift θ
    push_cast
    linear_combination this
  have hMre : ∀ θ, (M θ).re = 0 := by
    intro θ
    have h1 : ‖Complex.exp (L θ)‖ = 1 := by rw [hLe]; exact hU _
    rw [Complex.norm_exp, Real.exp_eq_one_iff] at h1
    simp [M, h1]
  have hMarg : ∀ θ, M (Complex.arg (circleExp θ : ℂ)) = M θ := by
    intro θ
    obtain ⟨k, hk⟩ := exists_int_of_circleExp_eq (circleExp_arg (circleExp θ))
    rw [hk]
    exact (hMper.int_mul k) θ
  let g : C(UnitCircle, ℂ) := ⟨fun z => M (Complex.arg z), by
    apply continuous_of_continuous_comp_circleExp
    have : (fun z : UnitCircle => M (Complex.arg z)) ∘ circleExp = M := funext hMarg
    rw [this]
    exact hMc⟩
  refine ⟨g, fun z => hMre _, fun z => ?_⟩
  change U z = circlePow n z * Complex.exp (M (Complex.arg z))
  conv_lhs => rw [← circleExp_arg z]
  rw [← hLe, ← circleExp_arg z, hMarg, circlePow_circleExp, circleExp_arg z, ← Complex.exp_add]
  congr 1
  simp only [M]
  ring

/-! ## The index theorem -/

/-- **Homotopy invariance of the index.** -/
theorem fredholmIndex_eq_of_continuous {P : ℝ → L2Real →L[ℂ] L2Real} (hP : Continuous P)
    (hF : ∀ t, IsFredholmOp (P t)) (a b : ℝ) : fredholmIndex (P a) = fredholmIndex (P b) := by
  have hloc : IsLocallyConstant (fun t => fredholmIndex (P t)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    obtain ⟨δ, hδ, hstab⟩ := (hF t₀).exists_stable
    have hev : ∀ᶠ t in nhds t₀, ‖P t - P t₀‖ < δ :=
      ((Metric.tendsto_nhds.mp (hP.tendsto t₀)) δ hδ).mono fun t ht => by
        rwa [dist_eq_norm] at ht
    filter_upwards [hev] with t ht
    have h := (hstab _ ht).2
    rwa [add_sub_cancel] at h
  exact hloc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ a) (Set.mem_univ b)

/-- The straight-line homotopy `zⁿ e^{σ g}` in the exponent. -/
def unimodularHomotopy (n : ℤ) (g : C(UnitCircle, ℂ)) : C(ℝ × UnitCircle, ℂ) :=
  ⟨fun p => circlePow n p.2 * Complex.exp (p.1 * g p.2), by fun_prop⟩

/-- **The Wiener–Hopf index theorem.**  For every continuous unimodular symbol `U` on the circle,
the Wiener–Hopf lift `P₊ C_U P₊ + (1 - P₊)` is Fredholm and its index is the winding number of `U`. -/
theorem fredholmIndex_wienerHopfLift_eq_circleWinding {U : C(UnitCircle, ℂ)}
    (hU : star U * U = 1) :
    IsFredholmOp (wienerHopfLift U) ∧ fredholmIndex (wienerHopfLift U) = circleWinding U := by
  refine ⟨isFredholmOp_wienerHopfLift hU, ?_⟩
  have hU' := (star_mul_self_eq_one_iff U).mp hU
  obtain ⟨g, hgre, hUg⟩ := exists_log_of_unimodular hU'
  set n := circleWinding U
  set H := (unimodularHomotopy n g).curry
  have hunit : ∀ σ : ℝ, star (H σ) * H σ = 1 := by
    intro σ
    rw [star_mul_self_eq_one_iff]
    intro z
    change ‖circlePow n z * Complex.exp (σ * g z)‖ = 1
    rw [norm_mul, norm_circlePow_apply, Complex.norm_exp, one_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, hgre, mul_zero, zero_mul, sub_zero, Real.exp_zero]
  have h0 : H 0 = circlePow n := by
    ext z
    change circlePow n z * Complex.exp (((0 : ℝ) : ℂ) * g z) = _
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  have h1 : H 1 = U := by
    ext z
    change circlePow n z * Complex.exp (((1 : ℝ) : ℂ) * g z) = _
    rw [Complex.ofReal_one, one_mul, hUg z]
  have hpath := fredholmIndex_eq_of_continuous (P := fun σ => wienerHopfLift (H σ))
    (continuous_wienerHopfLift.comp H.continuous) (fun σ => isFredholmOp_wienerHopfLift (hunit σ))
    1 0
  simp only [h0, h1] at hpath
  rw [hpath]
  exact (fredholmIndex_wienerHopfLift_circlePow n).2

end GaloisForLFunctions.HTGeometry
