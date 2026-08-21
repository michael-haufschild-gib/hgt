import GaloisForLFunctions.RHTower.SoninEulerCornerConcrete
import GaloisForLFunctions.RHTower.SoninLudersPinching
import GaloisForLFunctions.RHTower.SummableEulerCalkinInjectivity
import GaloisForLFunctions.HTGeometry.ProjectionCornerCommutator
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# The Sonin Euler inverse and polar corners are noncompact

The one-prime positive Euler weight `W_p` on the Sonin model is self-adjoint, strictly positive and
boundedly invertible, and its cross-boundary corner across the Sonin projection is noncompact
(`RHTower.centralPositiveEulerCorner_not_isCompactOperator`).

The abstract corner/commutator calculus of `HTGeometry.ProjectionCornerCommutator` then propagates
that noncompactness to the inverse weight and to both square roots:

```text
(1-Q) W_p Q,   (1-Q) W_p⁻¹ Q,   (1-Q) W_p^{1/2} Q,   (1-Q) W_p^{-1/2} Q
```

are all noncompact.  So neither the Euler cyclic density `W_p⁻¹`, nor either polar square-root
correction, can repair compactness of the Sonin seam.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real continuous functional calculus of the Sonin operator algebra.  Instance search does
not build this by itself for the concrete algebra, so it is supplied here. -/
local instance soninSelfAdjointCFC :
    ContinuousFunctionalCalculus ℝ (SoninL2 →L[ℂ] SoninL2) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-! ## The Sonin projection -/

theorem centralSoninProjection_isSelfAdjoint (a : ℝ) :
    IsSelfAdjoint (centralSoninProjection a) :=
  isSelfAdjoint_starProjection _

theorem centralSoninProjection_mul_self (a : ℝ) :
    centralSoninProjection a * centralSoninProjection a = centralSoninProjection a :=
  Submodule.isIdempotentElem_starProjection _

/-! ## The Euler weight is self-adjoint, positive and invertible -/

theorem positiveEulerDilationOperator_isSelfAdjoint (p : ℝ) (hp : 1 < p) :
    IsSelfAdjoint (positiveEulerDilationOperator p hp) := by
  have hS : IsSelfAdjoint (dilationSum p hp) := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
    exact adjoint_dilationSum_eq_self p hp
  unfold positiveEulerDilationOperator
  rw [IsSelfAdjoint, star_add, star_smul, star_smul, hS.star_eq, star_one]
  congr 2
  · simp
  · simp

/-- The Euler weight differs from a positive multiple of the identity by a small self-adjoint
perturbation. -/
theorem positiveEulerDilationOperator_sub (p : ℝ) (hp : 1 < p) :
    positiveEulerDilationOperator p hp
      = ((1 + p⁻¹ : ℝ) : ℂ) • (1 : SoninL2 →L[ℂ] SoninL2)
        - ((Real.sqrt p : ℂ)⁻¹) • dilationSum p hp := by
  unfold positiveEulerDilationOperator
  rw [neg_smul]
  abel

theorem norm_eulerPerturbation_le (p : ℝ) (hp : 1 < p) :
    ‖((Real.sqrt p : ℂ)⁻¹) • dilationSum p hp‖ ≤ 2 / Real.sqrt p := by
  have hsq : 0 < Real.sqrt p := Real.sqrt_pos.mpr (zero_lt_one.trans hp)
  rw [norm_smul]
  have hc : ‖((Real.sqrt p : ℂ)⁻¹)‖ = (Real.sqrt p)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsq]
  rw [hc]
  calc (Real.sqrt p)⁻¹ * ‖dilationSum p hp‖ ≤ (Real.sqrt p)⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left (norm_dilationSum_le_two p hp) (by positivity)
    _ = 2 / Real.sqrt p := by ring

/-- The strict arithmetic-mean inequality behind invertibility: `√p + 1/√p > 2` for `p ≠ 1`. -/
theorem two_lt_sqrt_add_inv_sqrt (p : ℝ) (hp : 1 < p) :
    2 / Real.sqrt p < 1 + p⁻¹ := by
  have hsq : 0 < Real.sqrt p := Real.sqrt_pos.mpr (zero_lt_one.trans hp)
  have hsqsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (zero_lt_one.trans hp).le
  have hne : Real.sqrt p ≠ 1 := by
    intro h
    rw [h, one_mul] at hsqsq
    linarith
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp
  rw [div_lt_iff₀ hsq]
  have hkey : 0 < (Real.sqrt p - 1) ^ 2 := by
    have : Real.sqrt p - 1 ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have hexp : (1 + p⁻¹) * Real.sqrt p = Real.sqrt p + (Real.sqrt p)⁻¹ := by
    field_simp
    nlinarith [hsqsq]
  rw [hexp]
  have hinv : Real.sqrt p * (Real.sqrt p)⁻¹ = 1 := mul_inv_cancel₀ hsq.ne'
  by_contra hcon
  rw [not_lt] at hcon
  have h2 : Real.sqrt p * (Real.sqrt p + (Real.sqrt p)⁻¹) ≤ Real.sqrt p * 2 :=
    mul_le_mul_of_nonneg_left hcon hsq.le
  rw [mul_add, hinv] at h2
  nlinarith [hkey]


/-! ## Invertibility and positivity of the Euler weight -/

theorem eulerPerturbation_isSelfAdjoint (p : ℝ) (hp : 1 < p) :
    IsSelfAdjoint (((Real.sqrt p : ℂ)⁻¹) • dilationSum p hp) := by
  have hS : IsSelfAdjoint (dilationSum p hp) := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
    exact adjoint_dilationSum_eq_self p hp
  rw [IsSelfAdjoint, star_smul, hS.star_eq]
  congr 1
  simp

theorem smul_one_eq_algebraMap (c : ℝ) :
    ((c : ℝ) : ℂ) • (1 : SoninL2 →L[ℂ] SoninL2)
      = algebraMap ℝ (SoninL2 →L[ℂ] SoninL2) c := by
  rw [Algebra.algebraMap_eq_smul_one, ← algebraMap_smul ℂ c (1 : SoninL2 →L[ℂ] SoninL2)]
  norm_num

theorem isUnit_positiveEulerDilationOperator (p : ℝ) (hp : 1 < p) :
    IsUnit (positiveEulerDilationOperator p hp) := by
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp
  have hcpos : (0 : ℝ) < 1 + p⁻¹ := by positivity
  have hcC : (((1 + p⁻¹ : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hcpos)
  have hTnorm : ‖((Real.sqrt p : ℂ)⁻¹) • dilationSum p hp‖ ≤ 2 / Real.sqrt p :=
    norm_eulerPerturbation_le p hp
  have hkey : 2 / Real.sqrt p < 1 + p⁻¹ := two_lt_sqrt_add_inv_sqrt p hp
  have hlt : ‖(((1 + p⁻¹ : ℝ)) : ℂ)⁻¹ • (((Real.sqrt p : ℂ)⁻¹) • dilationSum p hp)‖ < 1 := by
    have hnorm : ‖(((1 + p⁻¹ : ℝ)) : ℂ)⁻¹ • (((Real.sqrt p : ℂ)⁻¹) • dilationSum p hp)‖
        = (1 + p⁻¹)⁻¹ * ‖((Real.sqrt p : ℂ)⁻¹) • dilationSum p hp‖ := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
    rw [hnorm]
    have h1 : (1 + p⁻¹)⁻¹ * ‖((Real.sqrt p : ℂ)⁻¹) • dilationSum p hp‖
        ≤ (1 + p⁻¹)⁻¹ * (2 / Real.sqrt p) :=
      mul_le_mul_of_nonneg_left hTnorm (by positivity)
    have h2 : (1 + p⁻¹)⁻¹ * (2 / Real.sqrt p) < (1 + p⁻¹)⁻¹ * (1 + p⁻¹) :=
      mul_lt_mul_of_pos_left hkey (by positivity)
    rw [inv_mul_cancel₀ (ne_of_gt hcpos)] at h2
    linarith
  have hfac : positiveEulerDilationOperator p hp
      = (algebraMap ℂ (SoninL2 →L[ℂ] SoninL2) (((1 + p⁻¹ : ℝ)) : ℂ))
        * (1 - (((1 + p⁻¹ : ℝ)) : ℂ)⁻¹ • (((Real.sqrt p : ℂ)⁻¹) • dilationSum p hp)) := by
    rw [positiveEulerDilationOperator_sub, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul, smul_sub, smul_smul, mul_inv_cancel₀ hcC, one_smul]
  rw [hfac]
  exact (IsUnit.map (algebraMap ℂ (SoninL2 →L[ℂ] SoninL2)) (isUnit_iff_ne_zero.mpr hcC)).mul
    (isUnit_one_sub_of_norm_lt_one hlt)


/-! ## The Sonin space is nontrivial -/

/-- The Sonin model is nontrivial: otherwise every operator would be zero, hence compact,
contradicting the noncompact Euler corner. -/
theorem nontrivial_soninL2 : Nontrivial SoninL2 := by
  by_contra hcon
  rw [not_nontrivial_iff_subsingleton] at hcon
  refine centralPositiveEulerCorner_not_isCompactOperator 1 2 one_pos one_lt_two ?_
  haveI : Subsingleton (SoninL2 →L[ℂ] SoninL2) :=
    ⟨fun f g => ContinuousLinearMap.ext fun x => Subsingleton.elim _ _⟩
  have hzero : (crossBoundary (centralSoninProjection 1)
      (positiveEulerDilationOperator 2 one_lt_two) : SoninL2 →L[ℂ] SoninL2) = 0 :=
    Subsingleton.elim _ _
  rw [hzero]
  exact isCompactOperator_zero

/-! ## The spectrum of the Euler weight is strictly positive -/

theorem spectrum_positiveEulerDilationOperator_pos (p : ℝ) (hp : 1 < p) :
    ∀ x ∈ spectrum ℝ (positiveEulerDilationOperator p hp), 0 < x := by
  haveI := nontrivial_soninL2
  intro x hx
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp
  have hcpos : (0 : ℝ) < 1 + p⁻¹ := by positivity
  have hTnorm : ‖((Real.sqrt p : ℂ)⁻¹) • dilationSum p hp‖ ≤ 2 / Real.sqrt p :=
    norm_eulerPerturbation_le p hp
  have hkey : 2 / Real.sqrt p < 1 + p⁻¹ := two_lt_sqrt_add_inv_sqrt p hp
  rw [positiveEulerDilationOperator_sub, smul_one_eq_algebraMap,
    ← spectrum.singleton_sub_eq] at hx
  obtain ⟨u, hu, t, ht, hxut⟩ := Set.mem_sub.mp hx
  rw [Set.mem_singleton_iff] at hu
  subst hu
  have habs : |t| ≤ 2 / Real.sqrt p := by
    have h1 : ‖t‖ ≤ ‖((Real.sqrt p : ℂ)⁻¹) • dilationSum p hp‖ :=
      spectrum.norm_le_norm_of_mem ht
    rw [Real.norm_eq_abs] at h1
    linarith
  have hle : t ≤ 2 / Real.sqrt p := le_trans (le_abs_self t) habs
  rw [← hxut]
  linarith

/-! ## The inverse and the two square roots, as functional calculus of the Euler weight -/

/-- The Euler cyclic density `W_p⁻¹`. -/
def eulerInverseWeight (p : ℝ) (hp : 1 < p) : SoninL2 →L[ℂ] SoninL2 :=
  cfc (fun x : ℝ => x⁻¹) (positiveEulerDilationOperator p hp)

/-- The polar square root `W_p^{1/2}`. -/
def eulerSqrtWeight (p : ℝ) (hp : 1 < p) : SoninL2 →L[ℂ] SoninL2 :=
  cfc Real.sqrt (positiveEulerDilationOperator p hp)

/-- The inverse polar square root `W_p^{-1/2}`. -/
def eulerInverseSqrtWeight (p : ℝ) (hp : 1 < p) : SoninL2 →L[ℂ] SoninL2 :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (positiveEulerDilationOperator p hp)

theorem continuousOn_inv_spectrum (p : ℝ) (hp : 1 < p) :
    ContinuousOn (fun x : ℝ => x⁻¹) (spectrum ℝ (positiveEulerDilationOperator p hp)) := by
  refine ContinuousOn.inv₀ continuousOn_id fun x hx => ?_
  exact ne_of_gt (spectrum_positiveEulerDilationOperator_pos p hp x hx)

theorem continuousOn_invSqrt_spectrum (p : ℝ) (hp : 1 < p) :
    ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹)
      (spectrum ℝ (positiveEulerDilationOperator p hp)) := by
  refine ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) fun x hx => ?_
  exact ne_of_gt (Real.sqrt_pos.mpr (spectrum_positiveEulerDilationOperator_pos p hp x hx))

theorem eulerSqrtWeight_mul_self (p : ℝ) (hp : 1 < p) :
    eulerSqrtWeight p hp * eulerSqrtWeight p hp = positiveEulerDilationOperator p hp := by
  have hsa := positiveEulerDilationOperator_isSelfAdjoint p hp
  rw [eulerSqrtWeight, ← cfc_mul (R := ℝ) Real.sqrt Real.sqrt
    (positiveEulerDilationOperator p hp)
    (Real.continuous_sqrt.continuousOn) (Real.continuous_sqrt.continuousOn)]
  rw [cfc_congr (f := fun x : ℝ => Real.sqrt x * Real.sqrt x) (g := fun x : ℝ => x)
    (a := positiveEulerDilationOperator p hp) fun x hx => ?_]
  · exact cfc_id' ℝ (positiveEulerDilationOperator p hp)
  · exact Real.mul_self_sqrt (spectrum_positiveEulerDilationOperator_pos p hp x hx).le

theorem eulerInverseWeight_mul (p : ℝ) (hp : 1 < p) :
    eulerInverseWeight p hp * positiveEulerDilationOperator p hp = 1 := by
  have hsa := positiveEulerDilationOperator_isSelfAdjoint p hp
  have hid : positiveEulerDilationOperator p hp
      = cfc (fun x : ℝ => x) (positiveEulerDilationOperator p hp) :=
    (cfc_id' ℝ (positiveEulerDilationOperator p hp)).symm
  rw [eulerInverseWeight]
  nth_rewrite 2 [hid]
  rw [← cfc_mul (R := ℝ) (fun x : ℝ => x⁻¹) (fun x : ℝ => x)
    (positiveEulerDilationOperator p hp) (continuousOn_inv_spectrum p hp) continuousOn_id]
  rw [cfc_congr (f := fun x : ℝ => x⁻¹ * x) (g := fun _ : ℝ => (1 : ℝ))
    (a := positiveEulerDilationOperator p hp) fun x hx => ?_]
  · exact cfc_const_one ℝ (positiveEulerDilationOperator p hp)
  · exact inv_mul_cancel₀ (ne_of_gt (spectrum_positiveEulerDilationOperator_pos p hp x hx))

theorem eulerInverseSqrtWeight_mul_self (p : ℝ) (hp : 1 < p) :
    eulerInverseSqrtWeight p hp * eulerInverseSqrtWeight p hp = eulerInverseWeight p hp := by
  have hsa := positiveEulerDilationOperator_isSelfAdjoint p hp
  rw [eulerInverseSqrtWeight, ← cfc_mul (R := ℝ) (fun x : ℝ => (Real.sqrt x)⁻¹)
    (fun x : ℝ => (Real.sqrt x)⁻¹) (positiveEulerDilationOperator p hp)
    (continuousOn_invSqrt_spectrum p hp) (continuousOn_invSqrt_spectrum p hp)]
  rw [eulerInverseWeight]
  refine cfc_congr fun x hx => ?_
  have hxpos := spectrum_positiveEulerDilationOperator_pos p hp x hx
  rw [← mul_inv, Real.mul_self_sqrt hxpos.le]

theorem eulerInverseWeight_isSelfAdjoint (p : ℝ) (hp : 1 < p) :
    IsSelfAdjoint (eulerInverseWeight p hp) := by
  have hsa := positiveEulerDilationOperator_isSelfAdjoint p hp
  exact cfc_predicate (R := ℝ) (fun x : ℝ => x⁻¹) (positiveEulerDilationOperator p hp)

theorem eulerSqrtWeight_isSelfAdjoint (p : ℝ) (hp : 1 < p) :
    IsSelfAdjoint (eulerSqrtWeight p hp) := by
  have hsa := positiveEulerDilationOperator_isSelfAdjoint p hp
  exact cfc_predicate (R := ℝ) Real.sqrt (positiveEulerDilationOperator p hp)

theorem eulerInverseSqrtWeight_isSelfAdjoint (p : ℝ) (hp : 1 < p) :
    IsSelfAdjoint (eulerInverseSqrtWeight p hp) := by
  have hsa := positiveEulerDilationOperator_isSelfAdjoint p hp
  exact cfc_predicate (R := ℝ) (fun x : ℝ => (Real.sqrt x)⁻¹)
    (positiveEulerDilationOperator p hp)


theorem positiveEulerDilationOperator_mul_inverse (p : ℝ) (hp : 1 < p) :
    positiveEulerDilationOperator p hp * eulerInverseWeight p hp = 1 := by
  have hsa := positiveEulerDilationOperator_isSelfAdjoint p hp
  have hid : positiveEulerDilationOperator p hp
      = cfc (fun x : ℝ => x) (positiveEulerDilationOperator p hp) :=
    (cfc_id' ℝ (positiveEulerDilationOperator p hp)).symm
  rw [eulerInverseWeight]
  nth_rewrite 1 [hid]
  rw [← cfc_mul (R := ℝ) (fun x : ℝ => x) (fun x : ℝ => x⁻¹)
    (positiveEulerDilationOperator p hp) continuousOn_id (continuousOn_inv_spectrum p hp)]
  rw [cfc_congr (f := fun x : ℝ => x * x⁻¹) (g := fun _ : ℝ => (1 : ℝ))
    (a := positiveEulerDilationOperator p hp) fun x hx => ?_]
  · exact cfc_const_one ℝ (positiveEulerDilationOperator p hp)
  · exact mul_inv_cancel₀ (ne_of_gt (spectrum_positiveEulerDilationOperator_pos p hp x hx))

/-! ## The four noncompact corners -/

theorem crossCorner_eq_crossBoundary (Q A : SoninL2 →L[ℂ] SoninL2) :
    crossCorner Q A = crossBoundary Q A := rfl

/-- The forward Euler metric corner is noncompact (the parent theorem, in corner notation). -/
theorem not_isCompactOperator_eulerCorner (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ¬ IsCompactOperator
      (crossCorner (centralSoninProjection a) (positiveEulerDilationOperator p hp)) :=
  centralPositiveEulerCorner_not_isCompactOperator a p ha hp

/-- **Every self-adjoint inverse of the Euler metric has a noncompact corner.** -/
theorem not_isCompactOperator_corner_of_inverse (a p : ℝ) (ha : 0 < a) (hp : 1 < p)
    {B : SoninL2 →L[ℂ] SoninL2} (hBsa : IsSelfAdjoint B)
    (hAB : positiveEulerDilationOperator p hp * B = 1)
    (hBA : B * positiveEulerDilationOperator p hp = 1) :
    ¬ IsCompactOperator (crossCorner (centralSoninProjection a) B) :=
  not_isCompactOperator_crossCorner_inv (centralSoninProjection_mul_self a)
    (centralSoninProjection_isSelfAdjoint a) hBsa hAB hBA
    (not_isCompactOperator_eulerCorner a p ha hp)

/-- **The Euler cyclic-density corner is noncompact.** -/
theorem not_isCompactOperator_eulerInverseCorner (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ¬ IsCompactOperator (crossCorner (centralSoninProjection a) (eulerInverseWeight p hp)) :=
  not_isCompactOperator_corner_of_inverse a p ha hp (eulerInverseWeight_isSelfAdjoint p hp)
    (positiveEulerDilationOperator_mul_inverse p hp) (eulerInverseWeight_mul p hp)

/-- **Every self-adjoint square root of the Euler metric has a noncompact corner.** -/
theorem not_isCompactOperator_corner_of_sqrt (a p : ℝ) (ha : 0 < a) (hp : 1 < p)
    {C : SoninL2 →L[ℂ] SoninL2} (hCsa : IsSelfAdjoint C)
    (hC : C * C = positiveEulerDilationOperator p hp) :
    ¬ IsCompactOperator (crossCorner (centralSoninProjection a) C) := by
  refine not_isCompactOperator_crossCorner_sqrt (centralSoninProjection_mul_self a)
    (centralSoninProjection_isSelfAdjoint a) hCsa ?_
  rw [hC]
  exact not_isCompactOperator_eulerCorner a p ha hp

/-- **The polar square-root corner is noncompact.** -/
theorem not_isCompactOperator_eulerSqrtCorner (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ¬ IsCompactOperator (crossCorner (centralSoninProjection a) (eulerSqrtWeight p hp)) :=
  not_isCompactOperator_corner_of_sqrt a p ha hp (eulerSqrtWeight_isSelfAdjoint p hp)
    (eulerSqrtWeight_mul_self p hp)

/-- **Every self-adjoint square root of the Euler cyclic density has a noncompact corner.** -/
theorem not_isCompactOperator_corner_of_inverseSqrt (a p : ℝ) (ha : 0 < a) (hp : 1 < p)
    {C : SoninL2 →L[ℂ] SoninL2} (hCsa : IsSelfAdjoint C)
    (hC : C * C = eulerInverseWeight p hp) :
    ¬ IsCompactOperator (crossCorner (centralSoninProjection a) C) := by
  refine not_isCompactOperator_crossCorner_sqrt (centralSoninProjection_mul_self a)
    (centralSoninProjection_isSelfAdjoint a) hCsa ?_
  rw [hC]
  exact not_isCompactOperator_eulerInverseCorner a p ha hp

/-- **The inverse polar square-root corner is noncompact.** -/
theorem not_isCompactOperator_eulerInverseSqrtCorner (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ¬ IsCompactOperator
      (crossCorner (centralSoninProjection a) (eulerInverseSqrtWeight p hp)) :=
  not_isCompactOperator_corner_of_inverseSqrt a p ha hp
    (eulerInverseSqrtWeight_isSelfAdjoint p hp) (eulerInverseSqrtWeight_mul_self p hp)

/-! ## The polar-unitary corner

If `θ` is a bounded isomorphism carrying the Sonin space at `a` onto a second Sonin space with
projection `P`, then the corner of the polar unitary `θ W_p^{-1/2}` across the pair `(P, Q_a)` is
again noncompact:  the canonical Sonin identification cannot be unitarized modulo compacts. -/

/-- **The polar-unitary corner is noncompact.**  No property of `θ` beyond bounded invertibility
and the two range identities is used. -/
theorem not_isCompactOperator_polarCorner (a p : ℝ) (ha : 0 < a) (hp : 1 < p)
    {P θ θ' : SoninL2 →L[ℂ] SoninL2}
    (hθQ : P * (θ * centralSoninProjection a) = θ * centralSoninProjection a)
    (hθ'P : centralSoninProjection a * (θ' * P) = θ' * P)
    (hinv : θ' * θ = 1) :
    ¬ IsCompactOperator
      (mixedCorner P (centralSoninProjection a) (θ * eulerInverseSqrtWeight p hp)) := by
  rw [isCompactOperator_mixedCorner_iff hθQ hθ'P hinv]
  exact not_isCompactOperator_eulerInverseSqrtCorner a p ha hp

/-- The same conclusion for the forward polar correction `θ W_p^{1/2}`. -/
theorem not_isCompactOperator_polarSqrtCorner (a p : ℝ) (ha : 0 < a) (hp : 1 < p)
    {P θ θ' : SoninL2 →L[ℂ] SoninL2}
    (hθQ : P * (θ * centralSoninProjection a) = θ * centralSoninProjection a)
    (hθ'P : centralSoninProjection a * (θ' * P) = θ' * P)
    (hinv : θ' * θ = 1) :
    ¬ IsCompactOperator
      (mixedCorner P (centralSoninProjection a) (θ * eulerSqrtWeight p hp)) := by
  rw [isCompactOperator_mixedCorner_iff hθQ hθ'P hinv]
  exact not_isCompactOperator_eulerSqrtCorner a p ha hp

end

end RHTower




