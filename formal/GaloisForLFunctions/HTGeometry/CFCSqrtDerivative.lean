import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import GaloisForLFunctions.HTGeometry.OperatorLyapunovEquation

/-!
# Fréchet differentiability of the continuous functional calculus square root

`CFC.sqrt` is only well behaved on self-adjoint elements — off the self-adjoint part of a
C⋆-algebra it is identically zero — so it is not differentiable as a map on the whole algebra.
The fix used here avoids passing to the subtype `selfAdjoint A`: twist by the self-adjoint
projection `P x = (x + x⋆)/2`, setting

`saSquare y = (P y) (P y) + (y - P y)`,   `saSqrt x = √(P x) + (x - P x)`.

Then `saSquare ∘ saSqrt = id` on a neighbourhood of any strictly positive `a`, `saSquare` is a
polynomial map with strict derivative `Λ_{P y} ∘ P + (1 - P)`, and that derivative is invertible
exactly when the Lyapunov operator `Λ_{P y}` is — which `isUnit_lyapunov_of_isStrictlyPositive`
supplies.  The inverse function theorem then gives strict differentiability of `saSqrt`, and hence
the derivative of `CFC.sqrt` along self-adjoint directions: `D√(a)(h)` is the unique solution `y`
of the Lyapunov equation `√a · y + y · √a = h`.
-/

open scoped NNReal Ring

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ### The self-adjoint projection -/

/-- The real-linear projection `x ↦ (x + x⋆)/2` onto the self-adjoint part. -/
noncomputable def saProj : A →L[ℝ] A :=
  (2 : ℝ)⁻¹ • (ContinuousLinearMap.id ℝ A + ((starL ℝ : A ≃L⋆[ℝ] A) : A →L[ℝ] A))

omit [PartialOrder A] [StarOrderedRing A] in
lemma saProj_apply (x : A) : saProj x = (2 : ℝ)⁻¹ • (x + star x) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma isSelfAdjoint_saProj (x : A) : IsSelfAdjoint (saProj x) := by
  show star ((2 : ℝ)⁻¹ • (x + star x)) = (2 : ℝ)⁻¹ • (x + star x)
  rw [star_smul, star_add, star_star, star_trivial, add_comm]

omit [PartialOrder A] [StarOrderedRing A] in
lemma saProj_of_isSelfAdjoint {x : A} (hx : IsSelfAdjoint x) : saProj x = x := by
  show (2 : ℝ)⁻¹ • (x + star x) = x
  rw [hx.star_eq, ← two_smul ℝ x, smul_smul]
  norm_num

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma saProj_saProj (x : A) : saProj (saProj x) = saProj x :=
  saProj_of_isSelfAdjoint (isSelfAdjoint_saProj x)

omit [PartialOrder A] [StarOrderedRing A] in
lemma saProj_mul_saProj : (saProj : A →L[ℝ] A) * saProj = saProj := by
  ext x; exact saProj_saProj x

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_saProj_le (x : A) : ‖saProj x‖ ≤ ‖x‖ := by
  rw [saProj_apply, norm_smul, Real.norm_eq_abs]
  have h : ‖x + star x‖ ≤ 2 * ‖x‖ := by
    calc ‖x + star x‖ ≤ ‖x‖ + ‖star x‖ := norm_add_le _ _
      _ = 2 * ‖x‖ := by rw [norm_star]; ring
  calc |(2 : ℝ)⁻¹| * ‖x + star x‖ = (2 : ℝ)⁻¹ * ‖x + star x‖ := by norm_num
    _ ≤ (2 : ℝ)⁻¹ * (2 * ‖x‖) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = ‖x‖ := by ring

omit [PartialOrder A] [StarOrderedRing A] in
/-- The Lyapunov operator of a self-adjoint element commutes with the self-adjoint projection. -/
lemma commute_lyapunov_saProj {x : A} (hx : IsSelfAdjoint x) :
    (lyapunov x) * (saProj : A →L[ℝ] A) = (saProj : A →L[ℝ] A) * lyapunov x := by
  ext h
  show x * (saProj h) + (saProj h) * x = saProj (x * h + h * x)
  rw [saProj_apply, saProj_apply, star_add, star_mul, star_mul, hx.star_eq]
  simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul]
  module

/-! ### The twisted squaring map and its local inverse -/

/-- The twisted squaring map `y ↦ (P y)(P y) + (y - P y)`. -/
def saSquare (y : A) : A := (saProj y) * (saProj y) + (y - saProj y)

/-- The twisted square root `x ↦ √(P x) + (x - P x)`. -/
def saSqrt (x : A) : A := CFC.sqrt (saProj x) + (x - saProj x)

lemma saProj_saSqrt (x : A) : saProj (saSqrt x) = CFC.sqrt (saProj x) := by
  unfold saSqrt
  rw [map_add, map_sub, saProj_saProj,
    saProj_of_isSelfAdjoint (CFC.sqrt_nonneg (saProj x)).isSelfAdjoint, sub_self, add_zero]

lemma saSquare_saSqrt {x : A} (hx : 0 ≤ saProj x) : saSquare (saSqrt x) = x := by
  unfold saSquare
  rw [saProj_saSqrt, CFC.sqrt_mul_sqrt_self _ hx]
  unfold saSqrt
  abel

lemma saSqrt_of_isSelfAdjoint {x : A} (hx : IsSelfAdjoint x) : saSqrt x = CFC.sqrt x := by
  unfold saSqrt
  rw [saProj_of_isSelfAdjoint hx, sub_self, add_zero]

/-! ### The derivative of the twisted square -/

omit [PartialOrder A] [StarOrderedRing A] in
lemma hasStrictFDerivAt_saSquare (y : A) :
    HasStrictFDerivAt (saSquare : A → A)
      ((lyapunov (saProj y)).comp (saProj : A →L[ℝ] A)
        + ((1 : A →L[ℝ] A) - saProj)) y := by
  have h1 : HasStrictFDerivAt (fun z : A => (saProj z) * (saProj z))
      ((lyapunov (saProj y)).comp (saProj : A →L[ℝ] A)) y := by
    have h := HasStrictFDerivAt.mul' (𝕜 := ℝ) (saProj.hasStrictFDerivAt (x := y))
      (saProj.hasStrictFDerivAt (x := y))
    refine h.congr_fderiv ?_
    ext h'
    simp [lyapunov_apply]
  have h2 : HasStrictFDerivAt (fun z : A => z - saProj z)
      ((1 : A →L[ℝ] A) - saProj) y :=
    ((1 : A →L[ℝ] A) - saProj).hasStrictFDerivAt
  exact h1.add h2

/-- If a unit commutes with an element, so does its inverse. -/
lemma Units.val_inv_commute {R : Type*} [Ring R] (u : Rˣ) {P : R}
    (h : (↑u : R) * P = P * (↑u : R)) : (↑u⁻¹ : R) * P = P * (↑u⁻¹ : R) := by
  calc (↑u⁻¹ : R) * P = (↑u⁻¹ : R) * P * ((↑u : R) * (↑u⁻¹ : R)) := by rw [u.mul_inv, mul_one]
    _ = (↑u⁻¹ : R) * (P * (↑u : R)) * (↑u⁻¹ : R) := by noncomm_ring
    _ = (↑u⁻¹ : R) * ((↑u : R) * P) * (↑u⁻¹ : R) := by rw [← h]
    _ = (↑u⁻¹ : R) * (↑u : R) * P * (↑u⁻¹ : R) := by noncomm_ring
    _ = P * (↑u⁻¹ : R) := by rw [u.inv_mul, one_mul]

/-- In any ring, if `P` is idempotent and commutes with a unit `L`, then `L P + (1 - P)` is a
unit. -/
lemma isUnit_mul_idem_add_compl {R : Type*} [Ring R] {L P : R} (hPP : P * P = P)
    (hLP : L * P = P * L) (hu : IsUnit L) : IsUnit (L * P + (1 - P)) := by
  obtain ⟨u, rfl⟩ := hu
  have hLM : (↑u : R) * (↑u⁻¹ : R) = 1 := u.mul_inv
  have hML : (↑u⁻¹ : R) * (↑u : R) = 1 := u.inv_mul
  have hMP : (↑u⁻¹ : R) * P = P * (↑u⁻¹ : R) := Units.val_inv_commute u hLP
  have hcompl : ∀ N : R, N * P = P * N → (1 - P) * N * P = 0 := by
    intro N hN
    have hstep : (1 - P) * N * P = N * P - P * N * P := by noncomm_ring
    rw [hstep, ← hN, show N * P * P = N * (P * P) by noncomm_ring, hPP, sub_self]
  have hPcompl : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPP, sub_self]
  have hsq : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, mul_sub, mul_sub, mul_one, one_mul, mul_one, hPP]; abel
  refine ⟨⟨(↑u : R) * P + (1 - P), (↑u⁻¹ : R) * P + (1 - P), ?_, ?_⟩, rfl⟩
  · calc ((↑u : R) * P + (1 - P)) * ((↑u⁻¹ : R) * P + (1 - P))
        = (↑u : R) * (P * (↑u⁻¹ : R)) * P + (↑u : R) * (P * (1 - P))
          + (1 - P) * (↑u⁻¹ : R) * P + (1 - P) * (1 - P) := by noncomm_ring
      _ = (↑u : R) * ((↑u⁻¹ : R) * P) * P + (↑u : R) * 0 + 0 + (1 - P) := by
          rw [← hMP, hPcompl, hcompl _ hMP, hsq]
      _ = ((↑u : R) * (↑u⁻¹ : R)) * (P * P) + 0 + 0 + (1 - P) := by noncomm_ring
      _ = 1 := by rw [hLM, hPP, one_mul]; abel
  · calc ((↑u⁻¹ : R) * P + (1 - P)) * ((↑u : R) * P + (1 - P))
        = (↑u⁻¹ : R) * (P * (↑u : R)) * P + (↑u⁻¹ : R) * (P * (1 - P))
          + (1 - P) * (↑u : R) * P + (1 - P) * (1 - P) := by noncomm_ring
      _ = (↑u⁻¹ : R) * ((↑u : R) * P) * P + (↑u⁻¹ : R) * 0 + 0 + (1 - P) := by
          rw [← hLP, hPcompl, hcompl _ hLP, hsq]
      _ = ((↑u⁻¹ : R) * (↑u : R)) * (P * P) + 0 + 0 + (1 - P) := by noncomm_ring
      _ = 1 := by rw [hML, hPP, one_mul]; abel

omit [PartialOrder A] [StarOrderedRing A] in
/-- The derivative of the twisted square is invertible whenever the Lyapunov operator is. -/
lemma isUnit_saSquare_fderiv {x : A} (hx : IsSelfAdjoint x) (hu : IsUnit (lyapunov x)) :
    IsUnit ((lyapunov x).comp (saProj : A →L[ℝ] A) + ((1 : A →L[ℝ] A) - saProj)) :=
  isUnit_mul_idem_add_compl saProj_mul_saProj (commute_lyapunov_saProj hx) hu

/-! ### Packaging an invertible operator as a continuous linear equivalence -/

/-- A unit of the ring `E →L[ℝ] E` as a continuous linear equivalence. -/
noncomputable def unitsToEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : (E →L[ℝ] E)ˣ) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse (↑u) (↑u⁻¹)
    (fun x => congrArg (fun S : E →L[ℝ] E => S x) u.inv_mul)
    (fun x => congrArg (fun S : E →L[ℝ] E => S x) u.mul_inv)

@[simp] lemma unitsToEquiv_coe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : (E →L[ℝ] E)ˣ) : ((unitsToEquiv u : E ≃L[ℝ] E) : E →L[ℝ] E) = (↑u : E →L[ℝ] E) := rfl

@[simp] lemma unitsToEquiv_symm_coe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : (E →L[ℝ] E)ˣ) :
    (((unitsToEquiv u : E ≃L[ℝ] E).symm : E ≃L[ℝ] E) : E →L[ℝ] E) = (↑u⁻¹ : E →L[ℝ] E) := rfl

/-! ### The strictly positive neighbourhood -/

/-- Elements close to a strictly positive element have strictly positive self-adjoint part. -/
lemma isStrictlyPositive_saProj_of_norm_lt {a : A} {α : ℝ} (hα : 0 < α)
    (ha : α • (1 : A) ≤ a) {x : A} (hx : ‖x - a‖ < α) :
    IsStrictlyPositive (saProj x) := by
  have hasa : IsSelfAdjoint a := by
    have h0 : (0 : A) ≤ a := le_trans (smul_nonneg hα.le zero_le_one) ha
    exact h0.isSelfAdjoint
  have hdiff : saProj x - a = saProj (x - a) := by
    rw [map_sub, saProj_of_isSelfAdjoint hasa]
  have hn : ‖saProj x - a‖ < α := by
    rw [hdiff]
    exact lt_of_le_of_lt (norm_saProj_le _) hx
  have hsa : IsSelfAdjoint (saProj x - a) := (isSelfAdjoint_saProj x).sub hasa
  have hbound : a - saProj x ≤ ‖saProj x - a‖ • (1 : A) := by
    have h := (hsa.neg).le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one, norm_neg] at h
    simpa using h
  have hlow : (α - ‖saProj x - a‖) • (1 : A) ≤ saProj x := by
    have h1 : α • (1 : A) - ‖saProj x - a‖ • (1 : A) ≤ saProj x := by
      have := sub_le_sub_right ha (‖saProj x - a‖ • (1 : A))
      refine this.trans ?_
      have := sub_le_sub_left hbound (a)
      simpa using this
    rwa [← sub_smul] at h1
  have hpos : (0 : ℝ) < α - ‖saProj x - a‖ := by linarith
  refine (CStarAlgebra.isUnit_of_le _ hlow
    (IsStrictlyPositive.smul hpos isStrictlyPositive_one)).isStrictlyPositive ?_
  exact le_trans (smul_nonneg hpos.le zero_le_one) hlow

/-! ### The local inverse identity in the other direction -/

omit [PartialOrder A] [StarOrderedRing A] in
lemma isSelfAdjoint_mul_self {y : A} (hy : IsSelfAdjoint y) : IsSelfAdjoint (y * y) := by
  show star (y * y) = y * y
  rw [star_mul, hy.star_eq]

omit [PartialOrder A] [StarOrderedRing A] in
lemma saProj_saSquare (y : A) : saProj (saSquare y) = (saProj y) * (saProj y) := by
  unfold saSquare
  rw [map_add, map_sub, saProj_saProj,
    saProj_of_isSelfAdjoint (isSelfAdjoint_mul_self (isSelfAdjoint_saProj y)), sub_self, add_zero]

lemma saSqrt_saSquare {y : A} (hy : 0 ≤ saProj y) : saSqrt (saSquare y) = y := by
  unfold saSqrt
  rw [saProj_saSquare, CFC.sqrt_mul_self _ hy]
  unfold saSquare
  abel

omit [PartialOrder A] [StarOrderedRing A] in
lemma saSquare_of_isSelfAdjoint {y : A} (hy : IsSelfAdjoint y) : saSquare y = y * y := by
  unfold saSquare
  rw [saProj_of_isSelfAdjoint hy, sub_self, add_zero]

/-! ### Strict differentiability of the twisted square root -/

/-- **The twisted square root is strictly differentiable at a strictly positive element**, with
derivative the inverse of `Λ_{√a} ∘ P + (1 - P)`. -/
theorem hasStrictFDerivAt_saSqrt {a : A} (ha : IsStrictlyPositive a) {u : (A →L[ℝ] A)ˣ}
    (hu : (↑u : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt a)).comp (saProj : A →L[ℝ] A) + ((1 : A →L[ℝ] A) - saProj)) :
    HasStrictFDerivAt (saSqrt : A → A) (↑u⁻¹ : A →L[ℝ] A) a := by
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · rw [hasStrictFDerivAt_iff_isLittleO]
    have hz : (fun p : A × A => saSqrt p.1 - saSqrt p.2 - (↑u⁻¹ : A →L[ℝ] A) (p.1 - p.2))
        = fun _ => 0 := by
      funext p; exact Subsingleton.elim _ _
    rw [hz]
    exact Asymptotics.isLittleO_zero _ _
  · have hsqrtsa : IsSelfAdjoint (CFC.sqrt a) := (CFC.sqrt_nonneg a).isSelfAdjoint
    have hsqrtpos : IsStrictlyPositive (CFC.sqrt a) := ha.sqrt a
    obtain ⟨α, hα, hle⟩ := exists_pos_smul_one_le hsqrtpos
    have hf : HasStrictFDerivAt (saSquare : A → A)
        ((unitsToEquiv u : A ≃L[ℝ] A) : A →L[ℝ] A) (CFC.sqrt a) := by
      have hd := hasStrictFDerivAt_saSquare (A := A) (CFC.sqrt a)
      rw [saProj_of_isSelfAdjoint hsqrtsa] at hd
      rwa [unitsToEquiv_coe, hu]
    have hnb : ∀ᶠ y in nhds (CFC.sqrt a), saSqrt (saSquare y) = y := by
      have hball : Metric.ball (CFC.sqrt a) α ⊆ {y : A | saSqrt (saSquare y) = y} := by
        intro y hy
        exact saSqrt_saSquare
          (isStrictlyPositive_saProj_of_norm_lt hα hle
            (by simpa [dist_eq_norm] using hy)).nonneg
      exact Filter.mem_of_superset (Metric.ball_mem_nhds _ hα) hball
    have h2 := hf.to_local_left_inverse hnb
    rw [saSquare_of_isSelfAdjoint hsqrtsa, CFC.sqrt_mul_sqrt_self a ha.nonneg] at h2
    exact h2

/-- The derivative of the twisted square root solves the Lyapunov equation on self-adjoint
directions: `√a · (D√(a) h) + (D√(a) h) · √a = h`. -/
theorem lyapunov_fderiv_saSqrt {a : A} {u : (A →L[ℝ] A)ˣ}
    (hsqrtsa : IsSelfAdjoint (CFC.sqrt a))
    (hu : (↑u : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt a)).comp (saProj : A →L[ℝ] A) + ((1 : A →L[ℝ] A) - saProj))
    {h : A} (hh : IsSelfAdjoint h) :
    lyapunov (CFC.sqrt a) ((↑u⁻¹ : A →L[ℝ] A) h) = h := by
  have hTP : (↑u : A →L[ℝ] A) * (saProj : A →L[ℝ] A)
      = (saProj : A →L[ℝ] A) * (↑u : A →L[ℝ] A) := by
    have hcomp : (lyapunov (CFC.sqrt a)).comp (saProj : A →L[ℝ] A)
        = lyapunov (CFC.sqrt a) * (saProj : A →L[ℝ] A) := rfl
    rw [hu, hcomp]
    have hPP : (saProj : A →L[ℝ] A) * saProj = saProj := saProj_mul_saProj
    have hLP : (lyapunov (CFC.sqrt a)) * (saProj : A →L[ℝ] A)
        = (saProj : A →L[ℝ] A) * lyapunov (CFC.sqrt a) := commute_lyapunov_saProj hsqrtsa
    have e1 : (lyapunov (CFC.sqrt a) * (saProj : A →L[ℝ] A)
        + ((1 : A →L[ℝ] A) - saProj)) * saProj
        = (lyapunov (CFC.sqrt a)) * ((saProj : A →L[ℝ] A) * saProj)
          + (saProj - (saProj : A →L[ℝ] A) * saProj) := by
      rw [add_mul, sub_mul, one_mul, mul_assoc]
    have e2 : (saProj : A →L[ℝ] A) * (lyapunov (CFC.sqrt a) * (saProj : A →L[ℝ] A)
        + ((1 : A →L[ℝ] A) - saProj))
        = ((saProj : A →L[ℝ] A) * lyapunov (CFC.sqrt a)) * saProj
          + (saProj - (saProj : A →L[ℝ] A) * saProj) := by
      rw [mul_add, mul_sub, mul_one, ← mul_assoc]
    rw [e1, e2, hPP, sub_self, ← hLP, mul_assoc, hPP]
  have hMP := Units.val_inv_commute u hTP
  have hPy : saProj ((↑u⁻¹ : A →L[ℝ] A) h) = (↑u⁻¹ : A →L[ℝ] A) h := by
    have hc := congrArg (fun S : A →L[ℝ] A => S h) hMP
    simp only [mul_apply_eq_comp] at hc
    rw [saProj_of_isSelfAdjoint hh] at hc
    exact hc.symm
  have happ : (↑u : A →L[ℝ] A) ((↑u⁻¹ : A →L[ℝ] A) h) = h := by
    have hc := congrArg (fun S : A →L[ℝ] A => S h) u.mul_inv
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using hc
  rw [hu] at happ
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    sub_apply, one_apply_eq_self] at happ
  rwa [hPy, sub_self, add_zero] at happ

end

end GaloisForLFunctions.HTGeometry
