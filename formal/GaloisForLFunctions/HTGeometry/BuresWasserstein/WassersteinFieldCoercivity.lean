import GaloisForLFunctions.HTGeometry.TwistedLyapunovUnit
import GaloisForLFunctions.HTGeometry.HilbertSchmidtLyapunovInverse
import GaloisForLFunctions.HTGeometry.BuresWasserstein.LyapunovFormPositivity
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinFieldDerivative

/-!
# Coercivity of the derivative of the Wasserstein vector field

Kim–Mer–Pálfia (arXiv:2607.29142), Lemma 3.11.  For `A` and `X` in the Loewner interval
`[α, β]` the Hilbert–Schmidt quadratic form of the derivative of `X ↦ 1 - (A # X⁻¹)` is
coercive.  Where the source integrates the semigroup `e^{-t√c}`, here the derivative is read off
as the inverse of the Lyapunov operator `Λ_{√c}`, `c = a^{-1/2} X⁻¹ a^{-1/2}`, and the quadratic
form is computed exactly:

`⟨a^{1/2} y a^{1/2}, Y⟩_HS = ‖v^{-1/2} y v⁻¹‖²_HS + ‖v⁻¹ y v^{-1/2}‖²_HS`,  `v = √c`,

where `y = Λ_v⁻¹(a^{-1/2} X⁻¹ Y X⁻¹ a^{-1/2})`.  Bounding the two Hilbert–Schmidt norms from
below by `‖p‖²_HS / (2β³)` for `p = a^{1/2} Y a^{1/2}` and then `‖p‖²_HS` from below by
`α² ‖Y‖²_HS` yields the constant `α²/(2β³)`, which dominates the constant `α³/(2β⁴)` of the
source on `[α, β]`.
-/

open scoped NNReal Ring BigOperators InnerProductSpace
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

/-- A conjugation by a unit is injective. -/
lemma eq_of_conj_eq {R : Type*} [Ring R] {z A B : R} (hz : IsUnit z)
    (h : z * A * z = z * B * z) : A = B := by
  have key : ∀ w : R, z⁻¹ʳ * (z * w * z) * z⁻¹ʳ = w := fun w => by
    rw [mul_assoc z w z, Ring.inverse_mul_cancel_left z (w * z) hz, mul_assoc,
      Ring.mul_inverse_cancel z hz, mul_one]
  rw [← key A, h, key B]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]

omit [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)] in
/-- The adjoint of a self-adjoint operator is itself. -/
lemma adjoint_eq_self {b : E →L[ℂ] E} (hb : IsSelfAdjoint b) : adjoint b = b := by
  rw [← ContinuousLinearMap.star_eq_adjoint]; exact hb.star_eq

omit [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)] in
/-- **Self-adjoint conjugations are Hilbert–Schmidt self-adjoint.** -/
lemma hsInner_conj_eq {b : E →L[ℂ] E} (hb : IsSelfAdjoint b) {Z T : E →L[ℂ] E}
    (hZ : IsHilbertSchmidt Z) (hT : IsHilbertSchmidt T) :
    hsInner (b * Z * b) T = hsInner Z (b * T * b) := by
  have hadj : adjoint b = b := adjoint_eq_self hb
  calc hsInner (b * Z * b) T = hsInner ((b ∘L Z) ∘L b) T := rfl
    _ = hsInner (b ∘L Z) (T ∘L adjoint b) := hsInner_comp_right (hZ.comp_left b) hT b
    _ = hsInner Z (adjoint b ∘L (T ∘L adjoint b)) := hsInner_comp_left b Z _
    _ = hsInner Z (b * T * b) := by rw [hadj]; rfl

variable {a X Y : E →L[ℂ] E} {α β : ℝ}

/-- The Lyapunov solution occurring in the derivative of `X ↦ a # X⁻¹` is Hilbert–Schmidt. -/
lemma isHilbertSchmidt_gmInvDerivSolution
    (ha : IsStrictlyPositive a) (hX : IsStrictlyPositive X)
    (hY : IsHilbertSchmidt Y) (hYsa : IsSelfAdjoint Y)
    {u : ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ}
    (hu : (↑u : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    IsHilbertSchmidt ((↑u⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ))) := by
  have hNsa : IsSelfAdjoint (a ^ (-(1/2) : ℝ) : E →L[ℂ] E) := isSelfAdjoint_rpow a _
  have hcpos : IsStrictlyPositive (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ) :=
    isStrictlyPositive_conjMap_rpow ha hX.ringInverse
  have hqsa : IsSelfAdjoint (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ)) :=
    isSelfAdjoint_conjMap hNsa (hYsa.conjugate_self hX.ringInverse.isSelfAdjoint)
  have hqHS : IsHilbertSchmidt (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ)) := by
    rw [conjMap_apply']
    exact (((hY.comp_left _).comp_right _).comp_left _).comp_right _
  exact isHilbertSchmidt_of_lyapunov (hcpos.sqrt _) hqHS (lyapunov_twisted_unit_inv hu hqsa)

/-- The derivative of `X ↦ a # X⁻¹` maps Hilbert–Schmidt operators to Hilbert–Schmidt
operators. -/
lemma isHilbertSchmidt_gmInvDeriv
    (ha : IsStrictlyPositive a) (hX : IsStrictlyPositive X)
    (hY : IsHilbertSchmidt Y) (hYsa : IsSelfAdjoint Y)
    {u : ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ}
    (hu : (↑u : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    IsHilbertSchmidt (conjMap (a ^ (1/2 : ℝ))
      ((↑u⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
        (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ)))) := by
  rw [conjMap_apply']
  exact (((isHilbertSchmidt_gmInvDerivSolution ha hX hY hYsa hu).comp_left _).comp_right _)

/-- **Lemma 3.11, one term.**  The Hilbert–Schmidt quadratic form of the derivative of
`X ↦ a # X⁻¹` at `X` is coercive with constant `α²/(2β³)`. -/
theorem re_hsInner_gmInvDeriv_lower
    (hα : 0 < α) (hβ : 0 < β) (ha : IsStrictlyPositive a) (hX : IsStrictlyPositive X)
    (haα : α • (1 : E →L[ℂ] E) ≤ a) (haβ : a ≤ β • (1 : E →L[ℂ] E))
    (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hY : IsHilbertSchmidt Y) (hYsa : IsSelfAdjoint Y)
    {u : ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ}
    (hu : (↑u : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    (α * α / (2 * (β * (β * β)))) * hsNormSq Y
      ≤ RCLike.re (hsInner (conjMap (a ^ (1/2 : ℝ))
          ((↑u⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
            (conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ)))) Y) := by
  have hNsa : IsSelfAdjoint (a ^ (-(1/2) : ℝ) : E →L[ℂ] E) := isSelfAdjoint_rpow a _
  have hPsa : IsSelfAdjoint (a ^ (1/2 : ℝ) : E →L[ℂ] E) := isSelfAdjoint_rpow a _
  have hNP : (a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * a ^ (1/2 : ℝ) = 1 :=
    rpow_neg_half_mul_rpow_half ha
  have hPN : (a ^ (1/2 : ℝ) : E →L[ℂ] E) * a ^ (-(1/2) : ℝ) = 1 :=
    rpow_half_mul_rpow_neg_half ha
  set c : E →L[ℂ] E := conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ with hcdef
  have hcpos : IsStrictlyPositive c := isStrictlyPositive_conjMap_rpow ha hX.ringInverse
  set v : E →L[ℂ] E := CFC.sqrt c with hvdef
  have hvpos : IsStrictlyPositive v := hcpos.sqrt c
  have hvv : v * v = c := CFC.sqrt_mul_sqrt_self c hcpos.nonneg
  set q : E →L[ℂ] E := conjMap (a ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ) with hqdef
  set p : E →L[ℂ] E := conjMap (a ^ (1/2 : ℝ)) Y with hpdef
  have hqsa : IsSelfAdjoint q :=
    isSelfAdjoint_conjMap hNsa (hYsa.conjugate_self hX.ringInverse.isSelfAdjoint)
  have hqHS : IsHilbertSchmidt q := by
    rw [hqdef, conjMap_apply']
    exact (((hY.comp_left _).comp_right _).comp_left _).comp_right _
  have hpHS : IsHilbertSchmidt p := by
    rw [hpdef, conjMap_apply']
    exact (hY.comp_left _).comp_right _
  set y : E →L[ℂ] E := (↑u⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) q with hydef
  have hlyap : v * y + y * v = q := lyapunov_twisted_unit_inv hu hqsa
  have hyHS : IsHilbertSchmidt y := isHilbertSchmidt_of_lyapunov hvpos hqHS hlyap
  -- `q` is the conjugate of `p` by `c`
  have hcpc : c * p * c = q := by
    rw [hcdef, hpdef, hqdef, conjMap_apply', conjMap_apply', conjMap_apply']
    calc ((a ^ (-(1/2) : ℝ)) * X⁻¹ʳ * (a ^ (-(1/2) : ℝ)))
          * ((a ^ (1/2 : ℝ)) * Y * (a ^ (1/2 : ℝ)))
          * ((a ^ (-(1/2) : ℝ)) * X⁻¹ʳ * (a ^ (-(1/2) : ℝ)))
        = (a ^ (-(1/2) : ℝ)) * X⁻¹ʳ
            * (((a ^ (-(1/2) : ℝ)) * (a ^ (1/2 : ℝ))) * Y
              * ((a ^ (1/2 : ℝ)) * (a ^ (-(1/2) : ℝ)))) * X⁻¹ʳ * (a ^ (-(1/2) : ℝ)) := by
          noncomm_ring
      _ = (a ^ (-(1/2) : ℝ)) * (X⁻¹ʳ * Y * X⁻¹ʳ) * (a ^ (-(1/2) : ℝ)) := by
          rw [hNP, hPN, one_mul, mul_one]; noncomm_ring
  -- `p` is the Lyapunov transform of `y`
  have hpeq : p = v⁻¹ʳ * y * (v⁻¹ʳ * v⁻¹ʳ) + (v⁻¹ʳ * v⁻¹ʳ) * y * v⁻¹ʳ := by
    refine (eq_of_conj_eq (z := v * v) (hvv ▸ hcpos.isUnit) ?_).symm
    rw [lyapunov_solution hvpos, hlyap, hvv, hcpc]
  -- the sharp coercivity of the Lyapunov form
  have hXinv : β⁻¹ • (1 : E →L[ℂ] E) ≤ X⁻¹ʳ :=
    smul_one_le_ringInverse_of_le_smul_one hX hβ hXβ
  have hainv : β⁻¹ • (1 : E →L[ℂ] E) ≤ a⁻¹ʳ :=
    smul_one_le_ringInverse_of_le_smul_one ha hβ haβ
  have hcl : (β⁻¹ * β⁻¹) • (1 : E →L[ℂ] E) ≤ c := by
    have h1 : (a ^ (-(1/2) : ℝ)) * (β⁻¹ • (1 : E →L[ℂ] E)) * (a ^ (-(1/2) : ℝ))
        ≤ (a ^ (-(1/2) : ℝ)) * X⁻¹ʳ * (a ^ (-(1/2) : ℝ)) :=
      hNsa.conjugate_le_conjugate hXinv
    have h2 : (a ^ (-(1/2) : ℝ)) * (β⁻¹ • (1 : E →L[ℂ] E)) * (a ^ (-(1/2) : ℝ))
        = β⁻¹ • (a⁻¹ʳ : E →L[ℂ] E) := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one,
        show (a ^ (-(1/2) : ℝ)) * (a ^ (-(1/2) : ℝ)) = (a⁻¹ʳ : E →L[ℂ] E) by
          rw [← CFC.rpow_add ha.isUnit, CFC.inverse_eq_rpow_neg_one ha]; norm_num]
    have h3 : (β⁻¹ * β⁻¹) • (1 : E →L[ℂ] E) ≤ β⁻¹ • (a⁻¹ʳ : E →L[ℂ] E) := by
      rw [mul_smul]
      exact smul_le_smul_of_nonneg_left hainv (inv_pos.mpr hβ).le
    rw [hcdef, conjMap_apply']
    exact h3.trans (h2 ▸ h1)
  have hvlb : β⁻¹ • (1 : E →L[ℂ] E) ≤ v := by
    have hm := CFC.sqrt_le_sqrt _ _ hcl
    rwa [cfcSqrt_smul (by positivity) (zero_le_one (α := E →L[ℂ] E)), CFC.sqrt_one,
      show Real.sqrt (β⁻¹ * β⁻¹) = β⁻¹ from Real.sqrt_mul_self (inv_pos.mpr hβ).le] at hm
  have hsharp : hsNormSq p ≤ (2 * (β * (β * β))) * RCLike.re (hsInner p y) := by
    rw [hpeq]
    exact hsNormSq_le_re_hsInner_lyapunovSolution hvpos hyHS hβ hvlb
  -- the lower bound on `‖p‖²_HS`
  have hsqrta : (Real.sqrt α) • (1 : E →L[ℂ] E) ≤ (a ^ (1/2 : ℝ) : E →L[ℂ] E) := by
    have hm := CFC.sqrt_le_sqrt _ _ haα
    rwa [cfcSqrt_smul hα.le (zero_le_one (α := E →L[ℂ] E)), CFC.sqrt_one,
      CFC.sqrt_eq_rpow] at hm
  have hvecP : ∀ w : E, α * ‖w‖ ^ 2 ≤ ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E) w‖ ^ 2 := fun w => by
    have h := sq_mul_norm_sq_le_norm_apply_sq (Real.sqrt_nonneg α) hsqrta w
    rwa [Real.mul_self_sqrt hα.le] at h
  have hpY : (α * α) * hsNormSq Y ≤ hsNormSq p := by
    have h := le_hsNormSq_sandwich (S := (a ^ (1/2 : ℝ) : E →L[ℂ] E))
      (T := (a ^ (1/2 : ℝ) : E →L[ℂ] E)) hY hα.le hvecP
      (d := α) (by
        intro w
        rw [adjoint_eq_self hPsa]
        exact hvecP w)
    rw [hpdef, conjMap_apply']
    exact h
  -- assemble
  have hDY : RCLike.re (hsInner (conjMap (a ^ (1/2 : ℝ)) y) Y) = RCLike.re (hsInner p y) := by
    have h1 : hsInner ((a ^ (1/2 : ℝ) : E →L[ℂ] E) * y * (a ^ (1/2 : ℝ))) Y
        = hsInner y ((a ^ (1/2 : ℝ) : E →L[ℂ] E) * Y * (a ^ (1/2 : ℝ))) :=
      hsInner_conj_eq hPsa hyHS hY
    have h2 : hsInner y p = starRingEnd ℂ (hsInner p y) := hsInner_conj_symm y p
    rw [conjMap_apply', h1]
    rw [hpdef, conjMap_apply'] at h2 ⊢
    rw [h2]
    simp
  rw [hDY]
  have hden : (0 : ℝ) < 2 * (β * (β * β)) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  calc α * α * hsNormSq Y ≤ hsNormSq p := hpY
    _ ≤ (2 * (β * (β * β))) * RCLike.re (hsInner p y) := hsharp
    _ = RCLike.re (hsInner p y) * (2 * (β * (β * β))) := mul_comm _ _

/-- **Lemma 3.11** (Kim–Mer–Pálfia, arXiv:2607.29142).  For a weighted family in the Loewner
interval `[α, β]` and `X` in the same interval, the Hilbert–Schmidt quadratic form of the
derivative of the Wasserstein vector field is coercive with constant `α²/(2β³)`. -/
theorem re_hsInner_wassFieldDeriv_lower {ι : Type*} {s : Finset ι} {w : ι → ℝ}
    {Av : ι → E →L[ℂ] E}
    (hα : 0 < α) (hβ : 0 < β) (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hX : IsStrictlyPositive X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hY : IsHilbertSchmidt Y) (hYsa : IsSelfAdjoint Y)
    {u : ι → ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ}
    (hu : ∀ i ∈ s, (↑(u i) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    (α * α / (2 * (β * (β * β)))) * hsNormSq Y
      ≤ RCLike.re (hsInner (∑ i ∈ s, w i • (conjMap ((Av i) ^ (1/2 : ℝ))
          ((↑(u i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
            (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ))))) Y) := by
  have hDHS : ∀ i ∈ s, IsHilbertSchmidt (w i • (conjMap ((Av i) ^ (1/2 : ℝ))
      ((↑(u i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
        (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ))))) := fun i hi =>
    IsHilbertSchmidt.real_smul
      (isHilbertSchmidt_gmInvDeriv (hA i hi) hX hY hYsa (hu i hi)) _
  rw [hsInner_sum_left s hDHS hY, map_sum]
  have hterm : ∀ i ∈ s, w i * ((α * α / (2 * (β * (β * β)))) * hsNormSq Y)
      ≤ RCLike.re (hsInner (w i • (conjMap ((Av i) ^ (1/2 : ℝ))
          ((↑(u i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
            (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ))))) Y) := by
    intro i hi
    rw [hsInner_real_smul_left]
    have hre : RCLike.re ((w i : ℂ) * hsInner (conjMap ((Av i) ^ (1/2 : ℝ))
        ((↑(u i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
          (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ)))) Y)
        = w i * RCLike.re (hsInner (conjMap ((Av i) ^ (1/2 : ℝ))
        ((↑(u i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
          (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * Y * X⁻¹ʳ)))) Y) := by
      simp
    rw [hre]
    exact mul_le_mul_of_nonneg_left
      (re_hsInner_gmInvDeriv_lower hα hβ (hA i hi) hX (hAα i hi) (hAβ i hi) hXβ hY hYsa
        (hu i hi)) (hw i hi)
  calc (α * α / (2 * (β * (β * β)))) * hsNormSq Y
      = ∑ i ∈ s, w i * ((α * α / (2 * (β * (β * β)))) * hsNormSq Y) := by
        rw [← Finset.sum_mul, hwsum, one_mul]
    _ ≤ _ := Finset.sum_le_sum hterm

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
