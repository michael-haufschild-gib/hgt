import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinDerivLipschitz

/-!
# The second-order estimate for the Wasserstein vector field

The increment of `X ↦ a # X⁻¹` and its linearisation at `Y` are *both* Sylvester solutions with
the same first coefficient `X' = a^{-1/2}(a # Y⁻¹)a^{-1/2}`: the increment has second coefficient
`a^{-1/2}(a # X⁻¹)a^{-1/2}` and right-hand side `a^{-1/2}(Y⁻¹ - X⁻¹)a^{-1/2}`, the linearisation
has second coefficient `X'` again and right-hand side `a^{-1/2}Y⁻¹(X-Y)Y⁻¹a^{-1/2}`.  The
Sylvester perturbation bound therefore gives the quadratic estimate

`‖(a # Y⁻¹ - a # X⁻¹) - DΦ(Y)(X - Y)‖_HS ≤ C ‖X - Y‖ ‖X - Y‖_HS`

with no Taylor expansion and no differentiability.
-/

open scoped NNReal Ring BigOperators
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]

/-- The second-order constant of the Wasserstein field on `[α·1, β·1]`. -/
noncomputable def secondOrderConst (α β : ℝ) : ℝ :=
  β * (β / 2) * (α⁻¹ ^ 4 + β ^ 2 / 4 * α⁻¹ ^ 6)

/-- **The second-order estimate**, one term. -/
theorem hsNorm_increment_sub_deriv_le {a X Y : E →L[ℂ] E} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (ha : IsStrictlyPositive a)
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (haα : α • (1 : E →L[ℂ] E) ≤ a) (haβ : a ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y)) (hPsa : IsSelfAdjoint (X - Y))
    {v : ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ}
    (hv : (↑v : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) Y⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    hsNorm ((gm a Y⁻¹ʳ - gm a X⁻¹ʳ)
        - conjMap (a ^ (1/2 : ℝ)) ((↑v⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
          (conjMap (a ^ (-(1/2) : ℝ)) (Y⁻¹ʳ * (X - Y) * Y⁻¹ʳ))))
      ≤ secondOrderConst α β * (‖X - Y‖ * hsNorm (X - Y)) := by
  have hαinv : (0 : ℝ) < α⁻¹ := inv_pos.mpr hα
  have hβinv : (0 : ℝ) < β⁻¹ := inv_pos.mpr hβ
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hNsa : IsSelfAdjoint ((a ^ (-(1/2) : ℝ)) : E →L[ℂ] E) := isSelfAdjoint_rpow a _
  have hN2 : ‖(a ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (-(1/2) : ℝ) : E →L[ℂ] E)‖ ≤ α⁻¹ :=
    norm_rpow_neg_half_sq_le ha hα haα
  have hP2 : ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖ * ‖(a ^ (1/2 : ℝ) : E →L[ℂ] E)‖ ≤ β :=
    norm_rpow_half_sq_le ha.nonneg hβ.le haβ
  have hXn : ‖(X⁻¹ʳ : E →L[ℂ] E)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hX hα hXα
  have hYn : ‖(Y⁻¹ʳ : E →L[ℂ] E)‖ ≤ α⁻¹ := norm_ringInverse_le_of_smul_one_le hY hα hYα
  -- the two Sylvester problems
  obtain ⟨W', hW'def⟩ : ∃ z : E →L[ℂ] E,
      z = (a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * (gm a Y⁻¹ʳ - gm a X⁻¹ʳ) * a ^ (-(1/2) : ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨D', hD'def⟩ : ∃ z : E →L[ℂ] E,
      z = conjMap (a ^ (-(1/2) : ℝ)) ((Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ) := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ z : E →L[ℂ] E,
      z = conjMap (a ^ (-(1/2) : ℝ)) ((Y⁻¹ʳ : E →L[ℂ] E) * (X - Y) * Y⁻¹ʳ) := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ z : E →L[ℂ] E,
      z = (↑v⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) q := ⟨_, rfl⟩
  obtain ⟨Xc, hXcdef⟩ : ∃ z : E →L[ℂ] E,
      z = (a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * gm a Y⁻¹ʳ * a ^ (-(1/2) : ℝ) := ⟨_, rfl⟩
  obtain ⟨Yc, hYcdef⟩ : ∃ z : E →L[ℂ] E,
      z = (a ^ (-(1/2) : ℝ) : E →L[ℂ] E) * gm a X⁻¹ʳ * a ^ (-(1/2) : ℝ) := ⟨_, rfl⟩
  rw [← hqdef, ← hVdef]
  -- the increment solves a Sylvester equation
  have hsyl1 : Xc * W' + W' * Yc = D' := by
    rw [hXcdef, hYcdef, hW'def, hD'def, conjMap_apply']
    exact gm_sub_sylvester ha hY.ringInverse hX.ringInverse
  -- the linearisation solves a Lyapunov equation with the same first coefficient
  have hXcsqrt : Xc = CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) Y⁻¹ʳ) := by
    rw [hXcdef, cfcSqrt_conjMap_rpow_neg_half ha]
  have hqsa : IsSelfAdjoint q := by
    rw [hqdef]
    exact isSelfAdjoint_conjMap hNsa (hPsa.conjugate_self hY.ringInverse.isSelfAdjoint)
  have hsyl2 : Xc * V + V * Xc = q := by
    rw [hXcsqrt, hVdef]
    exact lyapunov_twisted_unit_inv hv hqsa
  -- lower bounds
  have hXclb : β⁻¹ • (1 : E →L[ℂ] E) ≤ Xc := by
    rw [hXcsqrt]; exact smul_one_le_cfcSqrt_conjMap ha hY hβ haβ hYβ
  have hYclb : β⁻¹ • (1 : E →L[ℂ] E) ≤ Yc := by
    rw [hYcdef, ← cfcSqrt_conjMap_rpow_neg_half ha]
    exact smul_one_le_cfcSqrt_conjMap ha hX hβ haβ hXβ
  have hXcsa : IsSelfAdjoint Xc := by
    rw [hXcsqrt]; exact (CFC.sqrt_nonneg _).isSelfAdjoint
  have hYcsa : IsSelfAdjoint Yc := by
    rw [hYcdef, ← cfcSqrt_conjMap_rpow_neg_half ha]
    exact (CFC.sqrt_nonneg _).isSelfAdjoint
  -- the key: `Xc - Yc = W'`
  have hcoeff : Xc - Yc = W' := by
    rw [hXcdef, hYcdef, hW'def]
    noncomm_ring
  -- Hilbert–Schmidt structure
  have hinvdiffHS : IsHilbertSchmidt ((Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ) :=
    isHilbertSchmidt_ringInverse_sub hY hX hPHS
  have hD'HS : IsHilbertSchmidt D' := by
    rw [hD'def, conjMap_apply']; exact (hinvdiffHS.comp_left _).comp_right _
  have hW'HS : IsHilbertSchmidt W' :=
    isHilbertSchmidt_of_sylvester hXcsa hYcsa hβinv hβinv hXclb hYclb hD'HS hsyl1
  have hVHS : IsHilbertSchmidt V := by
    rw [hVdef, hqdef]
    exact isHilbertSchmidt_gmInvDerivSolution ha hY hPHS hPsa hv
  -- sizes
  have hinvdiff : ‖(Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ‖ ≤ (α⁻¹ * α⁻¹) * ‖X - Y‖ := by
    have h := norm_ringInverse_sub_le_of_Icc hY hX hα hYα hXα
    rwa [show ‖Y - X‖ = ‖X - Y‖ by rw [← norm_neg (X - Y), neg_sub]] at h
  have hinvdiffHSn : hsNorm ((Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ) ≤ (α⁻¹ * α⁻¹) * hsNorm (X - Y) := by
    have hid : (Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ = Y⁻¹ʳ * ((X : E →L[ℂ] E) - Y) * X⁻¹ʳ := by
      have h1 : (Y⁻¹ʳ : E →L[ℂ] E) * ((X : E →L[ℂ] E) - Y) * X⁻¹ʳ
          = Y⁻¹ʳ * (X * X⁻¹ʳ) - (Y⁻¹ʳ * Y) * X⁻¹ʳ := by noncomm_ring
      rw [h1, Ring.mul_inverse_cancel _ hX.isUnit, Ring.inverse_mul_cancel _ hY.isUnit,
        mul_one, one_mul]
    rw [hid]
    refine (hsNorm_sandwich_le (S := (Y⁻¹ʳ : E →L[ℂ] E)) (T := (X⁻¹ʳ : E →L[ℂ] E)) hPHS).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul hYn hXn (norm_nonneg _) hαinv.le)
      (hsNorm_nonneg _)
  have hD'n : ‖D'‖ ≤ α⁻¹ * ((α⁻¹ * α⁻¹) * ‖X - Y‖) := by
    rw [hD'def]
    refine (norm_conjMap_le _ _).trans ?_
    exact mul_le_mul hN2 hinvdiff (norm_nonneg _) hαinv.le
  have hD'HSn : hsNorm D' ≤ α⁻¹ * ((α⁻¹ * α⁻¹) * hsNorm (X - Y)) := by
    rw [hD'def]
    refine (hsNorm_conjMap_le hinvdiffHS).trans ?_
    exact mul_le_mul hN2 hinvdiffHSn (hsNorm_nonneg _) hαinv.le
  have hW'n : ‖W'‖ ≤ (β / 2 * α⁻¹ ^ 3) * ‖X - Y‖ := by
    have h := norm_le_of_sylvester hXcsa hYcsa hβinv hβinv hXclb hYclb hsyl1
    have hid : ‖W'‖ = (β / 2) * ((β⁻¹ + β⁻¹) * ‖W'‖) := by field_simp; ring
    rw [hid]
    refine le_trans (mul_le_mul_of_nonneg_left (h.trans hD'n)
      (by positivity : (0:ℝ) ≤ β / 2)) (le_of_eq ?_)
    ring
  have hW'HSn : hsNorm W' ≤ (β / 2 * α⁻¹ ^ 3) * hsNorm (X - Y) := by
    have h := hsNorm_le_of_sylvester hXcsa hYcsa hW'HS hβinv hβinv hXclb hYclb hsyl1
    have hid : hsNorm W' = (β / 2) * ((β⁻¹ + β⁻¹) * hsNorm W') := by field_simp; ring
    rw [hid]
    refine le_trans (mul_le_mul_of_nonneg_left (h.trans hD'HSn)
      (by positivity : (0:ℝ) ≤ β / 2)) (le_of_eq ?_)
    ring
  -- the two right-hand sides differ by a second-order term
  have hqD' : hsNorm (q - D') ≤ (α⁻¹ ^ 4) * (‖X - Y‖ * hsNorm (X - Y)) := by
    have hidinv : (Y⁻¹ʳ : E →L[ℂ] E) * ((X : E →L[ℂ] E) - Y) * X⁻¹ʳ
        = (Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ := by
      have h1 : (Y⁻¹ʳ : E →L[ℂ] E) * ((X : E →L[ℂ] E) - Y) * X⁻¹ʳ
          = Y⁻¹ʳ * (X * X⁻¹ʳ) - (Y⁻¹ʳ * Y) * X⁻¹ʳ := by noncomm_ring
      rw [h1, Ring.mul_inverse_cancel _ hX.isUnit, Ring.inverse_mul_cancel _ hY.isUnit,
        mul_one, one_mul]
    have hinner : (Y⁻¹ʳ : E →L[ℂ] E) * (X - Y) * Y⁻¹ʳ - ((Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ)
        = (Y⁻¹ʳ : E →L[ℂ] E) * (X - Y) * ((Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ) := by
      calc (Y⁻¹ʳ : E →L[ℂ] E) * (X - Y) * Y⁻¹ʳ - ((Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ)
          = (Y⁻¹ʳ : E →L[ℂ] E) * (X - Y) * Y⁻¹ʳ
            - (Y⁻¹ʳ : E →L[ℂ] E) * ((X : E →L[ℂ] E) - Y) * X⁻¹ʳ := by rw [hidinv]
        _ = (Y⁻¹ʳ : E →L[ℂ] E) * (X - Y) * ((Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ) := by noncomm_ring
    have hid2 : q - D' = conjMap (a ^ (-(1/2) : ℝ))
        ((Y⁻¹ʳ : E →L[ℂ] E) * (X - Y) * ((Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ)) := by
      rw [hqdef, hD'def, ← map_sub, hinner]
    rw [hid2]
    have hHSin : IsHilbertSchmidt
        ((Y⁻¹ʳ : E →L[ℂ] E) * (X - Y) * ((Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ)) :=
      (hPHS.comp_left _).comp_right _
    refine (hsNorm_conjMap_le hHSin).trans ?_
    have hbin : hsNorm ((Y⁻¹ʳ : E →L[ℂ] E) * (X - Y) * ((Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ))
        ≤ α⁻¹ * ((α⁻¹ * α⁻¹) * ‖X - Y‖) * hsNorm (X - Y) := by
      refine (hsNorm_sandwich_le (S := (Y⁻¹ʳ : E →L[ℂ] E))
        (T := ((Y⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ)) hPHS).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (hsNorm_nonneg _)
      exact mul_le_mul hYn hinvdiff (norm_nonneg _) hαinv.le
    refine le_trans (mul_le_mul hN2 hbin (hsNorm_nonneg _) hαinv.le) (le_of_eq ?_)
    ring
  -- the Sylvester perturbation
  have hsyl := hsNorm_sylvester_sub_le hXcsa hXcsa hVHS hW'HS hβinv hβinv hXclb hXclb
    hsyl2 hsyl1
  have hcoeffn : ‖Xc - Xc‖ + ‖Xc - Yc‖ = ‖W'‖ := by rw [sub_self, norm_zero, hcoeff, zero_add]
  rw [hcoeffn] at hsyl
  have hZnn : (0 : ℝ) ≤ ‖X - Y‖ := norm_nonneg _
  have hPnn : (0 : ℝ) ≤ hsNorm (X - Y) := hsNorm_nonneg _
  have hprod : ‖W'‖ * hsNorm W'
      ≤ (β ^ 2 / 4 * α⁻¹ ^ 6) * (‖X - Y‖ * hsNorm (X - Y)) := by
    refine le_trans (mul_le_mul hW'n hW'HSn (hsNorm_nonneg _) (by positivity))
      (le_of_eq ?_)
    ring
  have hkey : (β⁻¹ + β⁻¹) * hsNorm (V - W')
      ≤ (α⁻¹ ^ 4 + β ^ 2 / 4 * α⁻¹ ^ 6) * (‖X - Y‖ * hsNorm (X - Y)) := by
    refine hsyl.trans ?_
    linarith [hqD', hprod]
  have hfinal : hsNorm (V - W')
      ≤ (β / 2) * ((α⁻¹ ^ 4 + β ^ 2 / 4 * α⁻¹ ^ 6) * (‖X - Y‖ * hsNorm (X - Y))) := by
    have hid : hsNorm (V - W') = (β / 2) * ((β⁻¹ + β⁻¹) * hsNorm (V - W')) := by
      field_simp; ring
    rw [hid]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  -- transport back
  have hpeel : conjMap (a ^ (1/2 : ℝ)) W' = gm a Y⁻¹ʳ - gm a X⁻¹ʳ := by
    rw [hW'def, conjMap_apply', ← mul_assoc]
    exact sandwich_peel ha _
  have hgoal : (gm a Y⁻¹ʳ - gm a X⁻¹ʳ) - conjMap (a ^ (1/2 : ℝ)) V
      = conjMap (a ^ (1/2 : ℝ)) (W' - V) := by
    rw [map_sub, hpeel]
  rw [hgoal]
  have houter : hsNorm (conjMap (a ^ (1/2 : ℝ)) (W' - V)) ≤ β * hsNorm (W' - V) := by
    refine (hsNorm_conjMap_le (hW'HS.sub hVHS)).trans ?_
    exact mul_le_mul_of_nonneg_right hP2 (hsNorm_nonneg _)
  have hsymm : hsNorm (W' - V) = hsNorm (V - W') := by
    show Real.sqrt (hsNormSq _) = Real.sqrt (hsNormSq _)
    rw [show (W' - V : E →L[ℂ] E) = -(V - W') by abel, hsNormSq_neg_eq_self]
  rw [hsymm] at houter
  refine houter.trans ?_
  unfold secondOrderConst
  refine le_trans (mul_le_mul_of_nonneg_left hfinal hβ.le) (le_of_eq ?_)
  ring

variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → E →L[ℂ] E}

/-- **The second-order estimate for the Wasserstein vector field.**  The increment of `Φ` differs
from its linearisation at `Y` by a quadratic term. -/
theorem hsNorm_wassField_increment_sub_deriv_le {X Y : E →L[ℂ] E} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hX : IsStrictlyPositive X) (hY : IsStrictlyPositive Y)
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hXα : α • (1 : E →L[ℂ] E) ≤ X) (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hPHS : IsHilbertSchmidt (X - Y)) (hPsa : IsSelfAdjoint (X - Y))
    {v : ι → ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ}
    (hv : ∀ i ∈ s, (↑(v i) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) Y⁻¹ʳ))).comp (saProj)
        + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj)) :
    hsNorm ((wassField s w Av X - wassField s w Av Y)
        - wassDerivFun s w Av Y v (X - Y))
      ≤ secondOrderConst α β * (‖X - Y‖ * hsNorm (X - Y)) := by
  have hid : (wassField s w Av X - wassField s w Av Y) - wassDerivFun s w Av Y v (X - Y)
      = ∑ i ∈ s, w i • ((gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ)
        - conjMap ((Av i) ^ (1/2 : ℝ)) ((↑(v i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
          (conjMap ((Av i) ^ (-(1/2) : ℝ)) (Y⁻¹ʳ * (X - Y) * Y⁻¹ʳ)))) := by
    unfold wassField wassDerivFun
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [gmInvMap_eq_gm hX, gmInvMap_eq_gm hY, ← smul_sub, ← smul_sub]
    congr 1
    abel
  rw [hid]
  have hHS : ∀ i ∈ s, IsHilbertSchmidt (w i • ((gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ)
      - conjMap ((Av i) ^ (1/2 : ℝ)) ((↑(v i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
        (conjMap ((Av i) ^ (-(1/2) : ℝ)) (Y⁻¹ʳ * (X - Y) * Y⁻¹ʳ))))) := by
    intro i hi
    refine IsHilbertSchmidt.real_smul (IsHilbertSchmidt.sub ?_ ?_) _
    · have hγ : (0 : ℝ) < Real.sqrt (α * β⁻¹) :=
        Real.sqrt_pos.mpr (by positivity)
      refine isHilbertSchmidt_gm_sub (hA i hi) hY.ringInverse hX.ringInverse hγ hβ
        (hAβ i hi) ?_ ?_ (isHilbertSchmidt_ringInverse_sub hY hX hPHS)
      · exact smul_one_le_gm (hA i hi) hY.ringInverse hα (inv_pos.mpr hβ) (hAα i hi)
          (smul_one_le_ringInverse_of_le_smul_one hY hβ hYβ)
      · exact smul_one_le_gm (hA i hi) hX.ringInverse hα (inv_pos.mpr hβ) (hAα i hi)
          (smul_one_le_ringInverse_of_le_smul_one hX hβ hXβ)
    · exact isHilbertSchmidt_gmInvDeriv (hA i hi) hY hPHS hPsa (hv i hi)
  refine (hsNorm_sum_le hHS).trans ?_
  have hterm : ∀ i ∈ s, hsNorm (w i • ((gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ)
      - conjMap ((Av i) ^ (1/2 : ℝ)) ((↑(v i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
        (conjMap ((Av i) ^ (-(1/2) : ℝ)) (Y⁻¹ʳ * (X - Y) * Y⁻¹ʳ)))))
      ≤ w i * (secondOrderConst α β * (‖X - Y‖ * hsNorm (X - Y))) := by
    intro i hi
    rw [hsNorm_real_smul, abs_of_nonneg (hw i hi)]
    exact mul_le_mul_of_nonneg_left
      (hsNorm_increment_sub_deriv_le hα hβ (hA i hi) hX hY (hAα i hi) (hAβ i hi)
        hXα hXβ hYα hYβ hPHS hPsa (hv i hi)) (hw i hi)
  calc ∑ i ∈ s, hsNorm (w i • ((gm (Av i) Y⁻¹ʳ - gm (Av i) X⁻¹ʳ)
        - conjMap ((Av i) ^ (1/2 : ℝ)) ((↑(v i)⁻¹ : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
          (conjMap ((Av i) ^ (-(1/2) : ℝ)) (Y⁻¹ʳ * (X - Y) * Y⁻¹ʳ)))))
      ≤ ∑ i ∈ s, w i * (secondOrderConst α β * (‖X - Y‖ * hsNorm (X - Y))) :=
        Finset.sum_le_sum hterm
    _ = secondOrderConst α β * (‖X - Y‖ * hsNorm (X - Y)) := by
        rw [← Finset.sum_mul, hwsum, one_mul]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
