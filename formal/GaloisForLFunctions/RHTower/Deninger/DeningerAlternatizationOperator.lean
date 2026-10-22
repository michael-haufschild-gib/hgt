import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Constructions

/-!
# Alternatization as a bounded operator

Antisymmetrizing a continuous multilinear map is a continuous linear operation with norm at most
`n!`, and on a form that is already alternating it multiplies by `n!`.  Over a field of
characteristic zero this exhibits the space of continuous alternating forms as a continuously linear
retract of the space of continuous multilinear forms, so a family of alternating forms is analytic
as soon as it is analytic after forgetting antisymmetry.  This is what makes the pullback of a
differential form along an analytic map an analytic family of forms, since the pullback is
multilinear in the linear map only before antisymmetrization.

* `deningerAlternatizationCLM` : antisymmetrization as a continuous linear map.
* `deningerAlternatizationCLM_toContinuousMultilinearMap` : it is `n!` on alternating forms.
* `deningerAnalyticAt_of_toContinuousMultilinearMap` : analyticity descends from multilinear forms.
-/

namespace RHTower

section Alternatization

variable {𝕜 M N ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup M] [NormedSpace 𝕜 M] [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  [Fintype ι] [DecidableEq ι]

theorem deningerNorm_sign_smul (σ : Equiv.Perm ι) (x : N) :
    ‖(Equiv.Perm.sign σ : ℤˣ) • x‖ = ‖x‖ := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp

/-- **Alternatization is bounded**, with norm at most `n!`. -/
theorem deningerNorm_alternatization_le (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => M) N) :
    ‖ContinuousMultilinearMap.alternatization f‖ ≤ (Fintype.card ι).factorial * ‖f‖ := by
  refine ContinuousAlternatingMap.opNorm_le_bound _
    (mul_nonneg (by positivity) (norm_nonneg f)) fun v => ?_
  rw [ContinuousMultilinearMap.alternatization_apply_apply]
  calc ‖∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℤˣ) • f (v ∘ σ)‖
      ≤ ∑ σ : Equiv.Perm ι, ‖(Equiv.Perm.sign σ : ℤˣ) • f (v ∘ σ)‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ‖f‖ * ∏ i, ‖v i‖ := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [deningerNorm_sign_smul]
        refine (f.le_opNorm (v ∘ σ)).trans_eq ?_
        congr 1
        exact Equiv.prod_comp σ fun i => ‖v i‖
    _ = (Fintype.card ι).factorial * ‖f‖ * ∏ i, ‖v i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul, mul_assoc]

/-- **Alternatization as a continuous linear map.** -/
noncomputable def deningerAlternatizationCLM :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => M) N →L[𝕜] (M [⋀^ι]→L[𝕜] N) :=
  LinearMap.mkContinuous
    { toFun := fun f => ContinuousMultilinearMap.alternatization f
      map_add' := fun f g => map_add ContinuousMultilinearMap.alternatization f g
      map_smul' := fun c f => by
        ext v
        simp only [ContinuousMultilinearMap.alternatization_apply_apply,
          smul_apply, RingHom.id_apply,
          ContinuousAlternatingMap.smul_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun σ _ => (smul_comm _ _ _) }
    ((Fintype.card ι).factorial) fun f => deningerNorm_alternatization_le f

theorem deningerAlternatizationCLM_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => M) N)
    (v : ι → M) :
    deningerAlternatizationCLM f v = ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℤˣ) • f (v ∘ σ) :=
  ContinuousMultilinearMap.alternatization_apply_apply f v

/-- **Alternatizing an alternating form multiplies it by `n!`.** -/
theorem deningerAlternatizationCLM_toContinuousMultilinearMap (A : M [⋀^ι]→L[𝕜] N) :
    deningerAlternatizationCLM A.toContinuousMultilinearMap = (Fintype.card ι).factorial • A := by
  ext v
  rw [deningerAlternatizationCLM_apply]
  have hterm : ∀ σ : Equiv.Perm ι,
      (Equiv.Perm.sign σ : ℤˣ) • A.toContinuousMultilinearMap (v ∘ σ) = A v := by
    intro σ
    have h : A.toContinuousMultilinearMap (v ∘ σ) = (Equiv.Perm.sign σ : ℤˣ) • A v :=
      A.toAlternatingMap.map_perm v σ
    rw [h, smul_smul, Int.units_mul_self, one_smul]
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm]
  rfl

/-- **A continuous alternating form is `n!⁻¹` times the alternatization of itself.** -/
theorem deningerSmul_alternatizationCLM [CharZero 𝕜] (A : M [⋀^ι]→L[𝕜] N) :
    (((Fintype.card ι).factorial : 𝕜))⁻¹ •
        deningerAlternatizationCLM A.toContinuousMultilinearMap = A := by
  rw [deningerAlternatizationCLM_toContinuousMultilinearMap,
    ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.2 (Nat.factorial_pos _).ne'

/-- **Analyticity of a family of alternating forms descends from the multilinear forms**: the
antisymmetrization retraction is continuous linear, so a family that is analytic after forgetting
antisymmetry is analytic. -/
theorem deningerAnalyticAt_of_toContinuousMultilinearMap [CharZero 𝕜] {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] {P : X → (M [⋀^ι]→L[𝕜] N)} {x : X}
    (h : AnalyticAt 𝕜 (fun y => (P y).toContinuousMultilinearMap) x) : AnalyticAt 𝕜 P x := by
  have hP : P = fun y => ((((Fintype.card ι).factorial : 𝕜))⁻¹ • deningerAlternatizationCLM)
      ((P y).toContinuousMultilinearMap) := by
    funext y
    exact (deningerSmul_alternatizationCLM (P y)).symm
  rw [hP]
  exact (ContinuousLinearMap.analyticAt _ _).comp h

end Alternatization

end RHTower
