import GaloisForLFunctions.HTGeometry.ExponentialJetSubstitution
import GaloisForLFunctions.HTGeometry.FamilyInversionGauge

/-!
# Every jet point with nonzero values is the jet point of an exponential family

Prescribing finitely many derivatives of `exp (sigma i)` at a point, with nonzero values, is always
possible: realize the prescription by Taylor polynomials, which are nonvanishing near the point, and
take a holomorphic logarithm there.

This is the analytic surjectivity needed to see that the exponential jet substitution kills no
nonzero polynomial — the same device already used for the inversion gauge, with the logarithm in
place of the reciprocal.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **Realization of exponential jets.**  Any prescription of finitely many derivatives with nonzero
value at the base point is realized by an exponential family on a neighbourhood. -/
theorem exists_expFamily_realizing_jets {m : ℕ} (n : ℕ) (z₀ : ℂ) (y : Fin m → ℕ → ℂ)
    (hy : ∀ i, y i 0 ≠ 0) :
    ∃ (V : Set ℂ) (sigma : Fin m → ℂ → ℂ), IsOpen V ∧ z₀ ∈ V ∧
      (∀ i, ∀ w ∈ V, ContDiffAt ℂ (⊤ : ℕ∞) (sigma i) w) ∧
      (∀ i, ∀ k ≤ n, iteratedDeriv k (fun w => Complex.exp (sigma i w)) z₀ = y i k) := by
  classical
  choose f hfsmooth hfcont hfjet using fun i : Fin m => exists_smooth_iteratedDeriv_eq n z₀ (y i)
  have hf0 : ∀ i, f i z₀ = y i 0 := by
    intro i
    have h := hfjet i 0 (Nat.zero_le n)
    rwa [iteratedDeriv_zero] at h
  have hfz0ne : ∀ i, f i z₀ ≠ 0 := by
    intro i
    rw [hf0 i]
    exact hy i
  set V : Set ℂ := {w : ℂ | ∀ i, f i w / f i z₀ ∈ Complex.slitPlane} with hV
  have hVopen : IsOpen V := by
    rw [hV, Set.setOf_forall]
    refine isOpen_iInter_of_finite fun i => ?_
    exact Complex.isOpen_slitPlane.preimage ((hfcont i).div_const _)
  have hz₀V : z₀ ∈ V := by
    intro i
    rw [div_self (hfz0ne i)]
    exact Complex.one_mem_slitPlane
  have hlogsmooth : ∀ u ∈ Complex.slitPlane, ContDiffAt ℂ (⊤ : ℕ∞) Complex.log u := by
    intro u hu
    have hdiff : DifferentiableOn ℂ Complex.log Complex.slitPlane := fun v hv =>
      (Complex.differentiableAt_log hv).differentiableWithinAt
    exact ((hdiff.analyticOnNhd Complex.isOpen_slitPlane) u hu).contDiffAt
  refine ⟨V, fun i w => Complex.log (f i w / f i z₀) + Complex.log (f i z₀), hVopen, hz₀V, ?_, ?_⟩
  · intro i w hw
    have hinner : ContDiffAt ℂ (⊤ : ℕ∞) (fun v => f i v / f i z₀) w :=
      (hfsmooth i w).div_const _
    exact ((hlogsmooth _ (hw i)).comp w hinner).add contDiffAt_const
  · intro i k hk
    have hagree : (fun w => Complex.exp (Complex.log (f i w / f i z₀) + Complex.log (f i z₀)))
        =ᶠ[nhds z₀] f i := by
      filter_upwards [hVopen.mem_nhds hz₀V] with w hw
      rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (hw i)),
        Complex.exp_log (hfz0ne i), div_mul_cancel₀ _ (hfz0ne i)]
    rw [iteratedDeriv_congr_of_eventuallyEq hagree k]
    exact hfjet i k hk

end

end GaloisForLFunctions.HTGeometry
