import GaloisForLFunctions.HTGeometry.PencilDerivationPlumbing

/-!
# Iterated derivations of a sum of phase composites

A pencil carrier is a sum of one phase composite per facet.  Since the derivation is linear and
sends a phase composite to a phase composite, an `r`-fold derivative of such a sum is again a sum of
phase composites, with the inner functions replaced by `(L w)^r · Θ^r`.

* `contDiff_eulerOp_iterate` — iterates of the Euler operator stay smooth;
* `differentiable_linearMap`, `differentiable_phaseComp` — the analytic side conditions;
* `dirDeriv_phaseComp_scaled` — one derivation step on an already scaled composite;
* `dirDeriv_iterate_sum_phaseComp` — the iterated rule for a finite sum.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

theorem contDiff_eulerOp_iterate {Ψ : ℂ → ℂ} (h : ContDiff ℂ (⊤ : ℕ∞) Ψ) (r : ℕ) :
    ContDiff ℂ (⊤ : ℕ∞) (eulerOp^[r] Ψ) := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact contDiff_eulerOp ih

/-- A linear form on a finite-dimensional space is differentiable. -/
theorem differentiable_linearMap (L : (Fin d → ℂ) →ₗ[ℂ] ℂ) :
    Differentiable ℂ fun z : Fin d → ℂ => L z :=
  (LinearMap.toContinuousLinearMap L).differentiable

theorem differentiable_phaseComp {L : (Fin d → ℂ) →ₗ[ℂ] ℂ} {Ψ : ℂ → ℂ}
    (hΨ : Differentiable ℂ Ψ) : Differentiable ℂ (phaseComp L Ψ) :=
  hΨ.comp (Complex.differentiable_exp.comp (differentiable_linearMap L))

/-- One derivation step on a scaled phase composite. -/
theorem dirDeriv_phaseComp_scaled {L : (Fin d → ℂ) →ₗ[ℂ] ℂ} {Φ : ℂ → ℂ}
    (hΦ : ContDiff ℂ (⊤ : ℕ∞) Φ) (w : Fin d → ℂ) (r : ℕ) :
    dirDeriv w (phaseComp L (fun u => (L w) ^ r * (eulerOp^[r] Φ) u))
      = phaseComp L (fun u => (L w) ^ (r + 1) * (eulerOp^[r + 1] Φ) u) := by
  rw [← dirDeriv_iterate_phaseComp hΦ w r, ← Function.iterate_succ_apply' (dirDeriv w) r,
    dirDeriv_iterate_phaseComp hΦ w (r + 1)]

/-- **An `r`-fold derivation of a sum of phase composites.** -/
theorem dirDeriv_iterate_sum_phaseComp {ι : Type*} (s : Finset ι)
    (Lin : ι → ((Fin d → ℂ) →ₗ[ℂ] ℂ)) (Φ : ι → ℂ → ℂ)
    (hΦ : ∀ i ∈ s, ContDiff ℂ (⊤ : ℕ∞) (Φ i)) (w : Fin d → ℂ) (r : ℕ) :
    (dirDeriv w)^[r] (fun z => ∑ i ∈ s, phaseComp (Lin i) (Φ i) z)
      = fun z => ∑ i ∈ s,
          phaseComp (Lin i) (fun u => (Lin i w) ^ r * (eulerOp^[r] (Φ i)) u) z := by
  induction r with
  | zero =>
    funext z
    simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih]
    have hdiff : ∀ i ∈ s, Differentiable ℂ
        (phaseComp (Lin i) fun u => (Lin i w) ^ r * (eulerOp^[r] (Φ i)) u) := by
      intro i hi
      exact differentiable_phaseComp
        (((contDiff_eulerOp_iterate (hΦ i hi) r).differentiable (by simp)).const_mul _)
    rw [dirDeriv_sum s hdiff w]
    funext z
    refine Finset.sum_congr rfl fun i hi => ?_
    exact congrFun (dirDeriv_phaseComp_scaled (hΦ i hi) w r) z

end

end GaloisForLFunctions.HTGeometry
