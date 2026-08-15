import GaloisForLFunctions.HTGeometry.WindowedSource

/-!
# The window-to-Euler-jet map is a linear equivalence

Composing the derivative-jet map of a degree window with the triangular derivative-to-Euler
transform gives a linear bijection from the window coefficients onto the Euler jets at the nodes.
Between finite-dimensional spaces the inverse is continuous, so a *small* Euler-jet target is
realized by *small* window coefficients — which is what keeps a perturbation inside a prescribed
coefficient box.
-/

open Polynomial Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The window-to-Euler-jet map. -/
def eulerWindowMap {K : ℕ} (x : Fin K → ℂ) (m N : ℕ) :
    (Fin (K * m) → ℂ) →ₗ[ℂ] (Fin K × Fin m → ℂ) :=
  (eulerTransform x m).comp (windowJetMap x m N (K * m))

theorem eulerWindowMap_apply {K : ℕ} (x : Fin K → ℂ) (m N : ℕ) (w : Fin (K * m) → ℂ)
    (a : Fin K) (r : Fin m) :
    eulerWindowMap x m N w (a, r) =
      (polyEuler^[(r : ℕ)] (windowLin N (K * m) w)).eval (x a) := by
  rw [eulerWindowMap, LinearMap.comp_apply, eulerTransform_apply,
    eval_polyEuler_iterate_range r.2 (windowLin N (K * m) w) (x a),
    ← Fin.sum_univ_eq_sum_range
      (fun k => eulerStirling (r : ℕ) k * (x a) ^ k *
        (Polynomial.derivative^[k] (windowLin N (K * m) w)).eval (x a)) m]
  exact Finset.sum_congr rfl fun k _ => by rw [windowJetMap_apply]

theorem eulerWindowMap_bijective {K : ℕ} {x : Fin K → ℂ} (hxinj : Function.Injective x)
    (hx0 : ∀ a, x a ≠ 0) (m N : ℕ) : Function.Bijective (eulerWindowMap x m N) := by
  constructor
  · exact (eulerTransform_injective hx0 m).comp (windowJetMap_injective hxinj hx0 m N)
  · exact (eulerTransform_surjective hx0 m).comp (windowJetMap_surjective hxinj hx0 m N)

/-- The window-to-Euler-jet linear equivalence. -/
def eulerWindowEquiv {K : ℕ} {x : Fin K → ℂ} (hxinj : Function.Injective x)
    (hx0 : ∀ a, x a ≠ 0) (m N : ℕ) : (Fin (K * m) → ℂ) ≃ₗ[ℂ] (Fin K × Fin m → ℂ) :=
  LinearEquiv.ofBijective _ (eulerWindowMap_bijective hxinj hx0 m N)

theorem eulerWindowEquiv_apply {K : ℕ} {x : Fin K → ℂ} (hxinj : Function.Injective x)
    (hx0 : ∀ a, x a ≠ 0) (m N : ℕ) (w : Fin (K * m) → ℂ) :
    eulerWindowEquiv hxinj hx0 m N w = eulerWindowMap x m N w := rfl

/-- **A small Euler-jet target is realized by small window coefficients.** -/
theorem exists_small_window {K : ℕ} {x : Fin K → ℂ} (hxinj : Function.Injective x)
    (hx0 : ∀ a, x a ≠ 0) (m N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ J : Fin K × Fin m → ℂ, ‖J‖ < δ →
      ∃ w : Fin (K * m) → ℂ, (∀ i, ‖w i‖ < ε) ∧
        ∀ (a : Fin K) (r : Fin m),
          (polyEuler^[(r : ℕ)] (windowLin N (K * m) w)).eval (x a) = J (a, r) := by
  classical
  set e := eulerWindowEquiv hxinj hx0 m N with he
  have hcont : Continuous (e.symm : (Fin K × Fin m → ℂ) → (Fin (K * m) → ℂ)) := by
    simpa using LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
  have hzero : (e.symm : (Fin K × Fin m → ℂ) → (Fin (K * m) → ℂ)) 0 = 0 := map_zero _
  have hct := hcont.continuousAt (x := (0 : Fin K × Fin m → ℂ))
  rw [Metric.continuousAt_iff] at hct
  obtain ⟨δ, hδ, hball⟩ := hct ε hε
  refine ⟨δ, hδ, fun J hJ => ?_⟩
  refine ⟨e.symm J, ?_, ?_⟩
  · intro i
    have hdist : dist (e.symm J) (e.symm 0) < ε := by
      refine hball ?_
      rw [dist_zero_right]
      exact hJ
    rw [hzero, dist_zero_right] at hdist
    exact lt_of_le_of_lt (norm_le_pi_norm (e.symm J) i) hdist
  · intro a r
    have hval : e (e.symm J) = J := e.apply_symm_apply J
    rw [eulerWindowEquiv_apply] at hval
    have := congrFun hval (a, r)
    rw [eulerWindowMap_apply] at this
    exact this

/-- **Small window realization with an arbitrary finite node index.** -/
theorem exists_small_window' {α : Type} [Fintype α] [DecidableEq α] {x : α → ℂ}
    (hxinj : Function.Injective x) (hx0 : ∀ a, x a ≠ 0) (m N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ J : α → Fin m → ℂ, (∀ a r, ‖J a r‖ < δ) →
      ∃ w : Fin (Fintype.card α * m) → ℂ, (∀ i, ‖w i‖ < ε) ∧
        ∀ (a : α) (r : Fin m),
          (polyEuler^[(r : ℕ)] (windowLin N (Fintype.card α * m) w)).eval (x a) = J a r := by
  classical
  set e := Fintype.equivFin α with he
  set x' : Fin (Fintype.card α) → ℂ := fun b => x (e.symm b) with hx'
  have hx'inj : Function.Injective x' := hxinj.comp e.symm.injective
  have hx'0 : ∀ b, x' b ≠ 0 := fun b => hx0 _
  obtain ⟨δ, hδ, hmain⟩ := exists_small_window hx'inj hx'0 m N hε
  refine ⟨δ, hδ, fun J hJ => ?_⟩
  have hJ' : ‖(fun p : Fin (Fintype.card α) × Fin m => J (e.symm p.1) p.2)‖ < δ := by
    rw [pi_norm_lt_iff hδ]
    intro p
    exact hJ _ _
  obtain ⟨w, hw, hval⟩ := hmain (fun p => J (e.symm p.1) p.2) hJ'
  refine ⟨w, hw, fun a r => ?_⟩
  have hstep := hval (e a) r
  rw [show x' (e a) = x a by rw [hx']; simp] at hstep
  rw [hstep, e.symm_apply_apply]

end

end GaloisForLFunctions.HTGeometry
