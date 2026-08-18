import GaloisForLFunctions.HTGeometry.LinearJet
import GaloisForLFunctions.HTGeometry.LineJetTransfer

/-!
# An equation with almost-periodic coefficients as an autonomous relation on the joint jet

An algebraic differential equation whose coefficients are functions of the point of the strip is an
*autonomous* relation in the joint variable `(coefficients, jet of the solution)`: the coefficients
enter only through their values, which are the zeroth jet of the coefficient tuple.

Freezing the coefficients at one time turns the same expression into an ordinary relation on the jet
of the solution, whose derivative in the top jet is the separant.  The two descriptions agree along
the jet of the pair, which is what lets one carrier construction serve a nonautonomous equation.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

variable {N n : ℕ}

/-- The relation on the joint jet: the coefficient values times the monomials in the jets. -/
noncomputable def coeffJetRelation (e : Fin N → Fin (n + 1) → ℕ)
    (Y : Fin (n + 1) → ((Fin N → ℂ) × ℂ)) : ℂ :=
  ∑ i : Fin N, (Y 0).1 i * ∏ k : Fin (n + 1), ((Y k).2) ^ (e i k)

/-- The same relation with the coefficients frozen. -/
noncomputable def frozenRelation (e : Fin N → Fin (n + 1) → ℕ) (c : Fin N → ℂ)
    (y : Fin (n + 1) → ℂ) : ℂ :=
  ∑ i : Fin N, c i * ∏ k : Fin (n + 1), (y k) ^ (e i k)

theorem coeffJetRelation_eq_frozen (e : Fin N → Fin (n + 1) → ℕ)
    (Y : Fin (n + 1) → ((Fin N → ℂ) × ℂ)) :
    coeffJetRelation e Y = frozenRelation e (Y 0).1 (fun k => (Y k).2) := rfl

theorem continuous_coeffJetRelation (e : Fin N → Fin (n + 1) → ℕ) :
    Continuous (coeffJetRelation (N := N) (n := n) e) := by
  refine continuous_finsetSum _ fun i _ => ?_
  refine Continuous.mul ?_ ?_
  · exact (continuous_apply i).comp (continuous_fst.comp (continuous_apply 0))
  · refine continuous_finsetProd _ fun k _ => ?_
    exact (continuous_snd.comp (continuous_apply k)).pow _

theorem continuous_frozenRelation (e : Fin N → Fin (n + 1) → ℕ) (c : Fin N → ℂ) :
    Continuous (frozenRelation e c) := by
  refine continuous_finsetSum _ fun i _ => ?_
  refine continuous_const.mul ?_
  refine continuous_finsetProd _ fun k _ => ?_
  exact (continuous_apply k).pow _

variable {σ Rs : ℝ}

/-- **The joint relation along the jet of a pair is the frozen relation along the jet of the second
component.** -/
theorem coeffJetRelation_jet_eq {G : ℂ → ((Fin N → ℂ) × ℂ)}
    (hG : DifferentiableOn ℂ G (verticalStrip σ Rs)) (e : Fin N → Fin (n + 1) → ℕ)
    {z : ℂ} (hz : z ∈ verticalStrip σ Rs) :
    coeffJetRelation e (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) G z)
      = frozenRelation e (G z).1
        (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) (fun w => (G w).2) z) := by
  have hsnd : ∀ k : ℕ, iteratedDeriv k (fun w => (G w).2) z = (iteratedDeriv k G z).2 := fun k =>
    iteratedDeriv_clm_comp_eqOn (isOpen_verticalStrip σ Rs)
      (ContinuousLinearMap.snd ℂ (Fin N → ℂ) ℂ) hG k hz
  have hzero : (iteratedDeriv ((0 : Fin (n + 1)) : ℕ) G z).1 = (G z).1 := by
    norm_num
  rw [coeffJetRelation_eq_frozen, hzero]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine congrArg (fun w => (G z).1 i * w) ?_
  refine Finset.prod_congr rfl fun k _ => ?_
  show ((iteratedDeriv (k : ℕ) G z).2) ^ e i k
    = (iteratedDeriv (k : ℕ) (fun w => (G w).2) z) ^ e i k
  rw [hsnd (k : ℕ)]

/-! ### The frozen relation is smooth, and its top partial derivative is the separant -/

theorem contDiff_frozenRelation (e : Fin N → Fin (n + 1) → ℕ) (c : Fin N → ℂ) :
    ContDiff ℂ (⊤ : ℕ∞) (frozenRelation e c) := by
  refine ContDiff.sum fun i _ => ?_
  refine ContDiff.mul contDiff_const ?_
  exact contDiff_prod fun k _ =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) k).contDiff).pow _

theorem differentiable_frozenRelation (e : Fin N → Fin (n + 1) → ℕ) (c : Fin N → ℂ) :
    Differentiable ℂ (frozenRelation e c) :=
  (contDiff_frozenRelation e c).differentiable (by simp)

theorem continuous_fderiv_frozenRelation (e : Fin N → Fin (n + 1) → ℕ) (c : Fin N → ℂ) :
    Continuous (fun y => fderiv ℂ (frozenRelation e c) y) :=
  (contDiff_frozenRelation e c).continuous_fderiv (by simp)


end GaloisForLFunctions.HTGeometry
