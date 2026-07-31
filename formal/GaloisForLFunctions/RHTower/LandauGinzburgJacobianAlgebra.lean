import GaloisForLFunctions.HTGeometry.AnalyticGermMaximalIdeal
import GaloisForLFunctions.RHTower.LandauGinzburgNodeGerm

/-!
# The Jacobian algebra of the node is one-dimensional

The two partial derivatives of the node `x y` are the two coordinates, so its Jacobian ideal in the
local ring of analytic germs at the origin is the coordinate ideal, and the Jacobian algebra is `ℂ`
— the Milnor number of a simple vacuum is one.  Transporting along the coordinate change of
`LandauGinzburgNodeGerm` gives the same conclusion at every simple zero.

* `nodePartialFst`, `nodePartialSnd` — the partial derivatives of the node, computed from `deriv`.
* `nodeJacobianIdeal`, `nodeJacobianIdeal_eq_coordIdeal`.
* `nodeJacobianAlgebraEquiv` — **the Jacobian algebra of the node is `ℂ`.**
* `lgJacobianAlgebraEquiv` — the same at the simple vacuum of any multiplier potential.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The partial derivative of the node in the first variable. -/
def nodePartialFst : ℂ × ℂ → ℂ := fun v => deriv (fun x => nodePotential (x, v.2)) v.1

/-- The partial derivative of the node in the second variable. -/
def nodePartialSnd : ℂ × ℂ → ℂ := fun v => deriv (fun y => nodePotential (v.1, y)) v.2

theorem nodePartialFst_eq : nodePartialFst = fun v : ℂ × ℂ => v.2 := by
  funext v
  have h : HasDerivAt (fun x : ℂ => nodePotential (x, v.2)) v.2 v.1 := by
    simpa [nodePotential] using (hasDerivAt_id v.1).mul_const v.2
  exact h.deriv

theorem nodePartialSnd_eq : nodePartialSnd = fun v : ℂ × ℂ => v.1 := by
  funext v
  have h : HasDerivAt (fun y : ℂ => nodePotential (v.1, y)) v.1 v.2 := by
    simpa [nodePotential] using (hasDerivAt_id v.2).const_mul v.1
  exact h.deriv

theorem analyticAt_nodePartialFst : AnalyticAt ℂ nodePartialFst ((0 : ℂ), (0 : ℂ)) := by
  rw [nodePartialFst_eq]
  exact analyticAt_snd

theorem analyticAt_nodePartialSnd : AnalyticAt ℂ nodePartialSnd ((0 : ℂ), (0 : ℂ)) := by
  rw [nodePartialSnd_eq]
  exact analyticAt_fst

theorem analyticGermOf_nodePartialFst :
    analyticGermOf analyticAt_nodePartialFst = germCoordSnd :=
  analyticGermOf_congr _ _ (by rw [nodePartialFst_eq])

theorem analyticGermOf_nodePartialSnd :
    analyticGermOf analyticAt_nodePartialSnd = germCoordFst :=
  analyticGermOf_congr _ _ (by rw [nodePartialSnd_eq])

/-- The Jacobian ideal of the node in the local ring of analytic germs at the origin. -/
def nodeJacobianIdeal : Ideal (AnalyticGerm ((0 : ℂ), (0 : ℂ))) :=
  Ideal.span {analyticGermOf analyticAt_nodePartialFst, analyticGermOf analyticAt_nodePartialSnd}

/-- **The Jacobian ideal of the node is the coordinate ideal.** -/
theorem nodeJacobianIdeal_eq_coordIdeal :
    nodeJacobianIdeal = Ideal.span {germCoordFst, germCoordSnd} := by
  rw [nodeJacobianIdeal, analyticGermOf_nodePartialFst, analyticGermOf_nodePartialSnd,
    Set.pair_comm]

/-- **The Jacobian algebra of the node is `ℂ`.**  Its Milnor number is one: the local algebra
attached to a simple vacuum is the ground field, independently of everything else. -/
def nodeJacobianAlgebraEquiv :
    (AnalyticGerm ((0 : ℂ), (0 : ℂ)) ⧸ nodeJacobianIdeal) ≃+* ℂ :=
  (Ideal.quotEquivOfEq nodeJacobianIdeal_eq_coordIdeal).trans analyticGermQuotientCoordEquiv

/-- **The Jacobian algebra at a simple vacuum of a multiplier potential is `ℂ`.**  The coordinate
change of `lgNodeGermEquiv` carries the node's Jacobian ideal to the corresponding ideal at
`(ρ, 0)`, and the quotient is unchanged. -/
def lgJacobianAlgebraEquiv {ρ : ℂ} {G : ℂ → ℂ} (hG : AnalyticAt ℂ G ρ) (hG0 : G ρ ≠ 0) :
    (AnalyticGerm ((ρ : ℂ), (0 : ℂ)) ⧸ nodeJacobianIdeal.map (lgNodeGermEquiv hG hG0)) ≃+* ℂ :=
  (Ideal.quotientEquiv nodeJacobianIdeal (nodeJacobianIdeal.map (lgNodeGermEquiv hG hG0))
    (lgNodeGermEquiv hG hG0) rfl).symm.trans nodeJacobianAlgebraEquiv

end

end GaloisForLFunctions.RHTower
