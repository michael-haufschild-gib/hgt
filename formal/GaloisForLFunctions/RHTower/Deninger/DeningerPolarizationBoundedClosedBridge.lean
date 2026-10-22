/-
The bounded weight-one polarization is the closed one on its whole domain.

`DeningerWeightOnePolarization H` carries an everywhere-defined generator `theta : End ℂ H`;
`DeningerClosedWeightOnePolarization H` carries a closed densely-defined one.  The two packages
prove the same four statements — the adjoint identity, skew-symmetry of the centered generator,
the critical line for eigenvalues, and the vanishing of Jordan-chain heads — from the same
polarization axioms.

They are not independent.  `DeningerCompleteCarrierSpectrumBounded` already derives, from the
weight-one derivation law, that `i·(theta − 1/2)` is symmetric and hence — by Hellinger–Toeplitz on
a complete carrier — that `theta` is continuous.  Continuity closes its graph, and its domain is
everything, so the bounded package is the domain-`⊤` closed package:

* `DeningerWeightOnePolarization.isClosed_toPMap_top` — the everywhere-defined generator is closed;
* `DeningerWeightOnePolarization.toClosed` — the closed package it determines.
-/
import GaloisForLFunctions.RHTower.Deninger.DeningerClosedOperatorPolarization
import GaloisForLFunctions.RHTower.Deninger.DeningerCompleteCarrierSpectrumBounded

noncomputable section

open scoped ComplexConjugate

namespace RHTower

namespace DeningerWeightOnePolarization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The graph of an everywhere-defined continuous generator is the zero set of a continuous map. -/
theorem graph_toPMap_top_eq [CompleteSpace H] (P : DeningerWeightOnePolarization H) :
    ((P.theta.toPMap ⊤).graph : Set (H × H))
      = {p : H × H | p.2 - P.theta p.1 = 0} := by
  ext p
  constructor
  · intro hp
    rcases (LinearPMap.mem_graph_iff' _).1 hp with ⟨y, hy⟩
    have h1 : (y : H) = p.1 := congrArg Prod.fst hy
    have h2 : (P.theta.toPMap ⊤) y = p.2 := congrArg Prod.snd hy
    rw [LinearMap.toPMap_apply] at h2
    simp only [Set.mem_setOf_eq, ← h2, h1, sub_self]
  · intro hp
    simp only [Set.mem_setOf_eq, sub_eq_zero] at hp
    refine (LinearPMap.mem_graph_iff' _).2 ⟨⟨p.1, Submodule.mem_top⟩, ?_⟩
    rw [LinearMap.toPMap_apply]
    exact Prod.ext rfl hp.symm

/-- The everywhere-defined generator is a closed operator. -/
theorem isClosed_toPMap_top [CompleteSpace H] (P : DeningerWeightOnePolarization H) :
    (P.theta.toPMap ⊤).IsClosed := by
  have hcont : Continuous fun p : H × H => p.2 - P.theta p.1 :=
    continuous_snd.sub ((theta_continuous P).comp continuous_fst)
  have hset : {p : H × H | p.2 - P.theta p.1 = 0}
      = (fun p : H × H => p.2 - P.theta p.1) ⁻¹' {0} := by
    ext p; simp
  have : IsClosed {p : H × H | p.2 - P.theta p.1 = 0} := by
    rw [hset]
    exact (isClosed_singleton (X := H) (x := 0)).preimage hcont
  rw [LinearPMap.IsClosed, P.graph_toPMap_top_eq]
  exact this

/-- **The bounded polarized package is a closed polarized package.**  Its generator is the
everywhere-defined one, closed by automatic boundedness and dense because its domain is
everything. -/
def toClosed [CompleteSpace H] (P : DeningerWeightOnePolarization H) :
    DeningerClosedWeightOnePolarization H where
  theta := P.theta.toPMap ⊤
  theta_closed := P.isClosed_toPMap_top
  theta_dense := by simp
  cupTrace := P.cupTrace
  cup_nondegenerate := P.cup_nondegenerate
  star := P.star
  star_mem_domain := fun _ => Submodule.mem_top
  theta_cup := by
    intro x y
    rw [LinearMap.toPMap_apply, LinearMap.toPMap_apply]
    exact P.theta_cup (x : H) (y : H)
  star_theta := by
    intro x
    rw [LinearMap.toPMap_apply, LinearMap.toPMap_apply]
    exact P.star_theta (x : H)
  inner_eq_cup_star := P.inner_eq_cup_star

@[simp] theorem toClosed_theta_apply [CompleteSpace H] (P : DeningerWeightOnePolarization H)
    (x : (P.toClosed).theta.domain) : (P.toClosed).theta x = P.theta (x : H) :=
  LinearMap.toPMap_apply _ _ _

@[simp] theorem toClosed_cupTrace [CompleteSpace H] (P : DeningerWeightOnePolarization H) :
    (P.toClosed).cupTrace = P.cupTrace := rfl

end DeningerWeightOnePolarization

end RHTower
