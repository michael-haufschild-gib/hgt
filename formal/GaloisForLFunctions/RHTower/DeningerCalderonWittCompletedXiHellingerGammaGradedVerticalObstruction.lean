import GaloisForLFunctions.RHTower.DeningerCalderonWittCompletedXiHellingerGammaPureHodgeCoface

/-!
# Graded vertical obstruction for the completed Hellinger--Gamma coface

Restoring the Hellinger grade gives an honest orthogonal `ℓ²` carrier for
the completed balanced primitives.  Their norms still tend to zero because
of the source Gamma-factorial gauge.

This creates a sharp boundary for one-marginal graph descent.  Suppose a
linear secondary boundary is defined on a domain containing every graded
balanced vertex and annihilates every adjacent coface.  Its value is then
constant along the vertex chain.  The vertex chain tends to zero, so any
nonzero depth-zero charge appears as a vertical element `(0, charge)` in
the ambient graph closure.  Consequently the graph is not closed.

Thus the existing Hodge/incidence marginal cannot by itself be both
single-valued closed and conservative on nonzero endpoint charge.  The
strongest survivor is the explicit vertical multivalued class.  A closing
construction must join the independent physical jet provenance before
forming this closure; raw or one-marginal graph completion cannot do so.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

namespace CompletedXiHellingerGammaPureHodgeCoface

open PrimitivePromotedHellingerGammaPureHodgeCoface

/-- Orthogonal Hilbert carrier retaining every Hellinger grade. -/
abbrev HellingerGammaPureHodgeXiDepthCompletion
    (p q : Nat.Primes) (hpq : p ≠ q) :=
  lp (fun _ : ℕ => HellingerGammaPureHodgeXiCofaceCompletion p q hpq) 2

/-- One completed balanced primitive at its own retained grade. -/
def hellingerGammaCompletedGradedBalancedVertex
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    HellingerGammaPureHodgeXiDepthCompletion p q hpq :=
  lp.single 2 n (hellingerGammaCompletedBalancedPrimitive hpq a n x)

/-- Adjacent-grade coface after restoring the orthogonal grade label. -/
def hellingerGammaCompletedGradedAdjacentCoface
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    HellingerGammaPureHodgeXiDepthCompletion p q hpq :=
  hellingerGammaCompletedGradedBalancedVertex hpq a (n + 1) x -
    hellingerGammaCompletedGradedBalancedVertex hpq a n x

/-- Factorial damping survives restoration of the orthogonal grade label. -/
theorem hellingerGammaCompletedGradedBalancedVertex_tendsto_zero
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    Tendsto
      (fun n : ℕ => hellingerGammaCompletedGradedBalancedVertex hpq a n x)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := hellingerGammaCompletedBalancedPrimitive_tendsto_zero hpq a x
  rw [tendsto_zero_iff_norm_tendsto_zero] at h
  convert h using 1
  funext n
  exact lp.norm_single (by norm_num) n _

/-- Ambient graph of a boundary defined on a possibly proper source domain. -/
def hellingerGammaCompletedDepthBoundaryGraph
    {p q : Nat.Primes} {hpq : p ≠ q}
    (D : Submodule ℂ (HellingerGammaPureHodgeXiDepthCompletion p q hpq))
    (boundary : D →ₗ[ℂ] ℂ) :
    Set (HellingerGammaPureHodgeXiDepthCompletion p q hpq × ℂ) :=
  Set.range fun z : D =>
    ((z : HellingerGammaPureHodgeXiDepthCompletion p q hpq), boundary z)

/--
Adjacent exactness conserves endpoint charge along the whole cofinal
chain.  Factorial damping then places that charge in the vertical
multivalued part of ambient graph closure.
-/
theorem hellingerGammaCompletedGradedCoface_vertical_charge_mem_closure
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq)
    (D : Submodule ℂ (HellingerGammaPureHodgeXiDepthCompletion p q hpq))
    (boundary : D →ₗ[ℂ] ℂ)
    (hvertex : ∀ n,
      hellingerGammaCompletedGradedBalancedVertex hpq a n x ∈ D)
    (hcoface : ∀ n,
      boundary
        ⟨hellingerGammaCompletedGradedAdjacentCoface hpq a n x,
          D.sub_mem (hvertex (n + 1)) (hvertex n)⟩ = 0) :
    ((0 : HellingerGammaPureHodgeXiDepthCompletion p q hpq),
        boundary
          ⟨hellingerGammaCompletedGradedBalancedVertex hpq a 0 x,
            hvertex 0⟩) ∈
      closure (hellingerGammaCompletedDepthBoundaryGraph D boundary) := by
  let v : ℕ → HellingerGammaPureHodgeXiDepthCompletion p q hpq :=
    fun n => hellingerGammaCompletedGradedBalancedVertex hpq a n x
  let vd : ∀ n, D := fun n => ⟨v n, hvertex n⟩
  have hstep : ∀ n, boundary (vd (n + 1)) = boundary (vd n) := by
    intro n
    have h := hcoface n
    change boundary (vd (n + 1) - vd n) = 0 at h
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  have hconst : ∀ n, boundary (vd n) = boundary (vd 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n => exact (hstep n).trans (by assumption)
  have hv : Tendsto v atTop (𝓝 0) := by
    exact hellingerGammaCompletedGradedBalancedVertex_tendsto_zero hpq a x
  have hb : Tendsto (fun n => boundary (vd n)) atTop (𝓝 (boundary (vd 0))) := by
    simpa only [hconst] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => boundary (vd 0)) atTop (𝓝 (boundary (vd 0))))
  apply mem_closure_of_tendsto (hv.prodMk_nhds hb)
  filter_upwards with n
  exact ⟨vd n, rfl⟩

/--
Any nonzero conserved endpoint charge makes the one-marginal boundary
graph nonclosed.
-/
theorem hellingerGammaCompletedGradedCoface_not_isClosed_graph
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq)
    (D : Submodule ℂ (HellingerGammaPureHodgeXiDepthCompletion p q hpq))
    (boundary : D →ₗ[ℂ] ℂ)
    (hvertex : ∀ n,
      hellingerGammaCompletedGradedBalancedVertex hpq a n x ∈ D)
    (hcoface : ∀ n,
      boundary
        ⟨hellingerGammaCompletedGradedAdjacentCoface hpq a n x,
          D.sub_mem (hvertex (n + 1)) (hvertex n)⟩ = 0)
    (hcharge : boundary
        ⟨hellingerGammaCompletedGradedBalancedVertex hpq a 0 x,
          hvertex 0⟩ ≠ 0) :
    ¬ IsClosed (hellingerGammaCompletedDepthBoundaryGraph D boundary) := by
  intro hclosed
  have hvertical :=
    hellingerGammaCompletedGradedCoface_vertical_charge_mem_closure
      hpq a x D boundary hvertex hcoface
  have hmem :
      ((0 : HellingerGammaPureHodgeXiDepthCompletion p q hpq),
          boundary
            ⟨hellingerGammaCompletedGradedBalancedVertex hpq a 0 x,
              hvertex 0⟩) ∈
        hellingerGammaCompletedDepthBoundaryGraph D boundary := by
    rwa [hclosed.closure_eq] at hvertical
  obtain ⟨z, hz⟩ := hmem
  have hz0 : z = 0 := by
    apply Subtype.ext
    exact congrArg Prod.fst hz
  have hboundary := congrArg Prod.snd hz
  have hzero :
      0 = boundary
        ⟨hellingerGammaCompletedGradedBalancedVertex hpq a 0 x,
          hvertex 0⟩ := by
    simpa [hz0] using hboundary
  exact hcharge hzero.symm

end CompletedXiHellingerGammaPureHodgeCoface

end

end RHTower
