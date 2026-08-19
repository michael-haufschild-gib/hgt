/-
# The induction step in real physical coordinates

The genericity theorems of the architecture live on a *real* coordinate space, while eigenvalue
branches are analytic in *complex* parameters.  The two meet because endpoint visibility only needs
continuity: restricting a complex-analytic branch along the real embedding gives a continuous
eigenvector family on the real coordinate space, and endpoint visibility is therefore open there.

So the induction step of Lemma A1 holds directly on the real coordinates of any linear Hamiltonian
family -- in particular on the coordinates of the tensor-tree architecture's traceless local
Hamiltonian submodule, where the maximally projective set is dense.

Main results:
* `analyticAt_linearMatrixFamily` — a linear family is analytic in its complex coefficients.
* `exists_analyticBranches_linearFamily` — analytic eigenvalue branches at a real base point with
  simple spectrum.
* `exists_mem_dense_realParameter_endpointComplete` — **the induction step in real coordinates**.
-/
import GaloisForLFunctions.HTGeometry.GeneralEndpointGenericIntersection

open Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ} {S : Type*} [Fintype S] [DecidableEq S]

omit [DecidableEq S] in
/-- A linear matrix family is analytic in its complex coefficients. -/
theorem analyticAt_linearMatrixFamily (B : Fin N → Matrix S S ℂ) (θ₀ : Fin N → ℂ) :
    AnalyticAt ℂ (fun θ : Fin N → ℂ => ∑ a, θ a • B a) θ₀ := by
  refine analyticAt_matrix_of_entries fun i j => ?_
  have hfun : (fun θ : Fin N → ℂ => (∑ a, θ a • B a) i j)
      = fun θ : Fin N → ℂ => ∑ a, θ a * B a i j := by
    funext θ
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun a _ => by simp
  rw [hfun]
  refine Finset.analyticAt_fun_sum _ fun a _ => ?_
  refine AnalyticAt.mul ?_ analyticAt_const
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) a).analyticAt θ₀

/-- **Analytic eigenvalue branches of a linear family at a base point with simple spectrum.** -/
theorem exists_analyticBranches_linearFamily (B : Fin N → Matrix S S ℂ) (θ₀ : Fin N → ℂ)
    {U : Matrix S S ℂ} (hU1 : Uᴴ * U = 1) (energy : S → ℂ) (hinj : Function.Injective energy)
    (hbase : Uᴴ * (∑ a, θ₀ a • B a) * U = Matrix.diagonal energy) (x : S) :
    ∃ branch : (Fin N → ℂ) → ℂ, AnalyticAt ℂ branch θ₀ ∧ branch θ₀ = energy x ∧
      ∀ᶠ θ in 𝓝 θ₀, matrixCharpolyRelation ((∑ a, θ a • B a), branch θ) = 0 :=
  exists_analyticBranch_of_unitaryDiagonal (analyticAt_linearMatrixFamily B θ₀) hU1 energy hinj
    hbase x

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The canonical eigenvector family read in real coordinates. -/
def realEndpointEigenvector (H : (Fin N → ℂ) → Matrix (A × Bool) (A × Bool) ℂ)
    (branch : (A × Bool) → (Fin N → ℂ) → ℂ) (x : A × Bool) (q : Fin N → ℝ) : A × Bool → ℂ :=
  endpointEigenvector H branch x (fun a => ((q a : ℝ) : ℂ))

/-- **The induction step of Lemma A1 in real coordinates.**  Restricting the analytic eigenvector
family along the real embedding keeps it continuous, so endpoint visibility is open on the real
coordinate space and meets every dense set there. -/
theorem exists_mem_dense_realParameter_endpointComplete
    {H : (Fin N → ℂ) → Matrix (A × Bool) (A × Bool) ℂ} {q₀ : Fin N → ℝ}
    (hH : AnalyticAt ℂ H (fun a => ((q₀ a : ℝ) : ℂ)))
    {branch : (A × Bool) → (Fin N → ℂ) → ℂ}
    (hbranch : ∀ x, AnalyticAt ℂ (branch x) (fun a => ((q₀ a : ℝ) : ℂ)))
    (hcomplete : ∀ p : (A × Bool) × (A × Bool), p.1 ≠ p.2 →
      layerReducedTransition (realEndpointEigenvector H branch p.1 q₀)
        (realEndpointEigenvector H branch p.2 q₀) ≠ 0)
    {Good : Set (Fin N → ℝ)} (hdense : Dense Good) :
    ∃ q ∈ Good, ∀ p : (A × Bool) × (A × Bool), p.1 ≠ p.2 →
      layerReducedTransition (realEndpointEigenvector H branch p.1 q)
        (realEndpointEigenvector H branch p.2 q) ≠ 0 := by
  refine exists_mem_dense_forall_layerReducedTransition_ne_zero (p₀ := q₀)
    (realEndpointEigenvector H branch) ?_ hcomplete hdense
  intro i y
  have hcoe : ContinuousAt (fun q : Fin N → ℝ => (fun a => ((q a : ℝ) : ℂ))) q₀ := by
    refine continuousAt_pi.mpr fun a => ?_
    exact (Complex.continuous_ofReal.comp (continuous_apply a)).continuousAt
  have hg : ContinuousAt
      (fun p : Fin N → ℂ => (Matrix.scalar (A × Bool) (branch i p) - H p).adjugate y i)
      (fun a => ((q₀ a : ℝ) : ℂ)) :=
    (analyticAt_generalAdjugateColumn hH (hbranch i) i y).continuousAt
  exact ContinuousAt.comp
    (g := fun p : Fin N → ℂ => (Matrix.scalar (A × Bool) (branch i p) - H p).adjugate y i)
    (f := fun q : Fin N → ℝ => fun a => ((q a : ℝ) : ℂ)) (x := q₀) hg hcoe

end

end GaloisForLFunctions.HTGeometry
