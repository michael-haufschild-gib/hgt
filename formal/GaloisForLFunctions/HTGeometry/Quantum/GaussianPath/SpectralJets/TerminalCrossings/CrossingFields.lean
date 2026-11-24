import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.TerminalCrossings.BoundaryTransitions
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.JointFrequencies

/-! # Unique field settings and connected transitions of the two spin sectors -/

open Matrix Set MeasureTheory Finset
namespace GaloisForLFunctions.HTGeometry.SpectralJets.TerminalCrossings
open UntouchedSites BoundaryField
noncomputable section

private theorem diff_injective {I : Type*} [Fintype I] [DecidableEq I] (E F : I→ℝ)
    (h : ∀ p q : I→ℤ, ∑ i, p i=0 → ∑ i, q i=0 →
      (∑ i, (p i:ℝ)*E i)+(∑ i, (q i:ℝ)*F i)=0 → p=0 ∧ q=0) :
    Function.Injective (fun pair : I×I => E pair.1-F pair.2) := by
  classical
  let d (a b j : I) : ℤ := (if a=j then 1 else 0)-(if b=j then 1 else 0)
  have hb (a b : I) : ∑ j, d a b j=0 := by simp [d,sum_sub_distrib]
  have he (a b : I) (G : I→ℝ) : (∑ j, (d a b j:ℝ)*G j)=G a-G b := by
    simp [d,Int.cast_sub,sub_mul,sum_sub_distrib,ite_mul]
  have hz (a b : I) (hh : d a b=0) : a=b := by
    by_contra hab
    have hh' := congrFun hh a
    simp [d,hab.symm] at hh'
  rintro ⟨a,b⟩ ⟨c,d'⟩ hval
  change E a-F b=E c-F d' at hval
  obtain ⟨hp,hq⟩ := h (d a c) (d d' b) (hb ..) (hb ..) (by rw [he,he]; linarith only [hval])
  exact Prod.ext (hz _ _ hp) (hz _ _ hq).symm

/-- With all other coefficients frozen, every pair of opposite-sector
energy levels has its own crossing field outside a countable set of
longitudinal bond strengths. Identity and the transverse boundary terms
connect these sector labels at the isolated crossings. -/
theorem gaussian_isolated_boundary_crossings :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let I := Fin (k+3)→Bool
      let hH := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian
      let V := hH.eigenvectorUnitary
      ∃ B : Set ℝ, B.Countable ∧ ∀ t∉B,
        let hF := boundaryHermitian ω k t
        let W := hF.eigenvectorUnitary
        let field := fun p : I×I => (hF.eigenvalues p.2-hH.eigenvalues p.1)/2
        Function.Injective field ∧
          (∀ p : I×I, ∀ h : ℝ, hH.eigenvalues p.1+h=hF.eigenvalues p.2-h ↔ h=field p) ∧
          ∀ d e : I→ℂ,
            (∀ A : SpinMatrix (Fin (k+3)), A=1 ∨ (∃ a : Fin 3, A=spin (Fin.last (k+2)) a) →
              ∀ i j, (star V.val*A*W.val) i j≠0 → d i=e j) →
            ∃ c : ℂ, (∀ i, d i=c) ∧ ∀ j, e j=c := by
  filter_upwards [gaussian_boundary_joint_nonresonance,gaussian_boundary_transition_labels] with ω hj hconn k
  intro I hH V
  obtain ⟨B,hB,hgood⟩ := hj k
  refine ⟨B,hB,fun t ht => ?_⟩
  intro hF W field
  have hinj := diff_injective hH.eigenvalues hF.eigenvalues (hgood t ht)
  refine ⟨?_,?_,hconn (k+1) (Fin.last (k+2)) W⟩
  · intro p q hh
    apply hinj
    change (hF.eigenvalues p.2-hH.eigenvalues p.1)/2=(hF.eigenvalues q.2-hH.eigenvalues q.1)/2 at hh
    change hH.eigenvalues p.1-hF.eigenvalues p.2=hH.eigenvalues q.1-hF.eigenvalues q.2
    linarith only [hh]
  intro p h
  dsimp only [field]
  constructor <;> intro hh <;> linarith only [hh]

#print axioms gaussian_isolated_boundary_crossings
end
end GaloisForLFunctions.HTGeometry.SpectralJets.TerminalCrossings
