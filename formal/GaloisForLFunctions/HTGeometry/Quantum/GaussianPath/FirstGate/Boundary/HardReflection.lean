import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.SpectralAlgebra
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.GaussianMaximumQuantiles

/-! # Hard spectral reflections in the algebra of the dephased boundary Z -/
open Matrix Polynomial MeasureTheory Filter
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section

/-- Almost surely on every sufficiently long prefix some sign-valued polynomial
of the dephased first-site Z stays farther than 11/25 from the whole
near-Hilbert circuit budget, up to any global phase. -/
theorem gaussian_firstZ_hard_reflection :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let p := pathPauliDisorderShell ω n
      let V := (isSelfAdjoint_pathHamiltonian p).isHermitian.eigenvectorUnitary
      let z := firstZProfile p
      ∃ Q : Polynomial ℂ, Q.degree < (2^N:ℕ) ∧ (∀ j, Q.eval (z j)=1 ∨ Q.eval (z j) = -1) ∧
        ProjectiveCircuitSeparated N (11/25) (nearHilbertContinuousCircuitBudget N)
          (aeval (spectralFunction V z) Q) := by
  filter_upwards [gaussian_firstZ_distinguishes] with ω hω
  have hn : Tendsto (fun n : ℕ => n+2) atTop atTop := tendsto_add_atTop_nat 2
  filter_upwards [hn.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier]
    with n hent
  intro N p V z
  classical
  let d := 2^N-1
  let e : (Fin N→Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans (finCongr (by
    simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
    have hp := Nat.two_pow_pos N
    dsimp [d]; omega))
  obtain ⟨x,hx⟩ := exists_coarsely_separated_spectral_reflection e V hent
  let f := anchoredBooleanPacket x ∘ e
  have hz : Function.Injective z := fun _ _ hij => hω n (congrArg Complex.re hij)
  have hi : Set.InjOn z (↑(Finset.univ : Finset (Fin N→Bool))) := hz.injOn
  let Q := Lagrange.interpolate Finset.univ z f
  have hQ (j) : Q.eval (z j)=f j := Lagrange.eval_interpolate_at_node f hi (Finset.mem_univ j)
  refine ⟨Q,by simpa only [Fintype.card_fun,Finset.card_univ,Fintype.card_bool,Fintype.card_fin] using
    Lagrange.degree_interpolate_lt f hi,?_,?_⟩
  · intro j
    rw [hQ]
    change anchoredBooleanPacket x (e j)=1 ∨ anchoredBooleanPacket x (e j) = -1
    generalize e j = k
    refine Fin.cases (Or.inl rfl) (fun i => ?_) k
    by_cases h : x i <;> simp [anchoredBooleanPacket,h]
  · rw [spectral_aeval,show (fun j => Q.eval (z j))=f from funext hQ]
    exact hx

#print axioms gaussian_firstZ_hard_reflection
end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary
