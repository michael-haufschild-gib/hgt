import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.UniformCounts
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.ThreeGateMatch
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.SpectralSorting.WrapPhase
import GaloisForLFunctions.HTGeometry.FermionicZeroBraidLocalProductDiagonalization

/-! # Three gates suffice for the bounded-time physical spectrum after conjugation -/
open MeasureTheory Matrix Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
open ClockSpectrum _root_.RHTower.PrimeCirclePeriodization
noncomputable section

theorem expTurns_turns (z : AddCircle (2*Real.pi)) : expTurns (turns z)=fourier 1 z := by
  let R : ℝ := (AddCircle.equivIoc (2*Real.pi) 0 z).val
  have hR : phase 1 R=z := by
    simpa only [phase,mul_one] using (AddCircle.coe_equivIoc (p:=2*Real.pi) (a:=0) (y:=z))
  have hv : 2*Real.pi*turns z=R := by
    change (2*Real.pi)*(R/(2*Real.pi))=R
    field_simp [Real.pi_ne_zero]
  calc _ = Complex.exp ((R:ℂ)*Complex.I) := by rw [expTurns,hv]
       _ = fourier 1 (phase 1 R) := by simp only [fourier_phase,Int.cast_one,mul_one,Complex.ofReal_one,one_mul]
       _ = _ := congrArg _ hR

/-- The physical unitary is the diagonal matrix of sorted experimental
angles after a unitary basis change, for every permutation of the labels. -/
theorem sorted_physical_diagonal {n : ℕ} (u : PathShell n) (t : ℝ)
    (p : Equiv.Perm (Fin (n+2) → Bool)) :
    ∃ W : unitaryGroup (Fin (n+2) → Bool) ℂ,
      W.val*unitaryEvolution (pathHamiltonian u) t*star W.val=
      diagonal fun j => expTurns (physicalTurns u t (p j)) := by
  let h := (isSelfAdjoint_pathHamiltonian u).isHermitian
  let V := h.eigenvectorUnitary
  let S : unitaryGroup (Fin (n+2) → Bool) ℂ := ⟨p.permMatrix ℂ,permMatrix_mem_unitary p⟩
  let f (j) := Complex.exp (-(Complex.I*((t:ℂ)*h.eigenvalues j)))
  have he (j) : f j=expTurns (physicalTurns u t j) := by
    rw [physicalTurns,expTurns_turns,fourier_phase]
    dsimp only [f,h]
    congr 1
    push_cast
    ring
  refine ⟨S*V⁻¹,?_⟩
  rw [unitaryEvolution_spectral h]
  change (S.val*star V.val)*(V.val*diagonal f*star V.val)*star (S.val*star V.val)=_
  have hV : star V.val*V.val=1 := V.property.1
  rw [star_mul,star_star]
  calc _ = S.val*(star V.val*V.val)*diagonal f*(star V.val*V.val)*star S.val := by simp only [mul_assoc]
       _ = _ := by
         rw [hV,mul_one,mul_one]
         change p.permMatrix ℂ * diagonal f * star (p.permMatrix ℂ) = _
         rw [SpectralSorting.relabel_diagonal]
         exact congrArg Matrix.diagonal (funext fun j => he (p j))

/-- Along almost every frozen Gaussian chain, three gates eventually
suffice at error 1/10 after a free change of basis, simultaneously
at all dates in every compact positive interval. -/
theorem gaussian_three_gate_conjugate_upper :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a T : ℝ, 0 < a →
      ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc a T,
        ∃ W : unitaryGroup (Fin (n+2) → Bool) ℂ, HasProjectiveCircuitApproximation (n+2) (1/10) 3
          (W.val*unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t*star W.val) := by
  filter_upwards [gaussian_uniform_phase_counts] with ω hω
  intro a T ha
  filter_upwards [hω a T ha 512 (by decide) (1/512) (by norm_num),eventually_ge_atTop 7] with n hn hn'
  intro t ht
  let u := pathPauliDisorderShell ω n
  obtain ⟨p,hp⟩ := three_gate_of_cdf (by omega : 9 ≤ n+2) (physicalTurns u t)
    (fun j => ⟨(turns_mem _).1.le,(turns_mem _).2⟩) (fun j => hn t ht j)
  obtain ⟨W,hW⟩ := sorted_physical_diagonal u t p
  exact ⟨W,hW.symm ▸ hp⟩

#print axioms gaussian_three_gate_conjugate_upper
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
