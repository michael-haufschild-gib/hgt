import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.SimultaneousReturns
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Simultaneous scalar occupation from three spins up to the largest prefix -/

open MeasureTheory Set Filter Topology Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
open SharpOccupation
noncomputable section

/-- Across n successive registers beginning at three spins there are
exactly 2^(n+3)−n−8 independent relative phases. -/
private theorem common_mass (n : ℕ) (x : ℝ) :
    (∏ j : Fin n, zeroGateArcDensity (2^(j.val+3)) x) =
      (2:ℝ)^(n*(n+5)/2)*x^(2^(n+3)-(n+8)) := by
  have hd (m : ℕ) : m+8≤2^(m+3) := by
    induction m with
    | zero => norm_num
    | succ m ih => rw [show m+1+3=m+3+1 by omega,pow_succ]; omega
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    change (∏ j : Fin n, zeroGateArcDensity (2^(j.val+3)) x)*zeroGateArcDensity (2^(n+3)) x=_
    rw [ih,zeroGateArcDensity,Nat.cast_pow,Nat.cast_ofNat]
    have ha : (n+1)*((n+1)+5)/2=n*(n+5)/2+(n+3) := by
      rw [show (n+1)*((n+1)+5)=n*(n+5)+2*(n+3) by ring]
      omega
    have hb : 2^(n+1+3)-(n+1+8)=(2^(n+3)-(n+8))+(2^(n+3)-1) := by
      have hbound := hd n
      rw [show n+1+3=n+3+1 by omega,pow_succ]
      omega
    rw [ha,hb,pow_add,pow_add]
    ring

/-- For one frozen chain, the fraction of times when all n prefixes fit
the empty circuit at the same physical error has an explicit power law.
Its exponent is twice the largest Hilbert dimension minus n+8. -/
theorem gaussian_common_error_returns :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (n : ℕ) (ε a : ℝ), ε∈Ioo (0:ℝ) (sqrt 2) →
      let H (j : Fin n) : selfAdjoint (Matrix (Config j.val) (Config j.val) ℂ) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω (j.val+1)),isSelfAdjoint_pathHamiltonian _⟩
      let B := {t : ℝ | ∀ j : Fin n, orbitCircuitDistance (H j) 0 t≤ε}
      Tendsto (fun T => volume.real (B∩Icc a T)/(T-a)) atTop
        (𝓝 ((2:ℝ)^(n*(n+5)/2)*(physicalArc ε)^(2^(n+3)-(n+8)))) := by
  filter_upwards [gaussian_simultaneous_empty_returns] with ω hω
  intro n ε a he H B
  obtain ⟨hx,htol⟩ := physicalArc_spec he.1 he.2
  let x : Icc (0:ℝ) (1/2) := ⟨physicalArc ε,hx.1.le,hx.2.le⟩
  let r : Icc (0:ℝ) 1 := ⟨x,x.property.1,x.property.2.trans (by norm_num)⟩
  have hp (j : Fin n) : zeroGateArcOccupationPolynomial (2^(j.val+3)) r =
      zeroGateArcDensity (2^(j.val+3)) (physicalArc ε) := by
    rw [←zeroGateFullArcMass_eq_exactPolynomial]
    simpa only [zeroGateFullArcMass,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,r,x] using
      relativeUnitArcMass_eq_power (fun _ : Fin (j.val+3) => false) x
  have hb : (⋂ j : Fin n, zeroGateReturnSet (H j) r)=B := by
    ext t
    simp only [mem_iInter,zeroGateReturnSet,mem_setOf_eq,r,x,htol,B]
  have h := hω n (fun _ => r) a
  change Tendsto (fun T => volume.real ((⋂ j : Fin n, zeroGateReturnSet (H j) r)∩Icc a T)/(T-a))
    atTop (𝓝 (∏ j : Fin n, zeroGateArcOccupationPolynomial (2^(j.val+3)) r)) at h
  simpa only [hb,hp,common_mass] using h

#print axioms gaussian_common_error_returns
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
