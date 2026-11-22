import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.CircuitWindows.RecordBound
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.GaussianRate
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Doubly exponential polynomial-budget waits from counted scalar entries -/
open Real Set Filter MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.CircuitWindows
open EmptyVisitFlux SharpOccupation Depth SpectralGapMass
noncomputable section

private theorem power_bound {R m x b g d : ℝ} {D : ℕ} (hD : 2 ≤ D) (hR : 0 < R)
    (hm : 0 ≤ m) (hd : d^2 ≤ m*R) (hx : 0 < x) (hx' : x ≤ 1) (hb : 0 < b) (hg : 1 ≤ g) :
    b^D*(d^2+(g^D+1)*R)/(x^(D-2)*R) < (m+3)*(g*b/x)^D := by
  have hW := one_le_pow₀ hg (n:=D)
  have hmass : d^2+(g^D+1)*R ≤ (m+2)*g^D*R := by
    have hv := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hW (show 0 ≤ m+1 by linarith only [hm])) hR.le
    linarith only [hd,hv]
  have hpow : x^(D-2)*x^2=x^D := by rw [←pow_add, Nat.sub_add_cancel hD]
  have hsmall : x^2 ≤ 1 := pow_le_one₀ hx.le hx'
  have hv : 0 < g*b/x := div_pos (mul_pos (zero_lt_one.trans_le hg) hb) hx
  calc
    _ ≤ b^D*((m+2)*g^D*R)/(x^(D-2)*R) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (pow_pos hb _).le)
        (mul_pos (pow_pos hx _) hR).le
    _ = ((m+2)*(g*b/x)^D)*x^2 := by
      rw [div_pow,mul_pow,←hpow]
      field_simp [hR.ne',hx.ne']
    _ ≤ (m+2)*(g*b/x)^D := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall
        (show 0 ≤ (m+2)*(g*b/x)^D by positivity)
    _ < _ := mul_lt_mul_of_pos_right (by linarith) (pow_pos hv _)

/-- The fraction of actual outer scalar entries with any inner circuit
visit during the next gᴰ time units decays exponentially in D. Both
tolerances are fixed and every subcritical gate budget is allowed. -/
theorem gaussian_physical_circuit_forward_wait :
    ∃ K : ℝ, 0 < K ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ (s : ℕ→ℕ), subcriticalBudget s → ∀ ε∈Ioo (0:ℝ) (sqrt 2),
      ∀ ρ∈Ioo (0:ℝ) (sqrt 2), ∀ g : ℝ, 1 ≤ g →
      ∀ q∈Ioo (g*physicalArc ε/physicalArc ρ) 1, ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        let P := nearHilbertContinuousCircuitBudget N
        let E := fun i => -H.2.isHermitian.eigenvalues i
        ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧
          (∀ t∈Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧ ∀ j ≤ s N,
          ∀ᶠ T : ℝ in atTop,
            let A := entriesAfter E (physicalArc ρ) σ T
            ((followed A (visitSet H j ε) (g^D)).card:ℝ)/(A.card:ℝ) < 
              K*q^D := by
  obtain ⟨c,C,hc,_,hR⟩ := gaussian_pair_rate_scale
  refine ⟨c⁻¹+3,by positivity,?_⟩
  filter_upwards [hR,gaussian_first_crossing_flux,gaussian_physical_return_rates] with ω hr hf hs
  intro s hsub ε hε ρ hρ g hg q hq
  let x := physicalArc ρ
  have hx : x∈Ioo (0:ℝ) (1/2) := (physicalArc_spec hρ.1 hρ.2).1
  have hy := (physicalArc_spec hε.1 hε.2).1
  have hg' := zero_lt_one.trans_le hg
  let b := q*x/g
  have hxb : physicalArc ε < b := (lt_div_iff₀ hg').mpr
    (by simpa only [mul_comm g] using (div_lt_iff₀ hx.1).mp hq.1)
  have hb := hy.1.trans hxb
  have hqeq : g*b/x=q := by dsimp only [b]; field_simp [hg'.ne',hx.1.ne']
  have hh := hs s hsub ε hε (physicalArc ε/2) b (half_pos hy.1) (half_lt_self hy.1) hxb
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hr,hf,hh] with k hr hf hh
  intro N D H P E
  obtain ⟨σ,hσ,he,hbefore,hrates⟩ := hf
  refine ⟨σ,hσ,he,hbefore,?_⟩
  intro j hj
  obtain ⟨_,t,ht,hsp⟩ := hh j hj σ
  obtain ⟨hmem,hflux⟩ := hrates ρ hρ.1 hρ.2
  let R := pairTurnRate E
  have hN : 1 ≤ (N:ℝ) := by dsimp only [N]; exact_mod_cast (show 1 ≤ k+3 by omega)
  have hD : 0 < (D:ℝ) := by dsimp only [D]; positivity
  have hD' : 2 ≤ D := by
    simpa only [D,N,pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ k+3 by omega)
  have hd : (Fintype.card (Fin N→Bool):ℝ)=(D:ℝ) := by simp [D]
  have hlow : c*(D:ℝ)^2*sqrt N ≤ R := by
    simpa only [D,Nat.cast_pow,Nat.cast_ofNat] using hr.1
  have hlow' : c*(D:ℝ)^2 ≤ R := (le_mul_of_one_le_right
    (mul_nonneg hc.le (sq_nonneg _)) (by simpa only [sqrt_one] using sqrt_le_sqrt hN)).trans hlow
  have hp : 0 < R := (mul_pos hc (pow_pos hD _)).trans_le hlow'
  have hmass : (D:ℝ)^2 ≤ c⁻¹*R := by
    rw [←div_eq_inv_mul,le_div_iff₀ hc]
    simpa only [mul_comm c] using hlow'
  apply fraction_from_records E x σ (g^D) (x^(D-2)*R) (b^D)
    (pow_nonneg (zero_le_one.trans hg) _) (mul_pos (pow_pos hx.1 _) hp) (pow_pos hb _)
    _ t ht.1 ht.2 (hsp.mono fun i h => h.1)
    (fun T u hu => ⟨((hmem u T).mp hu).1.le,((hmem u T).mp hu).2.1⟩) hflux
  change b^D*((Fintype.card (Fin N→Bool):ℝ)^2+(g^D+1)*R)/(x^(D-2)*R) < _
  rw [hd,←hqeq]
  exact power_bound hD' hp (inv_nonneg.mpr hc.le) hmass hx.1 (hx.2.le.trans (by norm_num)) hb hg

#print axioms gaussian_physical_circuit_forward_wait
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.CircuitWindows
