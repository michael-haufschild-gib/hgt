import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.LimitLaw.MeanGap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.EntryStatistics

/-! # Exact large-chain prefactor for entries to the empty-circuit region -/
open MeasureTheory Filter Finset Real Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
open EmptyVisitFlux SharpOccupation
noncomputable section

private theorem absolute_rate {I : Type*} [Fintype I] (E : I→ℝ) :
    4*π*pairTurnRate (fun i => -E i)=∑ p : I×I, |E p.1-E p.2| := by
  have he (a b : ℝ) : 2*max 0 (-a- -b)=|a-b|+(b-a) := by
    rcases le_total a b with h|h
    · rw [max_eq_right (by linarith only [h]),abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_left (by linarith only [h]),abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  have hz : (∑ p : I×I, (E p.2-E p.1))=0 := by
    rw [Fintype.sum_prod_type]
    simp only [sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,←mul_sum,sub_self]
  rw [pairTurnRate,←sum_div]
  calc
    _ = ∑ p : I×I, 2*max 0 (-E p.1- -E p.2) := by rw [←mul_sum]; field_simp; ring
    _ = _ := by simp only [he,sum_add_distrib,hz,add_zero]

/-- The Gaussian mean absolute gap fixes the leading coefficient in the
entry rate at every scalar tolerance below √2. The tolerance factor
is the exact angular occupation term x^(D−2). -/
theorem gaussian_entry_flux_prefactor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, Tendsto (fun n : ℕ =>
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)).isHermitian.eigenvalues
      pairTurnRate (fun i => -E i)/(((2:ℝ)^(n+2))^2*sqrt (n+2:ℕ)))
      atTop (𝓝 (12/(π*sqrt (48*π)))) := by
  filter_upwards [gaussian_mean_absolute_gap] with ω hw
  have hh := hw.div_const (4*π)
  rw [show 48/sqrt (48*π)/(4*π)=12/(π*sqrt (48*π)) by ring] at hh
  refine hh.congr fun n => ?_
  let u := pathPauliDisorderShell ω n
  let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
  let D := (2:ℝ)^(n+2)
  let v := sqrt (n+2:ℕ)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hv : 0 < v := by dsimp only [v]; positivity
  rw [integral_listLaw]
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_mul,
    Nat.cast_pow,Nat.cast_ofNat,scaledGap,scaledEnergy,←sub_div,abs_div,←sum_div]
  change (D*D)⁻¹*((∑ p : (Fin (n+2)→Bool)×(Fin (n+2)→Bool), |E p.1-E p.2|)/|v|)/(4*π) =
    pairTurnRate (fun i => -E i)/(D^2*v)
  rw [abs_of_pos hv,←absolute_rate E]
  field_simp [hv.ne',hD.ne']

/-- From the actual first near-Hilbert crossing, normalized scalar-entry
frequency and inverse normalized residence converge to the same constant.
The long-time observation limit is taken on each fixed prefix first. -/
theorem gaussian_first_crossing_entry_constant :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∃ R : ℕ → ℝ, Tendsto R atTop (𝓝 (12/(π*sqrt (48*π)))) ∧
      ∀ᶠ k : ℕ in atTop, let N := k+3
        let D : ℕ := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        let E := fun i => -H.2.isHermitian.eigenvalues i
        let P := nearHilbertContinuousCircuitBudget N
        ∃ σ > 0, orbitCircuitDistance H P σ=9/80 ∧
          (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
          ∀ ε ∈ Ioo (0:ℝ) (sqrt 2), let x := physicalArc ε
            let F := entriesAfter E x σ
            Tendsto (fun T : ℝ => ((F T).card:ℝ)/(T-σ)) atTop
              (𝓝 (x^(D-2)*((D:ℝ)^2*sqrt N)*R k)) ∧
            Tendsto (fun T : ℝ => volume.real (visitSet H 0 ε ∩ Icc σ T)/(F T).card)
              atTop (𝓝 (x/((D:ℝ)*sqrt N*R k))) := by
  obtain ⟨c,C,hc,hC,hvis⟩ := gaussian_crossing_rate_and_residence
  filter_upwards [gaussian_entry_flux_prefactor,hvis] with ω hh hw
  let R (k : ℕ) :=
    let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
    pairTurnRate (fun i => -E i)/(((2:ℝ)^(k+3))^2*sqrt (k+3:ℕ))
  have hR : Tendsto R atTop (𝓝 (12/(π*sqrt (48*π)))) := hh.comp (tendsto_add_atTop_nat 1)
  refine ⟨R,hR,?_⟩
  filter_upwards [hw,hR.eventually_const_lt (by positivity : (0:ℝ) < 12/(π*sqrt (48*π)))] with k hk hp
  intro N D H E P
  obtain ⟨σ,hσ,he,hb,h⟩ := hk
  refine ⟨σ,hσ,he,hb,fun ε hε => ?_⟩
  intro x F
  have hd : 0 < (D:ℝ) := by dsimp only [D]; positivity
  have hv : 0 < sqrt (N:ℝ) := by dsimp only [N]; positivity
  have hr : R k=pairTurnRate E/((D:ℝ)^2*sqrt N) := by
    simp only [R,D,N,H,E,Nat.cast_pow,Nat.cast_ofNat]
  have hh' := h ε hε
  have hscale := (eq_div_iff (mul_pos (pow_pos hd 2) hv).ne').mp hr
  constructor
  · rw [mul_assoc,mul_comm ((D:ℝ)^2*sqrt N) (R k),hscale]
    exact hh'.1
  · have hres : x/((D:ℝ)*sqrt N*R k)=(D:ℝ)*x/pairTurnRate E := by
      rw [←hscale]
      field_simp [hd.ne',hv.ne',hp.ne']
    rw [hres]
    exact hh'.2.2.1

#print axioms gaussian_entry_flux_prefactor
#print axioms gaussian_first_crossing_entry_constant
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
