import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.Kinematics.DurationTails
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.Kinematics.DurationUpper

/-! # All fixed scalar residence quantiles have the same thermodynamic scale -/
open MeasureTheory Filter Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
open EmptyVisitFlux SharpOccupation
noncomputable section

/-- The entry-count survival fraction crosses each prescribed level between
two deterministic multiples of 2πr/(D√N), at every fixed outer tolerance.
Both fractions use the same first crossing and the same observation record. -/
theorem gaussian_residence_quantiles {q : ℝ} (hq : q∈Ioo (0:ℝ) 1) :
    ∃ a B : ℝ, 0 < a ∧ 0 < B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D : ℕ := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let E := fun i => -H.2.isHermitian.eigenvalues i
      ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        ∀ ρ∈Ioo (0:ℝ) (sqrt 2), let r := physicalArc ρ
          let unitTime := 2*π*r/((D:ℝ)*sqrt N)
          let A := entriesAfter E r σ
          ∀ᶠ T : ℝ in atTop,
            ((longVisits (visitSet H 0 ρ) (B*unitTime) (A T)).card:ℝ)/(A T).card < q ∧
            q < ((longVisits (visitSet H 0 ρ) (a*unitTime) (A T)).card:ℝ)/(A T).card := by
  let h := (1-q)/4
  have hh : 0 < h := div_pos (sub_pos.mpr hq.2) (by norm_num)
  let b := sqrt (48/h)
  have hb : 0 < b := sqrt_pos.mpr (div_pos (by norm_num) hh)
  let a := h/(2*b)
  have ha : 0 < a := div_pos hh (mul_pos two_pos hb)
  have hab : a*b < h := by
    rw [show a*b=h/2 by dsimp only [a]; field_simp [hb.ne']]
    exact half_lt_self hh
  have hsin : exp (-(b^2/48))≤h := by
    rw [show b^2=48/h from sq_sqrt (div_pos (by norm_num) hh).le,
      show 48/h/48=(1:ℝ)/h by ring,Real.exp_neg,inv_eq_one_div,div_le_iff₀ (exp_pos _)]
    have hm := mul_le_mul_of_nonneg_left (add_one_le_exp (1/h)) hh.le
    rw [mul_add,show h*(1/h)=1 by field_simp [hh.ne'],mul_one] at hm
    linarith only [hm,hh]
  have hql : q < exp (-h)-exp (-(b^2/48)) := by
    have he := add_one_le_exp (-h)
    dsimp only [h] at he hsin
    dsimp only [h]
    linarith only [he,hsin,hq.2]
  let B := sqrt (48*π)/(12*q)
  have hB : 0 < B := by dsimp only [B]; exact div_pos (by positivity) (mul_pos (by norm_num) hq.1)
  have hqu : sqrt (48*π)/(24*B) < q := by
    rw [show sqrt (48*π)/(24*B)=q/2 by dsimp only [B]; field_simp [hq.1.ne',(by positivity : sqrt (48*π)≠0)]; ring]
    exact half_lt_self hq.1
  refine ⟨a,B,ha,hB,?_⟩
  filter_upwards [gaussian_residence_tail_lower,gaussian_residence_tail_upper] with ω hl hu
  filter_upwards [hl a b h q ha hb hab hql,hu B q hB hqu] with k hk hk'
  intro N D H P E
  obtain ⟨σ,hσ,he,hprior,hlo⟩ := hk
  obtain ⟨σ',hσ',he',hprior',hhi⟩ := hk'
  have heq : σ=σ' := le_antisymm
    (le_of_not_gt fun hh => ((hprior σ' ⟨hσ'.le,hh⟩).ne he'))
    (le_of_not_gt fun hh => ((hprior' σ ⟨hσ.le,hh⟩).ne he))
  subst σ'
  refine ⟨σ,hσ,he,hprior,?_⟩
  intro ρ hρ r unitTime A
  filter_upwards [hhi ρ hρ,hlo ρ hρ] with T hB' ha'
  have time (z : ℝ) : z*unitTime=2*π*r*z/((D:ℝ)*sqrt N) := by dsimp only [unitTime]; ring
  rw [time B,time a]
  exact ⟨hB',ha'⟩

#print axioms gaussian_residence_quantiles
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
