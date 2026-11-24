import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.FullRange.FiniteWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # Simultaneous occupation and first-record spacing on finite physical windows -/
open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
noncomputable section

/-- Full inverse of the phase chord on positive operator errors below two. -/
theorem physicalArc_full {ε : ℝ} (hε : ε∈Ioo (0:ℝ) 2) :
    physicalArc ε∈Ioo (0:ℝ) 1 ∧ zeroGateArcTolerance (physicalArc ε)=ε := by
  have hpos := Real.arcsin_pos.mpr (half_pos hε.1)
  have hn : -1≤ε/2 := by linarith only [hε.1]
  have h1 : ε/2<1 := by linarith only [hε.2]
  have hlt := Real.arcsin_lt_arcsin hn h1 le_rfl
  rw [Real.arcsin_one] at hlt
  constructor
  · exact ⟨div_pos (mul_pos zero_lt_two hpos) Real.pi_pos,
      (div_lt_iff₀ Real.pi_pos).mpr (by linarith only [hlt])⟩
  · unfold zeroGateArcTolerance physicalArc
    rw [show Real.pi*(2*Real.arcsin (ε/2)/Real.pi)/2 = Real.arcsin (ε/2) by field_simp [Real.pi_ne_zero],
      Real.sin_arcsin hn h1.le]
    ring

/-- At the prescribed operator error, one deterministic observation horizon
gives the sharp occupation exponent and the reciprocal spacing exponent for
records begun at any origin, including the actual first crossing. -/
theorem gaussian_finite_physical_rates_full :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ, subcriticalBudget s →
      ∀ ε ∈ Ioo (0:ℝ) 2, ∀ l b : ℝ, 0 < l → l < physicalArc ε → physicalArc ε < b →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D : ℕ := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        let G := 2*(2:ℝ)^(D^c)
        ∀ j ≤ s N, ∀ a : ℝ,
          (∀ T ≥ G, l^D < visitFraction H j ε a (a+T) ∧ visitFraction H j ε a (a+T) < b^D) ∧
          ∃ t, records H j ε a t ∧ ∀ i : ℕ, 0 < i → G ≤ t i-a →
            1/b^D < (t i-a)/i ∧ (t i-a)/i < 1/l^D := by
  obtain ⟨c,hc⟩ := gaussian_finite_occupation_full
  refine ⟨c,?_⟩
  filter_upwards [hc,gaussian_unit_hit_enlargement] with ω hocc hunit
  intro s hs ε hε l b hl hlx hxb
  let x := physicalArc ε
  obtain ⟨hx,htol⟩ := physicalArc_full hε
  obtain ⟨y,hxy,hyb⟩ := exists_between (lt_min hxb hx.2)
  have hy : y ∈ Ioo (0:ℝ) 1 := ⟨hx.1.trans hxy,hyb.trans_le (min_le_right ..)⟩
  have hδ : 0 < zeroGateArcTolerance y-ε := by
    rw [←htol]
    exact sub_pos.mpr (strictMonoOn_zeroGateArcTolerance_full ⟨hx.1.le,hx.2.le⟩ ⟨hy.1.le,hy.2.le⟩ hxy)
  filter_upwards [hocc s hs x hx l b hl hlx hxb,
    hocc (fun n => s n+n^4) (subcritical_add_pow_four hs) y hy l b hl (hlx.trans hxy)
      (hyb.trans_le (min_le_left ..)),hunit _ hδ] with k hlow hhigh hw
  intro N D H G j hj a
  have hobs (T : ℝ) (hT : G ≤ T) := hlow j hj a T hT
  change zeroGateArcTolerance x=ε at htol
  simp only [htol] at hobs
  refine ⟨hobs,?_⟩
  let t (i : ℕ) : ℝ := Nat.rec a (fun _ v => PrecisionReturns.firstVisit H (v+1) j ε) i
  have ht : records H j ε a t := ⟨rfl,fun i => PrecisionReturns.firstVisit_isLeast H (t i+1) j hε.1⟩
  refine ⟨t,ht,fun i hi htime => ?_⟩
  have hi' : 0 < (i:ℝ) := Nat.cast_pos.mpr hi
  have hpos : 0 < t i-a := (show 0 < G by dsimp only [G]; positivity).trans_le htime
  have hsmall := (hobs _ htime).1
  have hlarge := (hhigh (j+N^4) (Nat.add_le_add_right hj _) a (t i-a) htime).2
  rw [show a+(t i-a)=t i by ring] at hsmall hlarge
  have henlarge := hw j ε
  rw [show ε+(zeroGateArcTolerance y-ε)=zeroGateArcTolerance y by ring] at henlarge
  obtain ⟨cover,pack⟩ := resolved_visit_occupation_bounds _ t a 1 1 zero_lt_one le_rfl ht.1 ht.2 i
  rw [mul_one] at cover pack
  have hpack := pack.trans (measureReal_mono (inter_subset_inter_left _ henlarge)
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne))
  have hupper := (div_lt_iff₀ hpos).mp hlarge
  have hlower := (lt_div_iff₀ hpos).mp hsmall
  constructor
  · rw [div_lt_div_iff₀ (pow_pos (hx.1.trans hxb) D) hi',one_mul,mul_comm (t i-a)]
    exact hpack.trans_lt hupper
  · rw [div_lt_div_iff₀ hi' (pow_pos hl D),one_mul]
    simpa only [mul_comm (t i-a)] using hlower.trans_le cover

#print axioms gaussian_finite_physical_rates_full
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
