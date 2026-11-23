import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.PolynomialExcess
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.FirstExcess

/-! # Polynomial deadline and sustained excess after the first low-cost return -/
open MeasureTheory Filter Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section
private abbrev chain (ω : PathPauliDisorder) (n : ℕ) : selfAdjoint (Register (n+2)) :=
  ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩

/-- From the first physical low-budget dip after the near-Hilbert crossing,
the first one-sweep-plus-excess crossing occurs by (h/c)^(1/56).
That same budget stays unaffordable throughout the rest of the unit window. -/
theorem gaussian_polynomial_first_rebound :
    ∃ c>0, ∀ h∈Ioc (0:ℝ) c, let t := (h/c)^((56:ℝ)⁻¹)
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ s q : ℕ,
        ((2*s+q:ℕ):ℝ)≤h*(n+1:ℕ) →
        let v := firstLowAfterCrossing ω n s
        let J := n+1+(s+q)
        let u := firstExcessAfter ω n (s+q) v (1/8)
        0≤u ∧ u≤t ∧ orbitCircuitDistance (chain ω n) J (v+u)=1/8 ∧
          (∀ x∈Ico 0 u, orbitCircuitDistance (chain ω n) J (v+x) < 1/8) ∧
          ∀ x∈Icc t 1, 1/8 < orbitCircuitDistance (chain ω n) J (v+x) := by
  obtain ⟨c,hc,H⟩ := gaussian_polynomial_gate_band
  refine ⟨c,hc,?_⟩
  intro h hh t
  have hbase := div_pos hh.1 hc
  have ht : t∈Ioc (0:ℝ) 1 := ⟨rpow_pos_of_pos hbase _,rpow_le_one hbase.le
    ((div_le_one hc).mpr hh.2) (by positivity)⟩
  have hid : c*t^56=h := by
    have hp : t^56=h/c := rpow_inv_natCast_pow hbase.le (by norm_num : (56:ℕ)≠0)
    rw [hp]
    field_simp [hc.ne']
  filter_upwards [H t ht] with ω hw
  filter_upwards [hw] with n hn
  intro s q hq v J u
  let K := chain ω n
  have hv : HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution K.val v) :=
    (PrecisionReturns.firstVisit_isLeast K _ s (by norm_num : (0:ℝ)<1/10)).1.2
  have excludes (x) (hx : x∈Icc t 1) :
      ¬HasProjectiveCircuitApproximation (n+2) (1/10+1/8) (s+J) (unitaryEvolution K.val x) := by
    rintro ⟨z,hz,C,hC,hE⟩
    have hh' := hn x hx (s+J) ⟨z,hz,C,hC,hE.trans (by norm_num)⟩
    rw [hid] at hh'
    dsimp only [J] at hh'
    push_cast at hh' hq
    linarith only [hh',hq]
  obtain ⟨h₀,hu,he,hbefore⟩ := firstExcessAfter_le_of_increment ω n s q ht.1.le
    (by norm_num : (1/10:ℝ)<1/8) hv (excludes t ⟨le_rfl,ht.2⟩)
  refine ⟨h₀,hu,he,hbefore,?_⟩
  intro x hx
  apply lt_of_not_ge
  intro hh'
  have hu' := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution K.val (v+x)) J (1/8)).mpr hh'
  have hback := HasProjectiveCircuitApproximation.neg_time (t:=v) K hv
  have hlag := affordable_add_time K (x:= -v) (y:=v+x) hback hu'
  rw [neg_add_cancel_left] at hlag
  exact excludes x hx hlag

#print axioms gaussian_polynomial_first_rebound
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
