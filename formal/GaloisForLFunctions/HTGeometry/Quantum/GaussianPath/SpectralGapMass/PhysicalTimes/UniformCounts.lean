import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.AngularBins

/-! # Uniform eigenvalue counts at angular grid points -/
open MeasureTheory Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section

/-- Count physical eigenlines below b turns, with multiplicity. -/
def phaseCount {n : ℕ} (u : PathShell n) (t b : ℝ) :=
  (Finset.univ.filter fun j => physicalTurns u t j<b).card

/-- Every fixed grid eventually has its predicted cumulative counts,
simultaneously at every date in each compact positive interval. -/
theorem gaussian_uniform_phase_counts :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a T : ℝ, 0<a → ∀ Q : ℕ, 0<Q → ∀ δ>0,
      ∀ᶠ n : ℕ in atTop, ∀ t∈Icc a T, ∀ j : Fin (Q+1),
        |(phaseCount (pathPauliDisorderShell ω n) t (j.val/(Q:ℝ)):ℝ)/(2:ℝ)^(n+2)-j.val/(Q:ℝ)|<δ := by
  classical
  filter_upwards [gaussian_angular_counts] with ω hω
  intro a T ha Q hQ δ hδ
  by_cases hT : a≤T
  · let P (n : ℕ) (t : ℝ) := ∀ j : Fin (Q+1),
        |(phaseCount (pathPauliDisorderShell ω n) t (j.val/(Q:ℝ)):ℝ)/(2:ℝ)^(n+2)-j.val/(Q:ℝ)|<δ
    let Bad (n : ℕ) := ∃ t∈Icc a T, ¬P n t
    let t (n : ℕ) := if h : Bad n then h.choose else a
    have ht (n : ℕ) : t n∈Icc a T := by
      by_cases h : Bad n
      · simpa only [t,dif_pos h] using h.choose_spec.1
      · simpa only [t,dif_neg h] using (show a∈Icc a T from ⟨le_rfl,hT⟩)
    have hgrid (j : Fin (Q+1)) : ∀ᶠ n : ℕ in atTop,
        |(phaseCount (pathPauliDisorderShell ω n) (t n) (j.val/(Q:ℝ)):ℝ)/(2:ℝ)^(n+2)-j.val/(Q:ℝ)|<δ := by
      have hq : 0<(Q:ℝ) := Nat.cast_pos.mpr hQ
      have hj : j.val/(Q:ℝ)∈Icc (0:ℝ) 1 :=
        ⟨by positivity,(div_le_one hq).mpr (by exact_mod_cast Nat.le_of_lt_succ j.isLt)⟩
      have h := Metric.tendsto_nhds.mp (hω a T ha t (Eventually.of_forall ht) _ hj) δ hδ
      simpa only [Real.dist_eq,angular_fraction,phaseCount] using h
    filter_upwards [eventually_all.mpr hgrid] with n hn
    intro u hu
    change P n u
    by_contra h
    have hb : Bad n := ⟨u,hu,h⟩
    have hp : P n (t n) := hn
    rw [show t n=hb.choose from dif_pos hb] at hp
    exact hb.choose_spec.2 hp
  · exact Eventually.of_forall fun _ _ ht => (hT (ht.1.trans ht.2)).elim

#print axioms gaussian_uniform_phase_counts
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
