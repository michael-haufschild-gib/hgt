import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Iterated.ScalarOccupation.InitialWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Iterated.PhysicalCharge
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FirstAscent
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateReturnSpacing

/-! # The observed initial scalar residence bounds all subsequent mean excursion times -/

open Set Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated.ScalarOccupation
open SharpOccupation
noncomputable section

/-- Up to each low visit, scalar occupation is at most one initial
one-fifth-error residence per excursion. The exact scalar occupation law
converts this into an upper bound for the physical mean cycle length. -/
theorem gaussian_initial_residence_mean_bound :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let D := 2^N
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ u>0, orbitCircuitDistance H P u=1/4 ∧ (∀ t∈Ico 0 u, orbitCircuitDistance H P t<1/4) ∧
        let M := volume.real (visitSet H 0 (1/5) ∩ Icc 0 u)
        ∀ s≤P/2, let v := lowDate H P s
          (∀ n : ℕ, volume.real (visitSet H 0 (1/10) ∩ Icc 0 (v n))≤(n:ℝ)*M) ∧
          ∀ p<zeroGateArcDensity D (physicalArc (1/10)), ∀ᶠ n : ℕ in atTop, p*v n<(n:ℝ)*M := by
  obtain ⟨_,hcycle⟩ := gaussian_cycle_windows
  obtain ⟨_,hasc⟩ := gaussian_first_ascent_occupation
  filter_upwards [hcycle,hasc,gaussian_path_all_prefixes_maximally_projective] with ω hω hhard hspec
  filter_upwards [hω,hhard] with k hk hc
  intro N D H P
  have hp : P≤D/(32*(N+1)) := Nat.div_le_div_left (by omega) (by positivity)
  obtain ⟨u,hu,he,hbefore,_⟩ := hc P hp (1/4) (by constructor <;> norm_num)
  refine ⟨u,hu,he,hbefore,?_⟩
  intro M s hs v
  let σ := highDate H P s
  obtain ⟨hdates,_⟩ := hk s hs
  have rise (i : ℕ) (t : ℝ) (ht : t∈Icc (v i) (σ i)) : orbitCircuitDistance H P t≤9/80 := by
    rcases ht.2.lt_or_eq with hlt|rfl
    · exact le_of_not_ge (fun hh => hlt.not_ge ((hdates i).2.2.1.2 ⟨ht.1,hh⟩))
    · exact (hdates i).2.1.le
  have post (i : ℕ) (t : ℝ) (_ : v i≤t) (ht : t<v (i+1)) (hfit : t∈visitSet H 0 (1/10)) : t<σ i := by
    by_contra! hh
    obtain ⟨z,hz,C,hC,h⟩ := hfit
    exact ht.not_ge ((hdates i).2.2.2.1.2 ⟨hh,z,hz,C,hC.trans (Nat.zero_le s),h⟩)
  have inc (i : ℕ) : v i+1≤v (i+1) := by have h := hdates i; linarith only [h.1,h.2.2.2.2.1]
  have hmono : Monotone v := monotone_nat_of_le_succ fun i => (le_add_of_nonneg_right zero_le_one).trans (inc i)
  have bound (n : ℕ) := scalar_record_charge H P v σ hmono rise post hu.le
    (by rw [he]; norm_num : 17/80<orbitCircuitDistance H P u) n
  refine ⟨bound,?_⟩
  intro p hp
  have hx := physicalArc_spec (by norm_num : (0:ℝ)<1/10) ((Real.lt_sqrt (by norm_num)).mpr (by norm_num))
  let r : Icc (0:ℝ) (1/2) := ⟨physicalArc (1/10),hx.1.1.le,hx.1.2.le⟩
  have hset : zeroGateReturnSet H r=visitSet H 0 (1/10) := by
    ext t
    change orbitCircuitDistance H 0 t≤zeroGateArcTolerance (physicalArc (1/10)) ↔ _
    rw [hx.2]
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).symm
  have hl := maximallyProjective_zeroGateOccupation_from_start H (hspec k) r 0
  rw [hset] at hl
  simp only [sub_zero] at hl
  have hnv (n : ℕ) : (n:ℝ)≤v n := by
    induction n with
    | zero => change (↑(0:ℕ):ℝ)≤0; norm_num
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (add_le_add_left ih 1).trans (inc n)
  have hv : Tendsto v atTop atTop := tendsto_atTop_mono hnv tendsto_natCast_atTop_atTop
  filter_upwards [(hl.comp hv).eventually_const_lt hp,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  have hvn : 0<v n := (show 0<(n:ℝ) by exact_mod_cast hnpos).trans_le (hnv n)
  exact ((lt_div_iff₀ hvn).mp hn).trans_le (bound n)

#print axioms gaussian_initial_residence_mean_bound
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated.ScalarOccupation
