import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ShortCircuitReplay.UniformReplay
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.MaximalError.PhysicalWindow

/-! # Uniform sublinear gate distance throughout a bounded physical horizon -/

open Filter MeasureTheory Set Real
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ShortCircuitReplay
open ThermodynamicEdges EnergyMesh
noncomputable section

private theorem budget_distance_le_two {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) (t : ℝ) :
    orbitCircuitDistance H s t ≤ 2 := by
  obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr
    (orbitCircuitDistance_zeroGate_lt_two H t).le
  exact (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp
    ⟨z,hz,C,hC.trans (Nat.zero_le s),he⟩

/-- Every sublinear circuit budget has the same limiting profile on each
bounded physical horizon, uniformly even across the shrinking startup
interval. A return at a smaller budget perturbs it by at most the error
of that actual visit. -/
theorem gaussian_bounded_gate_replay :
    ∃ w : ℝ, 0 < w ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
      let N := fun n : ℕ => ((n+2 : ℕ):ℝ)
      let H := fun n => shellOperator (pathPauliDisorderShell ω n)
      Tendsto (fun n => physicalWidth ω n/N n) atTop (𝓝 w) ∧
      ∀ (k s : ℕ→ℕ), (∀ᶠ n in atTop, k n ≤ s n) →
        Tendsto (fun n => (s n:ℝ)/N n) atTop (𝓝 0) →
        ∀ T η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ v : ℝ, ∀ t ∈ Icc (0:ℝ) T,
          |orbitCircuitDistance (H n) (s n) (v+t)-clippedChord (N n*t*w)| ≤
            orbitCircuitDistance (H n) (k n) v+η := by
  obtain ⟨w,hw,hr⟩ := gaussian_uniform_gate_replay
  let J := {q : ℚ // (q:ℝ)<2}
  have window (q : J) (M : ℕ) := MaximalError.gaussian_positive_density_below_diameter
    q.property (Nat.cast_nonneg M)
  choose A c hA hc hp using window
  refine ⟨w,hw,?_⟩
  filter_upwards [hr,ae_all_iff.mpr (fun q => ae_all_iff.mpr (hp q))] with ω hω hp
  intro N H
  refine ⟨hω.1,?_⟩
  intro k s hk hs T η hη
  obtain ⟨f,hf,hreplay⟩ := hω.2 k s hk hs
  obtain ⟨q,hq₀,hq₁⟩ := exists_rat_btwn (sub_lt_self (2:ℝ) hη)
  let r : J := ⟨q,hq₁⟩
  obtain ⟨M,hM⟩ := exists_nat_ge T
  let X := max (A r M) (2*π/w)
  have hX : 0 < X := (hA r M).trans_le (le_max_left ..)
  have hsmall : 0 < η/X := div_pos hη hX
  have hbudget := (hs.add hs).eventually_lt_const (show 0+0 < c r M by rw [zero_add]; exact hc ..)
  filter_upwards [hp r M,hf.eventually_lt_const hsmall,hreplay,hbudget,hk] with n hhard hf' hr' hs' hk'
  intro v t ht
  let x := N n*t
  have hN : 0 < N n := by dsimp only [N]; positivity
  have hx : 0 ≤ x := mul_nonneg hN.le ht.1
  by_cases h : x ≤ X
  · have hh := hr' v x hx
    have ht' : x/N n=t := by dsimp only [x]; field_simp
    rw [ht'] at hh
    apply hh.trans
    apply add_le_add_right
    calc x*f n ≤ x*(η/X) := mul_le_mul_of_nonneg_left hf'.le hx
         _ ≤ X*(η/X) := mul_le_mul_of_nonneg_right h hsmall.le
         _ = η := by field_simp
  · have hlarge := (le_max_left (A r M) (2*π/w)).trans (le_of_not_ge h)
    have hfit : (q:ℝ) < orbitCircuitDistance (H n) (k n+s n) t := by
      apply lt_of_not_ge
      intro hh
      have hlow := hhard t (by rwa [abs_of_nonneg ht.1]) (by rw [abs_of_nonneg ht.1]; exact ht.2.trans hM)
        (k n+s n) ((hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr hh)
      have hrat : (((k n+s n : ℕ):ℝ)/N n) < c r M := by
        rw [Nat.cast_add,add_div]
        exact ((add_le_add (div_le_div_of_nonneg_right (Nat.cast_le.mpr hk') hN.le) le_rfl).trans_lt hs')
      exact ((div_lt_iff₀ hN).mp hrat).not_ge hlow.le
    have hcirc : 2*π ≤ x*w := (div_le_iff₀ hw).mp ((le_max_right ..).trans (le_of_not_ge h))
    have he : clippedChord (x*w)=2 := by
      rw [clippedChord,min_eq_right hcirc,show 2*π/4=π/2 by ring,sin_pi_div_two,mul_one]
    change |orbitCircuitDistance (H n) (s n) (v+t)-clippedChord (x*w)| ≤ _
    rw [he,abs_of_nonpos (sub_nonpos.mpr (budget_distance_le_two ..))]
    linarith only [hq₀,hfit,(translate_distance (H n) v t hk').2]

#print axioms gaussian_bounded_gate_replay
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ShortCircuitReplay
