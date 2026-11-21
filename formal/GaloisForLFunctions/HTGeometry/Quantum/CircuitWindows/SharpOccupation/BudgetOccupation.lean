import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.SpectralTube
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.CircuitNet

/-! # Occupation by circuits of bounded size at the physical operator error -/
open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

/-- All real times admitting a circuit at the given projective operator error. -/
def visitSet {n : ℕ} (H : selfAdjoint (Register n)) (s : ℕ) (ε : ℝ) : Set ℝ :=
  {t | HasProjectiveCircuitApproximation n ε s (unitaryEvolution H.val t)}

/-- Fraction of the observation interval occupied by visits. -/
def visitFraction {n : ℕ} (H : selfAdjoint (Register n)) (s : ℕ) (ε a T : ℝ) : ℝ :=
  volume.real (visitSet H s ε ∩ Icc a T)/(T-a)

theorem visitFraction_mono {n s j : ℕ} (H : selfAdjoint (Register n)) (hs : s ≤ j)
    (ε a T : ℝ) (hT : a ≤ T) : visitFraction H s ε a T ≤ visitFraction H j ε a T := by
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hT)
  apply measureReal_mono _ (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  apply inter_subset_inter_left
  rintro t ⟨c,hc,C,hC,he⟩
  exact ⟨c,hc,C,hC.trans hs,he⟩

/-- A finite unitary net controls long-time occupation. Each enlarged
tube contributes precisely the empty-circuit upper allowance at that radius. -/
theorem finite_budget_eventually_lt {n : ℕ} (H : selfAdjoint (Register n))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (s : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hy : y < 1/2) (a b : ℝ)
    (hb : let δ := zeroGateArcTolerance y-zeroGateArcTolerance x
          ((s:ℝ)+1)*((((n:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s*zeroGateArcDensity (2^n) y < b) :
    ∀ᶠ T : ℝ in atTop, visitFraction H s (zeroGateArcTolerance x) a T < b := by
  classical
  let δ := zeroGateArcTolerance y-zeroGateArcTolerance x
  have hδ : 0 < δ := sub_pos.mpr (strictMonoOn_zeroGateArcTolerance
    ⟨hx,(hxy.trans hy).le⟩ ⟨hx.trans hxy.le,hy.le⟩ hxy)
  obtain ⟨F,hcover,hcard⟩ := exists_budget_net n s δ hδ
  choose ψ hψ using unitary_visits_subset_shifted H
  let A (w : F) := shiftedTimes H (ψ w.1) y
  have hsub : visitSet H s (zeroGateArcTolerance x) ⊆ ⋃ w : F, A w := by
    rintro t ⟨c,hc,C,hC,he⟩
    obtain ⟨W,hW,hclose⟩ := hcover C hC
    refine mem_iUnion.mpr ⟨⟨W,hW⟩,hψ W y (hx.trans hxy.le) hy t c hc ?_⟩
    have htri := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution H.val t)
      (c • (C.eval : Register n)) (c • (W : Register n))
    rw [←smul_sub,norm_smul,hc,one_mul] at htri
    exact htri.trans ((add_le_add he hclose).trans_eq (by dsimp [δ]; ring))
  have htime (w : F) := shiftedTimes_occupation H hmax (ψ w.1) ⟨y,hx.trans hxy.le,hy.le⟩ a
  let p := zeroGateArcDensity (2^n) y
  have hsum : Tendsto (fun T : ℝ => ∑ w : F, volume.real (A w ∩ Icc a T)/(T-a)) atTop
      (𝓝 ((F.card:ℝ)*p)) := by
    simpa [A,p] using tendsto_finsetSum Finset.univ (fun (w : F) _ => htime w)
  have hNp : 0 ≤ p := by
    dsimp [p,zeroGateArcDensity]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hx.trans hxy.le) _)
  have hlim := hsum.eventually_lt_const ((mul_le_mul_of_nonneg_right hcard hNp).trans_lt hb)
  filter_upwards [hlim,eventually_gt_atTop a] with T ht hT
  apply lt_of_le_of_lt _ ht
  rw [←Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hT.le)
  let B (w : F) := A w ∩ Icc a T
  have hI : (⋃ w : F, B w) ⊆ Icc a T := iUnion_subset fun _ => inter_subset_right
  apply (measureReal_mono (s₂ := ⋃ w : F, B w) _ (measure_ne_top_of_subset hI measure_Icc_lt_top.ne)).trans
    (measureReal_iUnion_fintype_le B)
  rintro t ⟨ht,hI⟩
  obtain ⟨w,hw⟩ := mem_iUnion.mp (hsub ht)
  exact mem_iUnion.mpr ⟨w,hw,hI⟩

theorem zero_visitFraction_tendsto {n : ℕ} (H : selfAdjoint (Register n))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) (x : Icc (0:ℝ) (1/2)) (a : ℝ) :
    Tendsto (fun T => visitFraction H 0 (zeroGateArcTolerance x) a T) atTop
      (𝓝 (zeroGateArcDensity (2^n) x)) := by
  have hset : visitSet H 0 (zeroGateArcTolerance x) = zeroGateReturnSet H x := by
    ext t
    exact hasProjectiveCircuitApproximation_iff_infDist _ _ _
  simpa only [visitFraction,hset] using maximallyProjective_zeroGateOccupation_from_start H hmax x a

#print axioms finite_budget_eventually_lt
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
