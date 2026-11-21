import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.FullBudgetWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.TravelTime
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncrementClocks.FirstCrossing

/-! # Occupation bounds at the distinguished first crossing from the identity -/
open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Before the first crossing each origin is already in the sublevel set.
Between the crossing and a sufficiently close return the endpoint itself
witnesses a hit in every forward window. -/
private theorem initial_segment_hit {n P : ℕ} (H : selfAdjoint (Reg n)) {σ v W : ℝ}
    (hW : 0 ≤ W) (hsv : v ≤ σ+W)
    (hprior : ∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80)
    (hv : orbitCircuitDistance H P v ≤ 1/8) :
    robustWindowHits H P W ∩ Icc 0 v = Icc 0 v := by
  apply Set.inter_eq_right.mpr
  intro t ht
  by_cases h : t < σ
  · refine ⟨t,⟨le_rfl,le_add_of_nonneg_right hW⟩,?_⟩
    exact (hprior t ⟨ht.1,h⟩).le.trans (by norm_num)
  · exact ⟨v,⟨ht.2,hsv.trans (add_le_add (le_of_not_gt h) le_rfl)⟩,hv⟩

/-- The true first crossing has an improved upper deadline. For its first
subsequent visit to any budget up to half the threshold, a short wait
forces the absolute return time below the entropy-corrected deadline. -/
theorem gaussian_initial_crossing_short_return_tradeoff :
    ∃ q : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let x := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
      let P := nearHilbertContinuousCircuitBudget N
      let B := (2:ℝ)^(N-10*N.sqrt)
      let G := (2:ℝ)^(D^q)
      ∃ σ : ℝ, B < σ ∧ orbitCircuitDistance H P σ = 9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        ((2:ℝ)^(7*D/16)-1)*σ ≤ G ∧
        ∀ s ≤ P/2, ∃ v : ℝ, σ+B < v ∧
          IsLeast {t | σ ≤ t ∧ HasProjectiveCircuitApproximation N (1/10:ℝ) s
            (unitaryEvolution H.val t)} v ∧
          v ≤ min (σ+G) ((σ+1)*(100:ℝ)^(D-1)) ∧
          ∀ b e : ℕ, 16*(b+e) ≤ 7*D → σ+(2:ℝ)^b < v ∨ ((2:ℝ)^e-1)*v ≤ G := by
  obtain ⟨q,hq⟩ := gaussian_full_budget_robust_windows
  obtain ⟨_,hfirst⟩ := IncrementClocks.gaussian_path_first_crossing_near_dimension_wait
  refine ⟨q,?_⟩
  filter_upwards [hq,hfirst,gaussian_robust_travel_time] with ω hw hf htw
  filter_upwards [hw,hf,htw] with k hh hc htravel
  intro N D x H P B G
  obtain ⟨σ,hB,_,heq,hprior,_,hnext⟩ := hc
  have hB0 : 0 ≤ IncrementClocks.crossingWidth N := by dsimp [IncrementClocks.crossingWidth]; positivity
  have hσ : 0 ≤ σ := hB0.trans hB.le
  have hid : HasProjectiveCircuitApproximation N (1/10:ℝ) 0 (unitaryEvolution H.val 0) := by
    refine ⟨1,norm_one,TwoQubitCircuit.one N,by rfl,?_⟩
    simp [TwoQubitCircuit.one_eval,unitaryEvolution]
  have hstart := htravel σ 0 heq.ge 0 (Nat.zero_le _) hid
  rw [sub_zero,abs_of_nonneg hσ] at hstart
  have date (b e : ℕ) (hbe : 16*(b+e) ≤ 7*D) (v : ℝ) (hv0 : 0 ≤ v)
      (hsv : v ≤ σ+(2:ℝ)^b) (hv : orbitCircuitDistance H P v ≤ 1/8) :
      ((2:ℝ)^e-1)*v ≤ G := by
    have h := hh.2 b e hbe 0 v hv0
    rw [zero_add,initial_segment_hit H (by positivity) hsv hprior hv,
      Real.volume_real_Icc_of_le hv0,sub_zero] at h
    linarith only [h]
  refine ⟨σ,hstart,heq,hprior,date 0 (7*D/16) (by omega) σ hσ
    (le_add_of_nonneg_right (by positivity)) (by rw [heq]; norm_num),?_⟩
  intro s hs
  obtain ⟨v,hv,hdir,hy,hgap⟩ := hnext s hs
  have hsv : σ ≤ v := (le_add_of_nonneg_right hB0).trans hv.le
  have hwait := htravel σ v heq.ge s hs hy
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hsv)] at hwait
  have hleast : IsLeast {t | σ ≤ t ∧ HasProjectiveCircuitApproximation N (1/10:ℝ) s
      (unitaryEvolution H.val t)} v := by
    refine ⟨⟨hsv,hy⟩,?_⟩
    rintro t ⟨ht,⟨z,hz,C,hC,herr⟩⟩
    by_contra! h
    exact (hgap t ⟨ht,h⟩ z hz C hC).not_ge herr
  obtain ⟨w,hw,z,hz,C,hC,herr⟩ := hh.1 σ
  have hupper := hleast.2 ⟨hw.1,⟨z,hz,C,hC.trans (Nat.zero_le s),herr⟩⟩
  refine ⟨v,by change B < v-σ at hwait; linarith only [hwait],hleast,
    le_min (hupper.trans hw.2) (hdir.trans (min_le_right _ _)),?_⟩
  intro b e hbe
  by_cases h : σ+(2:ℝ)^b < v
  · exact Or.inl h
  · obtain ⟨z,hz,C,hC,herr⟩ := hy
    have hd : orbitCircuitDistance H P v ≤ 1/10 :=
      (hasProjectiveCircuitApproximation_iff_infDist _ P _).mp
        ⟨z,hz,C,hC.trans (hs.trans (Nat.div_le_self _ _)),herr⟩
    exact Or.inr (date b e hbe v (hσ.trans hsv) (le_of_not_gt h) (hd.trans (by norm_num)))

#print axioms gaussian_initial_crossing_short_return_tradeoff
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions
