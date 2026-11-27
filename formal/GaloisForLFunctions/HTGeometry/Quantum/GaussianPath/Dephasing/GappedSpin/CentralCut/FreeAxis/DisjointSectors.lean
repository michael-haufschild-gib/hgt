import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.SlopeGrid
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.StrongCoordinates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.PathConjugation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.BoundedField.GaussianSector

/-! # A sixth-power Gaussian sector for the original chain -/
open Set Filter Real MeasureTheory ProbabilityTheory Function
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
open PrescribedTimes AccuracyScales.TenthPlateau
noncomputable section

/-- Packed spin directions recover the two transverse onsite widths.
All laboratory coefficients of the resulting trajectories are positive. -/
theorem positive_sixth_power_sector :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      ∀ T ≥ (1:ℝ), ∃ B : ℕ, ∃ E : Set PathPauliDisorder, 2*B ≤ P ∧ MeasurableSet E ∧
        exp (-C*(K:ℝ)^2) ≤ T^6*pathPauliDisorderLaw.real E ∧ ∀ ω ∈ E,
          let u := pathPauliDisorderShell ω n
          (∀ l, u l ∈ Icc (1/20:ℝ) 4) ∧
          (∀ t : ℝ, HasProjectiveCircuitApproximation K (1/10) (2^K*3)
            (unitaryEvolution (pathHamiltonian u) t)) ∧
          ∀ t : ℝ, |t| ≤ T → HasProjectiveCircuitApproximation K (1/100) B
            (unitaryEvolution (pathHamiltonian u) t) := by
  classical
  obtain ⟨C,hC,hbox⟩ := bounded_gaussian_sector
  refine ⟨C,hC,?_⟩
  filter_upwards [hbox] with k hk
  intro n K P T hT
  obtain ⟨B,A,hB,hA,hfloor,⟨site,hfield⟩,hfit⟩ := hk T hT
  obtain ⟨N,hN,p,hp,hdj⟩ := packed_directions T hT
  let μ := Measure.pi fun _ : PathLabel n => gaussianReal 0 1
  let δ := 1/(3600*sqrt T)
  have hδ : δ ≤ 1/3600 := by
    dsimp only [δ]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith only [one_le_sqrt.mpr hT])
  choose F hz hx hy hc using (fun i : Fin N×Fin N => slope_frame (p i.1) (p i.2) (hp _) (hp _))
  choose E hE hmass hpre using (fun i : Fin N×Fin N => rotate_event (F i).R (F i).orthogonal A hA)
  have hcone (i) (x) (he : x∈E i) : SlopeCone (p i.1) (p i.2) δ (fun j => x (.inl (site,j))) := by
    obtain ⟨w,hw,rfl⟩ := hpre i x he
    obtain ⟨_,hd,_,_,_⟩ := hfit w hw
    have hab (j : Fin N) : |p j| ≤ 2 := by rw [abs_of_pos (zero_lt_one.trans_le (hp j).1)]; exact (hp j).2
    exact rotated_field_cone (F i) (hab _) (hab _) (hz i) (hx i) (hy i) hδ
      (fun j => w (.inl (site,j))) (hd (.inl (site,2)) rfl).le
      (hfield w hw 0 (by decide)) (hfield w hw 1 (by decide))
  have hdis : Pairwise (Disjoint on E) := fun i j hij => Set.disjoint_left.mpr fun x hi hj =>
    hdj i j hij _ (hcone i x hi) (hcone j x hj)
  let Y := fun (ω : PathPauliDisorder) l => pathPauliDisorderShell ω n l
  have hY := measurePreserving_pathDisorder_labels n
  have hU := MeasurableSet.iUnion hE
  have heq : pathPauliDisorderLaw.real (Y ⁻¹' ⋃ i, E i)=(N:ℝ)^2*μ.real A := by
    rw [hY.measureReal_preimage hU.nullMeasurableSet,measureReal_iUnion_fintype hdis hE]
    calc _ = ∑ _ : Fin N×Fin N, μ.real A := Finset.sum_congr rfl (fun i _ => hmass i)
         _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
                       nsmul_eq_mul,Nat.cast_mul,pow_two]
  refine ⟨B,Y ⁻¹' ⋃ i, E i,hB,hU.preimage hY.measurable,?_,?_⟩
  · rw [heq]
    calc _ ≤ T^7*μ.real A := hfloor
         _ = T^6*(T*μ.real A) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN measureReal_nonneg) (by positivity)
  · intro ω he u
    obtain ⟨i,hi⟩ := mem_iUnion.mp he
    obtain ⟨w,hw,hmap⟩ := hpre i (Y ω) hi
    change rotateLabels (F i).R n w=u.ofLp at hmap
    obtain ⟨hbnd,hd,ho,hglobal,hinc⟩ := hfit w hw
    refine ⟨fun l => ?_,fun t => ?_,fun t ht => ?_⟩
    · have h := octant_coordinates (F i) (hc i) w hbnd hd ho l
      rwa [hmap] at h
    · have h := frame_fit (F i) (hglobal t); rwa [hmap] at h
    · have h := frame_fit (F i) (hinc t ht); rwa [hmap] at h

#print axioms positive_sixth_power_sector
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
