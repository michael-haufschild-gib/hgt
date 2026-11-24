import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FiniteRecords.WindowCover
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.FullRange.PhysicalRates

/-! # First-hit probabilities for origins sampled from a finite physical record -/
open Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
noncomputable section

/-- In every sufficiently long finite record, an affordable date in the
next W time units costs at most W+1 times the single-date exponential
upper bound. The lower bound counts origins already affordable. -/
theorem gaussian_finite_forward_wait_full :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ, subcriticalBudget s →
      ∀ ε ∈ Ioo (0:ℝ) 2, ∀ l b : ℝ, 0<l → l<physicalArc ε → physicalArc ε<b →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D : ℕ := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        ∀ j ≤ s N, ∀ a T W : ℝ, 2*(2:ℝ)^(D^c) ≤ T → 0≤W →
          let p := volume.real (windowHits H j ε W ∩ Icc a (a+T))/T
          l^D < p ∧ p ≤ (W+1)*b^D := by
  obtain ⟨c,hc⟩ := gaussian_finite_occupation_full
  refine ⟨c,?_⟩
  filter_upwards [hc,gaussian_unit_hit_enlargement] with ω hocc hunit
  intro s hs ε hε l b hl hlx hxb
  let x := physicalArc ε
  obtain ⟨hx,htol⟩ := physicalArc_full hε
  obtain ⟨y,hxy,hyb⟩ := exists_between (lt_min hxb hx.2)
  have hy : y∈Ioo (0:ℝ) 1 := ⟨hx.1.trans hxy,hyb.trans_le (min_le_right ..)⟩
  have hδ : 0<zeroGateArcTolerance y-ε := by
    rw [←htol]
    exact sub_pos.mpr (strictMonoOn_zeroGateArcTolerance_full ⟨hx.1.le,hx.2.le⟩ ⟨hy.1.le,hy.2.le⟩ hxy)
  filter_upwards [hocc s hs x hx l b hl hlx hxb,
    hocc (fun n => s n+n^4) (subcritical_add_pow_four hs) y hy l b hl (hlx.trans hxy)
      (hyb.trans_le (min_le_left ..)),hunit _ hδ] with k hlow hhigh hw
  intro N D H j hj a T W hT hW p
  have hT₀ : 0<T := (show 0<2*(2:ℝ)^(D^c) by positivity).trans_le hT
  have hsmall := (hlow j hj a T hT).1
  change zeroGateArcTolerance x=ε at htol
  rw [htol,visitFraction,add_sub_cancel_left] at hsmall
  have hsub : visitSet H j ε ⊆ windowHits H j ε W := fun u hu =>
    ⟨u,⟨le_rfl,le_add_of_nonneg_right hW⟩,hu⟩
  refine ⟨hsmall.trans_le (div_le_div_of_nonneg_right
    (measureReal_mono (inter_subset_inter_left _ hsub)
      (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)) hT₀.le),?_⟩
  have henlarge := hw j ε
  rw [show ε+(zeroGateArcTolerance y-ε)=zeroGateArcTolerance y by ring] at henlarge
  have hb := finite_window_hit_fraction (a:=a) (T:=a+T) hW henlarge
    (lt_add_of_pos_right _ hT₀) (p:=b^D) (fun i => by
      simpa only [add_right_comm a T] using
        (hhigh (j+N^4) (Nat.add_le_add_right hj _) (a+(i.val:ℝ)) T hT).2)
  simpa only [add_sub_cancel_left,p] using hb

#print axioms gaussian_finite_forward_wait_full

/-- In each record, only an exponentially small fraction of origins can
return within b⁻ᴰ, for any b above the physical arc width. -/
theorem gaussian_finite_wait_quantile_full :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ, subcriticalBudget s →
      ∀ ε ∈ Ioo (0:ℝ) 2, ∀ z b : ℝ, physicalArc ε<z → z<b → b<1 →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        ∀ j ≤ s N, ∀ a T : ℝ, 2*(2:ℝ)^(D^c) ≤ T →
          volume.real (windowHits H j ε (1/b^D) ∩ Icc a (a+T))/T ≤ 2*(z/b)^D := by
  obtain ⟨c,h⟩ := gaussian_finite_forward_wait_full
  refine ⟨c,?_⟩
  filter_upwards [h] with ω hw
  intro s hs ε hε z b hxz hzb hb
  obtain ⟨l,hl,hlx⟩ := exists_between (physicalArc_full hε).1.1
  filter_upwards [hw s hs ε hε l z hl hlx hxz] with k hk
  intro N D H j hj a T hT
  have hz := (hl.trans hlx).trans hxz
  have hbpos := hz.trans hzb
  have hW : 1 ≤ 1/b^D := (le_div_iff₀ (pow_pos hbpos D)).mpr
    (by simpa only [one_mul] using pow_le_one₀ hbpos.le hb.le (n:=D))
  apply (hk j hj a T _ hT (zero_le_one.trans hW)).2.trans
  calc
    _ ≤ (2*(1/b^D))*z^D := mul_le_mul_of_nonneg_right (by linarith only [hW]) (pow_nonneg hz.le D)
    _ = _ := by rw [div_pow]; ring

#print axioms gaussian_finite_wait_quantile_full
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
