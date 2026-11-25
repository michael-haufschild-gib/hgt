import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline

/-! # Last low-cost exit, first robust crossing, and next low-cost entrance -/
open Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- An observation belongs to a gap between consecutive affordable times.
The crossing is the first one after the last affordable time before the
observation. Both low-cost endpoints use the same budget and tolerance. -/
def InReturnExcursion {n : ℕ} (H : selfAdjoint (Reg n)) (P s : ℕ) (u W G : ℝ) : Prop :=
  let cheap := {t | HasProjectiveCircuitApproximation n (1/10:ℝ) s (unitaryEvolution H.val t)}
  let d := orbitCircuitDistance H P
  ∃ b σ v : ℝ, u-G ≤ b ∧ IsGreatest (Iic u ∩ cheap) b ∧ b < σ ∧ σ ≤ u ∧
    d σ = 9/80 ∧ IsLeast {t | b ≤ t ∧ 9/80 ≤ d t} σ ∧
    u+W < v ∧ v ≤ σ+G ∧ IsLeast (Ici σ ∩ cheap) v ∧ Disjoint (Ioo b v) cheap

/-- A first upper crossing from strictly below attains the level. -/
theorem first_level {f : ℝ → ℝ} (hf : Continuous f) {b u c : ℝ}
    (hbu : b ≤ u) (hb : f b < c) (hu : c ≤ f u) :
    ∃ σ ∈ Ioc b u, f σ = c ∧ IsLeast {t | b ≤ t ∧ c ≤ f t} σ := by
  let K := Icc b u ∩ f ⁻¹' Ici c
  have hcomp : IsCompact K := isCompact_Icc.inter_right (isClosed_Ici.preimage hf)
  obtain ⟨σ,hσ,hmin⟩ := hcomp.exists_isMinOn
    (show K.Nonempty from ⟨u,⟨hbu,le_rfl⟩,hu⟩) continuous_id.continuousOn
  have hcσ : c ≤ f σ := hσ.2
  have hbσ : b < σ := lt_of_le_of_ne hσ.1.1 (fun h => hb.not_ge (by rwa [h]))
  have hm : IsLeast {t | b ≤ t ∧ c ≤ f t} σ := by
    refine ⟨⟨hσ.1.1,hcσ⟩,?_⟩
    rintro t ⟨ht,htc⟩
    by_cases htu : t ≤ u
    · exact hmin (show t ∈ K from ⟨⟨ht,htu⟩,htc⟩)
    · exact hσ.1.2.trans (le_of_not_ge htu)
  obtain ⟨w,hw,he⟩ := intermediate_value_Icc hbσ.le hf.continuousOn
    (show c ∈ Icc (f b) (f σ) from ⟨hb.le,hcσ⟩)
  have hσw : σ ≤ w := hm.2 ⟨hw.1,he.ge⟩
  exact ⟨σ,⟨hbσ,hσ.1.2⟩,(congrArg f (le_antisymm hσw hw.2)).trans he,hm⟩

/-- A full-budget hard window sits inside an actual return gap. Locating
the preceding exit before taking the crossing excludes every intermediate
low-cost hit, including hits strictly before the observed window. -/
theorem excursion_of_hard_window {n P s : ℕ} (H : selfAdjoint (Reg n)) (hs : s ≤ P)
    {u W G : ℝ} (hW : 0 ≤ W)
    (hvisit : ∀ a : ℝ, ∃ t ∈ Icc a (a+G),
      HasProjectiveCircuitApproximation n (1/10:ℝ) 0 (unitaryEvolution H.val t))
    (hwin : ∀ t ∈ Icc u (u+W), 1/8 < orbitCircuitDistance H P t) :
    InReturnExcursion H P s u W G := by
  let C := {t | HasProjectiveCircuitApproximation n (1/10:ℝ) s (unitaryEvolution H.val t)}
  have hclosed : IsClosed C := by
    simp only [C,hasProjectiveCircuitApproximation_iff_infDist]
    exact isClosed_le (orbitCircuitDistance_lipschitz H s).continuous continuous_const
  have meet (a : ℝ) : (Icc a (a+G) ∩ C).Nonempty := by
    obtain ⟨t,ht,z,hz,K,hK,he⟩ := hvisit a
    exact ⟨t,ht,z,hz,K,hK.trans (Nat.zero_le s),he⟩
  have hd (t : ℝ) (ht : t ∈ C) : orbitCircuitDistance H P t ≤ 1/10 := by
    obtain ⟨z,hz,K,hK,he⟩ := ht
    exact (hasProjectiveCircuitApproximation_iff_infDist _ P _).mp ⟨z,hz,K,hK.trans hs,he⟩
  have prev : (Icc (u-G) u ∩ C).Nonempty := by simpa only [sub_add_cancel] using meet (u-G)
  obtain ⟨b,hb,hmax⟩ := (isCompact_Icc.inter_right hclosed).exists_isMaxOn prev continuous_id.continuousOn
  have last : IsGreatest (Iic u ∩ C) b := by
    refine ⟨⟨hb.1.2,hb.2⟩,?_⟩
    rintro t ⟨htu,htC⟩
    by_cases hlo : u-G ≤ t
    · exact hmax (show t ∈ Icc (u-G) u ∩ C from ⟨⟨hlo,htu⟩,htC⟩)
    · exact (le_of_not_ge hlo).trans hb.1.1
  have hbu := hb.1.2
  have hstart := hd b hb.2
  have hend := hwin u ⟨le_rfl,le_add_of_nonneg_right hW⟩
  obtain ⟨σ,hσ,heq,hfirst⟩ := first_level (orbitCircuitDistance_lipschitz H P).continuous hbu
    (show orbitCircuitDistance H P b < 9/80 by linarith only [hstart])
    (show 9/80 ≤ orbitCircuitDistance H P u by linarith only [hend])
  obtain ⟨v,hv,hmin⟩ := (isCompact_Icc.inter_right hclosed).exists_isMinOn (meet σ) continuous_id.continuousOn
  have next : IsLeast (Ici σ ∩ C) v := by
    refine ⟨⟨hv.1.1,hv.2⟩,?_⟩
    rintro t ⟨htσ,htC⟩
    by_cases hi : t ≤ σ+G
    · exact hmin (show t ∈ Icc σ (σ+G) ∩ C from ⟨⟨htσ,hi⟩,htC⟩)
    · exact hv.1.2.trans (le_of_not_ge hi)
  have huv : u < v := lt_of_not_ge fun h =>
    (not_lt_of_ge (last.2 ⟨h,hv.2⟩)) (hσ.1.trans_le hv.1.1)
  have hfar : u+W < v := by
    by_contra! h
    linarith only [hwin v ⟨huv.le,h⟩,hd v hv.2]
  refine ⟨b,σ,v,hb.1.1,last,hσ.1,hσ.2,heq,hfirst,hfar,hv.1.2,next,?_⟩
  rw [Set.disjoint_left]
  intro t ht htC
  by_cases htu : t ≤ u
  · exact (not_le_of_gt ht.1) (last.2 ⟨htu,htC⟩)
  · exact (not_le_of_gt ht.2) (next.2 ⟨hσ.2.trans (le_of_not_ge htu),htC⟩)

#print axioms excursion_of_hard_window
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions
