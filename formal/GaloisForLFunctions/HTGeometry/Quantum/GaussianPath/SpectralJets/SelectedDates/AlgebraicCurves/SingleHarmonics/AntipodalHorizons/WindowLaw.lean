import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.PhysicalMesh

/-! # An all-times exclusion bound after a single extremal pair winding -/

open Set MeasureTheory Filter Real Topology
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
open EmptyVisitFlux
noncomputable section

/-- Index of the largest sorted energy of a prefix. -/
def topLevel (k : ℕ) : Level k := ⟨2^(k+3)-1,Nat.sub_lt (Nat.two_pow_pos _) one_pos⟩

private theorem level_count (k : ℕ) : 8 ≤ 2^(k+3) := calc
  8 = 2^3 := by norm_num
  _ ≤ 2^(k+3) := Nat.pow_le_pow_right (by decide) (by omega)

theorem top_pos (k : ℕ) : (0 : Level k) < topLevel k := by
  change 0 < 2^(k+3)-1
  have := level_count k
  omega

private instance outside_extremes (k : ℕ) : Nonempty (Outside (topLevel k) 0) := by
  have hh := level_count k
  let l : Level k := ⟨1,by omega⟩
  refine ⟨⟨l,fun h => ?_,fun h => ?_⟩⟩
  · have he : 1=2^(k+3)-1 := congrArg Fin.val h
    omega
  · have he : (1:ℕ)=0 := congrArg Fin.val h
    omega

/-- A scalar hit anywhere in the next L periods of the full spectral width. -/
def windowHit (k : ℕ) (n : ℕ) (L r : ℝ) : Set (Coupling k) :=
  {x | let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
    ∃ s∈Icc (0:ℝ) L, flow (fun l => -E l/(2*π)) (date E (topLevel k) 0 n s)∈enclosingUnitArc r}

/-- At one prescribed late antipode the probability of any scalar hit in
a window of Mδ periods is bounded by M+1 short-arc tests. -/
theorem gaussian_window_bound (k M : ℕ) {r δ : ℝ} (hr : 0 ≤ r) (hd : 0 < δ) (hs : r+δ ≤ 1/2)
    {b : ℝ≥0∞} (hb : let d := Fintype.card (Outside (topLevel k) 0)
      (d:ℝ≥0∞)*ENNReal.ofReal (r+δ)^(d-1) < b) :
    let G := centredProductGaussian (Fin (Fintype.card (ChainLabel (k+3)))) 1
    ∀ᶠ n : ℕ in atTop, G (windowHit k n ((M:ℝ)*δ) r) ≤ (M+1:ℕ)*b := by
  intro G
  let i := topLevel k
  let j : Level k := 0
  let R : Icc (0:ℝ) (1/2) := ⟨r+δ,add_nonneg hr hd.le,hs⟩
  let B (n : ℕ) (h : Fin (M+1)) := {x | spectators k i j n ((h.val:ℝ)*δ) x∈enclosingUnitArc R}
  have hind (h : Fin (M+1)) : ∀ᶠ n : ℕ in atTop, G (B n h) < b :=
    late_spread_bound k i j (top_pos k).ne.symm ((h.val:ℝ)*δ) R hb
  have hsimple : ∀ᵐ x ∂G, Function.Injective (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x) := by
    apply (productGaussian_absolutelyContinuous _ one_ne_zero _).ae_le
    exact (ae_iff.mpr (volume_notMaximallyProjective_chain_eq_zero k)).mono fun _ hx =>
      injective_sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) hx.injective
  filter_upwards [eventually_all.mpr hind] with n hn
  have hsub : windowHit k n ((M:ℝ)*δ) r ≤ᵐ[G] ⋃ h, B n h := by
    filter_upwards [hsimple] with x hx h
    let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
    have hE : E j < E i := lt_of_le_of_ne (monotone_sortedTuple _ (top_pos k).le) (hx.ne (top_pos k).ne)
    have hh (l : Level k) : E j ≤ E l ∧ E l ≤ E i := by
      refine ⟨monotone_sortedTuple _ (Fin.zero_le _),monotone_sortedTuple _ ?_⟩
      change l.val ≤ 2^(k+3)-1
      have := l.isLt
      omega
    obtain ⟨l,hl⟩ := grid_covers k i j x n M hd hr hE hh h
    exact mem_iUnion.mpr ⟨l,hl⟩
  calc G (windowHit k n ((M:ℝ)*δ) r) ≤ G (⋃ h, B n h) := measure_mono_ae hsub
       _ ≤ ∑ h, G (B n h) := measure_iUnion_fintype_le _ _
       _ ≤ ∑ _ : Fin (M+1), b := Finset.sum_le_sum fun h _ => (hn h).le
       _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

#print axioms gaussian_window_bound
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
