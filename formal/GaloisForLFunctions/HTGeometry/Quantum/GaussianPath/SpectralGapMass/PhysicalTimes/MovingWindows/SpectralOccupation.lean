import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.MovingWindows.LocalTrace
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.FiniteMoments
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.ThreeGateCost

/-! # Spectral gate costs in every translated physical interval -/
open MeasureTheory Filter Set Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
open ClockSpectrum
noncomputable section

/-- Cumulative eigenphase counts agree with the uniform law at each grid point. -/
def goodGrid {n : ℕ} (u : PathShell n) (t : ℝ) (Q : ℕ) (δ : ℝ) :=
  ∀ j : Fin (Q+1), |(phaseCount u t (j.val/(Q:ℝ)):ℝ)/(2:ℝ)^(n+2)-j.val/(Q:ℝ)| < δ

/-- Large discrepancies require a large amplitude at one of finitely many harmonics.
The finite family and its threshold are independent of the register size. -/
theorem grid_failure_cover (Q : ℕ) (hQ : 0 < Q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, 0 < k ∧ ∃ κ > 0, ∀ (ω : PathPauliDisorder) (n : ℕ),
      {t | ¬goodGrid (pathPauliDisorderShell ω n) t Q δ} ⊆
        ⋃ j : Fin k, largeOverlap ω n 1 (j.val+1) κ := by
  obtain ⟨k,hk,κ,hκ,h⟩ := finite_moments_control_grid Q hQ hδ
  refine ⟨k,hk,κ,hκ,?_⟩
  intro ω n t ht
  by_contra hbad
  apply ht
  let u := pathPauliDisorderShell ω n
  have hm (j : ℕ) (hj : j < k) : ‖∫ z, fourier ((j+1:ℕ):ℤ) z ∂(eigenphaseLaw u t : Measure (AddCircle (2*Real.pi)))‖ < κ := by
    apply lt_of_not_ge
    intro hc
    rw [eigenphase_moment,Int.cast_natCast,Nat.cast_add,Nat.cast_one] at hc
    exact hbad (mem_iUnion.mpr ⟨(⟨j,hj⟩ : Fin k),by rwa [empty_large_overlap]⟩)
  intro j
  simpa only [angular_fraction,phaseCount] using h (eigenphaseLaw u t) hm j

/-- A cover by finitely many harmonic exceptions gives a length bound
even when measurability of the exceptional event has not been used. -/
theorem harmonic_cover_volume {k : ℕ} {s : Set ℝ} (E : Fin k → Set ℝ)
    (hcov : s ⊆ ⋃ j, E j) (v B : ℝ) (f : Fin k → ℝ)
    (hb : ∀ j, volume.real (E j ∩ Icc v (v+B)) ≤ f j) :
    volume.real (s ∩ Icc v (v+B)) ≤ ∑ j, f j := by
  let L := Icc v (v+B)
  let A := ⋃ j : Fin k, E j ∩ L
  have hs : s∩L ⊆ A := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcov hx.1)
    exact mem_iUnion.mpr ⟨j,hj,hx.2⟩
  have hsub : A ⊆ L := iUnion_subset fun _ => inter_subset_right
  apply (measureReal_mono hs (measure_ne_top_of_subset hsub measure_Icc_lt_top.ne)).trans
  have he : A=⋃ j∈(univ : Finset (Fin k)), E j∩L := by simp only [mem_univ,iUnion_true,A]
  rw [he]
  exact (measureReal_biUnion_finset_le univ _).trans (sum_le_sum (fun i _ => hb i))

theorem gaussian_moving_grid (Q : ℕ) (hQ : 0 < Q) {δ η B : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ v : ℝ,
      volume.real ({t | ¬goodGrid (pathPauliDisorderShell ω n) t Q δ} ∩ Icc v (v+B)) ≤ η := by
  obtain ⟨k,hk,κ,hκ,hcov⟩ := grid_failure_cover Q hQ hδ
  have hpos : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  have hc (j : Fin k) := gaussian_moving_overlap (B:=B) hκ (div_pos hη hpos)
    (by positivity : 0 < (j.val:ℝ)+1)
  filter_upwards [ae_all_iff.mpr hc] with ω hw
  filter_upwards [eventually_all.mpr hw] with n hn
  intro v
  apply (harmonic_cover_volume _ (hcov ω n) v B (fun _ => η/k) (fun j => hn j 1 v)).trans_eq
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

def exactThreeAt {n : ℕ} (u : PathShell n) (t : ℝ) :=
  let M := unitaryEvolution (pathHamiltonian u) t
  (∃ W : unitaryGroup (Fin (n+2) → Bool) ℂ,
    HasProjectiveCircuitApproximation (n+2) (1/10) 3 (W.val*M*star W.val)) ∧
  ∀ W : unitaryGroup (Fin (n+2) → Bool) ℂ,
    ¬HasProjectiveCircuitApproximation (n+2) (1/10) 2 (W.val*M*star W.val)

theorem exact_three_of_grids {n : ℕ} (hn : 7 ≤ n) (u : PathShell n) (t : ℝ)
    (hu : goodGrid u t 512 (1/512)) (hl : goodGrid u t 17408 (1/(4*17408))) :
    exactThreeAt u t := by
  obtain ⟨p,hp⟩ := three_gate_of_cdf (by omega : 9 ≤ n+2) (physicalTurns u t)
    (fun j => ⟨(turns_mem _).1.le,(turns_mem _).2⟩) hu
  obtain ⟨W,hW⟩ := sorted_physical_diagonal u t p
  obtain ⟨f,hf⟩ := seventeen_phases_of_cdf _ (D:=(2:ℝ)^(n+2)) (by positivity) hl
  exact ⟨⟨W,hW.symm ▸ hp⟩,two_gates_excluded u t f hf⟩

/-- Almost surely on long prefixes, every length-B interval has at most η
exceptional time for the three-gate minimum after a free change of basis.
The origin may be any real time on the frozen trajectory. -/
theorem gaussian_moving_exact_three {η B : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ v : ℝ,
      volume.real ({t | ¬exactThreeAt (pathPauliDisorderShell ω n) t} ∩ Icc v (v+B)) ≤ η := by
  filter_upwards [gaussian_moving_grid (B:=B) 512 (by decide) (by norm_num : (0:ℝ) < 1/512) (half_pos hη),
    gaussian_moving_grid (B:=B) 17408 (by decide) (by norm_num : (0:ℝ) < 1/(4*17408)) (half_pos hη)] with ω hω hω'
  filter_upwards [hω,hω',eventually_ge_atTop 7] with n hn hn' hN
  intro v
  let u := pathPauliDisorderShell ω n
  let L := Icc v (v+B)
  let E := {t | ¬goodGrid u t 512 (1/512)}∩L
  let F := {t | ¬goodGrid u t 17408 (1/(4*17408))}∩L
  have he : {t | ¬exactThreeAt u t} ∩ L ⊆ E∪F := by
    intro t ht
    by_cases h : goodGrid u t 512 (1/512)
    · exact Or.inr ⟨fun h' => ht.1 (exact_three_of_grids hN u t h h'),ht.2⟩
    · exact Or.inl ⟨h,ht.2⟩
  have hf : E∪F ⊆ L := union_subset inter_subset_right inter_subset_right
  apply ((measureReal_mono he (measure_ne_top_of_subset hf measure_Icc_lt_top.ne)).trans
    (measureReal_union_le E F)).trans
  exact (add_le_add (hn v) (hn' v)).trans_eq (add_halves _)

#print axioms grid_failure_cover
#print axioms gaussian_moving_exact_three
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
