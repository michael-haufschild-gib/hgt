import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.MovingWindows.SpectralOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.IsolatedFields.GaussianWindow

/-! # Inverse-square-root exceptional time for the three-gate spectrum -/
open MeasureTheory Filter Set Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section

/-- Mutual overlaps of dates more than √(A/N) apart are small.
Packing dates separately for each harmonic gives one length bound at every origin. -/
theorem gaussian_grid_exception_length (Q : ℕ) (hQ : 0 < Q) {δ : ℝ} (hδ : 0 < δ) (B : ℝ) :
    ∃ K > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ v : ℝ,
      volume.real ({t | ¬goodGrid (pathPauliDisorderShell ω n) t Q δ} ∩ Icc v (v+B)) ≤ K/sqrt (n+2:ℕ) := by
  obtain ⟨k,hk,κ,hκ,hcov⟩ := grid_failure_cover Q hQ hδ
  have htol : 0 < κ^2/2 := by positivity
  obtain ⟨A,hA,hstart⟩ := Bulk.gaussian_startup_trace htol
  let M : ℝ := ⌈2/κ^2⌉₊
  let K := ((k:ℝ)*(M+1))*(2*sqrt A)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  refine ⟨K,by dsimp only [K]; positivity,?_⟩
  filter_upwards [hstart,gaussian_uniform_trace_decay (T:=max 1 ((k:ℝ)*max 0 B)) zero_lt_one htol]
    with ω hω hw
  filter_upwards [hω,hw] with n hn hf
  let N := ((n+2:ℕ):ℝ)
  have hN : 0 < N := by dsimp only [N]; positivity
  let r := sqrt A/sqrt N
  have hr : 0 < r := div_pos (sqrt_pos.mpr hA) (sqrt_pos.mpr hN)
  have he : N*r^2=A := by
    dsimp only [r]
    rw [div_pow,sq_sqrt hA.le,sq_sqrt hN.le]
    field_simp
  intro v
  have hvol (j : Fin k) :
      volume.real (largeOverlap ω n 1 (j.val+1) κ ∩ Icc v (v+B)) ≤ M*(2*r) := by
    let p := (j.val:ℝ)+1
    have hp : 1 ≤ p := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hpk : p ≤ k := by exact_mod_cast (Nat.succ_le_of_lt j.isLt)
    apply local_overlap_duration ω n hr.le (zero_lt_one.trans_le hp) hκ _ 1 v
    intro s hs
    have hs₀ : r ≤ s := (le_mul_of_one_le_left hr.le hp).trans hs.1
    by_cases hsmall : s ≤ 1
    · apply (hn s _ (by rwa [abs_of_nonneg (hr.le.trans hs₀)])).le
      exact he.ge.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hs₀ 2) hN.le)
    · apply (hf s ⟨le_of_not_ge hsmall,?_⟩).le
      exact hs.2.trans ((mul_le_mul_of_nonneg_left (le_max_right 0 B) (zero_le_one.trans hp)).trans
        ((mul_le_mul_of_nonneg_right hpk (le_max_left 0 B)).trans (le_max_right ..)))
  apply (harmonic_cover_volume _ (hcov ω n) v B _ hvol).trans
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  apply (le_div_iff₀ (sqrt_pos.mpr hN)).mpr
  have hmul : r*sqrt N=sqrt A := div_mul_cancel₀ _ (sqrt_pos.mpr hN).ne'
  change (k:ℝ)*(M*(2*r))*sqrt N ≤ ((k:ℝ)*(M+1))*(2*sqrt A)
  nlinarith only [congrArg (fun x : ℝ => ((k:ℝ)*M)*x) hmul,
    mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (sqrt_nonneg A)]

/-- Outside O(1/√N) time in every fixed-length interval, three gates
are necessary and sufficient after an arbitrary change of basis. -/
theorem gaussian_inverse_root_exception_length (B : ℝ) :
    ∃ K > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ v : ℝ,
      volume.real ({t | ¬exactThreeAt (pathPauliDisorderShell ω n) t} ∩ Icc v (v+B)) ≤ K/sqrt (n+2:ℕ) := by
  obtain ⟨a,ha,hu⟩ := gaussian_grid_exception_length 512 (by decide) (by norm_num : (0:ℝ) < 1/512) B
  obtain ⟨b,hb,hl⟩ := gaussian_grid_exception_length 17408 (by decide) (by norm_num : (0:ℝ) < 1/(4*17408)) B
  refine ⟨a+b,add_pos ha hb,?_⟩
  filter_upwards [hu,hl] with ω hω hw
  filter_upwards [hω,hw,eventually_ge_atTop 7] with n hn hf hN
  intro v
  let u := pathPauliDisorderShell ω n
  let I := Icc v (v+B)
  let E := {t | ¬goodGrid u t 512 (1/512)}∩I
  let F := {t | ¬goodGrid u t 17408 (1/(4*17408))}∩I
  have hsub : {t | ¬exactThreeAt u t}∩I ⊆ E∪F := by
    intro t ht
    by_cases h : goodGrid u t 512 (1/512)
    · exact Or.inr ⟨fun h' => ht.1 (exact_three_of_grids hN u t h h'),ht.2⟩
    · exact Or.inl ⟨h,ht.2⟩
  have hfin : E∪F ⊆ I := union_subset inter_subset_right inter_subset_right
  exact (measureReal_mono hsub (measure_ne_top_of_subset hfin measure_Icc_lt_top.ne)).trans
    ((measureReal_union_le E F).trans ((add_le_add (hn v) (hf v)).trans_eq (add_div ..).symm))

#print axioms gaussian_inverse_root_exception_length
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
