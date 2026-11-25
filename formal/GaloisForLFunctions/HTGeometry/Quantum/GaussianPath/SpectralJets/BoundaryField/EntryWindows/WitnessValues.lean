import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.Pencil
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.WindingForecast
import GaloisForLFunctions.HTGeometry.AveragedCentralizerProjectionFloor
import GaloisForLFunctions.HTGeometry.DivisorHeightRatioGate

/-! # Bounded field witnesses for all winding polynomials at one forecast date -/

open Matrix Set Real Polynomial
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
noncomputable section
variable {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]

private theorem exists_real_witness (p : ℂ[X]) (hp : p≠0) : ∃ y : ℝ, p.eval (y:ℂ)≠0 := by
  obtain ⟨y,_,hy⟩ := (Set.infinite_univ : (univ : Set ℝ).Infinite).exists_notMem_finset (SpectralJets.lineCuts p)
  exact ⟨y,fun hz => hy (SpectralJets.mem_lineCuts hp hz)⟩

/-- For a gap forecast larger than the entire baseline bandwidth by at
least one, the determinant already has modulus at least one at zero field. -/
theorem large_gap_witness (A Z : Matrix I I ℂ) (hA : A.IsHermitian) {b : ℝ} (hb : 2*‖A‖+1≤|b|) :
    1≤‖(gapPencil A Z b).det.eval 0‖ := by
  have he := eval_gapPencil A Z b 0
  simp only [Complex.ofReal_zero,zero_smul,add_zero] at he
  rw [he,gap_determinant A hA,norm_prod]
  apply Finset.one_le_prod
  intro p _
  simp only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  let g := hA.eigenvalues p.1-hA.eigenvalues p.2
  have hg : |g|≤2*‖A‖ := (abs_sub _ _).trans (by linarith only
    [abs_eigenvalue_le_l2_opNorm hA p.1,abs_eigenvalue_le_l2_opNorm hA p.2])
  have ht := abs_add_le (b-g) g
  rw [sub_add_cancel] at ht
  linarith only [hb,hg,ht]

/-- Although the winding is unbounded, a bounded set of field settings
witnesses a common positive lower value of all the corresponding gap
polynomials. Only finitely many windings need witnesses away from zero. -/
theorem winding_witnesses (A Z : Matrix I I ℂ) (hA : A.IsHermitian) {T x : ℝ} (hT : 0<T)
    (hx : x∈Icc (0:ℝ) 1) (hn : ∀ n : ℤ, (gapPencil A Z ((2*π)*((n:ℝ)+x)/T)).det≠0) :
    ∃ B≥(0:ℝ), ∃ c> (0:ℝ), ∀ n : ℤ, ∃ y : ℝ, |y|≤B ∧
      c≤‖(gapPencil A Z ((2*π)*((n:ℝ)+x)/T)).det.eval (y:ℂ)‖ := by
  classical
  let L := 2*‖A‖+1
  let b (n : ℤ) := (2*π)*((n:ℝ)+x)/T
  let P (n : ℤ) := (gapPencil A Z (b n)).det
  have hL : 0≤L := by dsimp only [L]; linarith only [norm_nonneg A]
  let F := windingBox T L
  have hF := winding_forecast hT hL hx
  choose y hy using fun n : F => exists_real_witness (P n.val) (hn _)
  let w (n : F) := ‖(P n.val).eval (y n:ℂ)‖
  obtain ⟨c,hc,hl⟩ := exists_pos_lowerBound_of_finite_pos (finite_range w)
    (fun _ ⟨n,he⟩ => he ▸ norm_pos_iff.mpr (hy n))
  let B := ∑ n : F, |y n|
  have hB : 0≤B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨B,hB,min c 1,lt_min hc zero_lt_one,fun n => ?_⟩
  by_cases h : n∈F
  · let m : F := ⟨n,h⟩
    exact ⟨y m,Finset.single_le_sum (f:=fun j : F => |y j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ m),
      (min_le_left ..).trans (hl _ ⟨m,rfl⟩)⟩
  · have hbig : L≤|b n| := le_of_not_gt fun hh => h (hF T (b n) n hT (by simp) hh.le rfl).1
    refine ⟨0,by simpa only [abs_zero] using hB,?_⟩
    simpa only [Complex.ofReal_zero] using (min_le_right c 1).trans (large_gap_witness A Z hA hbig)

#print axioms winding_witnesses
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
