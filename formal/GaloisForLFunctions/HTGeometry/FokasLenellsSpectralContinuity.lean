import GaloisForLFunctions.HTGeometry.FokasLenellsUniformizedScattering

/-!
# Joint spectral continuity from the Volterra factorial estimates

The kernel of the uniformized problem in arXiv:2607.19649v1 is affine and
uniformly Lipschitz in the complex spectral parameter. On every bounded
spectral and spatial neighborhood, the corpus's Volterra factorial bound
gives uniform convergence of the symbolic Picard series. This proves joint
continuity of the constructed solutions and fundamental matrices, including
uniformized parameter zero, for arbitrary Schwartz coefficient profiles.
-/

open Complex Matrix Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The spectral kernel is affine in the uniformized complex parameter. -/
theorem spectralKernel_sub (f g h : SchwartzMap ℝ ℂ) (z w : ℂ) (t s : ℝ) :
    spectralKernel f g h z t s-spectralKernel f g h w t s =
      pairOperator (I*(z-w)) 0 0 (-I*(z-w)) := by
  ext v <;> simp [spectralKernel, spectralEntries, pairOperator] <;> ring

/-- A uniform operator-norm Lipschitz bound in the spectral parameter. -/
theorem spectralKernel_parameter_bound (f g h : SchwartzMap ℝ ℂ) (z w : ℂ) (t s : ℝ) :
    ‖spectralKernel f g h z t s-spectralKernel f g h w t s‖ ≤ 2*‖z-w‖ := by
  rw [spectralKernel_sub]
  have hb := pairOperator_bound (I*(z-w)) 0 0 (-I*(z-w))
  simpa [norm_mul, two_mul] using hb

theorem spectralKernel_local_bound (f g h : SchwartzMap ℝ ℂ) (z w : ℂ) (t s : ℝ) :
    ‖spectralKernel f g h z t s‖ ≤ spectralMass f g h w+2*‖z-w‖ := by
  calc
    _ ≤ ‖spectralKernel f g h w t s‖+‖spectralKernel f g h z t s-spectralKernel f g h w t s‖ := by
      simpa only [add_sub_cancel] using norm_add_le (spectralKernel f g h w t s)
        (spectralKernel f g h z t s-spectralKernel f g h w t s)
    _ ≤ _ := add_le_add (spectralKernel_bound f g h w t s) (spectralKernel_parameter_bound f g h z w t s)

/-- Joint coefficient continuity precedes passage to the convergent Volterra series. -/
theorem continuous_spectralEntries_parameter (f g h : SchwartzMap ℝ ℂ) (i j : Fin 2) :
    Continuous (fun p : ℂ × ℝ => spectralEntries f g h p.1 i j p.2) := by
  fin_cases i <;> fin_cases j <;> simp [spectralEntries] <;> fun_prop

theorem continuous_spectralKernel_parameter (f g h : SchwartzMap ℝ ℂ) :
    Continuous (fun p : ℂ × ℝ => spectralKernel f g h p.1 0 p.2) := by
  have hU := ((continuous_spectralEntries_parameter f g h 0 0).smul
      (continuous_const : Continuous (fun _ : ℂ × ℝ => ContinuousLinearMap.fst ℝ ℂ ℂ))).add
    ((continuous_spectralEntries_parameter f g h 0 1).smul
      (continuous_const : Continuous (fun _ : ℂ × ℝ => ContinuousLinearMap.snd ℝ ℂ ℂ)))
  have hV := ((continuous_spectralEntries_parameter f g h 1 0).smul
      (continuous_const : Continuous (fun _ : ℂ × ℝ => ContinuousLinearMap.fst ℝ ℂ ℂ))).add
    ((continuous_spectralEntries_parameter f g h 1 1).smul
      (continuous_const : Continuous (fun _ : ℂ × ℝ => ContinuousLinearMap.snd ℝ ℂ ℂ)))
  exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := SpectralVector)
    (F := ℂ) (G := ℂ) ℝ).continuous.comp (hU.prodMk hV)

/-- Every symbolic Picard iterate is jointly continuous; no numerical iteration is used. -/
theorem continuous_spectralIterate_parameter (f g h : SchwartzMap ℝ ℂ) (v : SpectralVector) (n : ℕ) :
    Continuous (fun p : ℂ × ℝ => volterraIterate (fun _ => v) (spectralKernel f g h p.1) n p.2) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hK : Continuous (fun p : (ℂ × ℝ) × ℝ => spectralKernel f g h p.1.1 p.1.2 p.2) :=
      (continuous_spectralKernel_parameter f g h).comp
        (f := fun p : (ℂ × ℝ) × ℝ => (p.1.1,p.2)) (continuous_fst.fst.prodMk continuous_snd)
    have hu := ih.comp (f := fun p : (ℂ × ℝ) × ℝ => (p.1.1,p.2))
      (continuous_fst.fst.prodMk continuous_snd)
    have happ : Continuous (fun p : (ℂ × ℝ) × ℝ =>
        spectralKernel f g h p.1.1 p.1.2 p.2 (volterraIterate (fun _ => v) (spectralKernel f g h p.1.1) n p.2)) :=
      isBoundedBilinearMap_apply.continuous.comp (hK.prodMk hu)
    exact continuous_const.add (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℂ × ℝ) (s : ℝ) =>
        spectralKernel f g h p.1 p.2 s (volterraIterate (fun _ => v) (spectralKernel f g h p.1) n s))
      happ continuous_snd)

/-- Local uniform factorial convergence gives joint continuity for every complex spectrum and position. -/
theorem continuous_spectralSolution_parameter (f g h : SchwartzMap ℝ ℂ) (v : SpectralVector) :
    Continuous (fun p : ℂ × ℝ => spectralSolution f g h p.1 v p.2) := by
  refine continuous_iff_continuousAt.mpr fun p₀ => ?_
  let T : ℝ := |p₀.2|+1
  let M : ℝ := spectralMass f g h p₀.1+2
  let S : Set (ℂ × ℝ) := {p | ‖p.1-p₀.1‖ < 1 ∧ |p.2| < T}
  have hM : 0 ≤ M := by dsimp [M]; linarith [spectralMass_nonneg f g h p₀.1]
  have hopen : IsOpen S :=
    (isOpen_lt (continuous_fst.sub continuous_const).norm continuous_const).inter
      (isOpen_lt continuous_snd.abs continuous_const)
  have hmem : p₀ ∈ S := by simp [S, T]
  have hcont : ContinuousOn (fun p : ℂ × ℝ => spectralSolution f g h p.1 v p.2) S := by
    unfold spectralSolution volterraSolution
    refine ContinuousOn.add continuous_const.continuousOn ?_
    refine continuousOn_tsum
      (fun n => ((continuous_spectralIterate_parameter f g h v (n+1)).sub
        (continuous_spectralIterate_parameter f g h v n)).continuousOn)
      (summable_volterraBound (M := M) (T := T) (norm_nonneg v)) ?_
    intro n p hp
    have hKb : ∀ t s, ‖spectralKernel f g h p.1 t s‖ ≤ M := by
      intro t s
      have hl := spectralKernel_local_bound f g h p.1 p₀.1 t s
      dsimp [M]
      have hh : ‖p.1-p₀.1‖ < 1 := hp.1
      linarith
    refine (norm_volterraIterate_succ_sub_le continuous_const
      (continuous_spectralKernel f g h p.1) hM (norm_nonneg v) hKb (fun _ => le_rfl) n p.2).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg p.2) hp.2.le (n+1)) (by positivity)
  exact hcont.continuousAt (hopen.mem_nhds hmem)

/-- The constructed fundamental matrix varies continuously even at uniformized parameter zero. -/
theorem continuous_uniformizedFundamentalMatrix_parameter (f g h : SchwartzMap ℝ ℂ) :
    Continuous (fun p : ℂ × ℝ => uniformizedFundamentalMatrix f g h p.1 p.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · exact (continuous_spectralSolution_parameter f g h (1,0)).fst
  · exact (continuous_spectralSolution_parameter f g h (0,1)).fst
  · exact (continuous_spectralSolution_parameter f g h (1,0)).snd
  · exact (continuous_spectralSolution_parameter f g h (0,1)).snd

end
end GaloisForLFunctions.HTGeometry.FokasLenells
