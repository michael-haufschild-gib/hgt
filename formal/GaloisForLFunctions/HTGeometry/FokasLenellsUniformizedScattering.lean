import GaloisForLFunctions.HTGeometry.FokasLenellsUniformizedFrame

/-!
# Uniformized scattering with spectral-independent bounds

The effective-potential Volterra equation from arXiv:2607.19649 is a unique
classical linear ODE. Its Wronskians, endpoint determinants and scattering
determinant are exactly preserved. The endpoint displacement estimates give
a bound for every scattering entry independent of the real uniformized
spectral parameter. These estimates are conservative versions of (3.12)–(3.13).

All potential profiles are arbitrary Schwartz functions. Classical uniqueness,
complex linearity and all inverse matrices are proved without additional
hypotheses. Comparison with the original scattering convention is separate.
-/

open Complex Matrix MeasureTheory Filter
open scoped Topology Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section


/-- The Volterra solution is the unique global classical solution, not merely an integral solution. -/
theorem spectralSolution_existsUnique_differential (f g h : SchwartzMap ℝ ℂ) (z : ℂ) (v : SpectralVector) :
    ∃! u : ℝ → SpectralVector, u 0 = v ∧
      ∀ x, HasDerivAt u (spectralKernel f g h z x x (u x)) x := by
  refine ⟨spectralSolution f g h z v,
    ⟨spectralSolution_initial f g h z v, spectralSolution_hasDerivAt f g h z v⟩, ?_⟩
  intro u hu
  have hc : Continuous u := (show Differentiable ℝ u from fun x => (hu.2 x).differentiableAt).continuous
  have hK : Continuous (fun x : ℝ => spectralKernel f g h z 0 x) :=
    (continuous_spectralKernel f g h z).comp (f := fun x : ℝ => ((0:ℝ), x))
      (continuous_const.prodMk continuous_id)
  have hi : ∀ x, u x = v+∫ y in (0:ℝ)..x, spectralKernel f g h z x y (u y) := by
    intro x
    have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hu.2 y)
      ((hK.clm_apply hc).intervalIntegrable 0 x)
    rw [hu.1] at hd
    simpa only [add_comm, spectralKernel] using (sub_eq_iff_eq_add.mp hd.symm)
  exact (spectralSolution_existsUnique f g h z v).unique ⟨hc,hi⟩
    ⟨continuous_spectralSolution f g h z v, spectralSolution_equation f g h z v⟩

theorem pairOperator_complex_smul (a b c d r : ℂ) (v : SpectralVector) :
    pairOperator a b c d (r • v) = r • pairOperator a b c d v := by
  apply Prod.ext <;> simp [pairOperator] <;> ring

/-- Two basis solutions recover every initial vector by complex linearity. -/
theorem spectralSolution_linear_coordinates (f g h : SchwartzMap ℝ ℂ) (z : ℂ)
    (v : SpectralVector) (x : ℝ) :
    spectralSolution f g h z v x =
      v.1 • spectralSolution f g h z (1,0) x+v.2 • spectralSolution f g h z (0,1) x := by
  have hs : ∃! u : ℝ → SpectralVector, u 0 = v ∧
      ∀ x, HasDerivAt u (spectralKernel f g h z x x (u x)) x :=
    spectralSolution_existsUnique_differential f g h z v
  have hr : (fun y => v.1 • spectralSolution f g h z (1,0) y+
      v.2 • spectralSolution f g h z (0,1) y) 0 = v ∧
      ∀ y, HasDerivAt (fun s => v.1 • spectralSolution f g h z (1,0) s+
        v.2 • spectralSolution f g h z (0,1) s)
        (spectralKernel f g h z y y
          (v.1 • spectralSolution f g h z (1,0) y+v.2 • spectralSolution f g h z (0,1) y)) y := by
    constructor
    · simp [spectralSolution_initial]
    · intro y
      have hd := ((spectralSolution_hasDerivAt f g h z (1,0) y).const_smul v.1).fun_add
        ((spectralSolution_hasDerivAt f g h z (0,1) y).const_smul v.2)
      simpa only [Pi.smul_apply, map_add, spectralKernel, pairOperator_complex_smul] using hd
  exact congrFun (hs.unique (y₂ := fun y => v.1 • spectralSolution f g h z (1,0) y+
    v.2 • spectralSolution f g h z (0,1) y)
    ⟨spectralSolution_initial f g h z v, spectralSolution_hasDerivAt f g h z v⟩ hr) x

def uniformizedFundamentalMatrix (f g h : SchwartzMap ℝ ℂ) (z : ℂ) (x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(spectralSolution f g h z (1,0) x).1,(spectralSolution f g h z (0,1) x).1;
    (spectralSolution f g h z (1,0) x).2,(spectralSolution f g h z (0,1) x).2]

theorem uniformizedFundamentalMatrix_apply (f g h : SchwartzMap ℝ ℂ) (z : ℂ)
    (x : ℝ) (v : SpectralVector) :
    matrixVector (uniformizedFundamentalMatrix f g h z x) v = spectralSolution f g h z v x := by
  rw [spectralSolution_linear_coordinates f g h z v x]
  apply Prod.ext <;>
    simp [matrixVector, uniformizedFundamentalMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- Trace-free uniformized evolution preserves the exact Wronskian of arbitrary initial columns. -/
theorem spectralSolution_wedge (f g h : SchwartzMap ℝ ℂ) (z : ℂ)
    (v w : SpectralVector) (x : ℝ) :
    (spectralSolution f g h z v x).1*(spectralSolution f g h z w x).2-
      (spectralSolution f g h z v x).2*(spectralSolution f g h z w x).1 = v.1*w.2-v.2*w.1 := by
  let W : ℝ → ℂ := fun y =>
    (spectralSolution f g h z v y).1*(spectralSolution f g h z w y).2-
      (spectralSolution f g h z v y).2*(spectralSolution f g h z w y).1
  have hd : ∀ y, HasDerivAt W 0 y := by
    intro y
    have hv := spectralSolution_hasDerivAt f g h z v y
    have hw := spectralSolution_hasDerivAt f g h z w y
    have hv1 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt y hv
    have hv2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt y hv
    have hw1 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt y hw
    have hw2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt y hw
    refine ((hv1.fun_mul hw2).fun_sub (hv2.fun_mul hw1)).congr_deriv ?_
    simp [spectralKernel, spectralEntries, pairOperator]
    ring
  have he := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt) (fun y => (hd y).deriv) x 0
  simpa only [W, spectralSolution_initial] using he

theorem uniformizedFundamentalMatrix_det (f g h : SchwartzMap ℝ ℂ) (z : ℂ) (x : ℝ) :
    (uniformizedFundamentalMatrix f g h z x).det = 1 := by
  simpa [uniformizedFundamentalMatrix, Matrix.det_fin_two, mul_comm] using
    spectralSolution_wedge f g h z (1,0) (0,1) x

theorem uniformizedOrbit_wedge (f g h : SchwartzMap ℝ ℂ) (z : ℝ)
    (v w : SpectralVector) (b : Bool) (x : ℝ) :
    (uniformizedOrbit f g h z v b x).1*(uniformizedOrbit f g h z w b x).2-
      (uniformizedOrbit f g h z v b x).2*(uniformizedOrbit f g h z w b x).1 = v.1*w.2-v.2*w.1 := by
  rw [uniformizedOrbit, uniformizedOrbit, uniformizedInteractionSolution,
    uniformizedInteractionSolution, rotatingFrame_wedge]
  exact spectralSolution_wedge f g h (z:ℂ) v w _

theorem uniformizedAsymptoticVector_wedge (f g h : SchwartzMap ℝ ℂ) (z : ℝ)
    (v w : SpectralVector) (b : Bool) :
    (uniformizedAsymptoticVector f g h z v b).1*(uniformizedAsymptoticVector f g h z w b).2-
      (uniformizedAsymptoticVector f g h z v b).2*(uniformizedAsymptoticVector f g h z w b).1 = v.1*w.2-v.2*w.1 := by
  have hv := uniformizedOrbit_tendsto f g h z v b
  have hw := uniformizedOrbit_tendsto f g h z w b
  have ht := (hv.fst_nhds.mul hw.snd_nhds).sub (hv.snd_nhds.mul hw.fst_nhds)
  simp only [uniformizedOrbit_wedge] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

def uniformizedAsymptoticMatrix (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (b : Bool) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(uniformizedAsymptoticVector f g h z (1,0) b).1,(uniformizedAsymptoticVector f g h z (0,1) b).1;
    (uniformizedAsymptoticVector f g h z (1,0) b).2,(uniformizedAsymptoticVector f g h z (0,1) b).2]

theorem uniformizedAsymptoticMatrix_det (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (b : Bool) :
    (uniformizedAsymptoticMatrix f g h z b).det = 1 := by
  simpa [uniformizedAsymptoticMatrix, Matrix.det_fin_two, mul_comm] using
    uniformizedAsymptoticVector_wedge f g h z (1,0) (0,1) b

/-- The two constructed uniformized endpoint bases define their own scattering matrix. -/
def uniformizedScatteringMatrix (f g h : SchwartzMap ℝ ℂ) (z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  uniformizedAsymptoticMatrix f g h z false*(uniformizedAsymptoticMatrix f g h z true)⁻¹

theorem uniformizedScatteringMatrix_det (f g h : SchwartzMap ℝ ℂ) (z : ℝ) :
    (uniformizedScatteringMatrix f g h z).det = 1 := by
  rw [uniformizedScatteringMatrix, Matrix.det_mul, uniformizedAsymptoticMatrix_det,
    Matrix.det_nonsing_inv, uniformizedAsymptoticMatrix_det]
  simp

def effectiveDisplacement (f g h : SchwartzMap ℝ ℂ) : ℝ :=
  Real.exp (effectiveMass f g h)*effectiveMass f g h

theorem effectiveDisplacement_nonneg (f g h : SchwartzMap ℝ ℂ) :
    0 ≤ effectiveDisplacement f g h := mul_nonneg (Real.exp_pos _).le (effectiveMass_nonneg _ _ _)

theorem uniformizedAsymptoticMatrix_entry_displacement (f g h : SchwartzMap ℝ ℂ)
    (z : ℝ) (b : Bool) (i j : Fin 2) :
    ‖uniformizedAsymptoticMatrix f g h z b i j-(1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤
      effectiveDisplacement f g h := by
  have h0 := uniformizedAsymptoticVector_displacement f g h z (1,0) b
  have h1 := uniformizedAsymptoticVector_displacement f g h z (0,1) b
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, norm_one, norm_zero,
    max_eq_left (show (0:ℝ) ≤ 1 by positivity), max_eq_right (show (0:ℝ) ≤ 1 by positivity),
    one_mul, sub_zero] at h0 h1
  fin_cases i <;> fin_cases j
  · simpa [uniformizedAsymptoticMatrix, effectiveDisplacement] using (max_le_iff.mp h0).1
  · simpa [uniformizedAsymptoticMatrix, effectiveDisplacement] using (max_le_iff.mp h1).1
  · simpa [uniformizedAsymptoticMatrix, effectiveDisplacement] using (max_le_iff.mp h0).2
  · simpa [uniformizedAsymptoticMatrix, effectiveDisplacement] using (max_le_iff.mp h1).2

theorem uniformizedAsymptoticMatrix_entry_bound (f g h : SchwartzMap ℝ ℂ)
    (z : ℝ) (b : Bool) (i j : Fin 2) :
    ‖uniformizedAsymptoticMatrix f g h z b i j‖ ≤ effectiveDisplacement f g h+1 := by
  have he := uniformizedAsymptoticMatrix_entry_displacement f g h z b i j
  have hI : ‖(1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ 1 := by
    fin_cases i <;> fin_cases j <;> simp
  have hn := norm_add_le
    (uniformizedAsymptoticMatrix f g h z b i j-(1 : Matrix (Fin 2) (Fin 2) ℂ) i j)
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)
  rw [sub_add_cancel] at hn
  exact hn.trans (add_le_add he hI)

theorem uniformizedAsymptoticMatrix_inverse_entry_bound (f g h : SchwartzMap ℝ ℂ)
    (z : ℝ) (b : Bool) (i j : Fin 2) :
    ‖(uniformizedAsymptoticMatrix f g h z b)⁻¹ i j‖ ≤ effectiveDisplacement f g h+1 := by
  rw [Matrix.inv_def, uniformizedAsymptoticMatrix_det]
  simp only [Ring.inverse_one, one_smul, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · exact uniformizedAsymptoticMatrix_entry_bound f g h z b 1 1
  · change ‖-uniformizedAsymptoticMatrix f g h z b 0 1‖ ≤ _
    rw [norm_neg]
    exact uniformizedAsymptoticMatrix_entry_bound f g h z b 0 1
  · change ‖-uniformizedAsymptoticMatrix f g h z b 1 0‖ ≤ _
    rw [norm_neg]
    exact uniformizedAsymptoticMatrix_entry_bound f g h z b 1 0
  · exact uniformizedAsymptoticMatrix_entry_bound f g h z b 0 0

/-- Every scattering entry is bounded independently of the real spectral variable. -/
theorem uniformizedScatteringMatrix_entry_displacement (f g h : SchwartzMap ℝ ℂ)
    (z : ℝ) (i j : Fin 2) :
    ‖uniformizedScatteringMatrix f g h z i j-(1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤
      4*effectiveDisplacement f g h*(1+effectiveDisplacement f g h) := by
  let R := uniformizedAsymptoticMatrix f g h z false
  let L := uniformizedAsymptoticMatrix f g h z true
  let δ := effectiveDisplacement f g h
  have hn : 0 ≤ δ := effectiveDisplacement_nonneg f g h
  have hL : L*L⁻¹ = 1 := Matrix.mul_nonsing_inv _
    (by change IsUnit (uniformizedAsymptoticMatrix f g h z true).det
        rw [uniformizedAsymptoticMatrix_det]; exact isUnit_one)
  have he : uniformizedScatteringMatrix f g h z-1 = (R-L)*L⁻¹ := by
    rw [sub_mul, hL]
    rfl
  have hd : ∀ i j, ‖(R-L) i j‖ ≤ 2*δ := by
    intro i j
    calc
      ‖(R-L) i j‖ = ‖(R i j-(1 : Matrix (Fin 2) (Fin 2) ℂ) i j)-
          (L i j-(1 : Matrix (Fin 2) (Fin 2) ℂ) i j)‖ := by congr 1; simp
      _ ≤ ‖R i j-(1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖+
          ‖L i j-(1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ := norm_sub_le _ _
      _ ≤ δ+δ := add_le_add
        (uniformizedAsymptoticMatrix_entry_displacement f g h z false i j)
        (uniformizedAsymptoticMatrix_entry_displacement f g h z true i j)
      _ = _ := by ring
  have hi : ∀ i j, ‖L⁻¹ i j‖ ≤ δ+1 := uniformizedAsymptoticMatrix_inverse_entry_bound f g h z true
  change ‖(uniformizedScatteringMatrix f g h z-1) i j‖ ≤ _
  rw [he]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  calc
    ‖(R-L) i 0*L⁻¹ 0 j+(R-L) i 1*L⁻¹ 1 j‖ ≤
        ‖(R-L) i 0‖*‖L⁻¹ 0 j‖+‖(R-L) i 1‖*‖L⁻¹ 1 j‖ := by
      simpa only [norm_mul] using norm_add_le ((R-L) i 0*L⁻¹ 0 j) ((R-L) i 1*L⁻¹ 1 j)
    _ ≤ (2*δ)*(δ+1)+(2*δ)*(δ+1) := add_le_add
      (mul_le_mul (hd i 0) (hi 0 j) (norm_nonneg _) (by positivity))
      (mul_le_mul (hd i 1) (hi 1 j) (norm_nonneg _) (by positivity))
    _ = _ := by ring

end
end GaloisForLFunctions.HTGeometry.FokasLenells
