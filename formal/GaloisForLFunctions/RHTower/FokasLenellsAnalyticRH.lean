import GaloisForLFunctions.RHTower.FokasLenellsCauchyFourier

/-!
# A holomorphic realization of the actual regularized Fokas–Lenells RH problem

For every explicitly normalized Schwartz potential, every position, and every
prescribed time, the density (I+lower correction)R is genuinely in L². Its
normalized Cauchy integral is holomorphic off the real axis. Its horizontal slices
have uniform L² bounds and converge strongly to the previously constructed upper
and lower corrections. Those boundary values satisfy the actual jump almost
everywhere and are unique in the intrinsic Hardy boundary class.

This supplies the analytic realization of the small-data RH inverse mechanism in
arXiv:2607.19649v1. Weighted Sobolev estimates and nonlinear reconstruction remain
separate mathematical tasks.
-/

open MeasureTheory Complex Set Filter Topology Matrix
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual row density in the paper's Cauchy reconstruction integral. -/
def directRHDensity (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  directJumpRow q t x i+directJumpPerturbation q t x (directLowerCorrection q t x i)

/-- The density has an explicit L² bound in terms of the actual jump row. -/
theorem directRHDensity_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ‖directRHDensity q t x i‖ ≤ (9/5 : ℝ)*‖directJumpRow q t x i‖ := by
  have h1 := directJumpPerturbation_bound q t x (directLowerCorrection q t x i)
  have h2 := directLowerCorrection_bound q t x i
  have h3 := norm_add_le (directJumpRow q t x i)
    (directJumpPerturbation q t x (directLowerCorrection q t x i))
  change ‖directJumpRow q t x i+directJumpPerturbation q t x (directLowerCorrection q t x i)‖ ≤ _
  linarith

def boundaryComponent (u : Boundary) (j : Fin 2) : SoninL2 := ![u.1,u.2] j

theorem boundaryComponent_bound (u : Boundary) (j : Fin 2) : ‖boundaryComponent u j‖ ≤ ‖u‖ := by
  fin_cases j
  · exact norm_fst_le u
  · exact norm_snd_le u

theorem directRHDensity_lower_component (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    negativeCauchy (boundaryComponent (directRHDensity q t x i) j) =
      boundaryComponent (directLowerCorrection q t x i) j := by
  have he := (directLowerCorrection_equation q t x i).symm
  fin_cases j
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

theorem directRHDensity_upper_component (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    boundaryComponent (directRHDensity q t x i) j+
      negativeCauchy (boundaryComponent (directRHDensity q t x i) j) =
      boundaryComponent (directUpperCorrection q t x i) j := by
  rw [directRHDensity_lower_component]
  fin_cases j <;> change _ = _+_ <;> exact add_comm _ _

/-- Each matrix entry is the identity plus the actual Cauchy reconstruction integral. -/
def directAnalyticMatrix (q : SchwartzMap ℝ ℂ) (t x : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (1 : Matrix (Fin 2) (Fin 2) ℂ) i j+
    cauchyExtension (boundaryComponent (directRHDensity q t x i) j) z

/-- Every reconstructed entry is holomorphic on both components of the complement of the contour. -/
theorem analyticOnNhd_directAnalyticMatrix_entry (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun z => directAnalyticMatrix q t x z i j) {z : ℂ | z.im ≠ 0} :=
  analyticOnNhd_const.add (analyticOnNhd_cauchyExtension _)

/-- Uniform point-evaluation control from the actual jump density, in either half-plane. -/
theorem directAnalyticMatrix_entry_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i j : Fin 2) (upper : Bool) (r a : ℝ) :
    ‖directAnalyticMatrix q t x (halfPlanePoint upper r a) i j-(1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤
      (2*Real.pi)⁻¹ * Real.sqrt (Real.pi/Real.exp a) * ((9/5 : ℝ)*‖directJumpRow q t x i‖) := by
  simp only [directAnalyticMatrix,add_sub_cancel_left]
  exact (cauchyExtension_bound _ upper r a).trans
    (mul_le_mul_of_nonneg_left
      ((boundaryComponent_bound _ j).trans (directRHDensity_bound q t x i)) (by positivity))

/-- Normalization at vertical infinity holds with arbitrary horizontal drift. -/
theorem directAnalyticMatrix_tendsto_vertical_infinity (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (upper : Bool) (r : ℝ → ℝ) (i j : Fin 2) :
    Tendsto (fun a => directAnalyticMatrix q t x (halfPlanePoint upper (r a) a) i j) atTop
      (𝓝 ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)) := by
  simpa only [directAnalyticMatrix,add_zero] using
    (cauchyExtension_tendsto_vertical_infinity (boundaryComponent (directRHDensity q t x i) j) upper r).const_add
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)

/-- The actual horizontal row correction, represented in L² × L². -/
def directAnalyticSlice (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) : Boundary :=
  (cauchySlice (directRHDensity q t x i).1 upper a,cauchySlice (directRHDensity q t x i).2 upper a)

/-- The L² representative consists of the actual values of the holomorphic matrix along the line. -/
theorem directAnalyticSlice_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    normalizedBoundaryRow i (directAnalyticSlice q t x i upper a) =ᵐ[volume]
      (fun r => (directAnalyticMatrix q t x (halfPlanePoint upper r a) i 0,
        directAnalyticMatrix q t x (halfPlanePoint upper r a) i 1)) := by
  filter_upwards [(cauchyExtension_slice_memLp (directRHDensity q t x i).1 upper a).coeFn_toLp,
    (cauchyExtension_slice_memLp (directRHDensity q t x i).2 upper a).coeFn_toLp] with r h1 h2
  apply Prod.ext
  · exact congrArg ((1 : Matrix (Fin 2) (Fin 2) ℂ) i 0+·) h1
  · exact congrArg ((1 : Matrix (Fin 2) (Fin 2) ℂ) i 1+·) h2

/-- Uniform Hardy L² bounds hold at every height in either half-plane. -/
theorem directAnalyticSlice_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (a : ℝ) :
    ‖directAnalyticSlice q t x i upper a‖ ≤ (9/5 : ℝ)*‖directJumpRow q t x i‖ := by
  apply le_trans _ (directRHDensity_bound q t x i)
  exact max_le_max (cauchySlice_bound _ upper a) (cauchySlice_bound _ upper a)

/-- The lower boundary of the holomorphic matrix is the constructed lower RH correction. -/
theorem directAnalyticSlice_lower_tendsto (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    Tendsto (directAnalyticSlice q t x i false) atBot (𝓝 (directLowerCorrection q t x i)) := by
  have h0 := cauchySlice_lower_tendsto (directRHDensity q t x i).1
  have h1 := cauchySlice_lower_tendsto (directRHDensity q t x i).2
  have he := directLowerCorrection_equation q t x i
  rw [he]
  exact h0.prodMk_nhds h1

/-- The upper boundary of the holomorphic matrix is the constructed upper RH correction. -/
theorem directAnalyticSlice_upper_tendsto (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    Tendsto (directAnalyticSlice q t x i true) atBot (𝓝 (directUpperCorrection q t x i)) := by
  have h0 := cauchySlice_upper_tendsto (directRHDensity q t x i).1
  have h1 := cauchySlice_upper_tendsto (directRHDensity q t x i).2
  have he : ((directRHDensity q t x i).1+negativeCauchy (directRHDensity q t x i).1,
      (directRHDensity q t x i).2+negativeCauchy (directRHDensity q t x i).2) =
      directUpperCorrection q t x i :=
    Prod.ext (directRHDensity_upper_component q t x i 0) (directRHDensity_upper_component q t x i 1)
  rw [← he]
  exact h0.prodMk_nhds h1

/-- The upper boundary inherits the same sharp row bound as the lower boundary. -/
theorem directUpperCorrection_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ‖directUpperCorrection q t x i‖ ≤ (9/5 : ℝ)*‖directJumpRow q t x i‖ := by
  exact le_of_tendsto (directAnalyticSlice_upper_tendsto q t x i |>.norm)
    (Filter.Eventually.of_forall fun a => directAnalyticSlice_bound q t x i true a)

/-- The actual holomorphic slices realize the unique intrinsic Hardy RH boundary pair. -/
theorem directAnalyticRH_realizes_boundary (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    Tendsto (directAnalyticSlice q t x i false) atBot (𝓝 (directLowerCorrection q t x i)) ∧
    Tendsto (directAnalyticSlice q t x i true) atBot (𝓝 (directUpperCorrection q t x i)) ∧
    directBoundaryRow q t x i true =ᵐ[volume]
      (fun z => matrixVector (regularJump (globalSmallScatteringPotential q) t x z).transpose
        (directBoundaryRow q t x i false z)) :=
  ⟨directAnalyticSlice_lower_tendsto q t x i,directAnalyticSlice_upper_tendsto q t x i,
    directBoundaryRow_jump q t x i⟩

end
end RHTower.FokasLenells
