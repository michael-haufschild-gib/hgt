import GaloisForLFunctions.RHTower.FokasLenellsSpaceDifferentiability

/-!
# Spatial derivatives of the actual RH forcing

Second-order scattering decay supplies an L² envelope for the spatial
jump derivative. Its diagonal is zero by cancellation of opposite phases.
The actual jump entries, rows, and projected Cauchy forcing are therefore
C¹ in position, with derivatives jointly continuous in space and time.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The exact spatial derivative of the regularized jump has zero diagonal. -/
def directJumpSpaceMatrix (q : SchwartzMap ℝ ℂ) (t x z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0,directSpaceSymbol q t x true z;-directSpaceSymbol q t x false z,0]

/-- The nonlinear diagonal term is independent of position, while the off-diagonal terms differentiate by opposite frequency factors. -/
theorem directJumpMatrix_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x z : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => regularJump (globalSmallScatteringPotential q) t s z i j)
      (directJumpSpaceMatrix q t x z i j) x := by
  fin_cases i <;> fin_cases j
  · exact hasDerivAt_const x (1:ℂ)
  · exact directSymbol_space_hasDerivAt q t x true z
  · exact (directSymbol_space_hasDerivAt q t x false z).neg
  · change HasDerivAt (fun s => 1-regularJumpReflection (globalSmallScatteringPotential q) t s z*
      regularJumpReverseReflection (globalSmallScatteringPotential q) t s z) 0 x
    simp only [regularJumpReflection_product]
    exact hasDerivAt_const x _

/-- One L² envelope controls all entries of the jump derivative at all times and positions. -/
def directJumpSpaceEnvelope (q : SchwartzMap ℝ ℂ) (z : ℝ) : ℝ :=
  (2 : ℝ)*(‖regularSpectralReflection q false z‖+‖regularSpectralReflection q true z‖)

theorem directJumpSpaceEnvelope_memLp (q : SchwartzMap ℝ ℂ) : MemLp (directJumpSpaceEnvelope q) 2 volume :=
  (((regularSpectralReflection_memLp q false).norm).add
    ((regularSpectralReflection_memLp q true).norm)).const_mul (2:ℝ)

theorem directJumpSpaceMatrix_entry_bound (q : SchwartzMap ℝ ℂ) (t x z : ℝ) (i j : Fin 2) :
    ‖directJumpSpaceMatrix q t x z i j‖ ≤ directJumpSpaceEnvelope q z := by
  fin_cases i <;> fin_cases j
  · change ‖(0:ℂ)‖ ≤ _
    rw [norm_zero]
    unfold directJumpSpaceEnvelope
    positivity
  · change ‖directSpaceSymbol q t x true z‖ ≤ _
    rw [directSpaceSymbol_norm]
    unfold directJumpSpaceEnvelope
    nlinarith [norm_nonneg (regularSpectralReflection q false z)]
  · change ‖-directSpaceSymbol q t x false z‖ ≤ _
    rw [norm_neg,directSpaceSymbol_norm]
    unfold directJumpSpaceEnvelope
    nlinarith [norm_nonneg (regularSpectralReflection q true z)]
  · change ‖(0:ℂ)‖ ≤ _
    rw [norm_zero]
    unfold directJumpSpaceEnvelope
    positivity

theorem directJumpSpaceMatrix_entry_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    MemLp (fun z => directJumpSpaceMatrix q t x z i j) 2 volume := by
  fin_cases i <;> fin_cases j
  · change MemLp (fun _ : ℝ => (0:ℂ)) 2 volume
    simp
  · exact directSpaceSymbol_memLp q t x true
  · exact (directSpaceSymbol_memLp q t x false).neg
  · change MemLp (fun _ : ℝ => (0:ℂ)) 2 volume
    simp

theorem continuous_directJumpSpaceMatrix_entry_parameters (q : SchwartzMap ℝ ℂ) (z : ℝ) (i j : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directJumpSpaceMatrix q p.1 p.2 z i j) := by
  fin_cases i <;> fin_cases j
  · exact continuous_const
  · exact continuous_directSpaceSymbol_parameters q true z
  · exact (continuous_directSpaceSymbol_parameters q false z).neg
  · exact continuous_const

/-- Each entry of the actual jump derivative represented as an L² class. -/
def directJumpSpaceEntry (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) : SoninL2 :=
  (directJumpSpaceMatrix_entry_memLp q t x i j).toLp (fun z => directJumpSpaceMatrix q t x z i j)

/-- The specific jump perturbation is differentiable in the strong L² topology. -/
theorem directJumpEntry_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => directJumpEntry q t s i j) (directJumpSpaceEntry q t x i j) x := by
  apply hasDerivAt_toLp_two_of_dominated volume
    (fun s z => (regularJump (globalSmallScatteringPotential q) t s z-(1 : Matrix (Fin 2) (Fin 2) ℂ)) i j)
    (fun s z => directJumpSpaceMatrix q t s z i j)
    (fun s => globalSmall_regularJump_sub_one_memLp q t s i j)
    (fun s => directJumpSpaceMatrix_entry_memLp q t s i j)
    (directJumpSpaceEnvelope q) (directJumpSpaceEnvelope_memLp q)
  · exact Eventually.of_forall fun z s =>
      (directJumpMatrix_space_hasDerivAt q t s z i j).sub_const ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)
  · exact Eventually.of_forall fun z s => directJumpSpaceMatrix_entry_bound q t s z i j

/-- The jump derivative itself depends jointly continuously on both physical parameters in L². -/
theorem continuous_directJumpSpaceEntry_parameters (q : SchwartzMap ℝ ℂ) (i j : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directJumpSpaceEntry q p.1 p.2 i j) := by
  apply continuous_toLp_two_of_dominated volume
    (fun p : ℝ × ℝ => fun z => directJumpSpaceMatrix q p.1 p.2 z i j)
    (fun p => directJumpSpaceMatrix_entry_memLp q p.1 p.2 i j)
    (directJumpSpaceEnvelope q) (directJumpSpaceEnvelope_memLp q)
  · intro p
    exact Eventually.of_forall fun z => directJumpSpaceMatrix_entry_bound q p.1 p.2 z i j
  · exact Eventually.of_forall fun z => continuous_directJumpSpaceMatrix_entry_parameters q z i j

/-- Every actual matrix-jump entry is C¹ as an L²-valued function of position. -/
theorem directJumpEntry_space_contDiff (q : SchwartzMap ℝ ℂ) (t : ℝ) (i j : Fin 2) :
    ContDiff ℝ 1 (fun x => directJumpEntry q t x i j) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (directJumpEntry_space_hasDerivAt q t x i j).differentiableAt,?_⟩
  have he : deriv (fun x => directJumpEntry q t x i j) = fun x => directJumpSpaceEntry q t x i j :=
    funext fun x => (directJumpEntry_space_hasDerivAt q t x i j).deriv
  rw [he]
  have hc : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hh := (continuous_directJumpSpaceEntry_parameters q i j).comp hc
  exact hh

/-- The derivative of the actual jump row in the two-channel L² space. -/
def directJumpSpaceRow (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  (directJumpSpaceEntry q t x i 0,directJumpSpaceEntry q t x i 1)

theorem directJumpRow_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directJumpRow q t s i) (directJumpSpaceRow q t x i) x :=
  (directJumpEntry_space_hasDerivAt q t x i 0).prodMk (directJumpEntry_space_hasDerivAt q t x i 1)

theorem continuous_directJumpSpaceRow_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directJumpSpaceRow q p.1 p.2 i) :=
  (continuous_directJumpSpaceEntry_parameters q i 0).prodMk (continuous_directJumpSpaceEntry_parameters q i 1)

/-- The derivative of the actual inhomogeneous Cauchy data is the projection of the differentiated jump row. -/
def directRHSpaceForcing (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  boundaryCauchy (directJumpSpaceRow q t x i)

/-- The actual forcing used by the constructed inverse has the differentiated Cauchy projection prescribed by the paper's mechanism. -/
theorem directRHForcing_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directRHForcing q t s i) (directRHSpaceForcing q t x i) x := by
  exact (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x
    (directJumpRow_space_hasDerivAt q t x i)

theorem continuous_directRHSpaceForcing_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directRHSpaceForcing q p.1 p.2 i) :=
  boundaryCauchy.continuous.comp (continuous_directJumpSpaceRow_parameters q i)

/-- The specific Cauchy-inverse forcing is C¹ in position in the L² product space. -/
theorem directRHForcing_space_contDiff (q : SchwartzMap ℝ ℂ) (t : ℝ) (i : Fin 2) :
    ContDiff ℝ 1 (fun x => directRHForcing q t x i) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (directRHForcing_space_hasDerivAt q t x i).differentiableAt,?_⟩
  have he : deriv (fun x => directRHForcing q t x i) = fun x => directRHSpaceForcing q t x i :=
    funext fun x => (directRHForcing_space_hasDerivAt q t x i).deriv
  rw [he]
  have hc : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hh := (continuous_directRHSpaceForcing_parameters q i).comp hc
  exact hh


end
end RHTower.FokasLenells
