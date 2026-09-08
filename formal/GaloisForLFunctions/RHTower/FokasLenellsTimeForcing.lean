import GaloisForLFunctions.RHTower.FokasLenellsTimeDifferentiability

/-!
# C¹ time dependence of the actual RH jump and forcing

The opposite time phases cancel in the nonlinear diagonal jump entry. Hence
the full time derivative has only two off-diagonal entries. Their proved L²
envelope validates strong differentiation of every actual jump entry, both
jump rows, and the projected forcing used by the Cauchy inverse. The derivative
is jointly continuous in time and position. No arbitrary forcing or unproved
regularity of scattering data is supplied to these results.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The exact time derivative of the regularized jump has zero diagonal. -/
def directJumpTimeMatrix (q : SchwartzMap ℝ ℂ) (t x z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0,directTimeSymbol q t x true z;-directTimeSymbol q t x false z,0]

/-- The nonlinear diagonal term is time independent, while the off-diagonal terms differentiate by opposite inverse-frequency factors. -/
theorem directJumpMatrix_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x z : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => regularJump (globalSmallScatteringPotential q) s x z i j)
      (directJumpTimeMatrix q t x z i j) t := by
  fin_cases i <;> fin_cases j
  · exact hasDerivAt_const t (1:ℂ)
  · exact directSymbol_time_hasDerivAt q t x true z
  · exact (directSymbol_time_hasDerivAt q t x false z).neg
  · change HasDerivAt (fun s => 1-regularJumpReflection (globalSmallScatteringPotential q) s x z*
      regularJumpReverseReflection (globalSmallScatteringPotential q) s x z) 0 t
    simp only [regularJumpReflection_product]
    exact hasDerivAt_const t _

/-- One L² envelope controls all entries of the jump derivative at all times and positions. -/
def directJumpTimeEnvelope (q : SchwartzMap ℝ ℂ) (z : ℝ) : ℝ :=
  (1/2 : ℝ)*(‖regularInverseFrequencyReflection q false z‖+‖regularInverseFrequencyReflection q true z‖)

theorem directJumpTimeEnvelope_memLp (q : SchwartzMap ℝ ℂ) : MemLp (directJumpTimeEnvelope q) 2 volume :=
  (((regularInverseFrequencyReflection_memLp q false).norm).add
    ((regularInverseFrequencyReflection_memLp q true).norm)).const_mul (1/2:ℝ)

theorem directJumpTimeMatrix_entry_bound (q : SchwartzMap ℝ ℂ) (t x z : ℝ) (i j : Fin 2) :
    ‖directJumpTimeMatrix q t x z i j‖ ≤ directJumpTimeEnvelope q z := by
  fin_cases i <;> fin_cases j
  · change ‖(0:ℂ)‖ ≤ _
    rw [norm_zero]
    unfold directJumpTimeEnvelope
    positivity
  · change ‖directTimeSymbol q t x true z‖ ≤ _
    rw [directTimeSymbol_norm]
    unfold directJumpTimeEnvelope
    nlinarith [norm_nonneg (regularInverseFrequencyReflection q false z)]
  · change ‖-directTimeSymbol q t x false z‖ ≤ _
    rw [norm_neg,directTimeSymbol_norm]
    unfold directJumpTimeEnvelope
    nlinarith [norm_nonneg (regularInverseFrequencyReflection q true z)]
  · change ‖(0:ℂ)‖ ≤ _
    rw [norm_zero]
    unfold directJumpTimeEnvelope
    positivity

theorem directJumpTimeMatrix_entry_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    MemLp (fun z => directJumpTimeMatrix q t x z i j) 2 volume := by
  fin_cases i <;> fin_cases j
  · change MemLp (fun _ : ℝ => (0:ℂ)) 2 volume
    simp
  · exact directTimeSymbol_memLp q t x true
  · exact (directTimeSymbol_memLp q t x false).neg
  · change MemLp (fun _ : ℝ => (0:ℂ)) 2 volume
    simp

theorem continuous_directJumpTimeMatrix_entry_parameters (q : SchwartzMap ℝ ℂ) (z : ℝ) (i j : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directJumpTimeMatrix q p.1 p.2 z i j) := by
  fin_cases i <;> fin_cases j
  · exact continuous_const
  · exact continuous_directTimeSymbol_parameters q true z
  · exact (continuous_directTimeSymbol_parameters q false z).neg
  · exact continuous_const

/-- Each entry of the actual jump derivative represented as an L² class. -/
def directJumpTimeEntry (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) : SoninL2 :=
  (directJumpTimeMatrix_entry_memLp q t x i j).toLp (fun z => directJumpTimeMatrix q t x z i j)

/-- The specific jump perturbation is differentiable in the strong L² topology. -/
theorem directJumpEntry_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => directJumpEntry q s x i j) (directJumpTimeEntry q t x i j) t := by
  apply hasDerivAt_toLp_two_of_dominated volume
    (fun s z => (regularJump (globalSmallScatteringPotential q) s x z-(1 : Matrix (Fin 2) (Fin 2) ℂ)) i j)
    (fun s z => directJumpTimeMatrix q s x z i j)
    (fun s => globalSmall_regularJump_sub_one_memLp q s x i j)
    (fun s => directJumpTimeMatrix_entry_memLp q s x i j)
    (directJumpTimeEnvelope q) (directJumpTimeEnvelope_memLp q)
  · exact Eventually.of_forall fun z s =>
      (directJumpMatrix_time_hasDerivAt q s x z i j).sub_const ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)
  · exact Eventually.of_forall fun z s => directJumpTimeMatrix_entry_bound q s x z i j

/-- The jump derivative itself depends jointly continuously on both physical parameters in L². -/
theorem continuous_directJumpTimeEntry_parameters (q : SchwartzMap ℝ ℂ) (i j : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directJumpTimeEntry q p.1 p.2 i j) := by
  apply continuous_toLp_two_of_dominated volume
    (fun p : ℝ × ℝ => fun z => directJumpTimeMatrix q p.1 p.2 z i j)
    (fun p => directJumpTimeMatrix_entry_memLp q p.1 p.2 i j)
    (directJumpTimeEnvelope q) (directJumpTimeEnvelope_memLp q)
  · intro p
    exact Eventually.of_forall fun z => directJumpTimeMatrix_entry_bound q p.1 p.2 z i j
  · exact Eventually.of_forall fun z => continuous_directJumpTimeMatrix_entry_parameters q z i j

/-- Every actual matrix-jump entry is C¹ as an L²-valued function of time. -/
theorem directJumpEntry_time_contDiff (q : SchwartzMap ℝ ℂ) (x : ℝ) (i j : Fin 2) :
    ContDiff ℝ 1 (fun t => directJumpEntry q t x i j) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (directJumpEntry_time_hasDerivAt q t x i j).differentiableAt,?_⟩
  have he : deriv (fun t => directJumpEntry q t x i j) = fun t => directJumpTimeEntry q t x i j :=
    funext fun t => (directJumpEntry_time_hasDerivAt q t x i j).deriv
  rw [he]
  have hc : Continuous (fun t : ℝ => (t,x)) := continuous_id.prodMk continuous_const
  have hh := (continuous_directJumpTimeEntry_parameters q i j).comp hc
  exact hh

/-- The derivative of the actual jump row in the two-channel L² space. -/
def directJumpTimeRow (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  (directJumpTimeEntry q t x i 0,directJumpTimeEntry q t x i 1)

theorem directJumpRow_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directJumpRow q s x i) (directJumpTimeRow q t x i) t :=
  (directJumpEntry_time_hasDerivAt q t x i 0).prodMk (directJumpEntry_time_hasDerivAt q t x i 1)

theorem continuous_directJumpTimeRow_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directJumpTimeRow q p.1 p.2 i) :=
  (continuous_directJumpTimeEntry_parameters q i 0).prodMk (continuous_directJumpTimeEntry_parameters q i 1)

/-- The derivative of the actual inhomogeneous Cauchy data is the projection of the differentiated jump row. -/
def directRHTimeForcing (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  boundaryCauchy (directJumpTimeRow q t x i)

/-- The actual forcing used by the constructed inverse has the differentiated Cauchy projection prescribed by the paper's mechanism. -/
theorem directRHForcing_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directRHForcing q s x i) (directRHTimeForcing q t x i) t := by
  exact (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (directJumpRow_time_hasDerivAt q t x i)

theorem continuous_directRHTimeForcing_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directRHTimeForcing q p.1 p.2 i) :=
  boundaryCauchy.continuous.comp (continuous_directJumpTimeRow_parameters q i)

/-- The specific Cauchy-inverse forcing is C¹ in time in the L² product space. -/
theorem directRHForcing_time_contDiff (q : SchwartzMap ℝ ℂ) (x : ℝ) (i : Fin 2) :
    ContDiff ℝ 1 (fun t => directRHForcing q t x i) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (directRHForcing_time_hasDerivAt q t x i).differentiableAt,?_⟩
  have he : deriv (fun t => directRHForcing q t x i) = fun t => directRHTimeForcing q t x i :=
    funext fun t => (directRHForcing_time_hasDerivAt q t x i).deriv
  rw [he]
  have hc : Continuous (fun t : ℝ => (t,x)) := continuous_id.prodMk continuous_const
  have hh := (continuous_directRHTimeForcing_parameters q i).comp hc
  exact hh


/-- The actual L² scattering channel is an orbit of the previously formalized singular unitary time group. -/
theorem directSymbolL2_eq_evolution (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    directSymbolL2 q t x reverse = evolution (if reverse then t else -t) (directSymbolL2 q 0 x reverse) := by
  apply Lp.ext
  filter_upwards [(directSymbol_memLp q t x reverse).coeFn_toLp,
    evolution_ae (if reverse then t else -t) (directSymbolL2 q 0 x reverse),
    (directSymbol_memLp q 0 x reverse).coeFn_toLp] with z ht he h0
  change (directSymbolL2 q t x reverse : ℝ → ℂ) z = directSymbol q t x reverse z at ht
  change (directSymbolL2 q 0 x reverse : ℝ → ℂ) z = directSymbol q 0 x reverse z at h0
  rw [ht,he,h0]
  cases reverse
  · exact regularJumpReflection_time_factor (globalSmallScatteringPotential q) t x z
  · exact regularJumpReverseReflection_time_factor (globalSmallScatteringPotential q) t x z

/-- The actual direct-scattering channel preserves its L² norm for every prescribed time. -/
theorem directSymbolL2_norm_time_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖directSymbolL2 q t x reverse‖ = ‖directSymbolL2 q 0 x reverse‖ := by
  rw [directSymbolL2_eq_evolution,norm_evolution]

/-- The actual singular-generator L² norm is independent of both space and time. -/
theorem directTimeSymbolL2_norm_invariant (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖directTimeSymbolL2 q t x reverse‖ = ‖directTimeSymbolL2 q 0 0 reverse‖ := by
  have he : ∀ᵐ z : ℝ, ‖(directTimeSymbolL2 q t x reverse : ℝ → ℂ) z‖ =
      ‖(directTimeSymbolL2 q 0 0 reverse : ℝ → ℂ) z‖ := by
    filter_upwards [(directTimeSymbol_memLp q t x reverse).coeFn_toLp,
      (directTimeSymbol_memLp q 0 0 reverse).coeFn_toLp] with z ht h0
    change (directTimeSymbolL2 q t x reverse : ℝ → ℂ) z = directTimeSymbol q t x reverse z at ht
    change (directTimeSymbolL2 q 0 0 reverse : ℝ → ℂ) z = directTimeSymbol q 0 0 reverse z at h0
    rw [ht,h0,directTimeSymbol_norm,directTimeSymbol_norm]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono fun z hz => hz.le))
    (Lp.norm_le_norm_of_ae_le (he.mono fun z hz => hz.symm.le))

end
end RHTower.FokasLenells
