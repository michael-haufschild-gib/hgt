import GaloisForLFunctions.RHTower.FokasLenellsMixedDispersion
import GaloisForLFunctions.RHTower.FokasLenellsSpaceForcing
import GaloisForLFunctions.RHTower.FokasLenellsTimeForcing

/-!
# Mixed derivatives of the genuine Riemann–Hilbert forcing

One time and one spatial derivative extract exactly the off-diagonal part of
the actual scattering jump. Dominated L² differentiation and the bounded
Cauchy projection propagate this identity to the inhomogeneous inverse data.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

def directJumpMixedMatrix (q : SchwartzMap ℝ ℂ) (t x z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0,directSymbol q t x true z;-directSymbol q t x false z,0]

theorem directJumpTimeMatrix_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x z : ℝ) (i j : Fin 2) :
    HasDerivAt (fun y => directJumpTimeMatrix q t y z i j) (directJumpMixedMatrix q t x z i j) x := by
  fin_cases i <;> fin_cases j
  · exact hasDerivAt_const x (0 : ℂ)
  · exact directTimeSymbol_space_hasDerivAt q t x true z
  · exact (directTimeSymbol_space_hasDerivAt q t x false z).neg
  · exact hasDerivAt_const x (0 : ℂ)

theorem directJumpSpaceMatrix_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x z : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => directJumpSpaceMatrix q s x z i j) (directJumpMixedMatrix q t x z i j) t := by
  fin_cases i <;> fin_cases j
  · exact hasDerivAt_const t (0 : ℂ)
  · exact directSpaceSymbol_time_hasDerivAt q t x true z
  · exact (directSpaceSymbol_time_hasDerivAt q t x false z).neg
  · exact hasDerivAt_const t (0 : ℂ)

/-- The original jump envelope suffices for the mixed derivative. -/
theorem directJumpMixedMatrix_entry_bound (q : SchwartzMap ℝ ℂ) (t x z : ℝ) (i j : Fin 2) :
    ‖directJumpMixedMatrix q t x z i j‖ ≤ regularJumpL2Envelope q z := by
  fin_cases i <;> fin_cases j
  · change ‖(0 : ℂ)‖ ≤ _
    rw [norm_zero]
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  · change ‖regularJumpReverseReflection (globalSmallScatteringPotential q) t x z‖ ≤ _
    rw [(regularJumpReflection_norms (globalSmallScatteringPotential q) t x z).2]
    exact le_add_of_nonneg_left (norm_nonneg _)
  · change ‖-regularJumpReflection (globalSmallScatteringPotential q) t x z‖ ≤ _
    rw [norm_neg,(regularJumpReflection_norms (globalSmallScatteringPotential q) t x z).1]
    exact le_add_of_nonneg_right (norm_nonneg _)
  · change ‖(0 : ℂ)‖ ≤ _
    rw [norm_zero]
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem directJumpMixedMatrix_entry_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    MemLp (fun z => directJumpMixedMatrix q t x z i j) 2 volume := by
  fin_cases i <;> fin_cases j
  · change MemLp (fun _ : ℝ => (0 : ℂ)) 2 volume
    simp
  · exact directSymbol_memLp q t x true
  · exact (directSymbol_memLp q t x false).neg
  · change MemLp (fun _ : ℝ => (0 : ℂ)) 2 volume
    simp

theorem continuous_directJumpMixedMatrix_entry_parameters (q : SchwartzMap ℝ ℂ) (z : ℝ) (i j : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directJumpMixedMatrix q p.1 p.2 z i j) := by
  fin_cases i <;> fin_cases j
  · exact continuous_const
  · exact continuous_directSymbol_parameters q true z
  · exact (continuous_directSymbol_parameters q false z).neg
  · exact continuous_const

def directJumpMixedEntry (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) : SoninL2 :=
  (directJumpMixedMatrix_entry_memLp q t x i j).toLp (fun z => directJumpMixedMatrix q t x z i j)

theorem directJumpTimeEntry_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun y => directJumpTimeEntry q t y i j) (directJumpMixedEntry q t x i j) x := by
  exact hasDerivAt_toLp_two_of_dominated volume
    (fun y z => directJumpTimeMatrix q t y z i j) (fun y z => directJumpMixedMatrix q t y z i j)
    (fun y => directJumpTimeMatrix_entry_memLp q t y i j) (fun y => directJumpMixedMatrix_entry_memLp q t y i j)
    (regularJumpL2Envelope q) (regularJumpL2Envelope_memLp q)
    (Eventually.of_forall fun z y => directJumpTimeMatrix_space_hasDerivAt q t y z i j)
    (Eventually.of_forall fun z y => directJumpMixedMatrix_entry_bound q t y z i j) x

theorem directJumpSpaceEntry_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => directJumpSpaceEntry q s x i j) (directJumpMixedEntry q t x i j) t := by
  exact hasDerivAt_toLp_two_of_dominated volume
    (fun s z => directJumpSpaceMatrix q s x z i j) (fun s z => directJumpMixedMatrix q s x z i j)
    (fun s => directJumpSpaceMatrix_entry_memLp q s x i j) (fun s => directJumpMixedMatrix_entry_memLp q s x i j)
    (regularJumpL2Envelope q) (regularJumpL2Envelope_memLp q)
    (Eventually.of_forall fun z s => directJumpSpaceMatrix_time_hasDerivAt q s x z i j)
    (Eventually.of_forall fun z s => directJumpMixedMatrix_entry_bound q s x z i j) t

theorem continuous_directJumpMixedEntry_parameters (q : SchwartzMap ℝ ℂ) (i j : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directJumpMixedEntry q p.1 p.2 i j) := by
  apply continuous_toLp_two_of_dominated volume
    (fun p : ℝ × ℝ => fun z => directJumpMixedMatrix q p.1 p.2 z i j)
    (fun p => directJumpMixedMatrix_entry_memLp q p.1 p.2 i j)
    (regularJumpL2Envelope q) (regularJumpL2Envelope_memLp q)
  · intro p
    exact Eventually.of_forall fun z => directJumpMixedMatrix_entry_bound q p.1 p.2 z i j
  · exact Eventually.of_forall fun z => continuous_directJumpMixedMatrix_entry_parameters q z i j

def directJumpMixedRow (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  (directJumpMixedEntry q t x i 0,directJumpMixedEntry q t x i 1)

theorem directJumpTimeRow_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun y => directJumpTimeRow q t y i) (directJumpMixedRow q t x i) x :=
  (directJumpTimeEntry_space_hasDerivAt q t x i 0).prodMk (directJumpTimeEntry_space_hasDerivAt q t x i 1)

theorem directJumpSpaceRow_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directJumpSpaceRow q s x i) (directJumpMixedRow q t x i) t :=
  (directJumpSpaceEntry_time_hasDerivAt q t x i 0).prodMk (directJumpSpaceEntry_time_hasDerivAt q t x i 1)

theorem continuous_directJumpMixedRow_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directJumpMixedRow q p.1 p.2 i) :=
  (continuous_directJumpMixedEntry_parameters q i 0).prodMk (continuous_directJumpMixedEntry_parameters q i 1)

def directRHMixedForcing (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  boundaryCauchy (directJumpMixedRow q t x i)

theorem directRHTimeForcing_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun y => directRHTimeForcing q t y i) (directRHMixedForcing q t x i) x :=
  (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x
    (directJumpTimeRow_space_hasDerivAt q t x i)

theorem directRHSpaceForcing_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directRHSpaceForcing q s x i) (directRHMixedForcing q t x i) t :=
  (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (directJumpSpaceRow_time_hasDerivAt q t x i)

theorem continuous_directRHMixedForcing_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directRHMixedForcing q p.1 p.2 i) :=
  boundaryCauchy.continuous.comp (continuous_directJumpMixedRow_parameters q i)

theorem directRHForcing_mixed_commute (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    deriv (fun y => deriv (fun s => directRHForcing q s y i) t) x =
      deriv (fun s => deriv (fun y => directRHForcing q s y i) x) t := by
  have ht : (fun y => deriv (fun s => directRHForcing q s y i) t) =
      fun y => directRHTimeForcing q t y i :=
    funext fun y => (directRHForcing_time_hasDerivAt q t y i).deriv
  have hx : (fun s => deriv (fun y => directRHForcing q s y i) x) =
      fun s => directRHSpaceForcing q s x i :=
    funext fun s => (directRHForcing_space_hasDerivAt q s x i).deriv
  rw [ht,hx,(directRHTimeForcing_space_hasDerivAt q t x i).deriv,
    (directRHSpaceForcing_time_hasDerivAt q t x i).deriv]

end
end RHTower.FokasLenells
