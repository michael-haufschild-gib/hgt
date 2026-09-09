import GaloisForLFunctions.RHTower.FokasLenellsSecondTimeMultiplier
import GaloisForLFunctions.RHTower.FokasLenellsTimeForcing

/-!
# Second time derivatives of the actual RH jump and forcing

The actual compatible jump has zero diagonal second derivative. The
proved full-line second inverse weight differentiates its entries in L2,
then its rows and the forcing supplied to the actual Cauchy inverse.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

def compatibleJumpSecondTimeMatrix (q : SchwartzMap ℝ ℂ) (t x z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0,directSecondTimeSymbol (oddInitialPart q) t x true z;-directSecondTimeSymbol (oddInitialPart q) t x false z,0]

theorem directJumpTimeMatrix_oddInitialPart_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x z : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => directJumpTimeMatrix (oddInitialPart q) s x z i j)
      (compatibleJumpSecondTimeMatrix q t x z i j) t := by
  fin_cases i <;> fin_cases j
  · exact hasDerivAt_const t (0:ℂ)
  · exact directTimeSymbol_time_hasDerivAt _ t x true z
  · exact (directTimeSymbol_time_hasDerivAt _ t x false z).neg
  · exact hasDerivAt_const t (0:ℂ)

def compatibleJumpSecondTimeEnvelope (q : SchwartzMap ℝ ℂ) (z : ℝ) : ℝ :=
  ‖directSecondTimeSymbol (oddInitialPart q) 0 0 false z‖+‖directSecondTimeSymbol (oddInitialPart q) 0 0 true z‖

theorem compatibleJumpSecondTimeEnvelope_memLp (q : SchwartzMap ℝ ℂ) :
    MemLp (compatibleJumpSecondTimeEnvelope q) 2 volume :=
  (directSecondTimeSymbol_oddInitialPart_memLp q 0 0 false).norm.add
    (directSecondTimeSymbol_oddInitialPart_memLp q 0 0 true).norm

theorem compatibleJumpSecondTimeMatrix_entry_bound (q : SchwartzMap ℝ ℂ) (t x z : ℝ) (i j : Fin 2) :
    ‖compatibleJumpSecondTimeMatrix q t x z i j‖ ≤ compatibleJumpSecondTimeEnvelope q z := by
  fin_cases i <;> fin_cases j
  · change ‖(0:ℂ)‖ ≤ _
    rw [norm_zero]
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  · change ‖directSecondTimeSymbol (oddInitialPart q) t x true z‖ ≤ _
    change _ ≤ ‖directSecondTimeSymbol (oddInitialPart q) 0 0 false z‖+‖directSecondTimeSymbol (oddInitialPart q) 0 0 true z‖
    rw [directSecondTimeSymbol_norm,directSecondTimeSymbol_norm,directSecondTimeSymbol_norm]
    exact le_add_of_nonneg_left (mul_nonneg (by positivity) (norm_nonneg _))
  · change ‖-directSecondTimeSymbol (oddInitialPart q) t x false z‖ ≤ _
    change _ ≤ ‖directSecondTimeSymbol (oddInitialPart q) 0 0 false z‖+‖directSecondTimeSymbol (oddInitialPart q) 0 0 true z‖
    rw [norm_neg,directSecondTimeSymbol_norm,directSecondTimeSymbol_norm,directSecondTimeSymbol_norm]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (norm_nonneg _))
  · change ‖(0:ℂ)‖ ≤ _
    rw [norm_zero]
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem compatibleJumpSecondTimeMatrix_entry_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    MemLp (fun z => compatibleJumpSecondTimeMatrix q t x z i j) 2 volume := by
  fin_cases i <;> fin_cases j
  · change MemLp (fun _ : ℝ => (0:ℂ)) 2 volume
    simp
  · exact directSecondTimeSymbol_oddInitialPart_memLp q t x true
  · exact (directSecondTimeSymbol_oddInitialPart_memLp q t x false).neg
  · change MemLp (fun _ : ℝ => (0:ℂ)) 2 volume
    simp

theorem continuous_compatibleJumpSecondTimeMatrix_entry_parameters (q : SchwartzMap ℝ ℂ) (z : ℝ) (i j : Fin 2) :
    Continuous (fun p : ℝ × ℝ => compatibleJumpSecondTimeMatrix q p.1 p.2 z i j) := by
  fin_cases i <;> fin_cases j
  · exact continuous_const
  · exact continuous_directSecondTimeSymbol_parameters _ true z
  · exact (continuous_directSecondTimeSymbol_parameters _ false z).neg
  · exact continuous_const

def compatibleJumpSecondTimeEntry (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) : SoninL2 :=
  (compatibleJumpSecondTimeMatrix_entry_memLp q t x i j).toLp (fun z => compatibleJumpSecondTimeMatrix q t x z i j)

/-- Every actual first derivative jump entry has the genuine second strong L2 derivative. -/
theorem directJumpTimeEntry_oddInitialPart_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun s => directJumpTimeEntry (oddInitialPart q) s x i j) (compatibleJumpSecondTimeEntry q t x i j) t := by
  apply hasDerivAt_toLp_two_of_dominated volume
    (fun s z => directJumpTimeMatrix (oddInitialPart q) s x z i j)
    (fun s z => compatibleJumpSecondTimeMatrix q s x z i j)
    (fun s => directJumpTimeMatrix_entry_memLp _ s x i j)
    (fun s => compatibleJumpSecondTimeMatrix_entry_memLp q s x i j)
    (compatibleJumpSecondTimeEnvelope q) (compatibleJumpSecondTimeEnvelope_memLp q)
  · exact Eventually.of_forall fun z s => directJumpTimeMatrix_oddInitialPart_hasDerivAt q s x z i j
  · exact Eventually.of_forall fun z s => compatibleJumpSecondTimeMatrix_entry_bound q s x z i j

theorem continuous_compatibleJumpSecondTimeEntry_parameters (q : SchwartzMap ℝ ℂ) (i j : Fin 2) :
    Continuous (fun p : ℝ × ℝ => compatibleJumpSecondTimeEntry q p.1 p.2 i j) := by
  apply continuous_toLp_two_of_dominated volume
    (fun p : ℝ × ℝ => fun z => compatibleJumpSecondTimeMatrix q p.1 p.2 z i j)
    (fun p => compatibleJumpSecondTimeMatrix_entry_memLp q p.1 p.2 i j)
    (compatibleJumpSecondTimeEnvelope q) (compatibleJumpSecondTimeEnvelope_memLp q)
  · intro p
    exact Eventually.of_forall fun z => compatibleJumpSecondTimeMatrix_entry_bound q p.1 p.2 z i j
  · exact Eventually.of_forall fun z => continuous_compatibleJumpSecondTimeMatrix_entry_parameters q z i j

/-- Every entry of the original compatible jump perturbation is globally C2 as an L2 curve. -/
theorem directJumpEntry_oddInitialPart_time_contDiff_two (q : SchwartzMap ℝ ℂ) (x : ℝ) (i j : Fin 2) :
    ContDiff ℝ 2 (fun t => directJumpEntry (oddInitialPart q) t x i j) := by
  have he : deriv (fun t => directJumpEntry (oddInitialPart q) t x i j) =
      fun t => directJumpTimeEntry (oddInitialPart q) t x i j :=
    funext fun t => (directJumpEntry_time_hasDerivAt _ t x i j).deriv
  change ContDiff ℝ (1+1) (fun t => directJumpEntry (oddInitialPart q) t x i j)
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun t => (directJumpEntry_time_hasDerivAt _ t x i j).differentiableAt,by simp,?_⟩
  rw [he]
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (directJumpTimeEntry_oddInitialPart_hasDerivAt q t x i j).differentiableAt,?_⟩
  have he2 : deriv (fun t => directJumpTimeEntry (oddInitialPart q) t x i j) =
      fun t => compatibleJumpSecondTimeEntry q t x i j :=
    funext fun t => (directJumpTimeEntry_oddInitialPart_hasDerivAt q t x i j).deriv
  rw [he2]
  have hc : Continuous (fun t : ℝ => (t,x)) := continuous_id.prodMk continuous_const
  have hh := (continuous_compatibleJumpSecondTimeEntry_parameters q i j).comp hc
  exact hh

def compatibleJumpSecondTimeRow (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  (compatibleJumpSecondTimeEntry q t x i 0,compatibleJumpSecondTimeEntry q t x i 1)

theorem directJumpTimeRow_oddInitialPart_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directJumpTimeRow (oddInitialPart q) s x i) (compatibleJumpSecondTimeRow q t x i) t :=
  (directJumpTimeEntry_oddInitialPart_hasDerivAt q t x i 0).prodMk (directJumpTimeEntry_oddInitialPart_hasDerivAt q t x i 1)

theorem continuous_compatibleJumpSecondTimeRow_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => compatibleJumpSecondTimeRow q p.1 p.2 i) :=
  (continuous_compatibleJumpSecondTimeEntry_parameters q i 0).prodMk (continuous_compatibleJumpSecondTimeEntry_parameters q i 1)

def compatibleRHSecondTimeForcing (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  boundaryCauchy (compatibleJumpSecondTimeRow q t x i)

/-- The specific forcing supplied to the actual inverse has a second strong time derivative. -/
theorem directRHTimeForcing_oddInitialPart_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directRHTimeForcing (oddInitialPart q) s x i) (compatibleRHSecondTimeForcing q t x i) t :=
  (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (directJumpTimeRow_oddInitialPart_hasDerivAt q t x i)

theorem continuous_compatibleRHSecondTimeForcing_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => compatibleRHSecondTimeForcing q p.1 p.2 i) :=
  boundaryCauchy.continuous.comp (continuous_compatibleJumpSecondTimeRow_parameters q i)

/-- C2 regularity reaches the actual inhomogeneous Cauchy data. -/
theorem directRHForcing_oddInitialPart_time_contDiff_two (q : SchwartzMap ℝ ℂ) (x : ℝ) (i : Fin 2) :
    ContDiff ℝ 2 (fun t => directRHForcing (oddInitialPart q) t x i) := by
  have hc := (directJumpEntry_oddInitialPart_time_contDiff_two q x i 0).prodMk
    (directJumpEntry_oddInitialPart_time_contDiff_two q x i 1)
  have hh := (boundaryCauchy.restrictScalars ℝ).contDiff.comp hc
  exact hh

end
end RHTower.FokasLenells
