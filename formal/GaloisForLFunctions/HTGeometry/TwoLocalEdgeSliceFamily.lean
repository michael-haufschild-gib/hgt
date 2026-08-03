import GaloisForLFunctions.HTGeometry.TwoLocalDiagonalBaseGenericity
import GaloisForLFunctions.HTGeometry.SpectralClusterTransfer

/-!
# The two-parameter edge slice of the all-qubit two-local family

Through a real diagonal two-local Hamiltonian run two parameter directions attached to a chosen
qubit: the *edge direction*, which shifts every edge gap of that qubit while fixing every edge mean,
and the *transverse direction*, which switches on that qubit's flip coupling.

Along this two-parameter slice the Hamiltonian is, in the edge presentation of the qubit, exactly
the shifted block splitting of the diagonal energies.  The family is entire in all its coefficients,
it is Hermitian at real coefficients, and at zero transverse coupling it is diagonal, so it meets
every hypothesis of the block spectral machinery.
-/

open scoped BigOperators Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-- The all-qubit two-local Hamiltonian as a function of one coefficient vector. -/
def hypercubeTwoLocalMatrix (v : HypercubeTwoLocalParameter n → ℂ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  hypercubeTwoLocalHamiltonian (v .constant) (fun i => v (.onsite i))
    (fun i j => v (.interaction i j)) (fun i => v (.transverse i))

/-- The two-local family is entire in its coefficients. -/
theorem analyticAt_hypercubeTwoLocalMatrix (v₀ : HypercubeTwoLocalParameter n → ℂ) :
    AnalyticAt ℂ (fun v : HypercubeTwoLocalParameter n → ℂ => hypercubeTwoLocalMatrix v) v₀ := by
  classical
  have hcoord : ∀ θ : HypercubeTwoLocalParameter n,
      AnalyticAt ℂ (fun v : HypercubeTwoLocalParameter n → ℂ => v θ) v₀ :=
    fun θ => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : HypercubeTwoLocalParameter n => ℂ)
      θ).analyticAt v₀
  refine AnalyticAt.pi fun x => AnalyticAt.pi fun y => ?_
  show AnalyticAt ℂ (fun v : HypercubeTwoLocalParameter n → ℂ => hypercubeTwoLocalMatrix v x y) v₀
  unfold hypercubeTwoLocalMatrix hypercubeTwoLocalHamiltonian
  by_cases hxy : x = y
  · simp only [hxy]
    refine ((hcoord _).add ?_).add ?_
    · exact Finset.analyticAt_fun_sum _ fun i _ => (hcoord _).mul analyticAt_const
    · exact Finset.analyticAt_fun_sum _ fun i _ =>
        Finset.analyticAt_fun_sum _ fun j _ => ((hcoord _).mul analyticAt_const).mul
          analyticAt_const
  · simp only [if_neg hxy]
    refine Finset.analyticAt_fun_sum _ fun i _ => ?_
    by_cases hy : y = boolToggle x i
    · simp only [if_pos hy]
      exact hcoord _
    · simp only [if_neg hy]
      exact analyticAt_const

/-- At real coefficients the diagonal entries are the real two-local energies. -/
theorem hypercubeTwoLocalMatrix_diagonal_entry (p : HypercubeTwoLocalParameter n → ℝ)
    (x : Fin n → Bool) :
    hypercubeTwoLocalMatrix (fun θ => (p θ : ℂ)) x x
      = ((hypercubeTwoLocalEnergy p x : ℝ) : ℂ) := by
  simp only [hypercubeTwoLocalMatrix, hypercubeTwoLocalHamiltonian,
    hypercubeTwoLocalEnergy]
  push_cast
  ring

/-- Off the diagonal only the transverse couplings contribute. -/
theorem hypercubeTwoLocalMatrix_offdiagonal_entry (v : HypercubeTwoLocalParameter n → ℂ)
    {x y : Fin n → Bool} (hxy : x ≠ y) :
    hypercubeTwoLocalMatrix v x y
      = ∑ i, if y = boolToggle x i then v (.transverse i) else 0 := by
  simp only [hypercubeTwoLocalMatrix, hypercubeTwoLocalHamiltonian, if_neg hxy]

/-- With a single transverse coupling switched on, the off-diagonal entries are that coupling on the
edges of its qubit and zero elsewhere. -/
theorem hypercubeTwoLocalMatrix_offdiagonal_single (v : HypercubeTwoLocalParameter n → ℂ)
    (i : Fin n) (hzero : ∀ i' : Fin n, i' ≠ i → v (.transverse i') = 0)
    {x y : Fin n → Bool} (hxy : x ≠ y) :
    hypercubeTwoLocalMatrix v x y = if y = boolToggle x i then v (.transverse i) else 0 := by
  classical
  rw [hypercubeTwoLocalMatrix_offdiagonal_entry v hxy]
  refine Finset.sum_eq_single i (fun i' _ hi' => ?_) (fun h => absurd (Finset.mem_univ i) h)
  by_cases hy : y = boolToggle x i'
  · rw [if_pos hy, hzero i' hi']
  · rw [if_neg hy]


/-- The two-parameter edge slice through a real diagonal base: the first parameter shifts the edge
gaps of the chosen qubit, the second switches on its transverse coupling. -/
def twoLocalEdgeSlice (p : HypercubeTwoLocalParameter n → ℝ) (i : Fin n) (q : ℝ × ℝ) :
    HypercubeTwoLocalParameter n → ℂ :=
  fun θ => (((p + q.1 • edgeShiftDirection i) θ : ℝ) : ℂ)
    + (q.2 : ℂ) * (if θ = HypercubeTwoLocalParameter.transverse i then 1 else 0)

theorem twoLocalEdgeSlice_constant (p : HypercubeTwoLocalParameter n → ℝ) (i : Fin n)
    (q : ℝ × ℝ) :
    twoLocalEdgeSlice p i q HypercubeTwoLocalParameter.constant
      = (((p + q.1 • edgeShiftDirection i) HypercubeTwoLocalParameter.constant : ℝ) : ℂ) := by
  simp [twoLocalEdgeSlice]

theorem twoLocalEdgeSlice_onsite (p : HypercubeTwoLocalParameter n → ℝ) (i : Fin n)
    (q : ℝ × ℝ) (j : Fin n) :
    twoLocalEdgeSlice p i q (.onsite j)
      = (((p + q.1 • edgeShiftDirection i) (.onsite j) : ℝ) : ℂ) := by
  simp [twoLocalEdgeSlice]

theorem twoLocalEdgeSlice_interaction (p : HypercubeTwoLocalParameter n → ℝ) (i : Fin n)
    (q : ℝ × ℝ) (j k : Fin n) :
    twoLocalEdgeSlice p i q (.interaction j k)
      = (((p + q.1 • edgeShiftDirection i) (.interaction j k) : ℝ) : ℂ) := by
  simp [twoLocalEdgeSlice]

theorem twoLocalEdgeSlice_transverse_self (p : HypercubeTwoLocalParameter n → ℝ) (i : Fin n)
    (q : ℝ × ℝ) (htr : p (.transverse i) = 0) :
    twoLocalEdgeSlice p i q (.transverse i) = (q.2 : ℂ) := by
  simp [twoLocalEdgeSlice, edgeShiftDirection_transverse, htr]

theorem twoLocalEdgeSlice_transverse_other (p : HypercubeTwoLocalParameter n → ℝ) (i : Fin n)
    (q : ℝ × ℝ) {i' : Fin n} (hi' : i' ≠ i) (htr : p (.transverse i') = 0) :
    twoLocalEdgeSlice p i q (.transverse i') = 0 := by
  simp [twoLocalEdgeSlice, edgeShiftDirection_transverse, htr, hi']

/-- **The edge slice is the shifted block splitting.**  In the edge presentation of the chosen
qubit, the two-parameter slice of the two-local family is exactly the block splitting of the base
energies with its gaps shifted by the first parameter and its coupling the second. -/
theorem submatrix_hypercubeTwoLocalMatrix_twoLocalEdgeSlice
    (p : HypercubeTwoLocalParameter n → ℝ) (i : Fin n)
    (htr : ∀ i' : Fin n, p (.transverse i') = 0) (q : ℝ × ℝ) :
    (hypercubeTwoLocalMatrix (twoLocalEdgeSlice p i q)).submatrix (edgeEquiv i) (edgeEquiv i)
      = shiftedBlockSplitMatrix (edgeMean i (hypercubeTwoLocalEnergy p))
          (edgeGap i (hypercubeTwoLocalEnergy p)) q := by
  classical
  have hdiag : ∀ x : Fin n → Bool, hypercubeTwoLocalMatrix (twoLocalEdgeSlice p i q) x x
      = ((hypercubeTwoLocalEnergy (p + q.1 • edgeShiftDirection i) x : ℝ) : ℂ) := by
    intro x
    rw [← hypercubeTwoLocalMatrix_diagonal_entry (p + q.1 • edgeShiftDirection i) x]
    simp only [hypercubeTwoLocalMatrix, hypercubeTwoLocalHamiltonian,
      twoLocalEdgeSlice_constant, twoLocalEdgeSlice_onsite, twoLocalEdgeSlice_interaction,
      if_true]
  have hoff : ∀ x y : Fin n → Bool, x ≠ y →
      hypercubeTwoLocalMatrix (twoLocalEdgeSlice p i q) x y
        = if y = boolToggle x i then (q.2 : ℂ) else 0 := by
    intro x y hxy
    rw [hypercubeTwoLocalMatrix_offdiagonal_single _ i
      (fun i' hi' => twoLocalEdgeSlice_transverse_other p i q hi' (htr i')) hxy,
      twoLocalEdgeSlice_transverse_self p i q (htr i)]
  rw [submatrix_edgeEquiv_eq_blockSplitMatrix i
    (hypercubeTwoLocalEnergy (p + q.1 • edgeShiftDirection i)) (q.2 : ℂ) _ hdiag hoff]
  rw [show edgeMean i (hypercubeTwoLocalEnergy (p + q.1 • edgeShiftDirection i))
        = edgeMean i (hypercubeTwoLocalEnergy p) from
      funext fun z => edgeMean_shift_edgeDirection p i z q.1,
    show edgeGap i (hypercubeTwoLocalEnergy (p + q.1 • edgeShiftDirection i))
        = fun z => edgeGap i (hypercubeTwoLocalEnergy p) z + q.1 from
      funext fun z => edgeGap_shift_edgeDirection p i z q.1]
  rfl


/-- With every transverse coefficient switched off the two-local Hamiltonian is diagonal. -/
theorem hypercubeTwoLocalMatrix_diagonal_of_zeroTransverse (p : HypercubeTwoLocalParameter n → ℝ)
    (htr : ∀ i : Fin n, p (.transverse i) = 0) :
    hypercubeTwoLocalMatrix (fun θ => (p θ : ℂ))
      = Matrix.diagonal fun x => ((hypercubeTwoLocalEnergy p x : ℝ) : ℂ) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst hxy
    rw [hypercubeTwoLocalMatrix_diagonal_entry, Matrix.diagonal_apply_eq]
  · rw [hypercubeTwoLocalMatrix_offdiagonal_entry _ hxy, Matrix.diagonal_apply_ne _ hxy]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hy : y = boolToggle x i
    · rw [if_pos hy, htr i, Complex.ofReal_zero]
    · rw [if_neg hy]

end GaloisForLFunctions.HTGeometry
