import GaloisForLFunctions.HTGeometry.ExponentialBlockSeedWitness
import GaloisForLFunctions.HTGeometry.PPMatrixRankFormulaConsequences

/-!
# The boundary wedge is entirely realizable in two variables

The periodic pencil of one transcendental number moves the left block along the second coordinate
and the right block along the first.  Its two coordinate families are integrally independent on
their blocks, because a relation among them is a rational relation among distinct powers of a
transcendental number, so each block carries an exponential block seed and the two glue to an entire
two-variable realization of the boundary wedge.

Together with the exclusions of dimensions `0` and `1` this closes `htDim = 2` for every
`r, s ≥ 2`.

* `leftStep`, `rightStep` — the two coordinate families of the pencil;
* `stepIndep_leftStep`, `stepIndep_rightStep` — integral independence on each block;
* `boundaryWedgeHTRealizable_two_of_transcendental` — the two-variable witness;
* `boundaryWedge_htDim_eq_two` — the intrinsic dimension, unconditionally.
-/

namespace GaloisForLFunctions.UniformBoundaryWedge

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {r s : ℕ}

/-- The second-coordinate steps of the pencil: the left block moves, the right block does not. -/
def leftStep (τ : ℂ) (r s : ℕ) : BoundaryWedgeVertex r s → ℂ := fun v => (wedgeVec τ r s v).2

/-- The first-coordinate steps of the pencil: the right block moves, the left block does not. -/
def rightStep (τ : ℂ) (r s : ℕ) : BoundaryWedgeVertex r s → ℂ := fun v => (wedgeVec τ r s v).1

@[simp] theorem leftStep_none (τ : ℂ) (r s : ℕ) :
    leftStep τ r s none = τ ^ r := rfl

@[simp] theorem leftStep_inl (τ : ℂ) (r s : ℕ) (i : Fin r) :
    leftStep τ r s (some (Sum.inl i)) = τ ^ (i : ℕ) := rfl

@[simp] theorem leftStep_inr (τ : ℂ) (r s : ℕ) (j : Fin s) :
    leftStep τ r s (some (Sum.inr j)) = 0 := rfl

@[simp] theorem rightStep_none (τ : ℂ) (r s : ℕ) :
    rightStep τ r s none = τ ^ s := rfl

@[simp] theorem rightStep_inr (τ : ℂ) (r s : ℕ) (j : Fin s) :
    rightStep τ r s (some (Sum.inr j)) = τ ^ (j : ℕ) := rfl

@[simp] theorem rightStep_inl (τ : ℂ) (r s : ℕ) (i : Fin r) :
    rightStep τ r s (some (Sum.inl i)) = 0 := rfl

theorem leftStep_off (τ : ℂ) (r s : ℕ) {v : BoundaryWedgeVertex r s} (hv : v ∉ leftBlock r s) :
    leftStep τ r s v = 0 := by
  rcases v with _ | (i | j)
  · refine absurd (mem_leftBlock.mpr ?_) hv
    show boundaryWedgeLeft (none : BoundaryWedgeVertex r s)
    trivial
  · refine absurd (mem_leftBlock.mpr ?_) hv
    show boundaryWedgeLeft (some (Sum.inl i) : BoundaryWedgeVertex r s)
    trivial
  · rfl

theorem rightStep_off (τ : ℂ) (r s : ℕ) {v : BoundaryWedgeVertex r s} (hv : v ∉ rightBlock r s) :
    rightStep τ r s v = 0 := by
  rcases v with _ | (i | j)
  · refine absurd (mem_rightBlock.mpr ?_) hv
    show boundaryWedgeRight (none : BoundaryWedgeVertex r s)
    trivial
  · rfl
  · refine absurd (mem_rightBlock.mpr ?_) hv
    show boundaryWedgeRight (some (Sum.inr j) : BoundaryWedgeVertex r s)
    trivial

/-! ### Sums over a block -/

theorem sum_leftBlock (f : BoundaryWedgeVertex r s → ℂ) :
    ∑ v ∈ leftBlock r s, f v = f none + ∑ i : Fin r, f (some (Sum.inl i)) := by
  classical
  have hnone : (none : BoundaryWedgeVertex r s) ∉
      Finset.univ.image (fun i : Fin r => (some (Sum.inl i) : BoundaryWedgeVertex r s)) := by
    simp
  rw [leftBlock, Finset.sum_insert hnone,
    Finset.sum_image (by intro x _ y _ h; simpa using h)]

theorem sum_rightBlock (f : BoundaryWedgeVertex r s → ℂ) :
    ∑ v ∈ rightBlock r s, f v = f none + ∑ j : Fin s, f (some (Sum.inr j)) := by
  classical
  have hnone : (none : BoundaryWedgeVertex r s) ∉
      Finset.univ.image (fun j : Fin s => (some (Sum.inr j) : BoundaryWedgeVertex r s)) := by
    simp
  rw [rightBlock, Finset.sum_insert hnone,
    Finset.sum_image (by intro x _ y _ h; simpa using h)]

/-! ### Integral independence of the block steps -/

/-- The exponents of the left block: the deleted centre carries the top power. -/
def leftExponent (r : ℕ) : Option (Fin r) → ℕ
  | none => r
  | some i => (i : ℕ)

@[simp] theorem leftExponent_none (r : ℕ) : leftExponent r none = r := rfl

@[simp] theorem leftExponent_some (r : ℕ) (i : Fin r) : leftExponent r (some i) = (i : ℕ) := rfl

theorem leftExponent_injective (r : ℕ) : Function.Injective (leftExponent r) := by
  intro x y hxy
  rcases x with _ | i <;> rcases y with _ | j
  · rfl
  · exact absurd hxy.symm (Nat.ne_of_lt j.isLt)
  · exact absurd hxy (Nat.ne_of_lt i.isLt)
  · rw [Option.some.injEq]
    exact Fin.ext hxy

/-- The rational coefficient family of a left-block integer relation. -/
def leftCoeff (g : BoundaryWedgeVertex r s → ℤ) : Option (Fin r) → ℚ
  | none => ((g none : ℤ) : ℚ)
  | some i => ((g (some (Sum.inl i)) : ℤ) : ℚ)

@[simp] theorem leftCoeff_none (g : BoundaryWedgeVertex r s → ℤ) :
    leftCoeff g none = ((g none : ℤ) : ℚ) := rfl

@[simp] theorem leftCoeff_some (g : BoundaryWedgeVertex r s → ℤ) (i : Fin r) :
    leftCoeff g (some i) = ((g (some (Sum.inl i)) : ℤ) : ℚ) := rfl

/-- **The left-block steps are integrally independent.**  A relation among them is a rational
relation among the distinct powers `τ⁰, …, τ^{r−1}, τ^r`. -/
theorem stepIndep_leftStep {τ : ℂ} (hτ : Transcendental ℚ τ) (r s : ℕ) :
    StepIndep (leftBlock r s) (leftStep τ r s) := by
  classical
  intro g hsum v hv
  have hEq : ∑ x : Option (Fin r), leftCoeff g x • (τ ^ leftExponent r x)
      = ∑ v ∈ leftBlock r s, (g v : ℂ) * leftStep τ r s v := by
    have h1 : leftCoeff g none • (τ ^ leftExponent r none)
        = (g none : ℂ) * leftStep τ r s none := by
      rw [leftCoeff_none, leftStep_none, leftExponent_none, Rat.smul_def]
      push_cast
      ring
    have h2 : ∑ i : Fin r, leftCoeff g (some i) • (τ ^ leftExponent r (some i))
        = ∑ i : Fin r, (g (some (Sum.inl i)) : ℂ) * leftStep τ r s (some (Sum.inl i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [leftCoeff_some, leftStep_inl, leftExponent_some, Rat.smul_def]
      push_cast
      ring
    rw [sum_leftBlock, Fintype.sum_option, h1, h2]
  have hzero := transcendental_pow_combination_eq_zero hτ (leftExponent_injective r)
    (leftCoeff g) (hEq.trans hsum)
  rw [mem_leftBlock] at hv
  rcases v with _ | (i | j)
  · have h0 := hzero none
    rw [leftCoeff_none] at h0
    exact_mod_cast h0
  · have h0 := hzero (some i)
    rw [leftCoeff_some] at h0
    exact_mod_cast h0
  · exact absurd hv not_false

/-- The exponents of the right block. -/
def rightExponent (s : ℕ) : Option (Fin s) → ℕ
  | none => s
  | some j => (j : ℕ)

@[simp] theorem rightExponent_none (s : ℕ) : rightExponent s none = s := rfl

@[simp] theorem rightExponent_some (s : ℕ) (j : Fin s) : rightExponent s (some j) = (j : ℕ) := rfl

theorem rightExponent_injective (s : ℕ) : Function.Injective (rightExponent s) := by
  intro x y hxy
  rcases x with _ | i <;> rcases y with _ | j
  · rfl
  · exact absurd hxy.symm (Nat.ne_of_lt j.isLt)
  · exact absurd hxy (Nat.ne_of_lt i.isLt)
  · rw [Option.some.injEq]
    exact Fin.ext hxy

/-- The rational coefficient family of a right-block integer relation. -/
def rightCoeff (g : BoundaryWedgeVertex r s → ℤ) : Option (Fin s) → ℚ
  | none => ((g none : ℤ) : ℚ)
  | some j => ((g (some (Sum.inr j)) : ℤ) : ℚ)

@[simp] theorem rightCoeff_none (g : BoundaryWedgeVertex r s → ℤ) :
    rightCoeff g none = ((g none : ℤ) : ℚ) := rfl

@[simp] theorem rightCoeff_some (g : BoundaryWedgeVertex r s → ℤ) (j : Fin s) :
    rightCoeff g (some j) = ((g (some (Sum.inr j)) : ℤ) : ℚ) := rfl

/-- **The right-block steps are integrally independent.** -/
theorem stepIndep_rightStep {τ : ℂ} (hτ : Transcendental ℚ τ) (r s : ℕ) :
    StepIndep (rightBlock r s) (rightStep τ r s) := by
  classical
  intro g hsum v hv
  have hEq : ∑ x : Option (Fin s), rightCoeff g x • (τ ^ rightExponent s x)
      = ∑ v ∈ rightBlock r s, (g v : ℂ) * rightStep τ r s v := by
    have h1 : rightCoeff g none • (τ ^ rightExponent s none)
        = (g none : ℂ) * rightStep τ r s none := by
      rw [rightCoeff_none, rightStep_none, rightExponent_none, Rat.smul_def]
      push_cast
      ring
    have h2 : ∑ j : Fin s, rightCoeff g (some j) • (τ ^ rightExponent s (some j))
        = ∑ j : Fin s, (g (some (Sum.inr j)) : ℂ) * rightStep τ r s (some (Sum.inr j)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [rightCoeff_some, rightStep_inr, rightExponent_some, Rat.smul_def]
      push_cast
      ring
    rw [sum_rightBlock, Fintype.sum_option, h1, h2]
  have hzero := transcendental_pow_combination_eq_zero hτ (rightExponent_injective s)
    (rightCoeff g) (hEq.trans hsum)
  rw [mem_rightBlock] at hv
  rcases v with _ | (i | j)
  · have h0 := hzero none
    rw [rightCoeff_none] at h0
    exact_mod_cast h0
  · exact absurd hv not_false
  · have h0 := hzero (some j)
    rw [rightCoeff_some] at h0
    exact_mod_cast h0

/-! ### The two-variable witness -/

/-- The left block seed of the pencil. -/
def leftBlockSeed {τ : ℂ} (hτ : Transcendental ℚ τ) (r s : ℕ) : BlockSeed (leftBlock r s) :=
  expBlockSeed (fun _ hv => leftStep_off τ r s hv) (stepIndep_leftStep hτ r s)

/-- The right block seed of the pencil. -/
def rightBlockSeed {τ : ℂ} (hτ : Transcendental ℚ τ) (r s : ℕ) : BlockSeed (rightBlock r s) :=
  expBlockSeed (fun _ hv => rightStep_off τ r s hv) (stepIndep_rightStep hτ r s)

theorem glueSteps_eq_pencil {τ : ℂ} (hτ : Transcendental ℚ τ) (r s : ℕ) :
    glueSteps (leftBlockSeed hτ r s) (rightBlockSeed hτ r s)
      = boundaryWedgePencilVector τ r s := rfl

/-- **The boundary wedge has an entire two-variable realization.** -/
theorem boundaryWedgeHTRealizable_two_of_transcendental {τ : ℂ} (hτ : Transcendental ℚ τ)
    (r s : ℕ) : BoundaryWedgeHTRealizable r s 2 := by
  refine boundaryWedgeHTRealizable_two (leftBlockSeed hτ r s) (rightBlockSeed hτ r s) ?_
  rw [glueSteps_eq_pencil hτ r s]
  exact boundaryWedgePencilVector_linearIndependent hτ r s

/-- **The boundary wedge is entirely realizable in two variables**, unconditionally. -/
theorem boundaryWedgeHTRealizable_two_uncond (r s : ℕ) : BoundaryWedgeHTRealizable r s 2 := by
  obtain ⟨τ, hτ⟩ := exists_transcendental_complex
  exact boundaryWedgeHTRealizable_two_of_transcendental hτ r s

/-- **The intrinsic dimension of the boundary wedge is two.**  Dimension `0` is excluded by
`ℚ`-independence of the steps, dimension `1` by the period-rank obstruction, and dimension `2` is
realized by the exponential block seeds of the periodic pencil. -/
theorem boundaryWedge_htDim_eq_two (hr : 2 ≤ r) (hs : 2 ≤ s) {htDim : ℕ}
    (hfull : BoundaryWedgeHTRealizable r s htDim)
    (hleast : ∀ d, BoundaryWedgeHTRealizable r s d → htDim ≤ d) : htDim = 2 :=
  boundaryWedge_htDim_eq_two_of_entireRealizable hr hs hfull hleast
    (boundaryWedgeHTRealizable_two_uncond r s)

end

end GaloisForLFunctions.UniformBoundaryWedge
