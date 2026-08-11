import GaloisForLFunctions.RHTower.CCMPublishedRestrictedWeilMatrix

/-!
# The finite CCM zeta spectral triple on the literal restricted-Weil matrix

This module formalizes the unconditional finite algebraic core of Theorem 1.1 in
Connes--Consani--Moscovici, *Zeta Spectral Triples* (`arXiv:2511.22755`).  Numerical claims and the
conjectural convergence to `XiC` are deliberately absent.

The source theorem assumes that the lowest eigenvalue of the finite restricted-Weil matrix is
simple and has an even eigenvector normalized by the Dirichlet boundary functional.  The structure
below records exactly those consequences: positivity of the ground shift, its one-dimensional
radical, reflection evenness, and boundary normalization.  Under these hypotheses the paper's
constant-boundary rank-one perturbation of the physical logarithmic clock is metric-adjoint and
has real characteristic zeros.  The final theorem is the exact finite rank-one determinant /
resolvent-numerator identity used in the paper's regularized-determinant calculation.
-/

open Complex
open scoped Matrix ComplexOrder

namespace RHTower

noncomputable section

/-- Complexification of the literal restricted-Weil matrix shifted by a proposed simple ground
eigenvalue. -/
def ccmPublishedGroundShift (a mu : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  (ccmScalarShift (ccmPublishedRestrictedWeilMatrix a N) mu).map (algebraMap ℝ ℂ)

/-- Paper's finite Dirichlet boundary vector. -/
def ccmPublishedDirichletBoundary (N : ℕ) : Fin (2 * N + 1) → ℂ := fun _ => 1

/-- Complex centered clock before physical multiplication by `π/a`. -/
def ccmPublishedCenteredClockMatrix (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  (ccmDiagonalClock (ccmPublishedCenteredClock N)).map (algebraMap ℝ ℂ)

/-- Physical logarithmic clock `2πn/L = πn/a`, with `L=2a`. -/
def ccmPublishedPhysicalLogClock (a : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  (ccmDiagonalClock (ccmPublishedCenteredFrequency a N)).map (algebraMap ℝ ℂ)

/-- Complexification of the literal divided-difference source vector. -/
def ccmPublishedSourceVector (a : ℝ) (N : ℕ) : Fin (2 * N + 1) → ℂ :=
  fun i => (ccmPublishedCenteredSource a N i : ℂ)

/-- Exact hypotheses supplied by a simple even lowest eigenvector in the source paper.  The
one-dimensional radical statement is the algebraic form of simplicity after shifting by the
lowest eigenvalue. -/
structure CCMPublishedSimpleEvenGroundData (a : ℝ) (N : ℕ) where
  mu : ℝ
  ground : Fin (2 * N + 1) → ℂ
  shift_posSemidef : (ccmPublishedGroundShift a mu N).PosSemidef
  radical_eq_groundLine : ∀ v : Fin (2 * N + 1) → ℂ,
    ccmPublishedGroundShift a mu N *ᵥ v = 0 ↔ ∃ c : ℂ, v = c • ground
  ground_even : ∀ i,
    ground (Fin.revPerm (n := 2 * N + 1) i) = ground i
  dirichlet_normalized :
    star (ccmPublishedDirichletBoundary N) ⬝ᵥ ground = 1

namespace CCMPublishedSimpleEvenGroundData

variable {a : ℝ} {N : ℕ} (D : CCMPublishedSimpleEvenGroundData a N)

/-- The normalized simple ground vector lies in the radical of the shifted Weil metric. -/
theorem ground_mem_radical :
    ccmPublishedGroundShift a D.mu N *ᵥ D.ground = 0 := by
  apply (D.radical_eq_groundLine D.ground).2
  exact ⟨1, by simp⟩

/-- Dirichlet normalization makes the ground vector nonzero. -/
theorem ground_ne_zero : D.ground ≠ 0 := by
  intro h
  rw [h] at D.dirichlet_normalized
  simp at D.dirichlet_normalized

/-- Every radical vector satisfies the Riesz identity needed to turn metric-adjointness into a
full-spectrum real-root theorem. -/
theorem ground_riesz (v : Fin (2 * N + 1) → ℂ)
    (hv : ccmPublishedGroundShift a D.mu N *ᵥ v = 0) :
    star D.ground ⬝ᵥ v =
      (star D.ground ⬝ᵥ D.ground) *
        (star (ccmPublishedDirichletBoundary N) ⬝ᵥ v) := by
  obtain ⟨c, rfl⟩ := (D.radical_eq_groundLine v).1 hv
  rw [dotProduct_smul, dotProduct_smul, D.dirichlet_normalized]
  ring

/-- Complex reflection acts by reversal of coordinates. -/
theorem complexReflection_mulVec (v : Fin (2 * N + 1) → ℂ) :
    (ccmReflectionMatrix (Fin.revPerm (n := 2 * N + 1))).map (algebraMap ℝ ℂ) *ᵥ v =
      fun i => v (Fin.revPerm i) := by
  funext i
  rw [Matrix.mulVec, Finset.sum_eq_single (Fin.revPerm i)]
  · simp [ccmReflectionMatrix]
  · intro b _ hne
    simp [ccmReflectionMatrix, hne]
  · simp

/-- The paper's simple ground is fixed by centered reflection. -/
theorem reflection_mulVec_ground :
    (ccmReflectionMatrix (Fin.revPerm (n := 2 * N + 1))).map (algebraMap ℝ ℂ) *ᵥ D.ground =
      D.ground := by
  rw [D.complexReflection_mulVec]
  funext i
  exact D.ground_even i

/-- The literal published source is odd under centered reflection. -/
theorem reflection_mulVec_source :
    (ccmReflectionMatrix (Fin.revPerm (n := 2 * N + 1))).map (algebraMap ℝ ℂ) *ᵥ
        ccmPublishedSourceVector a N =
      -ccmPublishedSourceVector a N := by
  rw [D.complexReflection_mulVec]
  funext i
  simp only [Pi.neg_apply, ccmPublishedSourceVector]
  exact_mod_cast ccmPublishedCenteredSource_rev a N i

/-- Even ground and odd published source are orthogonal. -/
theorem source_orthogonal_ground :
    star (ccmPublishedSourceVector a N) ⬝ᵥ D.ground = 0 := by
  let G := (ccmReflectionMatrix (Fin.revPerm (n := 2 * N + 1))).map
    (algebraMap ℝ ℂ)
  have hG : G.IsHermitian := by
    exact realSymmetric_complexification_isHermitian _
      (ccmReflectionMatrix_transpose (Fin.revPerm (n := 2 * N + 1)) (fun i => by simp))
  have hinv := ccmHermitian_mulVec_inner G (ccmPublishedSourceVector a N) D.ground hG
  have hsource : G *ᵥ ccmPublishedSourceVector a N = -ccmPublishedSourceVector a N := by
    exact D.reflection_mulVec_source
  have hground : G *ᵥ D.ground = D.ground := D.reflection_mulVec_ground
  rw [hsource, hground] at hinv
  have hneg : -(star (ccmPublishedSourceVector a N) ⬝ᵥ D.ground) =
      star (ccmPublishedSourceVector a N) ⬝ᵥ D.ground := by
    simpa using hinv
  linarith

/-- Complexified shifted matrix retains the literal CCM rank-two displacement identity. -/
theorem centered_displacement :
    ccmPublishedCenteredClockMatrix N * ccmPublishedGroundShift a D.mu N -
        ccmPublishedGroundShift a D.mu N * ccmPublishedCenteredClockMatrix N =
      Matrix.vecMulVec (ccmPublishedSourceVector a N)
          (star (ccmPublishedDirichletBoundary N)) -
        Matrix.vecMulVec (ccmPublishedDirichletBoundary N)
          (star (ccmPublishedSourceVector a N)) := by
  let Q := ccmPublishedRestrictedWeilMatrix a N
  let C := ccmDiagonalClock (ccmPublishedCenteredClock N)
  let s := ccmPublishedCenteredSource a N
  have hreal := ccmScalarShift_displacement Q C
    (Matrix.vecMulVec s ccmConstantBoundary - Matrix.vecMulVec ccmConstantBoundary s) D.mu
    (ccmPublishedRestrictedWeilMatrix_displacement a N)
  have hmap := congrArg (fun M : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ =>
    M.map (algebraMap ℝ ℂ)) hreal
  change (C * ccmScalarShift Q D.mu - ccmScalarShift Q D.mu * C).map
      (algebraMap ℝ ℂ) =
    (Matrix.vecMulVec s ccmConstantBoundary -
      Matrix.vecMulVec ccmConstantBoundary s).map (algebraMap ℝ ℂ) at hmap
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul] at hmap
  simpa [Q, C, s, ccmPublishedCenteredClockMatrix, ccmPublishedGroundShift,
    ccmPublishedSourceVector, ccmPublishedDirichletBoundary, ccmConstantBoundary] using hmap

/-- Centered logarithmic clock is Hermitian. -/
theorem centeredClock_isHermitian : (ccmPublishedCenteredClockMatrix N).IsHermitian := by
  exact realSymmetric_complexification_isHermitian _
    (ccmDiagonalClock_transpose (ccmPublishedCenteredClock N))

/-- Exact source identity obtained from the literal displacement law and the normalized even
ground. -/
theorem shiftedMetric_mulVec_clock_ground :
    ccmPublishedGroundShift a D.mu N *ᵥ
        (ccmPublishedCenteredClockMatrix N *ᵥ D.ground) =
      -ccmPublishedSourceVector a N := by
  exact ccmActiveSource_boundary
    (ccmPublishedGroundShift a D.mu N)
    (ccmPublishedCenteredClockMatrix N)
    (ccmPublishedDirichletBoundary N)
    (ccmPublishedSourceVector a N)
    D.ground D.centered_displacement D.ground_mem_radical
    D.dirichlet_normalized D.source_orthogonal_ground

/-- Paper's centered eta-channel rank-one perturbation. -/
def centeredPerturbation : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  ccmSourceCompletion (ccmPublishedCenteredClockMatrix N) D.ground
    (ccmPublishedDirichletBoundary N)

/-- The centered perturbation is self-adjoint for the shifted restricted-Weil metric. -/
theorem centeredPerturbation_metricAdjoint :
    ccmPublishedGroundShift a D.mu N * D.centeredPerturbation =
      D.centeredPerturbationᴴ * ccmPublishedGroundShift a D.mu N := by
  exact ccmSourceCompletion_metricAdjoint
    (ccmPublishedGroundShift a D.mu N)
    (ccmPublishedCenteredClockMatrix N)
    (ccmPublishedDirichletBoundary N)
    (ccmPublishedSourceVector a N)
    D.ground D.shift_posSemidef.isHermitian D.centeredClock_isHermitian
    D.centered_displacement D.shiftedMetric_mulVec_clock_ground

/-- Every characteristic zero of the centered eta-channel perturbation is real. -/
theorem centeredPerturbation_charpoly_zero_im_eq_zero {z : ℂ}
    (hz : D.centeredPerturbation.charpoly.eval z = 0) : z.im = 0 := by
  exact ccmSourceCompletion_charpoly_zero_im_eq_zero
    (ccmPublishedGroundShift a D.mu N)
    (ccmPublishedCenteredClockMatrix N)
    D.ground (ccmPublishedDirichletBoundary N)
    D.shift_posSemidef D.centeredClock_isHermitian D.dirichlet_normalized
    D.ground_riesz D.centeredPerturbation_metricAdjoint hz

/-- Paper's physical eta-channel perturbation of `D_log`, at `L=2a`. -/
def physicalPerturbation : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  ccmSourceCompletion (ccmPublishedPhysicalLogClock a N) D.ground
    (ccmPublishedDirichletBoundary N)

/-- Physical clock is Hermitian. -/
theorem physicalClock_isHermitian : (ccmPublishedPhysicalLogClock a N).IsHermitian := by
  exact realSymmetric_complexification_isHermitian _
    (ccmDiagonalClock_transpose (ccmPublishedCenteredFrequency a N))

/-- Physical perturbation is the exact scalar rescaling of the centered perturbation. -/
theorem physicalPerturbation_eq_smul (ha : a ≠ 0) :
    D.physicalPerturbation = ((Real.pi / a : ℝ) : ℂ) • D.centeredPerturbation := by
  have hclock : ccmPublishedPhysicalLogClock a N =
      ((Real.pi / a : ℝ) : ℂ) • ccmPublishedCenteredClockMatrix N := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [ccmPublishedPhysicalLogClock, ccmPublishedCenteredClockMatrix,
        ccmDiagonalClock, ccmPublishedCenteredFrequency]
    · simp [ccmPublishedPhysicalLogClock, ccmPublishedCenteredClockMatrix,
        ccmDiagonalClock, Matrix.diagonal, hij]
  rw [physicalPerturbation, hclock, centeredPerturbation]
  ext i j
  simp [ccmSourceCompletion, Matrix.vecMulVec_apply]
  ring

/-- The physical perturbation is self-adjoint for the shifted restricted-Weil metric. -/
theorem physicalPerturbation_metricAdjoint (ha : a ≠ 0) :
    ccmPublishedGroundShift a D.mu N * D.physicalPerturbation =
      D.physicalPerturbationᴴ * ccmPublishedGroundShift a D.mu N := by
  rw [D.physicalPerturbation_eq_smul ha]
  have hs : star (((Real.pi / a : ℝ) : ℂ)) = ((Real.pi / a : ℝ) : ℂ) := by simp
  simp only [Matrix.mul_smul, Matrix.conjTranspose_smul, hs, Matrix.smul_mul]
  rw [D.centeredPerturbation_metricAdjoint]

/-- The physical perturbation has only real characteristic zeros. -/
theorem physicalPerturbation_charpoly_zero_im_eq_zero (ha : a ≠ 0) {z : ℂ}
    (hz : D.physicalPerturbation.charpoly.eval z = 0) : z.im = 0 := by
  exact ccmSourceCompletion_charpoly_zero_im_eq_zero
    (ccmPublishedGroundShift a D.mu N)
    (ccmPublishedPhysicalLogClock a N)
    D.ground (ccmPublishedDirichletBoundary N)
    D.shift_posSemidef D.physicalClock_isHermitian D.dirichlet_normalized
    D.ground_riesz (D.physicalPerturbation_metricAdjoint ha) hz

/-- The normalized simple ground is in the kernel of the physical perturbation. -/
theorem physicalPerturbation_mulVec_ground :
    D.physicalPerturbation *ᵥ D.ground = 0 :=
  ccmSourceCompletion_mulVec_c _ _ _ D.dirichlet_normalized

/-- Exact finite determinant/resolvent numerator identity from the source paper.  This is the
finite factor used before adjoining the unchanged exterior logarithmic-clock determinant. -/
theorem physicalPerturbation_shift_det_eq_fourierResolventNumerator
    (z : ℂ)
    (hz : IsUnit
      (ccmPublishedPhysicalLogClock a N -
        z • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)).det) :
    (D.physicalPerturbation -
        z • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)).det =
      -z *
        (ccmPublishedPhysicalLogClock a N -
          z • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)).det *
        (star (ccmPublishedDirichletBoundary N) ⬝ᵥ
          ((ccmPublishedPhysicalLogClock a N -
              z • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ))⁻¹ *ᵥ
            D.ground)) := by
  exact ccmSourceCompletion_shift_det_eq_neg_mul_resolvent
    (ccmPublishedPhysicalLogClock a N) D.ground
    (ccmPublishedDirichletBoundary N) z D.dirichlet_normalized hz

end CCMPublishedSimpleEvenGroundData

end
end RHTower
