import GaloisForLFunctions.HTGeometry.RightFlipScattering
import GaloisForLFunctions.HTGeometry.UnipotentDiagonalizationObstruction

/-!
# The Corcoran--de Leeuw model-1 Yang--Baxter family

`modelOneR A f g` is the regular two-state quantum `R`-matrix

```text
R(u,v) = [1, δG, δF, A δF δG; 0, 0, 1, A δG; 0, 1, 0, A δF; 0, 0, 0, 1],
```

written with `f = δF = F u - F v` and `g = δG = G u - G v`.  Nothing here is specialised to a
particular pair of analytic clocks `F, G`: the two increments and the constant `A` are free
scalars, and the Yang--Baxter equation is proved for the whole family, so the published
classification is not used as an input.

The file proves, unconditionally:

* the spectral-parameter quantum Yang--Baxter equation on the `12`, `13`, `23` legs, in the
  non-difference form `R₁₂(u,v) R₁₃(u,w) R₂₃(v,w) = R₂₃(v,w) R₁₃(u,w) R₁₂(u,v)`;
* regularity `R(u,u) = P`, so the braid form has anchor `1`, never `-P`;
* algebraic braiding unitarity `R₁₂(u,v) R₂₁(v,u) = 1`;
* the braid form is unipotent, `(Ř - 1)² = 0` at `A = 0`;
* `R² = 1 + (δF + δG)·K` with `K² = 0` at `A = 0`, so `R` is not diagonalisable whenever
  `δF + δG ≠ 0`, and therefore no positive-definite one-particle metric makes it unitary.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

/-- Corcoran--de Leeuw model 1 in the quantum convention, in the ordered pair basis
`(0,0), (0,1), (1,0), (1,1)`.  `f` is the increment of the first arbitrary analytic function and
`g` the increment of the second. -/
noncomputable def modelOneR {R : Type*} [CommRing R] (A f g : R) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R :=
  Matrix.of fun i j =>
    if i = (0, 0) then
      (if j = (0, 0) then 1 else if j = (0, 1) then g else if j = (1, 0) then f
        else A * f * g)
    else if i = (0, 1) then
      (if j = (1, 0) then 1 else if j = (1, 1) then A * g else 0)
    else if i = (1, 0) then
      (if j = (0, 1) then 1 else if j = (1, 1) then A * f else 0)
    else (if j = (1, 1) then 1 else 0)

/-- The braid (right-flip) form `Ř = R · P` of the model-1 matrix, written out explicitly:
`Ř = 1 + f E₁₂ + g E₁₃ + A f g E₁₄ + A g E₂₄ + A f E₃₄`. -/
noncomputable def modelOneBraid {R : Type*} [CommRing R] (A f g : R) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R :=
  Matrix.of fun i j =>
    if i = j then 1
    else if i = (0, 0) then
      (if j = (0, 1) then f else if j = (1, 0) then g else A * f * g)
    else if i = (0, 1) then (if j = (1, 1) then A * g else 0)
    else if i = (1, 0) then (if j = (1, 1) then A * f else 0)
    else 0

theorem modelOneBraid_eq_rightFlip (A f g : ℂ) :
    modelOneBraid A f g =
      rightFlip (modelOneR A f g) (twoParticleFlipMatrix (Fin 2)) := by
  ext i j
  simp only [rightFlip, Matrix.mul_apply, modelOneR, modelOneBraid, Matrix.of_apply,
    twoParticleFlipMatrix, Fintype.sum_prod_type, Fin.sum_univ_two, PEquiv.toMatrix_apply]
  fin_cases i <;> fin_cases j <;> norm_num

/-- Regularity: at coincident spectral parameters the quantum matrix is the tensor flip. -/
theorem modelOneR_regular (A : ℂ) :
    modelOneR A 0 0 = twoParticleFlipMatrix (Fin 2) := by
  ext i j
  simp only [modelOneR, Matrix.of_apply, twoParticleFlipMatrix, PEquiv.toMatrix_apply]
  fin_cases i <;> fin_cases j <;> norm_num

/-- Regularity in the braid convention: the braid matrix has anchor `1`. -/
theorem modelOneBraid_regular (A : ℂ) : modelOneBraid A 0 0 = 1 := by
  ext i j
  simp only [modelOneBraid, Matrix.of_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> norm_num

set_option maxHeartbeats 1000000 in
/-- The adjacent spectral braid equation for the model-1 braid family.  The three increments are
the ones produced by a common pair of clocks at three spectral points: `(f₁, g₁)` from `(u,v)`,
`(f₁ + f₃, g₁ + g₃)` from `(u,w)`, and `(f₃, g₃)` from `(v,w)`. -/
theorem modelOneBraid_adjacentBraid (A f₁ g₁ f₃ g₃ : ℂ) :
    threeParticleLeg12 (Fin 2) (modelOneBraid A f₁ g₁) *
        threeParticleLeg23 (Fin 2) (modelOneBraid A (f₁ + f₃) (g₁ + g₃)) *
        threeParticleLeg12 (Fin 2) (modelOneBraid A f₃ g₃) =
      threeParticleLeg23 (Fin 2) (modelOneBraid A f₃ g₃) *
        threeParticleLeg12 (Fin 2) (modelOneBraid A (f₁ + f₃) (g₁ + g₃)) *
        threeParticleLeg23 (Fin 2) (modelOneBraid A f₁ g₁) := by
  ext i j
  simp only [Matrix.mul_apply, threeParticleLeg12_apply, threeParticleLeg23_apply,
    modelOneBraid, Matrix.of_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num <;> ring

/-- **Quantum Yang--Baxter equation for the whole model-1 family.**  With
`f₁ = F u - F v`, `f₃ = F v - F w` (so `f₁ + f₃ = F u - F w`) and likewise for `g`, the three
non-difference legs satisfy the spectral quantum Yang--Baxter equation.  No classification result
is used: the identity is proved directly for arbitrary `A` and arbitrary increments. -/
theorem modelOneR_quantumYangBaxter (A f₁ g₁ f₃ g₃ : ℂ) :
    threeParticleLeg12 (Fin 2) (modelOneR A f₁ g₁) *
        threeParticleLeg13 (Fin 2) (modelOneR A (f₁ + f₃) (g₁ + g₃)) *
        threeParticleLeg23 (Fin 2) (modelOneR A f₃ g₃) =
      threeParticleLeg23 (Fin 2) (modelOneR A f₃ g₃) *
        threeParticleLeg13 (Fin 2) (modelOneR A (f₁ + f₃) (g₁ + g₃)) *
        threeParticleLeg12 (Fin 2) (modelOneR A f₁ g₁) := by
  have hF2 : twoParticleFlipMatrix (Fin 2) * twoParticleFlipMatrix (Fin 2) = 1 :=
    twoParticleFlipMatrix_sq (Fin 2)
  have hflipBraid :
      threeParticleLeg12 (Fin 2) (twoParticleFlipMatrix (Fin 2)) *
            threeParticleLeg23 (Fin 2) (twoParticleFlipMatrix (Fin 2)) *
            threeParticleLeg12 (Fin 2) (twoParticleFlipMatrix (Fin 2)) =
          threeParticleLeg23 (Fin 2) (twoParticleFlipMatrix (Fin 2)) *
            threeParticleLeg12 (Fin 2) (twoParticleFlipMatrix (Fin 2)) *
            threeParticleLeg23 (Fin 2) (twoParticleFlipMatrix (Fin 2)) := by
    simpa using threeParticleFlip_braid (Fin 2)
  have hmove23 : ∀ B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      (threeParticleLeg23 (Fin 2) (twoParticleFlipMatrix (Fin 2)) *
          threeParticleLeg12 (Fin 2) (twoParticleFlipMatrix (Fin 2))) *
          threeParticleLeg23 (Fin 2) B =
        threeParticleLeg12 (Fin 2) B *
          (threeParticleLeg23 (Fin 2) (twoParticleFlipMatrix (Fin 2)) *
            threeParticleLeg12 (Fin 2) (twoParticleFlipMatrix (Fin 2))) := by
    intro B
    simpa using threeParticleFlip_move23 (Fin 2) B
  have hmove12 : ∀ B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      (threeParticleLeg12 (Fin 2) (twoParticleFlipMatrix (Fin 2)) *
          threeParticleLeg23 (Fin 2) (twoParticleFlipMatrix (Fin 2))) *
          threeParticleLeg12 (Fin 2) B =
        threeParticleLeg23 (Fin 2) B *
          (threeParticleLeg12 (Fin 2) (twoParticleFlipMatrix (Fin 2)) *
            threeParticleLeg23 (Fin 2) (twoParticleFlipMatrix (Fin 2))) := by
    intro B
    simpa using threeParticleFlip_move12 (Fin 2) B
  have hbridge :=
    (rightFlip_adjacentBraid_iff_quantumYangBaxter
        (threeParticleLeg12 (Fin 2)) (threeParticleLeg23 (Fin 2))
        (twoParticleFlipMatrix (Fin 2)) hF2 hflipBraid hmove23 hmove12
        (modelOneBraid A f₁ g₁) (modelOneBraid A (f₁ + f₃) (g₁ + g₃))
        (modelOneBraid A f₃ g₃)).mp (modelOneBraid_adjacentBraid A f₁ g₁ f₃ g₃)
  have hflip : ∀ f g : ℂ,
      rightFlip (modelOneBraid A f g) (twoParticleFlipMatrix (Fin 2)) = modelOneR A f g := by
    intro f g
    rw [modelOneBraid_eq_rightFlip]
    simp only [rightFlip, Matrix.mul_assoc, hF2, Matrix.mul_one]
  simp only [hflip, conjugatedMiddleLeg, threeParticleLeg12_twoParticleFlipMatrix] at hbridge
  simpa [threeParticleLeg13] using hbridge

/-- **Algebraic braiding unitarity.**  `R₁₂(u,v) R₂₁(v,u) = 1`, where `R₂₁ = P R P` and the
increments at `(v,u)` are the negatives of those at `(u,v)`.  This is an inversion identity between
the two orderings, not an adjoint relation. -/
theorem modelOneR_braidingUnitarity (A f g : ℂ) :
    modelOneR A f g *
        (twoParticleFlipMatrix (Fin 2) * modelOneR A (-f) (-g) *
          twoParticleFlipMatrix (Fin 2)) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, modelOneR, Matrix.of_apply, twoParticleFlipMatrix,
    Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two, PEquiv.toMatrix_apply]
  fin_cases i <;> fin_cases j <;> norm_num
  ring

/-- The square-zero matrix `E₁₂ + E₁₃` in the ordered pair basis. -/
noncomputable def modelOneNilpotent :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j =>
    if i = (0, 0) then (if j = (0, 1) then 1 else if j = (1, 0) then 1 else 0) else 0

theorem modelOneNilpotent_sq :
    modelOneNilpotent * modelOneNilpotent = 0 := by
  ext i j
  simp only [Matrix.mul_apply, modelOneNilpotent, Matrix.of_apply, Matrix.zero_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num

theorem modelOneNilpotent_ne_zero : modelOneNilpotent ≠ 0 := by
  intro h
  have := congrFun (congrFun h (0, 0)) (0, 1)
  simp [modelOneNilpotent] at this

/-- At `A = 0` the braid form is unipotent of index two: `(Ř - 1)² = 0`. -/
theorem modelOneBraid_sub_one_sq (f g : ℂ) :
    (modelOneBraid 0 f g - 1) * (modelOneBraid 0 f g - 1) = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.sub_apply, modelOneBraid, Matrix.of_apply,
    Matrix.one_apply, Matrix.zero_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num

/-- **The flip-removed channel operator squares to a unipotent matrix.**  At `A = 0`,
`R² = 1 + (δF + δG)(E₁₂ + E₁₃)`. -/
theorem modelOneR_sq (f g : ℂ) :
    modelOneR 0 f g * modelOneR 0 f g = 1 + (f + g) • modelOneNilpotent := by
  ext i j
  simp only [Matrix.mul_apply, modelOneR, modelOneNilpotent, Matrix.of_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num
  ring

/-- **Intrinsic channel mixing.**  Whenever the two increments do not cancel, the flip-removed
channel operator is not diagonalisable, so no constant one-particle gauge `U ⊗ U` — indeed no
constant similarity at all — makes it diagonal. -/
theorem not_isDiagonalizableMatrix_modelOneR (f g : ℂ) (hfg : f + g ≠ 0) :
    ¬ IsDiagonalizableMatrix (modelOneR 0 f g) := by
  refine not_isDiagonalizableMatrix_of_mul_self_unipotent
    (K := (f + g) • modelOneNilpotent) ?_ ?_ (modelOneR_sq f g)
  · rw [Matrix.smul_mul, Matrix.mul_smul, modelOneNilpotent_sq, smul_zero, smul_zero]
  · intro h
    rcases smul_eq_zero.1 h with h' | h'
    · exact hfg h'
    · exact modelOneNilpotent_ne_zero h'

/-- **No positive-metric unitarity.**  The same nontrivial Jordan block rules out every
positive-definite one-particle metric that would make the flip-removed channel operator an
isometry. -/
theorem modelOneR_not_metric_isometry (f g : ℂ) (hfg : f + g ≠ 0)
    {Q : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ} (hQ : IsPositiveDefiniteMetric Q) :
    (modelOneR 0 f g)ᴴ * Q * modelOneR 0 f g ≠ Q := by
  refine not_conjTranspose_mul_mul_eq_of_mul_self_unipotent
    (K := (f + g) • modelOneNilpotent) ?_ ?_ (modelOneR_sq f g) hQ
  · rw [Matrix.smul_mul, Matrix.mul_smul, modelOneNilpotent_sq, smul_zero, smul_zero]
  · intro h
    rcases smul_eq_zero.1 h with h' | h'
    · exact hfg h'
    · exact modelOneNilpotent_ne_zero h'

/-- **Wrong zero-rapidity sector.**  No scalar multiple of the identity equals `-P`, so the
regular quantum branch can never be normalised into the fermionic `S(0) = -P` sector used by the
compact-local intertwiner theorem. -/
theorem smul_one_ne_neg_flip (c : ℂ) :
    c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≠
      -twoParticleFlipMatrix (Fin 2) := by
  intro h
  have h1 := congrFun (congrFun h (0, 1)) (1, 0)
  simp [twoParticleFlipMatrix, PEquiv.toMatrix_apply] at h1

end

end GaloisForLFunctions.HTGeometry
