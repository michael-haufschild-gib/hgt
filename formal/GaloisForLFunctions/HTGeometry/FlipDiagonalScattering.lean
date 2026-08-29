import GaloisForLFunctions.HTGeometry.AnchoredProjectiveEntryField
import GaloisForLFunctions.HTGeometry.DifferentialAdjoinPairClassification
import GaloisForLFunctions.HTGeometry.ScalarLogCurrentReconstruction

/-!
# Flip-diagonal two-particle scattering

A *flip-diagonal* two-particle operator acts on the ordered pair basis by exchanging the two
tensor factors and multiplying by one coefficient per ordered pair:

```text
S (e_a ⊗ e_b) = ω (a,b) • (e_b ⊗ e_a).
```

Equivalently `S = P · diagonal ω` for the tensor flip `P`.  This file collects the exact algebra
of that family over an arbitrary commutative ring, its Yang--Baxter property on two species, its
logarithmic-derivative connection over a differential field, and the differential field generated
by its entry ratios.

Nothing analytic is assumed anywhere: the Yang--Baxter equation holds for arbitrary coefficient
functions, and the channel algebra is commutative as soon as the coefficients are symmetric under
exchanging the two labels.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Matrix

open scoped Differential

noncomputable section

section Ring

variable {κ : Type*} [DecidableEq κ] {R : Type*} [CommRing R]

/-- The tensor flip on the ordered pair basis, over an arbitrary commutative ring. -/
def pairFlip (κ : Type*) [DecidableEq κ] (R : Type*) [CommRing R] :
    Matrix (κ × κ) (κ × κ) R :=
  (show Equiv.Perm (κ × κ) from Equiv.prodComm κ κ).permMatrix R

@[simp]
theorem pairFlip_apply (i j : κ × κ) :
    pairFlip κ R i j = if j = (i.2, i.1) then 1 else 0 := by
  have hswap : (i.2, i.1) = i.swap := rfl
  simp [pairFlip, PEquiv.toMatrix_apply, eq_comm, hswap]

theorem pairFlip_eq_twoParticleFlipMatrix (κ : Type*) [DecidableEq κ] :
    pairFlip κ ℂ = twoParticleFlipMatrix κ := rfl

variable [Fintype κ]

@[simp]
theorem pairFlip_mul_self : pairFlip κ R * pairFlip κ R = 1 := by
  let σ : Equiv.Perm (κ × κ) := Equiv.prodComm κ κ
  have hσ2 : σ * σ = 1 := by
    apply Equiv.ext
    intro x
    simp [Equiv.Perm.mul_apply, σ]
  change σ.permMatrix R * σ.permMatrix R = 1
  rw [← Matrix.permMatrix_mul, hσ2, Matrix.permMatrix_one]

/-- A flip-diagonal two-particle operator: exchange the two factors and multiply by one
coefficient per ordered pair. -/
def flipDiagonal (d : κ × κ → R) : Matrix (κ × κ) (κ × κ) R :=
  pairFlip κ R * Matrix.diagonal d

@[simp]
theorem flipDiagonal_apply (d : κ × κ → R) (i j : κ × κ) :
    flipDiagonal d i j = if j = (i.2, i.1) then d j else 0 := by
  rw [flipDiagonal, Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · by_cases hij : j = (i.2, i.1) <;> simp [hij]
  · intro b _ hb
    rw [Matrix.diagonal_apply_ne d hb, mul_zero]
  · intro h
    simp at h

/-- The coefficients determine the operator. -/
theorem flipDiagonal_injective {d e : κ × κ → R} (h : flipDiagonal d = flipDiagonal e) :
    d = e := by
  funext p
  have := congrFun (congrFun h (p.2, p.1)) p
  simpa using this

/-- **Zero-rapidity anchor.**  When every coefficient equals `-1`, the flip-diagonal operator is
exactly `-P`. -/
theorem flipDiagonal_eq_neg_pairFlip {d : κ × κ → R} (hd : ∀ p, d p = -1) :
    flipDiagonal d = -pairFlip κ R := by
  ext i j
  by_cases hij : j = (i.2, i.1) <;> simp [hij, hd]

/-- Symmetric coefficients commute with the flip. -/
theorem pairFlip_mul_diagonal_comm {d : κ × κ → R} (hd : ∀ a b, d (a, b) = d (b, a)) :
    pairFlip κ R * Matrix.diagonal d = Matrix.diagonal d * pairFlip κ R := by
  ext i j
  have hL : (pairFlip κ R * Matrix.diagonal d) i j = pairFlip κ R i j * d j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne d hb, mul_zero]
    · intro h
      simp at h
  have hR : (Matrix.diagonal d * pairFlip κ R) i j = d i * pairFlip κ R i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne' d hb, zero_mul]
    · intro h
      simp at h
  rw [hL, hR]
  by_cases hij : j = (i.2, i.1)
  · subst j
    simp [hd i.2 i.1]
  · simp [hij]

/-- **Commuting channel algebra.**  Two flip-diagonal operators with symmetric coefficients
multiply to the diagonal product; in particular they commute for all parameter values. -/
theorem flipDiagonal_mul_flipDiagonal {d e : κ × κ → R}
    (hd : ∀ a b, d (a, b) = d (b, a)) :
    flipDiagonal d * flipDiagonal e = Matrix.diagonal fun p => d p * e p := by
  rw [flipDiagonal, flipDiagonal, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal d),
    ← pairFlip_mul_diagonal_comm hd, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    pairFlip_mul_self, Matrix.one_mul, Matrix.diagonal_mul_diagonal]

theorem flipDiagonal_comm {d e : κ × κ → R}
    (hd : ∀ a b, d (a, b) = d (b, a)) (he : ∀ a b, e (a, b) = e (b, a)) :
    flipDiagonal d * flipDiagonal e = flipDiagonal e * flipDiagonal d := by
  rw [flipDiagonal_mul_flipDiagonal hd, flipDiagonal_mul_flipDiagonal he]
  simp [mul_comm]

end Ring

section YangBaxter

set_option maxHeartbeats 1000000 in
/-- **The adjacent spectral braid equation holds for arbitrary flip-diagonal coefficients.**  No
symmetry, regularity or analyticity of the coefficient functions is needed: both sides send
`e_a ⊗ e_b ⊗ e_c` to the same multiple of `e_c ⊗ e_b ⊗ e_a`. -/
theorem flipDiagonal_adjacentBraid (d₁ d₂ d₃ : Fin 2 × Fin 2 → ℂ) :
    threeParticleLeg12 (Fin 2) (flipDiagonal d₁) *
        threeParticleLeg23 (Fin 2) (flipDiagonal d₂) *
        threeParticleLeg12 (Fin 2) (flipDiagonal d₃) =
      threeParticleLeg23 (Fin 2) (flipDiagonal d₃) *
        threeParticleLeg12 (Fin 2) (flipDiagonal d₂) *
        threeParticleLeg23 (Fin 2) (flipDiagonal d₁) := by
  ext i j
  simp only [Matrix.mul_apply, threeParticleLeg12_apply, threeParticleLeg23_apply,
    flipDiagonal_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num
  all_goals ring

/-- **Quantum Yang--Baxter equation for a flip-diagonal two-species scattering family.** -/
theorem flipDiagonal_quantumYangBaxter {Θ : Type*} [Add Θ] (ω : Θ → Fin 2 × Fin 2 → ℂ)
    (x y : Θ) :
    threeParticleLeg12 (Fin 2) (rightFlip (flipDiagonal (ω x)) (twoParticleFlipMatrix (Fin 2))) *
        threeParticleLeg13 (Fin 2)
          (rightFlip (flipDiagonal (ω (x + y))) (twoParticleFlipMatrix (Fin 2))) *
        threeParticleLeg23 (Fin 2)
          (rightFlip (flipDiagonal (ω y)) (twoParticleFlipMatrix (Fin 2))) =
      threeParticleLeg23 (Fin 2)
          (rightFlip (flipDiagonal (ω y)) (twoParticleFlipMatrix (Fin 2))) *
        threeParticleLeg13 (Fin 2)
          (rightFlip (flipDiagonal (ω (x + y))) (twoParticleFlipMatrix (Fin 2))) *
        threeParticleLeg12 (Fin 2)
          (rightFlip (flipDiagonal (ω x)) (twoParticleFlipMatrix (Fin 2))) := by
  have hbridge :=
    (matrix_rightFlip_adjacentBraid_iff_quantumYangBaxter (κ := Fin 2)
      fun t => flipDiagonal (ω t)).mp
      (fun a b => flipDiagonal_adjacentBraid (ω a) (ω (a + b)) (ω b))
  exact hbridge x y

end YangBaxter

section DifferentialField

universe u

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [Differential F] [Differential E] [DifferentialAlgebra F E]

variable {κ : Type*} [DecidableEq κ] [Fintype κ]

/-- Entrywise derivative of a square matrix over a differential field, at an arbitrary index
type.  On `Fin (n+1)` this is the corpus `matrixDifferential`. -/
def entrywiseDeriv {ι : Type*} (S : Matrix ι ι E) : Matrix ι ι E := fun a b => (S a b)′

theorem entrywiseDeriv_eq_matrixDifferential {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    entrywiseDeriv S = matrixDifferential S := rfl

/-- The logarithmic connection of a matrix, in the corpus's Wigner--Smith normalisation. -/
def wignerSmithOf {ι : Type*} [Fintype ι] [DecidableEq ι] (c : F) (S : Matrix ι ι E) :
    Matrix ι ι E :=
  (-algebraMap F E c) • (S⁻¹ * entrywiseDeriv S)

omit [Differential F] [DifferentialAlgebra F E] in
theorem wignerSmithOf_eq_matrixWignerSmith {n : ℕ} (c : F)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    wignerSmithOf c S = matrixWignerSmith c S := rfl

theorem entrywiseDeriv_flipDiagonal (d : κ × κ → E) :
    entrywiseDeriv (flipDiagonal d) = flipDiagonal fun p => (d p)′ := by
  ext i j
  by_cases hij : j = (i.2, i.1) <;> simp [entrywiseDeriv, hij]

omit [Differential E] in
theorem flipDiagonal_inv (d : κ × κ → E) (hd : ∀ p, d p ≠ 0) :
    (flipDiagonal d)⁻¹ = Matrix.diagonal (fun p => (d p)⁻¹) * pairFlip κ E := by
  apply Matrix.inv_eq_right_inv
  rw [flipDiagonal, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal d),
    Matrix.diagonal_mul_diagonal]
  have hone : (Matrix.diagonal fun p => d p * (d p)⁻¹) = (1 : Matrix (κ × κ) (κ × κ) E) := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext p
    exact mul_inv_cancel₀ (hd p)
  rw [hone, Matrix.one_mul, pairFlip_mul_self]

/-- **The logarithmic connection of a flip-diagonal family is diagonal.**  Its entries are the
logarithmic derivatives of the coefficients, one per ordered pair. -/
theorem flipDiagonal_logDerivConnection (d : κ × κ → E) (hd : ∀ p, d p ≠ 0) :
    (flipDiagonal d)⁻¹ * entrywiseDeriv (flipDiagonal d) =
      Matrix.diagonal fun p => Differential.logDeriv (d p) := by
  rw [flipDiagonal_inv d hd, entrywiseDeriv_flipDiagonal, flipDiagonal, Matrix.mul_assoc,
    ← Matrix.mul_assoc (pairFlip κ E), pairFlip_mul_self, Matrix.one_mul,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  rw [Differential.logDeriv, div_eq_inv_mul]

/-- The two-species coefficient vector `Ω = diag(h, -1, -1, -1)` of the geometric-CDD model, in
the ordered pair basis. -/
def cddCoefficient (h : E) : Fin 2 × Fin 2 → E := fun p => if p = (0, 0) then h else -1

omit [Differential E] in
theorem cddCoefficient_symm (h : E) (a b : Fin 2) :
    cddCoefficient h (a, b) = cddCoefficient h (b, a) := by
  fin_cases a <;> fin_cases b <;> simp [cddCoefficient]

omit [Differential E] in
theorem cddCoefficient_ne_zero {h : E} (hh : h ≠ 0) (p : Fin 2 × Fin 2) :
    cddCoefficient h p ≠ 0 := by
  by_cases hp : p = (0, 0) <;> simp [cddCoefficient, hp, hh]

omit [Differential E] in
/-- **Zero-rapidity anchor `S(0) = -P`.**  When the free coefficient also takes the value `-1`,
the two-species scattering matrix is exactly minus the tensor flip. -/
theorem flipDiagonal_cddCoefficient_neg_one :
    flipDiagonal (cddCoefficient (-1 : E)) = -pairFlip (Fin 2) E :=
  flipDiagonal_eq_neg_pairFlip fun p => by by_cases hp : p = (0, 0) <;> simp [cddCoefficient, hp]

omit [Differential E] in
/-- The model is a genuine interaction: unless the free coefficient is itself `-1`, the scattering
matrix is not the constant exchange operator `-P`. -/
theorem flipDiagonal_cddCoefficient_ne_neg_pairFlip {h : E} (hh : h ≠ -1) :
    flipDiagonal (cddCoefficient h) ≠ -pairFlip (Fin 2) E := by
  intro hEq
  rw [← flipDiagonal_cddCoefficient_neg_one] at hEq
  have hcoeff := flipDiagonal_injective hEq
  have h0 := congrFun hcoeff (0, 0)
  simp only [cddCoefficient] at h0
  exact hh h0

/-- **The connection has a single nonzero channel.**  `S⁻¹ ∂S = diag(u, 0, 0, 0)` with
`u = h′ / h`. -/
theorem cdd_logDerivConnection {h : E} (hh : h ≠ 0) :
    (flipDiagonal (cddCoefficient h))⁻¹ * entrywiseDeriv (flipDiagonal (cddCoefficient h)) =
      Matrix.diagonal fun p => if p = (0, 0) then Differential.logDeriv h else 0 := by
  rw [flipDiagonal_logDerivConnection _ (cddCoefficient_ne_zero hh)]
  congr 1
  funext p
  by_cases hp : p = (0, 0)
  · simp [cddCoefficient, hp]
  · simp [cddCoefficient, hp, Differential.logDeriv]

/-- Traceless part of a square matrix at an arbitrary finite index type.  On `Fin (n+1)` this is
the corpus `matrixTracelessPartField`. -/
def tracelessPartOf {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι E) : Matrix ι ι E :=
  Q + (-(Matrix.trace Q / (Fintype.card ι : E))) • 1

omit [Differential E] [Differential F] [DifferentialAlgebra F E] in
theorem tracelessPartOf_eq_matrixTracelessPartField [CharZero E] {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :
    tracelessPartOf Q = matrixTracelessPartField Q := by
  rw [tracelessPartOf, matrixTracelessPartField]
  norm_num

omit [Differential E] [Differential F] [DifferentialAlgebra F E] in
/-- **Trace of the single-channel connection.**  `tr diag(u,0,0,0) = u`. -/
theorem trace_singleChannel (u : E) :
    Matrix.trace (Matrix.diagonal fun p : Fin 2 × Fin 2 => if p = (0, 0) then u else 0) = u := by
  simp [Matrix.trace_diagonal]

omit [Differential E] [Differential F] [DifferentialAlgebra F E] in
/-- **Traceless part of the single-channel connection.**  Removing the trace of `diag(u,0,0,0)`
in four channels leaves `diag(3u/4, -u/4, -u/4, -u/4)`. -/
theorem tracelessPartOf_singleChannel [CharZero E] (u : E) :
    tracelessPartOf (Matrix.diagonal fun p : Fin 2 × Fin 2 => if p = (0, 0) then u else 0) =
      Matrix.diagonal fun p : Fin 2 × Fin 2 =>
        if p = (0, 0) then 3 * u / 4 else -(u / 4) := by
  have hcard : (Fintype.card (Fin 2 × Fin 2) : E) = 4 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    norm_num
  rw [tracelessPartOf, trace_singleChannel, hcard]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = (0, 0) <;> simp [hi]
    ring
  · simp [hij]

omit [Differential F] [DifferentialAlgebra F E] in
/-- **The relative channel-delay reporter.**  The difference of the two leading diagonal
reporters of the Wigner--Smith matrix is `-i u`, with `u = h′ / h`. -/
theorem cdd_relativeDelay (c : F) {h : E} (hh : h ≠ 0) :
    wignerSmithOf c (flipDiagonal (cddCoefficient h)) (0, 0) (0, 0) -
        wignerSmithOf c (flipDiagonal (cddCoefficient h)) (0, 1) (0, 1) =
      -algebraMap F E c * Differential.logDeriv h := by
  rw [wignerSmithOf, cdd_logDerivConnection hh]
  simp

/-- **The relative reporter is hypertranscendental exactly when the scattering coefficient is.**
A nonzero hypertranscendental coefficient has a hypertranscendental logarithmic current. -/
theorem cdd_relativeDelay_hypertranscendental [CharZero E] {h : E}
    (hh : HypertranscendentalOver F h) (hh0 : h ≠ 0) :
    HypertranscendentalOver F (Differential.logDeriv h) :=
  logDeriv_hypertranscendentalOver hh hh0

/-- **The projective field of the two-species model is `F⟨h⟩`.**  Anchoring the pivot at one of the
constant channels, every entry ratio is `0`, `1` or `-h`, and the free coefficient is recovered. -/
theorem differentialAdjoin_pivotEntryFamily_cdd (h : E) :
    differentialAdjoin F
        (Set.range (pivotEntryFamily (flipDiagonal (cddCoefficient h)) ((0, 1), (1, 0)))) =
      differentialAdjoin F ({h} : Set E) := by
  have hpivot : flipDiagonal (cddCoefficient h) (0, 1) (1, 0) = -1 := by
    simp [cddCoefficient]
  have hstep :
      differentialAdjoin F
          (Set.range (pivotEntryFamily (flipDiagonal (cddCoefficient h)) ((0, 1), (1, 0)))) =
        differentialAdjoin F ({-h} : Set E) := by
    refine differentialAdjoin_range_eq_singleton _ ((0, 0), (0, 0)) (-h) ?_ ?_
    · rintro ⟨i, j⟩
      fin_cases i <;> fin_cases j <;>
        simp only [pivotEntryFamily, hpivot, flipDiagonal_apply, cddCoefficient]
      all_goals norm_num
      all_goals
        first
          | exact IntermediateField.one_mem _
          | exact IntermediateField.zero_mem _
          | exact IntermediateField.neg_mem _ (IntermediateField.one_mem _)
          | exact subset_differentialAdjoin F ({-h} : Set E) rfl
          | exact neg_mem_iff.mp (subset_differentialAdjoin F ({-h} : Set E) rfl)
    · simp [pivotEntryFamily, cddCoefficient]
  rw [hstep, differentialAdjoin_neg_singleton]

/-- **Projective differential transcendence degree one.**  The two-species model has a projective
field generated by the single scattering coefficient, of differential transcendence degree one
exactly when that coefficient is hypertranscendental over the base. -/
theorem cdd_projectiveField_degree [CharZero E] {h : E} (hh : HypertranscendentalOver F h) :
    differentialAdjoin F
        (Set.range (pivotEntryFamily (flipDiagonal (cddCoefficient h)) ((0, 1), (1, 0)))) =
        differentialAdjoin F ({h} : Set E) ∧
      (letI := derivationClosedDifferential (differentialAdjoin F ({h} : Set E))
        (derivationClosed_differentialAdjoin F ({h} : Set E))
       differentialTranscendenceDegree F (differentialAdjoin F ({h} : Set E)) = 1) :=
  ⟨differentialAdjoin_pivotEntryFamily_cdd h,
    differentialTranscendenceDegree_differentialAdjoin_singleton_eq_one hh⟩

end DifferentialField

end

end GaloisForLFunctions.HTGeometry
