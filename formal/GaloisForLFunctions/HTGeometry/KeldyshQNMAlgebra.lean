import GaloisForLFunctions.HTGeometry.FiniteModalHadamardAlgebra
import GaloisForLFunctions.HTGeometry.NonabelianAsymptoticConnection

/-!
# Finite-rank Keldysh algebra for quasinormal modes

Unconditional finite-dimensional core of the Keldysh/QNM identities used in
Besson--Jaramillo, *Quasi-normal mode expansions of black hole perturbations:
a hyperboloidal Keldysh's approach* (arXiv:2412.02793v2).

The module proves exact right/left mode diagonalization, biorthogonality,
reconstruction, generalized-pencil normalization, projective invariance of
returned modes, the Riesz scalar-product bridge, quadratic frequency mixing,
Sobolev-energy monotonicity, and a strict exponential truncation factor.
Analytic Fredholm hypotheses and numerically proposed Weyl laws are deliberately
not asserted here.
-/

open scoped BigOperators Matrix ComplexConjugate InnerProductSpace
open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Invertible modal basis used by the finite-dimensional Keldysh model. -/
abbrev KeldyshGL (n : ℕ) := Matrix.GeneralLinearGroup (Fin n) ℂ

/-- Generator reconstructed from a modal basis and its modal frequencies. -/
def keldyshGenerator {n : ℕ} (V : KeldyshGL n) (omega : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  V.val * Matrix.diagonal omega * V.inv

theorem keldyshGenerator_mul_basis {n : ℕ} (V : KeldyshGL n)
    (omega : Fin n → ℂ) :
    keldyshGenerator V omega * V.val = V.val * Matrix.diagonal omega := by
  rw [keldyshGenerator, Matrix.mul_assoc, Matrix.mul_assoc, V.inv_val, Matrix.mul_one]

theorem basisInv_mul_keldyshGenerator {n : ℕ} (V : KeldyshGL n)
    (omega : Fin n → ℂ) :
    V.inv * keldyshGenerator V omega = Matrix.diagonal omega * V.inv := by
  unfold keldyshGenerator
  calc
    V.inv * (V.val * Matrix.diagonal omega * V.inv) =
        (V.inv * V.val) * Matrix.diagonal omega * V.inv := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal omega * V.inv := by rw [V.inv_val, Matrix.one_mul]

/-- Rows of the inverse modal basis are biorthogonal to columns of the basis. -/
theorem keldysh_basis_biorthogonal {n : ℕ} (V : KeldyshGL n)
    (i j : Fin n) :
    ∑ k, V.inv i k * V.val k j = if i = j then 1 else 0 := by
  have h := congrFun (congrFun V.inv_val i) j
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

/-- Exact reconstruction from Keldysh excitation coefficients. -/
theorem keldysh_basis_reconstruction {n : ℕ} (V : KeldyshGL n)
    (u : Fin n → ℂ) :
    V.val *ᵥ (V.inv *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, V.val_inv, Matrix.one_mulVec]

/-- Modal synthesis with a freely chosen multiplier on every QNM. -/
def keldyshModalSynthesis {n : ℕ} (V : KeldyshGL n)
    (multiplier : Fin n → ℂ) (u : Fin n → ℂ) : Fin n → ℂ :=
  V.val *ᵥ (Matrix.diagonal multiplier *ᵥ (V.inv *ᵥ u))

theorem keldyshModalSynthesis_one {n : ℕ} (V : KeldyshGL n)
    (u : Fin n → ℂ) :
    keldyshModalSynthesis V (fun _ => 1) u = u := by
  have hdiag (x : Fin n → ℂ) : Matrix.diagonal (fun _ : Fin n => (1 : ℂ)) *ᵥ x = x := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [keldyshModalSynthesis, hdiag]
  exact keldysh_basis_reconstruction V u

/-- Rank-one expansion of finite Keldysh modal synthesis. -/
theorem keldyshModalSynthesis_apply {n : ℕ} (V : KeldyshGL n)
    (multiplier : Fin n → ℂ) (u : Fin n → ℂ) (r : Fin n) :
    keldyshModalSynthesis V multiplier u r =
      ∑ i, multiplier i * (∑ j, V.inv i j * u j) * V.val r i := by
  have hdiag (x : Fin n → ℂ) :
      Matrix.diagonal multiplier *ᵥ x = fun i => multiplier i * x i := by
    funext i
    simp [Matrix.mulVec]
  rw [keldyshModalSynthesis, hdiag]
  simp only [Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro i _
  simp only [dotProduct]
  ring

/-- Rank-one residue projector associated with mode `i`. -/
def keldyshModeProjector {n : ℕ} (V : KeldyshGL n)
    (i : Fin n) (u : Fin n → ℂ) : Fin n → ℂ :=
  fun r => (∑ j, V.inv i j * u j) * V.val r i

/-- Modal projectors resolve the identity. -/
theorem sum_keldyshModeProjector {n : ℕ} (V : KeldyshGL n)
    (u : Fin n → ℂ) :
    ∑ i, keldyshModeProjector V i u = u := by
  funext r
  have h := congrFun (keldysh_basis_reconstruction V u) r
  simpa [keldyshModeProjector, Matrix.mulVec, dotProduct, mul_comm] using h

/-- Rank-one modal projectors are mutually orthogonal idempotents. -/
theorem keldyshModeProjector_comp {n : ℕ} (V : KeldyshGL n)
    (i j : Fin n) (u : Fin n → ℂ) :
    keldyshModeProjector V i (keldyshModeProjector V j u) =
      if i = j then keldyshModeProjector V i u else 0 := by
  funext r
  unfold keldyshModeProjector
  have hsum :
      (∑ k, V.inv i k * ((∑ l, V.inv j l * u l) * V.val k j)) =
        (∑ l, V.inv j l * u l) * (∑ k, V.inv i k * V.val k j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum, keldysh_basis_biorthogonal]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- Totalized finite-rank Keldysh resolvent. At a pole its corresponding scalar inverse is zero,
matching Lean's total division while retaining the exact partial-fraction identity. -/
def keldyshResolvent {n : ℕ} (V : KeldyshGL n)
    (omega : Fin n → ℂ) (z : ℂ) (u : Fin n → ℂ) : Fin n → ℂ :=
  keldyshModalSynthesis V (fun i => (z - omega i)⁻¹) u

/-- Keldysh resolvent as a sum of frequency-pole-weighted rank-one residues. -/
theorem keldyshResolvent_apply {n : ℕ} (V : KeldyshGL n)
    (omega : Fin n → ℂ) (z : ℂ) (u : Fin n → ℂ) (r : Fin n) :
    keldyshResolvent V omega z u r =
      ∑ i, (z - omega i)⁻¹ * keldyshModeProjector V i u r := by
  rw [keldyshResolvent, keldyshModalSynthesis_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [keldyshModeProjector]
  ring

/-- Generalized-pencil generator `L = B V diag(omega) V⁻¹`. -/
def keldyshPencilGenerator {n : ℕ} (B V : KeldyshGL n)
    (omega : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  B.val * V.val * Matrix.diagonal omega * V.inv

/-- Left comodes normalized against the mass matrix `B`. -/
def keldyshPencilLeftComodes {n : ℕ} (B V : KeldyshGL n) :
    Matrix (Fin n) (Fin n) ℂ :=
  V.inv * B.inv

theorem keldyshPencilGenerator_mul_basis {n : ℕ} (B V : KeldyshGL n)
    (omega : Fin n → ℂ) :
    keldyshPencilGenerator B V omega * V.val =
      B.val * V.val * Matrix.diagonal omega := by
  unfold keldyshPencilGenerator
  calc
    (B.val * V.val * Matrix.diagonal omega * V.inv) * V.val =
        B.val * V.val * Matrix.diagonal omega * (V.inv * V.val) := by
      simp only [Matrix.mul_assoc]
    _ = B.val * V.val * Matrix.diagonal omega := by rw [V.inv_val, Matrix.mul_one]

/-- Generalized biorthogonality `W B V = 1`. -/
theorem keldyshPencilLeftComodes_mul_mass_mul_basis {n : ℕ}
    (B V : KeldyshGL n) :
    keldyshPencilLeftComodes B V * B.val * V.val = 1 := by
  unfold keldyshPencilLeftComodes
  calc
    (V.inv * B.inv) * B.val * V.val = V.inv * (B.inv * B.val) * V.val := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [B.inv_val, Matrix.mul_one, V.inv_val]

theorem basis_mul_keldyshPencilLeftComodes_mul_mass {n : ℕ}
    (B V : KeldyshGL n) :
    V.val * keldyshPencilLeftComodes B V * B.val = 1 := by
  rw [keldyshPencilLeftComodes, Matrix.mul_assoc, Matrix.mul_assoc,
    B.inv_val, Matrix.mul_one, V.val_inv]

theorem keldyshPencilLeftComodes_mul_generator {n : ℕ}
    (B V : KeldyshGL n) (omega : Fin n → ℂ) :
    keldyshPencilLeftComodes B V * keldyshPencilGenerator B V omega =
      Matrix.diagonal omega * keldyshPencilLeftComodes B V * B.val := by
  unfold keldyshPencilLeftComodes keldyshPencilGenerator
  have hB : B.inv * B.val = 1 := B.inv_val
  have hV : V.inv * V.val = 1 := V.inv_val
  have hVB : (V.inv * B.inv) * B.val = V.inv := by
    rw [Matrix.mul_assoc, hB, Matrix.mul_one]
  calc
    (V.inv * B.inv) * (B.val * V.val * Matrix.diagonal omega * V.inv) =
        ((V.inv * B.inv) * B.val) *
          (V.val * Matrix.diagonal omega * V.inv) := by
      simp only [Matrix.mul_assoc]
    _ = V.inv * (V.val * Matrix.diagonal omega * V.inv) := by rw [hVB]
    _ = (V.inv * V.val) * (Matrix.diagonal omega * V.inv) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal omega * V.inv := by rw [hV, Matrix.one_mul]
    _ = Matrix.diagonal omega * (V.inv * B.inv) * B.val := by
      rw [Matrix.mul_assoc, hVB]

/-- Generalized-pencil reconstruction from coefficients `W (B u)`. -/
theorem keldyshPencil_reconstruction {n : ℕ} (B V : KeldyshGL n)
    (u : Fin n → ℂ) :
    V.val *ᵥ (keldyshPencilLeftComodes B V *ᵥ (B.val *ᵥ u)) = u := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    basis_mul_keldyshPencilLeftComodes_mul_mass, Matrix.one_mulVec]

/-- Generalized-pencil modal synthesis with mass-weighted left coefficients. -/
def keldyshPencilModalSynthesis {n : ℕ} (B V : KeldyshGL n)
    (multiplier : Fin n → ℂ) (u : Fin n → ℂ) : Fin n → ℂ :=
  V.val *ᵥ (Matrix.diagonal multiplier *ᵥ
    (keldyshPencilLeftComodes B V *ᵥ (B.val *ᵥ u)))

theorem keldyshPencilModalSynthesis_one {n : ℕ} (B V : KeldyshGL n)
    (u : Fin n → ℂ) :
    keldyshPencilModalSynthesis B V (fun _ => 1) u = u := by
  have hdiag (x : Fin n → ℂ) : Matrix.diagonal (fun _ : Fin n => (1 : ℂ)) *ᵥ x = x := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [keldyshPencilModalSynthesis, hdiag]
  exact keldyshPencil_reconstruction B V u

/-- Rank-one generalized-pencil expansion with coefficients `W B u`. -/
theorem keldyshPencilModalSynthesis_apply {n : ℕ} (B V : KeldyshGL n)
    (multiplier : Fin n → ℂ) (u : Fin n → ℂ) (r : Fin n) :
    keldyshPencilModalSynthesis B V multiplier u r =
      ∑ i, multiplier i *
        (∑ j, keldyshPencilLeftComodes B V i j * (∑ k, B.val j k * u k)) *
          V.val r i := by
  have hdiag (x : Fin n → ℂ) :
      Matrix.diagonal multiplier *ᵥ x = fun i => multiplier i * x i := by
    funext i
    simp [Matrix.mulVec]
  rw [keldyshPencilModalSynthesis, hdiag]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Paper's normalized excitation coefficient `alpha(u) / alpha(mode)`. -/
def keldyshExcitationCoefficient {X : Type*} [AddCommGroup X] [Module ℂ X]
    (alpha : X →ₗ[ℂ] ℂ) (u mode : X) : ℂ :=
  alpha u / alpha mode

/-- Observable returned contribution; invariant under modal normalization. -/
def keldyshReturnedMode {X : Type*} [AddCommGroup X] [Module ℂ X]
    (alpha : X →ₗ[ℂ] ℂ) (u mode : X) : X :=
  keldyshExcitationCoefficient alpha u mode • mode

theorem keldyshExcitationCoefficient_mode_unit_smul
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (alpha : X →ₗ[ℂ] ℂ) (u mode : X) (z : ℂˣ) :
    keldyshExcitationCoefficient alpha u ((z : ℂ) • mode) =
      (z⁻¹ : ℂ) * keldyshExcitationCoefficient alpha u mode := by
  simp only [keldyshExcitationCoefficient, map_smul, smul_eq_mul]
  field_simp [z.ne_zero]

/-- Rescaling a mode changes its coefficient inversely but not its contribution. -/
theorem keldyshReturnedMode_mode_unit_smul
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (alpha : X →ₗ[ℂ] ℂ) (u mode : X) (z : ℂˣ) :
    keldyshReturnedMode alpha u ((z : ℂ) • mode) =
      keldyshReturnedMode alpha u mode := by
  rw [keldyshReturnedMode,
    keldyshExcitationCoefficient_mode_unit_smul alpha u mode z,
    keldyshReturnedMode]
  simp only [smul_smul]
  congr 1
  change ((z⁻¹ : ℂ) * keldyshExcitationCoefficient alpha u mode) * (z : ℂ) = _
  field_simp [z.ne_zero]

/-- Rescaling a comode cancels between numerator and denominator. -/
theorem keldyshExcitationCoefficient_comode_unit_smul
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (alpha : X →ₗ[ℂ] ℂ) (u mode : X) (z : ℂˣ) :
    keldyshExcitationCoefficient ((z : ℂ) • alpha) u mode =
      keldyshExcitationCoefficient alpha u mode := by
  simp only [keldyshExcitationCoefficient, LinearMap.smul_apply, smul_eq_mul]
  field_simp [z.ne_zero]

theorem keldyshReturnedMode_comode_unit_smul
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (alpha : X →ₗ[ℂ] ℂ) (u mode : X) (z : ℂˣ) :
    keldyshReturnedMode ((z : ℂ) • alpha) u mode =
      keldyshReturnedMode alpha u mode := by
  rw [keldyshReturnedMode, keldyshExcitationCoefficient_comode_unit_smul,
    keldyshReturnedMode]

/-- Riesz representation of a Keldysh left comode. -/
def keldyshRieszComode
    {X : Type*} [SeminormedAddCommGroup X] [InnerProductSpace ℂ X]
    (w : X) : X →ₗ[ℂ] ℂ :=
  (innerSL ℂ w).toLinearMap

@[simp] theorem keldyshRieszComode_apply
    {X : Type*} [SeminormedAddCommGroup X] [InnerProductSpace ℂ X]
    (w v : X) :
    keldyshRieszComode w v = ⟪w, v⟫_ℂ := by
  exact innerSL_apply_apply ℂ w v

theorem keldyshExcitationCoefficient_riesz
    {X : Type*} [SeminormedAddCommGroup X] [InnerProductSpace ℂ X]
    (w u mode : X) :
    keldyshExcitationCoefficient (keldyshRieszComode w) u mode =
      ⟪w, u⟫_ℂ / ⟪w, mode⟫_ℂ := by
  rfl

/-- Generalized-pencil coefficient `alpha(B u) / alpha(B mode)`. -/
def keldyshPencilExcitationCoefficient
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (B : X →ₗ[ℂ] X) (alpha : X →ₗ[ℂ] ℂ) (u mode : X) : ℂ :=
  alpha (B u) / alpha (B mode)

def keldyshPencilReturnedMode
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (B : X →ₗ[ℂ] X) (alpha : X →ₗ[ℂ] ℂ) (u mode : X) : X :=
  keldyshPencilExcitationCoefficient B alpha u mode • mode

theorem keldyshPencilReturnedMode_mode_unit_smul
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (B : X →ₗ[ℂ] X) (alpha : X →ₗ[ℂ] ℂ) (u mode : X) (z : ℂˣ) :
    keldyshPencilReturnedMode B alpha u ((z : ℂ) • mode) =
      keldyshPencilReturnedMode B alpha u mode := by
  simp only [keldyshPencilReturnedMode, keldyshPencilExcitationCoefficient,
    map_smul, smul_eq_mul, smul_smul]
  congr 1
  field_simp [z.ne_zero]

/-- Discrete-time node corresponding to angular frequency `omega`. -/
def qnmSampleNode (omega : ℂ) : ℂ := Complex.exp (Complex.I * omega)

/-- Frequency sums become products of sampled QNM nodes. -/
theorem qnmSampleNode_add (omega nu : ℂ) :
    qnmSampleNode (omega + nu) = qnmSampleNode omega * qnmSampleNode nu := by
  rw [qnmSampleNode, mul_add, Complex.exp_add]
  rfl

/-- Finite sampled QNM signal. -/
def finiteQNMSequence {d : ℕ} (amplitude frequency : Fin d → ℂ) : ℕ → ℂ :=
  _root_.HTGeometry.finiteModalSequence amplitude (qnmSampleNode ∘ frequency)

/-- Pointwise multiplication produces pairwise-sum QNM frequencies. -/
theorem finiteQNMSequence_mul {d e : ℕ}
    (amplitude1 frequency1 : Fin d → ℂ)
    (amplitude2 frequency2 : Fin e → ℂ) (n : ℕ) :
    finiteQNMSequence amplitude1 frequency1 n * finiteQNMSequence amplitude2 frequency2 n =
      _root_.HTGeometry.finiteModalSequence
        (_root_.HTGeometry.finiteModalProductWeight amplitude1 amplitude2)
        (_root_.HTGeometry.finiteModalProductNode
          (qnmSampleNode ∘ frequency1) (qnmSampleNode ∘ frequency2)) n :=
  _root_.HTGeometry.finiteModalSequence_mul amplitude1 (qnmSampleNode ∘ frequency1)
    amplitude2 (qnmSampleNode ∘ frequency2) n

/-- A quadratic `d`-mode QNM signal has Hankel width at most `d²`. -/
theorem finiteQNMSequence_quadratic_hankel_det_eq_zero {d : ℕ}
    (amplitude frequency : Fin d → ℂ) :
    (_root_.HTGeometry.algebraicHankelMatrix
      (fun n => finiteQNMSequence amplitude frequency n ^ 2) (d * d + 1)).det = 0 := by
  simpa [pow_two] using
    (_root_.HTGeometry.det_algebraicHankelMatrix_mul_eq_zero_of_finiteModalWidthAtMost
      (d := d) (e := d)
      (m₁ := finiteQNMSequence amplitude frequency)
      (m₂ := finiteQNMSequence amplitude frequency)
      ⟨amplitude, qnmSampleNode ∘ frequency, rfl⟩
      ⟨amplitude, qnmSampleNode ∘ frequency, rfl⟩)

/-- Finite Sobolev energy through derivative order `p`. -/
def finiteSobolevEnergy {X : Type*} [NormedAddCommGroup X]
    (D : ℕ → X → X) (p : ℕ) (u : X) : ℝ :=
  ∑ j ∈ Finset.range (p + 1), ‖D j u‖ ^ 2

theorem finiteSobolevEnergy_nonneg {X : Type*} [NormedAddCommGroup X]
    (D : ℕ → X → X) (p : ℕ) (u : X) :
    0 ≤ finiteSobolevEnergy D p u := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Raising Sobolev order adds exactly one nonnegative derivative energy. -/
theorem finiteSobolevEnergy_succ {X : Type*} [NormedAddCommGroup X]
    (D : ℕ → X → X) (p : ℕ) (u : X) :
    finiteSobolevEnergy D (p + 1) u =
      finiteSobolevEnergy D p u + ‖D (p + 1) u‖ ^ 2 := by
  simp [finiteSobolevEnergy, Finset.sum_range_succ]

theorem finiteSobolevEnergy_le_succ {X : Type*} [NormedAddCommGroup X]
    (D : ℕ → X → X) (p : ℕ) (u : X) :
    finiteSobolevEnergy D p u ≤ finiteSobolevEnergy D (p + 1) u := by
  rw [finiteSobolevEnergy_succ]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Strictly positive surface-gravity proxy, requiring no side hypothesis. -/
def positiveSurfaceGravity (kappa : ℝ) : ℝ := |kappa| + 1

theorem positiveSurfaceGravity_pos (kappa : ℝ) : 0 < positiveSurfaceGravity kappa := by
  unfold positiveSurfaceGravity
  linarith [abs_nonneg kappa]

/-- Explicit onset beyond the paper's inverse-surface-gravity threshold. -/
def guaranteedQNMOnsetTime (kappa delta : ℝ) : ℝ :=
  (delta ^ 2 + 2) / positiveSurfaceGravity kappa

/-- Exponential factor governing the modal tail at the guaranteed onset. -/
def qnmTruncationModeFactor (kappa delta : ℝ) (N : ℕ) : ℝ :=
  Real.exp ((1 - positiveSurfaceGravity kappa * guaranteedQNMOnsetTime kappa delta) * N)

theorem qnmTruncationModeFactor_eq (kappa delta : ℝ) (N : ℕ) :
    qnmTruncationModeFactor kappa delta N =
      Real.exp (-(delta ^ 2 + 1) * N) := by
  unfold qnmTruncationModeFactor guaranteedQNMOnsetTime
  have hk := ne_of_gt (positiveSurfaceGravity_pos kappa)
  congr 1
  field_simp
  ring

/-- Every positive-index tail factor is strictly below one. -/
theorem qnmTruncationModeFactor_succ_lt_one (kappa delta : ℝ) (N : ℕ) :
    qnmTruncationModeFactor kappa delta (N + 1) < 1 := by
  rw [qnmTruncationModeFactor_eq, Real.exp_lt_one_iff]
  have hpos : 0 < delta ^ 2 + 1 := by nlinarith [sq_nonneg delta]
  have hN : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hpos) hN

/-! ## Exact non-normal transient-growth witness -/

/-- Two-mode non-normal evolution step with strictly contractive modal multipliers. -/
def exactKeldyshTransientStep (u : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![(1 / 2 : ℂ) * u 0 - 2 * u 1, (1 / 4 : ℂ) * u 1]

/-- Fast right mode of the transient-growth witness. -/
def exactKeldyshTransientFastMode : Fin 2 → ℂ := ![1, 0]

/-- Slow right mode of the transient-growth witness. -/
def exactKeldyshTransientSlowMode : Fin 2 → ℂ := ![8, 1]

/-- Initial datum exhibiting one-step norm amplification. -/
def exactKeldyshTransientSeed : Fin 2 → ℂ := ![0, 1]

theorem exactKeldyshTransientStep_fastMode :
    exactKeldyshTransientStep exactKeldyshTransientFastMode =
      (1 / 2 : ℂ) • exactKeldyshTransientFastMode := by
  funext i
  fin_cases i <;>
    norm_num [exactKeldyshTransientStep, exactKeldyshTransientFastMode]

theorem exactKeldyshTransientStep_slowMode :
    exactKeldyshTransientStep exactKeldyshTransientSlowMode =
      (1 / 4 : ℂ) • exactKeldyshTransientSlowMode := by
  funext i
  fin_cases i <;>
    norm_num [exactKeldyshTransientStep, exactKeldyshTransientSlowMode]

theorem exactKeldyshTransientFastMultiplier_norm_lt_one :
    ‖(1 / 2 : ℂ)‖ < 1 := by
  norm_num [Complex.norm_real]

theorem exactKeldyshTransientSlowMultiplier_norm_lt_one :
    ‖(1 / 4 : ℂ)‖ < 1 := by
  norm_num [Complex.norm_real]

theorem exactKeldyshTransientSeed_norm : ‖exactKeldyshTransientSeed‖ = 1 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    fin_cases i <;> norm_num [exactKeldyshTransientSeed]
  · simpa [exactKeldyshTransientSeed] using
      norm_le_pi_norm exactKeldyshTransientSeed (1 : Fin 2)

theorem exactKeldyshTransientStep_seed_norm :
    ‖exactKeldyshTransientStep exactKeldyshTransientSeed‖ = 2 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    fin_cases i <;>
      norm_num [exactKeldyshTransientStep, exactKeldyshTransientSeed, Complex.norm_real]
  · simpa [exactKeldyshTransientStep, exactKeldyshTransientSeed, Complex.norm_real] using
      norm_le_pi_norm (exactKeldyshTransientStep exactKeldyshTransientSeed) (0 : Fin 2)

/-- Both modal multipliers are contractive, yet non-orthogonality doubles one datum's norm. -/
theorem exactKeldyshTransientGrowth :
    ‖exactKeldyshTransientSeed‖ <
      ‖exactKeldyshTransientStep exactKeldyshTransientSeed‖ := by
  rw [exactKeldyshTransientSeed_norm, exactKeldyshTransientStep_seed_norm]
  norm_num

end GaloisForLFunctions.HTGeometry
