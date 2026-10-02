import GaloisForLFunctions.RHTower.PrimeBurnolMixedReflectedCollision

/-!
# Complete mixed-prime theta cubic: principal collision coefficient

For every finite injective prime-depth packet and every real theta grade, the complete
literal reflected source cubic has second-order coefficient
`-Tr(G K^-1 (U-I/2) G V)`, with `G` the zero-clock Burnol Gram, `K` its radial-moment
Schur complement, and `U,V` the actual squared visibility and visibility-contrast matrices.
No cross-prime term or inverse-Gram coupling is omitted.

The proof establishes actual projection idempotence and local punctured invertibility,
uses the checked single-inverse cubic identity, and identifies the parity-coordinate
calculation with the original source by exact conjugation invariance.

This is a two-sided punctured principal-coefficient theorem. It supplies neither the
first-order counterterm nor a bounded renormalized remainder, cofinal operator control,
Gamma cancellation, or the source-to-Hardy index comparison required for RH.
-/

open Complex Matrix Filter Set Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

private def scaleBlock (N : ℕ) (z : ℂ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks 1 0 0 (z • (1 : Matrix (Fin N) (Fin N) ℂ))

private theorem continuous_scaleBlock (N : ℕ) : Continuous (scaleBlock N) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  rcases i with i | i <;> rcases j with j | j <;>
    dsimp [scaleBlock, Matrix.fromBlocks] <;> fun_prop

private theorem det_scaleBlock (N : ℕ) (z : ℂ) : (scaleBlock N z).det=z^N := by
  simp [scaleBlock, Matrix.det_fromBlocks_zero₂₁]

theorem continuous_primeBurnolReflectedParityGram {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) : Continuous (primeBurnolReflectedParityGram pe) := by
  change Continuous (fun k : ℝ => scaleBlock N (Complex.I*(k : ℂ)) *
    primeBurnolCollisionGram pe k * scaleBlock N (-Complex.I*(k : ℂ)))
  exact (((continuous_scaleBlock N).comp (by fun_prop)).mul
    (continuous_primeBurnolCollisionGram pe)).mul
    ((continuous_scaleBlock N).comp (by fun_prop))

theorem primeBurnolReflectedParityGram_zero {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) : primeBurnolReflectedParityGram pe 0 =
      Matrix.fromBlocks ((2 : ℂ) • primeBurnolMomentMatrix pe 0) 0 0 0 := by
  change scaleBlock N (Complex.I*(0 : ℂ)) * primeBurnolCollisionGram pe 0 *
    scaleBlock N (-Complex.I*(0 : ℂ)) = _
  rw [primeBurnolCollisionGram_zero]
  simp [scaleBlock, primeBurnolConfluentBlockGram, Matrix.fromBlocks_smul,
    Matrix.fromBlocks_multiply]

theorem eventually_primeBurnolReflectedParityGram_isUnit {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) :
    ∀ᶠ k : ℝ in 𝓝[≠] 0, IsUnit (primeBurnolReflectedParityGram pe k) := by
  have hdet := ((continuous_primeBurnolCollisionGram pe).matrix_det.continuousAt).eventually_ne
    (det_primeBurnolCollisionGram_zero_ne_zero pe)
  filter_upwards [hdet.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with k hJ hk
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  change (scaleBlock N (Complex.I*(k : ℂ)) * primeBurnolCollisionGram pe k *
    scaleBlock N (-Complex.I*(k : ℂ))).det ≠ 0
  rw [Matrix.det_mul, Matrix.det_mul, det_scaleBlock, det_scaleBlock]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero hkC)) hJ)
    (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hkC))

def primeBurnolThetaSquareMatrix {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => ((primeBurnolThetaVisibility a (pe i).1 : ℂ)^2))

def primeBurnolThetaMixedMatrix {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => (primeBurnolThetaVisibility a (pe i).1 : ℂ)*
    (primeBurnolThetaContrast a (pe i).1 : ℂ))

private def parityProjection (N : ℕ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  (2 : ℂ)⁻¹ • Matrix.fromBlocks 1 1 1 1

def primeBurnolParityThetaProjection {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks ((2 : ℂ)⁻¹ • 1 + primeBurnolThetaMixedMatrix pe a)
    (primeBurnolThetaSquareMatrix pe a - (2 : ℂ)⁻¹ • 1)
    (primeBurnolThetaSquareMatrix pe a - (2 : ℂ)⁻¹ • 1)
    ((2 : ℂ)⁻¹ • 1 - primeBurnolThetaMixedMatrix pe a)

private theorem parityProjection_idempotent (N : ℕ) :
    parityProjection N * parityProjection N=parityProjection N := by
  simp [parityProjection, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul, smul_smul, ← two_smul ℂ]

private theorem theta_uv (a : ℝ) (p : Nat.Primes) :
    ((primeBurnolThetaVisibility a p : ℂ)^2)^2 +
      ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ))^2 =
      (primeBurnolThetaVisibility a p : ℂ)^2 := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (primeBurnolThetaVisibility_sq_add_contrast_sq a p)
  push_cast at h
  linear_combination (primeBurnolThetaVisibility a p : ℂ)^2*h

theorem primeBurnolParityThetaProjection_idempotent {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) :
    primeBurnolParityThetaProjection pe a * primeBurnolParityThetaProjection pe a =
      primeBurnolParityThetaProjection pe a := by
  rw [primeBurnolParityThetaProjection, Matrix.fromBlocks_multiply]
  simp only [primeBurnolThetaSquareMatrix, primeBurnolThetaMixedMatrix,
    ← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_add,
    Matrix.diagonal_sub, Matrix.diagonal_mul_diagonal]
  all_goals
    congr 1
  all_goals
    congr 1
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    ring_nf
  all_goals linear_combination theta_uv a (pe i).1

private theorem trace_blocks {N : ℕ} (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

/-- Full mixed-prime cubic counterterm, with the genuine radial Schur inverse. -/
def primeBurnolMixedCubicPrincipalCoefficient {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) : ℂ :=
  -Matrix.trace (primeBurnolMomentMatrix pe 0 * (primeBurnolRadialSchurComplement pe)⁻¹ *
    (primeBurnolThetaSquareMatrix pe a - (2 : ℂ)⁻¹ • 1) *
    primeBurnolMomentMatrix pe 0 * primeBurnolThetaMixedMatrix pe a)

/-- The actual source cubic in parity coordinates. -/
def primeBurnolParityThetaCubicTrace {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (a k : ℝ) : ℂ :=
  let c := primeBurnolReflectedParityGram pe k
  let q := primeBurnolParityThetaProjection pe a
  Matrix.trace (c * cubicProjectionAssociatorAlgebra (c⁻¹*q*c) q (parityProjection N))

private theorem collision_cubic_block_limit {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) (a : ℝ) :
    Matrix.trace (primeBurnolReflectedParityGram pe 0 * parityProjection N *
      primeBurnolCollisionInverseResidue pe * primeBurnolParityThetaProjection pe a *
      primeBurnolReflectedParityGram pe 0 *
      (parityProjection N-primeBurnolParityThetaProjection pe a)) =
        primeBurnolMixedCubicPrincipalCoefficient pe a := by
  rw [primeBurnolReflectedParityGram_zero, primeBurnolCollisionInverseResidue_eq_schur]
  unfold parityProjection primeBurnolParityThetaProjection
  simp only [sub_eq_add_neg, Matrix.fromBlocks_smul, Matrix.fromBlocks_neg,
    Matrix.fromBlocks_add, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.mul_one, zero_add, add_zero,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [trace_blocks]
  unfold primeBurnolMixedCubicPrincipalCoefficient
  rw [← Matrix.trace_neg]
  norm_num
  simp only [sub_eq_add_neg]

private theorem matrix_cubic_single_inverse_of_isUnit {n : Type*} [Fintype n] [DecidableEq n]
    (c p q : Matrix n n ℂ) (hc : IsUnit c) (hp : p*p=p) (hq : q*q=q) :
    Matrix.trace (c*cubicProjectionAssociatorAlgebra (c⁻¹*q*c) q p) =
      Matrix.trace (c*p*c⁻¹*q*c*(p-q)) + Matrix.trace (c*(q*p*q-p*q*p)) := by
  rcases hc with ⟨c,rfl⟩
  have h := matrixTrace_weighted_cubic_single_inverse c p q hp hq
  change Matrix.trace ((c : Matrix n n ℂ)*cubicProjectionAssociatorAlgebra
    ((↑c⁻¹ : Matrix n n ℂ)*q*(c : Matrix n n ℂ)) q p) = _ at h
  simpa only [Matrix.coe_units_inv] using h

theorem primeBurnolParityThetaCubicTrace_principal {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) (a : ℝ) :
    Tendsto (fun k : ℝ => (k : ℂ)^2 * primeBurnolParityThetaCubicTrace pe a k)
      (𝓝[≠] 0) (𝓝 (primeBurnolMixedCubicPrincipalCoefficient pe a)) := by
  let p := parityProjection N
  let q := primeBurnolParityThetaProjection pe a
  let c := primeBurnolReflectedParityGram pe
  have hc : Tendsto c (𝓝[≠] (0 : ℝ)) (𝓝 (c 0)) :=
    (continuous_primeBurnolReflectedParityGram pe).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hi := primeBurnolReflectedParityGram_inverse_principal pe
  have hs : Tendsto (fun k : ℝ => (k : ℂ)^2) (𝓝[≠] 0) (𝓝 (0 : ℂ)) := by
    have h : Continuous (fun k : ℝ => (k : ℂ)^2) := by fun_prop
    simpa using (h.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hmatrix := (((((hc.mul (tendsto_const_nhds (x := p))).mul hi).mul
    (tendsto_const_nhds (x := q))).mul hc).mul (tendsto_const_nhds (x := p-q)))
  have htrace : Tendsto
      (fun k : ℝ => Matrix.trace (c k*p*((k : ℂ)^2 • (c k)⁻¹)*q*c k*(p-q)))
      (𝓝[≠] 0)
      (𝓝 (Matrix.trace (c 0*p*primeBurnolCollisionInverseResidue pe*q*c 0*(p-q)))) :=
    (continuous_id.matrix_trace.tendsto _).comp hmatrix
  have hpoly : Tendsto (fun k : ℝ => Matrix.trace (c k*(q*p*q-p*q*p)))
      (𝓝[≠] 0) (𝓝 (Matrix.trace (c 0*(q*p*q-p*q*p)))) :=
    (continuous_id.matrix_trace.tendsto _).comp (hc.mul tendsto_const_nhds)
  have ht := htrace.add (hs.mul hpoly)
  simp only [zero_mul, add_zero] at ht
  have hlim := collision_cubic_block_limit pe a
  change Matrix.trace (c 0*p*primeBurnolCollisionInverseResidue pe*q*c 0*(p-q)) = _ at hlim
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [eventually_primeBurnolReflectedParityGram_isUnit pe] with k hunit
  change _ = (k : ℂ)^2 * Matrix.trace (c k*cubicProjectionAssociatorAlgebra ((c k)⁻¹*q*c k) q p)
  rw [matrix_cubic_single_inverse_of_isUnit (c k) p q hunit
    (parityProjection_idempotent N) (primeBurnolParityThetaProjection_idempotent pe a)]
  simp [Matrix.trace_smul, mul_add]

private theorem collisionHadamard_square (N : ℕ) :
    primeBurnolCollisionHadamard N * primeBurnolCollisionHadamard N = (2 : ℂ) • 1 := by
  rw [← Matrix.fromBlocks_one (l := Fin N) (m := Fin N)]
  simp [primeBurnolCollisionHadamard, Matrix.fromBlocks_multiply,
    ← two_smul ℂ]
  conv_rhs => rw [← Matrix.fromBlocks_one (l := Fin N) (m := Fin N)]
  simp only [Matrix.fromBlocks_smul, smul_zero]

private def collisionHadamardUnit (N : ℕ) :
    (Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ)ˣ where
  val := primeBurnolCollisionHadamard N
  inv := (2 : ℂ)⁻¹ • primeBurnolCollisionHadamard N
  val_inv := by rw [Matrix.mul_smul, collisionHadamard_square, smul_smul]; norm_num
  inv_val := by rw [Matrix.smul_mul, collisionHadamard_square, smul_smul]; norm_num

private def reflectedNeutralProjection (N : ℕ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks 1 0 0 0

/-- Actual theta projection in the two original reflected clock sectors. -/
def primeBurnolReflectedThetaProjection {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks (primeBurnolThetaSquareMatrix pe a) (primeBurnolThetaMixedMatrix pe a)
    (primeBurnolThetaMixedMatrix pe a) (1-primeBurnolThetaSquareMatrix pe a)

private theorem parityGram_conjugation {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (k : ℝ) :
    sourceModularAutomorphism (collisionHadamardUnit N) (primeBurnolReflectedMixedGram pe k) =
      primeBurnolReflectedParityGram pe k := by
  rw [primeBurnolReflectedParityGram_eq_source]
  change ((2 : ℂ)⁻¹ • primeBurnolCollisionHadamard N)*primeBurnolReflectedMixedGram pe k*
    primeBurnolCollisionHadamard N = _
  simp only [Matrix.smul_mul]

private theorem parityNeutral_conjugation (N : ℕ) :
    sourceModularAutomorphism (collisionHadamardUnit N) (reflectedNeutralProjection N) =
      parityProjection N := by
  change ((2 : ℂ)⁻¹ • primeBurnolCollisionHadamard N)*reflectedNeutralProjection N*
    primeBurnolCollisionHadamard N = _
  simp [primeBurnolCollisionHadamard, reflectedNeutralProjection, parityProjection,
    Matrix.fromBlocks_multiply]

private theorem parityTheta_conjugation {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) :
    sourceModularAutomorphism (collisionHadamardUnit N) (primeBurnolReflectedThetaProjection pe a) =
      primeBurnolParityThetaProjection pe a := by
  change ((2 : ℂ)⁻¹ • primeBurnolCollisionHadamard N)*primeBurnolReflectedThetaProjection pe a*
    primeBurnolCollisionHadamard N = _
  simp only [primeBurnolCollisionHadamard, primeBurnolReflectedThetaProjection,
    primeBurnolParityThetaProjection, Matrix.smul_mul, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg]
  ext (i | i) (j | j) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
      smul_eq_mul, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply] <;> ring

private theorem trace_cubic_conjugation {n : Type*} [Fintype n] [DecidableEq n]
    (u : (Matrix n n ℂ)ˣ) (c p q : Matrix n n ℂ) :
    let s := sourceModularAutomorphism u
    Matrix.trace (s c*cubicProjectionAssociatorAlgebra ((s c)⁻¹*s q*s c) (s q) (s p)) =
      Matrix.trace (c*cubicProjectionAssociatorAlgebra (c⁻¹*q*c) q p) := by
  let s := sourceModularAutomorphism u
  have hinv : (s c)⁻¹=s (c⁻¹) := by
    change ((↑u⁻¹ : Matrix n n ℂ)*c*(u : Matrix n n ℂ))⁻¹ =
      (↑u⁻¹ : Matrix n n ℂ)*c⁻¹*(u : Matrix n n ℂ)
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [← Matrix.coe_units_inv, inv_inv, Matrix.mul_assoc]
  change Matrix.trace (s c*cubicProjectionAssociatorAlgebra ((s c)⁻¹*s q*s c) (s q) (s p)) = _
  calc
    _ = Matrix.trace (s (c*cubicProjectionAssociatorAlgebra (c⁻¹*q*c) q p)) := by
      rw [hinv]
      simp only [cubicProjectionAssociatorAlgebra, map_mul, map_sub, map_pow]
    _ = _ := Matrix.trace_units_conj' u _

/-- Complete literal reflected source cubic, before passing to parity coordinates. -/
def primeBurnolMixedReflectedThetaCubicTrace {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (a k : ℝ) : ℂ :=
  let c := primeBurnolReflectedMixedGram pe k
  let q := primeBurnolReflectedThetaProjection pe a
  Matrix.trace (c*cubicProjectionAssociatorAlgebra (c⁻¹*q*c) q (reflectedNeutralProjection N))

theorem primeBurnolParityThetaCubicTrace_eq_source {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (a k : ℝ) :
    primeBurnolParityThetaCubicTrace pe a k = primeBurnolMixedReflectedThetaCubicTrace pe a k := by
  unfold primeBurnolParityThetaCubicTrace primeBurnolMixedReflectedThetaCubicTrace
  rw [← parityGram_conjugation, ← parityTheta_conjugation, ← parityNeutral_conjugation]
  exact trace_cubic_conjugation (collisionHadamardUnit N) _ _ _

theorem primeBurnolMixedReflectedThetaCubicTrace_principal {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) (a : ℝ) :
    Tendsto (fun k : ℝ => (k : ℂ)^2 * primeBurnolMixedReflectedThetaCubicTrace pe a k)
      (𝓝[≠] 0) (𝓝 (primeBurnolMixedCubicPrincipalCoefficient pe a)) := by
  apply (primeBurnolParityThetaCubicTrace_principal pe a).congr'
  exact Filter.Eventually.of_forall fun k => by simp only [primeBurnolParityThetaCubicTrace_eq_source]

end
end RHTower
