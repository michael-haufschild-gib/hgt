import GaloisForLFunctions.RHTower.PrimeBurnolConfluentMomentGram
import GaloisForLFunctions.RHTower.PrimeBurnolThetaCubicTraceCancellation
import Mathlib.Topology.Instances.Matrix

/-!
# Full mixed-prime reflected Burnol collision

The literal reflected L2 Gram is conjugated into its even/odd basis and factored through a
continuous rational matrix. At zero clock separation that matrix is twice the confluent moment
Gram. Consequently the second-order inverse pole is exactly the odd-sector embedding of half
the inverse radial Schur complement. Every mixed-prime coefficient is retained.

A cubic trace reduction to one inverse is also proved for subsequent counterterm extraction.
The complete mixed cubic coefficient, its Gamma cancellation, a uniform residual estimate, and
the arithmetic-to-Hardy index comparison are not consequences claimed here.
-/

open Complex Matrix Set MeasureTheory Polynomial
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

theorem matrixTrace_weighted_cubic_single_inverse
    {n : Type*} [Fintype n] [DecidableEq n]
    (c : (Matrix n n ℂ)ˣ) (p q : Matrix n n ℂ)
    (hp : p*p=p) (hq : q*q=q) :
    Matrix.trace ((c : Matrix n n ℂ)*cubicProjectionAssociatorAlgebra
      (sourceModularAutomorphism c q) q p) =
      Matrix.trace ((c : Matrix n n ℂ)*p*(↑c⁻¹ : Matrix n n ℂ)*q*(c : Matrix n n ℂ)*(p-q)) +
      Matrix.trace ((c : Matrix n n ℂ)*(q*p*q-p*q*p)) := by
  let r := sourceModularAutomorphism c q
  have hr : r*r=r := sourceModularAutomorphism_idempotent c q hq
  have hd (x y : Matrix n n ℂ) (hx : x*x=x) (hy : y*y=y) :
      (x-y)^3=x-y-x*y*x+y*x*y := by noncomm_ring [hx,hy]
  have hcr : (c : Matrix n n ℂ)*r=q*c := by
    simp [r, sourceModularAutomorphism, ← mul_assoc]
  have hdisp : Matrix.trace ((c : Matrix n n ℂ)*(r-q)^3)=0 := by
    rw [weighted_modular_projection_cube_commutator c q hq, modularCommutator,
      Matrix.trace_sub, Matrix.trace_mul_comm]
    simp
  have htr : Matrix.trace ((c : Matrix n n ℂ)*r)=Matrix.trace ((c : Matrix n n ℂ)*q) := by
    rw [hcr, Matrix.trace_mul_comm]
  have hfirst : Matrix.trace ((c : Matrix n n ℂ)*(r*p*r)) =
      Matrix.trace ((c : Matrix n n ℂ)*p*(↑c⁻¹ : Matrix n n ℂ)*q*(c : Matrix n n ℂ)*q) := by
    calc
      Matrix.trace ((c : Matrix n n ℂ)*(r*p*r)) =
          Matrix.trace (q*((c : Matrix n n ℂ)*p*(↑c⁻¹ : Matrix n n ℂ)*q*(c : Matrix n n ℂ))) := by
            congr 1
            simp [r, sourceModularAutomorphism, ← mul_assoc]
      _ = _ := Matrix.trace_mul_comm _ _
  have hsecond : (c : Matrix n n ℂ)*(p*r*p) =
      (c : Matrix n n ℂ)*p*(↑c⁻¹ : Matrix n n ℂ)*q*(c : Matrix n n ℂ)*p := by
    simp [r, sourceModularAutomorphism, mul_assoc]
  change Matrix.trace ((c : Matrix n n ℂ)*cubicProjectionAssociatorAlgebra r q p)=_
  rw [cubicProjectionAssociatorAlgebra, mul_sub, mul_sub,
    Matrix.trace_sub, Matrix.trace_sub, hdisp, sub_zero, hd r p hr hp, hd q p hq hp]
  simp only [mul_add, mul_sub, Matrix.trace_add, Matrix.trace_sub, htr, hfirst, hsecond]
  abel

end GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section
open Filter Topology

private def collisionRate (u v : Nat.Primes × ℕ) : ℝ :=
  primeBurnolLogFrequency u + primeBurnolLogFrequency v

private theorem collisionRate_pos (u v : Nat.Primes × ℕ) : 0 < collisionRate u v :=
  add_pos (primeBurnolLogFrequency_pos u) (primeBurnolLogFrequency_pos v)

private def collisionEven (u v : Nat.Primes × ℕ) (k : ℝ) : ℂ :=
  let s := collisionRate u v
  primeBurnolAmplitude u * primeBurnolAmplitude v *
    ((2/s^3 + 2*s*(s^2-12*k^2)/(s^2+4*k^2)^3 : ℝ) : ℂ)

private def collisionCross (u v : Nat.Primes × ℕ) (k : ℝ) : ℂ :=
  let s := collisionRate u v
  primeBurnolAmplitude u * primeBurnolAmplitude v *
    ((4*(3*s^2-4*k^2)/(s^2+4*k^2)^3 : ℝ) : ℂ)

private def collisionOdd (u v : Nat.Primes × ℕ) (k : ℝ) : ℂ :=
  let s := collisionRate u v
  primeBurnolAmplitude u * primeBurnolAmplitude v *
    ((2*(24*s^4+48*s^2*k^2+64*k^4)/(s^3*(s^2+4*k^2)^3) : ℝ) : ℂ)

/-- Desingularized full mixed-prime reflected Gram, in even/odd coordinates. -/
def primeBurnolCollisionGram {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (k : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks (fun i j => collisionEven (pe i) (pe j) k)
    (fun i j => collisionCross (pe i) (pe j) k)
    (fun i j => collisionCross (pe i) (pe j) k)
    (fun i j => collisionOdd (pe i) (pe j) k)

theorem primeBurnolCollisionGram_zero {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    primeBurnolCollisionGram pe 0 = (2 : ℂ) • primeBurnolConfluentBlockGram pe := by
  ext (i | i) (j | j) <;>
    simp only [primeBurnolCollisionGram, primeBurnolConfluentBlockGram,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.smul_apply, smul_eq_mul]
  all_goals
    have hs : (collisionRate (pe i) (pe j) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (collisionRate_pos _ _).ne'
    simp only [collisionEven, collisionCross, collisionOdd, primeBurnolMomentMatrix,
      collisionRate] at hs ⊢
    push_cast
    norm_num
    field_simp <;> ring

theorem continuous_primeBurnolCollisionGram {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    Continuous (primeBurnolCollisionGram pe) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    have hs := collisionRate_pos (pe i) (pe j)
    dsimp [primeBurnolCollisionGram, collisionEven, collisionCross, collisionOdd,
      Matrix.fromBlocks]
    fun_prop (disch := intros; positivity)

theorem det_primeBurnolCollisionGram_zero_ne_zero {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) : (primeBurnolCollisionGram pe 0).det ≠ 0 := by
  rw [primeBurnolCollisionGram_zero, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (det_primeBurnolConfluentBlockGram_ne_zero pe)

theorem continuousAt_primeBurnolCollisionGram_inverse {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) :
    ContinuousAt (fun k : ℝ => (primeBurnolCollisionGram pe k)⁻¹) 0 := by
  apply (continuousAt_matrix_inv (primeBurnolCollisionGram pe 0) ?_).comp
    (continuous_primeBurnolCollisionGram pe).continuousAt
  simpa only [Ring.inverse_eq_inv'] using
    (continuousAt_inv₀ (det_primeBurnolCollisionGram_zero_ne_zero pe))

private theorem collision_pair_split (u v : Nat.Primes × ℕ) (k : ℝ) :
    primeBurnolAmplitude u * primeBurnolAmplitude v *
      (2 / primeBurnolPairRate u v k (-k)^3) =
    (collisionEven u v k -
        primeBurnolAmplitude u * primeBurnolAmplitude v *
          ((2 / collisionRate u v^3 : ℝ) : ℂ)) +
      Complex.I * (k : ℂ) * collisionCross u v k := by
  have hs := collisionRate_pos u v
  have hd : collisionRate u v^2+4*k^2 ≠ 0 := by positivity
  have hdC : ((collisionRate u v^2+4*k^2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hd
  have hm : ((collisionRate u v : ℂ)-2*Complex.I*(k : ℂ)) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    exact hs.ne' h'
  have hfac : ((collisionRate u v : ℂ)-2*Complex.I*(k : ℂ)) *
      ((collisionRate u v : ℂ)+2*Complex.I*(k : ℂ)) =
      ((collisionRate u v^2+4*k^2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have hr : (2 : ℂ) / ((collisionRate u v : ℂ)-2*Complex.I*(k : ℂ))^3 =
      2*((collisionRate u v : ℂ)+2*Complex.I*(k : ℂ))^3 /
        ((collisionRate u v^2+4*k^2 : ℝ) : ℂ)^3 := by
    apply (div_eq_div_iff (pow_ne_zero _ hm) (pow_ne_zero _ hdC)).2
    rw [← hfac, mul_pow]
    ring
  have hrate : primeBurnolPairRate u v k (-k) =
      ((collisionRate u v : ℂ)-2*Complex.I*(k : ℂ)) := by
    unfold primeBurnolPairRate collisionRate
    push_cast
    ring
  rw [hrate, hr]
  dsimp [collisionEven, collisionCross]
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem collision_odd_identity (u v : Nat.Primes × ℕ) (k : ℝ) :
    2*(primeBurnolAmplitude u * primeBurnolAmplitude v *
      ((2 / collisionRate u v^3 : ℝ) : ℂ)) - collisionEven u v k =
      (k : ℂ)^2 * collisionOdd u v k := by
  have hs := collisionRate_pos u v
  have hden : collisionRate u v^2+4*k^2 ≠ 0 := by positivity
  have hscalar : 2*(2 / collisionRate u v^3) -
      (2 / collisionRate u v^3 + 2*collisionRate u v*(collisionRate u v^2-12*k^2) /
        (collisionRate u v^2+4*k^2)^3) =
      k^2 * (2*(24*collisionRate u v^4+48*collisionRate u v^2*k^2+64*k^4) /
        (collisionRate u v^3*(collisionRate u v^2+4*k^2)^3)) := by
    field_simp
    ring
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hscalar
  push_cast at hc
  dsimp [collisionEven, collisionOdd]
  push_cast
  linear_combination primeBurnolAmplitude u * primeBurnolAmplitude v * hc

def primeBurnolReflectedMixedGram {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (k : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.gram ℂ (Sum.elim (fun i => primeBurnolWindowFeatureLp (pe i) k)
    (fun i => primeBurnolWindowFeatureLp (pe i) (-k)))

def primeBurnolCollisionHadamard (N : ℕ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks 1 1 1 (-1)

private def collisionScale (N : ℕ) (k : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks 1 0 0 ((Complex.I*(k : ℂ)) • 1)

private def collisionScaleStar (N : ℕ) (k : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks 1 0 0 ((-Complex.I*(k : ℂ)) • 1)

/-- The parity-coordinate Gram, retaining every mixed-prime coefficient. -/
def primeBurnolReflectedParityGram {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (k : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  collisionScale N k * primeBurnolCollisionGram pe k * collisionScaleStar N k

theorem primeBurnolReflectedParityGram_eq_source {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (k : ℝ) :
    primeBurnolReflectedParityGram pe k = (2 : ℂ)⁻¹ •
      (primeBurnolCollisionHadamard N * primeBurnolReflectedMixedGram pe k * primeBurnolCollisionHadamard N) := by
  let G := primeBurnolMomentMatrix pe 0
  let E : Matrix (Fin N) (Fin N) ℂ := fun i j => collisionEven (pe i) (pe j) k
  let B : Matrix (Fin N) (Fin N) ℂ := fun i j => collisionCross (pe i) (pe j) k
  let D : Matrix (Fin N) (Fin N) ℂ := fun i j => collisionOdd (pe i) (pe j) k
  have hbase (i j : Fin N) : G i j = primeBurnolAmplitude (pe i) *
      primeBurnolAmplitude (pe j) * ((2 / collisionRate (pe i) (pe j)^3 : ℝ) : ℂ) := by
    simp [G, primeBurnolMomentMatrix, collisionRate]
  have hraw : primeBurnolReflectedMixedGram pe k = Matrix.fromBlocks G
      (E-G+(Complex.I*(k : ℂ)) • B) (E-G-(Complex.I*(k : ℂ)) • B) G := by
    ext (i | i) (j | j)
    all_goals
      simp only [primeBurnolReflectedMixedGram, Matrix.gram_apply, Sum.elim_inl,
        Sum.elim_inr, inner_primeBurnolWindowFeatureLp_eq,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    · simp [G, primeBurnolMomentMatrix, primeBurnolPairRate]
    · simpa only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        E, B, hbase] using collision_pair_split (pe i) (pe j) k
    · have h := collision_pair_split (pe i) (pe j) (-k)
      simpa [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, E, B, hbase,
        collisionEven, collisionCross, sub_eq_add_neg] using h
    · simp [G, primeBurnolMomentMatrix, primeBurnolPairRate]
  have hodd (i j : Fin N) : 2*G i j-E i j=(k : ℂ)^2*D i j := by
    rw [hbase]
    exact collision_odd_identity (pe i) (pe j) k
  change collisionScale N k * Matrix.fromBlocks E B B D * collisionScaleStar N k = _
  rw [hraw]
  simp only [collisionScale, collisionScaleStar, primeBurnolCollisionHadamard,
    Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_neg, Matrix.neg_mul]
  ext (i | i) (j | j) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
  · ring
  · ring
  · ring
  · rw [show -Complex.I*(k : ℂ)*(Complex.I*(k : ℂ))=(k : ℂ)^2 by
      calc _ = -(Complex.I^2)*(k : ℂ)^2 := by ring
           _ = _ := by rw [Complex.I_sq]; ring]
    linear_combination -(hodd i j)

private theorem collision_scalar_block_inv (N : ℕ) (w : ℂ) (hw : w ≠ 0) :
    (Matrix.fromBlocks (1 : Matrix (Fin N) (Fin N) ℂ) 0 0
      (w • (1 : Matrix (Fin N) (Fin N) ℂ)))⁻¹ =
      Matrix.fromBlocks 1 0 0 (w⁻¹ • 1) := by
  apply Matrix.inv_eq_right_inv
  simp [Matrix.fromBlocks_multiply, smul_smul, hw, Matrix.fromBlocks_one]

private def collisionRescaledLeft (N : ℕ) (k : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks ((k : ℂ) • 1) 0 0 (Complex.I • 1)

private def collisionRescaledRight (N : ℕ) (k : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks ((k : ℂ) • 1) 0 0 (-Complex.I • 1)

private theorem collision_rescaled_inverse {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) {k : ℝ} (hk : k ≠ 0) :
    (k : ℂ)^2 • (primeBurnolReflectedParityGram pe k)⁻¹ =
      collisionRescaledLeft N k * (primeBurnolCollisionGram pe k)⁻¹ *
        collisionRescaledRight N k := by
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have hl : (k : ℂ) • (collisionScaleStar N k)⁻¹ = collisionRescaledLeft N k := by
    rw [collisionScaleStar, collision_scalar_block_inv N _ (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hkC)]
    simp [Matrix.fromBlocks_smul, smul_smul, collisionRescaledLeft, _root_.mul_inv_rev, hkC]
  have hr : (k : ℂ) • (collisionScale N k)⁻¹ = collisionRescaledRight N k := by
    rw [collisionScale, collision_scalar_block_inv N _ (mul_ne_zero Complex.I_ne_zero hkC)]
    simp [Matrix.fromBlocks_smul, smul_smul, collisionRescaledRight, _root_.mul_inv_rev, hkC]
  rw [primeBurnolReflectedParityGram, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← hl, ← hr]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two, Matrix.mul_assoc]

/-- Full mixed-prime coefficient of the second-order inverse pole. -/
def primeBurnolCollisionInverseResidue {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks 0 0 0 ((primeBurnolCollisionGram pe 0)⁻¹.toBlocks₂₂)

theorem primeBurnolReflectedParityGram_inverse_principal {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) :
    Tendsto (fun k : ℝ => (k : ℂ)^2 • (primeBurnolReflectedParityGram pe k)⁻¹)
      (𝓝[≠] 0) (𝓝 (primeBurnolCollisionInverseResidue pe)) := by
  have hl : Continuous (collisionRescaledLeft N) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    rcases i with i | i <;> rcases j with j | j <;>
      dsimp [collisionRescaledLeft, Matrix.fromBlocks] <;> fun_prop
  have hr : Continuous (collisionRescaledRight N) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    rcases i with i | i <;> rcases j with j | j <;>
      dsimp [collisionRescaledRight, Matrix.fromBlocks] <;> fun_prop
  have ht := (hl.continuousAt.mul (continuousAt_primeBurnolCollisionGram_inverse pe)).mul hr.continuousAt
  have hz : collisionRescaledLeft N 0 * (primeBurnolCollisionGram pe 0)⁻¹ *
      collisionRescaledRight N 0 = primeBurnolCollisionInverseResidue pe := by
    conv_lhs => arg 1; arg 2; rw [← Matrix.fromBlocks_toBlocks (primeBurnolCollisionGram pe 0)⁻¹]
    simp [collisionRescaledLeft, collisionRescaledRight, primeBurnolCollisionInverseResidue,
      Matrix.fromBlocks_multiply, smul_smul]
  have ht' := ht.tendsto
  simp only [Pi.mul_apply] at ht'
  rw [hz] at ht'
  apply (ht'.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with k hk
  exact (collision_rescaled_inverse pe hk).symm

theorem primeBurnolCollisionInverseResidue_eq_schur {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) :
    primeBurnolCollisionInverseResidue pe =
      Matrix.fromBlocks 0 0 0 ((2 : ℂ)⁻¹ • (primeBurnolRadialSchurComplement pe)⁻¹) := by
  letI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  rw [primeBurnolCollisionInverseResidue, primeBurnolCollisionGram_zero]
  rw [Matrix.inv_smul _ (2 : ℂ) (isUnit_iff_ne_zero.mpr
    (det_primeBurnolConfluentBlockGram_ne_zero pe))]
  rw [primeBurnolRadialSchurComplement_inverse]
  simp only [Matrix.toBlocks₂₂, invOf_eq_inv]
  rfl

end
end RHTower
