import GaloisForLFunctions.RHTower.PrimeBurnolMixedCubicPrincipal
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Full mixed reflected Burnol cubic: first-order Laurent coefficient

The literal desingularized collision Gram is a rational function of the squared clock.
Its derivative and inverse derivative vanish at collision. Entrywise matrix calculus then
identifies the first derivatives of the actual parity Gram and its regularized inverse.

The actual reflected source cubic has the checked second-order coefficient L2 and the
explicit full-matrix first-order coefficient L1 defined below:
`k * (tau(k) - L2/k^2) -> L1` on the two-sided punctured real clock limit.
The coefficient retains every cross-prime term and the complete confluent inverse.

This proves a two-term Laurent asymptotic. It does not assert a bounded finite part,
cofinal cancellation with Gamma, a Hardy-index transfer, or an RH conclusion.
-/

open Complex Matrix Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

private theorem square_comp_zero_derivative (F : ℝ → ℂ) (hF : DifferentiableAt ℝ F 0) :
    HasDerivAt (fun k : ℝ => F (k^2)) 0 0 := by
  have hs : HasDerivAt (fun k : ℝ => k^2) 0 0 := by
    simpa using! (hasDerivAt_id (0 : ℝ)).pow 2
  simpa [Function.comp_def] using hF.hasDerivAt.scomp_of_eq 0 hs (by norm_num)

private def squareEven (u v : Nat.Primes × ℕ) (t : ℝ) : ℂ :=
  let s := primeBurnolLogFrequency u + primeBurnolLogFrequency v
  primeBurnolAmplitude u * primeBurnolAmplitude v *
    ((2/s^3 + 2*s*(s^2-12*t)/(s^2+4*t)^3 : ℝ) : ℂ)

private def squareCross (u v : Nat.Primes × ℕ) (t : ℝ) : ℂ :=
  let s := primeBurnolLogFrequency u + primeBurnolLogFrequency v
  primeBurnolAmplitude u * primeBurnolAmplitude v *
    ((4*(3*s^2-4*t)/(s^2+4*t)^3 : ℝ) : ℂ)

private def squareOdd (u v : Nat.Primes × ℕ) (t : ℝ) : ℂ :=
  let s := primeBurnolLogFrequency u + primeBurnolLogFrequency v
  primeBurnolAmplitude u * primeBurnolAmplitude v *
    ((2*(24*s^4+48*s^2*t+64*t^2)/(s^3*(s^2+4*t)^3) : ℝ) : ℂ)

private def squareGram {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (t : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks (fun i j => squareEven (pe i) (pe j) t)
    (fun i j => squareCross (pe i) (pe j) t)
    (fun i j => squareCross (pe i) (pe j) t)
    (fun i j => squareOdd (pe i) (pe j) t)

private theorem collision_eq_squareGram {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (k : ℝ) :
    primeBurnolCollisionGram pe k = squareGram pe (k^2) := by
  ext (i|i) (j|j)
  · rfl
  · rfl
  · rfl
  · change _ = primeBurnolAmplitude (pe i)*primeBurnolAmplitude (pe j)*
      (((2*(24*(primeBurnolLogFrequency (pe i)+primeBurnolLogFrequency (pe j))^4+
        48*(primeBurnolLogFrequency (pe i)+primeBurnolLogFrequency (pe j))^2*k^2+
        64*(k^2)^2)/((primeBurnolLogFrequency (pe i)+primeBurnolLogFrequency (pe j))^3*
        ((primeBurnolLogFrequency (pe i)+primeBurnolLogFrequency (pe j))^2+4*k^2)^3)) : ℝ) : ℂ)
    rw [← pow_mul]
    rfl

private theorem differentiableAt_squareGram_entry {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (i j : Fin N ⊕ Fin N) :
    DifferentiableAt ℝ (fun t => squareGram pe t i j) 0 := by
  rcases i with i|i <;> rcases j with j|j
  all_goals
    have hs : 0 < primeBurnolLogFrequency (pe i)+primeBurnolLogFrequency (pe j) :=
      add_pos (primeBurnolLogFrequency_pos _) (primeBurnolLogFrequency_pos _)
    dsimp [squareGram, Matrix.fromBlocks, squareEven, squareCross, squareOdd]
    fun_prop (disch := intros; positivity)

theorem hasDerivAt_primeBurnolCollisionGram_zero {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) : HasDerivAt (primeBurnolCollisionGram pe) 0 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  simp_rw [collision_eq_squareGram]
  exact square_comp_zero_derivative _ (differentiableAt_squareGram_entry pe i j)

private theorem differentiableAt_matrix_det {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℂ) (hA : ∀ i j, DifferentiableAt ℝ (fun t => A t i j) 0) :
    DifferentiableAt ℝ (fun t => (A t).det) 0 := by
  simp only [Matrix.det_apply']
  fun_prop

private theorem differentiableAt_matrix_inv_entry {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℂ) (hA : ∀ i j, DifferentiableAt ℝ (fun t => A t i j) 0)
    (hdet : (A 0).det ≠ 0) (i j : n) :
    DifferentiableAt ℝ (fun t => (A t)⁻¹ i j) 0 := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  apply DifferentiableAt.mul
  · exact (differentiableAt_matrix_det A hA).inv hdet
  · simp only [Matrix.adjugate_apply]
    apply differentiableAt_matrix_det
    intro a b
    by_cases h : a=j
    · subst a
      simp only [Matrix.updateRow_self]
      fun_prop
    · simp only [Matrix.updateRow_ne h]
      exact hA a b

theorem hasDerivAt_primeBurnolCollisionGram_inverse_zero {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) :
    HasDerivAt (fun k : ℝ => (primeBurnolCollisionGram pe k)⁻¹) 0 0 := by
  have hz : squareGram pe 0 = primeBurnolCollisionGram pe 0 := by
    simpa using (collision_eq_squareGram pe 0).symm
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  simp_rw [collision_eq_squareGram]
  refine square_comp_zero_derivative (fun t => (squareGram pe t)⁻¹ i j) ?_
  apply differentiableAt_matrix_inv_entry _ (differentiableAt_squareGram_entry pe)
  rw [hz]
  exact det_primeBurnolCollisionGram_zero_ne_zero pe

private theorem deriv_matrix_mul {n : Type*} [Fintype n] [DecidableEq n]
    (A B : ℝ → Matrix n n ℂ) (A' B' : Matrix n n ℂ)
    (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0) :
    HasDerivAt (fun k => A k * B k) (A'*B 0 + A 0*B') 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
    ((hasDerivAt_pi.mp ((hasDerivAt_pi.mp hA) i)) l).mul
      ((hasDerivAt_pi.mp ((hasDerivAt_pi.mp hB) l)) j))
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib,Pi.mul_apply] using h

private theorem deriv_matrix_trace {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (hA : HasDerivAt A A' 0) :
    HasDerivAt (fun k => (A k).trace) A'.trace 0 := by
  simpa only [Matrix.trace,Matrix.diag] using HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hasDerivAt_pi.mp ((hasDerivAt_pi.mp hA) i)) i)

private def affine {n : Type*} (A B : Matrix n n ℂ) (k : ℝ) : Matrix n n ℂ :=
  A + (k : ℂ) • B

private theorem deriv_matrix_const {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : HasDerivAt (fun _ : ℝ => A) 0 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_const 0 (A i j)

private theorem deriv_affine {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) :
    HasDerivAt (affine A B) B 0 := by
  have hc : HasDerivAt (fun k : ℝ => (k : ℂ)) (1 : ℂ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  simpa only [affine,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,one_mul]
    using (hc.mul_const (B i j)).const_add (A i j)

private def evenCorner (N : ℕ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks 1 0 0 0

private def oddImag (N : ℕ) (z : ℂ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks 0 0 0 (z • 1)

private theorem parity_eq_affine {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (k : ℝ) :
    primeBurnolReflectedParityGram pe k =
      affine (evenCorner N) (oddImag N Complex.I) k * primeBurnolCollisionGram pe k *
        affine (evenCorner N) (oddImag N (-Complex.I)) k := by
  change Matrix.fromBlocks 1 0 0 ((Complex.I*(k : ℂ)) • 1) * _ *
    Matrix.fromBlocks 1 0 0 ((-Complex.I*(k : ℂ)) • 1) = _
  simp only [affine,evenCorner,oddImag,Matrix.fromBlocks_smul,
    Matrix.fromBlocks_add,smul_zero,add_zero,zero_add,smul_smul,mul_comm (k : ℂ)]

def primeBurnolReflectedGramFirstCoefficient {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  oddImag N Complex.I * primeBurnolCollisionGram pe 0 * evenCorner N +
    evenCorner N * primeBurnolCollisionGram pe 0 * oddImag N (-Complex.I)

theorem hasDerivAt_primeBurnolReflectedParityGram {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) :
    HasDerivAt (primeBurnolReflectedParityGram pe) (primeBurnolReflectedGramFirstCoefficient pe) 0 := by
  change HasDerivAt (fun k : ℝ => primeBurnolReflectedParityGram pe k) _ _
  simp_rw [parity_eq_affine]
  have h := deriv_matrix_mul _ _ _ _
    (deriv_matrix_mul _ _ _ _ (deriv_affine (evenCorner N) (oddImag N Complex.I))
      (hasDerivAt_primeBurnolCollisionGram_zero pe))
    (deriv_affine (evenCorner N) (oddImag N (-Complex.I)))
  simpa only [affine,Complex.ofReal_zero,zero_smul,add_zero,Matrix.mul_zero,
    primeBurnolReflectedGramFirstCoefficient] using h

def primeBurnolRegularizedReflectedInverse {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (k : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  affine (oddImag N Complex.I) (evenCorner N) k * (primeBurnolCollisionGram pe k)⁻¹ *
    affine (oddImag N (-Complex.I)) (evenCorner N) k

def primeBurnolReflectedInverseFirstCoefficient {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  evenCorner N * (primeBurnolCollisionGram pe 0)⁻¹ * oddImag N (-Complex.I) +
    oddImag N Complex.I * (primeBurnolCollisionGram pe 0)⁻¹ * evenCorner N

theorem hasDerivAt_primeBurnolRegularizedReflectedInverse {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) :
    HasDerivAt (primeBurnolRegularizedReflectedInverse pe)
      (primeBurnolReflectedInverseFirstCoefficient pe) 0 := by
  change HasDerivAt (fun k : ℝ => primeBurnolRegularizedReflectedInverse pe k) _ _
  have h := deriv_matrix_mul _ _ _ _
    (deriv_matrix_mul _ _ _ _ (deriv_affine (oddImag N Complex.I) (evenCorner N))
      (hasDerivAt_primeBurnolCollisionGram_inverse_zero pe))
    (deriv_affine (oddImag N (-Complex.I)) (evenCorner N))
  simpa only [primeBurnolRegularizedReflectedInverse,affine,Complex.ofReal_zero,
    zero_smul,add_zero,Matrix.mul_zero,primeBurnolReflectedInverseFirstCoefficient] using h

private theorem scalar_block_inverse (N : ℕ) (w : ℂ) (hw : w ≠ 0) :
    (Matrix.fromBlocks (1 : Matrix (Fin N) (Fin N) ℂ) 0 0
      (w • (1 : Matrix (Fin N) (Fin N) ℂ)))⁻¹ =
      Matrix.fromBlocks 1 0 0 (w⁻¹ • 1) := by
  apply Matrix.inv_eq_right_inv
  simp [Matrix.fromBlocks_multiply,smul_smul,hw,Matrix.fromBlocks_one]

theorem primeBurnolRegularizedReflectedInverse_eq {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) {k : ℝ} (hk : k ≠ 0) :
    primeBurnolRegularizedReflectedInverse pe k =
      (k : ℂ)^2 • (primeBurnolReflectedParityGram pe k)⁻¹ := by
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have hl : (k : ℂ) •
      (Matrix.fromBlocks (1 : Matrix (Fin N) (Fin N) ℂ) 0 0 ((-Complex.I*(k : ℂ)) • 1))⁻¹ =
        affine (oddImag N Complex.I) (evenCorner N) k := by
    rw [scalar_block_inverse _ _ (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hkC)]
    simp [affine,oddImag,evenCorner,Matrix.fromBlocks_smul,Matrix.fromBlocks_add,
      smul_smul,_root_.mul_inv_rev,hkC]
  have hr : (k : ℂ) •
      (Matrix.fromBlocks (1 : Matrix (Fin N) (Fin N) ℂ) 0 0 ((Complex.I*(k : ℂ)) • 1))⁻¹ =
        affine (oddImag N (-Complex.I)) (evenCorner N) k := by
    rw [scalar_block_inverse _ _ (mul_ne_zero Complex.I_ne_zero hkC)]
    simp [affine,oddImag,evenCorner,Matrix.fromBlocks_smul,Matrix.fromBlocks_add,
      smul_smul,_root_.mul_inv_rev,hkC]
  change _ = (k : ℂ)^2 •
    (Matrix.fromBlocks 1 0 0 ((Complex.I*(k : ℂ)) • 1) * primeBurnolCollisionGram pe k *
      Matrix.fromBlocks 1 0 0 ((-Complex.I*(k : ℂ)) • 1))⁻¹
  rw [Matrix.mul_inv_rev,Matrix.mul_inv_rev,primeBurnolRegularizedReflectedInverse,← hl,← hr]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,pow_two,Matrix.mul_assoc]


private def parityP (N : ℕ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  (2 : ℂ)⁻¹ • Matrix.fromBlocks 1 1 1 1

private theorem parityP_idempotent (N : ℕ) : parityP N * parityP N = parityP N := by
  simp [parityP,Matrix.fromBlocks_multiply,Matrix.fromBlocks_smul,smul_smul,← two_smul ℂ]

def primeBurnolMixedCubicFirstCoefficient {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) : ℂ :=
  let c := primeBurnolReflectedParityGram pe 0
  let d := primeBurnolReflectedGramFirstCoefficient pe
  let r := primeBurnolRegularizedReflectedInverse pe 0
  let s := primeBurnolReflectedInverseFirstCoefficient pe
  let p := parityP N
  let q := primeBurnolParityThetaProjection pe a
  Matrix.trace (d*p*r*q*c*(p-q) + c*p*s*q*c*(p-q) + c*p*r*q*d*(p-q))

private def regularizedCubic {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (a k : ℝ) : ℂ :=
  let c := primeBurnolReflectedParityGram pe k
  let p := parityP N
  let q := primeBurnolParityThetaProjection pe a
  Matrix.trace (c*p*primeBurnolRegularizedReflectedInverse pe k*q*c*(p-q)) +
    (k : ℂ)^2*Matrix.trace (c*(q*p*q-p*q*p))

private theorem deriv_regularizedCubic {N : ℕ} (pe : Fin N ↪ Nat.Primes × ℕ) (a : ℝ) :
    HasDerivAt (regularizedCubic pe a) (primeBurnolMixedCubicFirstCoefficient pe a) 0 := by
  let c := primeBurnolReflectedParityGram pe
  let r := primeBurnolRegularizedReflectedInverse pe
  let p := parityP N
  let q := primeBurnolParityThetaProjection pe a
  have hc := hasDerivAt_primeBurnolReflectedParityGram pe
  have hr := hasDerivAt_primeBurnolRegularizedReflectedInverse pe
  have h1 := deriv_matrix_mul c (fun _ => p) _ 0 hc (deriv_matrix_const p)
  have h2 := deriv_matrix_mul _ r _ _ h1 hr
  have h3 := deriv_matrix_mul _ (fun _ => q) _ 0 h2 (deriv_matrix_const q)
  have h4 := deriv_matrix_mul _ c _ _ h3 hc
  have h5 := deriv_matrix_mul _ (fun _ => p-q) _ 0 h4 (deriv_matrix_const (p-q))
  have ht := deriv_matrix_trace _ _ h5
  have hw := deriv_matrix_trace _ _ (deriv_matrix_mul c (fun _ => q*p*q-p*q*p) _ 0 hc
    (deriv_matrix_const (q*p*q-p*q*p)))
  have hk : HasDerivAt (fun k : ℝ => (k : ℂ)^2) 0 0 := by
    simpa using! ((hasDerivAt_id (0 : ℝ)).ofReal_comp).pow 2
  change HasDerivAt (fun k => regularizedCubic pe a k) _ _
  simpa only [regularizedCubic,primeBurnolMixedCubicFirstCoefficient,c,r,p,q,
    Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,Matrix.add_mul,Matrix.mul_add,
    Matrix.trace_add,Complex.ofReal_zero,zero_pow (by decide : 2 ≠ 0),zero_mul,add_assoc,
    Pi.mul_apply,Pi.add_apply] using! ht.add (hk.mul hw)

private theorem cubic_single_inverse {n : Type*} [Fintype n] [DecidableEq n]
    (c p q : Matrix n n ℂ) (hc : IsUnit c) (hp : p*p=p) (hq : q*q=q) :
    Matrix.trace (c*cubicProjectionAssociatorAlgebra (c⁻¹*q*c) q p) =
      Matrix.trace (c*p*c⁻¹*q*c*(p-q)) + Matrix.trace (c*(q*p*q-p*q*p)) := by
  rcases hc with ⟨c,rfl⟩
  have h := matrixTrace_weighted_cubic_single_inverse c p q hp hq
  change Matrix.trace ((c : Matrix n n ℂ)*cubicProjectionAssociatorAlgebra
    ((↑c⁻¹ : Matrix n n ℂ)*q*(c : Matrix n n ℂ)) q p) = _ at h
  simpa only [Matrix.coe_units_inv] using h

private theorem regularizedCubic_eq {N : ℕ} (pe : Fin N ↪ Nat.Primes × ℕ) (a k : ℝ)
    (hk : k ≠ 0) (hc : IsUnit (primeBurnolReflectedParityGram pe k)) :
    regularizedCubic pe a k = (k : ℂ)^2*primeBurnolParityThetaCubicTrace pe a k := by
  have ht := cubic_single_inverse _ (parityP N) (primeBurnolParityThetaProjection pe a)
    hc (parityP_idempotent N) (primeBurnolParityThetaProjection_idempotent pe a)
  change Matrix.trace (primeBurnolReflectedParityGram pe k*parityP N*
      primeBurnolRegularizedReflectedInverse pe k*primeBurnolParityThetaProjection pe a*
      primeBurnolReflectedParityGram pe k*(parityP N-primeBurnolParityThetaProjection pe a)) +
      (k : ℂ)^2*Matrix.trace (primeBurnolReflectedParityGram pe k*
        (primeBurnolParityThetaProjection pe a*parityP N*primeBurnolParityThetaProjection pe a-
          parityP N*primeBurnolParityThetaProjection pe a*parityP N)) =
      (k : ℂ)^2*Matrix.trace (primeBurnolReflectedParityGram pe k*
        cubicProjectionAssociatorAlgebra
          ((primeBurnolReflectedParityGram pe k)⁻¹*primeBurnolParityThetaProjection pe a*
            primeBurnolReflectedParityGram pe k) (primeBurnolParityThetaProjection pe a) (parityP N))
  rw [ht,primeBurnolRegularizedReflectedInverse_eq pe hk]
  simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,mul_add]

private theorem regularizedCubic_zero {N : ℕ} (pe : Fin N ↪ Nat.Primes × ℕ) (a : ℝ) :
    regularizedCubic pe a 0 = primeBurnolMixedCubicPrincipalCoefficient pe a := by
  have he : regularizedCubic pe a =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun k => (k : ℂ)^2*primeBurnolParityThetaCubicTrace pe a k) := by
    filter_upwards [self_mem_nhdsWithin,eventually_primeBurnolReflectedParityGram_isUnit pe]
      with k hk hc
    exact regularizedCubic_eq pe a k hk hc
  exact tendsto_nhds_unique
    ((deriv_regularizedCubic pe a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    ((primeBurnolParityThetaCubicTrace_principal pe a).congr' he.symm)

/-- Complete first-order Laurent coefficient after subtracting the checked mixed second-order pole. -/
theorem primeBurnolMixedReflectedThetaCubicTrace_first_coefficient {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) (a : ℝ) :
    Tendsto (fun k : ℝ => (k : ℂ)*
      (primeBurnolMixedReflectedThetaCubicTrace pe a k-
        primeBurnolMixedCubicPrincipalCoefficient pe a/(k : ℂ)^2))
      (𝓝[≠] 0) (𝓝 (primeBurnolMixedCubicFirstCoefficient pe a)) := by
  have ht := (deriv_regularizedCubic pe a).tendsto_slope_zero
  rw [regularizedCubic_zero] at ht
  simp only [zero_add,Complex.real_smul,Complex.ofReal_inv] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,eventually_primeBurnolReflectedParityGram_isUnit pe]
    with k hk hc
  rw [regularizedCubic_eq pe a k hk hc,primeBurnolParityThetaCubicTrace_eq_source]
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  field_simp

end
end RHTower
