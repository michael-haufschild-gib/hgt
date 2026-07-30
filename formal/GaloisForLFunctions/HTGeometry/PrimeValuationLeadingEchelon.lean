import GaloisForLFunctions.HTGeometry.PrimeSeparatedDeterminantCoefficient
import GaloisForLFunctions.HTGeometry.PrimeValuationVeroneseDifferentialBasis
import GaloisForLFunctions.HTGeometry.DifferentialIndependentLinearForms

/-!
# Prime-valuation leading-echelon law

A finite family of arithmetic functions may have infinitely many nonzero prime-power layers.
Suppose, however, that each source has a private valuation coordinate: at a selected exponent its
coefficient is a fixed nonzero scalar at every prime, while every other source vanishes there.
Then the family is differentially algebraically independent for the rotated logarithmic
derivation.

The proof does not truncate the other valuation layers.  Prime derivations turn every jet row into
an arbitrary function on one prime ray; unique factorization then reads one separated coefficient
of the full convolution determinant.  Thus uncontrolled infinite tails cannot cancel the private
valuation minor.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Matrix
open scoped Differential

noncomputable section

universe u

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 80000

/-- A nonuniform prime-power packet theorem in which the valuation exponents need only be
pairwise distinct; they need not be the initial consecutive exponents. -/
theorem cofinitePrimePowerPacket_of_injective_layerExponents
    (d : ℕ) (A : Fin d → Type u)
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    (e : Fin d → ℕ) (he : Function.Injective e)
    (a : ∀ r, A r → Nat.Primes → ℂ)
    (htail : ∀ r, TailCoefficientIndependent (a r)) :
    CofinitePrimePowerPacket
      (fun i : Σ r, A r => e i.1)
      (primePowerSigmaCoefficient a) := by
  intro forbidden hforbidden
  obtain ⟨q, hq, havoid, hunit⟩ :=
    exists_disjoint_layer_packets d A a htail forbidden hforbidden
  refine ⟨q, hq, havoid, ?_⟩
  let E : ∀ r, Matrix (A r) (A r) ℂ := fun r =>
    Matrix.of fun row col => a r col (q ⟨r, row⟩)
  let C : ∀ r, Matrix (A r) (A r) ℂ := fun r =>
    (((e r + 1 : ℕ) : ℂ)) • E r
  have hmatrix :
      primePowerBlockMatrix (fun i : Σ r, A r => e i.1)
          (primePowerPacketCoefficientMatrix
            (fun i : Σ r, A r => e i.1)
            (primePowerSigmaCoefficient a) q) =
        Matrix.blockDiagonal' C := by
    ext i j
    rcases i with ⟨r, i⟩
    rcases j with ⟨s, j⟩
    by_cases hrs : r = s
    · subst s
      simp [primePowerBlockMatrix, primePowerPacketCoefficientMatrix,
        primePowerSigmaCoefficient, Matrix.blockDiagonal', C, E]
    · have hers : e r ≠ e s := fun h => hrs (he h)
      simp [primePowerBlockMatrix, Matrix.blockDiagonal', C, E, hrs, hers]
  rw [hmatrix]
  have hC : ∀ r, IsUnit (C r) := by
    intro r
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    rw [show C r = (((e r + 1 : ℕ) : ℂ)) • E r from rfl,
      Matrix.det_smul]
    apply mul_ne_zero
    · apply pow_ne_zero
      exact_mod_cast Nat.succ_ne_zero (e r)
    · exact ((Matrix.isUnit_iff_isUnit_det _).mp (hunit r)).ne_zero
  have hPi : IsUnit C := Pi.isUnit_iff.mpr hC
  have hBlock : IsUnit (Matrix.blockDiagonal' C) :=
    hPi.map (Matrix.blockDiagonal'RingHom (fun r => A r) ℂ)
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hBlock).ne_zero

/-- The explicit coefficient form of the `k`-th rotated logarithmic jet. -/
def rotatedLogArithmeticJet (k : ℕ) (f : ArithmeticFunction ℂ) :
    ArithmeticFunction ℂ where
  toFun n := (Complex.I * (Real.log n : ℂ)) ^ k * f n
  map_zero' := by simp

@[simp]
theorem rotatedLogArithmeticJet_apply
    (k : ℕ) (f : ArithmeticFunction ℂ) (n : ℕ) :
    rotatedLogArithmeticJet k f n =
      (Complex.I * (Real.log n : ℂ)) ^ k * f n :=
  rfl

@[simp]
theorem rotatedLogArithmeticJet_zero (f : ArithmeticFunction ℂ) :
    rotatedLogArithmeticJet 0 f = f := by
  ext n
  simp

/-- Rotated logarithmic differentiation advances the explicit jet by one order. -/
theorem rotatedLogArithmeticJet_succ (k : ℕ) (f : ArithmeticFunction ℂ) :
    Complex.I • logWeight (rotatedLogArithmeticJet k f) =
      rotatedLogArithmeticJet (k + 1) f := by
  ext n
  simp only [ArithmeticFunction.smul_map, smul_eq_mul, logWeight_apply,
    rotatedLogArithmeticJet_apply, pow_succ]
  ring

/-- The differential jets of an embedded arithmetic function are its explicit rotated logarithmic
coefficient jets. -/
@[simp]
theorem differentialJet_algebraMap_rotatedLogArithmeticJet
    (k : ℕ) (f : ArithmeticFunction ℂ) :
    GaloisForLFunctions.differentialJet k
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (rotatedLogArithmeticJet k f) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [GaloisForLFunctions.differentialJet_succ, ih,
        arithmeticFunctionFractionField_deriv_apply,
        rotatedLogFractionDerivation_algebraMap,
        rotatedLogArithmeticJet_succ]

/-- Support on positive prime powers, with no restriction on the number of active valuation
layers or on their coefficients. -/
def SupportedOnPositivePrimePowers (f : ArithmeticFunction ℂ) : Prop :=
  ∀ ⦃n : ℕ⦄, f n ≠ 0 →
    ∃ (p : Nat.Primes) (e : ℕ), n = (p : ℕ) ^ (e + 1)

/-- A prime derivation of any rotated jet of a positive-prime-power source lives on the
corresponding prime ray. -/
theorem primeDeriv_rotatedLogArithmeticJet_supportedOnPrimeRay
    (f : ArithmeticFunction ℂ) (hsupport : SupportedOnPositivePrimePowers f)
    (q : Nat.Primes) (k : ℕ) :
    SupportedOnPrimeRay q (primeDeriv q.1 (rotatedLogArithmeticJet k f)) := by
  intro n hn
  have hvalue : f (n * q) ≠ 0 := by
    intro hzero
    apply hn
    rw [primeDeriv_apply, rotatedLogArithmeticJet_apply, hzero, mul_zero, mul_zero]
  obtain ⟨p, e, hp⟩ := hsupport hvalue
  have hqdvd : (q : ℕ) ∣ (p : ℕ) ^ (e + 1) := by
    rw [← hp]
    exact ⟨n, by ring⟩
  have hpq : q = p := by
    apply Subtype.ext
    exact Nat.prime_eq_prime_of_dvd_pow q.2 p.2 hqdvd
  subst p
  refine ⟨e, ?_⟩
  apply Nat.eq_of_mul_eq_mul_right q.2.pos
  calc
    n * q = (q : ℕ) ^ (e + 1) := hp
    _ = (q : ℕ) ^ e * q := by rw [pow_succ]

/-- Exact row coefficient obtained by applying a prime derivation to a rotated jet and reading it
at one lower power of that prime. -/
theorem primeDeriv_rotatedLogArithmeticJet_apply_primePow
    (f : ArithmeticFunction ℂ) (q : Nat.Primes) (e k : ℕ) :
    primeDeriv q.1 (rotatedLogArithmeticJet k f) ((q : ℕ) ^ e) =
      ((e + 1 : ℕ) : ℂ) *
        ((((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock q) ^ k *
          f ((q : ℕ) ^ (e + 1))) := by
  rw [primeDeriv_apply]
  have hmul : (q : ℕ) ^ e * q = (q : ℕ) ^ (e + 1) := by
    rw [pow_succ]
  rw [hmul, Nat.Prime.factorization_pow q.2]
  simp only [Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one,
    rotatedLogArithmeticJet_apply]
  have hlog : Real.log (((q : ℕ) ^ (e + 1) : ℕ) : ℝ) =
      ((e + 1 : ℕ) : ℝ) * Real.log ((q : ℕ) : ℝ) := by
    rw [show (((q : ℕ) ^ (e + 1) : ℕ) : ℝ) =
        ((q : ℕ) : ℝ) ^ (e + 1) by norm_num, Real.log_pow]
  have hlogC : (Real.log (((q : ℕ) ^ (e + 1) : ℕ) : ℝ) : ℂ) =
      ((e + 1 : ℕ) : ℂ) * (Real.log ((q : ℕ) : ℝ) : ℂ) := by
    exact_mod_cast hlog
  rw [hlogC]
  have hclock :
      Complex.I * (((e + 1 : ℕ) : ℂ) *
          (Real.log ((q : ℕ) : ℝ) : ℂ)) =
        ((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock q := by
    simp only [rotatedPrimeLogClock, primeLogClock]
    ring
  rw [hclock]
  norm_num

/-- **Finite leading-echelon jet theorem.**  Arbitrary infinite prime-power tails cannot create a
relation among a finite jet rectangle once every source has a private nonzero valuation
coordinate. -/
theorem primeValuationLeadingEchelonJets_algebraicIndependent_of_primeDependent
    {d : ℕ} [Nonempty (Fin d)]
    (g : Fin d → ArithmeticFunction ℂ)
    (e : Fin d → ℕ) (he : Function.Injective e)
    (c : Fin d → Nat.Primes → ℂ) (hc : ∀ r p, c r p ≠ 0)
    (hsupport : ∀ r, SupportedOnPositivePrimePowers (g r))
    (hprivate : ∀ r s (p : Nat.Primes),
      g s ((p : ℕ) ^ (e r + 1)) = if r = s then c s p else 0)
    (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun x : Fin d × Fin (m + 1) =>
        rotatedLogArithmeticJet x.2 (g x.1)) := by
  let A : Fin d → Type := fun _ => Unit × (Unit × Fin (m + 1))
  letI (r : Fin d) : Fintype (A r) := inferInstance
  letI (r : Fin d) : DecidableEq (A r) := inferInstance
  let a : ∀ r, A r → Nat.Primes → ℂ := fun r x p =>
    c r p * ((((e r + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ (x.2.2 : ℕ))
  have htail : ∀ r, TailCoefficientIndependent (a r) := by
    intro r
    let base : Unit → Nat.Primes → ℂ := fun _ _ => 1
    have hbase : TailCoefficientIndependent base := by
      rw [tailCoefficientIndependent_unit_iff]
      unfold PrimeCoefficientTailZero
      simpa [base] using (Set.infinite_univ : (Set.univ : Set Nat.Primes).Infinite)
    have hrange : (Set.range (coefficientPattern base)).Finite := by
      apply (Set.finite_singleton (fun _ : Unit => (1 : ℂ))).subset
      intro y hy
      obtain ⟨p, rfl⟩ := hy
      funext u
      cases u
      rfl
    have hraw := (primePowerCoefficientShiftedRotatedJet_tailIndependent_iff
      (e r) base (fun _ : Unit => 0)
      (fun _ _ _ => Subsingleton.elim _ _) hrange m).mpr hbase
    let raw : A r → Nat.Primes → ℂ := fun x p =>
      (((e r + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ (x.2.2 : ℕ)
    have hraw' : TailCoefficientIndependent raw := by
      simpa only [raw, A, base, primeShiftFactor, neg_zero, zero_mul,
        Complex.exp_zero, one_mul] using hraw
    have hweighted :=
      (tailCoefficientIndependent_commonWeight_iff raw (c r) (hc r)).mpr hraw'
    simpa only [a, raw] using hweighted
  obtain ⟨q, hq, _havoid, hdet⟩ :=
    cofinitePrimePowerPacket_of_injective_layerExponents d A e he a htail
      ∅ Set.finite_empty
  let I := Σ r, A r
  let exponent : I → ℕ := fun i => e i.1
  let sourceJet : I → ArithmeticFunction ℂ := fun x =>
    rotatedLogArithmeticJet x.2.2.2 (g x.1)
  let M : Matrix I I (ArithmeticFunction ℂ) := fun i j =>
    primeDeriv (q i).1 (sourceJet j)
  have hMsupport : ∀ i j, SupportedOnPrimeRay (q i) (M i j) := by
    intro i j
    exact primeDeriv_rotatedLogArithmeticJet_supportedOnPrimeRay
      (g j.1) (hsupport j.1) (q i) j.2.2.2
  have hcoeff :
      (fun i j => M i j ((q i : ℕ) ^ exponent i)) =
        primePowerBlockMatrix exponent
          (primePowerPacketCoefficientMatrix exponent
            (primePowerSigmaCoefficient a) q) := by
    funext i j
    rcases i with ⟨r, ⟨u, v, k⟩⟩
    rcases j with ⟨s, ⟨u', v', l⟩⟩
    simp only [M, sourceJet, exponent]
    rw [primeDeriv_rotatedLogArithmeticJet_apply_primePow]
    rw [hprivate r s (q ⟨r, (u, (v, k))⟩)]
    by_cases hrs : r = s
    · subst s
      rw [primePowerBlockMatrix, if_pos rfl]
      simp only [primePowerPacketCoefficientMatrix,
        primePowerSigmaCoefficient, a, if_true]
      ring
    · have hers : e r ≠ e s := fun h => hrs (he h)
      rw [if_neg hrs]
      simp only [mul_zero]
      rw [primePowerBlockMatrix, if_neg hers]
  have hMdet : M.det ≠ 0 := by
    apply primeRayMatrix_det_ne_zero q hq exponent M hMsupport
    rw [hcoeff]
    exact hdet
  have hAI : AlgebraicIndependent ℂ sourceJet := by
    refine algebraicIndependent_of_domain_jacobian
      (K := ℂ) (R := ArithmeticFunction ℂ)
      sourceJet (fun i => primeDeriv (q i).1)
      (fun i => primeDeriv_add (q i).1)
      (fun i => primeDeriv_mul (q i).1 (q i).2)
      (fun i => primeDeriv_algebraMap (q i).1 (q i).2)
      M hMdet ?_
    intro i j
    rfl
  let f : (Fin d × Fin (m + 1)) → I := fun x =>
    ⟨x.1, ((), ((), x.2))⟩
  have hf : Function.Injective f := by
    rintro ⟨r, k⟩ ⟨s, l⟩ h
    cases h
    rfl
  have hsub := hAI.comp f hf
  simpa only [Function.comp_apply, f, sourceJet] using! hsub

/-- Constant private coefficients are the prime-independent specialization of the
prime-dependent finite leading-echelon theorem. -/
theorem primeValuationLeadingEchelonJets_algebraicIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (g : Fin d → ArithmeticFunction ℂ)
    (e : Fin d → ℕ) (he : Function.Injective e)
    (c : Fin d → ℂ) (hc : ∀ r, c r ≠ 0)
    (hsupport : ∀ r, SupportedOnPositivePrimePowers (g r))
    (hprivate : ∀ r s (p : Nat.Primes),
      g s ((p : ℕ) ^ (e r + 1)) = if r = s then c s else 0)
    (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun x : Fin d × Fin (m + 1) =>
        rotatedLogArithmeticJet x.2 (g x.1)) := by
  apply primeValuationLeadingEchelonJets_algebraicIndependent_of_primeDependent
    g e he (fun r _ => c r) (fun r _ => hc r) hsupport
  simpa using hprivate

/-- **Prime-valuation leading-echelon law.**  A finite family of arbitrary positive-prime-power
sources is differentially independent whenever it has pairwise distinct private valuation
coordinates.  No assumption is made on any unselected valuation layer. -/
theorem primeValuationLeadingEchelon_differentialIndependent_of_primeDependent
    {d : ℕ} [Nonempty (Fin d)]
    (g : Fin d → ArithmeticFunction ℂ)
    (e : Fin d → ℕ) (he : Function.Injective e)
    (c : Fin d → Nat.Primes → ℂ) (hc : ∀ r p, c r p ≠ 0)
    (hsupport : ∀ r, SupportedOnPositivePrimePowers (g r))
    (hprivate : ∀ r s (p : Nat.Primes),
      g s ((p : ℕ) ^ (e r + 1)) = if r = s then c s p else 0) :
    GaloisForLFunctions.DifferentialIndependent ℂ
      (fun r => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (g r)) := by
  unfold GaloisForLFunctions.DifferentialIndependent
  simp_rw [differentialJet_algebraMap_rotatedLogArithmeticJet]
  let x : Fin d → ℕ → arithmeticFunctionFractionField := fun r k =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (rotatedLogArithmeticJet k (g r))
  apply algebraicIndependent_prod_nat_of_fin x
  intro m
  have hraw :=
    primeValuationLeadingEchelonJets_algebraicIndependent_of_primeDependent
    g e he c hc hsupport hprivate m
  have hmap := hraw.map'
    (f := IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
    (IsFractionRing.injective (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
  simpa only [Function.comp_apply, x] using! hmap

/-- **Constant-coefficient prime-valuation leading-echelon law.**  This preserves the original
interface while the stronger theorem permits nonzero private coefficients to vary with the
selected prime. -/
theorem primeValuationLeadingEchelon_differentialIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (g : Fin d → ArithmeticFunction ℂ)
    (e : Fin d → ℕ) (he : Function.Injective e)
    (c : Fin d → ℂ) (hc : ∀ r, c r ≠ 0)
    (hsupport : ∀ r, SupportedOnPositivePrimePowers (g r))
    (hprivate : ∀ r s (p : Nat.Primes),
      g s ((p : ℕ) ^ (e r + 1)) = if r = s then c s else 0) :
    GaloisForLFunctions.DifferentialIndependent ℂ
      (fun r => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (g r)) := by
  apply primeValuationLeadingEchelon_differentialIndependent_of_primeDependent
    g e he (fun r _ => c r) (fun r _ => hc r) hsupport
  simpa using hprivate

/-- Matrix linear forms compose by matrix multiplication. -/
theorem matrixLinearForms_comp
    {R B m n t : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Fintype n] [Fintype t]
    (M : Matrix m n R) (N : Matrix n t R) (x : t → B) (i : m) :
    matrixLinearForms M (matrixLinearForms N x) i =
      matrixLinearForms (M * N) x i := by
  classical
  simp only [matrixLinearForms, Matrix.mul_apply, map_sum, map_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The identity matrix acts trivially by matrix linear forms. -/
@[simp]
theorem matrixLinearForms_one_apply
    {R B n : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Fintype n] [DecidableEq n] (x : n → B) (i : n) :
    matrixLinearForms (1 : Matrix n n R) x i = x i := by
  classical
  simp [matrixLinearForms, Matrix.one_apply]

/-- Complex constants are killed by the rotated logarithmic differential structure on the
arithmetic-function fraction field. -/
@[simp]
theorem arithmeticFunctionFractionField_deriv_algebraMap_complex (z : ℂ) :
    (algebraMap ℂ arithmeticFunctionFractionField z)′ = 0 := by
  change rotatedLogFractionDerivation
      (algebraMap ℂ arithmeticFunctionFractionField z) = 0
  rw [show algebraMap ℂ arithmeticFunctionFractionField z =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (algebraMap ℂ (ArithmeticFunction ℂ) z) by
    exact (IsScalarTower.algebraMap_apply ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField z).symm]
  rw [rotatedLogFractionDerivation_algebraMap]
  change algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (rotatedLogArithmeticDerivationComplex
        (algebraMap ℂ (ArithmeticFunction ℂ) z)) = 0
  rw [Derivation.map_algebraMap, _root_.map_zero]

/-- **Finite valuation-profile minor theorem.**  Suppose the coefficients of a finite family are
constant along prime rays at selected pairwise-distinct valuation exponents.  If the resulting
square profile minor is nonsingular, then the family is differentially independent, irrespective
of all unselected prime-power layers. -/
theorem primeValuationProfileMinor_differentialIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (g : Fin d → ArithmeticFunction ℂ)
    (e : Fin d → ℕ) (he : Function.Injective e)
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : IsUnit P.det)
    (hsupport : ∀ r, SupportedOnPositivePrimePowers (g r))
    (hprofile : ∀ r s (p : Nat.Primes),
      g s ((p : ℕ) ^ (e r + 1)) = P r s) :
    GaloisForLFunctions.DifferentialIndependent ℂ
      (fun r => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (g r)) := by
  let N : Matrix (Fin d) (Fin d) ℂ := P⁻¹.transpose
  let h : Fin d → ArithmeticFunction ℂ := matrixLinearForms N g
  have hsupport' : ∀ s, SupportedOnPositivePrimePowers (h s) := by
    intro s n hn
    by_contra hnone
    have hgzero : ∀ j, g j n = 0 := by
      intro j
      by_contra hgj
      obtain ⟨p, k, hk⟩ := hsupport j hgj
      exact hnone ⟨p, k, hk⟩
    apply hn
    let ev : ArithmeticFunction ℂ →+ ℂ :=
      { toFun := fun f => f n
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change (matrixLinearForms N g s) n = 0
    simp only [matrixLinearForms, ← Algebra.smul_def]
    change ev (∑ j, N s j • g j) = 0
    rw [map_sum]
    change (∑ j, N s j * g j n) = 0
    apply Finset.sum_eq_zero
    intro j hj
    rw [hgzero j, mul_zero]
  have hprivate : ∀ r s (p : Nat.Primes),
      h s ((p : ℕ) ^ (e r + 1)) = if r = s then 1 else 0 := by
    intro r s p
    let ev : ArithmeticFunction ℂ →+ ℂ :=
      { toFun := fun f => f ((p : ℕ) ^ (e r + 1))
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change (matrixLinearForms N g s) ((p : ℕ) ^ (e r + 1)) = _
    simp only [matrixLinearForms, ← Algebra.smul_def]
    change ev (∑ j, N s j • g j) = _
    rw [map_sum]
    change (∑ j, N s j * g j ((p : ℕ) ^ (e r + 1))) = _
    simp only [N, Matrix.transpose_apply, hprofile]
    have hmul := congrFun (congrFun (Matrix.mul_nonsing_inv P hP) r) s
    rw [Matrix.mul_apply, Matrix.one_apply] at hmul
    calc
      (∑ j, P⁻¹ j s * P r j) = ∑ j, P r j * P⁻¹ j s := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = if r = s then 1 else 0 := hmul
  have hDI : GaloisForLFunctions.DifferentialIndependent ℂ
      (fun r => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (h r)) :=
    primeValuationLeadingEchelon_differentialIndependent
      h e he (fun _ => 1) (fun _ => one_ne_zero) hsupport' hprivate
  let embeddedH : Fin d → arithmeticFunctionFractionField := fun r =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (h r)
  have hembeddedH : embeddedH = matrixLinearForms N
      (fun r => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (g r)) := by
    funext r
    simp only [embeddedH, h, matrixLinearForms, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
  have hPN : P.transpose * N = 1 := by
    rw [show N = P⁻¹.transpose from rfl, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul P hP, Matrix.transpose_one]
  have hback : matrixLinearForms P.transpose embeddedH =
      (fun r => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (g r)) := by
    rw [hembeddedH]
    funext r
    rw [matrixLinearForms_comp, hPN, matrixLinearForms_one_apply]
  have hresult := differentialIndependent_matrixLinearForms_of_mul_eq_one
    arithmeticFunctionFractionField_deriv_algebraMap_complex
    P.transpose N hPN embeddedH hDI
  rw [hback] at hresult
  exact hresult

end

end GaloisForLFunctions.HTGeometry
