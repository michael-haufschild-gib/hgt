import GaloisForLFunctions.RHTower.HighExponentShellHypertranscendence
import GaloisForLFunctions.RHTower.SqrtCarrierCertificate

/-!
# Complete positive Kolchin-free resolution of the Riemann divisor

The first part proves a general HT-geometry law: differential independence is invariant under the
locally finite change from a sequence to its first term and successive differences.  The second
part applies the `Ω`-leading-echelon machinery to the dilated Möbius carriers
`ζ(ms)⁻¹`.  Together they show that, for every `K ≥ 12`, the `K`-free integers and the exact
largest-exponent shells `m ≥ K` form a complete positive coefficient partition of zeta whose
normalized channels are jointly differentially independent over the full zeta differential
field, while every channel carries exactly the zeta divisor on `re s > 1/2`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial GaloisForLFunctions

/-! ## A universal successive-difference invariance law -/

/-- Formal locally finite change from a sequence to its first term and successive differences. -/
def successiveDifferencePolynomial {B : Type*} [CommRing B]
    (p : ℕ × ℕ) : MvPolynomial (ℕ × ℕ) B :=
  match p.1 with
  | 0 => X p
  | n + 1 => X (n + 1, p.2) - X (n, p.2)

/-- The successive-difference substitution on the full countable jet polynomial algebra. -/
def successiveDifferenceAlgHom {B : Type*} [CommRing B] :
    MvPolynomial (ℕ × ℕ) B →ₐ[B] MvPolynomial (ℕ × ℕ) B :=
  MvPolynomial.aeval successiveDifferencePolynomial

/-- Formal inverse: the finite prefix sum at every jet order. -/
def prefixSumPolynomial {B : Type*} [CommRing B]
    (p : ℕ × ℕ) : MvPolynomial (ℕ × ℕ) B :=
  ∑ i ∈ Finset.range (p.1 + 1), X (i, p.2)

/-- Prefix-sum substitution on the full countable jet polynomial algebra. -/
def prefixSumAlgHom {B : Type*} [CommRing B] :
    MvPolynomial (ℕ × ℕ) B →ₐ[B] MvPolynomial (ℕ × ℕ) B :=
  MvPolynomial.aeval prefixSumPolynomial

@[simp] theorem successiveDifferenceAlgHom_X
    {B : Type*} [CommRing B] (p : ℕ × ℕ) :
    successiveDifferenceAlgHom (B := B) (X p) =
      successiveDifferencePolynomial p := by
  simp [successiveDifferenceAlgHom]

@[simp] theorem prefixSumAlgHom_X
    {B : Type*} [CommRing B] (p : ℕ × ℕ) :
    prefixSumAlgHom (B := B) (X p) = prefixSumPolynomial p := by
  simp [prefixSumAlgHom]

/-- Finite prefix summation exactly inverts successive differences. -/
theorem sum_successiveDifferencePolynomial
    {B : Type*} [CommRing B] (n r : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        successiveDifferencePolynomial (B := B) (i, r) = X (n, r) := by
  induction n with
  | zero => simp [successiveDifferencePolynomial]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [successiveDifferencePolynomial]

/-- Prefix sums are a left inverse to the successive-difference substitution. -/
theorem prefixSumAlgHom_comp_successiveDifferenceAlgHom
    {B : Type*} [CommRing B] :
    (prefixSumAlgHom (B := B)).comp successiveDifferenceAlgHom =
      AlgHom.id B (MvPolynomial (ℕ × ℕ) B) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨n, r⟩
  rw [AlgHom.comp_apply, successiveDifferenceAlgHom_X]
  cases n with
  | zero => simp [successiveDifferencePolynomial, prefixSumPolynomial]
  | succ n =>
      simp only [successiveDifferencePolynomial, map_sub, prefixSumAlgHom_X,
        prefixSumPolynomial]
      rw [Finset.sum_range_succ]
      simp

/-- The locally finite successive-difference substitution is injective. -/
theorem successiveDifferenceAlgHom_injective
    {B : Type*} [CommRing B] :
    Function.Injective (successiveDifferenceAlgHom (B := B)) := by
  intro P Q hPQ
  have hcomp := prefixSumAlgHom_comp_successiveDifferenceAlgHom (B := B)
  calc
    P = ((prefixSumAlgHom (B := B)).comp successiveDifferenceAlgHom) P := by
      rw [hcomp]
      rfl
    _ = ((prefixSumAlgHom (B := B)).comp successiveDifferenceAlgHom) Q := by
      exact congrArg (prefixSumAlgHom (B := B)) hPQ
    _ = Q := by
      rw [hcomp]
      rfl

/-- First coordinate followed by successive differences of a sequence. -/
def successiveDifference {L : Type*} [AddGroup L] (x : ℕ → L) : ℕ → L
  | 0 => x 0
  | n + 1 => x (n + 1) - x n

theorem differentialJet_successiveDifference
    {L : Type*} [Field L] [Differential L]
    (x : ℕ → L) (n r : ℕ) :
    differentialJet r (successiveDifference x n) =
      successiveDifference (fun i => differentialJet r (x i)) n := by
  cases n with
  | zero => rfl
  | succ n =>
      rw [successiveDifference, successiveDifference,
        GaloisForLFunctions.differentialJet_sub]

/-- **Universal successive-difference law.**  A differentially independent countable sequence
remains differentially independent after replacing it by its first coordinate and all successive
differences.  The inverse change is the locally finite prefix sum, so no completion is used. -/
theorem differentialIndependent_successiveDifference
    {B L : Type*} [Field B] [Field L] [Algebra B L] [Differential L]
    (x : ℕ → L) (hx : DifferentialIndependent B x) :
    DifferentialIndependent B (successiveDifference x) := by
  classical
  unfold DifferentialIndependent at hx ⊢
  rw [algebraicIndependent_iff] at hx ⊢
  intro P hP
  have hcomp :
      (MvPolynomial.aeval (R := B)
        (fun p : ℕ × ℕ =>
          differentialJet p.2 (successiveDifference x p.1))) =
      (MvPolynomial.aeval (R := B)
        (fun p : ℕ × ℕ => differentialJet p.2 (x p.1))).comp
        successiveDifferenceAlgHom := by
    apply MvPolynomial.algHom_ext
    rintro ⟨n, r⟩
    rw [AlgHom.comp_apply, successiveDifferenceAlgHom_X]
    cases n with
    | zero =>
        simp [successiveDifferencePolynomial, successiveDifference]
    | succ n =>
        simp only [successiveDifferencePolynomial, map_sub, MvPolynomial.aeval_X]
        rw [differentialJet_successiveDifference]
        rfl
  rw [hcomp] at hP
  have hzero : successiveDifferenceAlgHom P = 0 := hx _ hP
  exact successiveDifferenceAlgHom_injective (by simpa using hzero)

end

end GaloisForLFunctions.HTGeometry

open scoped BigOperators ArithmeticFunction.Omega Differential ArithmeticFunction.Moebius
  UpperEndDifferentialInstances UpperEndComplexTowerInstances
  LSeries.notation ArithmeticFunction.zeta

namespace RHTower

open ArithmeticFunction
open Complex Filter LSeries
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Dilated Möbius leading-echelon law -/

/-- Sign-normalized dilated Möbius source.  Its first nonconstant prime-power coefficient is
`+1`, matching the canonical `Ω`-leading-echelon convention. -/
def negativeDilatedMoebiusArithmetic (m : ℕ) : ArithmeticFunction ℂ :=
  -mPart m ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)

theorem primeDeriv_rotatedNegativeDilatedMoebius_eq_zero_of_cardFactors_lt
    {m : ℕ} (hm : 0 < m) (q : Nat.Primes) (k n : ℕ)
    (hΩ : Ω n < m - 1) :
    primeDeriv q.1
        (rotatedLogArithmeticJet k (negativeDilatedMoebiusArithmetic m)) n = 0 := by
  rw [primeDeriv_apply]
  by_cases hn : n = 0
  · subst n
    simp
  by_cases hpow : ∃ a : ℕ, a ^ m = n * q.1
  · obtain ⟨a, ha⟩ := hpow
    have ha0 : a ≠ 0 := by
      intro haz
      subst a
      simp only [zero_pow hm.ne'] at ha
      exact (mul_ne_zero hn q.2.ne_zero) ha.symm
    have hcard : Ω n + 1 = m * Ω a := by
      calc
        Ω n + 1 = Ω (n * q.1) := by
          rw [cardFactors_mul hn q.2.ne_zero, cardFactors_apply_prime q.2]
        _ = Ω (a ^ m) := by rw [ha]
        _ = m * Ω a := cardFactors_pow
    have hlt : m * Ω a < m := by omega
    have hΩa : Ω a = 0 := by
      by_contra hne
      have hone : 1 ≤ Ω a := Nat.one_le_iff_ne_zero.mpr hne
      have hle : m ≤ m * Ω a := by
        simpa using Nat.mul_le_mul_left m hone
      omega
    have ha1 : a = 1 :=
      (cardFactors_eq_zero_iff_eq_zero_or_one.mp hΩa).resolve_left ha0
    subst a
    have hmul1 : n * q.1 = 1 := ha.symm.trans (one_pow m)
    have hqdvd : q.1 ∣ 1 := by
      refine ⟨n, ?_⟩
      exact hmul1.symm.trans (mul_comm n q.1)
    exact False.elim (q.2.ne_one (Nat.dvd_one.mp hqdvd))
  · have hzero :
        mPart m ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) (n * q.1) = 0 := by
      apply mPart_apply_of_forall_pow_ne
      intro a ha
      exact hpow ⟨a, ha⟩
    simp [negativeDilatedMoebiusArithmetic, rotatedLogArithmeticJet_apply, hzero]

theorem primeDeriv_rotatedNegativeDilatedMoebius_eq_pointMass_of_cardFactors_eq
    {m : ℕ} (hm : 0 < m) (q : Nat.Primes) (k n : ℕ)
    (hΩ : Ω n = m - 1) :
    primeDeriv q.1
        (rotatedLogArithmeticJet k (negativeDilatedMoebiusArithmetic m)) n =
      arithmeticPointMass (q.1 ^ (m - 1))
        ((m : ℂ) * (((m : ℂ) * rotatedPrimeLogClock q) ^ k)) n := by
  by_cases htarget : n = q.1 ^ (m - 1)
  · subst n
    rw [primeDeriv_apply]
    have hpow : q.1 ^ (m - 1) * q.1 = q.1 ^ m := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow, rotatedLogArithmeticJet_apply, negativeDilatedMoebiusArithmetic,
      ArithmeticFunction.neg_apply, mPart_apply_pow hm.ne']
    rw [arithmeticPointMass_apply_self (pow_ne_zero _ q.2.ne_zero)]
    have hfactor :
        ((q.1 ^ m).factorization q.1 : ℂ) = (m : ℂ) := by
      rw [q.2.factorization_pow]
      simp
    have hlog : (Real.log ((q.1 ^ m : ℕ) : ℝ) : ℂ) =
        (m : ℂ) * (Real.log q.1 : ℂ) := by
      rw [show ((q.1 ^ m : ℕ) : ℝ) = (q.1 : ℝ) ^ m by norm_num, Real.log_pow]
      exact_mod_cast rfl
    rw [hfactor, hlog]
    rw [show Complex.I * ((m : ℂ) * (Real.log q.1 : ℂ)) =
      (m : ℂ) * (Complex.I * (Real.log q.1 : ℂ)) by ring]
    simp [rotatedPrimeLogClock, primeLogClock, ArithmeticFunction.moebius_apply_prime q.2]
  · rw [arithmeticPointMass_apply_of_ne (pow_ne_zero _ q.2.ne_zero) htarget]
    rw [primeDeriv_apply]
    by_cases hn : n = 0
    · subst n
      simp
    by_cases hpow : ∃ a : ℕ, a ^ m = n * q.1
    · obtain ⟨a, ha⟩ := hpow
      have ha0 : a ≠ 0 := by
        intro haz
        subst a
        simp only [zero_pow hm.ne'] at ha
        exact (mul_ne_zero hn q.2.ne_zero) ha.symm
      have hcard : Ω n + 1 = m * Ω a := by
        calc
          Ω n + 1 = Ω (n * q.1) := by
            rw [cardFactors_mul hn q.2.ne_zero, cardFactors_apply_prime q.2]
          _ = Ω (a ^ m) := by rw [ha]
          _ = m * Ω a := cardFactors_pow
      have hmul : m * Ω a = m := by omega
      have hΩa : Ω a = 1 := by
        exact Nat.eq_of_mul_eq_mul_left hm (by simpa using hmul)
      have hpa : a.Prime := cardFactors_eq_one_iff_prime.mp hΩa
      have hqdvd : q.1 ∣ a ^ m := by
        rw [ha]
        exact dvd_mul_left q.1 n
      have hqa : q.1 = a := Nat.prime_eq_prime_of_dvd_pow q.2 hpa hqdvd
      exfalso
      apply htarget
      apply Nat.eq_of_mul_eq_mul_right q.2.pos
      calc
        n * q.1 = a ^ m := ha.symm
        _ = q.1 ^ m := (congrArg (fun t : ℕ => t ^ m) hqa).symm
        _ = q.1 ^ (m - 1) * q.1 := by
          rw [← pow_succ]
          congr 1
          omega
    · have hzero :
          mPart m ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) (n * q.1) = 0 := by
        apply mPart_apply_of_forall_pow_ne
        intro a ha
        exact hpow ⟨a, ha⟩
      simp [negativeDilatedMoebiusArithmetic, rotatedLogArithmeticJet_apply, hzero]

/-! ## Zeta-relative differential independence of the dilation ladder -/

/-- Unified leading-echelon family: zeta at level one and the sign-normalized dilated Möbius
carrier at every other level. -/
def zetaNegativeDilatedMoebiusArithmetic (m : ℕ) : ArithmeticFunction ℂ :=
  if m = 1 then zetaArith else negativeDilatedMoebiusArithmetic m

theorem primeDeriv_rotatedZetaNegativeDilatedMoebius_eq_zero_of_cardFactors_lt
    {m : ℕ} (hm : 0 < m) (q : Nat.Primes) (k n : ℕ)
    (hΩ : Ω n < m - 1) :
    primeDeriv q.1
        (rotatedLogArithmeticJet k (zetaNegativeDilatedMoebiusArithmetic m)) n = 0 := by
  by_cases hm1 : m = 1
  · omega
  · rw [zetaNegativeDilatedMoebiusArithmetic, if_neg hm1]
    exact primeDeriv_rotatedNegativeDilatedMoebius_eq_zero_of_cardFactors_lt
      hm q k n hΩ

theorem primeDeriv_rotatedZetaNegativeDilatedMoebius_eq_pointMass_of_cardFactors_eq
    {m : ℕ} (hm : 0 < m) (q : Nat.Primes) (k n : ℕ)
    (hΩ : Ω n = m - 1) :
    primeDeriv q.1
        (rotatedLogArithmeticJet k (zetaNegativeDilatedMoebiusArithmetic m)) n =
      arithmeticPointMass (q.1 ^ (m - 1))
        ((m : ℂ) * (((m : ℂ) * rotatedPrimeLogClock q) ^ k)) n := by
  by_cases hm1 : m = 1
  · subst m
    simp only [zetaNegativeDilatedMoebiusArithmetic, Nat.reduceSubDiff,
      pow_zero, Nat.cast_one, one_mul]
    exact primeDeriv_rotatedZetaJet_eq_pointMass_of_cardFactors_eq_zero q k n
      (by simpa using hΩ)
  · rw [zetaNegativeDilatedMoebiusArithmetic, if_neg hm1]
    exact primeDeriv_rotatedNegativeDilatedMoebius_eq_pointMass_of_cardFactors_eq
      hm q k n hΩ

theorem zetaNegativeDilatedMoebiusJets_algebraicIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (level : Fin d → ℕ) (hpos : ∀ r, 0 < level r)
    (hinj : Function.Injective level) (jet : ℕ) :
    AlgebraicIndependent ℂ
      (fun x : Fin d × Fin (jet + 1) =>
        rotatedLogArithmeticJet x.2
          (zetaNegativeDilatedMoebiusArithmetic (level x.1))) := by
  apply omegaLeadingJets_algebraicIndependent
    (fun r => zetaNegativeDilatedMoebiusArithmetic (level r))
    level hpos hinj
  · intro r q k n hn
    exact primeDeriv_rotatedZetaNegativeDilatedMoebius_eq_zero_of_cardFactors_lt
      (hpos r) q k n hn
  · intro r q k n hn
    exact primeDeriv_rotatedZetaNegativeDilatedMoebius_eq_pointMass_of_cardFactors_eq
      (hpos r) q k n hn

theorem zetaNegativeDilatedMoebiusArithmetic_differentialIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (level : Fin d → ℕ) (hpos : ∀ r, 0 < level r)
    (hinj : Function.Injective level) :
    DifferentialIndependent ℂ
      (fun r => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField
          (zetaNegativeDilatedMoebiusArithmetic (level r))) := by
  unfold DifferentialIndependent
  simp_rw [differentialJet_algebraMap_rotatedLogArithmeticJet]
  let x : Fin d → ℕ → arithmeticFunctionFractionField := fun r k =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (rotatedLogArithmeticJet k
        (zetaNegativeDilatedMoebiusArithmetic (level r)))
  apply algebraicIndependent_prod_nat_of_fin x
  intro jet
  have hraw :=
    zetaNegativeDilatedMoebiusJets_algebraicIndependent level hpos hinj jet
  have hmap := hraw.map'
    (f := IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
    (IsFractionRing.injective (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
  simpa only [Function.comp_apply, x] using! hmap

theorem zetaNegativeDilatedMoebiusArithmetic_differentialIndependent_fintype
    {I : Type*} [Fintype I] [Nonempty I]
    (level : I → ℕ) (hpos : ∀ i, 0 < level i)
    (hinj : Function.Injective level) :
    DifferentialIndependent ℂ
      (fun i => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField
          (zetaNegativeDilatedMoebiusArithmetic (level i))) := by
  classical
  let E : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have hfin :=
    zetaNegativeDilatedMoebiusArithmetic_differentialIndependent
      (fun r => level (E.symm r))
      (fun r => hpos (E.symm r))
      (hinj.comp E.symm.injective)
  have hcomp := hfin.comp E E.injective
  convert hcomp using 1
  funext i
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

/-- Finite-abscissa realization of the sign-normalized dilated Möbius source. -/
def negativeDilatedMoebiusFiniteAbscissaSource (m : ℕ) :
    finiteAbscissaArithmeticSubalgebra := by
  by_cases hm : m = 0
  · exact 0
  · refine ⟨negativeDilatedMoebiusArithmetic m, 1, ?_⟩
    intro y hy
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    · intro n hn
      have hbound := abs_mPartMoebiusCoeff_le_one hm n
      simpa [negativeDilatedMoebiusArithmetic, mPartMoebiusCoeff,
        ← mPart_intCoe] using hbound
    · simpa using hy

@[simp] theorem negativeDilatedMoebiusFiniteAbscissaSource_val
    {m : ℕ} (hm : m ≠ 0) :
    (negativeDilatedMoebiusFiniteAbscissaSource m).1 =
      negativeDilatedMoebiusArithmetic m := by
  simp [negativeDilatedMoebiusFiniteAbscissaSource, hm]

def zetaNegativeDilatedMoebiusFiniteAbscissaSource (m : ℕ) :
    finiteAbscissaArithmeticSubalgebra :=
  if m = 1 then zetaSource else negativeDilatedMoebiusFiniteAbscissaSource m

@[simp] theorem zetaNegativeDilatedMoebiusFiniteAbscissaSource_val
    {m : ℕ} (hm : 0 < m) :
    (zetaNegativeDilatedMoebiusFiniteAbscissaSource m).1 =
      zetaNegativeDilatedMoebiusArithmetic m := by
  by_cases hm1 : m = 1
  · subst m
    simp [zetaNegativeDilatedMoebiusFiniteAbscissaSource,
      zetaNegativeDilatedMoebiusArithmetic]
  · simp [zetaNegativeDilatedMoebiusFiniteAbscissaSource,
      zetaNegativeDilatedMoebiusArithmetic, hm1,
      negativeDilatedMoebiusFiniteAbscissaSource_val hm.ne']

def zetaNegativeDilatedMoebiusUpperEndCarrier (m : ℕ) :
    upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero
    (zetaNegativeDilatedMoebiusFiniteAbscissaSource m)

theorem zetaNegativeDilatedMoebiusUpperEndCarrier_differentialIndependent
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (level : I → ℕ) (hpos : ∀ i, 0 < level i)
    (hinj : Function.Injective level) :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun i => zetaNegativeDilatedMoebiusUpperEndCarrier (level i)) := by
  apply differentialIndependent_finiteAbscissaPrimeProfiles_of_formal
  have h :=
    zetaNegativeDilatedMoebiusArithmetic_differentialIndependent_fintype
      level hpos hinj
  convert h using 1
  funext i
  rw [zetaNegativeDilatedMoebiusFiniteAbscissaSource_val (hpos i)]

theorem zetaNegativeDilatedMoebiusUpperEndCarrier_differentialIndependent_of_injective
    {I : Type*} (level : I → ℕ)
    (hpos : ∀ i, 0 < level i) (hinj : Function.Injective level) :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun i => zetaNegativeDilatedMoebiusUpperEndCarrier (level i)) := by
  classical
  apply differentialIndependent_of_forall_finite_subfamily
  intro J hJfinite
  by_cases hJempty : J = ∅
  · subst J
    exact algebraicIndependent_empty_type
  letI : Fintype J := hJfinite.fintype
  letI : Nonempty J :=
    Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr hJempty)
  apply zetaNegativeDilatedMoebiusUpperEndCarrier_differentialIndependent
    (fun j : J => level j)
  · intro j
    exact hpos j
  · intro i j hij
    exact Subtype.ext (hinj hij)

def negativeDilatedMoebiusUpperEndCarrier (m : ℕ) : upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero
    (negativeDilatedMoebiusFiniteAbscissaSource m)

/-- Upper-end realization of the actual dilated Möbius carrier `ζ(ms)⁻¹`. -/
def dilatedMoebiusUpperEndCarrier (m : ℕ) : upperEndMeroField :=
  -negativeDilatedMoebiusUpperEndCarrier m

/-- Finite-abscissa source of the actual dilated Möbius carrier `ζ(ms)⁻¹`. -/
def dilatedMoebiusFiniteAbscissaSource (m : ℕ) :
    finiteAbscissaArithmeticSubalgebra :=
  -negativeDilatedMoebiusFiniteAbscissaSource m

@[simp] theorem dilatedMoebiusFiniteAbscissaSource_val
    {m : ℕ} (hm : m ≠ 0) :
    (dilatedMoebiusFiniteAbscissaSource m).1 =
      mPart m ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) := by
  simp [dilatedMoebiusFiniteAbscissaSource,
    negativeDilatedMoebiusFiniteAbscissaSource_val hm,
    negativeDilatedMoebiusArithmetic]

/-- The independent upper-end carrier is exactly the analytic realization of the dilated
Möbius coefficient source. -/
theorem dilatedMoebiusUpperEndCarrier_eq_source
    (m : ℕ) :
    dilatedMoebiusUpperEndCarrier m =
      finiteAbscissaLSeriesToUpperEndMero
        (dilatedMoebiusFiniteAbscissaSource m) := by
  change -finiteAbscissaLSeriesToUpperEndMero
      (negativeDilatedMoebiusFiniteAbscissaSource m) =
    finiteAbscissaLSeriesToUpperEndMero
      (-negativeDilatedMoebiusFiniteAbscissaSource m)
  exact (map_neg finiteAbscissaLSeriesToUpperEndMero
    (negativeDilatedMoebiusFiniteAbscissaSource m)).symm

@[simp] theorem zetaNegativeDilatedMoebiusUpperEndCarrier_one :
    zetaNegativeDilatedMoebiusUpperEndCarrier 1 = zetaUpperEndMero := by
  rfl

theorem zetaNegativeDilatedMoebiusUpperEndCarrier_eq_negative
    {m : ℕ} (hm : m ≠ 1) :
    zetaNegativeDilatedMoebiusUpperEndCarrier m =
      negativeDilatedMoebiusUpperEndCarrier m := by
  simp [zetaNegativeDilatedMoebiusUpperEndCarrier,
    zetaNegativeDilatedMoebiusFiniteAbscissaSource,
    negativeDilatedMoebiusUpperEndCarrier, hm]

theorem zeta_negativeDilatedMoebiusTail_differentialIndependent
    (K : ℕ) (hK : 2 ≤ K) :
    DifferentialIndependent upperEndRationalCoordinateField
      (Sum.elim (fun _ : Unit => zetaUpperEndMero)
        (fun n : ℕ => negativeDilatedMoebiusUpperEndCarrier (K + n))) := by
  let level : Unit ⊕ ℕ → ℕ :=
    Sum.elim (fun _ : Unit => 1) (fun n : ℕ => K + n)
  have hpos : ∀ i, 0 < level i := by
    rintro (u | n)
    · simp [level]
    · dsimp only [level, Sum.elim_inr]
      omega
  have hinj : Function.Injective level := by
    rintro (u | m) (v | n) h
    · exact congrArg Sum.inl (Subsingleton.elim u v)
    · dsimp only [level, Sum.elim_inl, Sum.elim_inr] at h
      omega
    · dsimp only [level, Sum.elim_inl, Sum.elim_inr] at h
      omega
    · congr 1
      dsimp only [level, Sum.elim_inr] at h
      omega
  have h :=
    zetaNegativeDilatedMoebiusUpperEndCarrier_differentialIndependent_of_injective
      level hpos hinj
  convert h using 1
  funext i
  rcases i with u | n
  · simp [level]
  · have hne : K + n ≠ 1 := by omega
    simpa [level] using
      (zetaNegativeDilatedMoebiusUpperEndCarrier_eq_negative hne).symm

/-- The full dilated Möbius tail remains differentially independent after zeta and all of its
derivatives are adjoined to the base field. -/
theorem negativeDilatedMoebiusTail_relativeDifferentialIndependent
    (K : ℕ) (hK : 2 ≤ K) :
    DifferentialIndependent zetaUpperEndDifferentialField
      (fun n : ℕ => negativeDilatedMoebiusUpperEndCarrier (K + n)) := by
  exact
    (GaloisForLFunctions.differentialIndependent_sumElim_iff
      (fun _ : Unit => zetaUpperEndMero)
      (fun n : ℕ => negativeDilatedMoebiusUpperEndCarrier (K + n))).mp
      (zeta_negativeDilatedMoebiusTail_differentialIndependent K hK) |>.2

/-- Sign removal preserves relative differential independence. -/
theorem dilatedMoebiusTail_relativeDifferentialIndependent
    (K : ℕ) (hK : 2 ≤ K) :
    DifferentialIndependent zetaUpperEndDifferentialField
      (fun n : ℕ => dilatedMoebiusUpperEndCarrier (K + n)) := by
  letI : Differential zetaUpperEndDifferentialField :=
    derivationClosedDifferential
      (differentialAdjoin upperEndRationalCoordinateField
        (Set.range (fun _ : Unit => zetaUpperEndMero)))
      (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
        (Set.range (fun _ : Unit => zetaUpperEndMero)))
  letI : DifferentialAlgebra zetaUpperEndDifferentialField upperEndMeroField :=
    ⟨fun z => derivationClosedDifferential_apply
      (differentialAdjoin upperEndRationalCoordinateField
        (Set.range (fun _ : Unit => zetaUpperEndMero)))
      (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
        (Set.range (fun _ : Unit => zetaUpperEndMero))) z⟩
  let a : ℕ → zetaUpperEndDifferentialField := fun _ => -1
  have ha : ∀ n, a n ≠ 0 := fun _ => by simp [a]
  have hscaled :=
    (negativeDilatedMoebiusTail_relativeDifferentialIndependent K hK).mulBase a ha
  simpa [a, dilatedMoebiusUpperEndCarrier] using hscaled

/-- Normalized complete-resolution family: `ζ(Ks)⁻¹` first, followed by the adjacent reciprocal
dilation differences. -/
def completeResolutionUpperEndMultiplier (K : ℕ) : ℕ → upperEndMeroField :=
  successiveDifference (fun n => dilatedMoebiusUpperEndCarrier (K + n))

@[simp] theorem completeResolutionUpperEndMultiplier_zero (K : ℕ) :
    completeResolutionUpperEndMultiplier K 0 =
      dilatedMoebiusUpperEndCarrier K := by
  rfl

@[simp] theorem completeResolutionUpperEndMultiplier_succ (K n : ℕ) :
    completeResolutionUpperEndMultiplier K (n + 1) =
      dilatedMoebiusUpperEndCarrier (K + n + 1) -
        dilatedMoebiusUpperEndCarrier (K + n) := by
  rfl

/-- **Complete relative-rank theorem.**  The `K`-free head multiplier together with every
successive exponent-shell multiplier has maximal countable differential rank over the full zeta
differential field. -/
theorem completeResolutionUpperEndMultiplier_relativeDifferentialIndependent
    (K : ℕ) (hK : 2 ≤ K) :
    DifferentialIndependent zetaUpperEndDifferentialField
      (completeResolutionUpperEndMultiplier K) := by
  exact differentialIndependent_successiveDifference _
    (dilatedMoebiusTail_relativeDifferentialIndependent K hK)

/-! ## Exact positive coefficient resolution -/

/-- `K`-free head at index zero, followed by exact largest-exponent shells. -/
def completeResolutionIndicator (K : ℕ) : ℕ → ArithmeticFunction ℤ
  | 0 => mFreeIndicator K
  | j + 1 => shellIndicator (K + j)

theorem completeResolutionIndicator_eq_zero_or_one
    {K : ℕ} (j n : ℕ) :
    completeResolutionIndicator K j n = 0 ∨
      completeResolutionIndicator K j n = 1 := by
  cases j with
  | zero =>
      rw [completeResolutionIndicator, mFreeIndicator_apply]
      split_ifs <;> simp
  | succ j =>
      exact shellIndicator_eq_zero_or_one (K + j) n

/-- Distinct complete-resolution channels have disjoint coefficient supports. -/
theorem completeResolutionIndicator_pairwiseDisjoint
    {K i j n : ℕ} (hij : i ≠ j)
    (hi : completeResolutionIndicator K i n ≠ 0) :
    completeResolutionIndicator K j n = 0 := by
  cases i with
  | zero =>
      cases j with
      | zero => exact False.elim (hij rfl)
      | succ j =>
          by_contra hj
          have hhead :
              completeResolutionIndicator K 0 n = 1 :=
            (completeResolutionIndicator_eq_zero_or_one 0 n).resolve_left hi
          have htail :
              completeResolutionIndicator K (j + 1) n = 1 :=
            (completeResolutionIndicator_eq_zero_or_one (j + 1) n).resolve_left hj
          have hfreeK : MFree K n := by
            simpa [completeResolutionIndicator, mFreeIndicator_apply] using hhead
          have hnot : ¬ MFree (K + j) n :=
            (shellIndicator_eq_one_iff (K + j) n).mp
              (by simpa [completeResolutionIndicator] using htail) |>.2
          exact hnot (mFree_of_le (Nat.le_add_right K j) hfreeK)
  | succ i =>
      cases j with
      | zero =>
          by_contra hj
          have htail :
              completeResolutionIndicator K (i + 1) n = 1 :=
            (completeResolutionIndicator_eq_zero_or_one (i + 1) n).resolve_left hi
          have hhead :
              completeResolutionIndicator K 0 n = 1 :=
            (completeResolutionIndicator_eq_zero_or_one 0 n).resolve_left hj
          have hnot : ¬ MFree (K + i) n :=
            (shellIndicator_eq_one_iff (K + i) n).mp
              (by simpa [completeResolutionIndicator] using htail) |>.2
          have hfreeK : MFree K n := by
            simpa [completeResolutionIndicator, mFreeIndicator_apply] using hhead
          exact hnot (mFree_of_le (Nat.le_add_right K i) hfreeK)
      | succ j =>
          have hlevels : K + i ≠ K + j := by
            intro h
            apply hij
            congr 1
            omega
          exact shellIndicator_eq_zero_of_ne hlevels
            (by simpa [completeResolutionIndicator] using hi)

theorem sum_range_completeResolutionIndicator (K M n : ℕ) :
    ∑ j ∈ Finset.range (M + 1), completeResolutionIndicator K j n =
      mFreeIndicator (K + M) n := by
  induction M with
  | zero => simp [completeResolutionIndicator]
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [completeResolutionIndicator, shellIndicator_apply]
      ring

/-- **Exact complete fusion.**  Every positive integer belongs to exactly one channel, and the
infinite coefficient sum is locally finite and equal to the zeta coefficient. -/
theorem tsum_completeResolutionIndicator
    {K : ℕ} (n : ℕ) :
    (∑' j : ℕ, completeResolutionIndicator K j n) =
      (ζ : ArithmeticFunction ℤ) n := by
  rw [tsum_eq_sum (s := Finset.range (Ω n + 2))]
  · rw [show Ω n + 2 = (Ω n + 1) + 1 by omega,
      sum_range_completeResolutionIndicator]
    by_cases hn : n = 0
    · subst n
      simp
    · have hfree : MFree (K + (Ω n + 1)) n :=
        mFree_of_le (by omega) (mFree_cardFactors_succ hn)
      rw [mFreeIndicator_apply, if_pos hfree]
      simp [ArithmeticFunction.zeta_apply, hn]
  · intro j hj
    have hjlower : Ω n + 2 ≤ j := by
      simpa using hj
    cases j with
    | zero => omega
    | succ j =>
        by_contra hnonzero
        have hlower := shellIndicator_cardFactors_lower
          (m := K + j) (n := n)
          (by simpa [completeResolutionIndicator] using hnonzero)
        omega

/-- Arithmetic normalized channel: dilated Möbius head followed by adjacent differences. -/
def completeResolutionNormalizedArithmetic (K : ℕ) :
    ℕ → ArithmeticFunction ℤ
  | 0 => mPart K (μ : ArithmeticFunction ℤ)
  | j + 1 =>
      mPart (K + j + 1) (μ : ArithmeticFunction ℤ) -
        mPart (K + j) (μ : ArithmeticFunction ℤ)

/-- Every positive channel is zeta convolved with its normalized Möbius channel. -/
theorem completeResolutionNormalizedArithmetic_mul_zeta
    {K : ℕ} (hK : K ≠ 0) (j : ℕ) :
    completeResolutionNormalizedArithmetic K j *
        (ζ : ArithmeticFunction ℤ) =
      completeResolutionIndicator K j := by
  cases j with
  | zero =>
      exact mPart_moebius_mul_zeta hK
  | succ j =>
      rw [completeResolutionNormalizedArithmetic, sub_mul,
        mPart_moebius_mul_zeta (by omega : K + j + 1 ≠ 0),
        mPart_moebius_mul_zeta (by omega : K + j ≠ 0)]
      rfl

/-- Finite-abscissa source of each normalized complete-resolution channel. -/
def completeResolutionNormalizedFiniteAbscissaSource (K : ℕ) :
    ℕ → finiteAbscissaArithmeticSubalgebra
  | 0 => dilatedMoebiusFiniteAbscissaSource K
  | j + 1 =>
      dilatedMoebiusFiniteAbscissaSource (K + j + 1) -
        dilatedMoebiusFiniteAbscissaSource (K + j)

/-- The finite-abscissa source has exactly the complex-cast normalized arithmetic
coefficients. -/
@[simp] theorem completeResolutionNormalizedFiniteAbscissaSource_val
    {K : ℕ} (hK : K ≠ 0) (j : ℕ) :
    (completeResolutionNormalizedFiniteAbscissaSource K j).1 =
      ((completeResolutionNormalizedArithmetic K j :
        ArithmeticFunction ℤ) : ArithmeticFunction ℂ) := by
  cases j with
  | zero =>
      simp [completeResolutionNormalizedFiniteAbscissaSource,
        completeResolutionNormalizedArithmetic,
        dilatedMoebiusFiniteAbscissaSource_val hK,
        mPart_intCoe]
  | succ j =>
      rw [completeResolutionNormalizedFiniteAbscissaSource,
        completeResolutionNormalizedArithmetic,
        Subalgebra.coe_sub,
        dilatedMoebiusFiniteAbscissaSource_val (by omega : K + j + 1 ≠ 0),
        dilatedMoebiusFiniteAbscissaSource_val (by omega : K + j ≠ 0),
        ← mPart_intCoe, ← mPart_intCoe]
      ext n
      exact (Int.cast_sub
        ((mPart (K + j + 1) (μ : ArithmeticFunction ℤ)) n)
        ((mPart (K + j) (μ : ArithmeticFunction ℤ)) n)).symm

/-- The maximal-rank upper-end family is the faithful analytic realization of the same
normalized arithmetic family appearing in the convolution law. -/
theorem completeResolutionUpperEndMultiplier_eq_source
    (K j : ℕ) :
    completeResolutionUpperEndMultiplier K j =
      finiteAbscissaLSeriesToUpperEndMero
        (completeResolutionNormalizedFiniteAbscissaSource K j) := by
  cases j with
  | zero =>
      simp [completeResolutionUpperEndMultiplier,
        GaloisForLFunctions.HTGeometry.successiveDifference,
        completeResolutionNormalizedFiniteAbscissaSource,
        dilatedMoebiusUpperEndCarrier_eq_source]
  | succ j =>
      rw [completeResolutionUpperEndMultiplier_succ,
        dilatedMoebiusUpperEndCarrier_eq_source,
        dilatedMoebiusUpperEndCarrier_eq_source]
      change finiteAbscissaLSeriesToUpperEndMero
          (dilatedMoebiusFiniteAbscissaSource (K + j + 1)) -
        finiteAbscissaLSeriesToUpperEndMero
          (dilatedMoebiusFiniteAbscissaSource (K + j)) =
        finiteAbscissaLSeriesToUpperEndMero
          (dilatedMoebiusFiniteAbscissaSource (K + j + 1) -
            dilatedMoebiusFiniteAbscissaSource (K + j))
      exact (map_sub finiteAbscissaLSeriesToUpperEndMero
        (dilatedMoebiusFiniteAbscissaSource (K + j + 1))
        (dilatedMoebiusFiniteAbscissaSource (K + j))).symm

/-! ## Half-plane units and divisor equality -/

/-- Analytic normalized multiplier of the complete resolution. -/
def completeResolutionMultiplier (K : ℕ) : ℕ → ℂ → ℂ
  | 0 => fun s => (riemannZeta ((K : ℂ) * s))⁻¹
  | j + 1 => shellMultiplier (K + j)

/-- On the half-plane of absolute convergence, the normalized arithmetic source is exactly the
explicit reciprocal-dilation multiplier used in the divisor theorem. -/
theorem LSeries_completeResolutionNormalizedArithmetic
    {K : ℕ} (hK : K ≠ 0) (j : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(completeResolutionNormalizedArithmetic K j) s =
      completeResolutionMultiplier K j s := by
  cases j with
  | zero =>
      exact LSeries_mPart_moebius hK
        (one_div_natCast_lt_re hK hs)
  | succ j =>
      have hleft : LSeriesSummable
          ↗(mPart (K + j + 1) (μ : ArithmeticFunction ℤ)) s :=
        LSeriesSummable_mPart_moebius (by omega)
          (one_div_natCast_lt_re (by omega) hs)
      have hright : LSeriesSummable
          ↗(mPart (K + j) (μ : ArithmeticFunction ℤ)) s :=
        LSeriesSummable_mPart_moebius (by omega)
          (one_div_natCast_lt_re (by omega) hs)
      have hfun :
          ↗(completeResolutionNormalizedArithmetic K (j + 1)) =
            ↗(mPart (K + j + 1) (μ : ArithmeticFunction ℤ)) -
              ↗(mPart (K + j) (μ : ArithmeticFunction ℤ)) := by
        funext n
        change
          (((mPart (K + j + 1) (μ : ArithmeticFunction ℤ)) n -
            (mPart (K + j) (μ : ArithmeticFunction ℤ)) n : ℤ) : ℂ) =
          ((mPart (K + j + 1) (μ : ArithmeticFunction ℤ)) n : ℂ) -
            ((mPart (K + j) (μ : ArithmeticFunction ℤ)) n : ℂ)
        exact Int.cast_sub _ _
      rw [hfun, LSeries_sub hleft hright,
        LSeries_mPart_moebius (by omega)
          (one_div_natCast_lt_re (by omega) hs),
        LSeries_mPart_moebius (by omega)
          (one_div_natCast_lt_re (by omega) hs),
        completeResolutionMultiplier, shellMultiplier]
      push_cast
      rfl

/-! ## Infinite analytic completion -/

/-- Elementary right-end estimate: zeta tends to one at a rate controlled only by the real
part. -/
theorem norm_riemannZeta_sub_one_le
    {w : ℂ} (hw : 1 < w.re) :
    ‖riemannZeta w - 1‖ ≤ 1 / (w.re - 1) := by
  have hre0 : w.re ≠ 0 := by linarith
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ w) :=
    summable_one_div_nat_cpow.mpr hw
  have htailSum : Summable (fun i : ℕ => 1 / ((i + 2 : ℕ) : ℂ) ^ w) := by
    simpa [Function.comp_def] using hsum.comp_injective
      (fun i j hij => Nat.add_right_cancel hij :
        Function.Injective (fun i : ℕ => i + 2))
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  have h01 : ∑ i ∈ Finset.range 2, 1 / (i : ℂ) ^ w = 1 := by
    simp [Finset.sum_range_succ, Complex.zero_cpow hw0]
  have htailEq :
      riemannZeta w - 1 =
        ∑' i : ℕ, 1 / ((i + 2 : ℕ) : ℂ) ^ w := by
    rw [zeta_eq_tsum_one_div_nat_cpow hw, ← hsplit, h01]
    ring
  have hterm : ∀ i : ℕ,
      ‖1 / ((i + 2 : ℕ) : ℂ) ^ w‖ =
        1 / ((i + 2 : ℕ) : ℝ) ^ w.re := by
    intro i
    rw [norm_div, norm_one,
      Complex.norm_natCast_cpow_of_pos (by omega : 0 < i + 2)]
  rw [htailEq]
  calc
    ‖∑' i : ℕ, 1 / ((i + 2 : ℕ) : ℂ) ^ w‖
        ≤ ∑' i : ℕ, ‖1 / ((i + 2 : ℕ) : ℂ) ^ w‖ :=
      norm_tsum_le_tsum_norm htailSum.norm
    _ = ∑' i : ℕ, 1 / ((i + 2 : ℕ) : ℝ) ^ w.re :=
      tsum_congr hterm
    _ ≤ 1 / (w.re - 1) := by
      have hb := tsum_add_rpow_neg_le hw (M := 1) le_rfl
      rw [Nat.cast_one, Real.one_rpow] at hb
      refine le_trans (le_of_eq (tsum_congr fun i => ?_)) hb
      rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]

/-- Zeta tends to one along every integral dilation of a point in the open right half-plane. -/
theorem tendsto_riemannZeta_nat_dilation_one
    {K : ℕ} {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun n : ℕ => riemannZeta (((K + n : ℕ) : ℂ) * s))
      Filter.atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hre :
      Filter.Tendsto (fun n : ℕ => (((K + n : ℕ) : ℂ) * s).re)
        Filter.atTop Filter.atTop := by
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    have hadd : Filter.Tendsto (fun n : ℕ => K + n)
        Filter.atTop Filter.atTop :=
      by simpa [Nat.add_comm] using tendsto_add_atTop_nat K
    exact (tendsto_natCast_atTop_atTop.comp hadd).atTop_mul_const hs
  obtain ⟨N, hN⟩ :=
    (Filter.eventually_atTop.1
      (hre.eventually_gt_atTop (1 + 1 / ε)))
  refine ⟨N, fun n hn => ?_⟩
  have hn := hN n hn
  have hw : 1 < (((K + n : ℕ) : ℂ) * s).re := by
    have : 0 < 1 / ε := one_div_pos.mpr hε
    linarith
  have hbound := norm_riemannZeta_sub_one_le hw
  rw [dist_eq]
  refine hbound.trans_lt ?_
  have hden : 1 / ε < (((K + n : ℕ) : ℂ) * s).re - 1 := by
    linarith
  have hdenpos : 0 < (((K + n : ℕ) : ℂ) * s).re - 1 := by
    linarith
  exact (one_div_lt hdenpos hε).2 hden

/-- Reciprocal zeta has the same integral-dilation limit. -/
theorem tendsto_inv_riemannZeta_nat_dilation_one
    {K : ℕ} {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun n : ℕ => (riemannZeta (((K + n : ℕ) : ℂ) * s))⁻¹)
      Filter.atTop (nhds 1) := by
  simpa using
    (tendsto_riemannZeta_nat_dilation_one (K := K) hs).inv₀ one_ne_zero

/-- Quantitative reciprocal form of the right-end estimate. -/
theorem norm_inv_riemannZeta_sub_one_le
    {w : ℂ} (hw : 3 ≤ w.re) :
    ‖(riemannZeta w)⁻¹ - 1‖ ≤ 2 / (w.re - 1) := by
  have hw1 : 1 < w.re := by linarith
  have hζ : riemannZeta w ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hw1
  have htail := norm_riemannZeta_sub_one_le hw1
  have hden : 2 ≤ w.re - 1 := by linarith
  have hdenpos : 0 < w.re - 1 := by linarith
  have htailHalf : ‖riemannZeta w - 1‖ ≤ 1 / 2 := by
    refine htail.trans ?_
    exact (one_div_le hdenpos (by norm_num : (0 : ℝ) < 1 / 2)).2
      (by simpa using hden)
  have hreverse := norm_sub_norm_le (1 : ℂ) (riemannZeta w)
  have hsubnorm : ‖(1 : ℂ) - riemannZeta w‖ =
      ‖riemannZeta w - 1‖ := by
    rw [← norm_neg]
    congr 1
    ring
  rw [norm_one, hsubnorm] at hreverse
  have hζlower : 1 / 2 ≤ ‖riemannZeta w‖ := by
    linarith
  have hζnormpos : 0 < ‖riemannZeta w‖ := norm_pos_iff.mpr hζ
  have hinvnorm : ‖(riemannZeta w)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    simpa [one_div] using
      ((one_div_le hζnormpos (by norm_num : (0 : ℝ) < 2)).2 hζlower)
  have hid :
      (riemannZeta w)⁻¹ - 1 =
        (riemannZeta w)⁻¹ * (1 - riemannZeta w) := by
    field_simp [hζ]
  rw [hid, norm_mul, hsubnorm]
  calc
    ‖(riemannZeta w)⁻¹‖ * ‖riemannZeta w - 1‖
        ≤ 2 * ‖riemannZeta w - 1‖ :=
      mul_le_mul_of_nonneg_right hinvnorm (norm_nonneg _)
    _ ≤ 2 * (1 / (w.re - 1)) :=
      mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = 2 / (w.re - 1) := by ring

/-- Every finite prefix of the complete multipliers telescopes to one reciprocal dilation. -/
theorem sum_range_completeResolutionMultiplier
    (K N : ℕ) (s : ℂ) :
    ∑ j ∈ Finset.range (N + 1), completeResolutionMultiplier K j s =
      (riemannZeta (((K + N : ℕ) : ℂ) * s))⁻¹ := by
  induction N with
  | zero =>
      simp [completeResolutionMultiplier]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [completeResolutionMultiplier, shellMultiplier]
      push_cast
      ring

/-- **Infinite analytic completion law.**  Although every finite subfamily is differentially
independent, the ordered analytic completion is the exact partition of unity on `re s > 0`. -/
theorem tendsto_sum_range_completeResolutionMultiplier_one
    (K : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ j ∈ Finset.range (N + 1), completeResolutionMultiplier K j s)
      Filter.atTop (nhds 1) := by
  simpa only [sum_range_completeResolutionMultiplier] using
    (tendsto_inv_riemannZeta_nat_dilation_one (K := K) hs)

/-- **Uniform half-plane completion.**  The ordered partition of unity converges uniformly on
every closed half-plane contained in `re s > 0`; hence it converges locally uniformly on that
domain. -/
theorem completeResolutionMultiplier_uniformOn_rightHalfPlane
    (K : ℕ) {sigma0 : ℝ} (hsigma0 : 0 < sigma0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s : ℂ, sigma0 ≤ s.re →
        ‖(∑ j ∈ Finset.range (n + 1),
            completeResolutionMultiplier K j s) - 1‖ < ε := by
  intro ε hε
  have hre :
      Filter.Tendsto (fun n : ℕ => ((K + n : ℕ) : ℝ) * sigma0)
        Filter.atTop Filter.atTop := by
    have hadd : Filter.Tendsto (fun n : ℕ => K + n)
        Filter.atTop Filter.atTop :=
      by simpa [Nat.add_comm] using tendsto_add_atTop_nat K
    exact (tendsto_natCast_atTop_atTop.comp hadd).atTop_mul_const hsigma0
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.1
      (hre.eventually_gt_atTop (max 3 (1 + 2 / ε)))
  refine ⟨N, fun n hn s hs => ?_⟩
  have hnlarge := hN n hn
  have hnthree : 3 < ((K + n : ℕ) : ℝ) * sigma0 :=
    lt_of_le_of_lt (le_max_left _ _) hnlarge
  have hneps : 1 + 2 / ε < ((K + n : ℕ) : ℝ) * sigma0 :=
    lt_of_le_of_lt (le_max_right _ _) hnlarge
  have hscale : ((K + n : ℕ) : ℝ) * sigma0 ≤
      (((K + n : ℕ) : ℂ) * s).re := by
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    have hnonneg : (0 : ℝ) ≤ (K + n : ℕ) := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_left hs hnonneg
  have hwthree : 3 ≤ (((K + n : ℕ) : ℂ) * s).re := by
    linarith
  rw [sum_range_completeResolutionMultiplier]
  have hbound := norm_inv_riemannZeta_sub_one_le hwthree
  refine hbound.trans_lt ?_
  have hden : 2 / ε <
      (((K + n : ℕ) : ℂ) * s).re - 1 := by
    linarith
  have hdenpos : 0 <
      (((K + n : ℕ) : ℂ) * s).re - 1 := by
    linarith
  have hepshalf : 0 < ε / 2 := by linarith
  have hinvlt : 1 /
      ((((K + n : ℕ) : ℂ) * s).re - 1) < ε / 2 := by
    apply (one_div_lt hdenpos hepshalf).2
    simpa [one_div, div_eq_mul_inv] using hden
  have htwo : (0 : ℝ) < 2 := by norm_num
  have := mul_lt_mul_of_pos_left hinvlt htwo
  convert this using 1 <;> ring

theorem completeResolutionMultiplier_head_ne_zero
    {K : ℕ} (hK : 2 ≤ K) {s : ℂ} (hs : 1 / 2 < s.re) :
    completeResolutionMultiplier K 0 s ≠ 0 := by
  have hKr : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hK)
  have hmul :
      (K : ℝ) * (1 / 2 : ℝ) < (K : ℝ) * s.re :=
    mul_lt_mul_of_pos_left hs hKr
  have hre : (((K : ℂ) * s).re) = (K : ℝ) * s.re := by
    simp [Complex.mul_re]
  have hscaled : 1 < (((K : ℂ) * s).re) := by
    rw [hre]
    have hKcast : (2 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  exact inv_ne_zero (riemannZeta_ne_zero_of_one_lt_re hscaled)

theorem analyticAt_completeResolutionMultiplier_head
    {K : ℕ} (hK : 2 ≤ K) {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ (completeResolutionMultiplier K 0) s := by
  have hKr : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hK)
  have hmul :
      (K : ℝ) * (1 / 2 : ℝ) < (K : ℝ) * s.re :=
    mul_lt_mul_of_pos_left hs hKr
  have hre : (((K : ℂ) * s).re) = (K : ℝ) * s.re := by
    simp [Complex.mul_re]
  have hscaled : 1 < (((K : ℂ) * s).re) := by
    rw [hre]
    have hKcast : (2 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  have hne1 : (K : ℂ) * s ≠ 1 := by
    intro h
    rw [h] at hscaled
    norm_num at hscaled
  have hlin : AnalyticAt ℂ (fun z : ℂ => (K : ℂ) * z) s :=
    analyticAt_const.mul analyticAt_id
  have hcomp : AnalyticAt ℂ (fun z : ℂ => riemannZeta ((K : ℂ) * z)) s :=
    (analyticOn_riemannZeta _ hne1).comp hlin
  exact hcomp.inv (riemannZeta_ne_zero_of_one_lt_re hscaled)

theorem analyticOrderAt_mul_completeResolutionMultiplier_head
    {K : ℕ} (hK : 2 ≤ K) {s : ℂ} (hs : 1 / 2 < s.re)
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f s) :
    analyticOrderAt
        (fun z => f z * completeResolutionMultiplier K 0 z) s =
      analyticOrderAt f s := by
  have hH := analyticAt_completeResolutionMultiplier_head hK hs
  have hmul :
      analyticOrderAt (f * completeResolutionMultiplier K 0) s =
        analyticOrderAt f s +
          analyticOrderAt (completeResolutionMultiplier K 0) s :=
    analyticOrderAt_mul hf hH
  have hzero :
      analyticOrderAt (completeResolutionMultiplier K 0) s = 0 :=
    hH.analyticOrderAt_eq_zero.mpr
      (completeResolutionMultiplier_head_ne_zero hK hs)
  rw [show (fun z => f z * completeResolutionMultiplier K 0 z) =
      f * completeResolutionMultiplier K 0 from rfl,
    hmul, hzero, add_zero]

/-- Every normalized channel is a holomorphic unit on the RH half-plane. -/
theorem completeResolutionMultiplier_ne_zero
    {K : ℕ} (hK : 12 ≤ K) (j : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    completeResolutionMultiplier K j s ≠ 0 := by
  cases j with
  | zero =>
      exact completeResolutionMultiplier_head_ne_zero (by omega) hs
  | succ j =>
      exact shellMultiplier_ne_zero (by omega) hs

/-- Multiplication by any normalized channel preserves analytic vanishing order throughout the
strict right half-plane. -/
theorem analyticOrderAt_mul_completeResolutionMultiplier
    {K : ℕ} (hK : 12 ≤ K) (j : ℕ) {s : ℂ} (hs : 1 / 2 < s.re)
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f s) :
    analyticOrderAt
        (fun z => f z * completeResolutionMultiplier K j z) s =
      analyticOrderAt f s := by
  cases j with
  | zero =>
      exact analyticOrderAt_mul_completeResolutionMultiplier_head (by omega) hs hf
  | succ j =>
      exact analyticOrderAt_mul_shellMultiplier (by omega) hs hf

/-- Exact Dirichlet-series factorization of every positive channel on the half-plane of absolute
convergence. -/
theorem LSeries_completeResolutionIndicator
    {K : ℕ} (hK : K ≠ 0) (j : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(completeResolutionIndicator K j) s =
      riemannZeta s * completeResolutionMultiplier K j s := by
  cases j with
  | zero =>
      exact LSeries_mFree_eq_riemannZeta_div hK hs
  | succ j =>
      exact LSeries_shellIndicator (by omega : K + j ≠ 0) hs

/-- Every complete-resolution channel carries the exact zeta divisor, including multiplicity. -/
theorem analyticOrderAt_riemannZeta_completeResolutionChannel
    {K : ℕ} (hK : 12 ≤ K) (j : ℕ) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt
        (fun z => riemannZeta z * completeResolutionMultiplier K j z) s =
      analyticOrderAt riemannZeta s :=
  analyticOrderAt_mul_completeResolutionMultiplier hK j hs
    (analyticOn_riemannZeta _ hs1)

/-- **Publication capstone.**  For every cutoff `K ≥ 12`, the positive channels form a complete,
pairwise-disjoint `0/1` coefficient resolution of zeta; their normalized multipliers have maximal
countable differential rank over the full zeta differential field; and every channel carries
exactly the zeta divisor on `re s > 1/2`. -/
theorem completePositiveKolchinFreeRiemannResolution
    {K : ℕ} (hK : 12 ≤ K) :
    DifferentialIndependent zetaUpperEndDifferentialField
        (completeResolutionUpperEndMultiplier K)
    ∧ (∀ j : ℕ,
        completeResolutionUpperEndMultiplier K j =
          finiteAbscissaLSeriesToUpperEndMero
            (completeResolutionNormalizedFiniteAbscissaSource K j))
    ∧ (∀ j : ℕ,
        completeResolutionNormalizedArithmetic K j *
            (ζ : ArithmeticFunction ℤ) =
          completeResolutionIndicator K j)
    ∧ (∀ j : ℕ, ∀ s : ℂ, 1 < s.re →
        LSeries ↗(completeResolutionNormalizedArithmetic K j) s =
          completeResolutionMultiplier K j s)
    ∧ (∀ s : ℂ, 0 < s.re →
        Filter.Tendsto
          (fun N : ℕ =>
            ∑ j ∈ Finset.range (N + 1),
              completeResolutionMultiplier K j s)
          Filter.atTop (nhds 1))
    ∧ (∀ sigma0 : ℝ, 0 < sigma0 → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s : ℂ, sigma0 ≤ s.re →
          ‖(∑ j ∈ Finset.range (n + 1),
              completeResolutionMultiplier K j s) - 1‖ < ε)
    ∧ (∀ n : ℕ,
        (∑' j : ℕ, completeResolutionIndicator K j n) =
          (ζ : ArithmeticFunction ℤ) n)
    ∧ (∀ i j n : ℕ, i ≠ j →
        completeResolutionIndicator K i n ≠ 0 →
        completeResolutionIndicator K j n = 0)
    ∧ (∀ j : ℕ, ∀ s : ℂ, 1 / 2 < s.re →
        completeResolutionMultiplier K j s ≠ 0)
    ∧ (∀ j : ℕ, ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
        analyticOrderAt
            (fun z => riemannZeta z * completeResolutionMultiplier K j z) s =
          analyticOrderAt riemannZeta s) := by
  exact ⟨
    completeResolutionUpperEndMultiplier_relativeDifferentialIndependent K (by omega),
    completeResolutionUpperEndMultiplier_eq_source K,
    completeResolutionNormalizedArithmetic_mul_zeta (by omega),
    fun j s hs =>
      LSeries_completeResolutionNormalizedArithmetic (by omega) j hs,
    fun s hs =>
      tendsto_sum_range_completeResolutionMultiplier_one K hs,
    fun sigma0 hsigma0 =>
      completeResolutionMultiplier_uniformOn_rightHalfPlane K hsigma0,
    tsum_completeResolutionIndicator,
    fun _ _ _ hij hi => completeResolutionIndicator_pairwiseDisjoint hij hi,
    fun j s hs => completeResolutionMultiplier_ne_zero hK j hs,
    fun j s hs hs1 =>
      analyticOrderAt_riemannZeta_completeResolutionChannel hK j hs hs1⟩

end

end RHTower
