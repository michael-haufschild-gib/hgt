import GaloisForLFunctions.HTGeometry.ExponentZeroPrimeWalshSaturation
import GaloisForLFunctions.HTGeometry.ContinuumPrimeCoherenceSaturation
import GaloisForLFunctions.HTGeometry.ExponentZeroEulerGaugeCardinality

/-!
# Maximal isodivisorial hypertranscendental free frames

An explicit exponentially sparse prime reservoir avoids every prescribed finite prime chamber and
supports a continuum family of exponent-zero sign gauges.  After multiplication by an arbitrary
unimodular base phase, the complete natural-shift palettes remain differentially independent, the
continued positive-half-plane divisor is unchanged, and the phase family has maximal continuum
cardinality.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Cardinal Complex Filter Set
open scoped Differential

noncomputable section

def primeForbiddenBound (F : Finset Nat.Primes) : ℕ :=
  F.sup fun p => (p : ℕ)

def exponentialPrimeEmbeddingAvoiding (F : Finset Nat.Primes) : ℕ ↪ Nat.Primes where
  toFun n :=
    ⟨Nat.nth Nat.Prime (primeForbiddenBound F + 2 ^ n), Nat.prime_nth_prime _⟩
  inj' := by
    intro m n h
    have hnth : Nat.nth Nat.Prime (primeForbiddenBound F + 2 ^ m) =
        Nat.nth Nat.Prime (primeForbiddenBound F + 2 ^ n) :=
      congrArg Subtype.val h
    have hi : primeForbiddenBound F + 2 ^ m = primeForbiddenBound F + 2 ^ n :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hnth
    exact Nat.pow_right_injective (by omega : 2 ≤ 2) (Nat.add_left_cancel hi)

theorem exponentialPrimeEmbeddingAvoiding_not_mem
    (F : Finset Nat.Primes) (n : ℕ) :
    exponentialPrimeEmbeddingAvoiding F n ∉ F := by
  intro hmem
  have hupper : ((exponentialPrimeEmbeddingAvoiding F n : Nat.Primes) : ℕ) ≤
      primeForbiddenBound F :=
    Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hmem
  have hlower : primeForbiddenBound F + 2 ^ n + 2 ≤
      ((exponentialPrimeEmbeddingAvoiding F n : Nat.Primes) : ℕ) := by
    exact Nat.add_two_le_nth_prime (primeForbiddenBound F + 2 ^ n)
  change Nat.nth Nat.Prime (primeForbiddenBound F + 2 ^ n) ≤
    primeForbiddenBound F at hupper
  change primeForbiddenBound F + 2 ^ n + 2 ≤
    Nat.nth Nat.Prime (primeForbiddenBound F + 2 ^ n) at hlower
  have hlower' : primeForbiddenBound F + (2 ^ n + 2) ≤
      Nat.nth Nat.Prime (primeForbiddenBound F + 2 ^ n) := by
    simpa [Nat.add_assoc] using hlower
  have hbad : primeForbiddenBound F + (2 ^ n + 2) ≤ primeForbiddenBound F :=
    hlower'.trans hupper
  have hone : 1 ≤ 2 ^ n + 2 := by
    change Nat.succ 0 ≤ Nat.succ (2 ^ n + 1)
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hs : primeForbiddenBound F + 1 ≤ primeForbiddenBound F + (2 ^ n + 2) :=
    Nat.add_le_add_left hone _
  exact (Nat.not_succ_le_self _ (hs.trans hbad))

theorem exponentialPrimeEmbeddingAvoiding_weight_le
    (F : Finset Nat.Primes) (sigma : PositiveExponent) (n : ℕ) :
    exponentZeroWeight natPrimeSize sigma (exponentialPrimeEmbeddingAvoiding F n) ≤
      Real.exp (-sigma.1 * Real.log 2) ^ n := by
  have hnat : 2 ^ n ≤
      ((exponentialPrimeEmbeddingAvoiding F n : Nat.Primes) : ℕ) := by
    have h := Nat.add_two_le_nth_prime (primeForbiddenBound F + 2 ^ n)
    change primeForbiddenBound F + 2 ^ n + 2 ≤
      Nat.nth Nat.Prime (primeForbiddenBound F + 2 ^ n) at h
    change 2 ^ n ≤ Nat.nth Nat.Prime (primeForbiddenBound F + 2 ^ n)
    omega
  have hcast : ((2 ^ n : ℕ) : ℝ) ≤
      ((exponentialPrimeEmbeddingAvoiding F n : Nat.Primes) : ℝ) := by
    exact_mod_cast hnat
  have hlog : (n : ℝ) * Real.log 2 ≤
      Real.log ((exponentialPrimeEmbeddingAvoiding F n : Nat.Primes) : ℝ) := by
    calc
      (n : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ n) := by rw [Real.log_pow]
      _ ≤ Real.log ((exponentialPrimeEmbeddingAvoiding F n : Nat.Primes) : ℝ) :=
        Real.log_le_log (by positivity) (by simpa using hcast)
  unfold exponentZeroWeight
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  dsimp only [natPrimeSize]
  calc
    -sigma.1 * Real.log ((exponentialPrimeEmbeddingAvoiding F n : Nat.Primes) : ℝ) ≤
        -sigma.1 * ((n : ℝ) * Real.log 2) :=
      mul_le_mul_of_nonpos_left hlog (by linarith [sigma.2])
    _ = (n : ℝ) * (-sigma.1 * Real.log 2) := by ring

theorem summable_exponentZeroWeight_exponentialPrimeEmbeddingAvoiding
    (F : Finset Nat.Primes) (sigma : PositiveExponent) :
    Summable (fun n =>
      exponentZeroWeight natPrimeSize sigma (exponentialPrimeEmbeddingAvoiding F n)) := by
  let q : ℝ := Real.exp (-sigma.1 * Real.log 2)
  have hqnonneg : 0 ≤ q := Real.exp_pos _ |>.le
  have hqone : q < 1 := by
    change Real.exp (-sigma.1 * Real.log 2) < 1
    rw [Real.exp_lt_one_iff]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [sigma.2]
  have hgeom : Summable (fun n : ℕ => q ^ n) := by
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs, abs_of_nonneg hqnonneg]
  exact Summable.of_nonneg_of_le
    (fun n => (exponentZeroWeight_pos natPrimeSize sigma _).le)
    (fun n => by simpa [q] using
      exponentialPrimeEmbeddingAvoiding_weight_le F sigma n)
    hgeom

theorem summable_indicator_exponentialPrimeEmbeddingAvoiding_exponentZeroWeight
    (F : Finset Nat.Primes) (sigma : PositiveExponent) :
    Summable ((Set.range (exponentialPrimeEmbeddingAvoiding F)).indicator
      (exponentZeroWeight natPrimeSize sigma)) :=
  (summable_indicator_embedding_range_iff (exponentialPrimeEmbeddingAvoiding F)
    (exponentZeroWeight natPrimeSize sigma)).2
      (summable_exponentZeroWeight_exponentialPrimeEmbeddingAvoiding F sigma)

def exponentZeroPrefixEmbeddingAvoiding (F : Finset Nat.Primes) :
    PrefixFunctionCoordinate ↪ Nat.Primes where
  toFun q := exponentialPrimeEmbeddingAvoiding F (prefixFunctionCoordinateEquivNat q)
  inj' := (exponentialPrimeEmbeddingAvoiding F).injective.comp
    prefixFunctionCoordinateEquivNat.injective

def maximalIsodivisorialOrientation (F : Finset Nat.Primes) (x : ℕ → Bool) :
    Nat.Primes → Bool :=
  continuumSparsePrimeOrientation (fun _ => false) (exponentZeroPrefixEmbeddingAvoiding F) x

theorem maximalIsodivisorialOrientation_support
    (F : Finset Nat.Primes) (x : ℕ → Bool) :
    {p | maximalIsodivisorialOrientation F x p ≠ false} ⊆
      Set.range (exponentialPrimeEmbeddingAvoiding F) := by
  intro p hp
  by_cases hrange : p ∈ Set.range (exponentZeroPrefixEmbeddingAvoiding F)
  · obtain ⟨q, rfl⟩ := hrange
    exact ⟨prefixFunctionCoordinateEquivNat q, by
      rfl⟩
  · exfalso
    apply hp
    simp [maximalIsodivisorialOrientation, continuumSparsePrimeOrientation,
      basedSparsePrefixOrientation, sparsePrefixOrientation, hrange]

theorem maximalIsodivisorialOrientation_eq_false_of_mem
    (F : Finset Nat.Primes) (x : ℕ → Bool) {p : Nat.Primes} (hp : p ∈ F) :
    maximalIsodivisorialOrientation F x p = false := by
  by_contra hne
  obtain ⟨n, hn⟩ := maximalIsodivisorialOrientation_support F x hne
  rw [← hn] at hp
  exact exponentialPrimeEmbeddingAvoiding_not_mem F n hp

theorem boolOrientationPrimePhase_isExponentZeroEulerGauge_of_avoidingSupport
    (F : Finset Nat.Primes) (epsilon : Nat.Primes → Bool)
    (hsupport : {p | epsilon p ≠ false} ⊆
      Set.range (exponentialPrimeEmbeddingAvoiding F)) :
    IsExponentZeroEulerGauge natPrimeSize (boolOrientationPrimePhase epsilon) := by
  intro sigma
  have hsum :=
    (summable_indicator_exponentialPrimeEmbeddingAvoiding_exponentZeroWeight F sigma).mul_left 2
  apply Summable.of_nonneg_of_le
      (fun p => mul_nonneg (exponentZeroWeight_pos natPrimeSize sigma p).le (norm_nonneg _))
      (fun p => ?_) hsum
  by_cases hp : epsilon p = false
  · by_cases hprange : p ∈ Set.range (exponentialPrimeEmbeddingAvoiding F)
    · simp [boolOrientationPrimePhase, hp, hprange,
        (exponentZeroWeight_pos natPrimeSize sigma p).le]
    · simp [boolOrientationPrimePhase, hp, hprange]
  · have hprange := hsupport hp
    rw [Set.indicator_of_mem hprange]
    have hptrue : epsilon p = true := Bool.eq_true_of_not_eq_false hp
    rw [boolOrientationPrimePhase, if_pos hptrue]
    norm_num [Complex.norm_real, (exponentZeroWeight_pos natPrimeSize sigma p).le]
    simp [mul_comm]

theorem maximalIsodivisorialOrientation_isExponentZeroEulerGauge
    (F : Finset Nat.Primes) (x : ℕ → Bool) :
    IsExponentZeroEulerGauge natPrimeSize
      (boolOrientationPrimePhase (maximalIsodivisorialOrientation F x)) :=
  boolOrientationPrimePhase_isExponentZeroEulerGauge_of_avoidingSupport F _
    (maximalIsodivisorialOrientation_support F x)

def phaseWeightedPrimeCoefficient
    (eta : PrimePhase Nat.Primes) (epsilon : Nat.Primes → Bool) : Nat.Primes → ℂ :=
  fun p => (eta p : ℂ) * primeDirichletSign (epsilon p)

theorem phaseWeightedPrimeCoefficient_norm_le_one
    (eta : PrimePhase Nat.Primes) (epsilon : Nat.Primes → Bool) (p : Nat.Primes) :
    ‖phaseWeightedPrimeCoefficient eta epsilon p‖ ≤ 1 := by
  rw [phaseWeightedPrimeCoefficient, norm_mul, Circle.norm_coe]
  cases epsilon p <;> norm_num [primeDirichletSign]

theorem phaseWeightedPrimeCoefficient_ne_zero
    (eta : PrimePhase Nat.Primes) (epsilon : Nat.Primes → Bool) (p : Nat.Primes) :
    phaseWeightedPrimeCoefficient eta epsilon p ≠ 0 := by
  apply mul_ne_zero
  · exact Circle.coe_ne_zero (eta p)
  · exact primeDirichletSign_ne_zero (epsilon p)

theorem phaseWeightedSignedPrimeShiftedRotatedJets_algebraicIndependent
    {J A : Type*} [Fintype J] [DecidableEq J]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (eta : PrimePhase Nat.Primes) (epsilon : J → Nat.Primes → Bool)
    (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re))
    (htail : PrimeOrientationTailIndependent epsilon) (m : ℕ) :
    AlgebraicIndependent finitePrimeRationalCoefficientField
      (fun jak : J × (A × Fin (m + 1)) =>
        algebraMap arithmeticFunctionFractionField
          arithmeticFunctionRationalCoordinateField
          (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (boundedPrimeShiftedRotatedJet
              (phaseWeightedPrimeCoefficient eta (epsilon jak.1))
              (phaseWeightedPrimeCoefficient_norm_le_one eta (epsilon jak.1))
              (alpha jak.2.1) jak.2.2).1)) := by
  let raw : J × (A × Fin (m + 1)) → Nat.Primes → ℂ :=
    fun jak p => primeDirichletSign (epsilon jak.1 p) *
      primeShiftFactor (alpha jak.2.1) p * rotatedPrimeLogClock p ^ (jak.2.2 : ℕ)
  let coeff : J × (A × Fin (m + 1)) → Nat.Primes → ℂ :=
    fun jak p => (eta p : ℂ) * raw jak p
  have hraw : TailCoefficientIndependent raw :=
    (signedPrimeShiftedRotatedJet_tailIndependent_iff epsilon alpha hdistinct m).2 htail
  have hcoeff : TailCoefficientIndependent coeff :=
    (tailCoefficientIndependent_commonWeight_iff raw (fun p => (eta p : ℂ))
      (fun p => Circle.coe_ne_zero (eta p))).2 hraw
  have hai := algebraicIndependent_fractionPrimeColumns_over_finitePrimeCoefficientField
    coeff hcoeff
  have hbase := algebraicIndependent_constants_over_finitePrimeRationalCoefficientField _ hai
  convert hbase using 1
  funext jak
  congr 2
  rw [boundedPrimeShiftedRotatedJet_eq_arithmeticOfPrimeColumn]
  congr 1
  funext p
  simp only [phaseWeightedPrimeCoefficient, coeff, raw]
  ring

def phaseWeightedSignedPrimeNaturalShiftPalette
    (eta : PrimePhase Nat.Primes) (epsilon : Nat.Primes → Bool) (a : ℕ) :
    arithmeticFunctionRationalCoordinateField :=
  boundedPrimeShiftCarrier (phaseWeightedPrimeCoefficient eta epsilon)
    (phaseWeightedPrimeCoefficient_norm_le_one eta epsilon) (a : ℂ)

theorem phaseWeightedSignedPrimeNaturalShiftPalette_differentialIndependent
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (eta : PrimePhase Nat.Primes) (epsilon : J → Nat.Primes → Bool)
    (htail : PrimeOrientationTailIndependent epsilon) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (fun ja : J × ℕ =>
        phaseWeightedSignedPrimeNaturalShiftPalette eta (epsilon ja.1) ja.2) := by
  unfold GaloisForLFunctions.DifferentialIndependent
  simp_rw [phaseWeightedSignedPrimeNaturalShiftPalette,
    differentialJet_boundedPrimeShiftCarrier]
  apply algebraicIndependent_of_finite_type
  intro t ht
  obtain ⟨qa, hqa⟩ := Set.exists_upper_bound_image t (fun z => z.1.2) ht
  obtain ⟨qk, hqk⟩ := Set.exists_upper_bound_image t Prod.snd ht
  let f : t → J × (Fin (qa.1.2 + 1) × Fin (qk.2 + 1)) := fun z =>
    (z.1.1.1,
      (⟨z.1.1.2, Nat.lt_succ_of_le (hqa z.1 z.2)⟩,
        ⟨z.1.2, Nat.lt_succ_of_le (hqk z.1 z.2)⟩))
  have hf : Function.Injective f := by
    intro z w hzw
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun u => u.1) hzw
      · exact congrArg (fun u => ((u.2.1 : Fin (qa.1.2 + 1)) : ℕ)) hzw
    · exact congrArg (fun u => ((u.2.2 : Fin (qk.2 + 1)) : ℕ)) hzw
  have hrect := phaseWeightedSignedPrimeShiftedRotatedJets_algebraicIndependent
    eta epsilon (fun a : Fin (qa.1.2 + 1) => ((a : ℕ) : ℂ)) (by
      intro a b h
      apply Fin.ext
      exact natCastComplex_re_injective h) htail qk.2
  have hsub := hrect.comp f hf
  simpa only [Function.comp_apply, f] using! hsub

theorem maximalIsodivisorialNaturalShiftPalette_differentialIndependent
    (eta : PrimePhase Nat.Primes) (F : Finset Nat.Primes) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (fun xa : (ℕ → Bool) × ℕ =>
        phaseWeightedSignedPrimeNaturalShiftPalette eta
          (maximalIsodivisorialOrientation F xa.1) xa.2) := by
  classical
  unfold GaloisForLFunctions.DifferentialIndependent
  apply algebraicIndependent_of_finite_type
  intro t ht
  let S : Set (ℕ → Bool) :=
    (fun z : (((ℕ → Bool) × ℕ) × ℕ) => z.1.1) '' t
  have hS : S.Finite := ht.image _
  letI : Fintype S := hS.fintype
  cases isEmpty_or_nonempty S with
  | inl hEmpty =>
      letI : IsEmpty S := hEmpty
      have htEmpty : IsEmpty t := ⟨fun z => by
        have hzS : z.1.1.1 ∈ S := ⟨z.1, z.2, rfl⟩
        exact isEmptyElim (⟨z.1.1.1, hzS⟩ : S)⟩
      letI : IsEmpty t := htEmpty
      exact algebraicIndependent_empty_type
  | inr hNonempty =>
      letI : Nonempty S := hNonempty
      let epsilon : S → Nat.Primes → Bool :=
        fun s => maximalIsodivisorialOrientation F s.1
      have htail : PrimeOrientationTailIndependent epsilon := by
        simpa only [epsilon, maximalIsodivisorialOrientation,
          continuumSparsePrimeOrientation] using
          (basedSparsePrefixOrientation_tailIndependent
            (fun _ : Nat.Primes => false) (exponentZeroPrefixEmbeddingAvoiding F)
            (fun s : S => s.1) Subtype.val_injective)
      have hdiff :=
        phaseWeightedSignedPrimeNaturalShiftPalette_differentialIndependent eta epsilon htail
      unfold GaloisForLFunctions.DifferentialIndependent at hdiff
      let f : t → (S × ℕ) × ℕ := fun z =>
        ((⟨z.1.1.1, ⟨z.1, z.2, rfl⟩⟩, z.1.1.2), z.1.2)
      have hf : Function.Injective f := by
        intro z w hzw
        apply Subtype.ext
        apply Prod.ext
        · apply Prod.ext
          · exact congrArg (fun u : (S × ℕ) × ℕ => u.1.1.1) hzw
          · exact congrArg (fun u : (S × ℕ) × ℕ => u.1.2) hzw
        · exact congrArg (fun u : (S × ℕ) × ℕ => u.2) hzw
      have hsub := hdiff.comp f hf
      simpa only [Function.comp_apply, f, epsilon] using! hsub

theorem prefixFunctionOrientation_injective :
    Function.Injective prefixFunctionOrientation := by
  intro x y hxy
  funext n
  let q : PrefixFunctionCoordinate :=
    ⟨n + 1, fun b => b ⟨n, Nat.lt_succ_self n⟩⟩
  have hq := congrFun hxy q
  simpa [q, prefixFunctionOrientation, binaryPrefix] using hq

theorem maximalIsodivisorialOrientation_injective (F : Finset Nat.Primes) :
    Function.Injective (maximalIsodivisorialOrientation F) := by
  intro x y hxy
  apply prefixFunctionOrientation_injective
  funext q
  have hq := congrFun hxy (exponentZeroPrefixEmbeddingAvoiding F q)
  simpa [maximalIsodivisorialOrientation, continuumSparsePrimeOrientation,
    basedSparsePrefixOrientation] using hq

theorem boolOrientationPrimePhase_injective :
    Function.Injective (boolOrientationPrimePhase :
      (Nat.Primes → Bool) → PrimePhase Nat.Primes) := by
  intro epsilon delta h
  funext p
  have hinj : Function.Injective
      (fun b : Bool => if b then (-1 : Circle) else 1) := by
    intro a b hab
    cases a <;> cases b
    · rfl
    · exfalso
      have hc := congrArg ((↑) : Circle → ℂ) hab
      norm_num at hc
    · exfalso
      have hc := congrArg ((↑) : Circle → ℂ) hab
      norm_num at hc
    · rfl
  exact hinj (congrFun h p)

def maximalIsodivisorialPrimePhase
    (eta : PrimePhase Nat.Primes) (F : Finset Nat.Primes) (x : ℕ → Bool) :
    PrimePhase Nat.Primes :=
  eta * boolOrientationPrimePhase (maximalIsodivisorialOrientation F x)

theorem maximalIsodivisorialPrimePhase_apply_mem
    (eta : PrimePhase Nat.Primes) (F : Finset Nat.Primes)
    (x : ℕ → Bool) {p : Nat.Primes} (hp : p ∈ F) :
    maximalIsodivisorialPrimePhase eta F x p = eta p := by
  simp [maximalIsodivisorialPrimePhase,
    boolOrientationPrimePhase_false _ _
      (maximalIsodivisorialOrientation_eq_false_of_mem F x hp)]

theorem maximalIsodivisorialPrimePhase_injective
    (eta : PrimePhase Nat.Primes) (F : Finset Nat.Primes) :
    Function.Injective (maximalIsodivisorialPrimePhase eta F) := by
  intro x y hxy
  apply maximalIsodivisorialOrientation_injective F
  apply boolOrientationPrimePhase_injective
  exact mul_left_cancel hxy

theorem cardinalMk_range_maximalIsodivisorialPrimePhase
    (eta : PrimePhase Nat.Primes) (F : Finset Nat.Primes) :
    #(Set.range (maximalIsodivisorialPrimePhase eta F)) = Cardinal.continuum := by
  rw [Cardinal.mk_range_eq _ (maximalIsodivisorialPrimePhase_injective eta F),
    mk_boolSequence_eq_continuum]

theorem maximalIsodivisorial_completePositiveHalfPlaneDivisor_eq
    (eta : PrimePhase Nat.Primes) (F : Finset Nat.Primes)
    (f : ℂ → ℂ) (x : ℕ → Bool) :
    ∀ z ∈ positiveHalfPlane,
      meromorphicOrderAt
          (exponentZeroGaugeContinuedSource eta
            (boolOrientationPrimePhase (maximalIsodivisorialOrientation F x)) f) z =
        meromorphicOrderAt f z :=
  exponentZeroGauge_completePositiveHalfPlaneDivisor_eq eta _
    (maximalIsodivisorialOrientation_isExponentZeroEulerGauge F x) f

theorem meromorphicOn_maximalIsodivisorialContinuedSource
    (eta : PrimePhase Nat.Primes) (F : Finset Nat.Primes)
    {f : ℂ → ℂ} (hf : MeromorphicOn f positiveHalfPlane) (x : ℕ → Bool) :
    MeromorphicOn
      (exponentZeroGaugeContinuedSource eta
        (boolOrientationPrimePhase (maximalIsodivisorialOrientation F x)) f)
      positiveHalfPlane :=
  meromorphicOn_exponentZeroGaugeContinuedSource eta _
    (maximalIsodivisorialOrientation_isExponentZeroEulerGauge F x) hf

end

end GaloisForLFunctions.HTGeometry
