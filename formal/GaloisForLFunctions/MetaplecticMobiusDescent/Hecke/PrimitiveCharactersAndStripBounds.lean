/-
Primitive characters and strip bounds adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.HeckeLogarithmicDerivative
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.CanonicalCharactersAndLossParameters

/-!
# Primitive characters and strip bounds

Primitive Hecke characters with their scales, reciprocal bounds and normalized Gauss sums
(`TraceCharacter`). The functional equation, exponential growth and uniform strip bound of
the actual L-functions (`HeckeStripActual`).
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeLocalRamification
open CenteredMomentCorrelation CenteredMomentCanonical
open Eisenstein
open Eisenstein hiding O

theorem crtCharacter_eq_one_iff {S ι : Type*} [CommRing S] [Fintype ι]
    {R : ι → Type*} [∀ i, CommRing (R i)]
    (e : S ≃+* ∀ i, R i) (χ : ∀ i, MulChar (R i) ℂ) :
    crtCharacter e χ = 1 ↔ ∀ i, χ i = 1 := by
  constructor
  · intro h i
    apply MulChar.ext
    intro u
    let v : ∀ j, R j := Function.update (fun _ => 1) i (u : R i)
    have hv : IsUnit v := by
      rw [Pi.isUnit_iff]
      intro j
      by_cases hj : j = i
      · subst j
        simp [v]
      · simp [v, hj]
    have hx : IsUnit (e.symm v) := hv.map e.symm.toMonoidHom
    have heq := congrArg (fun f : MulChar S ℂ => f (e.symm v)) h
    rw [crtCharacter_apply, e.apply_symm_apply, MulChar.one_apply hx] at heq
    have hprod : (∏ j, χ j (v j)) = χ i (u : R i) := by
      rw [Finset.prod_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [v, hj]
      · simp
    rw [hprod] at heq
    simpa only [MulChar.one_apply u.isUnit] using heq
  · intro h
    apply MulChar.ext
    intro u
    rw [crtCharacter_apply, MulChar.one_apply u.isUnit]
    apply Finset.prod_eq_one
    intro i _
    rw [h i, MulChar.one_apply]
    exact (u.isUnit.map e.toMonoidHom).map (Pi.evalMonoidHom _ i)

theorem primePowerCharacter_eq_one_iff (P : Ideal O) [P.IsMaximal]
    {c : ℕ} (hc : 1 ≤ c) (χ : MulChar (O ⧸ P) ℂ) :
    primePowerCharacter P hc χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    apply MulChar.ext
    intro u
    obtain ⟨x,hx⟩ := primePowerReduction_surjective P hc (u : O ⧸ P)
    have hux : IsUnit x := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      apply (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
      change Ideal.Quotient.mk P a = (u : O ⧸ P) at hx
      rw [hx]
      exact u.isUnit
    have heq := congrArg (fun f : MulChar (O ⧸ P^c) ℂ => f x) h
    rw [primePowerCharacter_apply, hx, MulChar.one_apply hux] at heq
    simpa only [MulChar.one_apply u.isUnit] using heq
  · rintro rfl
    apply MulChar.ext
    intro u
    rw [primePowerCharacter_apply, MulChar.one_apply u.isUnit,
      MulChar.one_apply (u.isUnit.map (primePowerReduction P hc))]

theorem canonicalPrimePowerCharacter_eq_one_iff (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) : canonicalPrimePowerCharacter P hg hc = 1 ↔ 6 ∣ c := by
  rw [canonicalPrimePowerCharacter, primePowerCharacter_eq_one_iff,
    ← orderOf_dvd_iff_pow_eq_one, complexSexticChar_order_six P hg hchar]

theorem canonicalCRTCharacter_eq_one_iff {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    canonicalCRTCharacter P hg c hc hcop = 1 ↔ ∀ i, 6 ∣ c i := by
  rw [canonicalCRTCharacter, crtCharacter_eq_one_iff]
  exact forall_congr' (fun i => canonicalPrimePowerCharacter_eq_one_iff (P i) (hg i) (hchar i) (hc i))

theorem product_nonprincipal_of_coprime {A : Type*} [CommRing A]
    (I J : Ideal A) (hIJ : IsCoprime I J)
    (φ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ) (hψ : ψ ≠ 1) :
    ResidueCharacter.product I J φ ψ ≠ 1 := by
  intro h
  apply hψ
  apply MulChar.ext
  intro u
  let e := Ideal.quotientInfEquivQuotientProd I J hIJ
  obtain ⟨x,hx⟩ := e.surjective ((1 : A ⧸ I), (u : A ⧸ J))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Ideal.Quotient.mk I a, Ideal.Quotient.mk J a) = (1, (u : A ⧸ J)) at hx
  have hI := congrArg Prod.fst hx
  have hJ := congrArg Prod.snd hx
  dsimp only at hI hJ
  have hu : IsUnit (Ideal.Quotient.mk (I ⊓ J) a) := by
    apply (ResidueCharacter.isUnit_mk_inf_iff I J a).mpr
    constructor
    · rw [hI]
      exact isUnit_one
    · rw [hJ]
      exact u.isUnit
  have heq := congrArg (fun χ : MulChar (A ⧸ I ⊓ J) ℂ =>
    χ (Ideal.Quotient.mk (I ⊓ J) a)) h
  rw [ResidueCharacter.product_mk, hI, hJ, map_one, one_mul, MulChar.one_apply hu] at heq
  simpa only [MulChar.one_apply u.isUnit] using heq

theorem nonprincipal_fixed_times_local (Q P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) (hc6 : c < 6)
    (hcop : IsCoprime Q (P^c)) (φ : MulChar (O ⧸ Q) ℂ) :
    ResidueCharacter.product Q (P^c) φ (canonicalPrimePowerCharacter P hg hc) ≠ 1 := by
  apply product_nonprincipal_of_coprime _ _ hcop
  intro h
  exact Nat.not_dvd_of_pos_of_lt (by omega) hc6
    ((canonicalPrimePowerCharacter_eq_one_iff P hg hchar hc).mp h)

end HeckeLocalRamification

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeRowNonprincipal
open HeckeFamily CanonicalRowCompletion CenteredMomentCanonical
open Eisenstein hiding O

theorem nonprincipal_of_local_factor (χ : Character)
    (Q J P : Ideal O) [P.IsMaximal]
    (hQ : Q ≤ Ideal.span {lambda ^ 2})
    (φ : O →* ℂ) (hφ : CanonicalCoefficientClass.FactorsModulo Q φ)
    (hJ : CanonicalQuadraticSieve.Supported J)
    (hg : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) (hc6 : ¬ 6 ∣ c)
    (hcop : IsCoprime (Q * J) (P ^ c))
    (hrow : ∀ n : O, lambda ^ 2 ∣ n - 1 →
      elementCoeff χ n = φ n * idealRowHom n (P ^ c * J)) :
    χ.residue ≠ 1 := by
  let ψ := canonicalPrimePowerCharacter P hg hc
  have hψ : ψ ≠ 1 := fun h => hc6 ((HeckeLocalRamification.canonicalPrimePowerCharacter_eq_one_iff P hg hchar hc).mp h)
  obtain ⟨u, hu⟩ : ∃ u : (O ⧸ P ^ c)ˣ, ψ (u : O ⧸ P ^ c) ≠ 1 := by
    by_contra! h
    apply hψ
    apply MulChar.ext
    intro u
    rw [MulChar.one_apply u.isUnit]
    exact h u
  let e := Ideal.quotientInfEquivQuotientProd (Q * J) (P ^ c) hcop
  obtain ⟨x, hx⟩ := e.surjective ((1 : O ⧸ Q * J), (u : O ⧸ P ^ c))
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Ideal.Quotient.mk (Q * J) n, Ideal.Quotient.mk (P ^ c) n) = (1, (u : O ⧸ P ^ c)) at hx
  have hnQJ := congrArg Prod.fst hx
  have hnP := congrArg Prod.snd hx
  dsimp only at hnQJ hnP
  have hn : n - 1 ∈ Q * J := Ideal.Quotient.eq.mp (by simpa using hnQJ)
  have hnQ : n - 1 ∈ Q := Ideal.mul_le_right hn
  have hnJ : n - 1 ∈ J := Ideal.mul_le_left hn
  have hnprimary : lambda ^ 2 ∣ n - 1 := Ideal.mem_span_singleton.mp (hQ hnQ)
  have hv : elementCoeff χ n = ψ (u : O ⧸ P ^ c) := by
    rw [hrow n hnprimary, map_mul, hφ n 1 hnQ, map_one, one_mul,
      idealRowHom_congr_mod J n 1 hnJ, idealRowHom_one_supported J hJ, mul_one]
    rw [← canonicalPrimePowerCharacter_mk P hg hc n, hnP]
  have hv0 : elementCoeff χ n ≠ 0 := hv ▸ (MulChar.apply_ne_zero_iff.mpr u.isUnit)
  intro hχ
  have hunit : IsUnit (Ideal.Quotient.mk χ.modulus n) := MulChar.apply_ne_zero_iff.mp hv0
  have hv1 : elementCoeff χ n = 1 := by
    change χ.residue _ = 1
    rw [hχ, MulChar.one_apply hunit]
  exact hu (hv.symm.trans hv1)

theorem actual_row_nonprincipal (η χ : Character) (m f z : O)
    (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : lambda ^ 2 ∣ r - 1) (hx : f ^ 4 * z = (u : O) * lambda ^ a * (2 : O) ^ b * r)
    (P J : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hJ : CanonicalQuadraticSieve.Supported J)
    {c : ℕ} (hc : 1 ≤ c) (hc6 : ¬ 6 ∣ c)
    (hsplit : Ideal.span {r} = P ^ c * J)
    (hcop : IsCoprime ((η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}) * J) (P ^ c))
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n) :
    χ.residue ≠ 1 := by
  let φ := HeckeRowClosure.elementHom η * coprimalityMask m *
    numeratorBadTwist u a b r ((CanonicalQuadraticSieve.supported_iff_native _).mp hr)
  refine nonprincipal_of_local_factor χ (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}) J P
      ?_ φ ?_ hJ hg hchar hc hc6 hcop ?_
  · have hd3 : lambda ^ 2 ∣ (3 : O) := Eisenstein.lambda_sq_dvd_three
    have hd72 : lambda ^ 2 ∣ (72 : O) := hd3.trans ⟨24, by norm_num⟩
    exact Ideal.mul_le_left.trans ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_span_singleton.mpr hd72))
  · intro x y hxy
    change ((HeckeRowClosure.elementHom η x * coprimalityMask m x) *
      numeratorBadTwist u a b r ((CanonicalQuadraticSieve.supported_iff_native _).mp hr) x) =
      ((HeckeRowClosure.elementHom η y * coprimalityMask m y) *
      numeratorBadTwist u a b r ((CanonicalQuadraticSieve.supported_iff_native _).mp hr) y)
    rw [HeckeRowClosure.elementHom_periodic η x y (Ideal.mul_le_right (Ideal.mul_le_right hxy)),
      coprimalityMask_periodic m x y (Ideal.mul_le_left (Ideal.mul_le_right hxy)),
      numeratorBadTwist_periodic u a b r ((CanonicalQuadraticSieve.supported_iff_native _).mp hr)
        x y (Ideal.mul_le_left hxy)]
  · intro n hn
    rw [hχ n, rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r
      ((CanonicalQuadraticSieve.supported_iff_native _).mp hr) hpr hx n hn]
    change φ n * idealRowHom n (Ideal.span {r}) = φ n * idealRowHom n (P ^ c * J)
    rw [hsplit]

open UniqueFactorizationMonoid in

theorem extract_prime_power (I : Ideal O) (hI : CanonicalQuadraticSieve.Supported I)
    (P : Ideal O) (hP : P ∈ normalizedFactors I) :
    ∃ J : Ideal O, I = P ^ (normalizedFactors I).count P * J ∧
      CanonicalQuadraticSieve.Supported J ∧ IsCoprime J P := by
  let S := (normalizedFactors I).toFinset
  let J := ∏ Q ∈ S.erase P, Q ^ (normalizedFactors I).count Q
  have hPS : P ∈ S := Multiset.mem_toFinset.mpr hP
  have hsplit : I = P ^ (normalizedFactors I).count P * J := by
    calc
      I = (normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI.1).symm
      _ = ∏ Q ∈ S, Q ^ (normalizedFactors I).count Q := Finset.prod_multiset_count _
      _ = P ^ (normalizedFactors I).count P * J :=
        (Finset.mul_prod_erase S (fun Q => Q ^ (normalizedFactors I).count Q) hPS).symm
  have hgood := CanonicalQuadraticSieve.supported_factors_good I hI P hP
  let : P.IsMaximal := hgood.1
  refine ⟨J, hsplit, ?_, ?_⟩
  · exact (CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplit ▸ hI) |>.2
  · apply IsCoprime.prod_left
    intro Q hQ
    obtain ⟨hQP, hQS⟩ := Finset.mem_erase.mp hQ
    have hgoodQ := CanonicalQuadraticSieve.supported_factors_good I hI Q (Multiset.mem_toFinset.mp hQS)
    let : Q.IsMaximal := hgoodQ.1
    exact (Ideal.isCoprime_of_isMaximal hQP).pow_left

open UniqueFactorizationMonoid in

theorem principal_row_multiplicity (η χ : Character) (m f z : O)
    (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : lambda ^ 2 ∣ r - 1) (hx : f ^ 4 * z = (u : O) * lambda ^ a * (2 : O) ^ b * r)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (hprincipal : χ.residue = 1)
    (P : Ideal O) (hP : P ∈ normalizedFactors (Ideal.span {r}))
    (hcop : IsCoprime (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}) P) :
    6 ∣ (normalizedFactors (Ideal.span {r})).count P := by
  by_contra hc6
  have hgood := CanonicalQuadraticSieve.supported_factors_good (Ideal.span {r}) hr P hP
  let : P.IsMaximal := hgood.1
  obtain ⟨J, hsplit, hJ, hJP⟩ := extract_prime_power _ hr P hP
  have hc : 1 ≤ (normalizedFactors (Ideal.span {r})).count P := Multiset.count_pos.mpr hP
  exact actual_row_nonprincipal η χ m f z hmLam hm2 u a b r hr hpr hx P J
    hgood.2.1 hgood.2.2 hJ hc hc6 hsplit ((hcop.mul_left hJP).pow_right) hχ hprincipal

open UniqueFactorizationMonoid in

theorem principal_row_fixed_support (η χ : Character) (m f z : O)
    (hm : m ≠ 0) (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : lambda ^ 2 ∣ r - 1) (hx : f ^ 4 * z = (u : O) * lambda ^ a * (2 : O) ^ b * r)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (hprincipal : χ.residue = 1)
    (hfree : ∀ P ∈ normalizedFactors (Ideal.span {r}),
      (normalizedFactors (Ideal.span {r})).count P < 6) :
    r ∈ HeckeExceptionalRows.rows
      (normalizedFactors (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)})).toFinset := by
  let Q := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}
  have hQ : Q ≠ ⊥ := mul_ne_zero
    (mul_ne_zero η.modulus_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hm))
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
  refine ⟨Ideal.span_singleton_eq_bot.not.mp hr.1, ?_⟩
  intro P hP
  refine ⟨?_, hfree P hP⟩
  apply Multiset.mem_toFinset.mpr
  have hgood := CanonicalQuadraticSieve.supported_factors_good (Ideal.span {r}) hr P hP
  let : P.IsMaximal := hgood.1
  apply (Ideal.mem_normalizedFactors_iff hQ).mpr
  refine ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor P hP), ?_⟩
  by_contra hQP
  have hcop : IsCoprime Q P := by
    apply Ideal.coprime_of_no_prime_ge
    intro J hQJ hPJ hJ
    have hPJ' : P = J := hgood.1.eq_of_le hJ.ne_top hPJ
    exact hQP (hPJ' ▸ hQJ)
  have hd := principal_row_multiplicity η χ m f z hmLam hm2 u a b r hr hpr hx hχ hprincipal P hP hcop
  exact Nat.not_dvd_of_pos_of_lt (Multiset.count_pos.mpr hP) (hfree P hP) hd

end HeckeRowNonprincipal

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators SchwartzMap

namespace TraceCharacter

abbrev O := Eisenstein.O

open Eisenstein Eisenstein 
open SchwartzPlanePoisson FiniteFourier

def traceCharacter (c : O) (hc : c ≠ 0) : AddChar (O ⧸ Ideal.span {c}) ℂ :=
  residueTraceQuotientChar 1 c hc

theorem traceCharacter_mk (c : O) (hc : c ≠ 0) (x : O) :
    traceCharacter c hc (Ideal.Quotient.mk (Ideal.span {c}) x) =
      tracePhase (ringComplex x / (ringComplex c * (ringComplex traceLambda))) := by
  simpa only [traceCharacter, residueTraceQuotientChar_phase, one_mul]

theorem traceCharacter_eq_paperE (c : O) (hc : c ≠ 0) (x : O) :
    traceCharacter c hc (Ideal.Quotient.mk (Ideal.span {c}) x) =
      paperE (ringComplex x / ringComplex c) :=
by
  rw [traceCharacter_mk]
  unfold paperE
  congr 1
  ring

theorem traceCharacter_isPrimitive (c : O) (hc : c ≠ 0) :
    (traceCharacter c hc).IsPrimitive :=
  residueTraceQuotientChar_primitive c hc

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr (NeZero.ne c))
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

theorem residue_card :
    Fintype.card (O ⧸ Ideal.span {c}) = Ideal.absNorm (Ideal.span {c}) := by
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

def gaussScalar (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ :=
  gaussSum χ (traceCharacter c (NeZero.ne c))

theorem transform_nonunit (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : O ⧸ Ideal.span {c}) (ha : ¬ IsUnit a) :
    (∑ x : O ⧸ Ideal.span {c}, χ x * traceCharacter c (NeZero.ne c) (a * x)) = 0 := by
  simpa only [gaussSum, AddChar.mulShift_apply] using
    gaussSum_mulShift_nonunit_eq_zero χ hχ (traceCharacter c (NeZero.ne c)) ha

theorem transform_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : O ⧸ Ideal.span {c}) :
    (∑ x : O ⧸ Ideal.span {c}, χ x * traceCharacter c (NeZero.ne c) (a * x)) =
      χ⁻¹ a * gaussScalar c χ :=
  transform_primitive_character χ hχ (traceCharacter c (NeZero.ne c)) a

theorem paper_transform_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (h : O) :
    (∑ x : O ⧸ Ideal.span {c}, χ x *
      paperE (ringComplex (GaussianShiftedPartition.representative c x) *
        ringComplex h / ringComplex c)) =
      χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) * gaussScalar c χ := by
  simpa only [traceCharacter, residueTraceQuotientChar_frequency] using
    transform_eq c χ hχ (Ideal.Quotient.mk (Ideal.span {c}) h)

theorem gaussScalar_norm_sq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖gaussScalar c χ‖ ^ 2 = (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
  simpa only [gaussScalar, residue_card c] using
    primitive_gaussSum_norm_sq χ hχ (traceCharacter c (NeZero.ne c))
      (traceCharacter_isPrimitive c (NeZero.ne c))

theorem gaussScalar_norm (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖gaussScalar c χ‖ = Real.sqrt (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
  rw [← gaussScalar_norm_sq c χ hχ, Real.sqrt_sq (norm_nonneg _)]

theorem gaussScalar_norm_embedding (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖gaussScalar c χ‖ = ‖ringComplex c‖ := by
  rw [gaussScalar_norm c χ hχ, ← ringComplex_norm_sq_eq_absNorm_span,
    Real.sqrt_sq (norm_nonneg _)]

theorem gaussScalar_ne_zero (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : gaussScalar c χ ≠ 0 :=
  primitive_gaussSum_ne_zero χ hχ (traceCharacter c (NeZero.ne c))
    (traceCharacter_isPrimitive c (NeZero.ne c))

def normalizedGauss (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ :=
  gaussScalar c χ / (‖ringComplex c‖ : ℂ)

theorem normalizedGauss_norm (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : ‖normalizedGauss c χ‖ = 1 := by
  rw [normalizedGauss, norm_div, gaussScalar_norm_embedding c χ hχ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (ringComplex_ne_zero (NeZero.ne c)))]

theorem character_expansion (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : O ⧸ Ideal.span {c}) :
    χ a = (∑ x : O ⧸ Ideal.span {c}, χ⁻¹ x * traceCharacter c (NeZero.ne c) (a * x)) /
      gaussScalar c χ⁻¹ :=
  primitive_character_expansion χ hχ (traceCharacter c (NeZero.ne c))
    (traceCharacter_isPrimitive c (NeZero.ne c)) a


end TraceCharacter
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical FourierTransform

namespace GaussianTheta

abbrev O := Eisenstein.O

open Eisenstein SchwartzPlanePoisson QuadraticPhase

def gaussian (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * (‖z‖ : ℂ) ^ 2)

def coordinate (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * (ringComplex omega)

theorem omega3_re : (ringComplex omega).re = -(1 / 2 : ℝ) := by
  simpa only [neg_div] using complex_omega_coordinates.1

theorem coordinate_norm_sq (x y : ℝ) :
    ‖coordinate x y‖ ^ 2 = RankTwoEisShift.Q x y := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [coordinate, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, omega3_re, zero_mul, zero_add, add_zero, sub_zero]
  unfold RankTwoEisShift.Q
  nlinarith only [congrArg (fun t : ℝ => y ^ 2 * t) complex_omega_coordinates.2]

theorem exists_coordinate (w : ℂ) : ∃ x y : ℝ, w = coordinate x y := by
  let v := (basisEquiv (ringComplex omega) complex_omega_im_ne_zero).symm w
  refine ⟨v.re, v.im, ?_⟩
  have h := (basisEquiv (ringComplex omega) complex_omega_im_ne_zero).apply_symm_apply w
  simpa only [basisEquiv_apply, coordinate, mul_comm] using h.symm

theorem coordinate_dual_phase (x y : ℝ) (p : ℤ × ℤ) :
    paperE (coordinate x y * ringComplex (dualFrequencyEquiv p)) =
      RankTwoEisShift.dualPhase p.1 p.2 x y := by
  have he : ringComplex (dualFrequencyEquiv p) =
      ((p.1 : ℝ) + p.2 : ℝ) + (p.1 : ℂ) * ringComplex omega := by
    change ringComplex (Eisenstein.Coordinates.eval (p.1+p.2) p.1) = _
    rw [ringComplex_eval]
    push_cast
    rfl
  rw [he]
  change Complex.exp (2 * Real.pi * Complex.I * _) = _
  have ht := complexTrace_real_basis_product x y ((p.1 : ℝ) + p.2) (p.1 : ℝ)
  simp only [Complex.ofReal_intCast] at ht
  rw [coordinate, ht]
  unfold RankTwoEisShift.dualPhase
  congr 1
  push_cast
  ring

theorem gaussian_coordinate_shift (a x y : ℝ) (p : ℤ × ℤ) :
    gaussian a (ringComplex (Eisenstein.Coordinates.eval p.1 p.2) +
      coordinate x y) = RankTwoEisShift.shifted a x y p := by
  have he : ringComplex (Eisenstein.Coordinates.eval p.1 p.2) + coordinate x y =
      coordinate ((p.1 : ℝ) + x) ((p.2 : ℝ) + y) := by
    rw [ringComplex_eval]
    simp only [coordinate, Complex.ofReal_add, Complex.ofReal_intCast]
    ring
  rw [he]
  unfold gaussian RankTwoEisShift.shifted
  rw [← Complex.ofReal_pow, coordinate_norm_sq]
  congr 1
  push_cast
  ring

theorem gaussian_dual_coordinate (a : ℝ) (p : ℤ × ℤ) :
    gaussian a (ringComplex (dualFrequencyEquiv p)) =
      Complex.exp (((-Real.pi * a * RankTwoPoisson.eisQ (p.1, -p.2) : ℝ) : ℂ)) := by
  have hn : ‖ringComplex (dualFrequencyEquiv p)‖ ^ 2 =
      RankTwoPoisson.eisQ (p.1, -p.2) := by
    change ‖ringComplex (Eisenstein.Coordinates.eval (p.1+p.2) p.1)‖ ^ 2 = _
    rw [Eisenstein.Coordinates.complex_norm_eval_sq]
    unfold RankTwoPoisson.eisQ
    push_cast
    ring
  unfold gaussian
  rw [← Complex.ofReal_pow, hn]
  congr 1
  push_cast
  ring

theorem shifted_prefactor (a : ℝ) (ha : 0 < a) :
    (1 / (a : ℂ) ^ (1 / 2 : ℂ)) *
      (1 / (((3 * a / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) =
      ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) := by
  have h := EisensteinGaussianPrefactor.complex_eta_times_prefactor a 1 ha (by norm_num)
  simp only [mul_one] at h
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  apply (mul_left_cancel₀ ha0)
  rw [← mul_assoc, h]
  push_cast
  field_simp

theorem shifted_lattice_poisson (a : ℝ) (ha : 0 < a) (w : ℂ) :
    (∑' z : O, gaussian a (ringComplex z + w)) =
      ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) *
        ∑' h : O, paperE (w * ringComplex h) *
          gaussian (4 / (3 * a)) (ringComplex h) := by
  obtain ⟨x, y, rfl⟩ := exists_coordinate w
  have hp := RankTwoEisShift.shifted_eisenstein_gaussian_poisson ha x y
  rw [shifted_prefactor a ha] at hp
  change (∑' p : ℤ × ℤ, RankTwoEisShift.shifted a x y p) =
    ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) * ∑' p : ℤ × ℤ,
      Complex.exp (((-Real.pi * (4 / (3 * a)) * RankTwoPoisson.eisQ (p.1, -p.2) : ℝ) : ℂ)) *
        RankTwoEisShift.dualPhase p.1 p.2 x y at hp
  calc
    _ = ∑' p : ℤ × ℤ, gaussian a
        (ringComplex (Eisenstein.Coordinates.eval p.1 p.2) + coordinate x y) :=
      (Eisenstein.Coordinates.coordinateEquiv.symm.tsum_eq _).symm
    _ = ∑' p : ℤ × ℤ, RankTwoEisShift.shifted a x y p := by
      apply tsum_congr
      exact gaussian_coordinate_shift a x y
    _ = _ := by
      rw [hp]
      congr 1
      rw [← dualFrequencyEquiv.tsum_eq]
      apply tsum_congr
      intro p
      rw [coordinate_dual_phase, gaussian_dual_coordinate]
      exact mul_comm _ _

theorem gaussian_mul (a : ℝ) (z w : ℂ) :
    gaussian a (z * w) = gaussian (a * ‖z‖ ^ 2) w := by
  unfold gaussian
  rw [norm_mul]
  congr 1
  push_cast
  ring

theorem gaussian_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun z : O => gaussian a (ringComplex z)) := by
  simpa only [gaussian, Complex.ofReal_pow] using QuadraticPhase.Eisenstein.eis_gaussian_summable ha

theorem paperE_norm (z : ℂ) : ‖paperE z‖ = 1 := tracePhase_norm _

theorem weighted_gaussian_summable {R : Type*} [Fintype R]
    (q : O → R) (P : R → ℂ) (a : ℝ) (ha : 0 < a) :
    Summable (fun z : O => P (q z) * gaussian a (ringComplex z)) := by
  let C : ℝ := ∑ r : R, ‖P r‖
  have hP (r : R) : ‖P r‖ ≤ C :=
    Finset.single_le_sum (fun r _ => norm_nonneg (P r)) (Finset.mem_univ r)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _
    ((gaussian_summable a ha).norm.mul_left C)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hP _) (norm_nonneg _)

theorem gaussian_coset_poisson (a : ℝ) (ha : 0 < a) (c : O) (hc : c ≠ 0) (r : O) :
    (∑' z : O, gaussian a (ringComplex (r + c * z))) =
      ((2 / (Real.sqrt 3 * (a * ‖ringComplex c‖ ^ 2)) : ℝ) : ℂ) *
        ∑' h : O, paperE (ringComplex r * ringComplex h / ringComplex c) *
          gaussian (4 / (3 * (a * ‖ringComplex c‖ ^ 2))) (ringComplex h) := by
  have hc' := ringComplex_ne_zero hc
  have hscale : 0 < a * ‖ringComplex c‖ ^ 2 :=
    mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hc'))
  have he (z : O) : ringComplex (r + c * z) =
      ringComplex c * (ringComplex z + ringComplex r / ringComplex c) := by
    rw [map_add, map_mul]
    field_simp
    ring
  simp_rw [he, gaussian_mul]
  rw [shifted_lattice_poisson _ hscale]
  congr 1
  apply tsum_congr
  intro h
  congr 2
  ring

theorem finite_gaussian_phase_sum {R : Type*} [Fintype R]
    (a : ℝ) (ha : 0 < a) (b : R → ℂ) (P : R → ℂ) (K : ℂ) :
    (∑ r : R, P r * (K * ∑' h : O,
      paperE (b r * ringComplex h) * gaussian a (ringComplex h))) =
      K * ∑' h : O, (∑ r : R, P r * paperE (b r * ringComplex h)) *
        gaussian a (ringComplex h) := by
  have hs (r : R) : Summable (fun h : O =>
      P r * (paperE (b r * ringComplex h) * gaussian a (ringComplex h))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [norm_mul, paperE_norm, one_mul] using (gaussian_summable a ha).norm
  simp_rw [mul_left_comm (P _) K, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun r _ => (hs r).mul_left K)]
  apply tsum_congr
  intro h
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr (NeZero.ne c))
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

theorem periodic_gaussian_poisson (P : O ⧸ Ideal.span {c} → ℂ)
    (a : ℝ) (ha : 0 < a) :
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian a (ringComplex z)) =
      ((2 / (Real.sqrt 3 * (a * ‖ringComplex c‖ ^ 2)) : ℝ) : ℂ) *
        ∑' h : O, (∑ r : O ⧸ Ideal.span {c}, P r *
          TraceCharacter.traceCharacter c (NeZero.ne c)
            (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          gaussian (4 / (3 * (a * ‖ringComplex c‖ ^ 2))) (ringComplex h) := by
  rw [SchwartzPlanePoisson.GaussianAbelPartition.tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c})) P (fun z => gaussian a (ringComplex z))
    (weighted_gaussian_summable _ P a ha)]
  have hfiber (r : O ⧸ Ideal.span {c}) :=
    GaussianFiberEquiv.fiber_tsum c (NeZero.ne c) r
      (GaussianShiftedPartition.representative c r)
      (GaussianShiftedPartition.representative_spec c r)
      (fun z => gaussian a (ringComplex z))
  simp_rw [hfiber, gaussian_coset_poisson a ha c (NeZero.ne c)]
  have hd : 0 < 4 / (3 * (a * ‖ringComplex c‖ ^ 2)) := by
    exact div_pos (by norm_num) (mul_pos (by norm_num)
      (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero (NeZero.ne c))))))
  have h := finite_gaussian_phase_sum (4 / (3 * (a * ‖ringComplex c‖ ^ 2))) hd
    (fun r => ringComplex (GaussianShiftedPartition.representative c r) / ringComplex c) P
    (((2 / (Real.sqrt 3 * (a * ‖ringComplex c‖ ^ 2)) : ℝ) : ℂ))
  simp_rw [TraceCharacter.traceCharacter, residueTraceQuotientChar_frequency]
  convert h using 1 <;>
    congr 1 <;> (try ext r) <;>
    simp only [div_mul_eq_mul_div]

theorem primitive_gaussian_poisson (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (a : ℝ) (ha : 0 < a) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian a (ringComplex z)) =
      ((2 / (Real.sqrt 3 * (a * ‖ringComplex c‖ ^ 2)) : ℝ) : ℂ) *
        TraceCharacter.gaussScalar c χ *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          gaussian (4 / (3 * (a * ‖ringComplex c‖ ^ 2))) (ringComplex h) := by
  have hp := periodic_gaussian_poisson c χ a ha
  simp_rw [TraceCharacter.transform_eq c χ hχ] at hp
  rw [hp]
  simp_rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

def parameter (t : ℝ) : ℝ := 2 * t / (Real.sqrt 3 * ‖ringComplex c‖)

def theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) : ℂ :=
  ∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
    gaussian (parameter c t) (ringComplex z)

theorem parameter_pos (t : ℝ) (ht : 0 < t) : 0 < parameter c t := by
  unfold parameter
  exact div_pos (mul_pos (by norm_num) ht)
    (mul_pos (Real.sqrt_pos.mpr (by norm_num))
      (norm_pos_iff.mpr (ringComplex_ne_zero (NeZero.ne c))))

theorem theta_summable (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : 0 < t) :
    Summable (fun z : O => χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      gaussian (parameter c t) (ringComplex z)) :=
  weighted_gaussian_summable _ χ _ (parameter_pos c t ht)

theorem parameter_dual (t : ℝ) (ht : 0 < t) :
    4 / (3 * (parameter c t * ‖ringComplex c‖ ^ 2)) = parameter c (1 / t) := by
  have hn : ‖ringComplex c‖ ≠ 0 := norm_ne_zero_iff.mpr (ringComplex_ne_zero (NeZero.ne c))
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  unfold parameter
  field_simp
  ring_nf
  norm_num [Real.sq_sqrt]

theorem parameter_prefactor (t : ℝ) (ht : 0 < t) :
    2 / (Real.sqrt 3 * (parameter c t * ‖ringComplex c‖ ^ 2)) =
      1 / (‖ringComplex c‖ * t) := by
  have hn : ‖ringComplex c‖ ≠ 0 := norm_ne_zero_iff.mpr (ringComplex_ne_zero (NeZero.ne c))
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  unfold parameter
  field_simp

theorem theta_functional_equation (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) (ht : 0 < t) :
    theta c χ t = (TraceCharacter.normalizedGauss c χ / (t : ℂ)) *
      theta c χ⁻¹ (1 / t) := by
  have hp := primitive_gaussian_poisson c χ hχ (parameter c t) (parameter_pos c t ht)
  rw [parameter_dual c t ht, parameter_prefactor c t ht] at hp
  change theta c χ t =
    (((1 / (‖ringComplex c‖ * t) : ℝ) : ℂ) * TraceCharacter.gaussScalar c χ) *
      theta c χ⁻¹ (1 / t) at hp
  rw [hp]
  congr 1
  unfold TraceCharacter.normalizedGauss
  push_cast
  ring

def constantTerm (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ := χ 0

omit [NeZero c] in
theorem constantTerm_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    constantTerm c χ = if IsUnit c then 1 else 0 := by
  unfold constantTerm
  by_cases hu : IsUnit c
  · rw [if_pos hu]
    have h10 : (1 : O ⧸ Ideal.span {c}) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [Ideal.span_singleton_eq_top.mpr hu]
      trivial
    rw [← h10, map_one]
  · rw [if_neg hu]
    apply MulChar.map_nonunit
    intro hz
    have h10 := (isUnit_zero_iff.mp hz).symm
    have h1 : (1 : O) ∈ Ideal.span {c} := Ideal.Quotient.eq_zero_iff_mem.mp h10
    exact hu (Ideal.span_singleton_eq_top.mp ((Ideal.eq_top_iff_one _).mpr h1))

omit [NeZero c] in
theorem theta_zero_term (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) :
    χ (Ideal.Quotient.mk (Ideal.span {c}) (0 : O)) *
      gaussian (parameter c t) (ringComplex 0) = constantTerm c χ := by
  simp [gaussian, constantTerm]

theorem theta_inversion (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) (ht : 0 < t) :
    theta c χ (1 / t) = (TraceCharacter.normalizedGauss c χ * (t : ℂ)) * theta c χ⁻¹ t := by
  have h := theta_functional_equation c χ hχ (1 / t) (one_div_pos.mpr ht)
  simpa only [one_div, Complex.ofReal_inv, inv_inv, div_inv_eq_mul, one_mul] using h

theorem theta_root_nonzero (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) : TraceCharacter.normalizedGauss c χ ≠ 0 := by
  have h := TraceCharacter.normalizedGauss_norm c χ hχ
  intro hz
  rw [hz, norm_zero] at h
  exact zero_ne_one h

theorem embedding_unit_norm (u : Oˣ) : ‖ringComplex (u : O)‖ = 1 := by
  have h := ringComplex_norm_sq_eq_absNorm_span (u : O)
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top, Nat.cast_one] at h
  nlinarith [norm_nonneg (ringComplex (u : O))]

omit [NeZero c] in

theorem theta_mul_global_unit (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (u : Oˣ) :
    theta c χ t = χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) * theta c χ t := by
  have h := u.mulLeft.tsum_eq (fun z : O =>
    χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian (parameter c t) (ringComplex z))
  calc
    theta c χ t = ∑' z : O,
        χ (Ideal.Quotient.mk (Ideal.span {c}) ((u : O) * z)) *
          gaussian (parameter c t) (ringComplex ((u : O) * z)) := h.symm
    _ = χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) * theta c χ t := by
      rw [theta, ← tsum_mul_left]
      apply tsum_congr
      intro z
      simp only [map_mul, gaussian, norm_mul, embedding_unit_norm, one_mul, mul_assoc]

omit [NeZero c] in

theorem theta_eq_zero_of_global_unit (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ)
    (u : Oˣ) (hu : χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) ≠ 1) :
    theta c χ t = 0 :=
  eq_zero_of_mul_eq_self_left hu (theta_mul_global_unit c χ t u).symm

omit [NeZero c] in
theorem global_unit_invariant_of_theta_ne_zero
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : theta c χ t ≠ 0) :
    ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1 := by
  intro u
  by_contra hu
  exact ht (theta_eq_zero_of_global_unit c χ t u hu)

end GaussianTheta

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open Set Filter Asymptotics MeasureTheory
open scoped Topology BigOperators
namespace PeriodicThetaRegularity
open ThetaProduct EisensteinTheta HeckeTheta

theorem rectangularPair_f_continuous (a b : UnitAddCircle) (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) :
    ContinuousOn (rectangularPair a b u v hu hv).f (Ioi 0) :=
  (scaledEvenPair_f_continuous a u hu).mul (scaledEvenPair_f_continuous b v hv)

theorem pair_f_continuous {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    ContinuousOn (pair w).f (Ioi 0) := by
  have h : ContinuousOn (fun t => ∑ p : (Fin N × Fin N) × Fin 2,
      w p.1 * (parityPair p.1.1 p.1.2 N (Nat.cast_pos.mpr (NeZero.pos N)) p.2).f t)
      (Ioi 0) := by
    apply continuousOn_finsetSum
    intro p _
    exact continuousOn_const.mul
      (rectangularPair_f_continuous (xShift p.1.1 p.1.2 N p.2)
        (yShift p.1.2 N p.2) _ _ _ _)
  apply h.congr
  intro t _
  simp only [pair, finitePair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem theta_continuous {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    ContinuousOn (theta w) (Ioi 0) :=
  (pair_f_continuous w).congr (fun _t ht => theta_eq_pair w ht)

theorem theta_locallyIntegrable {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    LocallyIntegrableOn (theta w) (Ioi 0) :=
  (theta_continuous w).locallyIntegrableOn measurableSet_Ioi

theorem theta_rapid {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (r : ℝ) :
    (fun t => theta w t - w (0,0)) =O[atTop] (fun t : ℝ => t ^ r) := by
  apply ((pair w).hf_top r).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [theta_eq_pair w ht, pair_f₀]

theorem scaledTheta_continuous {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (A : ℝ) (hA : 0 < A) :
    ContinuousOn (fun t => theta w (A * t)) (Ioi 0) :=
  (theta_continuous w).comp (by fun_prop) (fun t ht => mul_pos hA ht)

theorem scaledTheta_rapid {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (A : ℝ) (hA : 0 < A) (r : ℝ) :
    (fun t => theta w (A * t) - w (0,0)) =O[atTop] (fun t : ℝ => t ^ r) :=
  rapid_rescale (theta w) (w (0,0)) (theta_rapid w) hA r

def primitivePair {N M : ℕ} [NeZero N] [NeZero M]
    (w : Fin N × Fin N → ℂ) (v : Fin M × Fin M → ℂ)
    (A : ℝ) (hA : 0 < A) (ε : ℂ) (hε : ε ≠ 0)
    (hfeq : ∀ t : ℝ, 0 < t →
      theta w (A / t) = ε * (t : ℂ) * theta v (A * t)) : WeakFEPair ℂ where
  f := fun t => theta w (A * t)
  g := fun t => theta v (A * t)
  k := 1
  ε := ε
  f₀ := w (0,0)
  g₀ := v (0,0)
  hf_int := (scaledTheta_continuous w A hA).locallyIntegrableOn measurableSet_Ioi
  hg_int := (scaledTheta_continuous v A hA).locallyIntegrableOn measurableSet_Ioi
  hk := zero_lt_one
  hε := hε
  h_feq t ht := by
    simpa only [mul_one_div, Real.rpow_one, smul_eq_mul] using hfeq t ht
  hf_top := scaledTheta_rapid w A hA
  hg_top := scaledTheta_rapid v A hA

end PeriodicThetaRegularity

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical Topology
open Filter Asymptotics

namespace ThetaRegularity

abbrev O := Eisenstein.O

open Eisenstein  GaussianTheta

theorem norm_gaussian (a : ℝ) (z : ℂ) :
    ‖gaussian a z‖ = Real.exp (-Real.pi * a * ‖z‖ ^ 2) := by
  simp [gaussian, Complex.norm_exp, pow_two, Complex.mul_re, Complex.mul_im]

theorem lattice_gap (z : O) (hz : z ≠ 0) : 1 ≤ ‖ringComplex z‖ ^ 2 := by
  rw [ringComplex_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {z}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hz)

theorem gaussian_le_inverse_square (a : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    ‖gaussian a z‖ ≤ ((1 + a * ‖z‖ ^ 2) ^ 2)⁻¹ := by
  let x := a * ‖z‖ ^ 2
  have hx : 0 ≤ x := mul_nonneg ha (sq_nonneg _)
  have h1 : 1 + x ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hs : (1 + x) ^ 2 ≤ Real.exp (Real.pi * x) := calc
    _ ≤ (Real.exp x) ^ 2 := by gcongr
    _ = Real.exp (2 * x) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right Real.two_le_pi hx)
  rw [norm_gaussian]
  have hexp : -Real.pi * a * ‖z‖ ^ 2 = -(Real.pi * x) := by dsimp [x]; ring
  rw [hexp]
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr hs

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr (NeZero.ne c))
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

def decayRate : ℝ := Real.pi * parameter c 1

theorem decayRate_pos : 0 < decayRate c :=
  mul_pos Real.pi_pos (parameter_pos c 1 one_pos)

omit [NeZero c] in
theorem parameter_eq (t : ℝ) : parameter c t = parameter c 1 * t := by
  unfold parameter
  ring

omit [NeZero c] in
theorem norm_gaussian_parameter (t : ℝ) (z : ℂ) :
    ‖gaussian (parameter c t) z‖ = Real.exp (-decayRate c * t * ‖z‖ ^ 2) := by
  rw [norm_gaussian, parameter_eq]
  congr 1
  unfold decayRate
  ring

theorem coefficient_norm_le_one (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (r : O ⧸ Ideal.span {c}) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    have hu : ‖χ (u : O ⧸ Ideal.span {c})‖ = 1 := by
      simpa only [MulChar.coe_equivToUnitHom] using
        Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    exact hu.le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    norm_num

theorem term_norm_le (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (z : O) :
    ‖χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      gaussian (parameter c t) (ringComplex z)‖ ≤
        Real.exp (-decayRate c * t * ‖ringComplex z‖ ^ 2) := by
  rw [norm_mul, norm_gaussian_parameter]
  exact mul_le_of_le_one_left (Real.exp_nonneg _) (coefficient_norm_le_one c χ _)

theorem continuousOn_theta_above (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (δ : ℝ) (hδ : 0 < δ) : ContinuousOn (theta c χ) (Set.Ioi δ) := by
  apply continuousOn_tsum (u := fun z : O => ‖gaussian (parameter c δ) (ringComplex z)‖)
  · intro z
    unfold gaussian parameter
    fun_prop
  · exact (gaussian_summable _ (parameter_pos c δ hδ)).norm
  · intro z t ht
    apply (term_norm_le c χ t z).trans
    rw [norm_gaussian_parameter]
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ decayRate c * ‖ringComplex z‖ ^ 2 :=
      mul_nonneg (decayRate_pos c).le (sq_nonneg _)
    have htd : δ < t := ht
    nlinarith

theorem continuousAt_theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 0 < t) : ContinuousAt (theta c χ) t := by
  have h := continuousOn_theta_above c χ (t / 2) (half_pos ht)
  exact h.continuousAt (isOpen_Ioi.mem_nhds (show t / 2 < t by linarith))

theorem continuousOn_theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    ContinuousOn (theta c χ) (Set.Ioi 0) :=
  fun t ht => (continuousAt_theta c χ t ht).continuousWithinAt

theorem theta_locallyIntegrableOn (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    MeasureTheory.LocallyIntegrableOn (theta c χ) (Set.Ioi 0) :=
  (continuousOn_theta c χ).locallyIntegrableOn measurableSet_Ioi

def tailConstant : ℝ := ∑' z : O, ‖gaussian (parameter c (1 / 2)) (ringComplex z)‖

omit [NeZero c] in
theorem tailConstant_nonneg : 0 ≤ tailConstant c := tsum_nonneg (fun _z => norm_nonneg _)

theorem tailConstant_le_cauchy :
    tailConstant c ≤ 4 * (1 + Real.pi / Real.sqrt (parameter c (1 / 2))) ^ 2 := by
  have ha := parameter_pos c (1 / 2) (by norm_num)
  apply le_trans (Summable.tsum_le_tsum
    (fun z : O => gaussian_le_inverse_square _ ha.le (ringComplex z))
    (gaussian_summable _ ha).norm
    (SchwartzPlanePoisson.scaled_eisenstein_cauchy_summable _ ha))
  exact SchwartzPlanePoisson.scaled_eisenstein_cauchy_bound _ ha

theorem tailConstant_le_linear :
    tailConstant c ≤ 8 * (1 + Real.pi ^ 2 * Real.sqrt 3 * ‖ringComplex c‖) := by
  have ha := parameter_pos c (1 / 2) (by norm_num)
  have hs : (Real.pi / Real.sqrt (parameter c (1 / 2))) ^ 2 =
      Real.pi ^ 2 * Real.sqrt 3 * ‖ringComplex c‖ := by
    rw [div_pow, Real.sq_sqrt ha.le]
    simp only [parameter]
    norm_num
    field_simp
  have h := tailConstant_le_cauchy c
  have hsq := sq_nonneg (1 - Real.pi / Real.sqrt (parameter c (1 / 2)))
  nlinarith

theorem tail_eq_tsum (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : 0 < t) :
    theta c χ t - constantTerm c χ = ∑' z : O, if z = 0 then 0 else
      χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian (parameter c t) (ringComplex z) := by
  have h := (theta_summable c χ t ht).tsum_eq_add_tsum_ite (0 : O)
  rw [theta_zero_term c χ t] at h
  exact sub_eq_iff_eq_add.mpr (by simpa only [theta, add_comm] using h)

theorem tail_term_bound (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 1 ≤ t) (z : O) :
    ‖if z = 0 then (0 : ℂ) else
      χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian (parameter c t) (ringComplex z)‖ ≤
      Real.exp (-decayRate c * t / 2) *
        ‖gaussian (parameter c (1 / 2)) (ringComplex z)‖ := by
  by_cases hz : z = 0
  · simp only [if_pos hz, norm_zero]
    positivity
  · rw [if_neg hz]
    apply (term_norm_le c χ t z).trans
    rw [norm_gaussian_parameter, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn := lattice_gap z hz
    have hβ := decayRate_pos c
    have hprod : 0 ≤ (t - 1) * (‖ringComplex z‖ ^ 2 - 1) :=
      mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hn)
    have hineq : t / 2 + ‖ringComplex z‖ ^ 2 / 2 ≤ t * ‖ringComplex z‖ ^ 2 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hineq hβ.le]

theorem theta_tail_bound (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : 1 ≤ t) :
    ‖theta c χ t - constantTerm c χ‖ ≤
      tailConstant c * Real.exp (-decayRate c * t / 2) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [tail_eq_tsum c χ t ht0]
  have hsum := (gaussian_summable _ (parameter_pos c (1 / 2) (by norm_num))).norm
  have hmajor := hsum.mul_left (Real.exp (-decayRate c * t / 2))
  have hnorm := Summable.of_nonneg_of_le (fun z => norm_nonneg _)
    (tail_term_bound c χ t ht) hmajor
  apply (norm_tsum_le_tsum_norm hnorm).trans
  have h := Summable.tsum_le_tsum (tail_term_bound c χ t ht) hnorm hmajor
  simpa only [tsum_mul_left, tailConstant, mul_comm] using h

theorem theta_tail_bound_conductor (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖theta c χ t - constantTerm c χ‖ ≤
      8 * (1 + Real.pi ^ 2 * Real.sqrt 3 * ‖ringComplex c‖) *
        Real.exp (-decayRate c * t / 2) :=
  (theta_tail_bound c χ t ht).trans
    (mul_le_mul_of_nonneg_right (tailConstant_le_linear c) (Real.exp_nonneg _))

theorem theta_tail_isBigO_exp (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    (fun t : ℝ => theta c χ t - constantTerm c χ) =O[atTop]
      (fun t : ℝ => Real.exp (-(decayRate c / 2) * t)) := by
  apply isBigO_iff.mpr
  refine ⟨tailConstant c, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have he : -(decayRate c / 2) * t = -decayRate c * t / 2 := by ring
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), he] using theta_tail_bound c χ t ht

theorem theta_tail_isBigO_rpow (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (r : ℝ) :
    (fun t : ℝ => theta c χ t - constantTerm c χ) =O[atTop] (fun t : ℝ => t ^ r) :=
  (theta_tail_isBigO_exp c χ).trans
    (isLittleO_exp_neg_mul_rpow_atTop (half_pos (decayRate_pos c)) r).isBigO

end ThetaRegularity

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators
namespace HeckePrimitive
open HeckeFamily

variable (c : O) [NeZero c]

private theorem span_ne_bot : Ideal.span ({c} : Set O) ≠ ⊥ := by
  simpa only [ne_eq, Ideal.span_singleton_eq_bot] using NeZero.ne c

private instance : Fintype (O ⧸ Ideal.span {c}) := by
  letI : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (span_ne_bot c)
  exact Fintype.ofFinite _

def character (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1) : Character :=
  Character.ofResidue (Ideal.span {c}) (span_ne_bot c) χ hu

omit [NeZero c] in
theorem inverse_unit_trivial (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1) :
    ∀ u : Oˣ, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1 := by
  intro u
  rw [MulChar.inv_apply_eq_inv', hu, inv_one]

def scale : ℝ := GaussianTheta.parameter c 1

theorem scale_pos : 0 < scale c := GaussianTheta.parameter_pos c 1 zero_lt_one

omit [NeZero c] in
theorem parameter_eq_scale_mul (t : ℝ) : GaussianTheta.parameter c t = scale c * t := by
  unfold scale GaussianTheta.parameter
  ring

theorem gaussianTheta_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1) (t : ℝ) :
    GaussianTheta.theta c χ t = HeckeTheta.theta (coefficients (character c χ hu))
      (scale c * t) := by
  unfold GaussianTheta.theta HeckeTheta.theta
  rw [← coordinateEquiv.tsum_eq]
  apply tsum_congr
  intro n
  rw [periodicCoeff_eq_elementCoeff]
  change χ (Ideal.Quotient.mk (Ideal.span {c}) (coordinateElement n.1 n.2)) *
      GaussianTheta.gaussian (GaussianTheta.parameter c t)
        (ringComplex (coordinateElement n.1 n.2)) = _
  congr 1
  unfold GaussianTheta.gaussian
  rw [Complex.ofReal_exp]
  congr 1
  rw [← Complex.ofReal_pow, ringComplex_norm_sq_eq_absNorm_span,
    ← normForm_eq_absNorm_span, parameter_eq_scale_mul]
  push_cast
  ring

def pair (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) : WeakFEPair ℂ :=
  PeriodicThetaRegularity.primitivePair
    (coefficients (character c χ hu))
    (coefficients (character c χ⁻¹ (inverse_unit_trivial c χ hu)))
    (scale c) (scale_pos c) (TraceCharacter.normalizedGauss c χ)
    (GaussianTheta.theta_root_nonzero c χ hp) (by
      intro t ht
      have h := GaussianTheta.theta_inversion c χ hp t ht
      rw [gaussianTheta_eq c χ hu,
        gaussianTheta_eq c χ⁻¹ (inverse_unit_trivial c χ hu)] at h
      simpa only [mul_one_div] using h)

@[simp] theorem pair_f (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) :
    (pair c χ hu hp).f t = GaussianTheta.theta c χ t :=
  (gaussianTheta_eq c χ hu t).symm

@[simp] theorem pair_g (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) :
    (pair c χ hu hp).g t = GaussianTheta.theta c χ⁻¹ t :=
  (gaussianTheta_eq c χ⁻¹ (inverse_unit_trivial c χ hu) t).symm

def completedL (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (s : ℂ) : ℂ :=
  (pair c χ hu hp).Λ s / 6

theorem pair_completed_eq_right (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (hs : 1 < s.re) :
    (pair c χ hu hp).Λ s = (scale c : ℂ) ^ (-s) *
      HeckeTheta.completed (coefficients (character c χ hu)) s := by
  let w := coefficients (character c χ hu)
  have h := (pair c χ hu hp).hasMellin hs
  calc
    (pair c χ hu hp).Λ s =
        mellin (fun t => HeckeTheta.theta w (scale c * t) - w (0,0)) s := h.2.symm
    _ = (scale c : ℂ) ^ (-s) * mellin (fun t => HeckeTheta.theta w t - w (0,0)) s :=
      by simpa only [smul_eq_mul] using
        mellin_comp_mul_left (fun t => HeckeTheta.theta w t - w (0,0)) s (scale_pos c)
    _ = (scale c : ℂ) ^ (-s) * HeckeTheta.completed w s := by
      congr 1
      rw [← (HeckeTheta.pair_hasMellin w hs).2]
      unfold mellin
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [HeckeTheta.theta_eq_pair w ht, HeckeTheta.pair_f₀]

theorem pair_completed_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    (pair c χ hu hp).Λ s = (scale c : ℂ) ^ (-s) *
      HeckeTheta.completed (coefficients (character c χ hu)) s :=
  HeckeMellinIdentity.scaled_eq (pair c χ hu hp)
    (HeckeTheta.pair (coefficients (character c χ hu))) rfl (HeckeTheta.pair_k _)
    (scale c) (scale_pos c) (fun _ hs => pair_completed_eq_right c χ hu hp hs) h0 h1

theorem symm_completed_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    (pair c χ hu hp).symm.Λ s =
      (pair c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv).Λ s := by
  apply HeckeMellinIdentity.eq_of_f (pair c χ hu hp).symm
    (pair c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv) rfl rfl _ rfl h0 h1
  intro t _
  change (pair c χ hu hp).g t = _
  rw [pair_g, pair_f]

theorem completedL_functional_equation (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedL c χ hu hp (1-s) = TraceCharacter.normalizedGauss c χ *
      completedL c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv s := by
  have h := (pair c χ hu hp).functional_equation s
  change (pair c χ hu hp).Λ (1-s) = TraceCharacter.normalizedGauss c χ *
    (pair c χ hu hp).symm.Λ s at h
  rw [symm_completed_eq c χ hu hp h0 h1] at h
  unfold completedL
  rw [h]
  ring

theorem completedL_eq_gamma_mul_LFunction (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) (hΓ : Complex.Gamma s ≠ 0) :
    completedL c χ hu hp s = (scale c : ℂ)^(-s) * (Real.pi : ℂ)^(-s) *
      Complex.Gamma s * LFunction (character c χ hu) s := by
  unfold completedL
  rw [pair_completed_eq c χ hu hp h0 h1]
  unfold LFunction continuedLattice HeckeTheta.latticeL
  simp only [Complex.cpow_neg]
  have hπ : (Real.pi : ℂ)^s ≠ 0 := by
    exact (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [Real.pi_ne_zero])
  field_simp

end HeckePrimitive

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace HeckePrimitiveSupremum
open HeckeFamily HeckeZeroSupremum

def primitiveZeroRealParts : Set ℝ :=
  {x | ∃ (χ : Character) (s : ℂ), FiniteFourier.IsPrimitiveOnIdeals χ.residue ∧
    (1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧
    LFunction χ s = 0 ∧ s.re = x}

def primitiveSetWithSentinel : Set ℝ := insert (1 / 2) primitiveZeroRealParts

theorem primitiveSet_subset : primitiveSetWithSentinel ⊆ zeroSetWithSentinel := by
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact Set.mem_insert _ _
  · obtain ⟨χ, s, _, hhalf, _, hpole, hz, rfl⟩ := hx
    exact Set.mem_insert_of_mem _ ⟨χ, s, by linarith, hpole, hz, rfl⟩

theorem primitiveSet_bddAbove : BddAbove primitiveSetWithSentinel :=
  zeroSet_bddAbove.mono primitiveSet_subset

theorem primitiveSet_nonempty : primitiveSetWithSentinel.Nonempty :=
  Set.insert_nonempty _ _

theorem beta_eq_primitive_supremum : beta = sSup primitiveSetWithSentinel := by
  apply le_antisymm
  · apply csSup_le zeroSet_nonempty
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact le_csSup primitiveSet_bddAbove (Set.mem_insert _ _)
    · by_cases hhalf : (1 / 2 : ℝ) ≤ x
      · obtain ⟨χ, s, hpos, hpole, hz, rfl⟩ := hx
        obtain ⟨ψ, hp, hpoleψ, hzψ⟩ :=
          HeckeFiniteDeletion.exists_primitive_zero χ hpos hpole hz
        apply le_csSup primitiveSet_bddAbove
        exact Set.mem_insert_of_mem _ ⟨ψ, s, hp, hhalf,
          zeroRealParts_le_one ⟨χ, s, hpos, hpole, hz, rfl⟩, hpoleψ, hzψ, rfl⟩
      · exact (le_of_not_ge hhalf).trans
          (le_csSup primitiveSet_bddAbove (Set.mem_insert _ _))
  · exact csSup_le_csSup zeroSet_bddAbove primitiveSet_nonempty primitiveSet_subset

theorem exists_primitive_zero_near_beta {ε : ℝ} (hε : 0 < ε)
    (hsmall : (1 / 2 : ℝ) ≤ beta - ε) :
    ∃ (χ : Character) (s : ℂ), FiniteFourier.IsPrimitiveOnIdeals χ.residue ∧
      (1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧
      LFunction χ s = 0 ∧ beta - ε < s.re := by
  rw [beta_eq_primitive_supremum] at hsmall ⊢
  obtain ⟨x, hx, hlt⟩ := Supremum.exists_gt_supremum_sub_of_insert
    primitiveSet_bddAbove hε hsmall
  obtain ⟨χ, s, hp, hhalf, hone, hpole, hz, rfl⟩ := hx
  exact ⟨χ, s, hp, hhalf, hone, hpole, hz, hlt⟩

end HeckePrimitiveSupremum

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex
namespace HeckeFamily

theorem idealCoeff_inverse_conj (χ : Character) (J : Ideal O) :
    idealCoeff χ.inverse J=conj (idealCoeff χ J) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  by_cases hJ : J=0
  · subst J
    rw [map_zero,map_zero,map_zero]
  have hg := cubicIdealGenerator_ne_zero J hJ
  rw [←span_cubicIdealGenerator J,
    idealCoeff_span χ.inverse hg,idealCoeff_span χ hg]
  exact (MulChar.star_apply' χ.residue _).symm

theorem idealTerm_inverse_conj (χ : Character) (s : ℂ) (J : Ideal O) :
    idealTerm χ.inverse s J=conj (idealTerm χ (conj s) J) := by
  by_cases hJ : J=0
  · subst J
    simp only [idealTerm,map_zero,zero_div]
  have hN : (0 : ℝ)< J.absNorm := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hpow := Complex.cpow_conj ((J.absNorm : ℝ) : ℂ) (conj s)
    (by rw [Complex.arg_ofReal_of_nonneg hN.le]; exact Real.pi_ne_zero.symm)
  simp only [conj_ofReal, conj_conj] at hpow
  unfold idealTerm
  rw [idealCoeff_inverse_conj,map_div₀]
  congr 1

theorem LFunction_inverse_conj (χ : Character) (hχ : χ.residue≠1) (s : ℂ) :
    LFunction χ.inverse s=conj (LFunction χ (conj s)) := by
  have hi : χ.inverse.residue≠1 := by
    change χ.residue⁻¹≠1
    simpa only [ne_eq,inv_eq_one] using hχ
  have hA := LFunction_entire_nonprincipal χ.inverse hi
  have hB : Differentiable ℂ (fun z => conj (LFunction χ (conj z))) := by
    intro z
    simpa only [Function.comp_def,conj_conj] using
      (LFunction_entire_nonprincipal χ hχ (conj z)).conj_conj
  have he : LFunction χ.inverse=(fun z => conj (LFunction χ (conj z))) := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hA).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hB) (z₀ := (2 : ℂ))
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num : (1 : ℝ)<(2 : ℂ).re)] with z hz
    rw [LFunction_eq_ideal_tsum χ.inverse hz,LFunction_eq_ideal_tsum χ (by simpa using hz),conj_tsum]
    exact tsum_congr (idealTerm_inverse_conj χ z)
  exact congr_fun he s

end HeckeFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators
namespace HeckeReciprocalBound
open HeckeFamily

def bound (σ : ℝ) : ℝ :=
  ∑' I : Ideal O, ‖fullIdealWeight (σ : ℂ) I‖

theorem normWeight_le_of_re_ge {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) (I : Ideal O) :
    ‖fullIdealWeight s I‖ ≤
      ‖fullIdealWeight (σ : ℂ) I‖ := by
  by_cases hI : I = 0
  · simp [hI, fullIdealWeight]
  · have hN : (1 : ℝ) ≤ Ideal.absNorm I := by
      have hpos : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff I).mpr (Ring.HasFiniteQuotients.finiteQuotient hI))
      exact_mod_cast hpos
    simp only [fullIdealWeight, hI, ite_false]
    have hn : (0 : ℝ) < Ideal.absNorm I := lt_of_lt_of_le zero_lt_one hN
    rw [show (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hs)

theorem reciprocal_norm_le (χ : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖HeckeReciprocal.reciprocal χ s‖ ≤ bound σ := by
  have hs1 : 1 < s.re := hσ.trans_le hs
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs1
  have hsp : s ≠ 1 := by intro h; norm_num [h] at hs1
  rw [HeckeReciprocal.reciprocal_eq_inv χ hs0 hsp, LFunction_eq_series χ hs1,
    ← IdealEuler.inverseSeries_eq_inv _ (idealCoeff_norm_le_one χ) s hs1]
  have hsum := IdealEuler.inverse_summable_norm (idealCoeff χ)
    (idealCoeff_norm_le_one χ) s hs1
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (fullIdealWeight_summable_norm (σ : ℂ) (by simpa using hσ))
  intro I
  change ‖(UniqueFactorizationMonoid.moebius I : ℂ) *
    (idealCoeff χ I * fullIdealWeight s I)‖ ≤ _
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖fullIdealWeight s I‖ := by
      apply (mul_le_of_le_one_left (by positivity)
        (IdealCoprimeBilinearSieve.moebius_norm_le_one I)).trans
      exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)
    _ ≤ _ := normWeight_le_of_re_ge hs I

end HeckeReciprocalBound

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology
open Filter Asymptotics Set MeasureTheory

namespace HeckeStrip

def gammaConstant : ℝ := Real.Gamma (11 / 10) / Real.Gamma (19 / 10)

theorem gammaConstant_pos : 0 < gammaConstant :=
  div_pos (Real.Gamma_pos_of_pos (by norm_num)) (Real.Gamma_pos_of_pos (by norm_num))

theorem gamma_ratio_left_bound (t : ℝ) :
    ‖Complex.Gamma (1 - ((-(1 / 10) : ℂ) + t * Complex.I)) /
      Complex.Gamma ((-(1 / 10) : ℂ) + t * Complex.I)‖ ≤
        gammaConstant * (3 + |t|) ^ 2 := by
  let s : ℂ := -(1 / 10) + t * Complex.I
  have hb := Gamma_shifted_pair_bound
    (1 / 2) (3 / 5) (-t) 2 (by norm_num) (by norm_num)
  simp only [Complex.ofReal_neg] at hb
  have hnum : ((1 / 2 : ℝ) : ℂ) + ((3 / 5 : ℝ) + (-t) * Complex.I) = 1 - s := by
    dsimp [s]; push_cast; ring
  have hden : ((1 / 2 : ℝ) : ℂ) - ((3 / 5 : ℝ) + (-t) * Complex.I) + (2 : ℕ) = s + 2 := by
    dsimp [s]; push_cast; ring
  rw [hnum, hden] at hb
  norm_num only [show (1 / 2 : ℝ) + 3 / 5 = 11 / 10 by norm_num,
    show (1 / 2 : ℝ) - 3 / 5 + (2 : ℕ) = 19 / 10 by norm_num] at hb
  have heq : Complex.Gamma (1 - s) / Complex.Gamma s =
      (∏ k ∈ Finset.range 2, (s + k)) *
        (Complex.Gamma (1 - s) / Complex.Gamma (s + 2)) := by
    rw [div_eq_mul_inv, CubicGammaExponential.inverse_Gamma_shift s 2]
    simp only [Nat.cast_ofNat, div_eq_mul_inv]
    ring
  have hs : ‖s‖ ≤ 1 / 10 + |t| := by
    simpa [s, norm_mul] using norm_add_le (-(1 / 10) : ℂ) ((t : ℂ) * Complex.I)
  have hf := norm_Gamma_shift_factor s 2
  have hf' : ‖∏ k ∈ Finset.range 2, (s + k)‖ ≤ (3 + |t|) ^ 2 := by
    have hs2 : ‖s‖ + (2 : ℝ) ≤ 3 + |t| := by linarith
    exact hf.trans (pow_le_pow_left₀ (by positivity) hs2 2)
  change ‖Complex.Gamma (1 - s) / Complex.Gamma s‖ ≤ _
  rw [heq, norm_mul]
  exact (mul_le_mul hf' hb (norm_nonneg _) (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem gamma_ratio_left_bound_of_re (z : ℂ) (hz : z.re = -(1 / 10)) :
    ‖Complex.Gamma (1 - z) / Complex.Gamma z‖ ≤ gammaConstant * (3 + |z.im|) ^ 2 := by
  have he : (-(1 / 10) : ℂ) + z.im * Complex.I = z := by
    simpa only [hz, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using Complex.re_add_im z
  simpa only [he] using gamma_ratio_left_bound z.im

def completionScale (Q : ℝ) : ℝ := Real.sqrt (3 * Q) / (2 * Real.pi)

theorem completionScale_pos (Q : ℝ) (hQ : 0 < Q) : 0 < completionScale Q := by
  unfold completionScale
  positivity

theorem completionScale_left_power (Q : ℝ) (hQ : 0 < Q) :
    completionScale Q ^ (6 / 5 : ℝ) =
      (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ) := by
  have he : completionScale Q = (Real.sqrt 3 / (2 * Real.pi)) * Real.sqrt Q := by
    unfold completionScale
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  rw [he, Real.mul_rpow (by positivity) (Real.sqrt_nonneg _)]
  congr 1
  rw [Real.sqrt_eq_rpow Q, ← Real.rpow_mul hQ.le]
  norm_num

def leftConstant : ℝ :=
  (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * gammaConstant

theorem leftConstant_pos : 0 < leftConstant :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _) gammaConstant_pos

theorem left_boundary_of_functional_equation (Q D : ℝ) (hQ : 0 < Q) (_hD : 0 ≤ D)
    (L Ldual : ℂ → ℂ) (ε : ℂ) (hε : ‖ε‖ = 1)
    (hfe : ∀ z : ℂ, z.re = -(1 / 10) → L z =
      ε * (completionScale Q : ℂ) ^ (1 - 2 * z) *
        (Complex.Gamma (1 - z) / Complex.Gamma z) * Ldual (1 - z))
    (hdual : ∀ z : ℂ, z.re = 11 / 10 → ‖Ldual z‖ ≤ D)
    (z : ℂ) (hz : z.re = -(1 / 10)) :
    ‖L z‖ ≤ leftConstant * D * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hscale : ‖(completionScale Q : ℂ) ^ (1 - 2 * z)‖ =
      (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (completionScale_pos Q hQ)]
    have hre : (1 - 2 * z).re = 6 / 5 := by simp [hz]; norm_num
    rw [hre, completionScale_left_power Q hQ]
  have hd : ‖Ldual (1 - z)‖ ≤ D := hdual _ (by simp [hz]; norm_num)
  rw [hfe z hz, norm_mul, norm_mul, norm_mul, hε, one_mul, hscale]
  have hg := gamma_ratio_left_bound_of_re z hz
  have hc := gammaConstant_pos
  have hm := mul_le_mul
    (mul_le_mul_of_nonneg_left hg (by positivity)) hd (norm_nonneg _)
    (by positivity : 0 ≤ ((Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ)) *
      (gammaConstant * (3 + |z.im|) ^ 2))
  calc
    _ ≤ ((Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ)) *
        (gammaConstant * (3 + |z.im|) ^ 2) * D := hm
    _ = _ := by unfold leftConstant; ring

def strip : Set ℂ := Complex.re ⁻¹' Ioo (-(1 / 10)) (11 / 10)
def closedStrip : Set ℂ := Complex.re ⁻¹' Icc (-(1 / 10)) (11 / 10)

theorem vertical_strip_of_exp_bound (F : ℂ → ℂ) (C : ℝ)
    (hF : DiffContOnCl ℂ F strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖F z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) → ‖F z‖ ≤ C)
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖F z‖ ≤ C)
    (z : ℂ) (hz : z ∈ closedStrip) : ‖F z‖ ≤ C := by
  obtain ⟨A, B, hA, hB, hgrowth⟩ := hgrowth
  apply PhragmenLindelof.vertical_strip hF ?_ hleft hright hz.1 hz.2
  refine ⟨1, ?_, B, ?_⟩
  · apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 11 / 10 - -(1 / 10))).mpr
    linarith [Real.two_le_pi]
  · apply isBigO_iff.mpr
    refine ⟨A, eventually_inf_principal.mpr (Eventually.of_forall fun z hz => ?_)⟩
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply (hgrowth z hz).trans
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    simp only [one_mul]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp |z.im|]) hB

theorem closure_strip_subset : closure strip ⊆ closedStrip :=
  closure_minimal (fun _ hz => ⟨hz.1.le, hz.2.le⟩)
    (isClosed_Icc.preimage Complex.continuous_re)

theorem shift_norm_lower (z : ℂ) (hz : z ∈ closedStrip) : 1 ≤ ‖z + 2‖ := by
  have h := Complex.re_le_norm (z + 2)
  norm_num at h
  linarith [hz.1]

theorem shift_ne_zero (z : ℂ) (hz : z ∈ closedStrip) : z + 2 ≠ 0 := by
  have h := shift_norm_lower z hz
  intro hzero
  rw [hzero, norm_zero] at h
  norm_num at h

theorem height_le_shift_norm (z : ℂ) (hz : z ∈ closedStrip) :
    3 + |z.im| ≤ 3 * ‖z + 2‖ := by
  have hr := Complex.re_le_norm (z + 2)
  have hi := Complex.abs_im_le_norm (z + 2)
  norm_num at hr hi
  linarith [hz.1]

theorem shift_norm_le_height (z : ℂ) (hz : z ∈ closedStrip) :
    ‖z + 2‖ ≤ 2 * (3 + |z.im|) := by
  have hr : 0 ≤ z.re + 2 := by linarith [hz.1]
  have h := Complex.norm_le_abs_re_add_abs_im (z + 2)
  norm_num [abs_of_nonneg hr] at h
  linarith [hz.2, abs_nonneg z.im]

def normalized (Q : ℝ) (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  L z / (((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) * (z + 2) ^ 2)

theorem norm_normalized (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ) (z : ℂ) :
    ‖normalized Q L z‖ = ‖L z‖ / (Q ^ (3 / 5 : ℝ) * ‖z + 2‖ ^ 2) := by
  simp [normalized, norm_pow,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hQ _)]

theorem normalized_diffContOnCl (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ)
    (hL : DiffContOnCl ℂ L strip) : DiffContOnCl ℂ (normalized Q L) strip := by
  have hqn : ((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)).ne'
  have hd : Differentiable ℂ (fun z : ℂ => ((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) * (z + 2) ^ 2) := by
    fun_prop
  refine ⟨hL.differentiableOn.div hd.differentiableOn ?_, hL.continuousOn.div hd.continuous.continuousOn ?_⟩
  · intro z hz
    exact mul_ne_zero hqn (pow_ne_zero _ (shift_ne_zero z ⟨hz.1.le, hz.2.le⟩))
  · intro z hz
    exact mul_ne_zero hqn (pow_ne_zero _ (shift_ne_zero z (closure_strip_subset hz)))

theorem normalized_exp_bound (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖normalized Q L z‖ ≤ A * Real.exp (B * |z.im|) := by
  obtain ⟨A, B, hA, hB, hg⟩ := hgrowth
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  refine ⟨A / Q ^ (3 / 5 : ℝ), B, div_nonneg hA hq.le, hB, ?_⟩
  intro z hz
  have hn := shift_norm_lower z ⟨hz.1.le, hz.2.le⟩
  have hn2 : 1 ≤ ‖z + 2‖ ^ 2 := by nlinarith
  rw [norm_normalized Q hQ]
  calc
    _ ≤ ‖L z‖ / Q ^ (3 / 5 : ℝ) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hq (by nlinarith)
    _ ≤ (A * Real.exp (B * |z.im|)) / Q ^ (3 / 5 : ℝ) :=
      div_le_div_of_nonneg_right (hg z hz) hq.le
    _ = _ := by ring

theorem normalized_boundary_bound (Q C : ℝ) (hQ : 0 < Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (z : ℂ) (hz : z ∈ closedStrip)
    (hL : ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2) :
    ‖normalized Q L z‖ ≤ 9 * C := by
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  have hn : 0 < ‖z + 2‖ := lt_of_lt_of_le zero_lt_one (shift_norm_lower z hz)
  have hh := height_le_shift_norm z hz
  have hh2 : (3 + |z.im|) ^ 2 ≤ 9 * ‖z + 2‖ ^ 2 := by
    nlinarith [abs_nonneg z.im, norm_nonneg (z + 2)]
  rw [norm_normalized Q hQ]
  apply (div_le_iff₀ (mul_pos hq (sq_pos_of_pos hn))).mpr
  apply hL.trans
  have h := mul_le_mul_of_nonneg_left hh2 (mul_nonneg hC hq.le)
  nlinarith

theorem uniform_strip_bound_of_edges (Q C : ℝ) (hQ : 0 < Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (hright : ∀ z : ℂ, z.re = 11 / 10 →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hn : ‖normalized Q L z‖ ≤ 9 * C := by
    apply vertical_strip_of_exp_bound _ _ (normalized_diffContOnCl Q hQ L hL)
      (normalized_exp_bound Q hQ L hgrowth) ?_ ?_ z hz
    · intro w hw
      apply normalized_boundary_bound Q C hQ hC L w
        (show w ∈ closedStrip from ⟨by rw [hw], by rw [hw]; norm_num⟩) (hleft w hw)
    · intro w hw
      apply normalized_boundary_bound Q C hQ hC L w
        (show w ∈ closedStrip from ⟨by rw [hw]; norm_num, by rw [hw]⟩) (hright w hw)
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  have hnz : 0 < ‖z + 2‖ := lt_of_lt_of_le zero_lt_one (shift_norm_lower z hz)
  rw [norm_normalized Q hQ] at hn
  have hb := (div_le_iff₀ (mul_pos hq (sq_pos_of_pos hnz))).mp hn
  have hh := shift_norm_le_height z hz
  have hh2 : ‖z + 2‖ ^ 2 ≤ 4 * (3 + |z.im|) ^ 2 := by
    nlinarith [norm_nonneg (z + 2), abs_nonneg z.im]
  have h := mul_le_mul_of_nonneg_left hh2 (mul_nonneg (by positivity : 0 ≤ 9 * C) hq.le)
  nlinarith

theorem uniform_strip_bound (Q C : ℝ) (hQ : 1 ≤ Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖L z‖ ≤ C)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  apply uniform_strip_bound_of_edges Q C (lt_of_lt_of_le zero_lt_one hQ) hC L hL
    hgrowth hleft ?_ z hz
  intro w hw
  apply (hright w hw).trans
  have hq : 1 ≤ Q ^ (3 / 5 : ℝ) := Real.one_le_rpow hQ (by norm_num)
  have hh : 1 ≤ (3 + |w.im|) ^ 2 := by nlinarith [abs_nonneg w.im]
  calc
    C ≤ C * Q ^ (3 / 5 : ℝ) := le_mul_of_one_le_right hC hq
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hC (le_trans zero_le_one hq)) hh

theorem uniform_strip_bound_of_functional_equation
    (Q D : ℝ) (hQ : 1 ≤ Q) (hD : 0 ≤ D) (L Ldual : ℂ → ℂ)
    (ε : ℂ) (hε : ‖ε‖ = 1) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hfe : ∀ z : ℂ, z.re = -(1 / 10) → L z =
      ε * (completionScale Q : ℂ) ^ (1 - 2 * z) *
        (Complex.Gamma (1 - z) / Complex.Gamma z) * Ldual (1 - z))
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖L z‖ ≤ D)
    (hdual : ∀ z : ℂ, z.re = 11 / 10 → ‖Ldual z‖ ≤ D)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * ((1 + leftConstant) * D) * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hQ0 := lt_of_lt_of_le zero_lt_one hQ
  have hc := leftConstant_pos
  apply uniform_strip_bound Q ((1 + leftConstant) * D) hQ (by positivity) L hL hgrowth ?_ ?_ z hz
  · intro w hw
    apply (left_boundary_of_functional_equation Q D hQ0 hD L Ldual ε hε hfe hdual w hw).trans
    have hbase : leftConstant * D ≤ (1 + leftConstant) * D := by nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hQ0.le _)) (sq_nonneg _)
  · intro w hw
    apply (hright w hw).trans
    nlinarith

theorem uncompleted_exp_bound (a : ℝ) (ha : 0 < a) (F : ℂ → ℂ)
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closedStrip, ‖F z‖ ≤ C) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ strip,
      ‖(a : ℂ) ^ (-z) * (Complex.Gamma z)⁻¹ * F z‖ ≤
        A * Real.exp (B * |z.im|) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨G, hG, hg⟩ := CubicGammaExponential.inverse_Gamma_strip_exp_bound_complex
    (-(1 / 10)) (11 / 10)
  let S : ℝ := a ^ (-(11 / 10) : ℝ) + a ^ (1 / 10 : ℝ)
  have hS : 0 ≤ S := add_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg ha.le _)
  refine ⟨S * G * C, Real.pi, by positivity, Real.pi_pos.le, ?_⟩
  intro z hz
  have hzc : z ∈ closedStrip := ⟨hz.1.le, hz.2.le⟩
  have haBound : ‖(a : ℂ) ^ (-z)‖ ≤ S := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.neg_re]
    exact rpow_between_endpoints a (-(11 / 10)) (1 / 10) (-z.re)
      ha (by linarith [hz.2]) (by linarith [hz.1])
  rw [norm_mul, norm_mul]
  have hgamma := hg z hzc
  have hprod := mul_le_mul (mul_le_mul haBound hgamma (norm_nonneg _) hS)
    (hF z hzc) (norm_nonneg _) (mul_nonneg hS (mul_nonneg hG.le (Real.exp_nonneg _)))
  nlinarith

theorem mellin_uncompleted_exp_bound (a : ℝ) (ha : 0 < a) (f : ℝ → ℂ)
    (hleft : MellinConvergent f (-(1 / 10) : ℂ))
    (hright : MellinConvergent f (11 / 10 : ℂ)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ strip,
      ‖(a : ℂ) ^ (-z) * (Complex.Gamma z)⁻¹ * mellin f z‖ ≤
        A * Real.exp (B * |z.im|) := by
  apply uncompleted_exp_bound a ha (mellin f)
  obtain ⟨C, hC, hb⟩ := mellin_uniform_strip_bound f
    (-(1 / 10)) (11 / 10) (by simpa using hleft) (by simpa using hright)
  exact ⟨C, hC, fun z hz => hb z hz.1 hz.2⟩

end HeckeStrip
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology BigOperators
open Set MeasureTheory
namespace HeckeStripActual
open HeckeFamily HeckePrimitive

variable (c : O) [NeZero c]

private instance : Fintype (O ⧸ Ideal.span {c}) := by
  letI : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using NeZero.ne c)
  exact Fintype.ofFinite _

def conductor : ℝ := Ideal.absNorm (Ideal.span {c})

theorem conductor_ge_one : 1 ≤ conductor c := by
  unfold conductor
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {c}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact NeZero.ne c)

theorem completionScale_eq_inv :
    HeckeStrip.completionScale (conductor c) = (Real.pi * scale c)⁻¹ := by
  have hn : 0 < ‖ringComplex c‖ := by
    have h := ThetaRegularity.lattice_gap c (NeZero.ne c)
    nlinarith [norm_nonneg (ringComplex c)]
  unfold HeckeStrip.completionScale conductor scale GaussianTheta.parameter
  rw [← ringComplex_norm_sq_eq_absNorm_span,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq (norm_nonneg _)]
  field_simp

theorem completionScale_cpow (s : ℂ) :
    (HeckeStrip.completionScale (conductor c) : ℂ)^s =
      (scale c : ℂ)^(-s) * (Real.pi : ℂ)^(-s) := by
  have ha : 0 < Real.pi * scale c := mul_pos Real.pi_pos (scale_pos c)
  have hprod : ((Real.pi * scale c : ℝ) : ℂ)^s *
      (((Real.pi * scale c)⁻¹ : ℝ) : ℂ)^s = 1 := by
    rw [← Complex.mul_cpow_ofReal_nonneg ha.le (inv_pos.mpr ha).le,
      ← Complex.ofReal_mul, mul_inv_cancel₀ ha.ne', Complex.ofReal_one, Complex.one_cpow]
  have hinv : (((Real.pi * scale c)⁻¹ : ℝ) : ℂ)^s =
      (((Real.pi * scale c : ℝ) : ℂ)^s)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hprod)
  rw [completionScale_eq_inv, hinv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (scale_pos c).le, mul_inv_rev]
  simp only [Complex.cpow_neg]

theorem completedL_eq_standard (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) (hΓ : Complex.Gamma s ≠ 0) :
    completedL c χ hu hp s =
      (HeckeStrip.completionScale (conductor c) : ℂ)^s * Complex.Gamma s *
        LFunction (character c χ hu) s := by
  rw [completedL_eq_gamma_mul_LFunction c χ hu hp h0 h1 hΓ, completionScale_cpow]

theorem LFunction_norm_le (η : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖LFunction η s‖ ≤ HeckeReciprocalBound.bound σ := by
  have hs1 := hσ.trans_le hs
  rw [LFunction_eq_series η hs1, IdealEuler.series]
  have hsum := IdealEuler.weighted_summable_norm (idealCoeff η) (idealCoeff_norm_le_one η) s hs1
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (fullIdealWeight_summable_norm (σ : ℂ) (by simpa using hσ))
  intro I
  change ‖idealCoeff η I * fullIdealWeight s I‖ ≤ _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I)).trans
    (HeckeReciprocalBound.normWeight_le_of_re_ge hs I)

theorem pair_strong (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1) :
    IsStrongFEPair (pair c χ hu hp) := by
  constructor
  · exact HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal (character c χ hu) hχ
  · apply HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal
      (character c χ⁻¹ (inverse_unit_trivial c χ hu))
    change χ⁻¹ ≠ 1
    simpa only [ne_eq, inv_eq_one] using hχ

theorem LFunction_eq_uncompleted (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1) (s : ℂ) :
    LFunction (character c χ hu) s =
      (HeckeStrip.completionScale (conductor c) : ℂ)^(-s) * (Complex.Gamma s)⁻¹ *
        completedL c χ hu hp s := by
  let a := HeckeStrip.completionScale (conductor c)
  have ha : 0 < a := HeckeStrip.completionScale_pos _ (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))
  have hL := LFunction_entire_nonprincipal (character c χ hu) hχ
  have hΛ : Differentiable ℂ (completedL c χ hu hp) :=
    (pair_strong c χ hu hp hχ).differentiable_Λ.div_const 6
  have hR : Differentiable ℂ (fun z : ℂ => (a : ℂ)^(-z) * (Complex.Gamma z)⁻¹ *
      completedL c χ hu hp z) :=
    (((differentiable_id.neg).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne'))).mul
      Complex.differentiable_one_div_Gamma).mul hΛ
  have he : LFunction (character c χ hu) = fun z : ℂ => (a : ℂ)^(-z) *
      (Complex.Gamma z)⁻¹ * completedL c χ hu hp z := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hL).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hR) (z₀ := (2 : ℂ))
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have h0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have h1 : z ≠ 1 := by intro h; norm_num [h] at hz
    have hΓ : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    rw [completedL_eq_standard c χ hu hp h0 h1 hΓ]
    have haz : (a : ℂ)^z ≠ 0 := (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [ha.ne'])
    change LFunction (character c χ hu) z = (a : ℂ)^(-z) * (Complex.Gamma z)⁻¹ *
      ((a : ℂ)^z * Complex.Gamma z * LFunction (character c χ hu) z)
    rw [Complex.cpow_neg]
    field_simp
  exact congr_fun he s

theorem functional_equation_left (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (hs : s.re = -(1/10)) :
    LFunction (character c χ hu) s = TraceCharacter.normalizedGauss c χ *
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-2*s) *
      (Complex.Gamma (1-s) / Complex.Gamma s) *
        LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s) := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have hs0 : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hs1 : 1-s ≠ 1 := by intro h; apply h0; linear_combination -h
  have hΓdual : Complex.Gamma (1-s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp [hs]; norm_num)
  have hΓ : Complex.Gamma s ≠ 0 := by
    have h := Complex.Gamma_ne_zero_of_re_pos (s := s+1) (by simp [hs]; norm_num)
    rw [Complex.Gamma_add_one s h0] at h
    exact (mul_ne_zero_iff.mp h).2
  have he := completedL_functional_equation c χ hu hp hs0 hs1
  rw [sub_sub_cancel] at he
  rw [completedL_eq_standard c χ hu hp h0 h1 hΓ,
    completedL_eq_standard c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv hs0 hs1 hΓdual] at he
  let a := HeckeStrip.completionScale (conductor c)
  have ha : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (HeckeStrip.completionScale_pos _ (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))).ne'
  have haz : (a : ℂ)^s ≠ 0 := (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [ha])
  have hpow : (a : ℂ)^(1-s) = (a : ℂ)^s * (a : ℂ)^(1-2*s) := by
    rw [← Complex.cpow_add _ _ ha]
    congr 1
    ring
  apply mul_left_cancel₀ (mul_ne_zero haz hΓ)
  calc
    _ = TraceCharacter.normalizedGauss c χ * ((a : ℂ)^(1-s) * Complex.Gamma (1-s) *
        LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s)) := he
    _ = _ := by
      change _ = ((a : ℂ)^s * Complex.Gamma s) *
        (TraceCharacter.normalizedGauss c χ * (a : ℂ)^(1-2*s) *
          (Complex.Gamma (1-s)/Complex.Gamma s) * _)
      rw [hpow]
      field_simp

theorem LFunction_exp_growth (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ HeckeStrip.strip,
      ‖LFunction (character c χ hu) z‖ ≤ A * Real.exp (B * |z.im|) := by
  let f : ℝ → ℂ := fun t => (pair c χ hu hp).f t / 6
  have hP := pair_strong c χ hu hp hχ
  have hconv (s : ℂ) : MellinConvergent f s := (hP.hasMellin s).1.div_const 6
  have h := HeckeStrip.mellin_uncompleted_exp_bound
    (HeckeStrip.completionScale (conductor c))
    (HeckeStrip.completionScale_pos _ (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))) f
    (hconv _) (hconv _)
  have heq (z : ℂ) :
      (HeckeStrip.completionScale (conductor c) : ℂ)^(-z) * (Complex.Gamma z)⁻¹ * mellin f z =
        LFunction (character c χ hu) z := by
    rw [LFunction_eq_uncompleted c χ hu hp hχ]
    congr 1
    change mellin (fun t => (pair c χ hu hp).f t / 6) z = (pair c χ hu hp).Λ z / 6
    rw [mellin_div_const, (hP.hasMellin z).2]
  simpa only [heq] using h

theorem uniform_strip_bound (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖LFunction (character c χ hu) z‖ ≤
      36 * ((1 + HeckeStrip.leftConstant) * HeckeReciprocalBound.bound (11/10)) *
        conductor c ^ (3/5 : ℝ) * (3 + |z.im|)^2 := by
  apply HeckeStrip.uniform_strip_bound_of_functional_equation
    (conductor c) (HeckeReciprocalBound.bound (11/10)) (conductor_ge_one c)
    (tsum_nonneg (fun _ => norm_nonneg _))
    (LFunction (character c χ hu))
    (LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)))
    (TraceCharacter.normalizedGauss c χ) (TraceCharacter.normalizedGauss_norm c χ hp)
    (LFunction_entire_nonprincipal (character c χ hu) hχ).diffContOnCl
    (LFunction_exp_growth c χ hu hp hχ) (fun _ hs => functional_equation_left c χ hu hp hs)
    _ _ z hz
  · intro s hs
    exact LFunction_norm_le _ (by norm_num : (1 : ℝ) < 11/10) hs.ge
  · intro s hs
    exact LFunction_norm_le _ (by norm_num : (1 : ℝ) < 11/10) hs.ge

end HeckeStripActual

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
