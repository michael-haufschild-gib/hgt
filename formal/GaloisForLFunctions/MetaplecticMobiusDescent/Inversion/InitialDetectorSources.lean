/-
Initial detector sources adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.InitialOverlapsAndExclusions
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.MellinBoundary

/-!
# Initial detector sources

Base characters and prime profiles of the initial detector source, live primes of physical
slots and surviving products of common ratios; positive marked reserves and complete excluded
pools.
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
open scoped BigOperators Classical ComplexConjugate
namespace InverseInitialDetectorSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorCoefficientTransfer
open InverseInitialRawDictionary InverseInitialConjugateEnergy
local notation "O" => Eisenstein.O

def baseCharacter (data : RowData) : Character := data.character ⟨1,one_ne_zero⟩

theorem baseCharacter_coeff (data : RowData) (I : Ideal O) :
    idealCoeff (baseCharacter data) I=fixedBase data.η data.m data.f I := by
  rw [HeckeRowClosure.idealCoeff_eq_row data.η (baseCharacter data) data.m data.f 1
    (data.character_spec ⟨1,one_ne_zero⟩),mul_one]
  rfl

theorem base_nonzero_prime (data : RowData) (P : Ideal O) (hP : Prime P)
    (hN : ((baseCharacter data).modulus.absNorm:ℝ)<(P.absNorm:ℝ)) :
    fixedBase data.η data.m data.f P≠0 := by
  rw [←baseCharacter_coeff]
  exact HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime _ P hP.ne_zero
    (ProbeRaySlots.prime_coprime_of_norm_gt (baseCharacter data) ⟨P,hP⟩ hN)

theorem character_eq_initial (data : RowData) (u : NonzeroElement)
    (W : ℝ→ℂ) (Z r σ freq b : ℝ) (hZ : 0< Z)
    (hW : ∀x,W x≠0 → x≤ b) :
    polynomial (data.character u) true W (Z^r) σ freq=
      originalTotalPolynomial
        ((HeckeInverseAmplification.idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
        1 (fixedBase data.η data.m data.f) (fun _=>1)
        (twistedProfile W σ freq) Z r 0 u.val :=
  canonical_inverse_eq_supported_initial data.η (data.character u) data.m data.f u.val
    data.lambda_dvd data.two_dvd (data.character_spec u) W Z r σ freq b hZ hW

theorem oriented_character_norm_initial (data : RowData) (u : NonzeroElement)
    (χ : Character) (reverse : Bool)
    (hc : ∀I,idealCoeff χ I=if reverse then conj (idealCoeff (data.character u) I)
      else idealCoeff (data.character u) I)
    (W : ℝ→ℂ) (Z r σ freq b : ℝ) (hZ : 0< Z)
    (hW : ∀x,W x≠0 → x≤ b) :
    ‖polynomial χ true W (Z^r) σ freq‖=
      ‖originalTotalPolynomial
        ((HeckeInverseAmplification.idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
        1 (fixedBase data.η data.m data.f) (fun _=>1)
        (twistedProfile (orientedProfile reverse W) σ (orientedFrequency reverse freq))
        Z r 0 u.val‖ := by
  rw [norm_of_oriented_coefficients χ (data.character u) reverse hc true W (Z^r) σ freq
    (Real.rpow_pos_of_pos hZ r)]
  rw [character_eq_initial data u (orientedProfile reverse W) Z r σ
    (orientedFrequency reverse freq) b hZ]
  intro x hx
  apply hW x
  intro hz
  exact hx (by cases reverse <;> simp [orientedProfile,hz])

def primeProfile (V : ℝ→ℂ) (D : ℝ) (ζ : ℂ) (P : Ideal O) : ℂ :=
  V ((P.absNorm:ℝ)/D)*(((P.absNorm:ℝ)/D:ℝ):ℂ)^(ζ-1)

theorem physical_slot_norm_initial (data : RowData) (u : NonzeroElement)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (W V : ℝ→ℂ) (Z r ell σ freq b bslot a : ℝ) (ζ : ℂ) (hZ : 0< Z)
    (hW : ∀x,W x≠0 → x≤ b) (hV : ∀x,V x≠0 → a≤ x)
    (hlarge : ((baseCharacter data).modulus.absNorm:ℝ)< a*Z^ell) :
    ‖polynomial (data.character u) true W (Z^r) σ freq*
      HeckePrimeRow.canonicalPrimeAmplitude M H u.val V bslot (Z^ell) ζ‖=
    ‖∑P∈(HeckePrimeAnnular.annulusSet bslot (Z^ell)).filter
        (fun P=> Prime P ∧ P∈RayQuotient.identityClass M H),
      (star (primeProfile V (Z^ell) ζ P)/fixedBase data.η data.m data.f P)*
        originalTotalPolynomial
          ((HeckeInverseAmplification.idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
          P (fixedBase data.η data.m data.f) (fun _=>1)
          (twistedProfile W σ freq) Z r ell u.val‖ := by
  let Pset := (HeckePrimeAnnular.annulusSet bslot (Z^ell)).filter
    (fun P=> Prime P ∧ P∈RayQuotient.identityClass M H)
  have hc := finite_source_cover W (Z^r) b (Real.rpow_pos_of_pos hZ r) hW
  have hbase (P : Ideal O) (hp : P∈Pset) (ha : primeProfile V (Z^ell) ζ P≠0) :
      fixedBase data.η data.m data.f P≠0 := by
    apply base_nonzero_prime data P (Finset.mem_filter.mp hp).2.1
    have hv : V ((P.absNorm:ℝ)/Z^ell)≠0 := by
      intro hz
      exact ha (by simp [primeProfile,hz])
    exact hlarge.trans_le ((le_div_iff₀ (Real.rpow_pos_of_pos hZ ell)).mp (hV _ hv))
  have he := inverse_times_conjugate_row_mark_norm (fixedBase data.η data.m data.f)
    (data.character u) u.val
    (fixedBase_row data.η (data.character u) data.m data.f u.val (data.character_spec u))
    W Z r ell σ freq hZ (HeckeInverseAmplification.idealsUpTo ⌈Z^r*b⌉₊) Pset
    (primeProfile V (Z^ell) ζ) hbase hc
  have hp : HeckePrimeRow.canonicalPrimeAmplitude M H u.val V bslot (Z^ell) ζ=
      ((Z^(-ell/2):ℝ):ℂ)*∑P∈Pset,
        primeProfile V (Z^ell) ζ P*star (CanonicalRowCompletion.idealRowHom u.val P) := by
    unfold HeckePrimeRow.canonicalPrimeAmplitude
    rw [normalization_eq Z ell hZ]
    congr 1
    apply Finset.sum_congr rfl
    intro P hP
    change star (CanonicalRowCompletion.idealRowHom u.val P)*V _*_ =
      (V _*_)*star (CanonicalRowCompletion.idealRowHom u.val P)
    ring
  rw [hp,←mul_assoc,he]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  rw [originalTotal_supported_source _ _ _
    (fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd)]

end InverseInitialDetectorSource

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson

noncomputable section
open scoped BigOperators Classical
namespace InverseInitialMarkedDictionary
open HeckeFamily HeckeDyadic InverseInitialRawDictionary InverseInitialConjugateEnergy
open InverseInitialPoissonBridge UniqueFactorizationMonoid
local notation "O" => Eisenstein.O

theorem indexed_mark_initial {ι : Type*} (T : Finset ι) (P : ι→Ideal O) (A : ι→ℂ)
    (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ→ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z) (S : Finset (Ideal O))
    (hc : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑i∈T,A i*idealCoeff χ (P i))=
      ∑i∈T,A i*originalTotalPolynomial S (P i) η (fun _=>1)
        (twistedProfile W σ freq) Z r z u := by
  rw [inverse_eq_initial_source η χ u hrow W Z r σ freq hZ S hc]
  have hn : ((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ)=((Z^(-(r+z)/2):ℝ):ℂ) := by
    rw [←Complex.ofReal_mul,←Real.rpow_add hZ]
    congr 2
    ring
  unfold originalTotalPolynomial
  simp only [add_zero,map_one,mul_one,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro I hI
  rw [hrow]
  simp only [heckeIdealCharacter_apply]
  calc
    _ = (((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ))*
      (A i*((moebius I:ℂ)*(η I*CanonicalRowCompletion.idealRowHom u I)*
      (η (P i)*CanonicalRowCompletion.idealRowHom u (P i))*
      twistedProfile W σ freq ((I.absNorm:ℝ)/Z^r))) := by ring
    _ = _ := by rw [hn];ring

theorem indexed_conjugate_mark_norm {ι : Type*} (T : Finset ι) (P : ι→Ideal O) (A : ι→ℂ)
    (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ→ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z) (S : Finset (Ideal O))
    (hc : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S)
    (hη : ∀i∈T,A i≠0 → η (P i)≠0) :
    ‖polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑i∈T,A i*star (CanonicalRowCompletion.idealRowHom u (P i)))‖=
      ‖∑i∈T,(star (A i)/η (P i))*originalTotalPolynomial S (P i) η (fun _=>1)
        (twistedProfile W σ freq) Z r z u‖ := by
  have hm : (∑i∈T,(star (A i)/η (P i))*idealCoeff χ (P i))=
      star (∑i∈T,A i*star (CanonicalRowCompletion.idealRowHom u (P i))) := by
    simp only [star_sum,star_mul,star_star]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : A i=0
    · simp [ha]
    · rw [hrow]
      field_simp [hη i hi ha]
  rw [←indexed_mark_initial T P (fun i=>star (A i)/η (P i)) η χ u hrow W Z r z σ freq hZ S hc,hm]
  simp only [norm_mul,norm_star]

theorem conjugate_mark_product {ι : Type*} [Fintype ι]
    (T : ι→Finset (Ideal O)) (A : ι→Ideal O→ℂ) (u : O) :
    (∏i,∑P∈T i,A i P*star (CanonicalRowCompletion.idealRowHom u P))=
      ∑p∈Fintype.piFinset T,(∏i,A i (p i))*
        star (CanonicalRowCompletion.idealRowHom u (∏i,p i)) := by
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.prod_mul_distrib,map_prod,star_prod]

end InverseInitialMarkedDictionary

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson

noncomputable section
open scoped BigOperators Classical
namespace InverseInitialPhysicalSlots
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open InverseInitialRawDictionary InverseInitialDetectorSource InverseInitialMarkedDictionary
open InverseInitialConjugateEnergy
local notation "O" => Eisenstein.O

variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

def livePrimes (V : ℝ→ℂ) (b D : ℝ) : Finset (Ideal O) :=
  ((HeckePrimeAnnular.annulusSet b D).filter
    (fun P=>Prime P ∧ P∈RayQuotient.identityClass M H)).filter
      (fun P=>V ((P.absNorm:ℝ)/D)≠0)

omit [NeZero M] in
theorem livePrime_data (V : ℝ→ℂ) (a b D : ℝ) (hD : 0<D)
    (hV : ∀x,V x≠0 → x∈Set.Icc a b) (P : Ideal O) (hp : P∈livePrimes M H V b D) :
    Prime P ∧ P∈RayQuotient.identityClass M H ∧ a*D≤(P.absNorm:ℝ) ∧ (P.absNorm:ℝ)≤b*D := by
  obtain ⟨hp,hv⟩ := Finset.mem_filter.mp hp
  obtain ⟨_,hp,hr⟩ := Finset.mem_filter.mp hp
  exact ⟨hp,hr,(le_div_iff₀ hD).mp (hV _ hv).1,(div_le_iff₀ hD).mp (hV _ hv).2⟩

omit [NeZero M] in
theorem amplitude_eq_live (u : O) (V : ℝ→ℂ) (b Z ell : ℝ) (ζ : ℂ) (hZ : 0<Z) :
    HeckePrimeRow.canonicalPrimeAmplitude M H u V b (Z^ell) ζ=
      ((Z^(-ell/2):ℝ):ℂ)*∑P∈livePrimes M H V b (Z^ell),
        primeProfile V (Z^ell) ζ P*star (CanonicalRowCompletion.idealRowHom u P) := by
  unfold HeckePrimeRow.canonicalPrimeAmplitude
  rw [normalization_eq Z ell hZ]
  congr 1
  rw [livePrimes]
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P hP
  split_ifs with hv
  · change star (CanonicalRowCompletion.idealRowHom u P)*V _*_ =
      (V _*_)*star (CanonicalRowCompletion.idealRowHom u P)
    ring
  · simp only [not_not] at hv
    simp [hv]

theorem slot_normalization {ι : Type*} [Fintype ι] (Z : ℝ) (hZ : 0<Z) (ell : ι→ℝ) :
    (∏i,((Z^(-ell i/2):ℝ):ℂ))=((Z^(-(∑i,ell i)/2):ℝ):ℂ) := by
  rw [←Complex.ofReal_prod,←Real.rpow_sum_of_pos hZ]
  congr 2
  simp only [neg_div,Finset.sum_div,Finset.sum_neg_distrib]

omit [NeZero M] in
theorem amplitude_product_eq_tuples {ι : Type*} [Fintype ι] (u : O)
    (V : ι→ℝ→ℂ) (b ell : ι→ℝ) (ζ : ι→ℂ) (Z : ℝ) (hZ : 0<Z) :
    (∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u (V i) (b i) (Z^(ell i)) (ζ i))=
      ((Z^(-(∑i,ell i)/2):ℝ):ℂ)*
        ∑p∈Fintype.piFinset (fun i=>livePrimes M H (V i) (b i) (Z^(ell i))),
        (∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i))*
          star (CanonicalRowCompletion.idealRowHom u (∏i,p i)) := by
  simp_rw [amplitude_eq_live M H _ _ _ _ _ _ hZ]
  rw [Finset.prod_mul_distrib,slot_normalization Z hZ,conjugate_mark_product]

omit [NeZero M] in
theorem physical_slots_norm_initial {ι : Type*} [Fintype ι]
    (data : RowData) (u : NonzeroElement) (W : ℝ→ℂ) (V : ι→ℝ→ℂ)
    (Z r σ freq bW : ℝ) (a b ell : ι→ℝ) (ζ : ι→ℂ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤bW) (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hlarge : ∀i,((baseCharacter data).modulus.absNorm:ℝ)<a i*Z^(ell i)) :
    ‖polynomial (data.character u) true W (Z^r) σ freq*
      (∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (Z^(ell i)) (ζ i))‖=
    ‖∑p∈Fintype.piFinset (fun i=>livePrimes M H (V i) (b i) (Z^(ell i))),
      (star (∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i))/
        fixedBase data.η data.m data.f (∏i,p i))*
      originalTotalPolynomial
        ((HeckeInverseAmplification.idealsUpTo ⌈Z^r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
        (∏i,p i) (fixedBase data.η data.m data.f) (fun _=>1)
        (twistedProfile W σ freq) Z r (∑i,ell i) u.val‖ := by
  let T := fun i=>livePrimes M H (V i) (b i) (Z^(ell i))
  let A := fun p:ι→Ideal O=>∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i)
  have hn (p : ι→Ideal O) (hp : p∈Fintype.piFinset T) (_ha : A p≠0) :
      fixedBase data.η data.m data.f (∏i,p i)≠0 := by
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hpi := Fintype.mem_piFinset.mp hp i
    have hd := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
      (Real.rpow_pos_of_pos hZ _) (hV i) (p i) hpi
    exact base_nonzero_prime data (p i) hd.1 ((hlarge i).trans_le hd.2.2.1)
  have he := indexed_conjugate_mark_norm (Fintype.piFinset T) (fun p=>∏i,p i) A
    (fixedBase data.η data.m data.f) (data.character u) u.val
    (fixedBase_row data.η (data.character u) data.m data.f u.val (data.character_spec u))
    W Z r (∑i,ell i) σ freq hZ (HeckeInverseAmplification.idealsUpTo ⌈Z^r*bW⌉₊)
    (finite_source_cover W (Z^r) bW (Real.rpow_pos_of_pos hZ _) hW) hn
  rw [amplitude_product_eq_tuples M H _ _ _ _ _ _ hZ,←mul_assoc]
  change ‖polynomial (data.character u) true W (Z^r) σ freq*↑(Z^(-(∑i,ell i)/2))*
    (∑p∈Fintype.piFinset T,A p*star (CanonicalRowCompletion.idealRowHom u (∏i,p i)))‖=_
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [originalTotal_supported_source _ _ _
    (fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd)]

omit [NeZero M] in
theorem live_tuple_injective {ι : Type*} [Fintype ι]
    (V : ι→ℝ→ℂ) (a b ell : ι→ℝ) (Z : ℝ) (hZ : 0<Z)
    (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hsep : ∀i j,i≠j → b i*Z^(ell i)<a j*Z^(ell j) ∨
      b j*Z^(ell j)<a i*Z^(ell i))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset
      (fun i=>livePrimes M H (V i) (b i) (Z^(ell i)))) : Function.Injective p := by
  intro i j he
  by_contra hij
  have hi := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
    (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
  have hj := livePrime_data M H (V j) (a j) (b j) (Z^(ell j))
    (Real.rpow_pos_of_pos hZ _) (hV j) (p j) (Fintype.mem_piFinset.mp hp j)
  rw [he] at hi
  rcases hsep i j hij with h|h <;> linarith [hi.2.2.1,hi.2.2.2,hj.2.2.1,hj.2.2.2]

omit [NeZero M] in
theorem live_tuple_admissible {ι : Type*} [Fintype ι]
    (data : RowData) (V : ι→ℝ→ℂ) (a b ell : ι→ℝ) (Z : ℝ) (hZ : 0<Z)
    (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hlarge : ∀i,((baseCharacter data).modulus.absNorm:ℝ)<a i*Z^(ell i))
    (hsep : ∀i j,i≠j → b i*Z^(ell i)<a j*Z^(ell j) ∨
      b j*Z^(ell j)<a i*Z^(ell i))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset
      (fun i=>livePrimes M H (V i) (b i) (Z^(ell i)))) :
    CanonicalQuadraticSieve.Admissible (∏i,p i) := by
  have hd i := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
    (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
  have hs (i : ι) : CanonicalQuadraticSieve.Supported (p i) := by
    by_contra hn
    exact base_nonzero_prime data (p i) (hd i).1 ((hlarge i).trans_le (hd i).2.2.1)
      (fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd (p i) hn)
  have hi := live_tuple_injective M H V a b ell Z hZ hV hsep p hp
  have hsprod : CanonicalQuadraticSieve.Supported (∏i,p i) := by
    have hh (S : Finset ι) : CanonicalQuadraticSieve.Supported (∏i∈S,p i) := by
      induction S using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        exact ⟨one_ne_zero,by intro P hP;simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP⟩
      | @insert i S hi ih =>
        rw [Finset.prod_insert hi]
        exact (CanonicalQuadraticSieve.supported_mul_iff _ _).mpr ⟨hs i,ih⟩
    exact hh Finset.univ
  refine ⟨hsprod.1,?_,?_⟩
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      let : (p i).IsMaximal := (Ideal.isPrime_of_prime (hd i).1).isMaximal (hd i).1.ne_zero
      let : (p j).IsMaximal := (Ideal.isPrime_of_prime (hd j).1).isMaximal (hd j).1.ne_zero
      exact (Ideal.isCoprime_of_isMaximal (hi.ne hij)).isRelPrime
    · intro i _
      exact (hd i).1.squarefree
  · intro P hP
    exact hsprod.2 P hP

end InverseInitialPhysicalSlots

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical
open Eisenstein _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve
namespace InverseInitialCommonRatios
open InverseInitialOverlap InverseInitialKernelBridge
local notation "Eis"=> Eisenstein.O
variable {σ:Type*} [DecidableEq σ]

def survivingProduct (I:Finset σ)(q:∀i∈I,Ideal Eis) : Ideal Eis :=
  ∏i∈I.attach,q i.val i.property

omit [DecidableEq σ] in
theorem actual_residual_product (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0) : residual (j*survivingProduct I q) j=survivingProduct I q :=
  quotient_mul_cancel hj

omit [DecidableEq σ] in
theorem residual_ratio_product (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0)(ell:σ→ℝ)(Z z G:ℝ)(hZ:0< Z)
    (hell:∑i∈I,ell i=z-G) :
    ((residual (j*survivingProduct I q) j).absNorm:ℝ)/Z^(z-G)=
      ∏i∈I.attach,((q i.val i.property).absNorm:ℝ)/Z^(ell i.val) := by
  rw [actual_residual_product I q j hj,Finset.prod_div_distrib]
  have hp : (∏i∈I.attach,Z^(ell i.val))=Z^(z-G) := by
    rw [←Real.rpow_sum_of_pos hZ]
    rw [Finset.sum_attach,hell]
  rw [hp]
  congr 1
  simp only [survivingProduct,map_prod,Nat.cast_prod]

omit [DecidableEq σ] in
theorem original_residual_window (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0)(ell:σ→ℝ)(W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0< Z)
    (hell:∑i∈I,ell i=z-G)(c:Ideal Eis) :
    residualOverlapWindow (j*survivingProduct I q) j W Z z G
      ((c.absNorm:ℝ)/Z^(r+z-2*G))=
      W (((j.absNorm:ℝ)/Z^G)*((c.absNorm:ℝ)/Z^(r+z-2*G))/
        (∏i∈I.attach,((q i.val i.property).absNorm:ℝ)/Z^(ell i.val))) := by
  unfold residualOverlapWindow
  rw [residual_ratio_product I q j hj ell Z z G hZ hell]

end InverseInitialCommonRatios

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace InverseInitialMarkedReserve

theorem exists_reserve (εm:ℝ)(hε:0<εm):
    ∃ρ gap η τ π eps loss:ℝ,
      0<ρ ∧ ρ≤1/4 ∧ ρ≤εm/4 ∧
      0< gap ∧ 2*gap≤ρ ∧
      0<η ∧ η≤1/7 ∧ η≤ gap/50 ∧
      0<τ ∧ τ≤ gap/50 ∧ 0<π ∧ 0< eps ∧ 0< loss ∧
      ρ+15*η+π+eps+loss≤εm:=by
  let ρ:=min (εm/4) (1/4)
  have hρ:0<ρ:=lt_min (by linarith) (by norm_num)
  have hρa:ρ≤εm/4:=min_le_left _ _
  have hρb:ρ≤1/4:=min_le_right _ _
  refine ⟨ρ,ρ/4,ρ/400,ρ/400,ρ/16,ρ/16,ρ/16,hρ,hρb,hρa,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

/-- The chosen positive reserves preserve both marked capacity inequalities under fixed-divisor shifts. -/
theorem shifted_capacity (ρ gap η r r' ell G:ℝ)
    (hρ:0<ρ)(hρmax:ρ≤1/4)(hgap:2*gap≤ρ)
    (hη:0<η)(hηmax:η≤1/7)(hr:0≤ r)(hell:0≤ ell)
    (_hG:0≤ G)(hGmax:G≤ ell)(hlo:r-η≤ r')(hhi:r'≤ r)
    (hfirst:r+2*ell<1)(hsecond:2*r+8*ell<3):
    0≤1+ρ ∧ 1+ρ≤2 ∧ -2≤ r'+ell-2*G ∧
      r'+2*ell≤(1+ρ)-2*gap ∧
      2*r'+8*ell≤3*(1+ρ)-2*gap ∧
      r'+ell+7*η≤2:=by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

end InverseInitialMarkedReserve

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace InverseInitialInputRadial
open Eisenstein SecondPassArithmetic 
open InverseInitialConjugateEnergy
local notation "O"=> Eisenstein.O
variable {ι:Type*}[DecidableEq ι](p:ι→ O)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,lambda∉Ideal.span {p i})

/-- The finite character expansion bounds the input row, giving summability against a Schwartz weight. -/
theorem input_energy_summable (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(test:Finset ι→ℂ)
    (a:ℂ)(Φ:𝓢(ℝ,ℂ))(Y:ℝ)(hY:0< Y):
    Summable (fun u:O=>Φ (‖ringComplex u‖^2/Y)*
      (‖a*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) pool Ψ j 1 1 test u‖^2:ℝ)):=by
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  let c : Finset ι → ℂ := fun S => a*supportMobius S*secondInputCoefficient p χ Ψ j 1 1 test S
  apply InverseInitialPoissonBridge.bounded_smoothed_summable
    (fun u => a*inputConjugateRow p χ pool Ψ j 1 1 test u)
    (∑ S∈pool.powerset, ‖c S‖) _ Φ Y hY
  intro u
  have he : a*inputConjugateRow p χ pool Ψ j 1 1 test u =
      ∑ S∈pool.powerset, c S*star (primeSubsetRow p χ S u) := by
    simp only [inputConjugateRow, supportConjugateSum, Finset.mul_sum, c, mul_assoc]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro S hS
  rw [norm_mul, norm_star]
  exact mul_le_of_le_one_right (norm_nonneg _) (primeSubsetRow_norm_le_one p χ S u)

theorem finite_rows_le_input_norm (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(test:Finset ι→ℂ)
    (a:ℂ)(Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)
    (hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (Y:ℝ)(hY:0< Y)(rows:Finset O)(hrows:∀u∈rows,‖ringComplex u‖^2≤ Y):
    (∑u∈rows,‖a*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) pool Ψ j 1 1 test u‖^2)≤
      ‖∑'u:O,Φ (‖ringComplex u‖^2/Y)*
        (‖a*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) pool Ψ j 1 1 test u‖^2:ℝ)‖:=by
  have hs:=input_energy_summable p hg pool Ψ j test a Φ Y hY
  have hr:=Complex.hasSum_re hs.hasSum
  have hfin:(∑u∈rows,‖a*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) pool Ψ j 1 1 test u‖^2)=
      ∑u∈rows,(Φ (‖ringComplex u‖^2/Y)*
        (‖a*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) pool Ψ j 1 1 test u‖^2:ℝ)).re:=by
    apply Finset.sum_congr rfl
    intro u hu
    rw [hone _ ⟨div_nonneg (sq_nonneg _) hY.le,(div_le_one hY).mpr (hrows u hu)⟩]
    simp only [one_mul,Complex.ofReal_re]
  rw [hfin]
  apply (hr.summable.sum_le_tsum rows (fun u _=>?_)).trans
  · rw [hr.tsum_eq]
    exact Complex.re_le_norm _
  · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_nonneg (hΦ _) (sq_nonneg _)

end InverseInitialInputRadial

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory JointLogSeparation Eisenstein SecondPassArithmetic
open FirstPassCubeLabels
namespace InverseInitialOverlapInputFourier
open InverseMoment InverseInitialOverlapFourier InverseInitialArithmetic InverseInitialRayAttachment
local notation "Eis"=> Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→ Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

/-- Finite character sums commute with the integrable Fourier superposition. -/
theorem input_integral (F : Finset ι) (Ψ : Eis→*ℂ) (j u : Eis)
    (H : Finset ι→ℝ→ℂ) (hH : ∀A∈F.powerset,Integrable (H A)) :
    inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ j 1 1 (fun A=>∫t:ℝ,H A t) u =
      ∫t:ℝ,inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ j 1 1 (fun A=> H A t) u := by
  rw [initial_input_row p hg]
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  have he (A:Finset ι) (t:ℝ) :
      supportMobius A*
        (Ψ (∏i∈A,p i)*primeCoprimeMask p A j*H A t)*
        star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) A u)=
      (supportMobius A*Ψ (∏i∈A,p i)*
        primeCoprimeMask p A j*
        star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) A u))*H A t := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun A hA=>(hH A hA).const_mul _)]
  simp only [integral_const_mul]
  apply Finset.sum_congr rfl
  intro A hA
  ring

theorem original_overlap_input
    (hp : ∀i,p i≠0) (F : Finset ι) (Ψ : Eis→*ℂ) (j u : Eis)
    (W : ℝ→ℂ) (a₀ b₀ : ℝ) (ha₀ : 0< a₀)
    (hs : Function.support W⊆Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (slots : Finset σ) (lists : σ→ Finset ι) (a : σ→ι→ℂ)
    (y : σ→ι→ℝ) (hy : ∀i∈slots,∀q∈lists i,0< y i q)
    (wFresh : ℝ→ℂ) (Z D yj : ℝ) (hZ : 0< Z) (hj : 0< yj) :
    ((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ j 1 1
      (fun A=> wFresh (primeProductNorm p A/Z^D)*
        ∑q∈slots.pi lists,
          (∏i∈slots.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*(primeProductNorm p A/Z^D)/(∏i∈slots.attach,y i.val (q i.val i.property)))) u =
      ∫t:ℝ,density (kernelLogSource W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ j 1 1
          (initialTest p
            (primeMark slots lists (fun i q=> a i q*kernelLogPhase (-t) (Real.log (y i q))))
            (childLogTest wFresh t) Z D) u) := by
  let g := kernelLogSource W a₀ b₀ ha₀ hs hW
  let H : Finset ι→ℝ→ℂ := fun A t=> density g (Real.log yj) t*
    (primeMark slots lists (fun i q=> a i q*kernelLogPhase (-t) (Real.log (y i q))) A*
      childLogTest wFresh t (primeProductNorm p A/Z^D))
  have hH (A:Finset ι) : Integrable (H A) := by
    have hi := (overlap_mode_integrable g slots lists a (fun i q=> Real.log (y i q))
      A (Real.log yj) (Real.log (primeProductNorm p A/Z^D))).const_mul
      (wFresh (primeProductNorm p A/Z^D))
    convert hi using 1
    funext t
    dsimp [H,childLogTest]
    ring
  have he (A:Finset ι) :
      wFresh (primeProductNorm p A/Z^D)*
        (∑q∈slots.pi lists,
          (∏i∈slots.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*(primeProductNorm p A/Z^D)/(∏i∈slots.attach,y i.val (q i.val i.property)))) =
      ∫t:ℝ,H A t := by
    rw [actual_overlap_separation W a₀ b₀ ha₀ hs hW slots lists a y hy A yj
      (primeProductNorm p A/Z^D) hj
      (div_pos (primeProductNorm_pos p hp A) (Real.rpow_pos_of_pos hZ D)),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [H,childLogTest,g]
    have hprofile : CanonicalCubeSeparation.sourceLogProfile W a₀ b₀ ha₀ hs hW =
        kernelLogSource W a₀ b₀ ha₀ hs hW := by
      ext x
      rw [CanonicalCubeSeparation.sourceLogProfile_apply,kernelLogSource_apply]
    rw [hprofile]
    ring
  simp_rw [he]
  rw [input_integral p hg F Ψ j u H (fun A _=> hH A),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [initial_input_row p hg,initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,initialTest]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end InverseInitialOverlapInputFourier

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory JointLogSeparation
namespace InverseInitialOverlapEnergy
open InverseInitialOverlapFourier InverseMoment

/-- Weighted Cauchy–Schwarz transfers polynomial pointwise energy to the Fourier integral. -/
theorem polynomial_measure_energy (g:𝓢(ℝ,ℂ))(J:ℕ) :
    ∃C:ℝ,0≤ C ∧ ∀{κ:Type*}[Fintype κ](xj:ℝ)(φ:κ→ℝ→ℂ)(E:ℝ),
      0≤ E→(∀k,Integrable (fun t=> density g xj t*φ k t))→
      (∀t,(∑k,‖φ k t‖^2)≤ E*((1+‖t‖)^J)^2)→
      (∑k,‖∫t:ℝ,density g xj t*φ k t‖^2)≤ C*E := by
  obtain ⟨C,hC,hint⟩ := density_moment g J
  refine ⟨C ^ 2,sq_nonneg _,?_⟩
  intro κ inst xj φ E hE hφ hbound
  let h : ℝ→ℝ := fun t=>(1+‖t‖)^J
  have hp (t:ℝ) : 0< h t := by dsimp [h];positivity
  let b : ℝ→ℂ := fun t=> density g xj t*(h t:ℂ)
  let f : κ→ℝ→ℂ := fun k t=>φ k t/(h t:ℂ)
  have he (k:κ)(t:ℝ) : b t*f k t=density g xj t*φ k t := by
    dsimp [b,f]
    have hn : (h t:ℂ)≠0 := by exact_mod_cast (hp t).ne'
    field_simp
  have hbnorm (t:ℝ) : ‖b t‖=h t*‖density g xj t‖ := by
    rw [show b t=density g xj t*(h t:ℂ) from rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),mul_comm]
  have hb : Integrable (fun t=>‖b t‖) := by
    simpa only [hbnorm,h]
      using (hint xj).1
  have hf : ∀k,Integrable (fun t=> b t*f k t) := by
    intro k
    simpa only [he] using hφ k
  have henergy (t:ℝ) : (∑k,‖f k t‖^2)≤ E := by
    simp only [f,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),div_pow,←Finset.sum_div]
    apply (div_le_iff₀ (sq_pos_of_pos (hp t))).mpr
    exact hbound t
  have hbint : (∫t:ℝ,‖b t‖)≤ C := by
    simpa only [hbnorm,h]
      using (hint xj).2
  have hb0 : 0≤∫t:ℝ,‖b t‖ := integral_nonneg fun _=> norm_nonneg _
  have hh := common_measure_energy volume b f E hE hb hf henergy
  simp only [he] at hh
  exact hh.trans (by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbint 2) hE)

end InverseInitialOverlapEnergy

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory JointLogSeparation
namespace InverseInitialOverlapHeight
open InverseInitialOverlapFourier InverseMoment JointLogSeparation

theorem twisted_polynomial_measure_energy (g:𝓢(ℝ,ℂ))(J:ℕ) :
    ∃C:ℝ,0≤ C ∧ ∀(θ:ℝ),∀{κ:Type*}[Fintype κ](xj:ℝ)(φ:κ→ℝ→ℂ)(E:ℝ),
      0≤ E→(∀k,Integrable (fun t=> density (frequencyTwist g θ) xj t*φ k t))→
      (∀t,(∑k,‖φ k t‖^2)≤ E*((1+‖t‖)^J)^2)→
      (∑k,‖∫t:ℝ,density (frequencyTwist g θ) xj t*φ k t‖^2)≤ C*E*(1+‖θ‖)^(2*(J+(volume:Measure ℝ).integrablePower)) := by
  obtain ⟨C,hC,hboundMoment⟩ := frequencyTwist_fourier_moment J g
  refine ⟨C ^ 2,sq_nonneg _,?_⟩
  intro θ κ inst xj φ E hE hφ hbound
  have hint:=JointLogSeparation.schwartz_fourier_one_plus_integrable (frequencyTwist g θ) J
  let h : ℝ→ℝ := fun t=>(1+‖t‖)^J
  have hp (t:ℝ) : 0< h t := by dsimp [h];positivity
  let b : ℝ→ℂ := fun t=> density (frequencyTwist g θ) xj t*(h t:ℂ)
  let f : κ→ℝ→ℂ := fun k t=>φ k t/(h t:ℂ)
  have he (k:κ)(t:ℝ) : b t*f k t=density (frequencyTwist g θ) xj t*φ k t := by
    dsimp [b,f]
    have hn : (h t:ℂ)≠0 := by exact_mod_cast (hp t).ne'
    field_simp
  have hbnorm (t:ℝ) : ‖b t‖=h t*‖density (frequencyTwist g θ) xj t‖ := by
    rw [show b t=density (frequencyTwist g θ) xj t*(h t:ℂ) from rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),mul_comm]
  have hb : Integrable (fun t=>‖b t‖) := by
    simpa only [hbnorm,h,density_norm]
      using hint
  have hf : ∀k,Integrable (fun t=> b t*f k t) := by
    intro k
    simpa only [he] using hφ k
  have henergy (t:ℝ) : (∑k,‖f k t‖^2)≤ E := by
    simp only [f,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),div_pow,←Finset.sum_div]
    apply (div_le_iff₀ (sq_pos_of_pos (hp t))).mpr
    exact hbound t
  have hbint : (∫t:ℝ,‖b t‖)≤ C*(1+‖θ‖)^(J+(volume:Measure ℝ).integrablePower) := by
    simpa only [hbnorm,h,density_norm]
      using hboundMoment θ
  have hb0 : 0≤∫t:ℝ,‖b t‖ := integral_nonneg fun _=> norm_nonneg _
  have hh := common_measure_energy volume b f E hE hb hf henergy
  simp only [he] at hh
  exact hh.trans (by
    simpa only [mul_pow,←pow_mul,Nat.mul_comm,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbint 2) hE)

end InverseInitialOverlapHeight

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory JointLogSeparation Eisenstein SecondPassArithmetic
open FirstPassCubeLabels
namespace InverseInitialMarkedInputEnergy
open InverseMoment InverseInitialOverlapFourier InverseInitialOverlapEnergy
open InverseInitialRayAttachment InverseInitialArithmetic
local notation "Eis"=> Eisenstein.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→ Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,lambda∉Ideal.span {p i})

theorem marked_input_integrable (g:𝓢(ℝ,ℂ))(F:Finset ι)(Ψ:Eis→*ℂ)(j u:Eis)
    (I:Finset σ)(L:σ→ Finset ι)(a:σ→ι→ℂ)(y:σ→ι→ℝ)
    (wFresh:ℝ→ℂ)(Z D xj:ℝ) :
    Integrable (fun t:ℝ=> density g xj t*
      (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ j 1 1
        (initialTest p (primeMark I L (fun i q=> a i q*kernelLogPhase (-t) (y i q)))
          (childLogTest wFresh t) Z D) u)) := by
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro A hA
  have hh := (overlap_mode_integrable g I L a y A xj
    (Real.log (primeProductNorm p A/Z^D))).const_mul
    (((Z^(-D/2):ℝ):ℂ)*supportMobius A*
      Ψ (∏i∈A,p i)*primeCoprimeMask p A j*
      star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) A u)*
      wFresh (primeProductNorm p A/Z^D))
  apply hh.congr
  filter_upwards with t
  unfold initialTest childLogTest
  ring

theorem marked_input_energy (g:𝓢(ℝ,ℂ))(J:ℕ) :
    ∃C:ℝ,0≤ C ∧ ∀(F:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(rows:Finset Eis)
      (I:Finset σ)(L:σ→ Finset ι)(a:σ→ι→ℂ)(y:σ→ι→ℝ)
      (wFresh:ℝ→ℂ)(Z D xj E:ℝ),0≤ E→
      (∀t,(∑u∈rows,‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ j 1 1
        (initialTest p (primeMark I L (fun i q=> a i q*kernelLogPhase (-t) (y i q)))
          (childLogTest wFresh t) Z D) u‖^2)≤ E*((1+‖t‖)^J)^2)→
      (∑u∈rows,‖∫t:ℝ,density g xj t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ j 1 1
          (initialTest p (primeMark I L (fun i q=> a i q*kernelLogPhase (-t) (y i q)))
            (childLogTest wFresh t) Z D) u)‖^2)≤ C*E := by
  obtain ⟨C,hC,htransfer⟩ := polynomial_measure_energy g J
  refine ⟨C,hC,?_⟩
  intro F Ψ j rows I L a y wFresh Z D xj E hE henergy
  let ψ : Eis→ℝ→ℂ := fun u t=>((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ j 1 1
    (initialTest p (primeMark I L (fun i q=> a i q*kernelLogPhase (-t) (y i q)))
      (childLogTest wFresh t) Z D) u
  let φ : rows→ℝ→ℂ := fun u t=>ψ u.val t
  have hh := htransfer xj φ E hE
    (fun u=> marked_input_integrable p hg g F Ψ j u.val I L a y wFresh Z D xj)
    (fun t=> by
      exact (Finset.sum_coe_sort rows (fun u=>‖ψ u t‖^2)).le.trans (henergy t))
  exact (Finset.sum_coe_sort rows
    (fun u=>‖∫t:ℝ,density g xj t*ψ u t‖^2)).symm.le.trans hh

end InverseInitialMarkedInputEnergy

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace InverseInitialTotalRows
open Eisenstein CompletedGauss  
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=> Eisenstein.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
/-- A radial majorant turns the smoothed input estimate into a finite-row moment bound. -/
theorem original_input_rows_fourier_bound
    (W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0< a₀)(hbcap:1≤ bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤ B₀)(hb:∀x,‖W x‖≤ B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤ cap)(hgap:0< gap)(heps:0< eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤ gap/50)(hτ:0<τ)(hτsmall:τ≤ gap/50)(hloss:0< loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤ Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0< C ∧ 1< Z₀ ∧
    ∀Z:ℝ,Z₀≤ Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤ Dpool→
    let F:=CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→ all.card≤ K→
    ∀(lists:σ→ Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→ primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤ Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤ Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→ O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤ z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→ FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(D m r:ℝ),0≤ m→ m≤ cap→-cap≤ D→
      (∏i∈assigned,bl i)≤ Z^η→
      (∏i∈all\assigned,Hslot i)≤ Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→
    ∀(rows:Finset O),(∀u∈rows,‖ringComplex u‖^2≤ Z^m)→
    ∀(y:σ→ primePool F→ℝ)(θ:ℝ),
      (∑u∈rows,‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Finset.univ Ψ
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) lists
            (fun i P=> coeff i P*kernelLogPhase (-θ) (y i P)))
            (childLogTest W θ) Z D) u‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialTotalEnergy.original_input_bound
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ B₀ hB₀ hb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  refine ⟨InverseClippingProfiles.momentOrder (4*J),Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows y θ
  have hZp:1< Z:=hZ₀.trans_le hZ
  have he:=henergy Z hZ Dpool hD all assigned hassigned hK lists Hslot
    (fun i P=> coeff i P*kernelLogPhase (-θ) (y i P)) hdis hHs hPs
    (by intro i hi P hP;simpa only [norm_mul,kernelLogPhase_norm,mul_one] using hac i hi P hP)
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent 1 θ le_rfl hbcap
  have hr:=InverseInitialInputRadial.finite_rows_le_input_norm p hg Finset.univ Ψ
    (assignedElement assigned qelem)
    (initialTest p (primeMark (all\assigned) lists
      (fun i P=> coeff i P*kernelLogPhase (-θ) (y i P))) (childLogTest W θ) Z D)
    ((Z^(-D/2):ℝ):ℂ) Φ hΦ hone (Z^m) (Real.rpow_pos_of_pos (by linarith) _) rows hrows
  apply hr.trans
  simpa only [InverseInitialProfileBounds.childLogTest_eq_clipped,pow_mul,pow_two,mul_pow] using he

end InverseInitialTotalRows

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace InverseInitialTotalFourier
open Eisenstein CompletedGauss  
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=> Eisenstein.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
open MeasureTheory JointLogSeparation JointLogSeparation InverseInitialOverlapFourier
/-- Fourier superposition preserves the input saving with polynomial height growth. -/
theorem original_fourier_energy_bound
    (g:𝓢(ℝ,ℂ))(W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0< a₀)(hbcap:1≤ bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤ B₀)(hb:∀x,‖W x‖≤ B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤ cap)(hgap:0< gap)(heps:0< eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤ gap/50)(hτ:0<τ)(hτsmall:τ≤ gap/50)(hloss:0< loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤ Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0< C ∧ 1< Z₀ ∧
    ∀Z:ℝ,Z₀≤ Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤ Dpool→
    let F:=CanonicalRowCompletion.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=CanonicalRowCompletion.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→ all.card≤ K→
    ∀(lists:σ→ Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→ primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤ Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤ Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→ O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤ z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→ FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(D m r:ℝ),0≤ m→ m≤ cap→-cap≤ D→
      (∏i∈assigned,bl i)≤ Z^η→
      (∏i∈all\assigned,Hslot i)≤ Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→
    ∀(rows:Finset O),(∀u∈rows,‖ringComplex u‖^2≤ Z^m)→
    ∀(y:σ→ primePool F→ℝ)(xj θ:ℝ),
      (∑u∈rows,‖∫t:ℝ,density (frequencyTwist g θ) xj t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Finset.univ Ψ
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) lists
            (fun i P=> coeff i P*kernelLogPhase (-t) (y i P)))
            (childLogTest W t) Z D) u)‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialTotalRows.original_input_rows_fourier_bound
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ hΦ hone B₀ hB₀ hb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  obtain ⟨Cm,hCm,hmeasure⟩:=InverseInitialOverlapHeight.twisted_polynomial_measure_energy g J
  refine ⟨J+(volume:Measure ℝ).integrablePower,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨(Cm+1)*C,Z₀,mul_pos (by linarith) hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=> by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows y xj θ
  have hZp:0< Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  let φ:O→ℝ→ℂ:=fun u t=>((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Finset.univ Ψ
    (assignedElement assigned qelem) 1 1
    (initialTest p (primeMark (all\assigned) lists
      (fun i P=> coeff i P*kernelLogPhase (-t) (y i P))) (childLogTest W t) Z D) u
  have ht:=hmeasure θ xj (fun u:rows=>φ u.val) (C*Z^(m+15*η+π+eps+loss))
    (by positivity)
    (fun u=> InverseInitialMarkedInputEnergy.marked_input_integrable p hg
      (frequencyTwist g θ) Finset.univ Ψ (assignedElement assigned qelem) u.val
      (all\assigned) lists coeff y W Z D xj)
    (fun t=> by
      apply (Finset.sum_coe_sort rows (fun u=>‖φ u t‖^2)).le.trans
      exact henergy Z hZ Dpool hD all assigned hassigned hK lists Hslot coeff
        hdis hHs hPs hac qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
        D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows y t)
  apply (Finset.sum_coe_sort rows (fun u=>‖∫t:ℝ,density (frequencyTwist g θ) xj t*φ u t‖^2)).symm.le.trans
  apply ht.trans
  have hh:0≤ C*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*(J+(volume:Measure ℝ).integrablePower)):=by positivity
  have he:=mul_le_mul_of_nonneg_right (show Cm≤ Cm+1 by linarith) hh
  convert he using 1 <;> simp only [pow_mul,pow_two,mul_pow] <;> first | rfl | ring

end InverseInitialTotalFourier

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical SchwartzMap ContDiff FourierTransform
namespace InverseInitialOriginalHeight
open InverseMoment InverseInitialProfile InverseInitialProfileBounds JointLogSeparation
open JointLogSeparation CompletedHeight

theorem child_eq_normTwisted (W:ℝ→ℂ)(θ:ℝ):childLogTest W θ=normTwistedSource W θ:=by
  rw [childLogTest_eq_clipped]
  funext x
  simp only [clippedSource,normTwistedSource,one_mul]

theorem child_support (W:ℝ→ℂ)(θ:ℝ):
    Function.support (childLogTest W θ)⊆Function.support W:=by
  rw [child_eq_normTwisted]
  exact normTwistedSource_support W θ

theorem child_smooth (W:ℝ→ℂ)(a b:ℝ)(ha:0< a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(θ:ℝ):
    ContDiff ℝ ∞ (childLogTest W θ):=by
  rw [child_eq_normTwisted]
  exact CanonicalRowCompletion.normTwistedSource_contDiff W a b ha hs hW θ

theorem kernelLogSource_child (W:ℝ→ℂ)(a b:ℝ)(ha:0< a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(θ:ℝ):
    kernelLogSource (childLogTest W θ) a b ha
      ((child_support W θ).trans hs) (child_smooth W a b ha hs hW θ)=
    frequencyTwist (kernelLogSource W a b ha hs hW) θ:=by
  ext x
  simp only [kernelLogSource_apply,childLogTest,
    frequencyTwist_apply,Real.log_exp]
  ring

end InverseInitialOriginalHeight

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators
namespace InverseInitialInputReindex
open Eisenstein SecondPassArithmetic InverseMoment
open InverseInitialArithmetic
local notation "O"=> Eisenstein.O

theorem input_puncture_span {ι:Type*}[DecidableEq ι](p:ι→ O)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,lambda∉Ideal.span {p i})
    (pool:Finset ι)(Ψ:O→*ℂ)(j₁ j₂:O)(hspan:Ideal.span {j₁}=Ideal.span {j₂})
    (test:Finset ι→ℂ)(u:O):
    inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) pool Ψ j₁ 1 1 test u=
      inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) pool Ψ j₂ 1 1 test u:=by
  rw [initial_input_row p hg,initial_input_row p hg]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [primeCoprimeMask_congr_span p A hspan]

theorem primeMark_subtype {σ ι:Type*}[DecidableEq σ][DecidableEq ι]
    (I:Finset σ)(L:σ→ Finset ι)(a:σ→ι→ℂ)(A:Finset ι):
    primeMark Finset.univ (fun i:I=> L i.val) (fun i:I=> a i.val) A=
      primeMark I L a A:=by
  exact Finset.prod_coe_sort I (fun i=> primeSlot (L i) (a i) A)

theorem primeMark_remaining {σ ι:Type*}[Fintype σ][DecidableEq σ][DecidableEq ι]
    (J:Finset σ)(L:σ→ Finset ι)(a:σ→ι→ℂ)(A:Finset ι):
    primeMark Finset.univ (fun i:{i:σ//i∉J}=> L i.val) (fun i:{i:σ//i∉J}=> a i.val) A=
      primeMark (Finset.univ\J) L a A:=by
  classical
  unfold primeMark
  exact (Finset.prod_subtype (Finset.univ\J) (by intro i;simp)
    (fun i=> primeSlot (L i) (a i) A)).symm

end InverseInitialInputReindex

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InverseInitialOverlapFresh
variable {σ : Type*} [DecidableEq σ]

omit [DecidableEq σ] in
theorem overlap_column_interval (I : Finset σ) (lo hi y : σ→ℝ)
    (a b jlo jhi yj yc : ℝ) (ha : 0< a) (hab : a≤ b)
    (hlo : ∀i∈I,0< lo i) (hy : ∀i∈I,y i∈Set.Icc (lo i) (hi i))
    (hjlo : 0< jlo) (hj : yj∈Set.Icc jlo jhi) (hc : 0< yc)
    (hsource : yj*yc/(∏i∈I,y i)∈Set.Icc a b) :
    yc∈Set.Icc (a*(∏i∈I,lo i)/jhi) (b*(∏i∈I,hi i)/jlo) := by
  have hyp : ∀i∈I,0< y i := fun i hi=>(hlo i hi).trans_le (hy i hi).1
  have hip : ∀i∈I,0< hi i := fun i hi=>(hyp i hi).trans_le (hy i hi).2
  have hprod : 0<∏i∈I,y i := Finset.prod_pos hyp
  have hloP : (∏i∈I,lo i)≤∏i∈I,y i :=
    Finset.prod_le_prod (fun i hi=>(hlo i hi).le) (fun i hi=>(hy i hi).1)
  have hhiP : (∏i∈I,y i)≤∏i∈I,hi i :=
    Finset.prod_le_prod (fun i hi=>(hyp i hi).le) (fun i hi=>(hy i hi).2)
  have hyj : 0< yj := hjlo.trans_le hj.1
  have hjhip : 0< jhi := hyj.trans_le hj.2
  have hsourceLo := (le_div_iff₀ hprod).mp hsource.1
  have hsourceHi := (div_le_iff₀ hprod).mp hsource.2
  constructor
  · apply (div_le_iff₀ hjhip).mpr
    calc
      a*(∏i∈I,lo i)≤ a*(∏i∈I,y i) := mul_le_mul_of_nonneg_left hloP ha.le
      _≤ yj*yc := hsourceLo
      _≤ jhi*yc := mul_le_mul_of_nonneg_right hj.2 hc.le
      _=yc*jhi := mul_comm _ _
  · apply (le_div_iff₀ hjlo).mpr
    calc
      yc*jlo=jlo*yc := mul_comm _ _
      _≤ yj*yc := mul_le_mul_of_nonneg_right hj.1 hc.le
      _≤ b*(∏i∈I,y i) := hsourceHi
      _≤ b*(∏i∈I,hi i) := mul_le_mul_of_nonneg_left hhiP (ha.le.trans hab)

omit [DecidableEq σ] in
theorem exists_overlap_fresh (I : Finset σ) (lo hi : σ→ℝ)
    (a b jlo jhi : ℝ) (ha : 0< a) (hab : a≤ b)
    (hlo : ∀i∈I,0< lo i) (hhi : ∀i∈I,lo i≤ hi i)
    (hjlo : 0< jlo) (hjhi : jlo≤ jhi) :
    ∃(wFresh : 𝓢(ℝ,ℂ))(A B:ℝ),0< A ∧ A≤ B ∧
      HasCompactSupport (wFresh:ℝ→ℂ) ∧ tsupport (wFresh:ℝ→ℂ)⊆Set.Icc A B ∧
      ∀(W:ℝ→ℂ),(Function.support W⊆Set.Icc a b)→
      ∀(y:σ→ℝ)(yj yc:ℝ),
      (∀i∈I,y i∈Set.Icc (lo i) (hi i))→ yj∈Set.Icc jlo jhi→0< yc→
      W (yj*yc/(∏i∈I,y i))≠0→ wFresh yc=1 := by
  let lower := a*(∏i∈I,lo i)/jhi
  let upper := b*(∏i∈I,hi i)/jlo
  have hl : 0< lower := div_pos (mul_pos ha (Finset.prod_pos hlo)) (hjlo.trans_le hjhi)
  have hu : 0< upper := div_pos (mul_pos (ha.trans_le hab)
    (Finset.prod_pos (fun i hi=>(hlo i hi).trans_le (hhi i hi)))) hjlo
  obtain ⟨w,hwc,hwone,hws⟩ := InverseSecondChildWindows.positive_cutoff
    lower (lower+upper+1) hl (by linarith)
  refine ⟨w,lower/2,lower+upper+2,half_pos hl,by linarith,hwc,?_,?_⟩
  · convert hws using 1 <;> first | rfl | ring
  · intro W hW y yj yc hy hj hc hn
    have hb := overlap_column_interval I lo hi y a b jlo jhi yj yc ha hab hlo hy hjlo hj hc (hW hn)
    apply hwone
    exact ⟨hb.1,by change yc≤ lower+upper+1;have := hb.2;change yc≤ upper at this;linarith⟩

end InverseInitialOverlapFresh

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace InverseInitialUniformFresh

/-- One compact window covers every overlap ratio with a bounded number of prime slots. -/
theorem exists_uniform_fresh (K:ℕ)(a b:ℝ)(ha:0< a)(hab:a≤ b):
    ∃(W:𝓢(ℝ,ℂ))(A B Bnorm:ℝ),0< A ∧ A≤ B ∧ 0≤ Bnorm ∧
      HasCompactSupport (W:ℝ→ℂ) ∧ tsupport (W:ℝ→ℂ)⊆Set.Icc A B ∧
      (∀x,‖W x‖≤ Bnorm) ∧
      ∀{σ:Type*}[DecidableEq σ](I:Finset σ),I.card≤ K→
      ∀(V:ℝ→ℂ),Function.support V⊆Set.Icc a b→
      ∀(y:σ→ℝ)(yj yc:ℝ),(∀i∈I,y i∈Set.Icc (1:ℝ) 2)→
        yj∈Set.Icc (1:ℝ) ((2:ℝ)^K)→0< yc→
        V (yj*yc/(∏i∈I,y i))≠0→ W yc=1:=by
  let lo:=a/(2:ℝ)^K
  let hi:=lo+b*(2:ℝ)^K+1
  have hlo:0< lo:=by dsimp [lo];positivity
  have hb:0< b:=ha.trans_le hab
  obtain ⟨W,hWc,hWone,hWs⟩:=InverseSecondChildWindows.positive_cutoff lo hi hlo (by
    dsimp [hi]
    have hbp : 0< b*(2:ℝ)^K:=by positivity
    linarith)
  refine ⟨W,lo/2,hi+1,(SchwartzMap.seminorm ℝ 0 0) W,half_pos hlo,?_,by positivity,hWc,hWs,
    SchwartzMap.norm_le_seminorm ℝ W,?_⟩
  · dsimp [hi]
    have hbp : 0< b*(2:ℝ)^K:=by positivity
    linarith
  · intro σ dec I hI V hV y yj yc hy hj hc hn
    have hh:=InverseInitialOverlapFresh.overlap_column_interval I (fun _=>1) (fun _=>2) y
      a b 1 ((2:ℝ)^K) yj yc ha hab (by intros;norm_num) hy (by norm_num) hj hc (hV hn)
    simp only [Finset.prod_const,one_pow,mul_one,div_one] at hh
    apply hWone
    refine ⟨hh.1,?_⟩
    have hp:(2:ℝ)^I.card≤(2:ℝ)^K:=pow_le_pow_right₀ (by norm_num) hI
    have hup:yc≤ b*(2:ℝ)^K:=hh.2.trans (mul_le_mul_of_nonneg_left hp hb.le)
    dsimp [hi]
    linarith

end InverseInitialUniformFresh

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical
open Eisenstein CompletedGauss _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve 
open InverseInitialOverlap InverseInitialRayAttachment
open InverseInitialPoissonBridge InverseInitialKernelBridge 
namespace InverseInitialEnergyCallerWindow
local notation "Eis" => Eisenstein.O

def originalSource (Z r b : ℝ) : Finset (Ideal Eis) :=
  (HeckeInverseAmplification.idealsUpTo ⌈Z^r*b⌉₊).filter Supported

theorem originalSource_supported (Z r b : ℝ) :
    ∀n∈originalSource Z r b,Squarefree n→ Supported n := by
  intro n hn _
  exact (Finset.mem_filter.mp hn).2

theorem residual_window_eq (W : ℝ→ℂ) {P j c : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hc : residual P j∣c)
    (Z r z G : ℝ) (hZ : 0< Z) :
    residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G)) =
      W (((reconstruct P j c).absNorm:ℝ)/Z^r) := by
  unfold residualOverlapWindow
  rw [←scaled_cutoff_argument hP hj hc hZ r z G]

/-- A live residual window reconstructs an ideal within the original finite norm cutoff. -/
theorem reconstructed_mem_originalSource
    (W : ℝ→ℂ) (Z r z G b : ℝ) (hZ : 0< Z) (hW : ∀x,W x≠0→ x≤ b)
    {P j c : Ideal Eis} (hP : CanonicalQuadraticSieve.Admissible P) (hj : j∣P)
    (hc : CanonicalQuadraticSieve.Admissible c) (hPc : residual P j∣c)
    (hlive : residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G))≠0) :
    reconstruct P j c∈originalSource Z r b := by
  have hs : Supported (reconstruct P j c) :=
    (supported_mul_iff _ _).mpr
      ⟨admissible_supported (InverseMoment.descentAdmissible_of_dvd hP hj),
        admissible_supported (InverseMoment.descentAdmissible_of_dvd hc (quadraticIdealQuotient_dvd hPc))⟩
  apply Finset.mem_filter.mpr
  refine ⟨InverseInitialRawDictionary.finite_source_cover W (Z^r) b
    (Real.rpow_pos_of_pos hZ r) hW _ hs.1 ?_,hs⟩
  rwa [residual_window_eq W hP.2.1 hj hPc Z r z G hZ] at hlive


end InverseInitialEnergyCallerWindow
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical
open Eisenstein CompletedGauss _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve 
open SecondPassArithmetic
namespace InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic 
open InverseInitialEnergyCallerWindow 
local notation "Eis"=> Eisenstein.O
variable {κ ι : Type*} [DecidableEq ι]

theorem input_finset_sum (p:ι→ Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,lambda∉Ideal.span {p i})(F:Finset ι)(Ψ:Eis→*ℂ)(j u:Eis)
    (T:Finset κ)(a:κ→ℂ)(H:κ→ Finset ι→ℂ) :
    inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ j 1 1 (fun A=>∑k∈T,a k*H k A) u=
      ∑k∈T,a k*inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ j 1 1 (H k) u := by
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro A hA
  ring

def tupleColumns (S:Finset (Ideal Eis))(T:Finset κ)(P:κ→ Ideal Eis)(j:Ideal Eis) :
    Finset (Ideal Eis) := T.biUnion (fun k=> columns S (P k) j)

theorem tupleColumns_admissible (S:Finset (Ideal Eis))(T:Finset κ)(P:κ→ Ideal Eis)
    (j:Ideal Eis)(hP:∀k∈T,CanonicalQuadraticSieve.Admissible (P k))(hj:∀k∈T,j∣P k)
    (hS:∀n∈S,Squarefree n→ Supported n) :
    ∀c∈tupleColumns S T P j,CanonicalQuadraticSieve.Admissible c := by
  intro c hc
  obtain ⟨k,hk,hc⟩ := Finset.mem_biUnion.mp hc
  exact columns_admissible S (hP k hk) (hj k hk) hS hc

theorem tupleColumns_coprime (S:Finset (Ideal Eis))(T:Finset κ)(P:κ→ Ideal Eis)
    (j:Ideal Eis)(hP:∀k∈T,CanonicalQuadraticSieve.Admissible (P k))(hj:∀k∈T,j∣P k) :
    ∀c∈tupleColumns S T P j,IsCoprime c j := by
  intro c hc
  obtain ⟨k,hk,hc⟩ := Finset.mem_biUnion.mp hc
  exact ((mem_columns (hP k hk).2.1 (hj k hk)).mp hc).2.1


end InverseInitialCommonTuples
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
noncomputable section
open scoped Classical BigOperators
namespace InverseInitialCompletePool
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve InverseInitialOverlap InverseInitialPoissonBridge
local notation "Eis" => Eisenstein.O
theorem original_column_norm_bound (S:Finset (Ideal Eis)){P j c:Ideal Eis}
    (hP:CanonicalQuadraticSieve.Admissible P)(hj:j∣P)(hc:c∈columns S P j) :
    c.absNorm≤ S.sup Ideal.absNorm*P.absNorm := by
  obtain ⟨hcs,hcj,hres,hnS⟩ := (mem_columns hP.2.1 hj).mp hc
  have hn := norm_reconstruct hres
  have hj0 := (InverseMoment.descentAdmissible_of_dvd hP hj).1
  have hjpos : 1≤ j.absNorm := Nat.one_le_iff_ne_zero.mpr
    (fun h=> hj0 (Ideal.absNorm_eq_zero_iff.mp h))
  have hnn : (reconstruct P j c).absNorm≤ S.sup Ideal.absNorm := Finset.le_sup hnS
  have hPN : (residual P j).absNorm≤ P.absNorm := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun h=> hP.1 (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm (quadraticIdealQuotient_dvd hj))
  calc
    c.absNorm≤ j.absNorm*c.absNorm := Nat.le_mul_of_pos_left _ hjpos
    _=(reconstruct P j c).absNorm*(residual P j).absNorm := hn.symm
    _≤ _ := Nat.mul_le_mul hnn hPN


end InverseInitialCompletePool
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace InverseInitialExcludedGeometry
open HeckeFamily InverseInitialExcludedPolynomial 
local notation "O"=> Eisenstein.O

def adjustedLength (Z r:ℝ)(j:Ideal O):ℝ:=r-Real.log (j.absNorm:ℝ)/Real.log Z

theorem adjusted_scale (Z r:ℝ)(hZ:1< Z){j:Ideal O}(hj:j≠0):
    Z^adjustedLength Z r j=Z^r/(j.absNorm:ℝ) := by
  have hjpos:0<(j.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj)
  have hzpos:=lt_trans zero_lt_one hZ
  rw [adjustedLength,Real.rpow_sub hzpos]
  congr 1
  rw [Real.rpow_def_of_pos hzpos]
  have hl:Real.log Z≠0:=(Real.log_pos hZ).ne'
  rw [mul_div_cancel₀ _ hl,Real.exp_log hjpos]

theorem divisor_norm_bounds {P j:Ideal O}(hP:P≠0)(hj:j∣P):
    1≤(j.absNorm:ℝ) ∧ (j.absNorm:ℝ)≤(P.absNorm:ℝ) := by
  have hj0:=ne_zero_of_dvd_ne_zero hP hj
  constructor
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  · exact_mod_cast Nat.le_of_dvd
      (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hP))
      (map_dvd Ideal.absNorm hj)

theorem adjustedLength_bounds (Z r η:ℝ)(hZ:1< Z){P j:Ideal O}
    (hP:P≠0)(hj:j∣P)(hlarge:Real.log (P.absNorm:ℝ)≤η*Real.log Z):
    r-η≤ adjustedLength Z r j ∧ adjustedLength Z r j≤ r := by
  obtain ⟨hn,hnP⟩:=divisor_norm_bounds hP hj
  have hl:0≤ Real.log (j.absNorm:ℝ):=Real.log_nonneg hn
  have hu:Real.log (j.absNorm:ℝ)≤η*Real.log Z:=
    (Real.log_le_log (lt_of_lt_of_le zero_lt_one hn) hnP).trans hlarge
  have hd:Real.log (j.absNorm:ℝ)/Real.log Z≤η:=(div_le_iff₀ (Real.log_pos hZ)).mpr hu
  have hd0:0≤ Real.log (j.absNorm:ℝ)/Real.log Z:=div_nonneg hl (Real.log_pos hZ).le
  dsimp [adjustedLength]
  constructor <;> linarith

theorem adjustedLength_eventually (P:Ideal O)(hP:P≠0)(η:ℝ)(hη:0<η):
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀r:ℝ,∀j∈idealDivisors P,
      r-η≤ adjustedLength Z r j ∧ adjustedLength Z r j≤ r := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log (P.absNorm:ℝ)/η))] with Z hZ hlog
  refine ⟨hZ,fun r j hj=> adjustedLength_bounds Z r η hZ hP ((mem_idealDivisors hP).mp hj) ?_⟩
  exact (div_le_iff₀ hη).mp hlog |>.trans_eq (mul_comm _ _)

theorem prime_coprime_of_norm_gt {P I:Ideal O}(hP:Prime P)(hI:I≠0)
    (hN:(I.absNorm:ℝ)<(P.absNorm:ℝ)):IsCoprime P I := by
  apply Ideal.coprime_of_no_prime_ge
  intro J hPJ hIJ hJ
  have hmax:=(Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have heq:=hmax.eq_of_le hJ.ne_top hPJ
  rw [←heq] at hIJ
  have hd:P∣I:=Ideal.dvd_iff_le.mpr hIJ
  exact (not_le_of_gt hN) (divisor_norm_bounds hI hd).2

theorem live_prime_deleted_coefficient (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(V:ℝ→ℂ)(a Y:ℝ)(hY:0< Y)
    (hV:∀x,V x≠0→ a≤ x)(hlarge:((∏Q∈S,Q).absNorm:ℝ)< a*Y)
    (P:Ideal O)(hP:Prime P)(hvp:V ((P.absNorm:ℝ)/Y)≠0):
    idealCoeff (χ.excludePrimes S hS) P=idealCoeff χ P := by
  rw [deleted_coefficient_product,if_pos]
  apply prime_coprime_of_norm_gt hP (prime_product_squarefree S hS).ne_zero
  exact hlarge.trans_le ((le_div_iff₀ hY).mp (hV _ hvp))

theorem prime_slot_unchanged (χ:Character)(S:Finset (Ideal O))
    (hS:∀P∈S,Prime P)(V:ℝ→ℂ)(a Y:ℝ)(hY:0< Y)
    (hV:∀x,V x≠0→ a≤ x)(hlarge:((∏Q∈S,Q).absNorm:ℝ)< a*Y)
    (P:Ideal O)(hP:Prime P):
    idealCoeff (χ.excludePrimes S hS) P*V ((P.absNorm:ℝ)/Y)=
      idealCoeff χ P*V ((P.absNorm:ℝ)/Y) := by
  by_cases hv:V ((P.absNorm:ℝ)/Y)=0
  · rw [hv,mul_zero,mul_zero]
  · rw [live_prime_deleted_coefficient χ S hS V a Y hY hV hlarge P hP hv]

end InverseInitialExcludedGeometry

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical
open Eisenstein _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve  UniqueFactorizationMonoid
namespace InverseInitialExcludedPool
open InverseInitialOverlap InverseInitialCommonTuples InverseInitialCompletePool InverseInitialPoissonBridge
local notation "O"=> Eisenstein.O

theorem column_outside (A E:Finset (Ideal O)){P j c:Ideal O}
    (hE:∀Q∈E,Prime Q)(hj:j∣P)(hP:outside E P)
    (hA:∀n∈A,outside E n)(hc:c∈columns A P j):outside E c := by
  obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hc
  obtain ⟨hnA,hns,hg⟩:=mem_original.mp hn
  have hjn:j∣n:=hg ▸ GCDMonoid.gcd_dvd_left n P
  intro Q hQ hd
  rcases (hE Q hQ).dvd_mul.mp hd with hn|hpr
  · exact hA n hnA Q hQ (hn.trans (quadraticIdealQuotient_dvd hjn))
  · exact hP Q hQ (hpr.trans (quadraticIdealQuotient_dvd hj))

theorem admissible_mem_excluded_complete (E:Finset (Ideal O)){I:Ideal O}
    (hI:CanonicalQuadraticSieve.Admissible I)(hout:outside E I)(D:ℕ)(hD:I.absNorm≤ D):
    I∈CanonicalRowCompletion.outsideSquarefreeIdeals E D := by
  apply Finset.mem_filter.mpr
  refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,hD,hout⟩,hI.2.1⟩
  exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)

/-- One finite norm cutoff contains all residual columns avoiding the excluded primes. -/
theorem exists_excluded_complete_pool {κ:Type*}(A E:Finset (Ideal O))(T:Finset κ)
    (P:κ→ Ideal O)(j:Ideal O)(hE:∀Q∈E,Prime Q)
    (hP:∀k∈T,CanonicalQuadraticSieve.Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside E (P k))
    (hA:∀n∈A,Squarefree n→ Supported n)(bmax Xmax:ℝ)(hb:0≤ bmax)(_hX:0≤ Xmax):
    ∃D:ℕ,tupleColumns (originalOutside A E) T P j⊆
      CanonicalRowCompletion.outsideSquarefreeIdeals E D ∧
      ∀b X:ℝ,0≤ b→ b≤ bmax→0≤ X→ X≤ Xmax→ b*X≤(D:ℝ) := by
  let D:=max (A.sup Ideal.absNorm*T.sup (fun k=>(P k).absNorm)) ⌈bmax*Xmax⌉₊
  refine ⟨D,?_,?_⟩
  · intro c hc
    obtain ⟨k,hk,hc⟩:=Finset.mem_biUnion.mp hc
    have hcA:c∈columns A (P k) j:=by
      obtain ⟨n,hn,he⟩:=Finset.mem_image.mp hc
      refine Finset.mem_image.mpr ⟨n,?_,he⟩
      obtain ⟨hnA,hns,hg⟩:=mem_original.mp hn
      exact mem_original.mpr ⟨(Finset.mem_filter.mp hnA).1,hns,hg⟩
    apply admissible_mem_excluded_complete E
      (columns_admissible A (hP k hk) (hj k hk) hA hcA)
      (column_outside _ E hE (hj k hk) (hPE k hk)
        (fun n hn=>(Finset.mem_filter.mp hn).2) hc)
    exact (original_column_norm_bound A (hP k hk) (hj k hk) hcA).trans
      ((Nat.mul_le_mul_left (A.sup Ideal.absNorm)
        (Finset.le_sup (f:=fun k=>(P k).absNorm) hk)).trans (le_max_left _ _))
  · intro b X hb0 hbb hX0 hXX
    apply (mul_le_mul hbb hXX hX0 hb).trans
    exact (Nat.le_ceil (bmax*Xmax)).trans (by exact_mod_cast (le_max_right
      (A.sup Ideal.absNorm*T.sup (fun k=>(P k).absNorm)) ⌈bmax*Xmax⌉₊))

end InverseInitialExcludedPool

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
