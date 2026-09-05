import GaloisForLFunctions.HTGeometry.TripticCompleteness
import GaloisForLFunctions.HTGeometry.TripticNormalForm
import GaloisForLFunctions.HTGeometry.TripticGammaProductRealization
import GaloisForLFunctions.HTGeometry.AllDepthSignatureDescent
import GaloisForLFunctions.HTGeometry.OrbitMarkerSourceFaceReconstruction
import GaloisForLFunctions.HTGeometry.TripticJetRowFreeness
import GaloisForLFunctions.HTGeometry.MeromorphicRationalBaseOperatorMatroid
import GaloisForLFunctions.HTGeometry.CountablePointFiniteConstraintCarrier
import GaloisForLFunctions.HTGeometry.ReflectionGradedPairFaceSignature
import Mathlib.Algebra.MonoidAlgebra.Basic

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

attribute [local instance] ellipticGammaStructuralGeneratorRestrictedDifferential
  ellipticGammaStructuralGeneratorDifferentialAlgebra ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

noncomputable local instance tripticQuotientDecidableEq (a b : ℂ) :
    DecidableEq (ℂ ⧸ tripticPeriodGroup a b) := Classical.decEq _

/-- `ℂ[δ][ℂ/H₃]`, with finite group support and finite differential order. -/
abbrev TripticDifferentialGroupAlgebra (a b : ℂ) :=
  AddMonoidAlgebra (Polynomial ℂ) (ℂ ⧸ tripticPeriodGroup a b)

/-- Carrier action, with class `g` represented by the source translated to `Quotient.out g`. -/
def tripticOperatorCarrier (a b : ℂ) (D : TripticDifferentialGroupAlgebra a b) : ℂ → ℂ :=
  ∑ g ∈ D.coeff.support, ∑ j ∈ (D.coeff g).support,
    fun z => (D.coeff g).coeff j * gammaJetSource a b (Quotient.out g) j z

/-- Mixed constant carried by the zeroth differential slice. -/
def tripticOperatorConst (D : TripticDifferentialGroupAlgebra a b) : ℂ :=
  ∑ g ∈ D.coeff.support, ∑ j ∈ (D.coeff g).support, (D.coeff g).coeff j * gammaJetConst j

theorem meromorphicOn_tripticOperatorCarrier {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (D : TripticDifferentialGroupAlgebra a b) :
    MeromorphicOn (tripticOperatorCarrier a b D) Set.univ := by
  classical
  rw [tripticOperatorCarrier]
  exact meromorphicOn_finsetSum D.coeff.support _ fun g _ =>
    meromorphicOn_finsetSum (D.coeff g).support _ fun j _ =>
      meromorphicOn_const_mul (meromorphicOn_gammaJetSource ha hb (Quotient.out g) j) _

theorem periodicOneGerm_tripticOperatorCarrier (a b : ℂ)
    (D : TripticDifferentialGroupAlgebra a b) :
    PeriodicOneGerm (tripticOperatorCarrier a b D) := by
  classical
  rw [tripticOperatorCarrier]
  exact periodicOneGerm_finsetSum D.coeff.support _ fun g _ =>
    periodicOneGerm_finsetSum (D.coeff g).support _ fun j _ =>
      periodicOneGerm_const_mul (periodicOneGerm_gammaJetSource a b (Quotient.out g) j) _

theorem mixedConstGerm_tripticOperatorCarrier {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (D : TripticDifferentialGroupAlgebra a b) :
    MixedConstGerm (tripticOperatorCarrier a b D) a b (tripticOperatorConst D) := by
  classical
  rw [tripticOperatorCarrier, tripticOperatorConst]
  exact mixedConstGerm_finsetSum D.coeff.support _ _ fun g _ =>
    mixedConstGerm_finsetSum (D.coeff g).support _ _ fun j _ =>
      mixedConstGerm_const_mul (mixedConstGerm_gammaJetSource ha hb (Quotient.out g) j) _

theorem sameClass_iff_mk_eq_mk (a b q p : ℂ) :
    SameClass a b q p ↔
      (QuotientAddGroup.mk q : ℂ ⧸ tripticPeriodGroup a b) = QuotientAddGroup.mk p := by
  rw [sameClass_iff]
  constructor
  · intro h
    have hmem : q - p ∈ tripticPeriodGroup a b := h
    have hneg := neg_mem (s := tripticPeriodGroup a b) hmem
    apply (QuotientAddGroup.eq).mpr
    have heq : -q + p = -(q - p) := by ring
    rw [heq]
    exact hneg
  · intro h
    have hmem : -q + p ∈ tripticPeriodGroup a b := (QuotientAddGroup.eq).mp h
    have hneg := neg_mem (s := tripticPeriodGroup a b) hmem
    show q - p ∈ tripticPeriodGroup a b
    have heq : q - p = -(-q + p) := by ring
    rw [heq]
    exact hneg

theorem sameClass_out_iff (a b p : ℂ) (g : ℂ ⧸ tripticPeriodGroup a b) :
    SameClass a b (Quotient.out g) p ↔ QuotientAddGroup.mk p = g := by
  rw [sameClass_iff_mk_eq_mk]
  rw [QuotientAddGroup.out_eq']
  exact eq_comm

theorem additiveOrbitalDivisorAt_tripticOperatorCarrier {a b : ℂ}
    (ha : 0 < a.im) (hb : 0 < b.im) (hindep : IndepPeriods a b)
    (D : TripticDifferentialGroupAlgebra a b) (p : ℂ) (i : ℕ) :
    additiveOrbitalDivisorAt (tripticOperatorCarrier a b D) b p (-((i : ℤ) + 1))
      = (-1 : ℂ) ^ i * (i.factorial : ℂ) * (D.coeff (QuotientAddGroup.mk p)).coeff i := by
  classical
  rw [tripticOperatorCarrier]
  rw [additiveOrbitalDivisorAt_finsetSum D.coeff.support _
    (fun g _ => meromorphicOn_finsetSum (D.coeff g).support _ fun j _ =>
      meromorphicOn_const_mul (meromorphicOn_gammaJetSource ha hb (Quotient.out g) j) _)
    (fun g _ => finiteOrbitSupport_finsetSum (D.coeff g).support _
      (fun j _ => meromorphicOn_const_mul
        (meromorphicOn_gammaJetSource ha hb (Quotient.out g) j) _)
      (fun j _ => finiteOrbitSupport_const_mul
        (meromorphicOn_gammaJetSource ha hb (Quotient.out g) j)
        (finiteOrbitSupport_gammaJetSource ha hb hindep (Quotient.out g) p j i) _))]
  have hinner : ∀ g ∈ D.coeff.support,
      additiveOrbitalDivisorAt
          (∑ j ∈ (D.coeff g).support,
            fun z => (D.coeff g).coeff j * gammaJetSource a b (Quotient.out g) j z)
          b p (-((i : ℤ) + 1))
        = if QuotientAddGroup.mk p = g
            then (D.coeff g).coeff i * ((-1 : ℂ) ^ i * (i.factorial : ℂ)) else 0 := by
    intro g hg
    rw [additiveOrbitalDivisorAt_finsetSum (D.coeff g).support _
      (fun j _ => meromorphicOn_const_mul
        (meromorphicOn_gammaJetSource ha hb (Quotient.out g) j) _)
      (fun j _ => finiteOrbitSupport_const_mul
        (meromorphicOn_gammaJetSource ha hb (Quotient.out g) j)
        (finiteOrbitSupport_gammaJetSource ha hb hindep (Quotient.out g) p j i) _)]
    have hscale : ∀ j ∈ (D.coeff g).support,
        additiveOrbitalDivisorAt
            (fun z => (D.coeff g).coeff j * gammaJetSource a b (Quotient.out g) j z)
            b p (-((i : ℤ) + 1))
          = (D.coeff g).coeff j * additiveOrbitalDivisorAt
              (gammaJetSource a b (Quotient.out g) j) b p (-((i : ℤ) + 1)) := by
      intro j hj
      exact additiveOrbitalDivisorAt_const_mul
        (meromorphicOn_gammaJetSource ha hb (Quotient.out g) j) _ b p _
    rw [Finset.sum_congr rfl hscale]
    by_cases hclass : QuotientAddGroup.mk p = g
    · rw [if_pos hclass]
      by_cases hi : i ∈ (D.coeff g).support
      · rw [Finset.sum_eq_single_of_mem i hi (by
          intro j hj hji
          rw [additiveOrbitalDivisorAt_gammaJetSource_of_ne_order ha hb
            (Quotient.out g) p j (Ne.symm hji), mul_zero])]
        rw [additiveOrbitalDivisorAt_gammaJetSource_sameClass ha hb hindep
          ((sameClass_out_iff a b p g).mpr hclass) i]
      · have hi0 : (D.coeff g).coeff i = 0 := by
          simpa [Polynomial.mem_support_iff] using hi
        rw [hi0, zero_mul]
        exact Finset.sum_eq_zero fun j hj => by
          rcases eq_or_ne j i with rfl | hji
          · rw [hi0, zero_mul]
          · rw [additiveOrbitalDivisorAt_gammaJetSource_of_ne_order ha hb
              (Quotient.out g) p j (Ne.symm hji), mul_zero]
    · rw [if_neg hclass]
      exact Finset.sum_eq_zero fun j hj => by
        rcases eq_or_ne i j with rfl | hij
        · rw [additiveOrbitalDivisorAt_gammaJetSource_of_not_sameClass ha hb
            (fun hs => hclass ((sameClass_out_iff a b p g).mp hs)) i, mul_zero]
        · rw [additiveOrbitalDivisorAt_gammaJetSource_of_ne_order ha hb
            (Quotient.out g) p j hij, mul_zero]
  rw [Finset.sum_congr rfl hinner]
  by_cases hp : QuotientAddGroup.mk p ∈ D.coeff.support
  · rw [Finset.sum_eq_single_of_mem (QuotientAddGroup.mk p) hp (by
      intro g hg hne
      rw [if_neg (Ne.symm hne)])]
    simp [mul_comm, mul_assoc]
  · have hz : D.coeff (QuotientAddGroup.mk p) = 0 := by
      simpa [Finsupp.mem_support_iff] using hp
    rw [hz]
    simp only [Polynomial.coeff_zero, mul_zero]
    exact Finset.sum_eq_zero fun g hg => by
      rw [if_neg (fun h : QuotientAddGroup.mk p = g => (h ▸ hp) hg)]

theorem finiteOrbitSupport_tripticOperatorCarrier {a b : ℂ}
    (ha : 0 < a.im) (hb : 0 < b.im) (hindep : IndepPeriods a b)
    (D : TripticDifferentialGroupAlgebra a b) (p : ℂ) (i : ℕ) :
    FiniteOrbitSupport (tripticOperatorCarrier a b D) b p (-((i : ℤ) + 1)) := by
  classical
  rw [tripticOperatorCarrier]
  exact finiteOrbitSupport_finsetSum D.coeff.support _
    (fun g _ => meromorphicOn_finsetSum (D.coeff g).support _ fun j _ =>
      meromorphicOn_const_mul (meromorphicOn_gammaJetSource ha hb (Quotient.out g) j) _)
    (fun g _ => finiteOrbitSupport_finsetSum (D.coeff g).support _
      (fun j _ => meromorphicOn_const_mul
        (meromorphicOn_gammaJetSource ha hb (Quotient.out g) j) _)
      (fun j _ => finiteOrbitSupport_const_mul
        (meromorphicOn_gammaJetSource ha hb (Quotient.out g) j)
        (finiteOrbitSupport_gammaJetSource ha hb hindep (Quotient.out g) p j i) _))

/-- Intrinsic finite operator cut out by finitely many divisor classes and a differential order. -/
noncomputable def tripticConstraintSupport (a b : ℂ) (P : Finset ℂ) :
    Finset (ℂ ⧸ tripticPeriodGroup a b) := by
  classical
  exact P.image fun q => QuotientAddGroup.mk q

def tripticConstraintOperator (a b : ℂ) (F : ℂ → ℂ) (P : Finset ℂ) (J : ℕ) :
    TripticDifferentialGroupAlgebra a b := by
  classical
  let S := tripticConstraintSupport a b P
  let poly : (ℂ ⧸ tripticPeriodGroup a b) → Polynomial ℂ := fun g =>
    ∑ j ∈ Finset.range J, Polynomial.monomial j
      (additiveOrbitalDivisorAt F b (Quotient.out g) (-((j : ℤ) + 1)) /
        ((-1 : ℂ) ^ j * (j.factorial : ℂ)))
  exact AddMonoidAlgebra.ofCoeff
    (Finsupp.onFinset S (fun g => if g ∈ S then poly g else 0) (by
      intro g hg
      by_contra hnot
      simp [hnot] at hg))

theorem tripticConstraintOperator_coeff_of_mem {a b : ℂ} (F : ℂ → ℂ) (P : Finset ℂ)
    (J : ℕ) {g : ℂ ⧸ tripticPeriodGroup a b}
    (hg : g ∈ tripticConstraintSupport a b P)
    {i : ℕ} (hi : i < J) :
    ((tripticConstraintOperator a b F P J).coeff g).coeff i =
      additiveOrbitalDivisorAt F b (Quotient.out g) (-((i : ℤ) + 1)) /
        ((-1 : ℂ) ^ i * (i.factorial : ℂ)) := by
  classical
  rw [tripticConstraintOperator, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.onFinset_apply]
  simp [hg, hi, Polynomial.coeff_monomial]

theorem tripticConstraintOperator_coeff_of_not_mem {a b : ℂ} (F : ℂ → ℂ) (P : Finset ℂ)
    (J : ℕ) {g : ℂ ⧸ tripticPeriodGroup a b}
    (hg : g ∉ tripticConstraintSupport a b P) :
    (tripticConstraintOperator a b F P J).coeff g = 0 := by
  classical
  rw [tripticConstraintOperator, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.onFinset_apply]
  simp [hg]

theorem tripticConstraintOperator_coeff_of_le {a b : ℂ} (F : ℂ → ℂ) (P : Finset ℂ)
    (J i : ℕ) (hi : J ≤ i) (g : ℂ ⧸ tripticPeriodGroup a b) :
    ((tripticConstraintOperator a b F P J).coeff g).coeff i = 0 := by
  classical
  rw [tripticConstraintOperator, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.onFinset_apply]
  by_cases hg : g ∈ tripticConstraintSupport a b P
  · simp [hg, Polynomial.coeff_monomial, Finset.mem_range, not_lt.mpr hi]
  · simp [hg]

theorem additiveOrbitalDivisorAt_eq_gammaCorrection_of_vanishing
    {F : ℂ → ℂ} {a b Cst : ℂ} (hF : MeromorphicOn F Set.univ)
    (hper : PeriodicOneGerm F) (hmixed : MixedConstGerm F a b Cst)
    (ha : 0 < a.im) (hb : 0 < b.im) (hindep : IndepPeriods a b)
    (P : Finset ℂ) (J : ℕ)
    (hvanish : ∀ (p : ℂ) (ell : ℤ), ell < 0 →
      additiveOrbitalDivisorAt (fun z => F z - gammaCorrection a b F P J z) b p ell = 0)
    (p : ℂ) (i : ℕ) :
    additiveOrbitalDivisorAt F b p (-((i : ℤ) + 1)) =
      additiveOrbitalDivisorAt (gammaCorrection a b F P J) b p (-((i : ℤ) + 1)) := by
  have hsplit := additiveOrbitalDivisorAt_sub hF
    (meromorphicOn_jetCombination ha hb (gammaCorrectionCoeff a b F P) P J)
    (finite_support_orbitalDivisorTerm hF hper hmixed ha
      (indepSwap_of_indepPeriods hindep) p (by omega : -((i : ℤ) + 1) < 0))
    (finiteOrbitSupport_jetCombination ha hb hindep
      (gammaCorrectionCoeff a b F P) P J p i)
  have hz := hvanish p (-((i : ℤ) + 1)) (by omega)
  rw [gammaCorrection] at hz ⊢
  rw [hsplit] at hz
  exact sub_eq_zero.mp hz

theorem additiveOrbitalDivisorAt_tripticConstraintOperatorCarrier_eq
    {F : ℂ → ℂ} {a b Cst : ℂ} (hF : MeromorphicOn F Set.univ)
    (hper : PeriodicOneGerm F) (hmixed : MixedConstGerm F a b Cst)
    (ha : 0 < a.im) (hb : 0 < b.im) (hindep : IndepPeriods a b)
    (P : Finset ℂ) (J : ℕ)
    (hvanish : ∀ (p : ℂ) (ell : ℤ), ell < 0 →
      additiveOrbitalDivisorAt (fun z => F z - gammaCorrection a b F P J z) b p ell = 0)
    (p : ℂ) (i : ℕ) :
    additiveOrbitalDivisorAt (tripticOperatorCarrier a b
        (tripticConstraintOperator a b F P J)) b p (-((i : ℤ) + 1)) =
      additiveOrbitalDivisorAt F b p (-((i : ℤ) + 1)) := by
  classical
  let g : ℂ ⧸ tripticPeriodGroup a b := QuotientAddGroup.mk p
  have hsame : SameClass a b (Quotient.out g) p :=
    (sameClass_out_iff a b p g).mpr rfl
  have hclass : additiveOrbitalDivisorAt F b (Quotient.out g) (-((i : ℤ) + 1)) =
      additiveOrbitalDivisorAt F b p (-((i : ℤ) + 1)) :=
    additiveOrbitalDivisorAt_congr_sameClass hF hper hmixed hsame (by omega)
  rw [additiveOrbitalDivisorAt_tripticOperatorCarrier ha hb hindep]
  by_cases hi : i < J
  · by_cases hg : g ∈ tripticConstraintSupport a b P
    · rw [tripticConstraintOperator_coeff_of_mem F P J hg hi, hclass]
      have hfac : ((-1 : ℂ) ^ i * (i.factorial : ℂ)) ≠ 0 :=
        mul_ne_zero (pow_ne_zero i (by norm_num)) (by exact_mod_cast i.factorial_ne_zero)
      exact mul_div_cancel₀ _ hfac
    · rw [tripticConstraintOperator_coeff_of_not_mem F P J hg]
      simp only [Polynomial.coeff_zero, mul_zero]
      have hnone : ¬ ∃ q ∈ P, SameClass a b q p := by
        rintro ⟨q, hq, hqp⟩
        apply hg
        rw [tripticConstraintSupport]
        refine Finset.mem_image.mpr ⟨q, hq, ?_⟩
        exact (sameClass_iff_mk_eq_mk a b q p).mp hqp
      have hgamma : additiveOrbitalDivisorAt (gammaCorrection a b F P J) b p
          (-((i : ℤ) + 1)) = 0 := by
        exact additiveOrbitalDivisorAt_jetCombination_of_notMem ha hb hindep
          (gammaCorrectionCoeff a b F P) P J hnone
      rw [← additiveOrbitalDivisorAt_eq_gammaCorrection_of_vanishing
        hF hper hmixed ha hb hindep P J hvanish p i] at hgamma
      exact hgamma.symm
  · have hJi : J ≤ i := not_lt.mp hi
    rw [tripticConstraintOperator_coeff_of_le F P J i hJi g]
    simp only [mul_zero]
    have hgamma : additiveOrbitalDivisorAt (gammaCorrection a b F P J) b p
        (-((i : ℤ) + 1)) = 0 := by
      exact additiveOrbitalDivisorAt_jetCombination_of_le ha hb hindep
        (gammaCorrectionCoeff a b F P) P hJi p
    rw [← additiveOrbitalDivisorAt_eq_gammaCorrection_of_vanishing
      hF hper hmixed ha hb hindep P J hvanish p i] at hgamma
    exact hgamma.symm

theorem exists_tripticOperator_normalForm
    {F : ℂ → ℂ} {a b Cst : ℂ} (hF : MeromorphicOn F Set.univ)
    (hper : PeriodicOneGerm F) (hmixed : MixedConstGerm F a b Cst)
    (ha : 0 < a.im) (hb : 0 < b.im) (hindep : IndepPeriods a b)
    (hindepA : LinearIndependent ℝ ![(1 : ℂ), a])
    (hindepB : LinearIndependent ℝ ![(1 : ℂ), b]) :
    ∃ D : TripticDifferentialGroupAlgebra a b,
      DifferentiallyAlgebraic
        (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ) := by
  obtain ⟨P, J, hvanish⟩ :=
    exists_gammaCorrection_vanishing_divisor hF hper hmixed ha hb hindep hindepA
  let D := tripticConstraintOperator a b F P J
  refine ⟨D, ?_⟩
  have hDmero := meromorphicOn_tripticOperatorCarrier ha hb D
  have hDper := periodicOneGerm_tripticOperatorCarrier a b D
  have hDmixed := mixedConstGerm_tripticOperatorCarrier ha hb D
  have hGmero : MeromorphicOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ :=
    fun z _ => (hF z (Set.mem_univ z)).sub (hDmero z (Set.mem_univ z))
  have hGper : PeriodicOneGerm (fun z => F z - tripticOperatorCarrier a b D z) :=
    periodicOneGerm_sub hper hDper
  have hGmixed : MixedConstGerm (fun z => F z - tripticOperatorCarrier a b D z) a b
      (Cst - tripticOperatorConst D) := mixedConstGerm_sub hmixed hDmixed
  have hzero : ∀ (p : ℂ) (ell : ℤ), ell < 0 →
      additiveOrbitalDivisorAt (fun z => F z - tripticOperatorCarrier a b D z) b p ell = 0 := by
    intro p ell hell
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, ell = -((i : ℤ) + 1) := ⟨(-ell - 1).toNat, by omega⟩
    rw [additiveOrbitalDivisorAt_sub hF hDmero
      (finite_support_orbitalDivisorTerm hF hper hmixed ha
        (indepSwap_of_indepPeriods hindep) p (by omega))
      (finiteOrbitSupport_tripticOperatorCarrier ha hb hindep D p i),
      additiveOrbitalDivisorAt_tripticConstraintOperatorCarrier_eq
        hF hper hmixed ha hb hindep P J hvanish p i,
      sub_self]
  exact (differentiallyAlgebraic_toMeromorphicNFOn_of_vanishing_orbital_divisor
    hGmero hGper hGmixed ha hb (indepTriple_of_indepPeriods hindep) hindepA hindepB hzero).2

theorem tripticOperator_normalForm_unique
    {F : ℂ → ℂ} {a b Cst : ℂ} (hF : MeromorphicOn F Set.univ)
    (hper : PeriodicOneGerm F) (hmixed : MixedConstGerm F a b Cst)
    (ha : 0 < a.im) (hb : 0 < b.im) (hindep : IndepPeriods a b)
    (hindepA : LinearIndependent ℝ ![(1 : ℂ), a])
    (hindepB : LinearIndependent ℝ ![(1 : ℂ), b])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b))
    {D E : TripticDifferentialGroupAlgebra a b}
    (hD : DifferentiallyAlgebraic
      (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ))
    (hE : DifferentiallyAlgebraic
      (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b E z) Set.univ)) :
    D = E := by
  have normalForm_zero : ∀ (A : TripticDifferentialGroupAlgebra a b),
      DifferentiallyAlgebraic
        (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b A z) Set.univ) →
      ∀ (p : ℂ) (ell : ℤ), ell < 0 →
        additiveOrbitalDivisorAt (fun z => F z - tripticOperatorCarrier a b A z) b p ell = 0 := by
    intro A hA
    have hAmero := meromorphicOn_tripticOperatorCarrier ha hb A
    have hAper := periodicOneGerm_tripticOperatorCarrier a b A
    have hAmixed := mixedConstGerm_tripticOperatorCarrier ha hb A
    exact (differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero
      (fun z _ => (hF z (Set.mem_univ z)).sub (hAmero z (Set.mem_univ z)))
      (periodicOneGerm_sub hper hAper) (mixedConstGerm_sub hmixed hAmixed)
      ha hb hindep hindepA hindepB hperiods).mp hA
  have hzD := normalForm_zero D hD
  have hzE := normalForm_zero E hE
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  apply Polynomial.ext
  intro i
  have hDi := hzD (Quotient.out g) (-((i : ℤ) + 1)) (by omega)
  have hEi := hzE (Quotient.out g) (-((i : ℤ) + 1)) (by omega)
  rw [additiveOrbitalDivisorAt_sub hF (meromorphicOn_tripticOperatorCarrier ha hb D)
      (finite_support_orbitalDivisorTerm hF hper hmixed ha
        (indepSwap_of_indepPeriods hindep) (Quotient.out g) (by omega))
      (finiteOrbitSupport_tripticOperatorCarrier ha hb hindep D (Quotient.out g) i),
    additiveOrbitalDivisorAt_tripticOperatorCarrier ha hb hindep D
      (Quotient.out g) i, QuotientAddGroup.out_eq'] at hDi
  rw [additiveOrbitalDivisorAt_sub hF (meromorphicOn_tripticOperatorCarrier ha hb E)
      (finite_support_orbitalDivisorTerm hF hper hmixed ha
        (indepSwap_of_indepPeriods hindep) (Quotient.out g) (by omega))
      (finiteOrbitSupport_tripticOperatorCarrier ha hb hindep E (Quotient.out g) i),
    additiveOrbitalDivisorAt_tripticOperatorCarrier ha hb hindep E
      (Quotient.out g) i, QuotientAddGroup.out_eq'] at hEi
  have hscale : ((-1 : ℂ) ^ i * (i.factorial : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero i (by norm_num)) (by exact_mod_cast i.factorial_ne_zero)
  apply mul_left_cancel₀ hscale
  linear_combination hEi - hDi

theorem existsUnique_tripticOperator_normalForm
    {F : ℂ → ℂ} {a b Cst : ℂ} (hF : MeromorphicOn F Set.univ)
    (hper : PeriodicOneGerm F) (hmixed : MixedConstGerm F a b Cst)
    (ha : 0 < a.im) (hb : 0 < b.im) (hindep : IndepPeriods a b)
    (hindepA : LinearIndependent ℝ ![(1 : ℂ), a])
    (hindepB : LinearIndependent ℝ ![(1 : ℂ), b])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b)) :
    ∃! D : TripticDifferentialGroupAlgebra a b,
      DifferentiallyAlgebraic
        (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ) := by
  obtain ⟨D, hD⟩ := exists_tripticOperator_normalForm hF hper hmixed ha hb hindep hindepA hindepB
  exact ⟨D, hD, fun E hE => tripticOperator_normalForm_unique hF hper hmixed ha hb hindep
    hindepA hindepB hperiods hE hD⟩

theorem tripticOperatorCarrier_zero (a b : ℂ) :
    tripticOperatorCarrier a b (0 : TripticDifferentialGroupAlgebra a b) = 0 := by
  funext z
  simp [tripticOperatorCarrier]

theorem differentiallyAlgebraic_iff_tripticNormalFormOperator_eq_zero
    {F : ℂ → ℂ} {a b Cst : ℂ} (hF : MeromorphicOn F Set.univ)
    (hper : PeriodicOneGerm F) (hmixed : MixedConstGerm F a b Cst)
    (ha : 0 < a.im) (hb : 0 < b.im) (hindep : IndepPeriods a b)
    (hindepA : LinearIndependent ℝ ![(1 : ℂ), a])
    (hindepB : LinearIndependent ℝ ![(1 : ℂ), b])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b))
    {D : TripticDifferentialGroupAlgebra a b}
    (hD : DifferentiallyAlgebraic
      (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ)) :
    DifferentiallyAlgebraic (toMeromorphicNFOn F Set.univ) ↔ D = 0 := by
  constructor
  · intro hFDA
    have hzero : DifferentiallyAlgebraic
        (toMeromorphicNFOn
          (fun z => F z - tripticOperatorCarrier a b
            (0 : TripticDifferentialGroupAlgebra a b) z) Set.univ) := by
      simpa [tripticOperatorCarrier_zero] using hFDA
    exact tripticOperator_normalForm_unique hF hper hmixed ha hb hindep hindepA hindepB hperiods
      hD hzero
  · rintro rfl
    simpa [tripticOperatorCarrier_zero] using hD

theorem additiveOrbitalDivisorAt_eq_tripticOperatorCarrier_of_normalForm
    {F : ℂ → ℂ} {a b Cst : ℂ} (hF : MeromorphicOn F Set.univ)
    (hper : PeriodicOneGerm F) (hmixed : MixedConstGerm F a b Cst)
    (ha : 0 < a.im) (hb : 0 < b.im) (hindep : IndepPeriods a b)
    (hindepA : LinearIndependent ℝ ![(1 : ℂ), a])
    (hindepB : LinearIndependent ℝ ![(1 : ℂ), b])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b))
    {D : TripticDifferentialGroupAlgebra a b}
    (hD : DifferentiallyAlgebraic
      (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ))
    (p : ℂ) (i : ℕ) :
    additiveOrbitalDivisorAt F b p (-((i : ℤ) + 1)) =
      additiveOrbitalDivisorAt (tripticOperatorCarrier a b D) b p (-((i : ℤ) + 1)) := by
  have hDmero := meromorphicOn_tripticOperatorCarrier ha hb D
  have hzero := (differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero
    (fun z _ => (hF z (Set.mem_univ z)).sub (hDmero z (Set.mem_univ z)))
    (periodicOneGerm_sub hper (periodicOneGerm_tripticOperatorCarrier a b D))
    (mixedConstGerm_sub hmixed (mixedConstGerm_tripticOperatorCarrier ha hb D))
    ha hb hindep hindepA hindepB hperiods).mp hD p (-((i : ℤ) + 1)) (by omega)
  change additiveOrbitalDivisorAt
    (fun z => F z - tripticOperatorCarrier a b D z) b p (-((i : ℤ) + 1)) = 0 at hzero
  rw [additiveOrbitalDivisorAt_sub hF hDmero
    (finite_support_orbitalDivisorTerm hF hper hmixed ha
      (indepSwap_of_indepPeriods hindep) p (by omega))
    (finiteOrbitSupport_tripticOperatorCarrier ha hb hindep D p i)] at hzero
  exact sub_eq_zero.mp hzero

theorem mem_finiteSupportTranslationStabilizer_iff_coeff_add
    {G : Type*} [AddCommGroup G] (D : G →₀ Polynomial ℂ) (q : G) :
    q ∈ finiteSupportTranslationStabilizer D ↔
      ∀ g : G, ∀ i : ℕ, (D (g + q)).coeff i = (D g).coeff i := by
  constructor
  · intro h g i
    have heq := congrArg (fun E : G →₀ Polynomial ℂ => E (g + q)) h
    rw [translateFiniteSupport_apply_add] at heq
    exact congrArg (fun P : Polynomial ℂ => P.coeff i) heq.symm
  · intro h
    apply Finsupp.ext
    intro y
    have hpoly : D ((y - q) + q) = D (y - q) := by
      apply Polynomial.ext
      intro i
      exact h (y - q) i
    have htrans := translateFiniteSupport_apply_add q (y - q) D
    rw [sub_add_cancel] at htrans hpoly
    exact htrans.trans hpoly.symm

theorem differentiallyAlgebraic_shiftDiff_iff_operator_stabilizer
    {F : ℂ → ℂ} {a b Cst : ℂ} (hF : MeromorphicOn F Set.univ)
    (hper : PeriodicOneGerm F) (hmixed : MixedConstGerm F a b Cst)
    (ha : 0 < a.im) (hb : 0 < b.im) (hindep : IndepPeriods a b)
    (hindepA : LinearIndependent ℝ ![(1 : ℂ), a])
    (hindepB : LinearIndependent ℝ ![(1 : ℂ), b])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b))
    {D : TripticDifferentialGroupAlgebra a b}
    (hD : DifferentiallyAlgebraic
      (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ))
    (h : ℂ) :
    DifferentiallyAlgebraic
        (toMeromorphicNFOn (HTGeometry.shiftDiffFun h F) Set.univ) ↔
      (QuotientAddGroup.mk h : ℂ ⧸ tripticPeriodGroup a b) ∈
        finiteSupportTranslationStabilizer D.coeff := by
  have hFhmero : MeromorphicOn (fun z => F (z + h)) Set.univ := by
    intro z hz
    exact meromorphicAt_comp_add.mpr (hF (z + h) (Set.mem_univ _))
  have hFhper := periodicOneGerm_comp_add hper h
  have hFhmixed := mixedConstGerm_comp_add' hmixed h
  have hGmero : MeromorphicOn (HTGeometry.shiftDiffFun h F) Set.univ := by
    intro z hz
    exact (hFhmero z (Set.mem_univ z)).sub (hF z (Set.mem_univ z))
  have hGper : PeriodicOneGerm (HTGeometry.shiftDiffFun h F) :=
    periodicOneGerm_sub hFhper hper
  have hGmixed : MixedConstGerm (HTGeometry.shiftDiffFun h F) a b 0 := by
    change MixedConstGerm (fun z => F (z + h) - F z) a b 0
    simpa using mixedConstGerm_sub hFhmixed hmixed
  have hdiv : ∀ (p : ℂ) (i : ℕ),
      additiveOrbitalDivisorAt (HTGeometry.shiftDiffFun h F) b p (-((i : ℤ) + 1)) =
        ((-1 : ℂ) ^ i * (i.factorial : ℂ)) *
          ((D.coeff (QuotientAddGroup.mk p + QuotientAddGroup.mk h)).coeff i -
            (D.coeff (QuotientAddGroup.mk p)).coeff i) := by
    intro p i
    rw [additiveOrbitalDivisorAt_shiftDiffFun hF
      (finite_support_orbitalDivisorTerm hFhmero hFhper hFhmixed ha
        (indepSwap_of_indepPeriods hindep) p (by omega))
      (finite_support_orbitalDivisorTerm hF hper hmixed ha
        (indepSwap_of_indepPeriods hindep) p (by omega)),
      additiveOrbitalDivisorAt_eq_tripticOperatorCarrier_of_normalForm
        hF hper hmixed ha hb hindep hindepA hindepB hperiods hD (p + h) i,
      additiveOrbitalDivisorAt_eq_tripticOperatorCarrier_of_normalForm
        hF hper hmixed ha hb hindep hindepA hindepB hperiods hD p i,
      additiveOrbitalDivisorAt_tripticOperatorCarrier ha hb hindep D (p + h) i,
      additiveOrbitalDivisorAt_tripticOperatorCarrier ha hb hindep D p i]
    have hmk : (QuotientAddGroup.mk (p + h) : ℂ ⧸ tripticPeriodGroup a b) =
        QuotientAddGroup.mk p + QuotientAddGroup.mk h := rfl
    rw [hmk]
    ring
  rw [differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero
    hGmero hGper hGmixed ha hb hindep hindepA hindepB hperiods,
    mem_finiteSupportTranslationStabilizer_iff_coeff_add]
  constructor
  · intro hzero g i
    have hz := hzero (Quotient.out g) (-((i : ℤ) + 1)) (by omega)
    rw [hdiv (Quotient.out g) i, QuotientAddGroup.out_eq'] at hz
    have hscale : ((-1 : ℂ) ^ i * (i.factorial : ℂ)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero i (by norm_num)) (by exact_mod_cast i.factorial_ne_zero)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hscale)
  · intro hcoeff p ell hell
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, ell = -((i : ℤ) + 1) := ⟨(-ell - 1).toNat, by omega⟩
    rw [hdiv p i, hcoeff (QuotientAddGroup.mk p) i, sub_self, mul_zero]

noncomputable def finiteSubgroupPolynomialMarker {G : Type*} [AddCommGroup G]
    (K : AddSubgroup G) [Finite K] : G →₀ Polynomial ℂ := by
  classical
  letI := Fintype.ofFinite K
  exact ∑ k : K, Finsupp.single k.1 (Polynomial.C 1)

theorem finiteSubgroupPolynomialMarker_apply_of_mem {G : Type*} [AddCommGroup G]
    (K : AddSubgroup G) [Finite K] {g : G} (hg : g ∈ K) :
    finiteSubgroupPolynomialMarker K g = Polynomial.C 1 := by
  classical
  letI := Fintype.ofFinite K
  let k : K := ⟨g, hg⟩
  rw [finiteSubgroupPolynomialMarker]
  change Finsupp.applyAddHom g (∑ l : K, Finsupp.single l.1 (Polynomial.C 1)) = _
  rw [map_sum]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (by
    intro l hl hlk
    have hne : (l : G) ≠ g := fun h => hlk (Subtype.ext h)
    simp [hne])]
  simp [k]

theorem finiteSubgroupPolynomialMarker_apply_of_not_mem {G : Type*} [AddCommGroup G]
    (K : AddSubgroup G) [Finite K] {g : G} (hg : g ∉ K) :
    finiteSubgroupPolynomialMarker K g = 0 := by
  classical
  letI := Fintype.ofFinite K
  rw [finiteSubgroupPolynomialMarker]
  change Finsupp.applyAddHom g (∑ k : K, Finsupp.single k.1 (Polynomial.C 1)) = _
  rw [map_sum]
  exact Finset.sum_eq_zero fun k hk => by
    have hne : (k : G) ≠ g := fun h => hg (h ▸ k.2)
    simp [hne]

theorem finiteSupportTranslationStabilizer_finiteSubgroupPolynomialMarker
    {G : Type*} [AddCommGroup G] (K : AddSubgroup G) [Finite K] :
    finiteSupportTranslationStabilizer (finiteSubgroupPolynomialMarker K) = K := by
  ext q
  rw [mem_finiteSupportTranslationStabilizer_iff_coeff_add]
  constructor
  · intro h
    have h0 := h 0 0
    by_contra hq
    rw [zero_add, finiteSubgroupPolynomialMarker_apply_of_not_mem K hq,
      finiteSubgroupPolynomialMarker_apply_of_mem K K.zero_mem] at h0
    norm_num at h0
  · intro hq g i
    have hmem : g + q ∈ K ↔ g ∈ K := by
      constructor
      · intro hgq
        have hh := K.add_mem hgq (K.neg_mem hq)
        simpa [add_assoc] using hh
      · intro hg
        exact K.add_mem hg hq
    by_cases hg : g ∈ K
    · rw [finiteSubgroupPolynomialMarker_apply_of_mem K (hmem.mpr hg),
        finiteSubgroupPolynomialMarker_apply_of_mem K hg]
    · rw [finiteSubgroupPolynomialMarker_apply_of_not_mem K (fun h => hg (hmem.mp h)),
        finiteSubgroupPolynomialMarker_apply_of_not_mem K hg]

def tripticFiniteSubgroupOperator (a b : ℂ)
    (K : AddSubgroup (ℂ ⧸ tripticPeriodGroup a b)) [Finite K] :
    TripticDifferentialGroupAlgebra a b :=
  AddMonoidAlgebra.ofCoeff (finiteSubgroupPolynomialMarker K)

theorem tripticFiniteSubgroupOperator_ne_zero (a b : ℂ)
    (K : AddSubgroup (ℂ ⧸ tripticPeriodGroup a b)) [Finite K] :
    tripticFiniteSubgroupOperator a b K ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun D : TripticDifferentialGroupAlgebra a b => (D.coeff 0).coeff 0) hzero
  rw [tripticFiniteSubgroupOperator, AddMonoidAlgebra.coeff_ofCoeff,
    finiteSubgroupPolynomialMarker_apply_of_mem K K.zero_mem] at hcoeff
  norm_num at hcoeff

theorem finiteSupportTranslationStabilizer_tripticFiniteSubgroupOperator
    (a b : ℂ) (K : AddSubgroup (ℂ ⧸ tripticPeriodGroup a b)) [Finite K] :
    finiteSupportTranslationStabilizer (tripticFiniteSubgroupOperator a b K).coeff = K := by
  rw [tripticFiniteSubgroupOperator, AddMonoidAlgebra.coeff_ofCoeff,
    finiteSupportTranslationStabilizer_finiteSubgroupPolynomialMarker]

theorem finite_tripticOperator_stabilizer_of_ne_zero {a b : ℂ}
    (D : TripticDifferentialGroupAlgebra a b) (hD : D ≠ 0) :
    Finite (finiteSupportTranslationStabilizer D.coeff) := by
  apply finite_finiteSupportTranslationStabilizer_of_ne_zero
  intro hcoeff
  apply hD
  apply AddMonoidAlgebra.ext
  exact hcoeff

theorem tripticOperatorCarrier_differentiallyAlgebraic_iff {a b : ℂ}
    (ha : 0 < a.im) (hb : 0 < b.im) (hindep : IndepPeriods a b)
    (hindepA : LinearIndependent ℝ ![(1 : ℂ), a])
    (hindepB : LinearIndependent ℝ ![(1 : ℂ), b])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b))
    (D : TripticDifferentialGroupAlgebra a b) :
    DifferentiallyAlgebraic
        (toMeromorphicNFOn (tripticOperatorCarrier a b D) Set.univ) ↔ D = 0 := by
  rw [differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero
    (meromorphicOn_tripticOperatorCarrier ha hb D)
    (periodicOneGerm_tripticOperatorCarrier a b D)
    (mixedConstGerm_tripticOperatorCarrier ha hb D)
    ha hb hindep hindepA hindepB hperiods]
  constructor
  · intro hzero
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    apply Polynomial.ext
    intro i
    have h := hzero (Quotient.out g) (-((i : ℤ) + 1)) (by omega)
    rw [additiveOrbitalDivisorAt_tripticOperatorCarrier ha hb hindep D
      (Quotient.out g) i, QuotientAddGroup.out_eq'] at h
    have hfac : ((i.factorial : ℂ)) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    have hsign : ((-1 : ℂ) ^ i) ≠ 0 := pow_ne_zero i (by norm_num)
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hsign hfac)
  · rintro rfl p ell hell
    rw [tripticOperatorCarrier]
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.support_zero, Finset.sum_empty]
    exact additiveOrbitalDivisorAt_eq_zero_of_terms 0 b p ell fun m => by
      have hfun : (fun w : ℂ => (0 : ℂ → ℂ) (w + b) - (0 : ℂ → ℂ) w) = fun _ => 0 := by
        funext z
        simp
      rw [hfun]
      exact laurentCoeff_eq_zero_of_analyticAt analyticAt_const hell

theorem exists_tripticCarrier_with_exact_finite_spectrum
    {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) (hindep : IndepPeriods a b)
    (hindepA : LinearIndependent ℝ ![(1 : ℂ), a])
    (hindepB : LinearIndependent ℝ ![(1 : ℂ), b])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b))
    (K : AddSubgroup (ℂ ⧸ tripticPeriodGroup a b)) [Finite K] :
    ∃ (F : ℂ → ℂ) (D : TripticDifferentialGroupAlgebra a b),
      D ≠ 0 ∧ MeromorphicOn F Set.univ ∧ PeriodicOneGerm F ∧
      MixedConstGerm F a b (tripticOperatorConst D) ∧
      DifferentiallyAlgebraic
        (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ) ∧
      ∀ h : ℂ, DifferentiallyAlgebraic
          (toMeromorphicNFOn (HTGeometry.shiftDiffFun h F) Set.univ) ↔
        (QuotientAddGroup.mk h : ℂ ⧸ tripticPeriodGroup a b) ∈ K := by
  let D := tripticFiniteSubgroupOperator a b K
  let F := tripticOperatorCarrier a b D
  have hnormal : DifferentiallyAlgebraic
      (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ) := by
    have hfun : (fun z => F z - tripticOperatorCarrier a b D z) =
        tripticOperatorCarrier a b (0 : TripticDifferentialGroupAlgebra a b) := by
      funext z
      simp [F, tripticOperatorCarrier_zero]
    rw [hfun]
    exact (tripticOperatorCarrier_differentiallyAlgebraic_iff
      ha hb hindep hindepA hindepB hperiods 0).2 rfl
  refine ⟨F, D, tripticFiniteSubgroupOperator_ne_zero a b K,
    meromorphicOn_tripticOperatorCarrier ha hb D,
    periodicOneGerm_tripticOperatorCarrier a b D,
    mixedConstGerm_tripticOperatorCarrier ha hb D, hnormal, ?_⟩
  intro h
  rw [differentiallyAlgebraic_shiftDiff_iff_operator_stabilizer
    (meromorphicOn_tripticOperatorCarrier ha hb D)
    (periodicOneGerm_tripticOperatorCarrier a b D)
    (mixedConstGerm_tripticOperatorCarrier ha hb D)
    ha hb hindep hindepA hindepB hperiods hnormal h,
    finiteSupportTranslationStabilizer_tripticFiniteSubgroupOperator]

/-! ### Literal differential-translation action and convolution law -/

/-- Differentiation preserves punctured-germ `1`-periodicity. -/
theorem periodicOneGerm_deriv_of_meromorphicOn {F : ℂ → ℂ}
    (hF : MeromorphicOn F Set.univ) (hper : PeriodicOneGerm F) :
    PeriodicOneGerm (deriv F) := by
  intro z
  obtain ⟨W, hWopen, hWmem, hW⟩ := exists_isOpen_of_eventually_nhdsNE
    ((hper z).and ((eventually_nhdsNE_analyticAt_comp_add hF 0 z).and
      (eventually_nhdsNE_analyticAt_comp_add hF 1 z)))
  filter_upwards [hWmem] with w hw
  have han0 : AnalyticAt ℂ F w := by simpa using (hW w hw).2.1
  have han1 : AnalyticAt ℂ F (w + 1) := (hW w hw).2.2
  have heq : (fun u => F (u + 1)) =ᶠ[𝓝 w] F := by
    filter_upwards [hWopen.mem_nhds hw] with u hu
    exact (hW u hu).1
  have hderiv := heq.deriv_eq
  rw [deriv_comp_add_const] at hderiv
  exact hderiv

/-- Every differential jet of a punctured-germ periodic meromorphic function is periodic. -/
theorem periodicOneGerm_iteratedDeriv_of_meromorphicOn {F : ℂ → ℂ}
    (hF : MeromorphicOn F Set.univ) (hper : PeriodicOneGerm F) (j : ℕ) :
    PeriodicOneGerm (iteratedDeriv j F) := by
  induction j with
  | zero => simpa [iteratedDeriv_zero] using hper
  | succ j ih =>
      rw [iteratedDeriv_succ]
      exact periodicOneGerm_deriv_of_meromorphicOn
        (meromorphicOn_iteratedDeriv hF j) ih

/-- The literal action of `ℂ[δ][ℂ/H₃]` on a meromorphic source.  Pole coordinates use the
contragredient convention: the basis class `g` acts by translation through `-g`. -/
def tripticDifferentialAction (a b : ℂ) (P : TripticDifferentialGroupAlgebra a b)
    (F : ℂ → ℂ) : ℂ → ℂ :=
  ∑ g ∈ P.coeff.support, ∑ j ∈ (P.coeff g).support,
    fun z => (P.coeff g).coeff j *
      iteratedDeriv j (fun w => F (w - Quotient.out g)) z

/-- Mixed constant carried by the order-zero slice of a literal operator. -/
def tripticDifferentialActionConst (P : TripticDifferentialGroupAlgebra a b) (Cst : ℂ) : ℂ :=
  ∑ g ∈ P.coeff.support, ∑ j ∈ (P.coeff g).support,
    (P.coeff g).coeff j * if j = 0 then Cst else 0

theorem meromorphicOn_tripticDifferentialAction {a b : ℂ} {F : ℂ → ℂ}
    (hF : MeromorphicOn F Set.univ) (P : TripticDifferentialGroupAlgebra a b) :
    MeromorphicOn (tripticDifferentialAction a b P F) Set.univ := by
  classical
  rw [tripticDifferentialAction]
  exact meromorphicOn_finsetSum P.coeff.support _ fun g _ =>
    meromorphicOn_finsetSum (P.coeff g).support _ fun j _ =>
      meromorphicOn_const_mul
        (meromorphicOn_iteratedDeriv (by
          intro z _
          simpa [sub_eq_add_neg] using
            (meromorphicAt_comp_add (f := F) (a := z) (h := -Quotient.out g)).mpr
              (hF (z + -Quotient.out g) (Set.mem_univ _))) j) _

theorem periodicOneGerm_tripticDifferentialAction {a b : ℂ} {F : ℂ → ℂ}
    (hF : MeromorphicOn F Set.univ) (hper : PeriodicOneGerm F)
    (P : TripticDifferentialGroupAlgebra a b) :
    PeriodicOneGerm (tripticDifferentialAction a b P F) := by
  classical
  rw [tripticDifferentialAction]
  exact periodicOneGerm_finsetSum P.coeff.support _ fun g _ =>
    periodicOneGerm_finsetSum (P.coeff g).support _ fun j _ =>
      periodicOneGerm_const_mul
        (periodicOneGerm_iteratedDeriv_of_meromorphicOn (by
          intro z _
          simpa [sub_eq_add_neg] using
            (meromorphicAt_comp_add (f := F) (a := z) (h := -Quotient.out g)).mpr
              (hF (z + -Quotient.out g) (Set.mem_univ _)))
          (by simpa [sub_eq_add_neg] using periodicOneGerm_comp_add hper (-Quotient.out g)) j) _

theorem mixedConstGerm_tripticDifferentialAction {a b Cst : ℂ} {F : ℂ → ℂ}
    (hF : MeromorphicOn F Set.univ) (hmixed : MixedConstGerm F a b Cst)
    (P : TripticDifferentialGroupAlgebra a b) :
    MixedConstGerm (tripticDifferentialAction a b P F) a b
      (tripticDifferentialActionConst P Cst) := by
  classical
  rw [tripticDifferentialAction, tripticDifferentialActionConst]
  exact mixedConstGerm_finsetSum P.coeff.support _ _ fun g _ =>
    mixedConstGerm_finsetSum (P.coeff g).support _ _ fun j _ => by
      refine mixedConstGerm_const_mul ?_ _
      let G : ℂ → ℂ := fun w => F (w - Quotient.out g)
      have hGmero : MeromorphicOn G Set.univ := by
        intro z _
        simpa [G, sub_eq_add_neg] using
          (meromorphicAt_comp_add (f := F) (a := z) (h := -Quotient.out g)).mpr
            (hF (z + -Quotient.out g) (Set.mem_univ _))
      have hGmixed : MixedConstGerm G a b Cst := by
        simpa [G, sub_eq_add_neg] using mixedConstGerm_comp_add' hmixed (-Quotient.out g)
      cases j with
      | zero => simpa [G, iteratedDeriv_zero]
      | succ j =>
          simpa [G, Nat.succ_eq_add_one] using
            mixedConstGerm_iteratedDeriv_succ hGmero hGmixed j

/-- The falling Laurent-jet factor converts normalized order `i-j` into normalized order `i`. -/
theorem laurentJetFactor_mul_normalization {i j : ℕ} (hji : j ≤ i) :
    (∏ t ∈ Finset.range j,
        (((-((i : ℤ) + 1) : ℤ) : ℂ) + (t : ℂ) + 1)) *
        ((-1 : ℂ) ^ (i - j) * ((i - j).factorial : ℂ)) =
      (-1 : ℂ) ^ i * (i.factorial : ℂ) := by
  induction i generalizing j with
  | zero =>
      have hj : j = 0 := Nat.eq_zero_of_le_zero hji
      subst j
      simp
  | succ i ih =>
      cases j with
      | zero => simp
      | succ j =>
          have hji' : j ≤ i := Nat.succ_le_succ_iff.mp hji
          rw [Finset.prod_range_succ']
          have hprod :
              (∏ t ∈ Finset.range j,
                  (((-(((i + 1 : ℕ) : ℤ) + 1) : ℤ) : ℂ) + ((t + 1 : ℕ) : ℂ) + 1)) =
                ∏ t ∈ Finset.range j,
                  (((-((i : ℤ) + 1) : ℤ) : ℂ) + (t : ℂ) + 1) := by
            refine Finset.prod_congr rfl fun t ht => ?_
            push_cast
            ring
          rw [hprod, Nat.succ_sub_succ_eq_sub]
          have hih := ih hji'
          calc
            (∏ t ∈ Finset.range j,
                (((-((i : ℤ) + 1) : ℤ) : ℂ) + (t : ℂ) + 1)) *
                  (((-(((i + 1 : ℕ) : ℤ) + 1) : ℤ) : ℂ) + ((0 : ℕ) : ℂ) + 1) *
                  ((-1 : ℂ) ^ (i - j) * ((i - j).factorial : ℂ)) =
                (-(i + 1 : ℂ)) *
                  ((∏ t ∈ Finset.range j,
                      (((-((i : ℤ) + 1) : ℤ) : ℂ) + (t : ℂ) + 1)) *
                    ((-1 : ℂ) ^ (i - j) * ((i - j).factorial : ℂ))) := by
                      push_cast
                      ring
            _ = (-(i + 1 : ℂ)) * ((-1 : ℂ) ^ i * (i.factorial : ℂ)) := by rw [hih]
            _ = (-1 : ℂ) ^ (i + 1) * ((i + 1).factorial : ℂ) := by
              rw [Nat.factorial_succ, pow_succ]
              push_cast
              ring

theorem finiteOrbitSupport_iteratedDeriv_comp_sub
    {F : ℂ → ℂ} {a b Cst : ℂ} (hF : MeromorphicOn F Set.univ)
    (hper : PeriodicOneGerm F) (hmixed : MixedConstGerm F a b Cst)
    (ha : 0 < a.im) (hindep : IndepPeriods a b)
    (q p : ℂ) (j i : ℕ) :
    FiniteOrbitSupport (iteratedDeriv j (fun w => F (w - q))) b p (-((i : ℤ) + 1)) := by
  let G : ℂ → ℂ := fun w => F (w - q)
  have hGmero : MeromorphicOn G Set.univ := by
    intro z _
    simpa [G, sub_eq_add_neg] using
      (meromorphicAt_comp_add (f := F) (a := z) (h := -q)).mpr
        (hF (z + -q) (Set.mem_univ _))
  have hGper : PeriodicOneGerm G := by
    simpa [G, sub_eq_add_neg] using periodicOneGerm_comp_add hper (-q)
  have hGmixed : MixedConstGerm G a b Cst := by
    simpa [G, sub_eq_add_neg] using mixedConstGerm_comp_add' hmixed (-q)
  have hjmero := meromorphicOn_iteratedDeriv hGmero j
  have hjper := periodicOneGerm_iteratedDeriv_of_meromorphicOn hGmero hGper j
  have hjmixed : MixedConstGerm (iteratedDeriv j G) a b (if j = 0 then Cst else 0) := by
    cases j with
    | zero => simpa [G, iteratedDeriv_zero]
    | succ j =>
        simpa [G, Nat.succ_eq_add_one] using
          mixedConstGerm_iteratedDeriv_succ hGmero hGmixed j
  exact finite_support_orbitalDivisorTerm hjmero hjper hjmixed ha
    (indepSwap_of_indepPeriods hindep) p (by omega)

theorem additiveOrbitalDivisorAt_tripticDifferentialAction
    {F : ℂ → ℂ} {a b Cst : ℂ} (hF : MeromorphicOn F Set.univ)
    (hper : PeriodicOneGerm F) (hmixed : MixedConstGerm F a b Cst)
    (ha : 0 < a.im) (hindep : IndepPeriods a b)
    (P : TripticDifferentialGroupAlgebra a b) (p : ℂ) (i : ℕ) :
    additiveOrbitalDivisorAt (tripticDifferentialAction a b P F) b p (-((i : ℤ) + 1)) =
      ∑ g ∈ P.coeff.support, ∑ j ∈ (P.coeff g).support,
        (P.coeff g).coeff j *
          (∏ t ∈ Finset.range j,
            (((-((i : ℤ) + 1) : ℤ) : ℂ) + (t : ℂ) + 1)) *
          additiveOrbitalDivisorAt F b (p - Quotient.out g)
            (-((i : ℤ) + 1) + (j : ℤ)) := by
  classical
  rw [tripticDifferentialAction]
  rw [additiveOrbitalDivisorAt_finsetSum P.coeff.support _
    (fun g _ => meromorphicOn_finsetSum (P.coeff g).support _ fun j _ =>
      meromorphicOn_const_mul
        (meromorphicOn_iteratedDeriv (by
          intro z _
          simpa [sub_eq_add_neg] using
            (meromorphicAt_comp_add (f := F) (a := z) (h := -Quotient.out g)).mpr
              (hF (z + -Quotient.out g) (Set.mem_univ _))) j) _)
    (fun g _ => finiteOrbitSupport_finsetSum (P.coeff g).support _
      (fun j _ => meromorphicOn_const_mul
        (meromorphicOn_iteratedDeriv (by
          intro z _
          simpa [sub_eq_add_neg] using
            (meromorphicAt_comp_add (f := F) (a := z) (h := -Quotient.out g)).mpr
              (hF (z + -Quotient.out g) (Set.mem_univ _))) j) _)
      (fun j _ => finiteOrbitSupport_const_mul
        (meromorphicOn_iteratedDeriv (by
          intro z _
          simpa [sub_eq_add_neg] using
            (meromorphicAt_comp_add (f := F) (a := z) (h := -Quotient.out g)).mpr
              (hF (z + -Quotient.out g) (Set.mem_univ _))) j)
        (finiteOrbitSupport_iteratedDeriv_comp_sub hF hper hmixed ha hindep
          (Quotient.out g) p j i) _))]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [additiveOrbitalDivisorAt_finsetSum (P.coeff g).support _
    (fun j _ => meromorphicOn_const_mul
      (meromorphicOn_iteratedDeriv (by
        intro z _
        simpa [sub_eq_add_neg] using
          (meromorphicAt_comp_add (f := F) (a := z) (h := -Quotient.out g)).mpr
            (hF (z + -Quotient.out g) (Set.mem_univ _))) j) _)
    (fun j _ => finiteOrbitSupport_const_mul
      (meromorphicOn_iteratedDeriv (by
        intro z _
        simpa [sub_eq_add_neg] using
          (meromorphicAt_comp_add (f := F) (a := z) (h := -Quotient.out g)).mpr
            (hF (z + -Quotient.out g) (Set.mem_univ _))) j)
      (finiteOrbitSupport_iteratedDeriv_comp_sub hF hper hmixed ha hindep
        (Quotient.out g) p j i) _)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [additiveOrbitalDivisorAt_const_mul
    (meromorphicOn_iteratedDeriv (by
      intro z _
      simpa [sub_eq_add_neg] using
        (meromorphicAt_comp_add (f := F) (a := z) (h := -Quotient.out g)).mpr
          (hF (z + -Quotient.out g) (Set.mem_univ _))) j),
    additiveOrbitalDivisorAt_iteratedDeriv (by
      intro z _
      simpa [sub_eq_add_neg] using
        (meromorphicAt_comp_add (f := F) (a := z) (h := -Quotient.out g)).mpr
          (hF (z + -Quotient.out g) (Set.mem_univ _)))]
  have hfun : (fun w => F (w - Quotient.out g)) =
      fun w => F (w + -Quotient.out g) := by
    funext w
    rw [sub_eq_add_neg]
  rw [hfun, GaloisForLFunctions.additiveOrbitalDivisorAt_comp_add]
  ring

/-- Coefficients of a polynomial product, indexed by the finite support of the left factor. -/
theorem Polynomial.coeff_mul_eq_sum_support (L Q : Polynomial ℂ) (i : ℕ) :
    (L * Q).coeff i =
      ∑ j ∈ L.support, if j ≤ i then L.coeff j * Q.coeff (i - j) else 0 := by
  classical
  conv_lhs => rw [← L.sum_monomial_eq]
  rw [Polynomial.sum, Finset.sum_mul, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun j hj => ?_
  by_cases hji : j ≤ i
  · rw [if_pos hji]
    have hidx : i - j + j = i := Nat.sub_add_cancel hji
    conv_lhs => rw [← hidx]
    rw [Polynomial.coeff_monomial_mul]
  · rw [if_neg hji, Polynomial.coeff_mul]
    exact Finset.sum_eq_zero fun x hx => by
      have hsum : x.1 + x.2 = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      have hne : x.1 ≠ j := by
        intro heq
        have : j + x.2 = i := by simpa [heq] using hsum
        omega
      simp [Polynomial.coeff_monomial, Ne.symm hne]

/-- Convolution in an additive group algebra, with the unique right index solved explicitly. -/
theorem AddMonoidAlgebra.coeff_mul_eq_sum_support
    {R G : Type*} [Semiring R] [AddCommGroup G] [DecidableEq G]
    (P D : AddMonoidAlgebra R G) (q : G) :
    (P * D).coeff q = ∑ g ∈ P.coeff.support, P.coeff g * D.coeff (q - g) := by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  change (∑ g ∈ P.coeff.support,
      ∑ h ∈ D.coeff.support, if g + h = q then P.coeff g * D.coeff h else 0) = _
  refine Finset.sum_congr rfl fun g hg => ?_
  by_cases hmem : q - g ∈ D.coeff.support
  · rw [Finset.sum_eq_single_of_mem (q - g) hmem (by
      intro h hh hne
      rw [if_neg (fun heq => hne (by
        apply add_left_cancel (a := g)
        simpa [add_assoc] using heq))])]
    rw [if_pos (by simp)]
  · have hz : D.coeff (q - g) = 0 := by
      simpa [Finsupp.mem_support_iff] using hmem
    rw [hz, mul_zero]
    exact Finset.sum_eq_zero fun h hh => by
      rw [if_neg (fun heq => hmem (by
        have : h = q - g := by
          apply add_left_cancel (a := g)
          simpa [add_assoc] using heq
        simpa [this] using hh))]

theorem additiveOrbitalDivisorAt_tripticDifferentialAction_eq_mul_coeff
    {F : ℂ → ℂ} {a b Cst : ℂ} (hF : MeromorphicOn F Set.univ)
    (hper : PeriodicOneGerm F) (hmixed : MixedConstGerm F a b Cst)
    (ha : 0 < a.im) (hb : 0 < b.im) (hindep : IndepPeriods a b)
    (hindepA : LinearIndependent ℝ ![(1 : ℂ), a])
    (hindepB : LinearIndependent ℝ ![(1 : ℂ), b])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b))
    {D : TripticDifferentialGroupAlgebra a b}
    (hD : DifferentiallyAlgebraic
      (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ))
    (P : TripticDifferentialGroupAlgebra a b) (p : ℂ) (i : ℕ) :
    additiveOrbitalDivisorAt (tripticDifferentialAction a b P F) b p (-((i : ℤ) + 1)) =
      (-1 : ℂ) ^ i * (i.factorial : ℂ) *
        ((P * D).coeff (QuotientAddGroup.mk p)).coeff i := by
  classical
  rw [additiveOrbitalDivisorAt_tripticDifferentialAction hF hper hmixed ha hindep]
  rw [AddMonoidAlgebra.coeff_mul_eq_sum_support, Polynomial.finsetSum_coeff,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [Polynomial.coeff_mul_eq_sum_support, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  by_cases hji : j ≤ i
  · rw [if_pos hji]
    have hidx : -((i : ℤ) + 1) + (j : ℤ) = -(((i - j : ℕ) : ℤ) + 1) := by
      omega
    rw [hidx, additiveOrbitalDivisorAt_eq_tripticOperatorCarrier_of_normalForm
      hF hper hmixed ha hb hindep hindepA hindepB hperiods hD,
      additiveOrbitalDivisorAt_tripticOperatorCarrier ha hb hindep]
    have hmk : (QuotientAddGroup.mk (p - Quotient.out g) :
        ℂ ⧸ tripticPeriodGroup a b) = QuotientAddGroup.mk p - g := by
      change (QuotientAddGroup.mk p : ℂ ⧸ tripticPeriodGroup a b) -
          (QuotientAddGroup.mk (Quotient.out g) : ℂ ⧸ tripticPeriodGroup a b) =
        (QuotientAddGroup.mk p : ℂ ⧸ tripticPeriodGroup a b) - g
      rw [QuotientAddGroup.out_eq']
    rw [hmk]
    have hscale := laurentJetFactor_mul_normalization hji
    calc
      ((P.coeff g).coeff j *
          (∏ t ∈ Finset.range j,
            (((-((i : ℤ) + 1) : ℤ) : ℂ) + (t : ℂ) + 1))) *
          (((-1 : ℂ) ^ (i - j) * ((i - j).factorial : ℂ)) *
            (D.coeff (QuotientAddGroup.mk p - g)).coeff (i - j)) =
        (P.coeff g).coeff j *
          ((∏ t ∈ Finset.range j,
            (((-((i : ℤ) + 1) : ℤ) : ℂ) + (t : ℂ) + 1)) *
            ((-1 : ℂ) ^ (i - j) * ((i - j).factorial : ℂ))) *
          (D.coeff (QuotientAddGroup.mk p - g)).coeff (i - j) := by ring
      _ = (P.coeff g).coeff j * ((-1 : ℂ) ^ i * (i.factorial : ℂ)) *
          (D.coeff (QuotientAddGroup.mk p - g)).coeff (i - j) := by rw [hscale]
      _ = (-1 : ℂ) ^ i * (i.factorial : ℂ) *
          ((P.coeff g).coeff j *
            (D.coeff (QuotientAddGroup.mk p - g)).coeff (i - j)) := by ring
  · rw [if_neg hji]
    have hij : i < j := Nat.lt_of_not_ge hji
    rw [prod_range_eq_zero_of_mem (j := j) (ℓ := -((i : ℤ) + 1))
      (by exact_mod_cast (by omega : -(j : ℤ) ≤ -((i : ℤ) + 1))) (by omega)]
    simp

/-- **Exact mixed differential-translation annihilator.**  For a source with intrinsic divisor
`D`, an actual finite differential-translation operator `P` has DA output exactly when the literal
group-algebra product `P * D` vanishes. -/
theorem differentiallyAlgebraic_tripticDifferentialAction_iff_mul_eq_zero
    {F : ℂ → ℂ} {a b Cst : ℂ} (hF : MeromorphicOn F Set.univ)
    (hper : PeriodicOneGerm F) (hmixed : MixedConstGerm F a b Cst)
    (ha : 0 < a.im) (hb : 0 < b.im) (hindep : IndepPeriods a b)
    (hindepA : LinearIndependent ℝ ![(1 : ℂ), a])
    (hindepB : LinearIndependent ℝ ![(1 : ℂ), b])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b))
    {D : TripticDifferentialGroupAlgebra a b}
    (hD : DifferentiallyAlgebraic
      (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ))
    (P : TripticDifferentialGroupAlgebra a b) :
    DifferentiallyAlgebraic
        (toMeromorphicNFOn (tripticDifferentialAction a b P F) Set.univ) ↔
      P * D = 0 := by
  rw [differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero
    (meromorphicOn_tripticDifferentialAction hF P)
    (periodicOneGerm_tripticDifferentialAction hF hper P)
    (mixedConstGerm_tripticDifferentialAction hF hmixed P)
    ha hb hindep hindepA hindepB hperiods]
  constructor
  · intro hzero
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    apply Polynomial.ext
    intro i
    have hz := hzero (Quotient.out g) (-((i : ℤ) + 1)) (by omega)
    rw [additiveOrbitalDivisorAt_tripticDifferentialAction_eq_mul_coeff
      hF hper hmixed ha hb hindep hindepA hindepB hperiods hD P (Quotient.out g) i,
      QuotientAddGroup.out_eq'] at hz
    have hscale : ((-1 : ℂ) ^ i * (i.factorial : ℂ)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero i (by norm_num)) (by exact_mod_cast i.factorial_ne_zero)
    exact (mul_eq_zero.mp hz).resolve_left hscale
  · intro hmul p ell hell
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, ell = -((i : ℤ) + 1) :=
      ⟨(-ell - 1).toNat, by omega⟩
    rw [additiveOrbitalDivisorAt_tripticDifferentialAction_eq_mul_coeff
      hF hper hmixed ha hb hindep hindepA hindepB hperiods hD P p i, hmul]
    simp

/-! ### Complete finite-family operator matroid -/

/-- Distinguished quotient class represented by the untranslated meromorphic gamma source. -/
def tripticBaseSourceClass (a b : ℂ) : ℂ ⧸ tripticPeriodGroup a b :=
  QuotientAddGroup.mk (-(gammaPresentationShift b))

/-- Non-base coordinates in the common finite support of a family of triptic operator rows. -/
abbrev TripticNonbaseRowIndex
    {a b : ℂ} {ρ : Type} [Fintype ρ]
    (Q : ρ → (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ) :=
  {g : FinsuppOperatorRowIndex Q // g.1 ≠ tripticBaseSourceClass a b}

/-- Translation parameters for every non-base quotient coordinate. -/
def tripticPreferredShifts
    {a b : ℂ} {ρ : Type} [Fintype ρ]
    (Q : ρ → (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ) :
    TripticNonbaseRowIndex Q → ℂ :=
  fun g => -(gammaPresentationShift b) - Quotient.out g.1.1

/-- Finite polynomial rows on the preferred packet: `none` is the base-source class and every
other common-support class is represented by its quotient lift. -/
def tripticPreferredOperatorRows
    {a b : ℂ} {ρ : Type} [Fintype ρ]
    (Q : ρ → (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ) :
    ρ → Option (TripticNonbaseRowIndex Q) → Polynomial ℂ :=
  fun r g => g.elim (Q r (tripticBaseSourceClass a b)) (fun h => Q r h.1.1)

theorem thetaTranslationNonresonant_tripticPreferredShifts
    {a b : ℂ} {ρ : Type} [Fintype ρ]
    (Q : ρ → (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ)
    (g : TripticNonbaseRowIndex Q) :
    ThetaTranslationNonresonant b a (tripticPreferredShifts Q g) := by
  rw [tripticPreferredShifts]
  apply thetaTranslationNonresonant_of_not_sameClass_neg
  intro hsame
  apply g.2
  unfold tripticBaseSourceClass
  have hmk := (sameClass_iff_mk_eq_mk a b
    (Quotient.out g.1.1) (-(gammaPresentationShift b))).mp hsame
  rwa [QuotientAddGroup.out_eq'] at hmk

theorem thetaTranslationNonresonant_sub_tripticPreferredShifts
    {a b : ℂ} {ρ : Type} [Fintype ρ]
    (Q : ρ → (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ)
    (g h : TripticNonbaseRowIndex Q) (hgh : g ≠ h) :
    ThetaTranslationNonresonant b a
      (tripticPreferredShifts Q h - tripticPreferredShifts Q g) := by
  have hclass : ¬ SameClass a b (Quotient.out g.1.1) (Quotient.out h.1.1) := by
    intro hs
    apply hgh
    apply Subtype.ext
    apply Subtype.ext
    have hmk := (sameClass_iff_mk_eq_mk a b
      (Quotient.out g.1.1) (Quotient.out h.1.1)).mp hs
    simpa only [QuotientAddGroup.out_eq'] using hmk
  have hnr := thetaTranslationNonresonant_of_not_sameClass hclass
  have hshift : tripticPreferredShifts Q h - tripticPreferredShifts Q g =
      Quotient.out g.1.1 - Quotient.out h.1.1 := by
    simp only [tripticPreferredShifts]
    ring
  rwa [hshift]

/-- Preferred base/non-base coordinates preserve and reflect every polynomial-row dependence in
the original finitely supported quotient rows. -/
theorem linearIndependent_tripticPreferredOperatorRows_iff
    {a b : ℂ} {ρ : Type} [Fintype ρ] [DecidableEq ρ]
    (Q : ρ → (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ) :
    LinearIndependent (Polynomial ℂ) (tripticPreferredOperatorRows Q) ↔
      LinearIndependent (Polynomial ℂ) Q := by
  classical
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h A hrel r
    apply h A
    funext g
    cases g with
    | none =>
        have hg := congrArg
          (fun f : (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ =>
            f (tripticBaseSourceClass a b)) hrel
        simpa [tripticPreferredOperatorRows] using hg
    | some g =>
        have hg := congrArg
          (fun f : (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ => f g.1.1) hrel
        simpa [tripticPreferredOperatorRows] using hg
  · intro h A hrel r
    apply h A
    apply Finsupp.ext
    intro g
    by_cases hbase : g = tripticBaseSourceClass a b
    · subst g
      have hg := congrArg
        (fun f : Option (TripticNonbaseRowIndex Q) → Polynomial ℂ => f none) hrel
      simpa [tripticPreferredOperatorRows] using hg
    · by_cases hzero : ∀ j, Q j g = 0
      · simp [hzero]
      · push Not at hzero
        obtain ⟨j, hj⟩ := hzero
        let gs : FinsuppOperatorRowIndex Q :=
          ⟨g, mem_finsuppOperatorRowSupport_of_ne Q hj⟩
        let gn : TripticNonbaseRowIndex Q := ⟨gs, hbase⟩
        have hg := congrArg
          (fun f : Option (TripticNonbaseRowIndex Q) → Polynomial ℂ => f (some gn)) hrel
        simpa [tripticPreferredOperatorRows, gn, gs] using hg

/-- The same dependence equivalence on every subfamily, retaining the common coordinate packet of
the full family. -/
theorem linearIndependent_restrict_tripticPreferredOperatorRows_iff
    {a b : ℂ} {ρ : Type} [Fintype ρ] [DecidableEq ρ]
    (Q : ρ → (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ) (I : Set ρ) :
    LinearIndependent (Polynomial ℂ)
        (fun i : I => tripticPreferredOperatorRows Q i) ↔
      LinearIndependent (Polynomial ℂ) (fun i : I => Q i) := by
  classical
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h A hrel r
    apply h A
    funext g
    cases g with
    | none =>
        have hg := congrArg
          (fun f : (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ =>
            f (tripticBaseSourceClass a b)) hrel
        simpa [tripticPreferredOperatorRows] using hg
    | some g =>
        have hg := congrArg
          (fun f : (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ => f g.1.1) hrel
        simpa [tripticPreferredOperatorRows] using hg
  · intro h A hrel r
    apply h A
    apply Finsupp.ext
    intro g
    by_cases hbase : g = tripticBaseSourceClass a b
    · subst g
      have hg := congrArg
        (fun f : Option (TripticNonbaseRowIndex Q) → Polynomial ℂ => f none) hrel
      simpa [tripticPreferredOperatorRows] using hg
    · by_cases hzero : ∀ j : I, Q j g = 0
      · simp [hzero]
      · push Not at hzero
        obtain ⟨j, hj⟩ := hzero
        let gs : FinsuppOperatorRowIndex Q :=
          ⟨g, mem_finsuppOperatorRowSupport_of_ne Q hj⟩
        let gn : TripticNonbaseRowIndex Q := ⟨gs, hbase⟩
        have hg := congrArg
          (fun f : Option (TripticNonbaseRowIndex Q) → Polynomial ℂ => f (some gn)) hrel
        simpa [tripticPreferredOperatorRows, gn, gs] using hg

/-- Localized `ℂ(δ)` matroid of literal finitely supported quotient rows. -/
def tripticDifferentialGroupAlgebraRowMatroid
    {a b : ℂ} {ρ : Type} [Fintype ρ]
    (Q : ρ → (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ) : Matroid ρ :=
  differentialOperatorRowMatroid (C := ℂ) (ι := ρ)
    (κ := Option (TripticNonbaseRowIndex Q)) (tripticPreferredOperatorRows Q)

@[simp] theorem tripticDifferentialGroupAlgebraRowMatroid_ground
    {a b : ℂ} {ρ : Type} [Fintype ρ]
    (Q : ρ → (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ) :
    (tripticDifferentialGroupAlgebraRowMatroid Q).E = Set.univ := by
  simp [tripticDifferentialGroupAlgebraRowMatroid]

theorem tripticDifferentialGroupAlgebraRowMatroid_indep_iff
    {a b : ℂ} {ρ : Type} [Fintype ρ] [DecidableEq ρ]
    (Q : ρ → (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ) (I : Set ρ) :
    (tripticDifferentialGroupAlgebraRowMatroid Q).Indep I ↔
      LinearIndependent (Polynomial ℂ) (fun i : I => Q i) := by
  rw [tripticDifferentialGroupAlgebraRowMatroid,
    differentialOperatorRowMatroid_indep_iff,
    linearIndependent_restrict_tripticPreferredOperatorRows_iff]

/-- **Complete nonlinear triptic operator-row matroid.**  Every finite family of polynomial rows
on the literal quotient `ℂ/H₃` acts on a preferred finite packet of elliptic-gamma translates, and
its genuine differential matroid over `ℂ(z)` is exactly its localized `ℂ(δ)` row matroid. -/
theorem tripticPreferredOperatorRows_differentialMatroid
    {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b))
    {ρ : Type} [Fintype ρ] [DecidableEq ρ]
    (Q : ρ → (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (differentialOperatorRowApply (tripticPreferredOperatorRows Q)
          (ellipticGammaTranslateFamily
            (optionShift (tripticPreferredShifts Q)) a b ha hb)) =
      tripticDifferentialGroupAlgebraRowMatroid Q := by
  classical
  let x := ellipticGammaTranslateFamily
    (optionShift (tripticPreferredShifts Q)) a b ha hb
  have hxC : DifferentialIndependent ℂ x :=
    differentialIndependent_ellipticGammaTranslateFamily_option ha hb hperiods
      (tripticPreferredShifts Q)
      (thetaTranslationNonresonant_tripticPreferredShifts Q)
      (thetaTranslationNonresonant_sub_tripticPreferredShifts Q)
  have hxR : DifferentialIndependent meromorphicRationalCoordinateField x :=
    (differentialIndependent_meromorphicRationalCoordinateField_iff x).mpr hxC
  simpa [tripticDifferentialGroupAlgebraRowMatroid] using
    (differentialFamilyMatroid_differentialOperatorRows_rationalBase_eq
      (tripticPreferredOperatorRows Q) x hxR)

/-- Numerical `ℂ(δ)`-rank form of the complete finite-family theorem. -/
theorem tripticPreferredOperatorRows_differentialRank
    {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b))
    {ρ : Type} [Fintype ρ] [DecidableEq ρ]
    (Q : ρ → (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ) (I : Finset ρ) :
    (differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (differentialOperatorRowApply (tripticPreferredOperatorRows Q)
          (ellipticGammaTranslateFamily
            (optionShift (tripticPreferredShifts Q)) a b ha hb))).eRk (↑I : Set ρ) =
      (Module.finrank (FractionRing (Polynomial ℂ))
        (Submodule.span (FractionRing (Polynomial ℂ))
          ((fun r => localizeOperatorRow (tripticPreferredOperatorRows Q r)) ''
            (↑I : Set ρ))) : ℕ∞) := by
  rw [tripticPreferredOperatorRows_differentialMatroid ha hb hperiods Q]
  rw [tripticDifferentialGroupAlgebraRowMatroid]
  exact linearFamilyMatroid_eRk_finset
    (fun r => localizeOperatorRow (tripticPreferredOperatorRows Q r)) I

/-! ### Closed concrete capstone -/

/-- Full theorem package at fixed periods.  Arithmetic genericity is absent from the fields: it is
discharged once when the closed package is constructed. -/
structure TripticMixedConstraintNormalFormPackage (a b : ℂ) : Prop where
  upperHalfPlaneA : 0 < a.im
  upperHalfPlaneB : 0 < b.im
  uniqueNormalForm : ∀ (F : ℂ → ℂ) (Cst : ℂ),
    MeromorphicOn F Set.univ → PeriodicOneGerm F → MixedConstGerm F a b Cst →
    ∃! D : TripticDifferentialGroupAlgebra a b,
      DifferentiallyAlgebraic
        (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ)
  intrinsicDivisor : ∀ (F : ℂ → ℂ) (Cst : ℂ) (D : TripticDifferentialGroupAlgebra a b),
    MeromorphicOn F Set.univ → PeriodicOneGerm F → MixedConstGerm F a b Cst →
    DifferentiallyAlgebraic
      (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ) →
    ∀ (p : ℂ) (i : ℕ),
      additiveOrbitalDivisorAt F b p (-((i : ℤ) + 1)) =
        (-1 : ℂ) ^ i * (i.factorial : ℂ) *
          (D.coeff (QuotientAddGroup.mk p)).coeff i
  daKernel : ∀ (F : ℂ → ℂ) (Cst : ℂ) (D : TripticDifferentialGroupAlgebra a b),
    MeromorphicOn F Set.univ → PeriodicOneGerm F → MixedConstGerm F a b Cst →
    DifferentiallyAlgebraic
      (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ) →
    (DifferentiallyAlgebraic (toMeromorphicNFOn F Set.univ) ↔ D = 0)
  regularModule : ∀ D : TripticDifferentialGroupAlgebra a b,
    DifferentiallyAlgebraic
      (toMeromorphicNFOn (tripticOperatorCarrier a b D) Set.univ) ↔ D = 0
  exactAnnihilator : ∀ (F : ℂ → ℂ) (Cst : ℂ) (D P : TripticDifferentialGroupAlgebra a b),
    MeromorphicOn F Set.univ → PeriodicOneGerm F → MixedConstGerm F a b Cst →
    DifferentiallyAlgebraic
      (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ) →
    (DifferentiallyAlgebraic
        (toMeromorphicNFOn (tripticDifferentialAction a b P F) Set.univ) ↔ P * D = 0)
  exactSpectrum : ∀ (F : ℂ → ℂ) (Cst : ℂ) (D : TripticDifferentialGroupAlgebra a b),
    MeromorphicOn F Set.univ → PeriodicOneGerm F → MixedConstGerm F a b Cst →
    DifferentiallyAlgebraic
      (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ) →
    ∀ h : ℂ,
      DifferentiallyAlgebraic (toMeromorphicNFOn (HTGeometry.shiftDiffFun h F) Set.univ) ↔
        (QuotientAddGroup.mk h : ℂ ⧸ tripticPeriodGroup a b) ∈
          finiteSupportTranslationStabilizer D.coeff
  finiteSpectrum : ∀ D : TripticDifferentialGroupAlgebra a b, D ≠ 0 →
    Finite (finiteSupportTranslationStabilizer D.coeff)
  realizesEveryFiniteSpectrum : ∀ K : AddSubgroup (ℂ ⧸ tripticPeriodGroup a b),
    ∀ _ : Finite K,
    ∃ (F : ℂ → ℂ) (D : TripticDifferentialGroupAlgebra a b),
      D ≠ 0 ∧ MeromorphicOn F Set.univ ∧ PeriodicOneGerm F ∧
      MixedConstGerm F a b (tripticOperatorConst D) ∧
      DifferentiallyAlgebraic
        (toMeromorphicNFOn (fun z => F z - tripticOperatorCarrier a b D z) Set.univ) ∧
      ∀ h : ℂ, DifferentiallyAlgebraic
          (toMeromorphicNFOn (HTGeometry.shiftDiffFun h F) Set.univ) ↔
        (QuotientAddGroup.mk h : ℂ ⧸ tripticPeriodGroup a b) ∈ K
  completeFamilyMatroid : ∀ {ρ : Type} (_ : Fintype ρ) (_ : DecidableEq ρ)
    (Q : ρ → (ℂ ⧸ tripticPeriodGroup a b) →₀ Polynomial ℂ),
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (differentialOperatorRowApply (tripticPreferredOperatorRows Q)
          (ellipticGammaTranslateFamily
            (optionShift (tripticPreferredShifts Q)) a b
              upperHalfPlaneA upperHalfPlaneB)) =
      tripticDifferentialGroupAlgebraRowMatroid Q

/-- **Unconditional closed triptic mixed-constraint normal form.**  The prime-log period pair
discharges every arithmetic and upper-half-plane condition internally. -/
theorem tripticMixedConstraintNormalForm_unconditional :
    TripticMixedConstraintNormalFormPackage
      (reflectionPairPeriods true) (reflectionPairPeriods false) := by
  let a := reflectionPairPeriods true
  let b := reflectionPairPeriods false
  have ha : 0 < a.im := reflectionPairPeriods_im_pos true
  have hb : 0 < b.im := reflectionPairPeriods_im_pos false
  have hindep : IndepPeriods a b :=
    indepPeriods_of_periodsIntegrallyIndependent reflectionPairPeriods
      reflectionPairPeriods_integrallyIndependent (i := false) (j := true) Bool.false_ne_true
  have hindepA : LinearIndependent ℝ ![(1 : ℂ), a] := linearIndependent_one_of_im_pos ha
  have hindepB : LinearIndependent ℝ ![(1 : ℂ), b] := linearIndependent_one_of_im_pos hb
  have hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b) :=
    linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent
      reflectionPairPeriods reflectionPairPeriods_integrallyIndependent (by decide : true ≠ false)
  change TripticMixedConstraintNormalFormPackage a b
  refine {
    upperHalfPlaneA := ha
    upperHalfPlaneB := hb
    uniqueNormalForm := ?_
    intrinsicDivisor := ?_
    daKernel := ?_
    regularModule := ?_
    exactAnnihilator := ?_
    exactSpectrum := ?_
    finiteSpectrum := ?_
    realizesEveryFiniteSpectrum := ?_
    completeFamilyMatroid := ?_ }
  · intro F Cst hF hper hmixed
    exact existsUnique_tripticOperator_normalForm hF hper hmixed ha hb hindep
      hindepA hindepB hperiods
  · intro F Cst D hF hper hmixed hD p i
    rw [additiveOrbitalDivisorAt_eq_tripticOperatorCarrier_of_normalForm
      hF hper hmixed ha hb hindep hindepA hindepB hperiods hD,
      additiveOrbitalDivisorAt_tripticOperatorCarrier ha hb hindep]
  · intro F Cst D hF hper hmixed hD
    exact differentiallyAlgebraic_iff_tripticNormalFormOperator_eq_zero
      hF hper hmixed ha hb hindep hindepA hindepB hperiods hD
  · intro D
    exact tripticOperatorCarrier_differentiallyAlgebraic_iff
      ha hb hindep hindepA hindepB hperiods D
  · intro F Cst D P hF hper hmixed hD
    exact differentiallyAlgebraic_tripticDifferentialAction_iff_mul_eq_zero
      hF hper hmixed ha hb hindep hindepA hindepB hperiods hD P
  · intro F Cst D hF hper hmixed hD h
    exact differentiallyAlgebraic_shiftDiff_iff_operator_stabilizer
      hF hper hmixed ha hb hindep hindepA hindepB hperiods hD h
  · exact finite_tripticOperator_stabilizer_of_ne_zero
  · intro K hK
    letI := hK
    exact exists_tripticCarrier_with_exact_finite_spectrum
      ha hb hindep hindepA hindepB hperiods K
  · intro ρ hρ hdρ Q
    letI := hρ
    letI := hdρ
    simpa using tripticPreferredOperatorRows_differentialMatroid ha hb hperiods Q

end
end GaloisForLFunctions.HTGeometry
