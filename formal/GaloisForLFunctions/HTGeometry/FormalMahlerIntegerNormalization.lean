import GaloisForLFunctions.HTGeometry.DifferentialAdjoinFiniteTrdeg
import GaloisForLFunctions.HTGeometry.FormalMahlerDescent
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.RingTheory.LaurentSeries

/-!
# Formal Mahler integer normalization

A nonzero complex algebraic differential relation on a formal power series can be normalized to
a nonzero relation with integer coefficients, without assuming that the series coefficients lie in
a prescribed number field. The proof moves the relation into the Laurent-series differential
field, adjoins the finitely many polynomial coefficient-functions, descends through their finite
transcendence degree to `ℚ`, clears denominators, and returns to the power-series carrier.
-/

open PowerSeries MvPolynomial
open scoped Differential

namespace GaloisForLFunctions

noncomputable section

abbrev FormalLaurent := LaurentSeries ℂ

local instance formalLaurentRatAlgebra : Algebra ℚ FormalLaurent :=
  RingHom.toAlgebra ((algebraMap ℂ FormalLaurent).comp (algebraMap ℚ ℂ))

local instance formalLaurentRatComplexTower :
    IsScalarTower ℚ ℂ FormalLaurent :=
  ⟨fun q c f => by
    ext n
    simp [Algebra.smul_def]
    ring⟩

@[reducible] def rationalZeroDifferential : Differential ℚ := ⟨0⟩

@[reducible] def formalLaurentDifferential : Differential FormalLaurent := by
  letI : Algebra ℤ (PowerSeries ℂ) := Ring.toIntAlgebra _
  letI : Algebra ℤ FormalLaurent := Ring.toIntAlgebra _
  letI : IsScalarTower ℤ (PowerSeries ℂ) FormalLaurent :=
    .of_algebraMap_eq fun z => by ext n; simp
  let D : Derivation ℤ (PowerSeries ℂ) FormalLaurent :=
    ((Algebra.linearMap (PowerSeries ℂ) FormalLaurent).compDer
      ((PowerSeries.derivative ℂ).restrictScalars ℤ))
  exact ⟨fractionRingDerivation D⟩

local instance : Differential FormalLaurent := formalLaurentDifferential

theorem formalLaurentDifferential_algebraMap (A : PowerSeries ℂ) :
    letI := formalLaurentDifferential
    (algebraMap (PowerSeries ℂ) FormalLaurent A)′ =
      algebraMap (PowerSeries ℂ) FormalLaurent (d⁄dX ℂ A) := by
  letI : Algebra ℤ (PowerSeries ℂ) := Ring.toIntAlgebra _
  letI : Algebra ℤ FormalLaurent := Ring.toIntAlgebra _
  letI : IsScalarTower ℤ (PowerSeries ℂ) FormalLaurent :=
    .of_algebraMap_eq fun z => by ext n; simp
  let D : Derivation ℤ (PowerSeries ℂ) FormalLaurent :=
    ((Algebra.linearMap (PowerSeries ℂ) FormalLaurent).compDer
      ((PowerSeries.derivative ℂ).restrictScalars ℤ))
  letI := formalLaurentDifferential
  change fractionRingDerivation D
      (algebraMap (PowerSeries ℂ) FormalLaurent A) = _
  rw [fractionRingDerivation_algebraMap]
  rfl

theorem formalLaurentDifferentialAlgebraRat :
    letI := rationalZeroDifferential
    letI := formalLaurentDifferential
    DifferentialAlgebra ℚ FormalLaurent := by
  letI := rationalZeroDifferential
  letI := formalLaurentDifferential
  constructor
  intro q
  have hq : algebraMap ℚ FormalLaurent q =
      algebraMap (PowerSeries ℂ) FormalLaurent (PowerSeries.C (q : ℂ)) := by
    ext n
    simp
  rw [hq, formalLaurentDifferential_algebraMap]
  have hqderiv : q′ = (0 : ℚ) := by rfl
  rw [hqderiv, PowerSeries.derivative_C]
  simp

theorem differentialJet_formalLaurent_algebraMap (n : ℕ) (A : PowerSeries ℂ) :
    letI := formalLaurentDifferential
    differentialJet n (algebraMap (PowerSeries ℂ) FormalLaurent A) =
      algebraMap (PowerSeries ℂ) FormalLaurent ((⇑(d⁄dX ℂ))^[n] A) := by
  letI := formalLaurentDifferential
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 = n + 1 by rfl, differentialJet_succ, ih,
        formalLaurentDifferential_algebraMap, Function.iterate_succ_apply']

theorem iterate_powerSeriesDerivative_coe (n : ℕ) (p : Polynomial ℂ) :
    ((⇑(d⁄dX ℂ))^[n] (p : PowerSeries ℂ)) =
      ((Polynomial.derivative^[n] p) : PowerSeries ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        PowerSeries.derivative_coe]

theorem differentialJet_formalLaurent_polynomial_eq_zero
    (p : Polynomial ℂ) {n : ℕ} (h : p.natDegree < n) :
    letI := formalLaurentDifferential
    differentialJet n
        (algebraMap (PowerSeries ℂ) FormalLaurent (p : PowerSeries ℂ)) = 0 := by
  letI := formalLaurentDifferential
  rw [differentialJet_formalLaurent_algebraMap,
    iterate_powerSeriesDerivative_coe, Polynomial.iterate_derivative_eq_zero h]
  simp

theorem finite_range_differentialJet_formalLaurent_polynomial (p : Polynomial ℂ) :
    letI := formalLaurentDifferential
    (Set.range fun n => differentialJet n
      (algebraMap (PowerSeries ℂ) FormalLaurent (p : PowerSeries ℂ))).Finite := by
  letI := formalLaurentDifferential
  let f : ℕ → FormalLaurent := fun n => differentialJet n
    (algebraMap (PowerSeries ℂ) FormalLaurent (p : PowerSeries ℂ))
  let s : Set FormalLaurent := f '' (Finset.range (p.natDegree + 2) : Set ℕ)
  apply ((Finset.range (p.natDegree + 2)).finite_toSet.image f).subset
  rintro y ⟨n, rfl⟩
  change f n ∈ s
  by_cases hn : n < p.natDegree + 2
  · exact ⟨n, Finset.mem_range.mpr hn, rfl⟩
  · have hnzero : f n = 0 := by
      apply differentialJet_formalLaurent_polynomial_eq_zero (n := n)
      omega
    have hbase : f (p.natDegree + 1) = 0 := by
      apply differentialJet_formalLaurent_polynomial_eq_zero (n := p.natDegree + 1)
      omega
    exact ⟨p.natDegree + 1, Finset.mem_range.mpr (by omega), hbase.trans hnzero.symm⟩

def formalPointRow (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) :=
  MvPolynomial.optionEquivRight ℂ (Fin (n + 1))
    (MvPolynomial.renameEquiv ℂ (_root_.finSuccEquiv (n + 1)) P)

theorem formalPointRow_ne_zero {n : ℕ}
    {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0) :
    formalPointRow n P ≠ 0 := by
  exact (MvPolynomial.optionEquivRight ℂ (Fin (n + 1))).injective.ne
    ((MvPolynomial.renameEquiv ℂ (_root_.finSuccEquiv (n + 1))).injective.ne hP)

theorem aeval_map_formalPointRow (n : ℕ) (F : PowerSeries ℂ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    aeval (fun j : Fin (n + 1) => (⇑(d⁄dX ℂ))^[(j : ℕ)] F)
        (MvPolynomial.map (algebraMap (Polynomial ℂ) (PowerSeries ℂ))
          (formalPointRow n P)) =
      aeval (formalJets n F) P := by
  let ψ : MvPolynomial (Fin (n + 2)) ℂ →+*
      MvPolynomial (Fin (n + 1)) (PowerSeries ℂ) :=
    (MvPolynomial.map (algebraMap (Polynomial ℂ) (PowerSeries ℂ))).comp
      ((MvPolynomial.optionEquivRight ℂ (Fin (n + 1))).toRingEquiv.toRingHom.comp
        (MvPolynomial.renameEquiv ℂ
          (_root_.finSuccEquiv (n + 1))).toRingEquiv.toRingHom)
  let lhs : MvPolynomial (Fin (n + 2)) ℂ →+* PowerSeries ℂ :=
    (aeval (formalJets n F)).toRingHom
  let rhs : MvPolynomial (Fin (n + 2)) ℂ →+* PowerSeries ℂ :=
    (aeval (fun j : Fin (n + 1) => (⇑(d⁄dX ℂ))^[(j : ℕ)] F)).toRingHom.comp ψ
  change (aeval (fun j : Fin (n + 1) => (⇑(d⁄dX ℂ))^[(j : ℕ)] F)).toRingHom
    (ψ P) = lhs P
  change rhs P = lhs P
  have hhom : rhs = lhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, rhs, ψ]
      exact Polynomial.coe_C r
    · intro i
      induction i using Fin.cases with
      | zero =>
          simp [lhs, rhs, ψ, formalJets, _root_.finSuccEquiv,
            _root_.finSuccEquiv']
          exact Polynomial.coe_X
      | succ j =>
          have hmap : (_root_.finSuccEquiv (n + 1)) j.succ = some j :=
            _root_.finSuccEquiv_succ j
          simp [lhs, rhs, ψ, formalJets, hmap]
  rw [hhom]

def formalPointRowEmbedding : Polynomial ℂ →+* FormalLaurent :=
  (algebraMap (PowerSeries ℂ) FormalLaurent).comp
    (algebraMap (Polynomial ℂ) (PowerSeries ℂ))

def formalPointCoefficientGenerators {n : ℕ}
    (R : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) : Set FormalLaurent :=
  Set.range fun d : R.support => formalPointRowEmbedding (MvPolynomial.coeff d.1 R)

def liftFormalPointRow {n : ℕ}
    (R : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    MvPolynomial (Fin (n + 1))
      (differentialAdjoin ℚ (formalPointCoefficientGenerators R)) :=
  ∑ d : R.support, MvPolynomial.monomial d.1
    ⟨formalPointRowEmbedding (MvPolynomial.coeff d.1 R),
      subset_differentialAdjoin ℚ (formalPointCoefficientGenerators R)
        (Set.mem_range_self d)⟩

theorem coeff_liftFormalPointRow_of_mem {n : ℕ}
    (R : MvPolynomial (Fin (n + 1)) (Polynomial ℂ))
    {d : Fin (n + 1) →₀ ℕ} (hd : d ∈ R.support) :
    MvPolynomial.coeff d (liftFormalPointRow R) =
      ⟨formalPointRowEmbedding (MvPolynomial.coeff d R),
        subset_differentialAdjoin ℚ (formalPointCoefficientGenerators R)
          (Set.mem_range_self (⟨d, hd⟩ : R.support))⟩ := by
  classical
  simp only [liftFormalPointRow, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single (⟨d, hd⟩ : R.support)]
  · simp
  · intro e he hne
    rw [if_neg]
    intro hde
    apply hne
    exact Subtype.ext hde
  · simp

theorem coeff_liftFormalPointRow_of_not_mem {n : ℕ}
    (R : MvPolynomial (Fin (n + 1)) (Polynomial ℂ))
    {d : Fin (n + 1) →₀ ℕ} (hd : d ∉ R.support) :
    MvPolynomial.coeff d (liftFormalPointRow R) = 0 := by
  classical
  simp only [liftFormalPointRow, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_zero]
  intro e he
  rw [if_neg]
  intro hde
  exact hd (hde ▸ e.property)

theorem map_liftFormalPointRow {n : ℕ}
    (R : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    MvPolynomial.map
        (algebraMap (differentialAdjoin ℚ (formalPointCoefficientGenerators R))
          FormalLaurent)
        (liftFormalPointRow R) =
      MvPolynomial.map formalPointRowEmbedding R := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map]
  by_cases hd : d ∈ R.support
  · rw [coeff_liftFormalPointRow_of_mem R hd]
    rfl
  · have hcoeff : MvPolynomial.coeff d R = 0 :=
      not_ne_iff.mp (mt MvPolynomial.mem_support_iff.mpr hd)
    rw [coeff_liftFormalPointRow_of_not_mem R hd, hcoeff, map_zero, map_zero]

theorem liftFormalPointRow_ne_zero {n : ℕ}
    {R : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)} (hR : R ≠ 0) :
    liftFormalPointRow R ≠ 0 := by
  intro h
  have hmap := congrArg (MvPolynomial.map
    (algebraMap (differentialAdjoin ℚ (formalPointCoefficientGenerators R))
      FormalLaurent)) h
  rw [map_liftFormalPointRow, map_zero] at hmap
  apply hR
  apply MvPolynomial.map_injective formalPointRowEmbedding
    (by
      simpa [formalPointRowEmbedding] using
        (Polynomial.algebraMap_hahnSeries_injective (R := ℂ) (Γ := ℤ)))
  simpa only [map_zero] using hmap

theorem formalPointCoefficientGenerators_finite_jetSet {n : ℕ}
    (R : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    (differentialJetSet (formalPointCoefficientGenerators R)).Finite := by
  rw [show differentialJetSet (formalPointCoefficientGenerators R) =
      ⋃ d : R.support, Set.range (fun j => differentialJet j
        (formalPointRowEmbedding (MvPolynomial.coeff d.1 R))) by
    ext y
    simp [differentialJetSet, formalPointCoefficientGenerators]]
  exact Set.finite_iUnion fun d =>
    finite_range_differentialJet_formalLaurent_polynomial
      (MvPolynomial.coeff d.1 R)

theorem differentialAlgebraicOver_of_finiteJetRelation
    {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] [Differential K]
    {x : K} {n : ℕ} {Q : MvPolynomial (Fin (n + 1)) F}
    (hQ : Q ≠ 0)
    (hann : MvPolynomial.aeval
      (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) Q = 0) :
    DifferentialAlgebraicOver F x := by
  unfold DifferentialAlgebraicOver DifferentialIndependent
  intro hx
  let e : Fin (n + 1) → Unit × ℕ := fun j => ((), (j : ℕ))
  have he : Function.Injective e := by
    intro i j hij
    exact Fin.ext (congrArg Prod.snd hij)
  have hrename : MvPolynomial.rename e Q ≠ 0 := fun h =>
    hQ (MvPolynomial.rename_injective e he h)
  apply hrename
  apply hx.eq_zero_of_aeval_eq_zero
  rw [MvPolynomial.aeval_rename]
  simpa [e, Function.comp_def] using hann

theorem map_aeval_powerSeries_formalLaurent {σ : Type*}
    (g : σ → PowerSeries ℂ) (P : MvPolynomial σ (PowerSeries ℂ)) :
    algebraMap (PowerSeries ℂ) FormalLaurent (MvPolynomial.aeval g P) =
      MvPolynomial.aeval
        (fun i => algebraMap (PowerSeries ℂ) FormalLaurent (g i))
        (MvPolynomial.map (algebraMap (PowerSeries ℂ) FormalLaurent) P) := by
  rw [MvPolynomial.map_aeval]
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  congr 1

set_option maxHeartbeats 3000000 in
theorem differentialAlgebraicOver_rat_of_formalRelation
    {F : PowerSeries ℂ} {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P ≠ 0) (hann : MvPolynomial.aeval (formalJets n F) P = 0) :
    DifferentialAlgebraicOver ℚ
      (algebraMap (PowerSeries ℂ) FormalLaurent F) := by
  letI : Differential ℚ := rationalZeroDifferential
  letI : DifferentialAlgebra ℚ FormalLaurent :=
    formalLaurentDifferentialAlgebraRat
  let R := formalPointRow n P
  let S := formalPointCoefficientGenerators R
  let B := differentialAdjoin ℚ S
  let QB := liftFormalPointRow R
  have hR0 : R ≠ 0 := formalPointRow_ne_zero hP
  have hQB0 : QB ≠ 0 := liftFormalPointRow_ne_zero hR0
  have hrowPS : MvPolynomial.aeval
      (fun j : Fin (n + 1) => (⇑(d⁄dX ℂ))^[(j : ℕ)] F)
      (MvPolynomial.map (algebraMap (Polynomial ℂ) (PowerSeries ℂ)) R) = 0 := by
    rw [aeval_map_formalPointRow]
    exact hann
  have hrowLS : MvPolynomial.aeval
      (fun j : Fin (n + 1) => differentialJet (j : ℕ)
        (algebraMap (PowerSeries ℂ) FormalLaurent F))
      (MvPolynomial.map formalPointRowEmbedding R) = 0 := by
    have hmap := congrArg (algebraMap (PowerSeries ℂ) FormalLaurent) hrowPS
    rw [map_zero] at hmap
    rw [map_aeval_powerSeries_formalLaurent] at hmap
    rw [MvPolynomial.map_map, MvPolynomial.aeval_def,
      MvPolynomial.eval₂_map] at hmap
    change MvPolynomial.eval₂ formalPointRowEmbedding
      (fun i : Fin (n + 1) => algebraMap (PowerSeries ℂ) FormalLaurent
        ((⇑(d⁄dX ℂ))^[(i : ℕ)] F)) R = 0 at hmap
    change MvPolynomial.eval₂ formalPointRowEmbedding
      (fun j : Fin (n + 1) => differentialJet (j : ℕ)
        (algebraMap (PowerSeries ℂ) FormalLaurent F)) R = 0
    rw [show (fun j : Fin (n + 1) => differentialJet (j : ℕ)
        (algebraMap (PowerSeries ℂ) FormalLaurent F)) =
      (fun j => algebraMap (PowerSeries ℂ) FormalLaurent
        ((⇑(d⁄dX ℂ))^[(j : ℕ)] F)) by
        funext j
        exact differentialJet_formalLaurent_algebraMap (j : ℕ) F]
    exact hmap
  have hQBann : MvPolynomial.aeval
      (fun j : Fin (n + 1) => differentialJet (j : ℕ)
        (algebraMap (PowerSeries ℂ) FormalLaurent F)) QB = 0 := by
    rw [← map_liftFormalPointRow R] at hrowLS
    rw [MvPolynomial.aeval_map_algebraMap] at hrowLS
    exact hrowLS
  have hyB : DifferentialAlgebraicOver B
      (algebraMap (PowerSeries ℂ) FormalLaurent F) :=
    differentialAlgebraicOver_of_finiteJetRelation hQB0 hQBann
  have hSfinite : (differentialJetSet S).Finite :=
    formalPointCoefficientGenerators_finite_jetSet R
  have hBfinite : Algebra.trdeg ℚ B < Cardinal.aleph0 :=
    differentialAdjoin_trdeg_lt_aleph0_of_finite_jetSet S hSfinite
  exact differentialAlgebraicOver_of_intermediate_trdeg_lt_aleph0 B
    (derivationClosed_differentialAdjoin ℚ S) hBfinite hyB

theorem map_aeval_complex_powerSeries_formalLaurent {σ : Type*}
    (g : σ → PowerSeries ℂ) (P : MvPolynomial σ ℂ) :
    algebraMap (PowerSeries ℂ) FormalLaurent (MvPolynomial.aeval g P) =
      MvPolynomial.aeval
        (fun i => algebraMap (PowerSeries ℂ) FormalLaurent (g i)) P := by
  rw [MvPolynomial.map_aeval, MvPolynomial.aeval_def]
  congr 1

/-- Rational differential algebraicity in the formal Laurent carrier yields an integer
relation over `ℂ`, without asking typeclass inference to choose between its two rational algebra
structures. -/
theorem exists_integerJetRelation_formalLaurent {x : FormalLaurent}
    (hx : DifferentialAlgebraicOver ℚ x) :
    ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 1)) ℂ), Q ≠ 0 ∧
      (∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ)) ∧
      MvPolynomial.aeval
        (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) Q = 0 := by
  obtain ⟨n, P, hP0, hPann⟩ :=
    exists_rational_jet_relation_of_differentialAlgebraicOver hx
  let Qz := clearRationalJetCoefficients P
  let Q : MvPolynomial (Fin (n + 1)) ℂ := MvPolynomial.map (Int.castRingHom ℂ) Qz
  have hQz0 : Qz ≠ 0 := clearRationalJetCoefficients_ne_zero P hP0
  have hQ0 : Q ≠ 0 := by
    intro h
    apply hQz0
    apply MvPolynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
    change MvPolynomial.map (Int.castRingHom ℂ) Qz = 0 at h
    simpa using h
  have hQcoeff : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ) := by
    intro m
    exact ⟨MvPolynomial.coeff m Qz, MvPolynomial.coeff_map _ _ _⟩
  have hrat : MvPolynomial.aeval
      (fun j : Fin (n + 1) => differentialJet (j : ℕ) x)
      (MvPolynomial.map (Int.castRingHom ℚ) Qz) = 0 := by
    rw [map_clearRationalJetCoefficients P, map_mul, MvPolynomial.aeval_C,
      hPann, mul_zero]
  refine ⟨n, Q, hQ0, hQcoeff, ?_⟩
  change MvPolynomial.aeval
    (fun j : Fin (n + 1) => differentialJet (j : ℕ) x)
    (MvPolynomial.map (Int.castRingHom ℂ) Qz) = 0
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map] at hrat
  have hcast : (algebraMap ℂ FormalLaurent).comp (Int.castRingHom ℂ) =
      (algebraMap ℚ FormalLaurent).comp (Int.castRingHom ℚ) := by
    ext z
    simp
  rw [hcast]
  exact hrat

set_option maxHeartbeats 3000000 in
theorem exists_integer_jet_relation_of_formalRelation
    {F : PowerSeries ℂ} {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P ≠ 0) (hann : MvPolynomial.aeval (formalJets n F) P = 0) :
    ∃ (n' : ℕ) (Q : MvPolynomial (Fin (n' + 1)) ℂ), Q ≠ 0 ∧
      (∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ)) ∧
      MvPolynomial.aeval
        (fun j : Fin (n' + 1) => (⇑(d⁄dX ℂ))^[(j : ℕ)] F) Q = 0 := by
  letI : Differential ℚ := rationalZeroDifferential
  letI : DifferentialAlgebra ℚ FormalLaurent :=
    formalLaurentDifferentialAlgebraRat
  have hda : DifferentialAlgebraicOver ℚ
      (algebraMap (PowerSeries ℂ) FormalLaurent F) :=
    differentialAlgebraicOver_rat_of_formalRelation hP hann
  obtain ⟨n', Q, hQ, hint, hrel⟩ :=
    exists_integerJetRelation_formalLaurent hda
  refine ⟨n', Q, hQ, hint, ?_⟩
  apply HahnSeries.ofPowerSeries_injective
  change algebraMap (PowerSeries ℂ) FormalLaurent
      (MvPolynomial.aeval
        (fun j : Fin (n' + 1) => (⇑(d⁄dX ℂ))^[(j : ℕ)] F) Q) =
    algebraMap (PowerSeries ℂ) FormalLaurent 0
  rw [map_zero, map_aeval_complex_powerSeries_formalLaurent]
  simpa [differentialJet_formalLaurent_algebraMap] using hrel

theorem integerCoefficients_rename_finSucc {n : ℕ}
    {Q : MvPolynomial (Fin (n + 1)) ℂ}
    (hint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ)) :
    ∀ m, ∃ z : ℤ,
      MvPolynomial.coeff m (MvPolynomial.rename Fin.succ Q) = (z : ℂ) := by
  intro m
  by_cases hm : MvPolynomial.coeff m (MvPolynomial.rename Fin.succ Q) = 0
  · exact ⟨0, by simpa using hm⟩
  · obtain ⟨u, hu, _hucoeff⟩ := MvPolynomial.coeff_rename_ne_zero Fin.succ Q m hm
    obtain ⟨z, hz⟩ := hint u
    refine ⟨z, ?_⟩
    calc
      MvPolynomial.coeff m (MvPolynomial.rename Fin.succ Q) =
          MvPolynomial.coeff (u.mapDomain Fin.succ) (MvPolynomial.rename Fin.succ Q) := by
            rw [hu]
      _ = MvPolynomial.coeff u Q :=
        MvPolynomial.coeff_rename_mapDomain Fin.succ (Fin.succ_injective (n + 1)) Q u
      _ = (z : ℂ) := hz

set_option maxHeartbeats 3000000 in
/-- Formal Mahler normalization with no coefficient-field hypothesis: every nonzero complex
formal differential relation yields a nonzero integer-coefficient relation. -/
theorem formal_mahler_integer_normalization
    {F : PowerSeries ℂ} {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (hP : P ≠ 0) (hann : MvPolynomial.aeval (formalJets n F) P = 0) :
    ∃ (n' : ℕ) (Q : MvPolynomial (Fin (n' + 2)) ℂ), Q ≠ 0 ∧
      (∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ)) ∧
      MvPolynomial.aeval (formalJets n' F) Q = 0 := by
  obtain ⟨n', Q, hQ, hint, hrel⟩ :=
    exists_integer_jet_relation_of_formalRelation hP hann
  let Q' : MvPolynomial (Fin (n' + 2)) ℂ := MvPolynomial.rename Fin.succ Q
  have hQ' : Q' ≠ 0 := fun h => hQ
    (MvPolynomial.rename_injective Fin.succ (Fin.succ_injective (n' + 1)) h)
  refine ⟨n', Q', hQ', integerCoefficients_rename_finSucc hint, ?_⟩
  change MvPolynomial.aeval (formalJets n' F) (MvPolynomial.rename Fin.succ Q) = 0
  rw [MvPolynomial.aeval_rename]
  simpa [formalJets, Function.comp_def] using hrel

end

end GaloisForLFunctions
