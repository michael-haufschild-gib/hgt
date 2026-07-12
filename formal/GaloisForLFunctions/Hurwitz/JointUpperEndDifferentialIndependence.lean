import GaloisForLFunctions.Hurwitz.JointHypertranscendence
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialIndependence

/-!
# Joint Hurwitz independence in the upper-end meromorphic differential field

The functional relation theorem is upgraded here to an object-level statement.  Every rationally
independent exponent family defines a genuinely differentially independent family of Hurwitz-zeta
germs over the faithfully embedded rational coordinate field `ℂ(a)`.
-/

open Complex HurwitzZetaShift Polynomial

namespace HurwitzJointLadder

open HurwitzLadder HurwitzOrbit HurwitzJointOrbit GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open Filter Set Topology
open scoped Differential

noncomputable section

/-- A Hurwitz zeta function as an analytic germ at the complex upper end. -/
def hzetaUpperEndAnalytic (s : ℂ) (hs : 1 < s.re) : upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (hzeta s), hzeta s, 0,
    by
      simpa [UHP, upperTail] using
        (hzeta_differentiableOn hs).analyticOnNhd isOpen_UHP,
    rfl⟩

/-- The genuine `n`th shift derivative of Hurwitz zeta as an upper-end analytic germ. -/
def hzetaUpperEndAnalyticJet (s : ℂ) (hs : 1 < s.re) (n : ℕ) :
    upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (iteratedDeriv n (hzeta s)),
    iteratedDeriv n (hzeta s), 0,
    by
      simpa [UHP, upperTail] using
        analyticOnNhd_iteratedDeriv
          ((hzeta_differentiableOn hs).analyticOnNhd isOpen_UHP) n,
    rfl⟩

@[simp]
theorem hzetaUpperEndAnalyticJet_zero (s : ℂ) (hs : 1 < s.re) :
    hzetaUpperEndAnalyticJet s hs 0 = hzetaUpperEndAnalytic s hs := by
  rfl

/-- Analytic-germ differentiation advances the genuine Hurwitz jet. -/
theorem upperEndAnalyticDeriv_hzetaJet (s : ℂ) (hs : 1 < s.re) (n : ℕ) :
    upperEndAnalyticDeriv (hzetaUpperEndAnalyticJet s hs n) =
      hzetaUpperEndAnalyticJet s hs (n + 1) := by
  apply Subtype.ext
  change (deriv (iteratedDeriv n (hzeta s)) : Germ upperEndFilter ℂ) =
    (iteratedDeriv (n + 1) (hzeta s) : Germ upperEndFilter ℂ)
  rw [iteratedDeriv_succ]

/-- A Hurwitz zeta function as an element of the upper-end meromorphic field. -/
def hzetaUpperEndMero (s : ℂ) (hs : 1 < s.re) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact algebraMap upperEndAnalyticSubring upperEndMeroField
    (hzetaUpperEndAnalytic s hs)

/-- Differential-field jets of the Hurwitz element are its genuine analytic derivative germs. -/
theorem differentialJet_hzetaUpperEndMero (s : ℂ) (hs : 1 < s.re) (n : ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    differentialJet n (hzetaUpperEndMero s hs) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (hzetaUpperEndAnalyticJet s hs n) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI := upperEndMeroFieldDifferential
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 = n + 1 by rfl, differentialJet_succ, ih,
        upperEndMeroFieldDifferential_algebraMap,
        upperEndAnalyticDeriv_hzetaJet]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def jointHzetaUpperEndAnalyticJet {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re)
    (N : ℕ) : ι × Fin (N + 1) → upperEndAnalyticSubring :=
  fun jk => hzetaUpperEndAnalyticJet (s jk.1) (hs1 jk.1) (jk.2 : ℕ)

def jointHzetaUpperEndFieldJet {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re)
    (N : ℕ) : ι × Fin (N + 1) → upperEndMeroField :=
  fun jk => by
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    exact differentialJet (jk.2 : ℕ) (hzetaUpperEndMero (s jk.1) (hs1 jk.1))

omit [Fintype ι] [DecidableEq ι] in
theorem jointHzetaUpperEndFieldJet_eq_algebraMap
    {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re) (N : ℕ) (jk : ι × Fin (N + 1)) :
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    jointHzetaUpperEndFieldJet hs1 N jk =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (jointHzetaUpperEndAnalyticJet hs1 N jk) := by
  letI := isDomain_upperEndAnalyticSubring
  letI := upperEndMeroFieldDifferential
  exact differentialJet_hzetaUpperEndMero (s jk.1) (hs1 jk.1) (jk.2 : ℕ)

def jointHzetaPolynomialRelation {s : ι → ℂ} (N : ℕ)
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ)) (a : ℂ) : ℂ :=
  MvPolynomial.eval₂ (Polynomial.evalRingHom a)
    (fun jk => iteratedDeriv (jk.2 : ℕ) (hzeta (s jk.1)) a) P

omit [Fintype ι] [DecidableEq ι] in
theorem analyticOnNhd_jointHzetaPolynomialRelation
    {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re) (N : ℕ)
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ)) :
    AnalyticOnNhd ℂ (jointHzetaPolynomialRelation (s := s) N P) UHP := by
  induction P using MvPolynomial.induction_on with
  | C p =>
      have heq : jointHzetaPolynomialRelation (s := s) N (MvPolynomial.C p) =
          fun a => p.eval a := by
        funext a
        simp [jointHzetaPolynomialRelation]
      rw [heq]
      simpa [UHP, upperTail] using upperEnd_analyticOnNhd_polyEval p
  | add P Q hP hQ =>
      have heq : jointHzetaPolynomialRelation (s := s) N (P + Q) =
          jointHzetaPolynomialRelation (s := s) N P +
            jointHzetaPolynomialRelation (s := s) N Q := by
        funext a
        simp [jointHzetaPolynomialRelation]
      rw [heq]
      exact hP.add hQ
  | mul_X P jk hP =>
      have heq : jointHzetaPolynomialRelation (s := s) N (P * MvPolynomial.X jk) =
          fun a => jointHzetaPolynomialRelation (s := s) N P a *
            iteratedDeriv (jk.2 : ℕ) (hzeta (s jk.1)) a := by
        funext a
        simp [jointHzetaPolynomialRelation]
      rw [heq]
      exact hP.mul (analyticOnNhd_iteratedDeriv
        ((hzeta_differentiableOn (hs1 jk.1)).analyticOnNhd isOpen_UHP) (jk.2 : ℕ))

omit [Fintype ι] [DecidableEq ι] in
theorem jointHzetaUpperEndAnalyticRelation_coe
    {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re) (N : ℕ)
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ)) :
    ((MvPolynomial.eval₂ upperEndPolyToAnalytic
        (jointHzetaUpperEndAnalyticJet hs1 N) P : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) =
      (jointHzetaPolynomialRelation (s := s) N P : Germ upperEndFilter ℂ) := by
  induction P using MvPolynomial.induction_on with
  | C p =>
      rw [MvPolynomial.eval₂_C]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun a => by
        simp [jointHzetaPolynomialRelation]
  | add P Q hP hQ =>
      rw [MvPolynomial.eval₂_add]
      change
        ((MvPolynomial.eval₂ upperEndPolyToAnalytic
          (jointHzetaUpperEndAnalyticJet hs1 N) P : upperEndAnalyticSubring) :
            Germ upperEndFilter ℂ) +
        ((MvPolynomial.eval₂ upperEndPolyToAnalytic
          (jointHzetaUpperEndAnalyticJet hs1 N) Q : upperEndAnalyticSubring) :
            Germ upperEndFilter ℂ) = _
      rw [hP, hQ, ← Germ.coe_add]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun a => by
        simp [jointHzetaPolynomialRelation]
  | mul_X P jk hP =>
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      change
        ((MvPolynomial.eval₂ upperEndPolyToAnalytic
          (jointHzetaUpperEndAnalyticJet hs1 N) P : upperEndAnalyticSubring) :
            Germ upperEndFilter ℂ) *
          (jointHzetaUpperEndAnalyticJet hs1 N jk : Germ upperEndFilter ℂ) = _
      rw [hP]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun a => by
        simp [jointHzetaPolynomialRelation]

omit [Fintype ι] [DecidableEq ι] in
theorem jointHzetaPolynomialRelation_eq_zero_of_upperEnd_eq_zero
    {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re) (N : ℕ)
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (hzero : MvPolynomial.eval₂ upperEndPolyToAnalytic
      (jointHzetaUpperEndAnalyticJet hs1 N) P = 0) :
    ∀ a : ℂ, 0 < a.im → jointHzetaPolynomialRelation (s := s) N P a = 0 := by
  let F := jointHzetaPolynomialRelation (s := s) N P
  have hgerm : (F : Germ upperEndFilter ℂ) = 0 := by
    rw [← jointHzetaUpperEndAnalyticRelation_coe hs1 N P]
    exact congrArg Subtype.val hzero
  rw [← Germ.coe_zero, Germ.coe_eq] at hgerm
  change ∀ᶠ a in upperEndFilter, F a = 0 at hgerm
  rw [upperEndFilter_basis.eventually_iff] at hgerm
  obtain ⟨L, -, hL⟩ := hgerm
  let w : ℂ := ((max 0 L + 1 : ℝ) : ℂ) * Complex.I
  have hwL : w ∈ upperTail L := by
    simp only [w, upperTail, mem_setOf_eq, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    linarith [le_max_right 0 L]
  have hwU : w ∈ UHP := by
    show 0 < w.im
    simp only [w, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    linarith [le_max_left 0 L]
  have hlocal : F =ᶠ[nhds w] 0 := by
    filter_upwards [(upperTail_isOpen L).mem_nhds hwL] with a ha
    exact hL ha
  have hF := analyticOnNhd_jointHzetaPolynomialRelation hs1 N P
  have hall := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_UHP hwU hlocal
  intro a ha
  exact hall ha

omit [Fintype ι] in
theorem jointHzetaUpperEndClearedRelation_eq_zero_of_fieldRelation_eq_zero
    {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re) (N : ℕ)
    (Q : MvPolynomial (ι × Fin (N + 1)) (RatFunc ℂ))
    (hzero :
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      MvPolynomial.eval₂ upperEndRatfuncToMero
        (jointHzetaUpperEndFieldJet hs1 N) Q = 0) :
    MvPolynomial.eval₂ upperEndPolyToAnalytic
      (jointHzetaUpperEndAnalyticJet hs1 N)
      (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) = 0 := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let fieldJet := jointHzetaUpperEndFieldJet hs1 N
  let analyticJet := jointHzetaUpperEndAnalyticJet hs1 N
  have hclearField : MvPolynomial.eval₂ upperEndPolyToMero fieldJet
      (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) = 0 := by
    calc
      MvPolynomial.eval₂ upperEndPolyToMero fieldJet
          (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) =
          MvPolynomial.eval₂ upperEndRatfuncToMero fieldJet
            (MvPolynomial.map (algebraMap ℂ[X] (RatFunc ℂ))
              (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q)) := by
            rw [MvPolynomial.eval₂_map]
            rw [← upperEndPolyToMero_eq_comp]
      _ = MvPolynomial.eval₂ upperEndRatfuncToMero fieldJet
          (MvPolynomial.C
            (algebraMap ℂ[X] (RatFunc ℂ)
              (GaloisForLFunctions.HTGeometry.ratFuncCommonDenominator Q)) * Q) := by
            rw [GaloisForLFunctions.HTGeometry.map_clearRatFuncCoefficients]
      _ = 0 := by
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hzero, mul_zero]
  have hmap : algebraMap upperEndAnalyticSubring upperEndMeroField
      (MvPolynomial.eval₂ upperEndPolyToAnalytic analyticJet
        (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q)) = 0 := by
    rw [MvPolynomial.eval₂_comp_right]
    rw [MvPolynomial.eval₂_map]
    change MvPolynomial.eval₂ upperEndPolyToMero
      (fun jk => algebraMap upperEndAnalyticSubring upperEndMeroField (analyticJet jk))
      (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) = 0
    rw [show (fun jk => algebraMap upperEndAnalyticSubring upperEndMeroField
      (analyticJet jk)) = fieldJet by
        funext jk
        exact (jointHzetaUpperEndFieldJet_eq_algebraMap hs1 N jk).symm]
    exact hclearField
  exact (IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField)
    (by simpa using hmap)

/-- Every finite jet rectangle is algebraically independent inside the concrete upper-end
meromorphic field over its faithfully embedded rational coordinate field. -/
theorem joint_hzeta_upperEnd_rectangle_algebraicIndependent
    {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re)
    (hmono : Function.Injective (monomialValue (fun j => monoScalar (s j)))) (N : ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    AlgebraicIndependent (RatFunc ℂ) (jointHzetaUpperEndFieldJet hs1 N) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  rw [algebraicIndependent_iff]
  intro Q hQ
  apply joint_hzeta_rational_hypertranscendental_in_shift hs1 hmono N Q
  have hfield : MvPolynomial.eval₂ upperEndRatfuncToMero
      (jointHzetaUpperEndFieldJet hs1 N) Q = 0 := by
    simpa [MvPolynomial.aeval_def, RingHom.algebraMap_toAlgebra] using hQ
  have hclear := jointHzetaUpperEndClearedRelation_eq_zero_of_fieldRelation_eq_zero
    hs1 N Q hfield
  exact jointHzetaPolynomialRelation_eq_zero_of_upperEnd_eq_zero hs1 N
    (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) hclear

/-- Rational linear independence supplies the intrinsic monodromy hypothesis for every finite
upper-end jet rectangle. -/
theorem joint_hzeta_upperEnd_rectangle_algebraicIndependent_of_linearIndependent
    {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re)
    (hsQ : LinearIndependent ℚ (exponentFamily s)) (N : ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    AlgebraicIndependent (RatFunc ℂ) (jointHzetaUpperEndFieldJet hs1 N) :=
  joint_hzeta_upperEnd_rectangle_algebraicIndependent hs1
    (monomialValue_monoScalar_injective_of_linearIndependent s hsQ) N

/-- **Finite-family object-level joint hypertranscendence.**  A finite Hurwitz family with
pairwise-distinct monodromy monomials is genuinely differentially independent over `ℂ(a)` in the
upper-end meromorphic differential field. -/
theorem joint_hzeta_upperEnd_differentialIndependent_finite
    {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re)
    (hmono : Function.Injective (monomialValue (fun j => monoScalar (s j)))) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ) (fun j => hzetaUpperEndMero (s j) (hs1 j)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  unfold DifferentialIndependent
  apply algebraicIndependent_of_finite_type
  intro t ht
  let N : ℕ := ∑ p ∈ ht.toFinset, p.2
  have horder : ∀ p : t, p.1.2 < N + 1 := by
    intro p
    have hpMem : p.1 ∈ ht.toFinset := ht.mem_toFinset.mpr p.2
    have hle : p.1.2 ≤ ∑ q ∈ ht.toFinset, q.2 :=
      Finset.single_le_sum (fun q _ => Nat.zero_le q.2) hpMem
    exact Nat.lt_succ_of_le hle
  let e : t → ι × Fin (N + 1) := fun p => (p.1.1, ⟨p.1.2, horder p⟩)
  have he : Function.Injective e := by
    intro p q hpq
    apply Subtype.ext
    exact Prod.ext
      (congrArg (fun z : ι × Fin (N + 1) => z.1) hpq)
      (congrArg (fun z : ι × Fin (N + 1) => z.2.1) hpq)
  have hrect := joint_hzeta_upperEnd_rectangle_algebraicIndependent hs1 hmono N
  have hcomp := hrect.comp e he
  simpa [e, jointHzetaUpperEndFieldJet] using hcomp

/-- Rational linear independence gives finite-family object-level joint hypertranscendence. -/
theorem joint_hzeta_upperEnd_differentialIndependent_finite_of_linearIndependent
    {s : ι → ℂ} (hs1 : ∀ j, 1 < (s j).re)
    (hsQ : LinearIndependent ℚ (exponentFamily s)) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ) (fun j => hzetaUpperEndMero (s j) (hs1 j)) :=
  joint_hzeta_upperEnd_differentialIndependent_finite hs1
    (monomialValue_monoScalar_injective_of_linearIndependent s hsQ)

/-- **Arbitrary-family object-level joint hypertranscendence.**  If `1` together with an
arbitrarily indexed exponent family is rationally linearly independent, the entire corresponding
Hurwitz family is differentially independent over `ℂ(a)` in one concrete meromorphic differential
field. -/
theorem joint_hzeta_upperEnd_differentialIndependent
    {κ : Type*} {s : κ → ℂ} (hs1 : ∀ j, 1 < (s j).re)
    (hsQ : LinearIndependent ℚ (exponentFamily s)) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ) (fun j => hzetaUpperEndMero (s j) (hs1 j)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  unfold DifferentialIndependent
  apply algebraicIndependent_of_finite_type
  intro t ht
  let J : Set κ := Prod.fst '' t
  have hJ : J.Finite := ht.image Prod.fst
  letI : Finite J := hJ
  letI : Fintype J := Fintype.ofFinite J
  letI : DecidableEq J := Classical.decEq J
  let sJ : J → ℂ := fun j => s j.1
  have hs1J : ∀ j, 1 < (sJ j).re := fun j => hs1 j.1
  have hsQJ : LinearIndependent ℚ (exponentFamily sJ) := by
    simpa [sJ] using exponentFamily_linearIndependent_comp s hsQ
      (fun j : J => j.1) Subtype.val_injective
  have hfin :=
    joint_hzeta_upperEnd_differentialIndependent_finite_of_linearIndependent hs1J hsQJ
  unfold DifferentialIndependent at hfin
  let et : t → J × ℕ := fun p =>
    (⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩, p.1.2)
  have het : Function.Injective et := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : J × ℕ => z.1.1) hpq
    · exact congrArg (fun z : J × ℕ => z.2) hpq
  have hcomp := hfin.comp et het
  simpa [et, sJ] using hcomp

end

end HurwitzJointLadder
