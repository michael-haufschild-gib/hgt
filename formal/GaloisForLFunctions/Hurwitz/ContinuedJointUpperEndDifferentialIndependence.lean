import GaloisForLFunctions.Hurwitz.ContinuedJointHypertranscendence
import GaloisForLFunctions.Hurwitz.ContinuedUpperEnd

/-!
# Object-level unrestricted joint continued-Hurwitz independence

The unrestricted functional theorem is transported to the concrete upper-end meromorphic
differential field over the faithfully embedded rational coordinate field `ℂ(a)`.
-/

open Complex Polynomial

namespace HurwitzJointLadder

open HurwitzLadder HurwitzJointOrbit HurwitzZetaContinuation GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open Filter Set Topology
open scoped Differential

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def continuedJointHzetaUpperEndAnalyticJet {s : ι → ℂ}
    (N : ℕ) : ι × Fin (N + 1) → upperEndAnalyticSubring :=
  fun jk => continuedHzetaUpperEndAnalyticJet (s jk.1) (jk.2 : ℕ)

def continuedJointHzetaUpperEndFieldJet {s : ι → ℂ}
    (N : ℕ) : ι × Fin (N + 1) → upperEndMeroField :=
  fun jk => by
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    exact differentialJet (jk.2 : ℕ) (continuedHzetaUpperEndMero (s jk.1))

omit [Fintype ι] [DecidableEq ι] in
theorem continuedJointHzetaUpperEndFieldJet_eq_algebraMap
    {s : ι → ℂ} (N : ℕ) (jk : ι × Fin (N + 1)) :
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    continuedJointHzetaUpperEndFieldJet (s := s) N jk =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (continuedJointHzetaUpperEndAnalyticJet (s := s) N jk) := by
  letI := isDomain_upperEndAnalyticSubring
  letI := upperEndMeroFieldDifferential
  exact differentialJet_continuedHzetaUpperEndMero (s jk.1) (jk.2 : ℕ)

def continuedJointHzetaPolynomialRelation {s : ι → ℂ} (N : ℕ)
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ)) (a : ℂ) : ℂ :=
  MvPolynomial.eval₂ (Polynomial.evalRingHom a)
    (fun jk => iteratedDeriv (jk.2 : ℕ) (continuedHzeta (s jk.1)) a) P

omit [Fintype ι] [DecidableEq ι] in
theorem analyticOnNhd_continuedJointHzetaPolynomialRelation
    {s : ι → ℂ} (N : ℕ)
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ)) :
    AnalyticOnNhd ℂ (continuedJointHzetaPolynomialRelation (s := s) N P) UHP := by
  induction P using MvPolynomial.induction_on with
  | C p =>
      have heq : continuedJointHzetaPolynomialRelation (s := s) N (MvPolynomial.C p) =
          fun a => p.eval a := by
        funext a
        simp [continuedJointHzetaPolynomialRelation]
      rw [heq]
      simpa [UHP, upperTail] using upperEnd_analyticOnNhd_polyEval p
  | add P Q hP hQ =>
      have heq : continuedJointHzetaPolynomialRelation (s := s) N (P + Q) =
          continuedJointHzetaPolynomialRelation (s := s) N P +
            continuedJointHzetaPolynomialRelation (s := s) N Q := by
        funext a
        simp [continuedJointHzetaPolynomialRelation]
      rw [heq]
      exact hP.add hQ
  | mul_X P jk hP =>
      have heq : continuedJointHzetaPolynomialRelation (s := s) N
          (P * MvPolynomial.X jk) = fun a =>
            continuedJointHzetaPolynomialRelation (s := s) N P a *
              iteratedDeriv (jk.2 : ℕ) (continuedHzeta (s jk.1)) a := by
        funext a
        simp [continuedJointHzetaPolynomialRelation]
      rw [heq]
      exact hP.mul (analyticOnNhd_iteratedDeriv
        (continuedHzeta_analyticOnNhd (s jk.1)) (jk.2 : ℕ))

omit [Fintype ι] [DecidableEq ι] in
theorem continuedJointHzetaUpperEndAnalyticRelation_coe
    {s : ι → ℂ} (N : ℕ)
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ)) :
    ((MvPolynomial.eval₂ upperEndPolyToAnalytic
        (continuedJointHzetaUpperEndAnalyticJet (s := s) N) P : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) =
      (continuedJointHzetaPolynomialRelation (s := s) N P : Germ upperEndFilter ℂ) := by
  induction P using MvPolynomial.induction_on with
  | C p =>
      rw [MvPolynomial.eval₂_C]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun a => by
        simp [continuedJointHzetaPolynomialRelation]
  | add P Q hP hQ =>
      rw [MvPolynomial.eval₂_add]
      change
        ((MvPolynomial.eval₂ upperEndPolyToAnalytic
          (continuedJointHzetaUpperEndAnalyticJet (s := s) N) P : upperEndAnalyticSubring) :
            Germ upperEndFilter ℂ) +
        ((MvPolynomial.eval₂ upperEndPolyToAnalytic
          (continuedJointHzetaUpperEndAnalyticJet (s := s) N) Q : upperEndAnalyticSubring) :
            Germ upperEndFilter ℂ) = _
      rw [hP, hQ, ← Germ.coe_add]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun a => by
        simp [continuedJointHzetaPolynomialRelation]
  | mul_X P jk hP =>
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      change
        ((MvPolynomial.eval₂ upperEndPolyToAnalytic
          (continuedJointHzetaUpperEndAnalyticJet (s := s) N) P : upperEndAnalyticSubring) :
            Germ upperEndFilter ℂ) *
          (continuedJointHzetaUpperEndAnalyticJet (s := s) N jk : Germ upperEndFilter ℂ) = _
      rw [hP]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun a => by
        simp [continuedJointHzetaPolynomialRelation]

omit [Fintype ι] [DecidableEq ι] in
theorem continuedJointHzetaPolynomialRelation_eq_zero_of_upperEnd_eq_zero
    {s : ι → ℂ} (N : ℕ)
    (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (hzero : MvPolynomial.eval₂ upperEndPolyToAnalytic
      (continuedJointHzetaUpperEndAnalyticJet (s := s) N) P = 0) :
    ∀ a : ℂ, 0 < a.im →
      continuedJointHzetaPolynomialRelation (s := s) N P a = 0 := by
  let F := continuedJointHzetaPolynomialRelation (s := s) N P
  have hgerm : (F : Germ upperEndFilter ℂ) = 0 := by
    rw [← continuedJointHzetaUpperEndAnalyticRelation_coe N P]
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
  have hF := analyticOnNhd_continuedJointHzetaPolynomialRelation (s := s) N P
  have hall := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_UHP hwU hlocal
  intro a ha
  exact hall ha

omit [Fintype ι] in
theorem continuedJointHzetaUpperEndClearedRelation_eq_zero_of_fieldRelation_eq_zero
    {s : ι → ℂ} (N : ℕ)
    (Q : MvPolynomial (ι × Fin (N + 1)) (RatFunc ℂ))
    (hzero :
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      MvPolynomial.eval₂ upperEndRatfuncToMero
        (continuedJointHzetaUpperEndFieldJet (s := s) N) Q = 0) :
    MvPolynomial.eval₂ upperEndPolyToAnalytic
      (continuedJointHzetaUpperEndAnalyticJet (s := s) N)
      (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) = 0 := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let fieldJet := continuedJointHzetaUpperEndFieldJet (s := s) N
  let analyticJet := continuedJointHzetaUpperEndAnalyticJet (s := s) N
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
        exact (continuedJointHzetaUpperEndFieldJet_eq_algebraMap N jk).symm]
    exact hclearField
  exact (IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField)
    (by simpa using hmap)

/-- Every finite jet rectangle of an unrestricted augmented-rationally-independent continued
Hurwitz family is algebraically independent over `ℂ(a)`. -/
theorem continued_joint_hzeta_upperEnd_rectangle_algebraicIndependent
    {s : ι → ℂ} (hsQ : LinearIndependent ℚ (exponentFamily s)) (N : ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    AlgebraicIndependent (RatFunc ℂ)
      (continuedJointHzetaUpperEndFieldJet (s := s) N) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  rw [algebraicIndependent_iff]
  intro Q hQ
  apply continued_joint_hzeta_rational_hypertranscendental_in_shift_of_linearIndependent
    hsQ N Q
  have hfield : MvPolynomial.eval₂ upperEndRatfuncToMero
      (continuedJointHzetaUpperEndFieldJet (s := s) N) Q = 0 := by
    simpa [MvPolynomial.aeval_def, RingHom.algebraMap_toAlgebra] using hQ
  have hclear :=
    continuedJointHzetaUpperEndClearedRelation_eq_zero_of_fieldRelation_eq_zero N Q hfield
  exact continuedJointHzetaPolynomialRelation_eq_zero_of_upperEnd_eq_zero N
    (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) hclear

/-- **Unrestricted finite-family object-level joint hypertranscendence.** -/
theorem continued_joint_hzeta_upperEnd_differentialIndependent_finite
    {s : ι → ℂ} (hsQ : LinearIndependent ℚ (exponentFamily s)) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ) (fun j => continuedHzetaUpperEndMero (s j)) := by
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
  have hrect := continued_joint_hzeta_upperEnd_rectangle_algebraicIndependent hsQ N
  have hcomp := hrect.comp e he
  simpa [e, continuedJointHzetaUpperEndFieldJet] using! hcomp

/-- Every finite jet rectangle for nonintegral, pairwise residue-separated exponents is
algebraically independent over `ℂ(a)`. -/
theorem continued_joint_hzeta_upperEnd_rectangle_algebraicIndependent_of_integerResidueSeparated
    {s : ι → ℂ} (hnonintegral : ∀ j, ∀ m : ℤ, s j ≠ (m : ℂ))
    (hseparated : ∀ i j, i ≠ j → ∀ m : ℤ, s i - s j ≠ (m : ℂ)) (N : ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    AlgebraicIndependent (RatFunc ℂ)
      (continuedJointHzetaUpperEndFieldJet (s := s) N) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  rw [algebraicIndependent_iff]
  intro Q hQ
  apply
    continued_joint_hzeta_rational_hypertranscendental_in_shift_of_integerResidueSeparated
      hnonintegral hseparated N Q
  have hfield : MvPolynomial.eval₂ upperEndRatfuncToMero
      (continuedJointHzetaUpperEndFieldJet (s := s) N) Q = 0 := by
    simpa [MvPolynomial.aeval_def, RingHom.algebraMap_toAlgebra] using hQ
  have hclear :=
    continuedJointHzetaUpperEndClearedRelation_eq_zero_of_fieldRelation_eq_zero N Q hfield
  exact continuedJointHzetaPolynomialRelation_eq_zero_of_upperEnd_eq_zero N
    (GaloisForLFunctions.HTGeometry.clearRatFuncCoefficients Q) hclear

/-- **Exact-residue object-level joint differential independence.** -/
theorem continued_joint_hzeta_upperEnd_differentialIndependent_finite_of_integerResidueSeparated
    {s : ι → ℂ} (hnonintegral : ∀ j, ∀ m : ℤ, s j ≠ (m : ℂ))
    (hseparated : ∀ i j, i ≠ j → ∀ m : ℤ, s i - s j ≠ (m : ℂ)) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ) (fun j => continuedHzetaUpperEndMero (s j)) := by
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
  have hrect :=
    continued_joint_hzeta_upperEnd_rectangle_algebraicIndependent_of_integerResidueSeparated
      hnonintegral hseparated N
  have hcomp := hrect.comp e he
  simpa [e, continuedJointHzetaUpperEndFieldJet] using! hcomp

end

end HurwitzJointLadder
