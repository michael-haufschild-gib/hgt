import GaloisForLFunctions.HTGeometry.EllipticGammaCommensurableReflectionFactorizationUniversalityLaw
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaReflectionHypertranscendenceUniversalityLaw

/-!
# Arithmetic phase classification for rank-two elliptic Gamma reflection
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

local instance ellipticGammaArithmeticPhaseUnivDomain :
    IsDomain (Bottcher.analyticSubring Set.univ) :=
  multipleEllipticGammaHTUnivDomain

local instance ellipticGammaArithmeticPhaseComplexAlgebraAnalytic :
    Algebra ℂ (Bottcher.analyticSubring Set.univ) :=
  multipleEllipticGammaHTComplexAlgebraAnalytic

local instance ellipticGammaArithmeticPhaseComplexAlgebraMero :
    Algebra ℂ (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTComplexAlgebraMero

local instance ellipticGammaArithmeticPhaseMeroDifferential :
    Differential (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTMeroDifferential

local instance ellipticGammaArithmeticPhaseComplexDifferential : Differential ℂ :=
  multipleEllipticGammaHTComplexDifferential

local instance ellipticGammaArithmeticPhaseMeroCharZero :
    CharZero (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTMeroCharZero

local instance ellipticGammaArithmeticPhaseComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTComplexDifferentialAlgebra

local instance ellipticGammaArithmeticPhaseCoordinateDifferential :
    Differential meromorphicRationalCoordinateField :=
  multipleEllipticGammaHTCoordinateDifferential

local instance ellipticGammaArithmeticPhaseCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField
      (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTCoordinateDifferentialAlgebra

/-- A rank-two upper-half-plane period packet. -/
theorem ellipticGamma_rankTwoPeriods_upperHalfPlane
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ∀ i : Fin 2, 0 < (![sigma, tau] i).im := by
  intro i
  fin_cases i
  · simpa using hsigma
  · simpa using htau

/-- Failure of rational independence in an upper-half-plane elliptic-Gamma period triple is
equivalent to a positive integral commensurability relation. -/
theorem not_linearIndependent_ellipticGammaSourcePeriods_iff_positiveCommensurable
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ¬ LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau) ↔
      ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ ∃ k : ℤ,
        (m : ℂ) * sigma = (n : ℂ) * tau + (k : ℂ) := by
  constructor
  · intro hdep
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
    have hrel :
        ((g 0 : ℚ) : ℂ) + (g 1 : ℂ) * sigma + (g 2 : ℂ) * tau = 0 := by
      simpa only [Fin.sum_univ_three, ellipticGammaSourcePeriods,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Rat.smul_def, mul_one] using hg
    have him : (g 1 : ℝ) * sigma.im + (g 2 : ℝ) * tau.im = 0 := by
      have h := congrArg Complex.im hrel
      simpa using h
    have hg1 : g 1 ≠ 0 := by
      intro hg10
      have hg2 : g 2 = 0 := by
        rw [hg10, Rat.cast_zero, zero_mul, zero_add] at him
        exact_mod_cast (mul_eq_zero.mp him).resolve_right htau.ne'
      have hg0 : g 0 = 0 := by
        rw [hg10, hg2] at hrel
        simpa using hrel
      fin_cases i
      · exact hi hg0
      · exact hi hg10
      · exact hi hg2
    have hg2 : g 2 ≠ 0 := by
      intro hg20
      have hg1r : (g 1 : ℝ) = 0 := by
        rw [hg20, Rat.cast_zero, zero_mul, add_zero] at him
        exact (mul_eq_zero.mp him).resolve_right hsigma.ne'
      exact hg1 (by exact_mod_cast hg1r)
    have hrat : ∃ a b k : ℚ, 0 < a ∧ 0 < b ∧
        (a : ℂ) * sigma = (b : ℂ) * tau + (k : ℂ) := by
      rcases (lt_or_gt_of_ne hg1) with hg1neg | hg1pos
      · have hg2pos : 0 < g 2 := by
          by_contra hg2npos
          have hg2neg : g 2 < 0 :=
            lt_of_le_of_ne (le_of_not_gt hg2npos) hg2
          have hneg : (g 1 : ℝ) * sigma.im + (g 2 : ℝ) * tau.im < 0 :=
            add_neg
              (mul_neg_of_neg_of_pos (by exact_mod_cast hg1neg) hsigma)
              (mul_neg_of_neg_of_pos (by exact_mod_cast hg2neg) htau)
          linarith
        refine ⟨-g 1, g 2, g 0, neg_pos.mpr hg1neg, hg2pos, ?_⟩
        push_cast
        linear_combination -hrel
      · have hg2neg : g 2 < 0 := by
          by_contra hg2nneg
          have hg2pos : 0 < g 2 :=
            lt_of_le_of_ne (le_of_not_gt hg2nneg) (Ne.symm hg2)
          have hpos : 0 < (g 1 : ℝ) * sigma.im + (g 2 : ℝ) * tau.im :=
            add_pos
              (mul_pos (by exact_mod_cast hg1pos) hsigma)
              (mul_pos (by exact_mod_cast hg2pos) htau)
          linarith
        refine ⟨g 1, -g 2, -g 0, hg1pos, neg_pos.mpr hg2neg, ?_⟩
        push_cast
        linear_combination hrel
    obtain ⟨a, b, k, ha, hb, habk⟩ := hrat
    let m : ℕ := a.num.natAbs * b.den * k.den
    let n : ℕ := b.num.natAbs * a.den * k.den
    let z : ℤ := k.num * (a.den * b.den : ℕ)
    have ham : 0 < a.num.natAbs :=
      Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr ha))
    have hbn : 0 < b.num.natAbs :=
      Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hb))
    have hm : 0 < m := mul_pos (mul_pos ham b.den_pos) k.den_pos
    have hn : 0 < n := mul_pos (mul_pos hbn a.den_pos) k.den_pos
    refine ⟨m, n, hm, hn, z, ?_⟩
    have haNumCast : ((a.num.natAbs : ℕ) : ℂ) = (a.num : ℂ) := by
      simpa using congrArg (fun w : ℤ => (w : ℂ))
        (Int.natAbs_of_nonneg (le_of_lt (Rat.num_pos.mpr ha)))
    have hbNumCast : ((b.num.natAbs : ℕ) : ℂ) = (b.num : ℂ) := by
      simpa using congrArg (fun w : ℤ => (w : ℂ))
        (Int.natAbs_of_nonneg (le_of_lt (Rat.num_pos.mpr hb)))
    rw [Rat.cast_def, Rat.cast_def, Rat.cast_def] at habk
    field_simp at habk
    dsimp only [m, n, z]
    push_cast
    rw [haNumCast, hbNumCast]
    linear_combination habk
  · rintro ⟨m, n, hm, hn, k, hperiod⟩ hindependent
    have hcomb : ∑ i, (![-(k : ℚ), (m : ℚ), -(n : ℚ)] : Fin 3 → ℚ) i •
        ellipticGammaSourcePeriods sigma tau i = 0 := by
      simp only [Fin.sum_univ_three, ellipticGammaSourcePeriods,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Rat.smul_def]
      push_cast
      linear_combination hperiod
    have hz := Fintype.linearIndependent_iff.mp hindependent _ hcomb
    have hm0 : (m : ℚ) = 0 := hz 1
    have : m = 0 := by exact_mod_cast hm0
    omega

/-- Independent rank-two period triples carry the full multiple elliptic-Gamma
hypertranscendence/reflection certificate. -/
structure EllipticGammaRankTwoIndependentReflectionCertificate
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) : Prop where
  independent :
    LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)
  productHypertranscendental :
    HypertranscendentalOver meromorphicRationalCoordinateField
      (multipleEllipticGammaMero ![sigma, tau]
        (ellipticGamma_rankTwoPeriods_upperHalfPlane sigma tau hsigma htau))
  logDerivativeHypertranscendental :
    HypertranscendentalOver meromorphicRationalCoordinateField
      (multipleEllipticGammaLogDerivMero ![sigma, tau]
        (ellipticGamma_rankTwoPeriods_upperHalfPlane sigma tau hsigma htau))
  productReflection :
    ∀ z : ℂ,
      multipleEllipticGammaProduct ![sigma, tau]
          ((∑ i : Fin 2, ![sigma, tau] i) - z) =
        if Even (Fintype.card (Fin 2)) then
          (multipleEllipticGammaProduct ![sigma, tau] z)⁻¹
        else multipleEllipticGammaProduct ![sigma, tau] z
  logDerivativeReflection :
    ∀ z : ℂ,
      multipleEllipticGammaForwardProduct ![sigma, tau] z ≠ 0 →
      multipleEllipticGammaBackwardProduct ![sigma, tau] z ≠ 0 →
      logDeriv (multipleEllipticGammaProduct ![sigma, tau])
          ((∑ i : Fin 2, ![sigma, tau] i) - z) =
        multipleEllipticGammaLogSign (Fin 2) *
          logDeriv (multipleEllipticGammaProduct ![sigma, tau]) z
  reflectionProduct :
    if Even (Fintype.card (Fin 2)) then
      ∀ z : ℂ,
        multipleEllipticGammaForwardProduct ![sigma, tau] z ≠ 0 →
        multipleEllipticGammaBackwardProduct ![sigma, tau] z ≠ 0 →
        multipleEllipticGammaProduct ![sigma, tau] z *
          multipleEllipticGammaProduct ![sigma, tau]
            ((∑ i : Fin 2, ![sigma, tau] i) - z) = 1
    else
      ∀ z : ℂ,
        multipleEllipticGammaProduct ![sigma, tau]
            ((∑ i : Fin 2, ![sigma, tau] i) - z) =
          multipleEllipticGammaProduct ![sigma, tau] z

/-- Dependent upper-half-plane period triples carry a positive integral commensurability witness
whose finite residue-class factorization obeys additive reciprocal reflection. -/
structure EllipticGammaCommensurableReflectionCertificate
    (sigma tau : ℂ) where
  m : ℕ
  n : ℕ
  m_pos : 0 < m
  n_pos : 0 < n
  k : ℤ
  periodRelation : (m : ℂ) * sigma = (n : ℂ) * tau + (k : ℂ)
  factorizedReflection :
    ∀ z : ℂ,
      ellipticGammaCommensurableFamilyProduct
          (ellipticNome sigma) (ellipticNome tau) (ellipticNome sigma ^ m)
          (ellipticThetaCoordinate tau (sigma - z)) m n =
        (ellipticGammaCommensurableFamilyProduct
          (ellipticNome sigma) (ellipticNome tau) (ellipticNome sigma ^ m)
          (ellipticThetaCoordinate tau z) m n)⁻¹

theorem ellipticGammaRankTwoIndependentReflectionCertificate_iff
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    EllipticGammaRankTwoIndependentReflectionCertificate
        sigma tau hsigma htau ↔
      LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau) := by
  constructor
  · exact fun h => h.independent
  · intro hindependent
    have hperiods :=
      ellipticGamma_rankTwoPeriods_upperHalfPlane sigma tau hsigma htau
    have hminor : MultipleEllipticGammaHasRankThreeMinor ![sigma, tau] := by
      refine ⟨0, 1, Fin.zero_ne_one, ?_⟩
      simpa using hindependent
    have hphase :=
      multipleEllipticGamma_rankThreeMinor_reflectionHypertranscendenceUniversality
        ![sigma, tau] hperiods hminor
    exact
      { independent := hindependent
        productHypertranscendental := hphase.1
        logDerivativeHypertranscendental := hphase.2.1
        productReflection := hphase.2.2.1
        logDerivativeReflection := hphase.2.2.2.1
        reflectionProduct := hphase.2.2.2.2 }

theorem ellipticGammaCommensurableReflectionCertificate_nonempty_iff
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    Nonempty (EllipticGammaCommensurableReflectionCertificate sigma tau) ↔
      ¬ LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau) := by
  constructor
  · rintro ⟨hcert⟩
    exact
      (not_linearIndependent_ellipticGammaSourcePeriods_iff_positiveCommensurable
        sigma tau hsigma htau).2
        ⟨hcert.m, hcert.n, hcert.m_pos, hcert.n_pos, hcert.k,
          hcert.periodRelation⟩
  · intro hdep
    obtain ⟨m, n, hm, hn, k, hperiod⟩ :=
      (not_linearIndependent_ellipticGammaSourcePeriods_iff_positiveCommensurable
        sigma tau hsigma htau).1 hdep
    letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    refine ⟨?_⟩
    exact
      { m := m
        n := n
        m_pos := hm
        n_pos := hn
        k := k
        periodRelation := hperiod
        factorizedReflection := fun z =>
          ellipticGammaCommensurableFamilyProduct_additiveReflection
            (z := z) ⟨k, hperiod⟩ }

/-- **Elliptic-Gamma arithmetic reflection phase universality.** Every upper-half-plane period
pair lies in exactly one of two exhaustive phases: an independent hypertranscendental
multiple-elliptic-Gamma reflection phase, or a dependent positive-commensurable finite
factorization reflection phase. -/
theorem ellipticGamma_arithmeticReflectionPhaseUniversality
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    (EllipticGammaRankTwoIndependentReflectionCertificate sigma tau hsigma htau ∨
      Nonempty (EllipticGammaCommensurableReflectionCertificate sigma tau)) ∧
    ¬ (EllipticGammaRankTwoIndependentReflectionCertificate sigma tau hsigma htau ∧
      Nonempty (EllipticGammaCommensurableReflectionCertificate sigma tau)) := by
  have hi :=
    ellipticGammaRankTwoIndependentReflectionCertificate_iff
      sigma tau hsigma htau
  have hc :=
    ellipticGammaCommensurableReflectionCertificate_nonempty_iff
      sigma tau hsigma htau
  constructor
  · by_cases hindependent :
        LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)
    · exact Or.inl (hi.2 hindependent)
    · exact Or.inr (hc.2 hindependent)
  · rintro ⟨hindependent, hcommensurable⟩
    exact (hc.1 hcommensurable) (hi.1 hindependent)

end

end GaloisForLFunctions

