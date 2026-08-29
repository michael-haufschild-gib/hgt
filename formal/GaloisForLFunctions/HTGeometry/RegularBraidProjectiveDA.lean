import GaloisForLFunctions.HTGeometry.AnalyticMatrixGerm
import GaloisForLFunctions.HTGeometry.BraidYangBaxterSutherland
import GaloisForLFunctions.HTGeometry.SutherlandProjectiveAlgebraicity
import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbit
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval

/-!
# Regular difference-form braid families are projectively differentially algebraic

An analytic difference-form braid Yang--Baxter family with `Ř 0 = 1` has, after normalising by one
nonvanishing entry, entry ratios that satisfy algebraic differential equations over `ℂ(z)`.  The
proof is the Sutherland linearisation: differentiating the braid equation at the anchor makes the
derivative the unique solution of one explicit finite linear system whose coefficients are
polynomial in the normalised entries, and that system is invertible because it is the identity at
the anchor.

No classification of solutions is used and the state dimension is arbitrary.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher Matrix

noncomputable section

/-- Constants of the meromorphic field come from the rational coordinate field, on any chart. -/
theorem ratfuncToMero_C_eq_constToMero_on {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (c : ℂ) :
    ratfuncToMero U hUo hUc hUne hUinf (RatFunc.C c) = constToMero U c := by
  have hpc : polyToAnalytic U (Polynomial.C c) = constToAnalytic U c := by
    apply Subtype.ext
    have hfun : (fun z : ℂ => (Polynomial.C c).eval z) = fun _ : ℂ => c :=
      funext fun _ => Polynomial.eval_C
    show Germ.coeRingHom (Filter.principal U) (fun z : ℂ => (Polynomial.C c).eval z)
      = Germ.coeRingHom (Filter.principal U) (fun _ : ℂ => c)
    rw [hfun]
  rw [← RatFunc.algebraMap_C, ratfuncToMero_algebraMap_polynomial, polyToMero,
    RingHom.comp_apply, hpc]
  rfl

variable {κ : Type*} [DecidableEq κ] [Fintype κ]

section Braid

variable {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
  (hUinf : U.Infinite)

omit [DecidableEq κ] [Fintype κ] in
/-- The derivative family of an analytic matrix family is analytic. -/
theorem analyticOnNhd_of_hasMatrixDerivAt {Rf Rd : ℂ → Matrix (κ × κ) (κ × κ) ℂ}
    (hAn : ∀ i j, AnalyticOnNhd ℂ (fun t => Rf t i j) U)
    (hderiv : ∀ t, HasMatrixDerivAt Rf (Rd t) t) (i j : κ × κ) :
    AnalyticOnNhd ℂ (fun t => Rd t i j) U := by
  have hfun : (fun t => Rd t i j) = deriv (fun s => Rf s i j) := by
    funext t
    exact ((hderiv t) i j).deriv.symm
  rw [hfun]
  simpa using analyticOnNhd_iteratedDeriv (hAn i j) 1

omit [DecidableEq κ] [Fintype κ] in
/-- The normalised family is analytic where the anchor entry does not vanish. -/
theorem analyticOnNhd_normalized {Rf : ℂ → Matrix (κ × κ) (κ × κ) ℂ} (u₀ : κ)
    (hAn : ∀ i j, AnalyticOnNhd ℂ (fun t => Rf t i j) U)
    (hpiv : ∀ z ∈ U, Rf z (u₀, u₀) (u₀, u₀) ≠ 0) (i j : κ × κ) :
    AnalyticOnNhd ℂ (fun t => (Rf t (u₀, u₀) (u₀, u₀))⁻¹ * Rf t i j) U := by
  intro z hz
  have hfun : (fun t => (Rf t (u₀, u₀) (u₀, u₀))⁻¹ * Rf t i j)
      = ((fun t => Rf t i j) / fun t => Rf t (u₀, u₀) (u₀, u₀)) := by
    funext t
    rw [Pi.div_apply, div_eq_inv_mul]
  rw [hfun]
  exact ((hAn i j) z hz).div ((hAn (u₀, u₀) (u₀, u₀)) z hz) (hpiv z hz)

/-- The Sutherland identity transfers to the germ realisation of the family. -/
theorem sutherland_analyticMatrixElement {Rf Rd : ℂ → Matrix (κ × κ) (κ × κ) ℂ}
    (hAn : MatAnalyticOn U Rf) (hRd : MatAnalyticOn U Rd)
    (hsuth : ∀ t : ℂ, legLeft (Rf t) * legRight (Rd t) - legLeft (Rd t) * legRight (Rf t)
      = sutherlandSource (Rf t) (Rd 0)) :
    legLeft (analyticMatrixElement Rf hAn) * legRight (analyticMatrixElement Rd hRd)
        - legLeft (analyticMatrixElement Rd hRd) * legRight (analyticMatrixElement Rf hAn)
      = sutherlandSource (analyticMatrixElement Rf hAn)
          (analyticMatrixElement (fun _ => Rd 0) (MatAnalyticOn.const (Rd 0))) := by
  have hleft : analyticMatrixElement
        (fun t => legLeft (Rf t) * legRight (Rd t) - legLeft (Rd t) * legRight (Rf t))
        (((hAn.legLeft).mul hRd.legRight).sub ((hRd.legLeft).mul hAn.legRight))
      = legLeft (analyticMatrixElement Rf hAn) * legRight (analyticMatrixElement Rd hRd)
        - legLeft (analyticMatrixElement Rd hRd) * legRight (analyticMatrixElement Rf hAn) := by
    rw [analyticMatrixElement_sub (hAn.legLeft.mul hRd.legRight) (hRd.legLeft.mul hAn.legRight),
      analyticMatrixElement_mul hAn.legLeft hRd.legRight,
      analyticMatrixElement_mul hRd.legLeft hAn.legRight,
      analyticMatrixElement_legLeft hAn, analyticMatrixElement_legRight hRd,
      analyticMatrixElement_legLeft hRd, analyticMatrixElement_legRight hAn]
  have hright : analyticMatrixElement (fun t => sutherlandSource (Rf t) (Rd 0))
        ((((MatAnalyticOn.const (Rd 0)).legRight).mul (hAn.legLeft.mul hAn.legRight)).sub
          ((hAn.legLeft.mul hAn.legRight).mul ((MatAnalyticOn.const (Rd 0)).legLeft)))
      = sutherlandSource (analyticMatrixElement Rf hAn)
          (analyticMatrixElement (fun _ => Rd 0) (MatAnalyticOn.const (Rd 0))) := by
    simp only [sutherlandSource]
    rw [analyticMatrixElement_sub
        ((MatAnalyticOn.const (Rd 0)).legRight.mul (hAn.legLeft.mul hAn.legRight))
        ((hAn.legLeft.mul hAn.legRight).mul (MatAnalyticOn.const (Rd 0)).legLeft),
      analyticMatrixElement_mul (MatAnalyticOn.const (Rd 0)).legRight
        (hAn.legLeft.mul hAn.legRight),
      analyticMatrixElement_mul (hAn.legLeft.mul hAn.legRight)
        (MatAnalyticOn.const (Rd 0)).legLeft,
      analyticMatrixElement_mul hAn.legLeft hAn.legRight,
      analyticMatrixElement_legLeft hAn, analyticMatrixElement_legRight hAn,
      analyticMatrixElement_legRight (MatAnalyticOn.const (Rd 0)),
      analyticMatrixElement_legLeft (MatAnalyticOn.const (Rd 0))]
  rw [← hleft, ← hright]
  exact analyticMatrixElement_congr _ _ fun z _ => hsuth z

/-- **Regular difference-form braid families are projectively differentially algebraic.**  On a
nonempty connected open chart containing the anchor, on which the anchor entry does not vanish,
every entry ratio of an analytic difference-form braid Yang--Baxter family with `Ř 0 = 1` satisfies
an algebraic differential equation with complex polynomial coefficients.  The state dimension is
arbitrary and no classification of solutions is used. -/
theorem exists_jetRelation_normalized_of_regular_braid
    (u₀ : κ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUinf : U.Infinite) (hzero : (0 : ℂ) ∈ U)
    (Rf Rd : ℂ → Matrix (κ × κ) (κ × κ) ℂ)
    (hAn : MatAnalyticOn U Rf)
    (hderiv : ∀ t, HasMatrixDerivAt Rf (Rd t) t)
    (hbraid : ∀ x y : ℂ, legLeft (Rf x) * legRight (Rf (x + y)) * legLeft (Rf y)
      = legRight (Rf y) * legLeft (Rf (x + y)) * legRight (Rf x))
    (hreg : Rf 0 = 1)
    (hpiv : ∀ z ∈ U, Rf z (u₀, u₀) (u₀, u₀) ≠ 0)
    (a b : κ × κ) :
    ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ), P ≠ 0 ∧
      ∀ z ∈ U, MvPolynomial.eval
        (Fin.cons z fun j : Fin (n + 1) =>
          iteratedDeriv (j : ℕ)
            (fun t => (Rf t (u₀, u₀) (u₀, u₀))⁻¹ * Rf t a b) z) P = 0 := by
  classical
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  letI := meroFieldDifferential hUo hUc hUne
  letI := GaloisForLFunctions.ratFuncCoordinateDifferential
  letI : DifferentialAlgebra (RatFunc ℂ) (meroField U) :=
    ⟨fun r => meroField_deriv_ratfuncToMero_on hUo hUc hUne hUinf r⟩
  letI : CharZero (meroField U) :=
    charZero_of_injective_algebraMap (algebraMap (RatFunc ℂ) (meroField U)).injective
  have hρinj : Function.Injective (algebraMap (analyticSubring U) (meroField U)) :=
    IsFractionRing.injective (analyticSubring U) (meroField U)
  have hRdAn : MatAnalyticOn U Rd := fun i j =>
    analyticOnNhd_of_hasMatrixDerivAt hAn hderiv i j
  have hYAn : MatAnalyticOn U (fun t => (Rf t (u₀, u₀) (u₀, u₀))⁻¹ • Rf t) := fun i j =>
    analyticOnNhd_normalized u₀ hAn hpiv i j
  set Xsub := analyticMatrixElement Rf hAn with hXsub
  set Dsub := analyticMatrixElement Rd hRdAn with hDsub
  set Hsub := analyticMatrixElement (fun _ => Rd 0) (MatAnalyticOn.const (Rd 0)) with hHsub
  set Ysub := analyticMatrixElement (fun t => (Rf t (u₀, u₀) (u₀, u₀))⁻¹ • Rf t) hYAn with hYsub
  set ρ := algebraMap (analyticSubring U) (meroField U) with hρ
  -- the Sutherland identity in the meromorphic field
  have hsuthSub := sutherland_analyticMatrixElement hAn hRdAn
    (fun t => sutherland_of_braid Rf Rd hderiv hbraid hreg t)
  have hderivXm : entrywiseDeriv (Xsub.map ρ) = Dsub.map ρ := by
    refine Matrix.ext fun i j => ?_
    show (ρ (Xsub i j))′ = ρ (Dsub i j)
    rw [hρ, meroFieldDifferential_algebraMap hUo hUc hUne]
    exact congrArg _ (congrFun (congrFun (analyticMatrixElement_deriv hUo hAn hRdAn
      (fun t i j => ((hderiv t) i j).deriv.symm)) i) j).symm
  have hsuthM : legLeft (Xsub.map ρ) * legRight (entrywiseDeriv (Xsub.map ρ))
      - legLeft (entrywiseDeriv (Xsub.map ρ)) * legRight (Xsub.map ρ)
      = sutherlandSource (Xsub.map ρ) (Hsub.map ρ) := by
    rw [hderivXm, ← legLeft_map, ← legRight_map, ← legLeft_map, ← legRight_map,
      ← Matrix.map_mul, ← Matrix.map_mul,
      ← Matrix.map_sub (f := ⇑ρ) (fun x y => map_sub ρ x y), ← sutherlandSource_map]
    exact congrArg (fun M : Matrix (TripleIndex κ) (TripleIndex κ) (analyticSubring U) =>
      M.map ⇑ρ) hsuthSub
  -- the constant matrix comes from the rational coordinate field
  have hH : ∀ i j, (Hsub.map ρ) i j ∈ Set.range (algebraMap (RatFunc ℂ) (meroField U)) := by
    intro i j
    refine ⟨RatFunc.C (Rd 0 i j), ?_⟩
    show ratfuncToMero U hUo hUc hUne hUinf (RatFunc.C (Rd 0 i j)) = _
    rw [ratfuncToMero_C_eq_constToMero_on hUo hUc hUne hUinf]
    exact (analyticMeroElement_const U (Rd 0 i j)).symm
  -- the anchor entry is a nonzero meromorphic germ
  have hpivM : (Xsub.map ρ) (u₀, u₀) (u₀, u₀) ≠ 0 := by
    intro h
    have := (analyticMeroElement_eq_zero_iff (hAn (u₀, u₀) (u₀, u₀))).mp h 0 hzero
    exact hpiv 0 hzero this
  -- the normalised germ matrix is the projective normalisation
  have hYmEq : Ysub.map ρ = ((Xsub.map ρ) (u₀, u₀) (u₀, u₀))⁻¹ • (Xsub.map ρ) := by
    refine Matrix.ext fun i j => ?_
    have hmul : (Xsub.map ρ) (u₀, u₀) (u₀, u₀) * (Ysub.map ρ) i j = (Xsub.map ρ) i j := by
      show ρ (Xsub (u₀, u₀) (u₀, u₀)) * ρ (Ysub i j) = ρ (Xsub i j)
      rw [← map_mul]
      refine congrArg _ ?_
      exact analyticFunctionElement_mul_congr _ _ (hAn i j) fun z hz => by
        show Rf z (u₀, u₀) (u₀, u₀) * ((Rf z (u₀, u₀) (u₀, u₀))⁻¹ * Rf z i j) = Rf z i j
        field_simp [hpiv z hz]
    rw [Matrix.smul_apply, smul_eq_mul, ← hmul]
    field_simp [hpivM]
  -- the Sutherland endomorphism is invertible: at the anchor it is the identity
  have hdetSub : (sutherlandMatrix u₀ Ysub).det ≠ 0 := by
    intro h
    have hev := congrArg (analyticEvalAt U 0 hzero) h
    rw [map_zero, RingHom.map_det, RingHom.mapMatrix_apply, sutherlandMatrix_map, hYsub,
      analyticMatrixElement_map_eval] at hev
    rw [show ((Rf 0 (u₀, u₀) (u₀, u₀))⁻¹ • Rf 0) = 1 by rw [hreg]; simp] at hev
    rw [sutherlandMatrix_one, Matrix.det_one] at hev
    exact one_ne_zero hev
  have hdetM : (sutherlandMatrix u₀
      (((Xsub.map ρ) (u₀, u₀) (u₀, u₀))⁻¹ • (Xsub.map ρ))).det ≠ 0 := by
    rw [← hYmEq, ← sutherlandMatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    intro h
    exact hdetSub (hρinj (by simpa using h))
  -- the abstract theorem
  have hDA := differentialAlgebraicOver_normalized_entry_of_sutherland u₀
    (Xsub.map ρ) (Hsub.map ρ) hH hpivM hsuthM hdetM a b
  have hentry : ((Xsub.map ρ) (u₀, u₀) (u₀, u₀))⁻¹ * (Xsub.map ρ) a b
      = analyticMeroElement (fun t => (Rf t (u₀, u₀) (u₀, u₀))⁻¹ * Rf t a b) (hYAn a b) := by
    have := congrFun (congrFun hYmEq a) b
    rw [Matrix.smul_apply, smul_eq_mul] at this
    exact this.symm
  rw [hentry] at hDA
  exact (differentialAlgebraicOver_analyticMeroElement_iff hUo hUc hUne hUinf
    (hYAn a b)).mp hDA

end Braid

end

end GaloisForLFunctions.HTGeometry
