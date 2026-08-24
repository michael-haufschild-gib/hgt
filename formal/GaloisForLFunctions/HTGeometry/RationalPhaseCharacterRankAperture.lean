import GaloisForLFunctions.HTGeometry.RationalDiagonalJetDependence
import GaloisForLFunctions.HTGeometry.AnalyticRationalCharacterStabilizer
import GaloisForLFunctions.HTGeometry.LocalizationDerivationMap
import GaloisForLFunctions.HTGeometry.LocalInverseHypertranscendence
import GaloisForLFunctions.HTGeometry.PolynomialPhaseAperture
import Mathlib.RingTheory.Localization.Away.Basic

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Set Filter Topology
open Bottcher

noncomputable section

set_option maxHeartbeats 600000

variable {r : ℕ}

/-- Localization of the rational-torus polynomial ring away from one
denominator. -/
abbrev RationalPhaseAway (Q : MvPolynomial (Fin r) ℂ) := Localization.Away Q

/-- Square-zero graph of the diagonal polynomial derivation, valued in the
principal localization. -/
def rationalPhaseAwayGraphHom (omega : Fin r → ℝ)
    (Q : MvPolynomial (Fin r) ℂ) :
    MvPolynomial (Fin r) ℂ →+*
      TrivSqZeroExt (RationalPhaseAway Q) (RationalPhaseAway Q) where
  toFun P :=
    (algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) P,
      algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q)
        (rationalDiagonalPolynomialDerivation omega P))
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' := by intro P R; ext <;> simp
  map_mul' := by
    intro P R
    apply TrivSqZeroExt.ext
    · simp
    · simp [Derivation.leibniz, mul_comm]

theorem rationalPhaseAwayGraphHom_isUnit
    (omega : Fin r → ℝ) (Q : MvPolynomial (Fin r) ℂ)
    (s : Submonoid.powers Q) : IsUnit (rationalPhaseAwayGraphHom omega Q s.1) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  exact IsLocalization.map_units (RationalPhaseAway Q) s

/-- Square-zero graph extended through the denominator localization. -/
def rationalPhaseAwayGraphLift (omega : Fin r → ℝ)
    (Q : MvPolynomial (Fin r) ℂ) :
    RationalPhaseAway Q →+*
      TrivSqZeroExt (RationalPhaseAway Q) (RationalPhaseAway Q) :=
  IsLocalization.lift (rationalPhaseAwayGraphHom_isUnit omega Q)

@[simp] theorem rationalPhaseAwayGraphLift_algebraMap
    (omega : Fin r → ℝ) (Q P : MvPolynomial (Fin r) ℂ) :
    rationalPhaseAwayGraphLift omega Q
        (algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) P) =
      rationalPhaseAwayGraphHom omega Q P := by
  exact RingHom.congr_fun
    (IsLocalization.lift_comp (rationalPhaseAwayGraphHom_isUnit omega Q)) P

theorem rationalPhaseAwayGraphLift_fst
    (omega : Fin r → ℝ) (Q : MvPolynomial (Fin r) ℂ)
    (x : RationalPhaseAway Q) :
    (rationalPhaseAwayGraphLift omega Q x).fst = x := by
  let fst : TrivSqZeroExt (RationalPhaseAway Q) (RationalPhaseAway Q) →+*
      RationalPhaseAway Q :=
    { toFun := TrivSqZeroExt.fst
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  let f : RationalPhaseAway Q →+* RationalPhaseAway Q :=
    fst.comp (rationalPhaseAwayGraphLift omega Q)
  have hf : f.comp (algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q)) =
      (RingHom.id (RationalPhaseAway Q)).comp
        (algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q)) := by
    apply RingHom.ext
    intro P
    change (rationalPhaseAwayGraphLift omega Q
        (algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) P)).fst =
      algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) P
    rw [rationalPhaseAwayGraphLift_algebraMap]
    rfl
  have heq : f = RingHom.id (RationalPhaseAway Q) :=
    IsLocalization.ringHom_ext (Submonoid.powers Q) hf
  simpa [f, fst] using RingHom.congr_fun heq x

/-- Quotient-rule endofunction on the principal localization. -/
def rationalPhaseAwayDerivation (omega : Fin r → ℝ)
    (Q : MvPolynomial (Fin r) ℂ) :
    RationalPhaseAway Q → RationalPhaseAway Q := fun x =>
  (rationalPhaseAwayGraphLift omega Q x).snd

@[simp] theorem rationalPhaseAwayDerivation_algebraMap
    (omega : Fin r → ℝ) (Q P : MvPolynomial (Fin r) ℂ) :
    rationalPhaseAwayDerivation omega Q
        (algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) P) =
      algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q)
        (rationalDiagonalPolynomialDerivation omega P) := by
  rw [rationalPhaseAwayDerivation,
    rationalPhaseAwayGraphLift_algebraMap]
  rfl

/-- The quotient-rule graph is transported by every ring hom whose target
derivation has the same values on polynomial coordinates. -/
theorem rationalPhaseAwayGraphLift_ringHom_commutes_of_base
    {T : Type*} [CommRing T]
    (omega : Fin r → ℝ) (Q : MvPolynomial (Fin r) ℂ)
    (targetGraph : T →+* TrivSqZeroExt T T)
    (htargetFst : ∀ z, (targetGraph z).fst = z)
    (phi : RationalPhaseAway Q →+* T)
    (hbase : ∀ P : MvPolynomial (Fin r) ℂ,
      phi (algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q)
        (rationalDiagonalPolynomialDerivation omega P)) =
      (targetGraph
        (phi (algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) P))).snd)
    (x : RationalPhaseAway Q) :
    phi (rationalPhaseAwayDerivation omega Q x) = (targetGraph (phi x)).snd := by
  let lhs : RationalPhaseAway Q →+* TrivSqZeroExt T T :=
    { toFun := fun z =>
        (phi z, phi (rationalPhaseAwayDerivation omega Q z))
      map_zero' := by ext <;> simp [rationalPhaseAwayDerivation]
      map_one' := by ext <;> simp [rationalPhaseAwayDerivation]
      map_add' := by intro a b; ext <;> simp [rationalPhaseAwayDerivation]
      map_mul' := by
        intro a b
        apply TrivSqZeroExt.ext
        · simp
        · simp [rationalPhaseAwayDerivation, rationalPhaseAwayGraphLift_fst] }
  let rhs : RationalPhaseAway Q →+* TrivSqZeroExt T T :=
    targetGraph.comp phi
  have heq : lhs = rhs := by
    apply IsLocalization.ringHom_ext (Submonoid.powers Q)
    apply RingHom.ext
    intro P
    apply TrivSqZeroExt.ext
    · change phi (algebraMap (MvPolynomial (Fin r) ℂ)
          (RationalPhaseAway Q) P) =
        (targetGraph (phi (algebraMap (MvPolynomial (Fin r) ℂ)
          (RationalPhaseAway Q) P))).fst
      exact (htargetFst _).symm
    · change phi (rationalPhaseAwayDerivation omega Q
          (algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) P)) =
        (targetGraph (phi (algebraMap (MvPolynomial (Fin r) ℂ)
          (RationalPhaseAway Q) P))).snd
      rw [rationalPhaseAwayDerivation_algebraMap]
      exact hbase P
  have hx := RingHom.congr_fun heq x
  exact congrArg TrivSqZeroExt.snd hx

/-- Map from a denominator localization to the full rational function field. -/
def rationalPhaseAwayToFraction (Q : MvPolynomial (Fin r) ℂ) (hQ : Q ≠ 0) :
    RationalPhaseAway Q →ₐ[ℂ] FractionRing (MvPolynomial (Fin r) ℂ) :=
  let phi : MvPolynomial (Fin r) ℂ →ₐ[ℂ]
      FractionRing (MvPolynomial (Fin r) ℂ) :=
    { toRingHom := algebraMap (MvPolynomial (Fin r) ℂ)
        (FractionRing (MvPolynomial (Fin r) ℂ))
      commutes' := fun _ => rfl }
  IsLocalization.Away.liftAlgHom Q (f := phi) (by
    change IsUnit (algebraMap (MvPolynomial (Fin r) ℂ)
      (FractionRing (MvPolynomial (Fin r) ℂ)) Q)
    rw [isUnit_iff_ne_zero]
    intro hzero
    apply hQ
    apply IsFractionRing.injective (MvPolynomial (Fin r) ℂ)
      (FractionRing (MvPolynomial (Fin r) ℂ))
    simpa using hzero)

@[simp] theorem rationalPhaseAwayToFraction_algebraMap
    (Q : MvPolynomial (Fin r) ℂ) (hQ : Q ≠ 0)
    (P : MvPolynomial (Fin r) ℂ) :
    rationalPhaseAwayToFraction Q hQ
        (algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) P) =
      algebraMap (MvPolynomial (Fin r) ℂ)
        (FractionRing (MvPolynomial (Fin r) ℂ)) P := by
  simp [rationalPhaseAwayToFraction, IsLocalization.Away.liftAlgHom,
    IsLocalization.Away.lift_eq]

/-- The canonical map from a nontrivial principal localization into the
fraction field is injective. -/
theorem rationalPhaseAwayToFraction_injective
    (Q : MvPolynomial (Fin r) ℂ) (hQ : Q ≠ 0) :
    Function.Injective (rationalPhaseAwayToFraction Q hQ) := by
  intro x y hxy
  have hzero : rationalPhaseAwayToFraction Q hQ (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers Q) (x - y)
  change (x - y) *
      algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) (s : _) =
    algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) a at hs
  have haMap : algebraMap (MvPolynomial (Fin r) ℂ)
      (FractionRing (MvPolynomial (Fin r) ℂ)) a = 0 := by
    have h := congrArg (rationalPhaseAwayToFraction Q hQ) hs
    rw [map_mul, hzero, zero_mul,
      rationalPhaseAwayToFraction_algebraMap] at h
    exact h.symm
  have ha : a = 0 := by
    apply IsFractionRing.injective (MvPolynomial (Fin r) ℂ)
      (FractionRing (MvPolynomial (Fin r) ℂ))
    simpa using haMap
  rw [ha, map_zero] at hs
  obtain ⟨u, hu⟩ := IsLocalization.map_units (RationalPhaseAway Q) s
  have hmul : (u : RationalPhaseAway Q) * (x - y) =
      (u : RationalPhaseAway Q) * 0 := by simpa [hu, mul_comm] using hs
  exact sub_eq_zero.mp ((Units.mul_right_inj u).mp hmul)

/-- The principal-localization map to the rational function field preserves
the diagonal derivation. -/
theorem rationalPhaseAwayToFraction_derivation
    (omega : Fin r → ℝ) (Q : MvPolynomial (Fin r) ℂ) (hQ : Q ≠ 0)
    (x : RationalPhaseAway Q) :
    rationalPhaseAwayToFraction Q hQ (rationalPhaseAwayDerivation omega Q x) =
      rationalDiagonalDerivation omega (rationalPhaseAwayToFraction Q hQ x) := by
  let D₀ : Derivation ℂ (MvPolynomial (Fin r) ℂ)
      (FractionRing (MvPolynomial (Fin r) ℂ)) :=
    (Algebra.linearMap (MvPolynomial (Fin r) ℂ)
      (FractionRing (MvPolynomial (Fin r) ℂ))).compDer
        (rationalDiagonalPolynomialDerivation omega)
  let graph := fractionRingDerivationGraphLift D₀
  have h := rationalPhaseAwayGraphLift_ringHom_commutes_of_base
    omega Q graph (fractionRingDerivationGraphLift_fst D₀)
    (rationalPhaseAwayToFraction Q hQ).toRingHom (fun P => by
      change rationalPhaseAwayToFraction Q hQ
          (algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q)
            (rationalDiagonalPolynomialDerivation omega P)) =
        (fractionRingDerivationGraphLift D₀
          (rationalPhaseAwayToFraction Q hQ
            (algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) P))).snd
      rw [rationalPhaseAwayToFraction_algebraMap,
        rationalPhaseAwayToFraction_algebraMap,
        fractionRingDerivationGraphLift_algebraMap]
      rfl) x
  simpa [graph, D₀, rationalDiagonalDerivation,
    fractionRingDerivation_apply] using h

/-! ### Analytic realization on the phase strip -/

variable {rho omega : Fin r → ℝ}

local instance phaseAnalyticAlgebra :
    Algebra ℂ (analyticSubring (phaseStrip rho omega)) :=
  (constToAnalytic (phaseStrip rho omega)).toAlgebra

def phaseCoordinateAnalytic (i : Fin r) :
    analyticSubring (phaseStrip rho omega) :=
  analyticFunctionElement (fun t => phasePoint omega t i) (by
    simpa [phasePoint] using
      (analyticOnNhd_const.mul analyticOnNhd_id).cexp)

/-- Polynomial evaluation on the phase coordinates, as analytic germs on the
phase strip. -/
def phasePolynomialAnalyticHom :
    MvPolynomial (Fin r) ℂ →ₐ[ℂ] analyticSubring (phaseStrip rho omega) :=
  MvPolynomial.aeval (phaseCoordinateAnalytic (rho := rho) (omega := omega))

@[simp] theorem phasePolynomialAnalyticHom_coe
    (P : MvPolynomial (Fin r) ℂ) :
    ((phasePolynomialAnalyticHom (rho := rho) (omega := omega) P :
        analyticSubring (phaseStrip rho omega)) :
      Germ (Filter.principal (phaseStrip rho omega)) ℂ) =
    ((fun t => MvPolynomial.eval (phasePoint omega t) P : ℂ → ℂ) :
      Germ (Filter.principal (phaseStrip rho omega)) ℂ) := by
  rw [phasePolynomialAnalyticHom, MvPolynomial.aeval_def]
  exact eval₂_analyticFunctionElement_coe
    (U := phaseStrip rho omega)
    (fun i t => phasePoint omega t i)
    (fun i => by
      simpa [phaseCoordinateAnalytic, phasePoint] using
        (analyticOnNhd_const.mul analyticOnNhd_id).cexp) P

theorem rationalDiagonalPolynomialDerivation_eq_diagonalPolynomialDerivation
    (P : MvPolynomial (Fin r) ℂ) :
    rationalDiagonalPolynomialDerivation omega P =
      diagonalPolynomialDerivation omega P := by
  have h := GaloisForLFunctions.derivation_aeval_eq_sum_pderiv
    (rationalDiagonalPolynomialDerivation omega)
    (MvPolynomial.X : Fin r → MvPolynomial (Fin r) ℂ) P
  simpa [diagonalPolynomialDerivation, rationalDiagonalPolynomialDerivation,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- Time differentiation of polynomial phase evaluation is the diagonal
polynomial derivation. -/
theorem analyticSubringDerivation_phasePolynomialAnalyticHom
    (P : MvPolynomial (Fin r) ℂ) :
    analyticSubringDerivation (isOpen_phaseStrip rho omega)
        (phasePolynomialAnalyticHom (rho := rho) (omega := omega) P) =
      phasePolynomialAnalyticHom (rho := rho) (omega := omega)
        (rationalDiagonalPolynomialDerivation omega P) := by
  change analyticSubringDeriv (isOpen_phaseStrip rho omega)
      (phasePolynomialAnalyticHom (rho := rho) (omega := omega) P) = _
  apply Subtype.ext
  rw [analyticSubringDeriv_coe, phasePolynomialAnalyticHom_coe,
    analyticGermDeriv_coe, phasePolynomialAnalyticHom_coe, Germ.coe_eq]
  refine eventually_principal.mpr fun t ht => ?_
  have hderiv := deriv_phaseFunction
    (ρ := rho) (omega := omega)
    (F := polynomialPhaseObservable P)
    (analyticOnNhd_polynomialPhaseObservable P (polyannulus rho)) ht
  rw [torusDerivation_polynomialPhaseObservable] at hderiv
  rw [rationalDiagonalPolynomialDerivation_eq_diagonalPolynomialDerivation]
  exact hderiv

/-- Square-zero graph of ordinary differentiation on analytic germs. -/
def analyticSubringDerivativeGraph :
    analyticSubring (phaseStrip rho omega) →+*
      TrivSqZeroExt (analyticSubring (phaseStrip rho omega))
        (analyticSubring (phaseStrip rho omega)) where
  toFun a := (a, analyticSubringDeriv (isOpen_phaseStrip rho omega) a)
  map_zero' := by ext <;> simp [analyticSubringDeriv_zero]
  map_one' := by
    apply TrivSqZeroExt.ext
    · rfl
    · apply Subtype.ext
      change ((deriv (fun _ : ℂ => 1) : ℂ → ℂ) :
        Germ (Filter.principal (phaseStrip rho omega)) ℂ) = 0
      rw [deriv_const']
      rfl
  map_add' := by
    intro a b
    apply TrivSqZeroExt.ext
    · rfl
    · exact analyticSubringDeriv_add (isOpen_phaseStrip rho omega) a b
  map_mul' := by
    intro a b
    apply TrivSqZeroExt.ext
    · rfl
    · simp [analyticSubringDeriv_mul, mul_comm]

@[simp] theorem analyticSubringDerivativeGraph_fst
    (a : analyticSubring (phaseStrip rho omega)) :
    (analyticSubringDerivativeGraph (rho := rho) (omega := omega) a).fst = a := rfl

theorem phasePolynomialAnalyticHom_isUnit
    (Q : MvPolynomial (Fin r) ℂ)
    (hQ : ∀ z ∈ polyannulus rho, MvPolynomial.aeval z Q ≠ 0) :
    IsUnit (phasePolynomialAnalyticHom (rho := rho) (omega := omega) Q) := by
  let f : ℂ → ℂ := fun t => MvPolynomial.eval (phasePoint omega t) Q
  have hf : AnalyticOnNhd ℂ f (phaseStrip rho omega) := by
    change AnalyticOnNhd ℂ
      (phaseFunction omega (polynomialPhaseObservable Q)) (phaseStrip rho omega)
    exact analyticOnNhd_phaseFunction
      (omega := omega)
      (analyticOnNhd_polynomialPhaseObservable Q (polyannulus rho))
  have hf0 : ∀ t ∈ phaseStrip rho omega, f t ≠ 0 := by
    intro t ht
    simpa [f, MvPolynomial.aeval_def] using hQ (phasePoint omega t)
      (phasePoint_mem_polyannulus ht)
  let invElem : analyticSubring (phaseStrip rho omega) :=
    analyticFunctionElement (fun t => (f t)⁻¹)
      (fun t ht => (hf t ht).inv (hf0 t ht))
  have hvalInv :
      phasePolynomialAnalyticHom (rho := rho) (omega := omega) Q * invElem = 1 := by
    apply Subtype.ext
    change ((phasePolynomialAnalyticHom (rho := rho) (omega := omega) Q :
          analyticSubring (phaseStrip rho omega)) :
        Germ (Filter.principal (phaseStrip rho omega)) ℂ) *
        ((invElem : analyticSubring (phaseStrip rho omega)) :
          Germ (Filter.principal (phaseStrip rho omega)) ℂ) = 1
    rw [phasePolynomialAnalyticHom_coe]
    change ((f : ℂ → ℂ) : Germ (Filter.principal (phaseStrip rho omega)) ℂ) *
        (((fun t => (f t)⁻¹) : ℂ → ℂ) :
          Germ (Filter.principal (phaseStrip rho omega)) ℂ) = 1
    rw [← Germ.coe_mul, ← Germ.coe_one, Germ.coe_eq]
    exact eventually_principal.mpr fun t ht => mul_inv_cancel₀ (hf0 t ht)
  have hinvVal : invElem *
      phasePolynomialAnalyticHom (rho := rho) (omega := omega) Q = 1 := by
    rw [mul_comm]
    exact hvalInv
  exact ⟨⟨phasePolynomialAnalyticHom (rho := rho) (omega := omega) Q,
    invElem, hvalInv, hinvVal⟩, rfl⟩

/-- Analytic realization of the denominator localization on the phase strip. -/
def rationalPhaseAwayToAnalytic
    (Q : MvPolynomial (Fin r) ℂ)
    (hQ : ∀ z ∈ polyannulus rho, MvPolynomial.aeval z Q ≠ 0) :
    RationalPhaseAway Q →ₐ[ℂ] analyticSubring (phaseStrip rho omega) :=
  IsLocalization.Away.liftAlgHom Q
    (f := phasePolynomialAnalyticHom (rho := rho) (omega := omega))
    (phasePolynomialAnalyticHom_isUnit Q hQ)

@[simp] theorem rationalPhaseAwayToAnalytic_algebraMap
    (Q : MvPolynomial (Fin r) ℂ)
    (hQ : ∀ z ∈ polyannulus rho, MvPolynomial.aeval z Q ≠ 0)
    (P : MvPolynomial (Fin r) ℂ) :
    rationalPhaseAwayToAnalytic Q hQ
        (algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) P) =
      phasePolynomialAnalyticHom (rho := rho) (omega := omega) P := by
  simp [rationalPhaseAwayToAnalytic, IsLocalization.Away.liftAlgHom,
    IsLocalization.Away.lift_eq]

/-- Analytic realization preserves the quotient-rule derivation. -/
theorem rationalPhaseAwayToAnalytic_derivation
    (Q : MvPolynomial (Fin r) ℂ)
    (hQ : ∀ z ∈ polyannulus rho, MvPolynomial.aeval z Q ≠ 0)
    (x : RationalPhaseAway Q) :
    rationalPhaseAwayToAnalytic Q hQ (rationalPhaseAwayDerivation omega Q x) =
      analyticSubringDeriv (isOpen_phaseStrip rho omega)
        (rationalPhaseAwayToAnalytic Q hQ x) := by
  have h := rationalPhaseAwayGraphLift_ringHom_commutes_of_base
    omega Q (analyticSubringDerivativeGraph (rho := rho) (omega := omega))
      analyticSubringDerivativeGraph_fst
    (rationalPhaseAwayToAnalytic Q hQ).toRingHom (fun P => by
      change rationalPhaseAwayToAnalytic Q hQ
          (algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q)
            (rationalDiagonalPolynomialDerivation omega P)) =
        analyticSubringDeriv (isOpen_phaseStrip rho omega)
          (rationalPhaseAwayToAnalytic Q hQ
            (algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) P))
      rw [rationalPhaseAwayToAnalytic_algebraMap,
        rationalPhaseAwayToAnalytic_algebraMap]
      exact (analyticSubringDerivation_phasePolynomialAnalyticHom P).symm) x
  exact h

/-- A derivation-preserving map preserves every iterate. -/
theorem map_iterate_rationalPhaseAwayDerivation
    {T : Type*} (phi : RationalPhaseAway Q → T) (D : T → T)
    (hcomm : ∀ x, phi (rationalPhaseAwayDerivation omega Q x) = D (phi x))
    (n : ℕ) (x : RationalPhaseAway Q) :
    phi ((rationalPhaseAwayDerivation omega Q)^[n] x) = D^[n] (phi x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n hn =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hn, hcomm]

theorem rationalPhaseAwayToFraction_iterate
    (Q : MvPolynomial (Fin r) ℂ) (hQ : Q ≠ 0)
    (n : ℕ) (x : RationalPhaseAway Q) :
    rationalPhaseAwayToFraction Q hQ
        ((rationalPhaseAwayDerivation omega Q)^[n] x) =
      (rationalDiagonalDerivation omega)^[n]
        (rationalPhaseAwayToFraction Q hQ x) :=
  map_iterate_rationalPhaseAwayDerivation _ _
    (rationalPhaseAwayToFraction_derivation omega Q hQ) n x

theorem rationalPhaseAwayToAnalytic_iterate
    (Q : MvPolynomial (Fin r) ℂ)
    (hQ : ∀ z ∈ polyannulus rho, MvPolynomial.aeval z Q ≠ 0)
    (n : ℕ) (x : RationalPhaseAway Q) :
    rationalPhaseAwayToAnalytic Q hQ
        ((rationalPhaseAwayDerivation omega Q)^[n] x) =
      (analyticSubringDeriv (isOpen_phaseStrip rho omega))^[n]
        (rationalPhaseAwayToAnalytic Q hQ x) :=
  map_iterate_rationalPhaseAwayDerivation _ _
    (rationalPhaseAwayToAnalytic_derivation Q hQ) n x

/-! ### The presented rational observable -/

/-- The fraction `P / Q` inside the principal localization at `Q`. -/
def rationalPhaseAwayElement (P Q : MvPolynomial (Fin r) ℂ) :
    RationalPhaseAway Q :=
  algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) P *
    IsLocalization.Away.invSelf Q

theorem rationalPhaseAwayToFraction_element
    (P Q : MvPolynomial (Fin r) ℂ) (hQ : Q ≠ 0) :
    rationalPhaseAwayToFraction Q hQ (rationalPhaseAwayElement P Q) =
      MvPolynomial.aeval
          (rationalTorusCoordinate (C := ℂ) (r := r)) P /
        MvPolynomial.aeval
          (rationalTorusCoordinate (C := ℂ) (r := r)) Q := by
  let qF := algebraMap (MvPolynomial (Fin r) ℂ)
    (FractionRing (MvPolynomial (Fin r) ℂ)) Q
  have hqF : qF ≠ 0 := by
    intro hzero
    apply hQ
    apply IsFractionRing.injective (MvPolynomial (Fin r) ℂ)
      (FractionRing (MvPolynomial (Fin r) ℂ))
    simpa [qF] using hzero
  have hmul := congrArg (rationalPhaseAwayToFraction Q hQ)
    (IsLocalization.Away.mul_invSelf Q :
      algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) Q *
        IsLocalization.Away.invSelf Q = 1)
  rw [map_mul, map_one, rationalPhaseAwayToFraction_algebraMap] at hmul
  have hinv : rationalPhaseAwayToFraction Q hQ
      (IsLocalization.Away.invSelf Q) = qF⁻¹ := by
    calc
      rationalPhaseAwayToFraction Q hQ (IsLocalization.Away.invSelf Q) =
          (qF⁻¹ * qF) *
            rationalPhaseAwayToFraction Q hQ (IsLocalization.Away.invSelf Q) := by
              rw [inv_mul_cancel₀ hqF, one_mul]
      _ = qF⁻¹ *
          (qF * rationalPhaseAwayToFraction Q hQ
            (IsLocalization.Away.invSelf Q)) := by ring
      _ = qF⁻¹ := by rw [hmul]; simp
  rw [rationalPhaseAwayElement, map_mul,
    rationalPhaseAwayToFraction_algebraMap, hinv, div_eq_mul_inv,
    aeval_rationalTorusCoordinate_eq_algebraMap,
    aeval_rationalTorusCoordinate_eq_algebraMap]

theorem rationalPhaseAwayToAnalytic_element_eq
    (hF : AnalyticOnNhd ℂ F (polyannulus rho))
    (P Q : MvPolynomial (Fin r) ℂ)
    (hQ : ∀ z ∈ polyannulus rho, MvPolynomial.aeval z Q ≠ 0)
    (hrep : ∀ z ∈ polyannulus rho,
      F z = MvPolynomial.aeval z P / MvPolynomial.aeval z Q) :
    rationalPhaseAwayToAnalytic Q hQ (rationalPhaseAwayElement P Q) =
      analyticFunctionElement (phaseFunction omega F)
        (analyticOnNhd_phaseFunction hF) := by
  let phi := rationalPhaseAwayToAnalytic (rho := rho) (omega := omega) Q hQ
  obtain ⟨u, hu⟩ := phasePolynomialAnalyticHom_isUnit
    (rho := rho) (omega := omega) Q hQ
  apply (Units.mul_right_inj u).mp
  change (u : _) * phi (rationalPhaseAwayElement P Q) =
    (u : _) * analyticFunctionElement (phaseFunction omega F)
      (analyticOnNhd_phaseFunction hF)
  rw [hu]
  have hmul := congrArg phi
    (IsLocalization.Away.mul_invSelf Q :
      algebraMap (MvPolynomial (Fin r) ℂ) (RationalPhaseAway Q) Q *
        IsLocalization.Away.invSelf Q = 1)
  rw [map_mul, map_one, rationalPhaseAwayToAnalytic_algebraMap] at hmul
  have hleft : phi (rationalPhaseAwayElement P Q) *
      phasePolynomialAnalyticHom (rho := rho) (omega := omega) Q =
    phasePolynomialAnalyticHom (rho := rho) (omega := omega) P := by
    rw [rationalPhaseAwayElement, map_mul,
      rationalPhaseAwayToAnalytic_algebraMap]
    calc
      phasePolynomialAnalyticHom (rho := rho) (omega := omega) P *
            phi (IsLocalization.Away.invSelf Q) *
          phasePolynomialAnalyticHom (rho := rho) (omega := omega) Q =
        phasePolynomialAnalyticHom (rho := rho) (omega := omega) P *
          (phasePolynomialAnalyticHom (rho := rho) (omega := omega) Q *
            phi (IsLocalization.Away.invSelf Q)) := by ring
      _ = phasePolynomialAnalyticHom (rho := rho) (omega := omega) P := by
        rw [hmul, mul_one]
  rw [mul_comm _ (phi (rationalPhaseAwayElement P Q)), hleft,
    mul_comm _ (analyticFunctionElement (phaseFunction omega F)
      (analyticOnNhd_phaseFunction hF))]
  symm
  apply Subtype.ext
  change (((analyticFunctionElement (phaseFunction omega F)
          (analyticOnNhd_phaseFunction hF) :
        analyticSubring (phaseStrip rho omega)) :
      Germ (Filter.principal (phaseStrip rho omega)) ℂ) *
      ((phasePolynomialAnalyticHom (rho := rho) (omega := omega) Q :
        analyticSubring (phaseStrip rho omega)) :
      Germ (Filter.principal (phaseStrip rho omega)) ℂ)) =
    ((phasePolynomialAnalyticHom (rho := rho) (omega := omega) P :
      analyticSubring (phaseStrip rho omega)) :
      Germ (Filter.principal (phaseStrip rho omega)) ℂ)
  rw [analyticFunctionElement_coe, phasePolynomialAnalyticHom_coe,
    phasePolynomialAnalyticHom_coe, ← Germ.coe_mul, Germ.coe_eq]
  exact eventually_principal.mpr fun t ht => by
    have hz := phasePoint_mem_polyannulus ht
    change F (phasePoint omega t) *
        MvPolynomial.eval (phasePoint omega t) Q =
      MvPolynomial.eval (phasePoint omega t) P
    rw [hrep (phasePoint omega t) hz]
    simpa [MvPolynomial.aeval_def] using
      div_mul_cancel₀ (MvPolynomial.eval (phasePoint omega t) P)
        (hQ (phasePoint omega t) hz)

theorem iterate_analyticSubringDeriv_analyticFunctionElement
    {U : Set ℂ} (hUo : IsOpen U) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) (n : ℕ) :
    (analyticSubringDeriv hUo)^[n] (analyticFunctionElement f hf) =
      analyticJetElement f hf n := by
  induction n with
  | zero => exact (analyticJetElement_zero f hf).symm
  | succ n hn =>
      rw [Function.iterate_succ_apply', hn,
        analyticSubringDeriv_analyticJetElement]

/-- A symbolic polynomial relation among localized rational jets becomes the
same pointwise relation among analytic time jets throughout the phase strip. -/
theorem rationalPhase_relation_on_strip_of_symbolic
    (hρ : ∀ i, 0 < rho i)
    (hF : AnalyticOnNhd ℂ F (polyannulus rho))
    (P Q : MvPolynomial (Fin r) ℂ)
    (hQ : ∀ z ∈ polyannulus rho, MvPolynomial.aeval z Q ≠ 0)
    (hrep : ∀ z ∈ polyannulus rho,
      F z = MvPolynomial.aeval z P / MvPolynomial.aeval z Q)
    {n : ℕ} (H : MvPolynomial (Fin (n + 1)) ℂ)
    (hrel : MvPolynomial.aeval
      (fun j : Fin (n + 1) =>
        (rationalDiagonalDerivation omega)^[(j : ℕ)]
          (MvPolynomial.aeval
              (rationalTorusCoordinate (C := ℂ) (r := r)) P /
            MvPolynomial.aeval
              (rationalTorusCoordinate (C := ℂ) (r := r)) Q)) H = 0) :
    ∀ t ∈ phaseStrip rho omega,
      MvPolynomial.eval
        (fun j : Fin (n + 1) =>
          iteratedDeriv (j : ℕ) (phaseFunction omega F) t) H = 0 := by
  classical
  have hQ0 : Q ≠ 0 := by
    intro hzero
    have h := hQ (fun _ => (1 : ℂ)) (one_mem_polyannulus hρ)
    rw [hzero, map_zero] at h
    exact h rfl
  let x₀ : RationalPhaseAway Q := rationalPhaseAwayElement P Q
  let y : Fin (n + 1) → RationalPhaseAway Q := fun j =>
    (rationalPhaseAwayDerivation omega Q)^[(j : ℕ)] x₀
  have hfrac : rationalPhaseAwayToFraction Q hQ0
      (MvPolynomial.aeval y H) = 0 := by
    have hcomp := MvPolynomial.comp_aeval_apply y
      (rationalPhaseAwayToFraction Q hQ0) H
    rw [show (fun j => rationalPhaseAwayToFraction Q hQ0 (y j)) =
        (fun j : Fin (n + 1) =>
          (rationalDiagonalDerivation omega)^[(j : ℕ)]
            (MvPolynomial.aeval
                (rationalTorusCoordinate (C := ℂ) (r := r)) P /
              MvPolynomial.aeval
                (rationalTorusCoordinate (C := ℂ) (r := r)) Q)) by
      funext j
      simp only [y, x₀]
      rw [rationalPhaseAwayToFraction_iterate,
        rationalPhaseAwayToFraction_element], hrel] at hcomp
    exact hcomp
  have haway : MvPolynomial.aeval y H = 0 := by
    apply rationalPhaseAwayToFraction_injective Q hQ0
    simpa using hfrac
  have hana : MvPolynomial.aeval
      (fun j : Fin (n + 1) =>
        analyticJetElement (phaseFunction omega F)
          (analyticOnNhd_phaseFunction hF) (j : ℕ)) H = 0 := by
    have hcomp := MvPolynomial.comp_aeval_apply y
      (rationalPhaseAwayToAnalytic (rho := rho) (omega := omega) Q hQ) H
    rw [haway, map_zero] at hcomp
    rw [show (fun j => rationalPhaseAwayToAnalytic
        (rho := rho) (omega := omega) Q hQ (y j)) =
        (fun j : Fin (n + 1) =>
          analyticJetElement (phaseFunction omega F)
            (analyticOnNhd_phaseFunction hF) (j : ℕ)) by
      funext j
      simp only [y, x₀]
      rw [rationalPhaseAwayToAnalytic_iterate,
        rationalPhaseAwayToAnalytic_element_eq hF P Q hQ hrep,
        iterate_analyticSubringDeriv_analyticFunctionElement]] at hcomp
    exact hcomp.symm
  have hpoint := (eval₂_analyticFunctionElement_eq_zero_iff
    (U := phaseStrip rho omega)
    (fun j : Fin (n + 1) =>
      iteratedDeriv (j : ℕ) (phaseFunction omega F))
    (fun j => analyticOnNhd_iteratedDeriv
      (analyticOnNhd_phaseFunction hF) (j : ℕ)) H).mp (by
        have halg : algebraMap ℂ
            (analyticSubring (phaseStrip rho omega)) =
          constToAnalytic (phaseStrip rho omega) := rfl
        rw [MvPolynomial.aeval_def, halg] at hana
        simpa [analyticJetElement] using hana)
  exact hpoint

/-- A rational phase regular on a polyannulus admits an autonomous relation at
exactly its active-character rank. -/
theorem exists_rationalPhase_realAutonomousAnnihilator_activeLatticeNatRank
    (hρ : ∀ i, 0 < rho i)
    (hF : AnalyticOnNhd ℂ F (polyannulus rho))
    (P Q : MvPolynomial (Fin r) ℂ)
    (hQ : ∀ z ∈ polyannulus rho, MvPolynomial.aeval z Q ≠ 0)
    (hrep : ∀ z ∈ polyannulus rho,
      F z = MvPolynomial.aeval z P / MvPolynomial.aeval z Q) :
    ∃ R : Polynomial (MvPolynomial (Fin (activeLatticeNatRank F)) ℂ),
      R ≠ 0 ∧ RealAutonomousAnnihilator
        (phaseFunction omega F) (activeLatticeNatRank F) R := by
  classical
  let zrat : FractionRing (MvPolynomial (Fin r) ℂ) :=
    MvPolynomial.aeval (rationalTorusCoordinate (C := ℂ) (r := r)) P /
      MvPolynomial.aeval (rationalTorusCoordinate (C := ℂ) (r := r)) Q
  have hfix : ∀ u ∈ unitCharacterStabilizer (activeSupport F),
      rationalTorusScaleEquiv u zrat = zrat := by
    intro u hu
    exact rationalTorusScaleEquiv_fixed_of_analytic_presentation
      hρ hF P Q hQ hrep hu
  obtain ⟨H, hH, hrel⟩ :=
    exists_rationalDiagonalIterate_relation_of_activeSupport_fix
      omega F zrat hfix
  refine ⟨jetUnlift H, jetUnlift_ne_zero hH, ?_⟩
  intro t
  have hstrip := rationalPhase_relation_on_strip_of_symbolic
    (omega := omega) hρ hF P Q hQ hrep H (by simpa [zrat] using hrel)
      (t : ℂ) (ofReal_mem_phaseStrip hρ t)
  let a : Fin (activeLatticeNatRank F + 1) → ℂ := fun j =>
    iteratedDeriv (j : ℕ) (phaseFunction omega F) (t : ℂ)
  have hlift :
      Polynomial.eval₂
          (MvPolynomial.eval fun j : Fin (activeLatticeNatRank F) =>
            a j.castSucc)
          (a (Fin.last (activeLatticeNatRank F))) (jetUnlift H) =
        MvPolynomial.eval a H := by
    rw [← eval_jetLift a, lastVariableJetLift_jetUnlift]
  change Polynomial.eval₂
      (MvPolynomial.eval fun j : Fin (activeLatticeNatRank F) => a j.castSucc)
      (a (Fin.last (activeLatticeNatRank F))) (jetUnlift H) = 0
  rw [hlift]
  exact hstrip

/-- Exact autonomous differential order of every rational phase regular on a
polyannulus: the rank of its active character lattice. -/
theorem autonomousMinimalOrder_rationalPhase_eq_activeLatticeNatRank
    (hρ : ∀ i, 0 < rho i)
    (hindep : RationallyIndependentFrequency omega)
    (hF : AnalyticOnNhd ℂ F (polyannulus rho))
    (P Q : MvPolynomial (Fin r) ℂ)
    (hQ : ∀ z ∈ polyannulus rho, MvPolynomial.aeval z Q ≠ 0)
    (hrep : ∀ z ∈ polyannulus rho,
      F z = MvPolynomial.aeval z P / MvPolynomial.aeval z Q) :
    autonomousMinimalOrder (phaseFunction omega F) = activeLatticeNatRank F := by
  apply autonomousMinimalOrder_eq_activeLatticeNatRank_of_relation hρ hindep hF
  exact exists_rationalPhase_realAutonomousAnnihilator_activeLatticeNatRank
    hρ hF P Q hQ hrep

/-- Rational-phase order compression is equivalent to a positive-dimensional
unit-torus stabilizer. -/
theorem autonomousMinimalOrder_rationalPhase_lt_card_iff_stabilizer_pos
    (hρ : ∀ i, 0 < rho i)
    (hindep : RationallyIndependentFrequency omega)
    (hF : AnalyticOnNhd ℂ F (polyannulus rho))
    (P Q : MvPolynomial (Fin r) ℂ)
    (hQ : ∀ z ∈ polyannulus rho, MvPolynomial.aeval z Q ≠ 0)
    (hrep : ∀ z ∈ polyannulus rho,
      F z = MvPolynomial.aeval z P / MvPolynomial.aeval z Q) :
    autonomousMinimalOrder (phaseFunction omega F) < r ↔
      0 < Module.finrank ℂ
        (characterAnnihilator (activeSupport F)) := by
  simpa using autonomousMinimalOrder_lt_card_iff_stabilizer_pos_of_exact
    (autonomousMinimalOrder_rationalPhase_eq_activeLatticeNatRank
      hρ hindep hF P Q hQ hrep)

end


end GaloisForLFunctions.HTGeometry

