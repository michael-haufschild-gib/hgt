import GaloisForLFunctions.RHTower.DeningerArithmeticSemisimpleHodge
import GaloisForLFunctions.RHTower.DeningerCompactOpenGradedRealJetUniversalityLaw
import GaloisForLFunctions.RHTower.XiWeilPolarization

/-!
# Real/Hodge factorization on semisimplified arithmetic cohomology

Deninger's flow-invariant Real structure and his positive Hodge star are distinct.  On raw
source jets, Schwarz reflection carries the derivative parity `(-1)^k`; rephasing degree `k`
by `I^k` removes that parity.  The resulting normalized Real structure conjugates coefficients
and reindexes through `rho ↦ conj rho`.

On multiplicity-exact semisimplified `H¹`, the positive Hodge star factors as this source Real
structure followed by the complex-linear arithmetic Weil transport

`rho ↦ 1 - conj rho`.

The Real structure commutes with Frobenius unconditionally.  Frobenius commutes with the Weil
transport exactly when RH holds.  This identifies the precise source operator that a
Green/Hodge construction must produce; no positivity, zero-location, or simplicity premise is
used in the factorization.
-/

open Complex

namespace RHTower

noncomputable section

/-- Degree-rephased compact-open point jet. -/
def deningerArithmeticNormalizedCompactOpenJet
    (F : DeningerCompactOpenEntire) (z : ℂ) (k : ℕ) : ℂ :=
  Complex.I ^ k * deningerCompactOpenJet z k F

/--
Rephasing raw degree-`k` jets by `I^k` removes the `(-1)^k` character from source
Schwarz reflection.
-/
theorem deningerArithmeticNormalizedCompactOpenJet_sigma
    (F : DeningerCompactOpenEntire) (rho : XiDivisorSupport) (k : ℕ) :
    deningerArithmeticNormalizedCompactOpenJet
        (deningerCompactOpenFunctionalEquationSigma F)
        (xiSpectralPointSupport rho) k =
      (starRingEnd ℂ)
        (deningerArithmeticNormalizedCompactOpenJet F
          (xiSpectralPointSupport (xiZeroConjEquiv rho)) k) := by
  rw [deningerArithmeticNormalizedCompactOpenJet,
    deningerCompactOpenXiJet_functionalEquationSigma,
    deningerArithmeticNormalizedCompactOpenJet]
  simp only [map_mul, map_pow, conj_I]
  rw [← mul_assoc, ← mul_pow]
  simp

/-- Conjugation lifted to multiplicity copies is an involution. -/
@[simp]
theorem xiZeroCopyConjEquiv_apply_apply (q : XiZeroCopy) :
    xiZeroCopyConjEquiv (xiZeroCopyConjEquiv q) = q := by
  have hfst :
      (xiZeroCopyConjEquiv (xiZeroCopyConjEquiv q)).1 = q.1 := by
    apply Subtype.ext
    simp [xiZeroCopyConjEquiv, xiZeroConjEquiv, Equiv.sigmaCongr,
      Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft]
  apply Sigma.ext hfst
  apply (Fin.heq_ext_iff (congrArg (fun rho : XiDivisorSupport =>
    Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ))) hfst)).2
  simp [xiZeroCopyConjEquiv, xiZeroConjEquiv, Equiv.sigmaCongr,
    Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft]
  exact Fin.val_eq_val_of_heq (cast_heq _ q.2)

theorem xiZeroCopyConjEquiv_symm_apply (q : XiZeroCopy) :
    xiZeroCopyConjEquiv.symm q = xiZeroCopyConjEquiv q := by
  apply xiZeroCopyConjEquiv.injective
  rw [xiZeroCopyConjEquiv.apply_symm_apply,
    xiZeroCopyConjEquiv_apply_apply]

/-- Rephased source Real structure on multiplicity-exact semisimplified `H¹`. -/
def deningerArithmeticGradedSourceReal :
    DeningerArithmeticGradedH1 ≃ₛₗ[starRingEnd ℂ]
      DeningerArithmeticGradedH1 :=
  (Finsupp.mapRange.linearEquiv (starLinearEquiv ℂ)).trans
    (Finsupp.domLCongr xiZeroCopyConjEquiv)

@[simp]
theorem deningerArithmeticGradedSourceReal_apply
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    deningerArithmeticGradedSourceReal a q =
      (starRingEnd ℂ) (a (xiZeroCopyConjEquiv q)) := by
  change
    (starRingEnd ℂ) (a (xiZeroCopyConjEquiv.symm q)) =
      (starRingEnd ℂ) (a (xiZeroCopyConjEquiv q))
  rw [xiZeroCopyConjEquiv_symm_apply]

/-- The normalized source Real structure is involutive. -/
theorem deningerArithmeticGradedSourceReal_sq
    (a : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedSourceReal
        (deningerArithmeticGradedSourceReal a) = a := by
  ext q
  simp [deningerArithmeticGradedSourceReal_apply,
    xiZeroCopyConjEquiv_apply_apply]

/-- Source Schwarz reality commutes with semisimple arithmetic Frobenius unconditionally. -/
theorem deningerArithmeticGradedTheta_sourceReal
    (a : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedTheta
        (deningerArithmeticGradedSourceReal a) =
      deningerArithmeticGradedSourceReal
        (deningerArithmeticGradedTheta a) := by
  ext q
  simp only [deningerArithmeticGradedTheta, deningerDivisorTheta,
    finsuppDiagonal_apply, deningerArithmeticGradedSourceReal_apply,
    map_mul]
  change
    (q.1 : ℂ) *
        (starRingEnd ℂ) (a (xiZeroCopyConjEquiv q)) =
      (starRingEnd ℂ)
        (((starRingEnd ℂ) (q.1 : ℂ)) *
          a (xiZeroCopyConjEquiv q))
  simp

/--
Index transport from Schwarz conjugation to functional-equation reflection.  On supports it is
`rho ↦ 1 - conj rho`.
-/
def deningerArithmeticPurityIndexEquiv : XiZeroCopy ≃ XiZeroCopy :=
  xiZeroCopyReflectEquiv.trans xiZeroCopyConjEquiv.symm

/-- Complex-linear arithmetic Weil transport comparing source reality with Hodge duality. -/
def deningerArithmeticGradedWeilTransport :
    DeningerArithmeticGradedH1 ≃ₗ[ℂ]
      DeningerArithmeticGradedH1 :=
  Finsupp.domLCongr deningerArithmeticPurityIndexEquiv

/--
Exact Real/Hodge factorization: positive Hodge star is source Schwarz reality followed by the
arithmetic Weil transport.
-/
theorem deningerArithmeticGradedHodgeStar_factor
    (a : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedWeilTransport
        (deningerArithmeticGradedSourceReal a) =
      deningerArithmeticGradedHodgeStar a := by
  ext q
  change
    (starRingEnd ℂ)
        (a (xiZeroCopyConjEquiv.symm
          (deningerArithmeticPurityIndexEquiv.symm q))) =
      (starRingEnd ℂ)
        (a (xiZeroCopyReflectEquiv.symm q))
  rw [deningerArithmeticPurityIndexEquiv]
  simp

/--
The arithmetic Weil transport is Frobenius-natural exactly when the Riemann hypothesis holds.
This is the exact operator-valued purity gate left after the unconditional source Real
structure has been removed.
-/
theorem deningerArithmeticGradedTheta_weilTransport_iff_riemannHypothesis :
    (∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGradedTheta
          (deningerArithmeticGradedWeilTransport a) =
        deningerArithmeticGradedWeilTransport
          (deningerArithmeticGradedTheta a)) ↔
      RiemannHypothesis := by
  constructor
  · intro hW
    rw [← deningerArithmeticGradedTheta_hodgeStar_iff_riemannHypothesis]
    intro a
    rw [← deningerArithmeticGradedHodgeStar_factor]
    calc
      deningerArithmeticGradedTheta
          (deningerArithmeticGradedWeilTransport
            (deningerArithmeticGradedSourceReal a)) =
          deningerArithmeticGradedWeilTransport
            (deningerArithmeticGradedTheta
              (deningerArithmeticGradedSourceReal a)) :=
        hW (deningerArithmeticGradedSourceReal a)
      _ = deningerArithmeticGradedWeilTransport
            (deningerArithmeticGradedSourceReal
              (deningerArithmeticGradedTheta a)) := by
        rw [deningerArithmeticGradedTheta_sourceReal]
      _ = deningerArithmeticGradedHodgeStar
            (deningerArithmeticGradedTheta a) :=
        deningerArithmeticGradedHodgeStar_factor
          (deningerArithmeticGradedTheta a)
  · intro hRH
    have hH :=
      deningerArithmeticGradedTheta_hodgeStar_of_riemannHypothesis hRH
    intro a
    have hWa :
        deningerArithmeticGradedWeilTransport a =
          deningerArithmeticGradedHodgeStar
            (deningerArithmeticGradedSourceReal a) := by
      calc
        deningerArithmeticGradedWeilTransport a =
            deningerArithmeticGradedWeilTransport
              (deningerArithmeticGradedSourceReal
                (deningerArithmeticGradedSourceReal a)) := by
          rw [deningerArithmeticGradedSourceReal_sq]
        _ = deningerArithmeticGradedHodgeStar
              (deningerArithmeticGradedSourceReal a) :=
          deningerArithmeticGradedHodgeStar_factor
            (deningerArithmeticGradedSourceReal a)
    have hWTheta :
        deningerArithmeticGradedWeilTransport
            (deningerArithmeticGradedTheta a) =
          deningerArithmeticGradedHodgeStar
            (deningerArithmeticGradedSourceReal
              (deningerArithmeticGradedTheta a)) := by
      calc
        deningerArithmeticGradedWeilTransport
            (deningerArithmeticGradedTheta a) =
            deningerArithmeticGradedWeilTransport
              (deningerArithmeticGradedSourceReal
                (deningerArithmeticGradedSourceReal
                  (deningerArithmeticGradedTheta a))) := by
          rw [deningerArithmeticGradedSourceReal_sq]
        _ = deningerArithmeticGradedHodgeStar
              (deningerArithmeticGradedSourceReal
                (deningerArithmeticGradedTheta a)) :=
          deningerArithmeticGradedHodgeStar_factor
            (deningerArithmeticGradedSourceReal
              (deningerArithmeticGradedTheta a))
    rw [hWa, hWTheta, hH]
    congr 1
    exact deningerArithmeticGradedTheta_sourceReal a

/--
Direct Deninger Real/Hodge decomposition and exact residual purity gate.
-/
theorem deningerArithmetic_realHodge_factorization :
    (∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGradedSourceReal
          (deningerArithmeticGradedSourceReal a) = a) ∧
    (∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGradedTheta
          (deningerArithmeticGradedSourceReal a) =
        deningerArithmeticGradedSourceReal
          (deningerArithmeticGradedTheta a)) ∧
    (∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGradedWeilTransport
          (deningerArithmeticGradedSourceReal a) =
        deningerArithmeticGradedHodgeStar a) ∧
    ((∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGradedTheta
          (deningerArithmeticGradedWeilTransport a) =
        deningerArithmeticGradedWeilTransport
          (deningerArithmeticGradedTheta a)) ↔
      RiemannHypothesis) := by
  exact ⟨deningerArithmeticGradedSourceReal_sq,
    deningerArithmeticGradedTheta_sourceReal,
    deningerArithmeticGradedHodgeStar_factor,
    deningerArithmeticGradedTheta_weilTransport_iff_riemannHypothesis⟩

end

end RHTower
