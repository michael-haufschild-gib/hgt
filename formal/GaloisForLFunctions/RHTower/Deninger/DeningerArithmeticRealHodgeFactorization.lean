import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticOrientedHodge
import GaloisForLFunctions.RHTower.Deninger.DeningerDivisorSchwarzMonodromy
import GaloisForLFunctions.RHTower.Deninger.DeningerCompactOpenGradedRealJetUniversalityLaw
import GaloisForLFunctions.RHTower.XiWeilPolarization

/-!
# Real/Hodge factorization on semisimplified arithmetic cohomology

Deninger's flow-invariant Real structure and his positive Hodge star are distinct.  On raw
source jets, Schwarz reflection carries the derivative parity `(-1)^k`; rephasing degree `k`
by `I^k` removes that parity.  The resulting normalized Real structure conjugates coefficients
and reindexes through `rho ↦ conj rho`.

On multiplicity-exact semisimplified `H¹`, the even ordinary/compact-support identification
factors as this source Real structure followed by the complex-linear arithmetic Weil transport

`rho ↦ 1 - conj rho`.

The genuine degree-one Hodge star also contains the canonical orientation character of the
fixed-point-free functional-equation orbits.  It factors through the correspondingly oriented
Weil transport.  The Real structure commutes with Frobenius unconditionally.  Frobenius commutes
with either Weil transport exactly when RH holds.  The oriented transport is the precise source
operator that a Green/Hodge construction must produce; no zero-location or simplicity premise is
used in these factorizations.
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
    map_mul, deningerDivisorThetaEigen]
  rw [show ((xiZeroCopyConjEquiv q).1 : ℂ) =
    (starRingEnd ℂ) (q.1 : ℂ) from rfl, starRingEnd_self_apply]

/--
Index transport from Schwarz conjugation to functional-equation reflection.  On supports it is
`rho ↦ 1 - conj rho`.
-/
def deningerArithmeticPurityIndexEquiv : XiZeroCopy ≃ XiZeroCopy :=
  xiZeroCopyConjEquiv.symm.trans xiZeroCopyReflectEquiv

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
  simp [deningerArithmeticPurityIndexEquiv]

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

/-- Multiplication by the negative functional-equation orientation character. -/
def deningerArithmeticGradedOrientationEquiv :
    DeningerArithmeticGradedH1 ≃ₗ[ℂ]
      DeningerArithmeticGradedH1 where
  toFun :=
    finsuppDiagonal
      (fun q => -deningerArithmeticFEOrientation q)
  invFun :=
    finsuppDiagonal
      (fun q => -deningerArithmeticFEOrientation q)
  left_inv a := by
    ext q
    simp only [finsuppDiagonal_apply]
    have heps := deningerArithmeticFEOrientation_sq q
    calc
      -deningerArithmeticFEOrientation q *
          (-deningerArithmeticFEOrientation q * a q) =
        (deningerArithmeticFEOrientation q *
            deningerArithmeticFEOrientation q) * a q := by ring
      _ = a q := by rw [heps, one_mul]
  right_inv a := by
    ext q
    simp only [finsuppDiagonal_apply]
    have heps := deningerArithmeticFEOrientation_sq q
    calc
      -deningerArithmeticFEOrientation q *
          (-deningerArithmeticFEOrientation q * a q) =
        (deningerArithmeticFEOrientation q *
            deningerArithmeticFEOrientation q) * a q := by ring
      _ = a q := by rw [heps, one_mul]
  map_add' a b := by
    ext q
    simp only [finsuppDiagonal_apply, Finsupp.add_apply]
    ring
  map_smul' c a := by
    ext q
    simp only [finsuppDiagonal_apply, Finsupp.smul_apply, smul_eq_mul]
    change
      -deningerArithmeticFEOrientation q * (c * a q) =
        c * (-deningerArithmeticFEOrientation q * a q)
    ring

@[simp]
theorem deningerArithmeticGradedOrientationEquiv_apply
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    deningerArithmeticGradedOrientationEquiv a q =
      -deningerArithmeticFEOrientation q * a q := by
  change
    finsuppDiagonal (fun q => -deningerArithmeticFEOrientation q) a q =
      -deningerArithmeticFEOrientation q * a q
  rw [finsuppDiagonal_apply]

/--
Oriented arithmetic Weil transport.  This is the linear comparison from normalized source
Schwarz reality to the genuine odd Hodge star.
-/
def deningerArithmeticGradedOrientedWeilTransport :
    DeningerArithmeticGradedH1 ≃ₗ[ℂ]
      DeningerArithmeticGradedH1 :=
  deningerArithmeticGradedWeilTransport.trans
    deningerArithmeticGradedOrientationEquiv

@[simp]
theorem deningerArithmeticGradedOrientedWeilTransport_apply
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    deningerArithmeticGradedOrientedWeilTransport a q =
      -deningerArithmeticFEOrientation q *
        deningerArithmeticGradedWeilTransport a q := by
  change
    deningerArithmeticGradedOrientationEquiv
        (deningerArithmeticGradedWeilTransport a) q =
      -deningerArithmeticFEOrientation q *
        deningerArithmeticGradedWeilTransport a q
  rw [deningerArithmeticGradedOrientationEquiv_apply]

/--
Exact genuine Real/Hodge factorization: odd Hodge star is normalized source Schwarz reality
followed by oriented arithmetic Weil transport.
-/
theorem deningerArithmeticGradedOrientedHodge_factor
    (a : DeningerArithmeticGradedH1) :
    deningerArithmeticGradedOrientedWeilTransport
        (deningerArithmeticGradedSourceReal a) =
      deningerArithmeticGradedOrientedHodge.sigma a := by
  ext q
  change
    deningerArithmeticGradedOrientedWeilTransport
        (deningerArithmeticGradedSourceReal a) q =
      deningerArithmeticGradedOrientedHodgeSigma a q
  rw [deningerArithmeticGradedOrientedWeilTransport_apply,
    deningerArithmeticGradedHodgeStar_factor,
    deningerArithmeticGradedHodgeStar_apply,
    deningerArithmeticGradedOrientedHodgeSigma_apply]

/--
Frobenius naturality of the oriented Weil transport is exactly the residual Deninger purity
condition, hence exactly RH.
-/
theorem
    deningerArithmeticGradedTheta_orientedWeilTransport_iff_riemannHypothesis :
    (∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGradedTheta
          (deningerArithmeticGradedOrientedWeilTransport a) =
        deningerArithmeticGradedOrientedWeilTransport
          (deningerArithmeticGradedTheta a)) ↔
      RiemannHypothesis := by
  constructor
  · intro hW
    rw [← deningerArithmeticGradedTheta_orientedHodge_iff_riemannHypothesis]
    intro a
    rw [← deningerArithmeticGradedOrientedHodge_factor]
    calc
      deningerArithmeticGradedTheta
          (deningerArithmeticGradedOrientedWeilTransport
            (deningerArithmeticGradedSourceReal a)) =
          deningerArithmeticGradedOrientedWeilTransport
            (deningerArithmeticGradedTheta
              (deningerArithmeticGradedSourceReal a)) :=
        hW (deningerArithmeticGradedSourceReal a)
      _ = deningerArithmeticGradedOrientedWeilTransport
            (deningerArithmeticGradedSourceReal
              (deningerArithmeticGradedTheta a)) := by
        rw [deningerArithmeticGradedTheta_sourceReal]
      _ = deningerArithmeticGradedOrientedHodge.sigma
            (deningerArithmeticGradedTheta a) :=
        deningerArithmeticGradedOrientedHodge_factor
          (deningerArithmeticGradedTheta a)
  · intro hRH
    have hH :=
      deningerArithmeticGradedTheta_orientedHodge_iff_riemannHypothesis.mpr hRH
    intro a
    have hWa :
        deningerArithmeticGradedOrientedWeilTransport a =
          deningerArithmeticGradedOrientedHodge.sigma
            (deningerArithmeticGradedSourceReal a) := by
      calc
        deningerArithmeticGradedOrientedWeilTransport a =
            deningerArithmeticGradedOrientedWeilTransport
              (deningerArithmeticGradedSourceReal
                (deningerArithmeticGradedSourceReal a)) := by
          rw [deningerArithmeticGradedSourceReal_sq]
        _ = deningerArithmeticGradedOrientedHodge.sigma
              (deningerArithmeticGradedSourceReal a) :=
          deningerArithmeticGradedOrientedHodge_factor
            (deningerArithmeticGradedSourceReal a)
    have hWTheta :
        deningerArithmeticGradedOrientedWeilTransport
            (deningerArithmeticGradedTheta a) =
          deningerArithmeticGradedOrientedHodge.sigma
            (deningerArithmeticGradedSourceReal
              (deningerArithmeticGradedTheta a)) := by
      calc
        deningerArithmeticGradedOrientedWeilTransport
            (deningerArithmeticGradedTheta a) =
            deningerArithmeticGradedOrientedWeilTransport
              (deningerArithmeticGradedSourceReal
                (deningerArithmeticGradedSourceReal
                  (deningerArithmeticGradedTheta a))) := by
          rw [deningerArithmeticGradedSourceReal_sq]
        _ = deningerArithmeticGradedOrientedHodge.sigma
              (deningerArithmeticGradedSourceReal
                (deningerArithmeticGradedTheta a)) :=
          deningerArithmeticGradedOrientedHodge_factor
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

/--
Genuine odd Deninger Real/Hodge decomposition and exact residual purity gate.
-/
theorem deningerArithmetic_orientedRealHodge_factorization :
    (∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGradedSourceReal
          (deningerArithmeticGradedSourceReal a) = a) ∧
    (∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGradedTheta
          (deningerArithmeticGradedSourceReal a) =
        deningerArithmeticGradedSourceReal
          (deningerArithmeticGradedTheta a)) ∧
    (∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGradedOrientedWeilTransport
          (deningerArithmeticGradedSourceReal a) =
        deningerArithmeticGradedOrientedHodge.sigma a) ∧
    ((∀ a : DeningerArithmeticGradedH1,
      deningerArithmeticGradedTheta
          (deningerArithmeticGradedOrientedWeilTransport a) =
        deningerArithmeticGradedOrientedWeilTransport
          (deningerArithmeticGradedTheta a)) ↔
      RiemannHypothesis) := by
  exact ⟨deningerArithmeticGradedSourceReal_sq,
    deningerArithmeticGradedTheta_sourceReal,
    deningerArithmeticGradedOrientedHodge_factor,
    deningerArithmeticGradedTheta_orientedWeilTransport_iff_riemannHypothesis⟩

end

end RHTower
