import GaloisForLFunctions.RHTower.DeningerMeyerSecondaryPoissonRegulator
import GaloisForLFunctions.RHTower.DeningerArithmeticPaugamKReal
import GaloisForLFunctions.RHTower.KRealStructureRealization

/-!
# Reciprocal Paugam polarization of the Meyer--Poisson regulator quotient

The local secondary Meyer regulator quotient is canonically one complex dimension.  This creates
a sharp parity obstruction: a single local quotient cannot carry Paugam's odd `K_R` coefficient,
because no conjugate-linear endomorphism of a complex line squares to `-1`.

The minimal repair is not another local scalar correction.  It is reciprocal doubling.  Pair the
quotient at radius `x` with the quotient at `x⁻¹`, exchange them by conjugation through their
canonical defect coordinates, and apply Paugam's sign-conjugation.  The resulting anti-linear
operator squares to `-1`.

The canonical cross-cup in defect coordinates is negative multiplication.  Its Paugam
cup--sign-conjugation diagonal is exactly the sum of the two complex norm squares.  Hence the
reciprocal double has a positive zero-radical local cup--Hodge form.

The general fact that an odd structure cannot live on `ℂ` was already formalized in
`KRealStructureRealization`; it is not claimed new here.  New content is the exact application to
the Meyer regulator quotient and the source-coordinate reciprocal doubled survivor.  This remains
local value-space polarization, not identification with the full arithmetic cup/trace complex.
-/

namespace RHTower

open scoped ComplexConjugate

noncomputable section

open GaloisForLFunctions.RHTower

namespace KRealStructure

/-- Transport a `K_R` structure through a complex-linear equivalence. -/
def transportLinearEquiv {odd : Bool} {V W : Type*}
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (K : KRealStructure odd V) :
    KRealStructure odd W where
  sigma :=
    { toFun := fun w => e (K.sigma (e.symm w))
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp }
  sq := by
    intro w
    change
      e (K.sigma (e.symm
        (e (K.sigma (e.symm w))))) =
        kRealParityAction odd w
    rw [e.symm_apply_apply, K.sq]
    cases odd <;> simp [kRealParityAction]

end KRealStructure

/-- The one-dimensional secondary Poisson collar quotient at radius `x`. -/
abbrev DeningerMeyerPoissonCollarQuotient (x : ℝ) :=
  (ℂ × ℂ) ⧸ deningerMeyerPoissonCalderonGraph x

/--
**Odd-line obstruction for the actual regulator quotient.**  No single local Poisson collar
quotient can be Paugam's odd coefficient.
-/
theorem
    not_nonempty_deningerMeyerPoissonCollarQuotient_oddKReal
    (x : ℝ) :
    IsEmpty
      (KRealStructure true
        (DeningerMeyerPoissonCollarQuotient x)) := by
  constructor
  intro K
  have KC : KRealStructure true ℂ :=
    KRealStructure.transportLinearEquiv
      (deningerMeyerPoissonCalderonQuotientEquiv x) K
  exact not_nonempty_kRealStructure_true_complex.false KC

/-- Conjugate-linear exchange between any two canonical Poisson collar quotient lines. -/
def deningerMeyerPoissonQuotientConjugation
    (x y : ℝ) :
    DeningerMeyerPoissonCollarQuotient x →ₗ⋆[ℂ]
      DeningerMeyerPoissonCollarQuotient y where
  toFun q :=
    (deningerMeyerPoissonCalderonQuotientEquiv y).symm
      (starRingEnd ℂ
        (deningerMeyerPoissonCalderonQuotientEquiv x q))
  map_add' q r := by
    simp
  map_smul' c q := by
    simpa only [map_smul, smul_eq_mul, map_mul] using
      (deningerMeyerPoissonCalderonQuotientEquiv y).symm.map_smul
        (starRingEnd ℂ c)
        (starRingEnd ℂ
          (deningerMeyerPoissonCalderonQuotientEquiv x q))

@[simp]
theorem deningerMeyerPoissonQuotientConjugation_coordinate
    (x y : ℝ) (q : DeningerMeyerPoissonCollarQuotient x) :
    deningerMeyerPoissonCalderonQuotientEquiv y
        (deningerMeyerPoissonQuotientConjugation x y q) =
      starRingEnd ℂ
        (deningerMeyerPoissonCalderonQuotientEquiv x q) := by
  simp [deningerMeyerPoissonQuotientConjugation]

/--
Canonical upper/lower exchange on the reciprocal pair of Poisson regulator quotients.
-/
def deningerMeyerPoissonReciprocalPaugamExchange
    (x : ℝ) :
    PaugamSpectralExchange
      (Vplus := DeningerMeyerPoissonCollarQuotient x)
      (Vminus := DeningerMeyerPoissonCollarQuotient x⁻¹) where
  plusToMinus :=
    deningerMeyerPoissonQuotientConjugation x x⁻¹
  minusToPlus :=
    deningerMeyerPoissonQuotientConjugation x⁻¹ x
  minus_plus q := by
    apply
      (deningerMeyerPoissonCalderonQuotientEquiv x).injective
    simp
  plus_minus q := by
    apply
      (deningerMeyerPoissonCalderonQuotientEquiv x⁻¹).injective
    simp

/-- Concrete reciprocal Paugam sign-conjugation squares to `-1`. -/
theorem deningerMeyerPoissonReciprocal_signConjugation_sq
    (x : ℝ)
    (q :
      DeningerMeyerPoissonCollarQuotient x ×
        DeningerMeyerPoissonCollarQuotient x⁻¹) :
    (deningerMeyerPoissonReciprocalPaugamExchange x).signConjugationSigma
        ((deningerMeyerPoissonReciprocalPaugamExchange x).signConjugationSigma q) =
      -q :=
  (deningerMeyerPoissonReciprocalPaugamExchange x).signConjugationSigma_sq q

/--
Oriented cross-cup on reciprocal defect coordinates.  Negative multiplication is the orientation
for which Paugam sign-conjugation gives positive diagonal.
-/
def deningerMeyerPoissonReciprocalCrossPairing
    (x : ℝ) :
    DeningerMeyerPoissonCollarQuotient x →ₗ[ℂ]
      DeningerMeyerPoissonCollarQuotient x⁻¹ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun q r =>
      -(deningerMeyerPoissonCalderonQuotientEquiv x q *
        deningerMeyerPoissonCalderonQuotientEquiv x⁻¹ r))
    (by
      intros
      simp
      ring)
    (by
      intros
      simp
      ring)
    (by
      intros
      simp
      ring)
    (by
      intros
      simp
      ring)

@[simp]
theorem deningerMeyerPoissonReciprocalCrossPairing_apply
    (x : ℝ)
    (q : DeningerMeyerPoissonCollarQuotient x)
    (r : DeningerMeyerPoissonCollarQuotient x⁻¹) :
    deningerMeyerPoissonReciprocalCrossPairing x q r =
      -(deningerMeyerPoissonCalderonQuotientEquiv x q *
        deningerMeyerPoissonCalderonQuotientEquiv x⁻¹ r) :=
  rfl

/--
**Exact local cup--Hodge diagonal.**  On the reciprocal double, the Paugam alternating cup
followed by sign-conjugation is the sum of the two defect-coordinate norm squares.
-/
theorem deningerMeyerPoissonReciprocal_cupSigma_self
    (x : ℝ)
    (q :
      DeningerMeyerPoissonCollarQuotient x ×
        DeningerMeyerPoissonCollarQuotient x⁻¹) :
    PaugamSpectralExchange.splitPairing
        (deningerMeyerPoissonReciprocalCrossPairing x) q
        ((deningerMeyerPoissonReciprocalPaugamExchange x).signConjugationSigma
          q) =
      ((Complex.normSq
          (deningerMeyerPoissonCalderonQuotientEquiv x q.1) +
        Complex.normSq
          (deningerMeyerPoissonCalderonQuotientEquiv x⁻¹ q.2) :
            ℝ) : ℂ) := by
  rw [PaugamSpectralExchange.splitPairing_signConjugation_self]
  simp only [deningerMeyerPoissonReciprocalCrossPairing_apply]
  simp only [deningerMeyerPoissonReciprocalPaugamExchange]
  rw [deningerMeyerPoissonQuotientConjugation_coordinate,
    deningerMeyerPoissonQuotientConjugation_coordinate]
  push_cast
  rw [← Complex.mul_conj]
  rw [show
      starRingEnd ℂ
          (deningerMeyerPoissonCalderonQuotientEquiv x⁻¹ q.2) *
          deningerMeyerPoissonCalderonQuotientEquiv x⁻¹ q.2 =
        deningerMeyerPoissonCalderonQuotientEquiv x⁻¹ q.2 *
          starRingEnd ℂ
            (deningerMeyerPoissonCalderonQuotientEquiv x⁻¹ q.2) by
      ring,
    ← Complex.mul_conj]
  ring

theorem deningerMeyerPoissonReciprocal_cupSigma_re_nonneg
    (x : ℝ)
    (q :
      DeningerMeyerPoissonCollarQuotient x ×
        DeningerMeyerPoissonCollarQuotient x⁻¹) :
    0 ≤
      (PaugamSpectralExchange.splitPairing
        (deningerMeyerPoissonReciprocalCrossPairing x) q
        ((deningerMeyerPoissonReciprocalPaugamExchange x).signConjugationSigma
          q)).re := by
  rw [deningerMeyerPoissonReciprocal_cupSigma_self]
  simp only [Complex.ofReal_re]
  exact add_nonneg
    (Complex.normSq_nonneg _)
    (Complex.normSq_nonneg _)

/-- The positive reciprocal cup--Hodge diagonal has zero radical. -/
theorem deningerMeyerPoissonReciprocal_cupSigma_eq_zero_iff
    (x : ℝ)
    (q :
      DeningerMeyerPoissonCollarQuotient x ×
        DeningerMeyerPoissonCollarQuotient x⁻¹) :
    PaugamSpectralExchange.splitPairing
        (deningerMeyerPoissonReciprocalCrossPairing x) q
        ((deningerMeyerPoissonReciprocalPaugamExchange x).signConjugationSigma
          q) = 0 ↔
      q = 0 := by
  rw [deningerMeyerPoissonReciprocal_cupSigma_self]
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.zero_re] at hre
    have h1 :
        Complex.normSq
          (deningerMeyerPoissonCalderonQuotientEquiv x q.1) = 0 := by
      nlinarith
        [Complex.normSq_nonneg
          (deningerMeyerPoissonCalderonQuotientEquiv x q.1),
        Complex.normSq_nonneg
          (deningerMeyerPoissonCalderonQuotientEquiv x⁻¹ q.2)]
    have h2 :
        Complex.normSq
          (deningerMeyerPoissonCalderonQuotientEquiv x⁻¹ q.2) = 0 := by
      nlinarith
        [Complex.normSq_nonneg
          (deningerMeyerPoissonCalderonQuotientEquiv x q.1),
        Complex.normSq_nonneg
          (deningerMeyerPoissonCalderonQuotientEquiv x⁻¹ q.2)]
    apply Prod.ext
    · have hz := Complex.normSq_eq_zero.mp h1
      apply
        (deningerMeyerPoissonCalderonQuotientEquiv x).injective
      simpa using hz
    · have hz := Complex.normSq_eq_zero.mp h2
      apply
        (deningerMeyerPoissonCalderonQuotientEquiv x⁻¹).injective
      simpa using hz
  · rintro rfl
    simp

end

end RHTower
