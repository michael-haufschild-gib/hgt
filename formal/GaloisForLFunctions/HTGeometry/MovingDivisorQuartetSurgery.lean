import GaloisForLFunctions.HTGeometry.MovingDivisorEntireFreeness
import GaloisForLFunctions.HTGeometry.QuartetPolynomial
import GaloisForLFunctions.HTGeometry.TranslationPowerProfield

/-!
# The off-real quartet representative of a moving-divisor product

Multiplying the symmetric canonical product of a moving divisor by the real even quartet polynomial
`Q_tau` produces a second even real entire function of exact order one with the same real zeros, the
extra off-real quartet `{±tau, ±conj tau}`, the same maximal translation freeness at every power,
and literally the same positive-power translation profields.
-/

open Complex Filter Set
open scoped Topology ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

namespace MovingDivisor

variable (Dv : MovingDivisor)

/-- The quartet surgery of the symmetric canonical product. -/
def quartetProduct (τ : ℂ) (θ : ℕ → ℝ) : ℂ → ℂ :=
  fun z => Polynomial.eval z (quartetPoly τ) * Dv.evenCanonicalProduct θ z

theorem quartetProduct_apply (τ : ℂ) (θ : ℕ → ℝ) (z : ℂ) :
    Dv.quartetProduct τ θ z
      = Polynomial.eval z (quartetPoly τ) * Dv.evenCanonicalProduct θ z := rfl

theorem quartetProduct_analytic (τ : ℂ) (θ : ℕ → ℝ) :
    AnalyticOnNhd ℂ (Dv.quartetProduct τ θ) Set.univ :=
  (Bottcher.analyticOnNhd_polyEval (Set.univ : Set ℂ) _).mul (Dv.evenCanonicalProduct_analytic θ)

theorem quartetProduct_even (τ : ℂ) (θ : ℕ → ℝ) (z : ℂ) :
    Dv.quartetProduct τ θ (-z) = Dv.quartetProduct τ θ z := by
  rw [quartetProduct, quartetProduct, eval_quartetPoly_neg, Dv.evenCanonicalProduct_even]

theorem quartetProduct_conj (τ : ℂ) (θ : ℕ → ℝ) (z : ℂ) :
    Dv.quartetProduct τ θ ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) (Dv.quartetProduct τ θ z) := by
  rw [quartetProduct, quartetProduct, eval_quartetPoly_conj, Dv.evenCanonicalProduct_conj, map_mul]

theorem quartetProduct_orderOneEnvelope (τ : ℂ) (θ : ℕ → ℝ) :
    OrderOneEnvelope (Dv.quartetProduct τ θ) :=
  (orderOneEnvelope_polyEval _).mul (Dv.evenCanonicalProduct_orderOneEnvelope θ)

/-- The zero set of the quartet surgery: the old divisor plus the off-real quartet. -/
theorem quartetProduct_eq_zero_iff (τ : ℂ) (θ : ℕ → ℝ) (z : ℂ) :
    Dv.quartetProduct τ θ z = 0 ↔
      (z = τ ∨ z = -τ ∨ z = (starRingEnd ℂ) τ ∨ z = -((starRingEnd ℂ) τ)) ∨
        ∃ n, z = (Dv.zero θ n : ℂ) ∨ z = -(Dv.zero θ n : ℂ) := by
  rw [quartetProduct, mul_eq_zero, eval_quartetPoly_eq_zero_iff,
    Dv.evenCanonicalProduct_eq_zero_iff θ]

/-- The quartet is contained in the zero set. -/
theorem quartetProduct_quartet_zeros (τ : ℂ) (θ : ℕ → ℝ) :
    Dv.quartetProduct τ θ τ = 0 ∧ Dv.quartetProduct τ θ (-τ) = 0 ∧
      Dv.quartetProduct τ θ ((starRingEnd ℂ) τ) = 0 ∧
      Dv.quartetProduct τ θ (-((starRingEnd ℂ) τ)) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := quartet_root τ
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [quartetProduct]
  · rw [h1, zero_mul]
  · rw [h2, zero_mul]
  · rw [h3, zero_mul]
  · rw [h4, zero_mul]

/-- **The real zeros are unchanged.** -/
theorem quartetProduct_real_eq_zero_iff {τ : ℂ} (hτ : τ.im ≠ 0) (θ : ℕ → ℝ) {z : ℂ}
    (hz : z.im = 0) :
    Dv.quartetProduct τ θ z = 0 ↔ Dv.evenCanonicalProduct θ z = 0 := by
  rw [quartetProduct, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (eval_quartetPoly_ne_zero_of_im_eq_zero hτ hz)
    · exact h
  · exact Or.inr

end MovingDivisor

/-- **The quartet surgery keeps maximal translation freeness at every positive power.** -/
theorem not_familyDifferentiallyAlgebraicOn_quartetProduct_translates_pow
    (Dv : MovingDivisor) (τ : ℂ) (θ : BoundedRealSequence) {m : ℕ}
    (shift : InjectiveShiftConfiguration (Fin m)) {N : ℕ} (hN : N ≠ 0)
    (hcar : ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => Dv.evenCarrierB θ (z + shift.1 i)) (commonUpperTranslationDomain shift)) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i z => (Dv.quartetProduct τ (θ : ℕ → ℝ) (z + shift.1 i)) ^ N)
      (commonUpperTranslationDomain shift) := by
  intro hcon
  refine not_familyDifferentiallyAlgebraicOn_evenCanonicalProduct_translates_pow Dv θ shift hN
    hcar ?_
  refine familyDifferentiallyAlgebraicOn_of_mul_polynomial
    (fun i z => (Dv.evenCanonicalProduct (θ : ℕ → ℝ) (z + shift.1 i)) ^ N)
    (fun i => (shiftPoly (quartetPoly τ) (shift.1 i)) ^ N)
    (fun i => pow_ne_zero _ (shiftPoly_ne_zero (quartetPoly_ne_zero τ) _)) ?_ ?_
  · intro z hz i
    exact ((Dv.analyticOnNhd_evenCanonicalProduct_translate (θ : ℕ → ℝ) (shift.1 i)
      (commonUpperTranslationDomain shift) z hz).pow N).contDiffAt
  · have hfun : (fun i z => Polynomial.eval z ((shiftPoly (quartetPoly τ) (shift.1 i)) ^ N)
        * (Dv.evenCanonicalProduct (θ : ℕ → ℝ) (z + shift.1 i)) ^ N)
        = fun i z => (Dv.quartetProduct τ (θ : ℕ → ℝ) (z + shift.1 i)) ^ N := by
      funext i z
      rw [Polynomial.eval_pow, eval_shiftPoly, MovingDivisor.quartetProduct, mul_pow]
    rw [hfun]
    exact hcon

/-- **The quartet surgery has the same positive-power translation profields.** -/
theorem translationPowerProfield_quartetProduct (Dv : MovingDivisor) (τ : ℂ) (θ : ℕ → ℝ) (N : ℕ)
    (hF : AnalyticOnNhd ℂ (Dv.quartetProduct τ θ) Set.univ)
    (hE : AnalyticOnNhd ℂ (Dv.evenCanonicalProduct θ) Set.univ) :
    translationPowerProfield (Dv.quartetProduct τ θ) hF N
      = translationPowerProfield (Dv.evenCanonicalProduct θ) hE N :=
  translationPowerProfield_mul_polynomial hE hF (quartetPoly_ne_zero τ)
    (fun _ => rfl) N

end

end GaloisForLFunctions.HTGeometry
