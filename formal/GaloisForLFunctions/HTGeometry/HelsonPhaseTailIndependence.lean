import GaloisForLFunctions.HTGeometry.CofinalRecurrentPrimeValuationMaster

/-!
# The shift–jet palette of an arbitrary nowhere-vanishing phase is tail independent

The recurring-pattern criterion for tail independence is designed for coefficient families of finite
range, and a generic unimodular phase has infinite range, so it cannot be applied to a Helson phase
directly.  It does not have to be: a single source contributes its coefficient as a common weight
on every column of the shift–jet palette, and a common nowhere-vanishing weight does not change tail
independence.  The criterion is therefore applied once, to the constant family, whose single pattern
recurs at every prime.

Consequently the complete shift–jet rectangle of any phase that never vanishes — in particular of
any unimodular Helson phase — is tail independent, with no hypothesis on the distribution of its
values.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The constant coefficient family displays one pattern, at every coordinate, so it spans. -/
theorem recurringCoefficientPatternsSpan_const {J P : Type*} [Unique J] [Infinite P] :
    RecurringCoefficientPatternsSpan (fun _ : J => fun _ : P => (1 : ℂ)) := by
  intro a hrec
  have hset : {p : P | coefficientPattern (fun _ : J => fun _ : P => (1 : ℂ)) p
      = fun _ => (1 : ℂ)} = Set.univ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    funext j
    rfl
  have hinf : {p : P | coefficientPattern (fun _ : J => fun _ : P => (1 : ℂ)) p
      = fun _ => (1 : ℂ)}.Infinite := by
    rw [hset]
    exact Set.infinite_univ
  have h := hrec (fun _ => (1 : ℂ)) hinf
  funext j
  rw [Unique.eq_default j]
  simpa using h

/-- The unweighted shift–jet palette is tail independent. -/
theorem tailCoefficientIndependent_shiftJet_const {J A : Type*} [Unique J] [Fintype A] [DecidableEq A]
    (alpha : A → ℂ) (hdistinct : Function.Injective fun a => (alpha a).re) (m : ℕ) :
    TailCoefficientIndependent
      (coefficientShiftJet (fun _ : J => fun _ : Nat.Primes => (1 : ℂ))
        (fun a p => primeShiftFactor (alpha a) p) primeLogClock m) :=
  coefficientShiftJet_tailIndependent_of_recurringPatternsSpan _ _ _
    recurringCoefficientPatternsSpan_const m
    (primeFactorClockFiberIndependent alpha hdistinct m)

/-- **A nowhere-vanishing phase keeps the shift–jet palette tail independent.**  The phase enters
every column as one common weight, and a common nowhere-vanishing weight is invisible to tail
independence. -/
theorem tailCoefficientIndependent_phaseShiftJet {J A : Type*} [Unique J] [Fintype A]
    [DecidableEq A] (w : Nat.Primes → ℂ) (hw : ∀ p, w p ≠ 0) (alpha : A → ℂ)
    (hdistinct : Function.Injective fun a => (alpha a).re) (m : ℕ) :
    TailCoefficientIndependent
      (coefficientShiftJet (fun _ : J => w)
        (fun a p => primeShiftFactor (alpha a) p) primeLogClock m) := by
  have hconst := tailCoefficientIndependent_shiftJet_const (J := J) alpha hdistinct m
  have hshape : (fun jak : J × (A × Fin (m + 1)) => fun p : Nat.Primes =>
      w p * coefficientShiftJet (fun _ : J => fun _ : Nat.Primes => (1 : ℂ))
        (fun a p => primeShiftFactor (alpha a) p) primeLogClock m jak p)
      = coefficientShiftJet (fun _ : J => w)
        (fun a p => primeShiftFactor (alpha a) p) primeLogClock m := by
    funext jak p
    simp only [coefficientShiftJet, one_mul]
    ring
  rw [← hshape]
  exact (tailCoefficientIndependent_commonWeight_iff _ w hw).mpr hconst

/-- **Pong's tail hypothesis holds for every unimodular phase.**  A Helson phase never vanishes, so
each of its prime-power layers carries a tail-independent shift–jet rectangle, whatever the
distribution of its values. -/
theorem tailCoefficientIndependent_helsonShiftJet {J A : Type*} [Unique J] [Fintype A]
    [DecidableEq A] (χ : Nat.Primes → ℂ) (hunit : ∀ p, ‖χ p‖ = 1) (r : ℕ) (alpha : A → ℂ)
    (hdistinct : Function.Injective fun a => (alpha a).re) (m : ℕ) :
    TailCoefficientIndependent
      (coefficientShiftJet (fun _ : J => fun p => χ p ^ r)
        (fun a p => primeShiftFactor (alpha a) p) primeLogClock m) := by
  refine tailCoefficientIndependent_phaseShiftJet (J := J) _ ?_ alpha hdistinct m
  intro p
  refine pow_ne_zero r ?_
  intro h
  have := hunit p
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- **The rotated shift–jet rectangle of a nowhere-vanishing phase is tail independent.**  Rotating
the logarithmic clock scales each column by a nonzero constant, which tail independence does not
see. -/
theorem primePowerCoefficientShiftedRotatedJet_tailIndependent_phase
    {J A : Type*} [Unique J] [Fintype A] [DecidableEq A]
    (e : ℕ) (w : Nat.Primes → ℂ) (hw : ∀ p, w p ≠ 0) (alpha : A → ℂ)
    (hdistinct : Function.Injective fun a => (alpha a).re) (m : ℕ) :
    TailCoefficientIndependent
      (fun jak : J × (A × Fin (m + 1)) => fun p =>
        w p * primeShiftFactor (alpha jak.2.1) p *
          ((((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ (jak.2.2 : ℕ))) := by
  classical
  let raw : J × (A × Fin (m + 1)) → Nat.Primes → ℂ := fun jak p =>
    w p * primeShiftFactor (alpha jak.2.1) p * primeLogClock p ^ (jak.2.2 : ℕ)
  let u : J × (A × Fin (m + 1)) → ℂ := fun jak =>
    ((((e + 1 : ℕ) : ℂ) * Complex.I) ^ (jak.2.2 : ℕ))
  have hu : ∀ jak, u jak ≠ 0 := by
    intro jak
    refine pow_ne_zero _ (mul_ne_zero ?_ Complex.I_ne_zero)
    exact_mod_cast Nat.succ_ne_zero e
  have hscale :
      TailCoefficientIndependent (fun jak p => u jak * raw jak p) ↔
        TailCoefficientIndependent raw :=
    tailCoefficientIndependent_scale_columns_iff raw u hu
  have hraw : TailCoefficientIndependent raw :=
    tailCoefficientIndependent_phaseShiftJet (J := J) w hw alpha hdistinct m
  have hscaled := hscale.mpr hraw
  convert hscaled using 1
  funext jak p
  simp only [u, raw, rotatedPrimeLogClock, mul_pow]
  ring

universe u

/-- **Algebraic independence of the shifted-jet rectangle of a nowhere-vanishing phase.**  This is
the conclusion of Pong's independence theorem for a single source per valuation layer, with the
recurring-pattern hypothesis discharged: a phase that never vanishes needs no assumption on the
distribution of its values. -/
theorem primePowerCoefficientShiftedJets_algebraicIndependent_phase
    {d : ℕ} (J B : Fin d → Type u)
    [∀ r, Unique (J r)] [∀ r, Fintype (J r)] [∀ r, DecidableEq (J r)]
    [∀ r, Fintype (B r)] [∀ r, DecidableEq (B r)]
    (w : ∀ r, J r → Nat.Primes → ℂ) (hw : ∀ r j p, w r j p ≠ 0)
    (alpha : ∀ r, B r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun b => (alpha r b).re))
    (m : Fin d → ℕ) :
    AlgebraicIndependent finitePrimeRationalCoefficientField
      (fun x : Σ r, J r × (B r × Fin (m r + 1)) =>
        algebraMap arithmeticFunctionFractionField
          arithmeticFunctionRationalCoordinateField
          (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (primePowerCoefficientShiftedRotatedJet
              x.1 (w x.1 x.2.1) (alpha x.1 x.2.2.1) x.2.2.2))) := by
  classical
  let A : Fin d → Type u := fun r => J r × (B r × Fin (m r + 1))
  letI (r : Fin d) : Fintype (A r) := inferInstance
  letI (r : Fin d) : DecidableEq (A r) := inferInstance
  let a : ∀ r, A r → Nat.Primes → ℂ := fun r x p =>
    w r x.1 p * primeShiftFactor (alpha r x.2.1) p *
      ((((r.1 + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ (x.2.2 : ℕ))
  have hatail : ∀ r, TailCoefficientIndependent (a r) := by
    intro r
    have h := primePowerCoefficientShiftedRotatedJet_tailIndependent_phase
      (J := J r) r.1 (w r default) (fun p => hw r default p) (alpha r) (hdistinct r) (m r)
    convert h using 1
    funext x p
    simp only [a]
    rw [Unique.eq_default x.1]
  have hraw := algebraicIndependent_primePowerSigmaTower_over_finitePrimeCoefficientField
    d A a hatail
  apply algebraicIndependent_constants_over_finitePrimeRationalCoefficientField at hraw
  simpa only [A, a, primePowerSigmaExponent, primePowerSigmaCoefficient,
    primePowerCoefficientShiftedRotatedJet] using hraw

end

end GaloisForLFunctions.HTGeometry
