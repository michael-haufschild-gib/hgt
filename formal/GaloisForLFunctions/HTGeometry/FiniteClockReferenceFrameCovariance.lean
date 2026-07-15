import GaloisForLFunctions.HTGeometry.FiniteConstraintGroupAverage

/-!
# Covariance of finite clock-observer structures under reference-frame changes

A change of quantum reference frame that is implementable by an invertible operator must move
the clock and every observed quantity together.  This file proves that finite cyclic observable
twirling, its conditional-variance defect, and membership in the clock commutant are covariant
under the same two-sided conjugation.  These are static identities between observer structures;
no Hamiltonian or temporal evolution is introduced.

Physics provenance: P. A. Höhn and A. Vanrietvelde, *How to switch between relational quantum
clocks*, New J. Phys. 22 (2020) 123048, arXiv:1810.04153; T. Thiemann, *(Quantum) reference
frames, relational observables, gauge reduction and physical interpretation*, arXiv:2603.04072.
-/

namespace HTGeometry

section

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Two-sided conjugation preserves products when the inner frame maps cancel. -/
theorem twoSidedConjugation_mul
    (V W A B : E →L[𝕜] E) (hWV : W * V = 1) :
    (V * A * W) * (V * B * W) = V * (A * B) * W := by
  calc
    (V * A * W) * (V * B * W) = V * A * (W * V) * B * W := by
      noncomm_ring
    _ = V * (A * B) * W := by rw [hWV]; simp [mul_assoc]

/-- Two-sided conjugation by inverse frame maps is injective on observables. -/
theorem twoSidedConjugation_eq_iff
    (V W A B : E →L[𝕜] E) (hWV : W * V = 1) :
    V * A * W = V * B * W ↔ A = B := by
  constructor
  · intro h
    have hcancel := congrArg (fun T : E →L[𝕜] E => W * T * V) h
    have hleft : W * (V * A * W) * V = A := by
      calc
        W * (V * A * W) * V = (W * V) * A * (W * V) := by noncomm_ring
        _ = A := by rw [hWV]; simp
    have hright : W * (V * B * W) * V = B := by
      calc
        W * (V * B * W) * V = (W * V) * B * (W * V) := by noncomm_ring
        _ = B := by rw [hWV]; simp
    exact hleft.symm.trans (hcancel.trans hright)
  · rintro rfl
    rfl

/-- Powers of a clock transform by the same conjugation when the frame maps are two-sided
inverses. -/
theorem twoSidedConjugation_pow
    (U V W : E →L[𝕜] E) (hWV : W * V = 1) (hVW : V * W = 1) : ∀ n : ℕ,
    (V * U * W) ^ n = V * U ^ n * W
  | 0 => by simp [hVW]
  | n + 1 => by
      rw [pow_succ, twoSidedConjugation_pow U V W hWV hVW n, pow_succ,
        twoSidedConjugation_mul V W (U ^ n) U hWV]

/-- Finite conjugation numerators are covariant under an invertible change of clock frame. -/
theorem finiteCyclicObservableTwirlNumerator_twoSidedConjugation
    (U X V W : E →L[𝕜] E) (hWV : W * V = 1) (hVW : V * W = 1) : ∀ N : ℕ,
    finiteCyclicObservableTwirlNumerator (V * U * W) (V * X * W) N =
      V * finiteCyclicObservableTwirlNumerator U X N * W
  | 0 => by simp [finiteCyclicObservableTwirlNumerator]
  | n + 1 => by
      simp only [finiteCyclicObservableTwirlNumerator]
      rw [finiteCyclicObservableTwirlNumerator_twoSidedConjugation
          U X V W hWV hVW n,
        twoSidedConjugation_pow U V W hWV hVW (n + 1),
        twoSidedConjugation_mul V W U
          (finiteCyclicObservableTwirlNumerator U X n) hWV,
        twoSidedConjugation_mul V W X (U ^ (n + 1)) hWV]
      noncomm_ring

/-- **Finite clock-reference-frame covariance.**  Moving the clock and observable together by
an invertible frame change conjugates their observable twirl by that same frame change. -/
theorem finiteCyclicObservableTwirl_twoSidedConjugation
    (U X V W : E →L[𝕜] E) (N : ℕ)
    (hWV : W * V = 1) (hVW : V * W = 1) :
    finiteCyclicObservableTwirl (V * U * W) (V * X * W) N =
      V * finiteCyclicObservableTwirl U X N * W := by
  rw [finiteCyclicObservableTwirl, finiteCyclicObservableTwirl,
    finiteCyclicObservableTwirlNumerator_twoSidedConjugation U X V W hWV hVW N]
  simp only [mul_smul_comm, smul_mul_assoc]

/-- A finite-period clock remains finite-period after an invertible reference-frame change. -/
theorem twoSidedConjugation_period
    (U V W : E →L[𝕜] E) (N : ℕ)
    (hWV : W * V = 1) (hVW : V * W = 1) (hperiod : U ^ N = 1) :
    (V * U * W) ^ N = 1 := by
  rw [twoSidedConjugation_pow U V W hWV hVW N, hperiod]
  simpa using hVW

/-- Whether an observable belongs to the clock commutant is independent of an invertibly
implemented reference-frame change. -/
theorem twoSidedConjugation_commutes_iff
    (U X V W : E →L[𝕜] E) (hWV : W * V = 1) :
    (V * U * W) * (V * X * W) = (V * X * W) * (V * U * W) ↔
      U * X = X * U := by
  rw [twoSidedConjugation_mul V W U X hWV,
    twoSidedConjugation_mul V W X U hWV,
    twoSidedConjugation_eq_iff V W (U * X) (X * U) hWV]

/-- **Clock-observability-defect covariance.**  The complete finite-clock conditional-variance
defect is conjugated, not changed into a new value object, by an invertible frame switch. -/
theorem finiteCyclicObservableTwirlKadisonDefect_twoSidedConjugation
    (U X V W : E →L[𝕜] E) (N : ℕ)
    (hWV : W * V = 1) (hVW : V * W = 1) :
    finiteCyclicObservableTwirlKadisonDefect (V * U * W) (V * X * W) N =
      V * finiteCyclicObservableTwirlKadisonDefect U X N * W := by
  rw [finiteCyclicObservableTwirlKadisonDefect,
    finiteCyclicObservableTwirlKadisonDefect,
    twoSidedConjugation_mul V W X X hWV,
    finiteCyclicObservableTwirl_twoSidedConjugation U (X * X) V W N hWV hVW,
    finiteCyclicObservableTwirl_twoSidedConjugation U X V W N hWV hVW,
    twoSidedConjugation_mul V W
      (finiteCyclicObservableTwirl U X N)
      (finiteCyclicObservableTwirl U X N) hWV]
  noncomm_ring

end

end HTGeometry
