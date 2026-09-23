import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEPerturbativeGradeSeparation

/-!
# Third-order Einstein--Teukolsky resonance-source cohomology

Write the Taylor expansion of a gauge-fixed Einstein operator as

`E(g + h) = L h + (1/2) B(h,h) + (1/6) C(h,h,h) + O(h^(4 : ℕ))`.

For a real one-mode perturbation, let `h₊, h₋` be the two linear frequency branches and let
`h₊₊, h₊₋, h₋₋` be the three second-order coefficients. Exact expansion shows that the cubic
`++-` coefficient is

`B(h₊,h₊₋) + B(h₋,h₊₊)
  + (C(h₊,h₊,h₋) + C(h₊,h₋,h₊) + C(h₋,h₊,h₊))/6`.

Thus the AIME mass-memory cascade is not the complete same-grade source. A second-harmonic
cascade and the direct third variation have exactly the same grade. If `P` is an idempotent
mass-charge projector, `h₊₋ = P h₊₋ + (1-P)h₊₋` is the unique split whose first component lies
in the charge sector and whose second component lies in `ker P`.

Let `ell` be a left resonant state for `L`. Since `ell ∘ L = 0`, every gauge-exact source lies
invisible to the resonant projection. Consequently a cancellation of a nonzero AIME projection
forces at least one of the orthogonal stationary cascade, second-harmonic cascade, or direct cubic
vertex to define a nonzero class modulo `range L`. This is the precise obstruction left after
gauge fixing; positivity and passivity do not determine that cokernel class.
-/

open Complex

namespace RHTower

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Hessian coupling between a linear two-branch field and a general quadratic response. -/
def d4EinsteinThirdOrderQuadraticCascade
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus hPlusPlus hPlusMinus hMinusMinus : V) (x y : ℂ) : V :=
  B (x • hPlus + y • hMinus)
    (x ^ (2 : ℕ) • hPlusPlus + (x * y) • hPlusMinus + y ^ (2 : ℕ) • hMinusMinus)

/-- Exact four-grade expansion of the Hessian contribution at third perturbative order. -/
theorem d4EinsteinThirdOrderQuadraticCascade_eq
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus hPlusPlus hPlusMinus hMinusMinus : V) (x y : ℂ) :
    d4EinsteinThirdOrderQuadraticCascade B hPlus hMinus hPlusPlus hPlusMinus
        hMinusMinus x y =
      x ^ (3 : ℕ) • B hPlus hPlusPlus +
      (x ^ (2 : ℕ) * y) • (B hPlus hPlusMinus + B hMinus hPlusPlus) +
      (x * y ^ (2 : ℕ)) • (B hPlus hMinusMinus + B hMinus hPlusMinus) +
      y ^ (3 : ℕ) • B hMinus hMinusMinus := by
  simp [d4EinsteinThirdOrderQuadraticCascade, map_add, map_smul]
  module

/-- Third-variation contribution evaluated on the real two-branch linear field. -/
def d4EinsteinDirectThirdVariation
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus : V) (x y : ℂ) : V :=
  (1 / 6 : ℂ) •
    C (x • hPlus + y • hMinus) (x • hPlus + y • hMinus)
      (x • hPlus + y • hMinus)

/-- Direct third-variation coefficient in the `++-` grade, without assuming permutation
symmetry of the displayed trilinear representative. -/
def d4EinsteinDirectThirdVariationPlusPlusMinus
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus : V) : V :=
  (1 / 6 : ℂ) •
    (C hPlus hPlus hMinus + C hPlus hMinus hPlus + C hMinus hPlus hPlus)

/-- Exact four-grade expansion of the direct third variation. -/
theorem d4EinsteinDirectThirdVariation_eq
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus : V) (x y : ℂ) :
    d4EinsteinDirectThirdVariation C hPlus hMinus x y =
      (1 / 6 : ℂ) •
        (x ^ (3 : ℕ) • C hPlus hPlus hPlus +
        (x ^ (2 : ℕ) * y) •
          (C hPlus hPlus hMinus + C hPlus hMinus hPlus + C hMinus hPlus hPlus) +
        (x * y ^ (2 : ℕ)) •
          (C hPlus hMinus hMinus + C hMinus hPlus hMinus + C hMinus hMinus hPlus) +
        y ^ (3 : ℕ) • C hMinus hMinus hMinus) := by
  simp [d4EinsteinDirectThirdVariation, map_add, map_smul]
  module

/-- Permutation symmetry reduces the direct `++-` coefficient to
`C(h₊,h₊,h₋)/2`. -/
theorem d4EinsteinDirectThirdVariationPlusPlusMinus_eq_half
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus : V)
    (h₁ : C hPlus hMinus hPlus = C hPlus hPlus hMinus)
    (h₂ : C hMinus hPlus hPlus = C hPlus hPlus hMinus) :
    d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus =
      (1 / 2 : ℂ) • C hPlus hPlus hMinus := by
  simp [d4EinsteinDirectThirdVariationPlusPlusMinus, h₁, h₂]
  module

/-- Complete nonlinear Einstein source coefficient in the `++-` grade. -/
def d4EinsteinThirdOrderPlusPlusMinusSource
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus hPlusPlus hPlusMinus : V) : V :=
  B hPlus hPlusMinus + B hMinus hPlusPlus +
    d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus

/-- Complete nonlinear Einstein source coefficient in the pure `+++` grade. -/
def d4EinsteinThirdOrderPurePlusSource
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hPlusPlus : V) : V :=
  B hPlus hPlusPlus + (1 / 6 : ℂ) • C hPlus hPlus hPlus

/-- Complete nonlinear Einstein source coefficient in the `+--` grade. -/
def d4EinsteinThirdOrderPlusMinusMinusSource
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus hPlusMinus hMinusMinus : V) : V :=
  B hPlus hMinusMinus + B hMinus hPlusMinus +
    (1 / 6 : ℂ) •
      (C hPlus hMinus hMinus + C hMinus hPlus hMinus + C hMinus hMinus hPlus)

/-- Complete nonlinear Einstein source coefficient in the pure `---` grade. -/
def d4EinsteinThirdOrderPureMinusSource
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hMinus hMinusMinus : V) : V :=
  B hMinus hMinusMinus + (1 / 6 : ℂ) • C hMinus hMinus hMinus

/-- Full nonlinear coefficient at third perturbative order. -/
def d4EinsteinThirdOrderNonlinearSource
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus hPlusPlus hPlusMinus hMinusMinus : V) (x y : ℂ) : V :=
  d4EinsteinThirdOrderQuadraticCascade B hPlus hMinus hPlusPlus hPlusMinus
      hMinusMinus x y +
    d4EinsteinDirectThirdVariation C hPlus hMinus x y

/-- Source-faithful helicity decomposition of the third-order Einstein Taylor coefficient. -/
theorem d4EinsteinThirdOrderNonlinearSource_eq
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus hPlusPlus hPlusMinus hMinusMinus : V) (x y : ℂ) :
    d4EinsteinThirdOrderNonlinearSource B C hPlus hMinus hPlusPlus hPlusMinus
        hMinusMinus x y =
      x ^ (3 : ℕ) • d4EinsteinThirdOrderPurePlusSource B C hPlus hPlusPlus +
      (x ^ (2 : ℕ) * y) •
        d4EinsteinThirdOrderPlusPlusMinusSource B C hPlus hMinus hPlusPlus hPlusMinus +
      (x * y ^ (2 : ℕ)) •
        d4EinsteinThirdOrderPlusMinusMinusSource B C hPlus hMinus hPlusMinus hMinusMinus +
      y ^ (3 : ℕ) • d4EinsteinThirdOrderPureMinusSource B C hMinus hMinusMinus := by
  rw [d4EinsteinThirdOrderNonlinearSource, d4EinsteinThirdOrderQuadraticCascade_eq,
    d4EinsteinDirectThirdVariation_eq]
  simp [d4EinsteinThirdOrderPurePlusSource, d4EinsteinThirdOrderPlusPlusMinusSource,
    d4EinsteinThirdOrderPlusMinusMinusSource, d4EinsteinThirdOrderPureMinusSource,
    d4EinsteinDirectThirdVariationPlusPlusMinus]
  module

/-- A charge projector splits the `++-` source into AIME, charge-orthogonal stationary,
second-harmonic, and direct-third-variation channels. -/
theorem d4EinsteinThirdOrderPlusPlusMinusSource_chargeSplit
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (P : V →ₗ[ℂ] V) (hPlus hMinus hPlusPlus hPlusMinus : V) :
    d4EinsteinThirdOrderPlusPlusMinusSource B C hPlus hMinus hPlusPlus hPlusMinus =
      B hPlus (P hPlusMinus) +
      (B hPlus (hPlusMinus - P hPlusMinus) + B hMinus hPlusPlus +
        d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus) := by
  simp [d4EinsteinThirdOrderPlusPlusMinusSource]
  module

/-- Any decomposition into a projector-fixed charge part and a projector-null remainder is the
canonical projector split. -/
theorem d4EinsteinChargeProjector_split_unique
    (P : V →ₗ[ℂ] V) (h memory remainder : V)
    (hsum : h = memory + remainder) (hmemory : P memory = memory)
    (hremainder : P remainder = 0) :
    memory = P h ∧ remainder = h - P h := by
  constructor
  · rw [hsum, map_add, hmemory, hremainder, add_zero]
  · rw [hsum]
    have hprojected : P (memory + remainder) = memory := by
      simp [map_add, hmemory, hremainder]
    rw [hprojected]
    abel

/-- Every idempotent charge map gives the canonical charge-plus-kernel decomposition. -/
theorem d4EinsteinChargeProjector_canonicalSplit
    (P : V →ₗ[ℂ] V) (hP : ∀ v, P (P v) = P v) (h : V) :
    h = P h + (h - P h) ∧ P (P h) = P h ∧ P (h - P h) = 0 := by
  constructor
  · abel
  constructor
  · exact hP h
  · simp [map_sub, hP]

/-- A left resonant state annihilates every source change in the range of the linearized
Einstein--Teukolsky operator. -/
theorem d4TeukolskyResonantProjection_add_range
    (L : V →ₗ[ℂ] V) (ell : V →ₗ[ℂ] ℂ)
    (hleft : ∀ v, ell (L v) = 0) (source gauge : V) :
    ell (source + L gauge) = ell source := by
  simp [map_add, hleft]

/-- If all three non-AIME channels are linearized-operator exact, the full resonant projection
equals the AIME projection. -/
theorem d4TeukolskyResonantProjection_fullSource_of_exact_remainders
    (L : V →ₗ[ℂ] V) (ell : V →ₗ[ℂ] ℂ)
    (hleft : ∀ v, ell (L v) = 0)
    (aime orthogonal secondHarmonic direct : V)
    (gOrthogonal gSecondHarmonic gDirect : V)
    (hOrthogonal : orthogonal = L gOrthogonal)
    (hSecondHarmonic : secondHarmonic = L gSecondHarmonic)
    (hDirect : direct = L gDirect) :
    ell (aime + orthogonal + secondHarmonic + direct) = ell aime := by
  subst orthogonal
  subst secondHarmonic
  subst direct
  simp [map_add, hleft]

/-- At an Xi descendant, a nonzero AIME seed cannot be cancelled by three gauge-exact
third-order channels. -/
theorem d4ThetaAIMEFullThirdOrderResonantProjection_ne_zero_of_exact_remainders
    (L : V →ₗ[ℂ] V) (ell : V →ₗ[ℂ] ℂ)
    (hleft : ∀ v, ell (L v) = 0)
    (amplitude : ℂ) (q : XiZeroCopy) (ha : amplitude ≠ 0)
    (aime orthogonal secondHarmonic direct : V)
    (gOrthogonal gSecondHarmonic gDirect : V)
    (hAIME : ell aime =
      d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q))
    (hOrthogonal : orthogonal = L gOrthogonal)
    (hSecondHarmonic : secondHarmonic = L gSecondHarmonic)
    (hDirect : direct = L gDirect) :
    ell (aime + orthogonal + secondHarmonic + direct) ≠ 0 := by
  rw [d4TeukolskyResonantProjection_fullSource_of_exact_remainders L ell hleft aime
    orthogonal secondHarmonic direct gOrthogonal gSecondHarmonic gDirect hOrthogonal
    hSecondHarmonic hDirect, hAIME]
  exact (d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr ha

/-- Cancellation of a nonzero resonant AIME coefficient forces a nonzero resonant projection in
at least one of the other three same-grade channels. -/
theorem d4TeukolskyResonantCancellation_forces_physical_remainder
    (ell : V →ₗ[ℂ] ℂ) (aime orthogonal secondHarmonic direct : V)
    (hAIME : ell aime ≠ 0)
    (hcancel : ell (aime + orthogonal + secondHarmonic + direct) = 0) :
    ell orthogonal ≠ 0 ∨ ell secondHarmonic ≠ 0 ∨ ell direct ≠ 0 := by
  by_contra h
  rw [not_or, not_or] at h
  rcases h with ⟨hOrthogonal, hSecondHarmonic, hDirect⟩
  rw [not_ne_iff] at hOrthogonal hSecondHarmonic hDirect
  simp [map_add, hOrthogonal, hSecondHarmonic, hDirect] at hcancel
  exact hAIME hcancel

/-- In cokernel form, cancellation forces at least one non-AIME channel to lie outside the range
of the linearized Einstein--Teukolsky operator. -/
theorem d4TeukolskyResonantCancellation_forces_nonexact_remainder
    (L : V →ₗ[ℂ] V) (ell : V →ₗ[ℂ] ℂ)
    (hleft : ∀ v, ell (L v) = 0)
    (aime orthogonal secondHarmonic direct : V)
    (hAIME : ell aime ≠ 0)
    (hcancel : ell (aime + orthogonal + secondHarmonic + direct) = 0) :
    (¬ ∃ gauge, orthogonal = L gauge) ∨
      (¬ ∃ gauge, secondHarmonic = L gauge) ∨
      (¬ ∃ gauge, direct = L gauge) := by
  rcases d4TeukolskyResonantCancellation_forces_physical_remainder ell aime orthogonal
      secondHarmonic direct hAIME hcancel with hOrthogonal | hSecondHarmonic | hDirect
  · left
    rintro ⟨gauge, rfl⟩
    exact hOrthogonal (hleft gauge)
  · right; left
    rintro ⟨gauge, rfl⟩
    exact hSecondHarmonic (hleft gauge)
  · right; right
    rintro ⟨gauge, rfl⟩
    exact hDirect (hleft gauge)

/-- Applied to the canonical charge split, cancellation forces a nonexact orthogonal stationary
cascade, second-harmonic cascade, or direct third-variation vertex. -/
theorem d4EinsteinThirdOrderPlusPlusMinusCancellation_forces_nonexact_channel
    (L : V →ₗ[ℂ] V) (ell : V →ₗ[ℂ] ℂ)
    (hleft : ∀ v, ell (L v) = 0)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (P : V →ₗ[ℂ] V) (hPlus hMinus hPlusPlus hPlusMinus : V)
    (hAIME : ell (B hPlus (P hPlusMinus)) ≠ 0)
    (hcancel : ell
      (d4EinsteinThirdOrderPlusPlusMinusSource B C hPlus hMinus hPlusPlus hPlusMinus) = 0) :
    (¬ ∃ gauge, B hPlus (hPlusMinus - P hPlusMinus) = L gauge) ∨
      (¬ ∃ gauge, B hMinus hPlusPlus = L gauge) ∨
      (¬ ∃ gauge,
        d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus = L gauge) := by
  rw [d4EinsteinThirdOrderPlusPlusMinusSource_chargeSplit B C P hPlus hMinus hPlusPlus
    hPlusMinus] at hcancel
  apply d4TeukolskyResonantCancellation_forces_nonexact_remainder L ell hleft
    (B hPlus (P hPlusMinus)) (B hPlus (hPlusMinus - P hPlusMinus))
      (B hMinus hPlusPlus) (d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus)
      hAIME
  simpa only [add_assoc] using hcancel

end


end RHTower
