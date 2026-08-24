import GaloisForLFunctions.RHTower.DeningerPeriodizationMap

/-!
# Canonical all-prime Deninger tomography Hasse principle

Periodize an exponential-Schwartz source at the logarithm of every prime.  Cofinality of the prime
periods makes the resulting tomography faithful without choosing a separate infinite prime family.
Equality and vanishing are detected pointwise, every nonzero source is witnessed by one prime and
one real time, and the source space is linearly equivalent to its realized tomograms.

This supplies prime-local observability for Connes--Deninger and local-place routes.  It is not an
arithmetic identification between the resulting periods and a Brauer invariant.
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-- Canonical tomography over every prime logarithmic period. -/
noncomputable def deningerPrimeTomographyMap :
    DeningerExpSchwartz →ₗ[ℂ]
      ((q : Nat.Primes) → DeningerSmoothPeriodic (Real.log (q : ℕ))) :=
  deningerTomographyMap (fun q : Nat.Primes ↦ Real.log (q : ℕ))
    (fun q ↦ Real.log_pos (by exact_mod_cast q.2.one_lt))

/-- Canonical all-prime tomography is injective without a chosen prime-family premise. -/
theorem deningerPrimeTomographyMap_injective :
    Function.Injective deningerPrimeTomographyMap := by
  exact deningerTomographyMap_injective
    (Q := {q : ℕ | Nat.Prime q}) Nat.infinite_setOf_prime
      (fun _ hq ↦ hq) (fun q ↦ Real.log_pos (by exact_mod_cast q.2.one_lt))

/-- Exponential-Schwartz sources are linearly equivalent to realized all-prime tomograms. -/
noncomputable def deningerPrimeTomographyEquivRange :
    DeningerExpSchwartz ≃ₗ[ℂ] LinearMap.range deningerPrimeTomographyMap :=
  LinearEquiv.ofInjective deningerPrimeTomographyMap
    deningerPrimeTomographyMap_injective

/-- Pointwise prime-period Hasse congruence for exponential-Schwartz sources. -/
theorem deningerExpSchwartz_congr_primeTomography_hasse_iff
    (f g : DeningerExpSchwartz) :
    f = g ↔ ∀ (q : Nat.Primes) (t : ℝ),
      (((deningerPrimeTomographyMap f q :
          DeningerSmoothPeriodic (Real.log (q : ℕ))) : ℝ → ℂ) t) =
        (((deningerPrimeTomographyMap g q :
          DeningerSmoothPeriodic (Real.log (q : ℕ))) : ℝ → ℂ) t) := by
  constructor
  · rintro rfl
    exact fun _ _ ↦ rfl
  · intro h
    apply deningerPrimeTomographyMap_injective
    funext q
    apply Subtype.ext
    funext t
    exact h q t

/-- A source vanishes exactly when all prime-periodized values vanish. -/
theorem deningerExpSchwartz_eq_zero_primeTomography_hasse_iff
    (f : DeningerExpSchwartz) :
    f = 0 ↔ ∀ (q : Nat.Primes) (t : ℝ),
      (((deningerPrimeTomographyMap f q :
          DeningerSmoothPeriodic (Real.log (q : ℕ))) : ℝ → ℂ) t) = 0 := by
  rw [deningerExpSchwartz_congr_primeTomography_hasse_iff]
  simp

/-- Every nonzero source is detected by one prime period at one real time. -/
theorem exists_primePeriodization_ne_zero_of_deningerExpSchwartz_ne_zero
    (f : DeningerExpSchwartz) (hf : f ≠ 0) :
    ∃ (q : Nat.Primes) (t : ℝ),
      (((deningerPrimeTomographyMap f q :
          DeningerSmoothPeriodic (Real.log (q : ℕ))) : ℝ → ℂ) t) ≠ 0 := by
  by_contra h
  push Not at h
  exact hf ((deningerExpSchwartz_eq_zero_primeTomography_hasse_iff f).2 h)

end

end RHTower
