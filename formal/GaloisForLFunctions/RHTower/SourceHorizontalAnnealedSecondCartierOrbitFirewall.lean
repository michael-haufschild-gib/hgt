import GaloisForLFunctions.RHTower.SourceHorizontalAnnealedEscortVacuumStaging
import GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierOrbitCoercivity

/-!
# Annealed second-Cartier orbit firewall

Pre-vacuum escort annealing scales the source-horizontal grade by `alpha`.  This file transports
that exact staging law into the positive two-sided second-Cartier orbit.  Every nonzero annealing
exponent preserves the coefficient-faithful hyperbolic obstruction: on a strict-right Xi fibre,
the annealed orbit is bounded only at `alpha = 0`.  The zero exponent makes the character unitary
by erasing its horizontal grade, not by proving the divisor is central.

Consequently universal boundedness of the annealed actual-Xi orbit is exactly the disjunction
`alpha = 0 ∨ RiemannHypothesis`.  This rules out annealing, tempering, and memory attenuation as
standalone producers for every route using the common source-horizontal second-Cartier landing.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Horizontal annealing preserves the vertical phase and scales only displacement from the
critical line. -/
def sourceHorizontalAnnealedXiPoint (alpha : ℝ) (s : ℂ) : ℂ :=
  ⟨1 / 2 + alpha * (s.re - 1 / 2), s.im⟩

theorem sourceHorizontalAnnealedXiPoint_re (alpha : ℝ) (s : ℂ) :
    (sourceHorizontalAnnealedXiPoint alpha s).re =
      1 / 2 + alpha * (s.re - 1 / 2) := rfl

/-- Zero-temperature annealing collapses horizontal grade while retaining vertical phase. -/
theorem sourceHorizontalAnnealedXiPoint_zero (s : ℂ) :
    sourceHorizontalAnnealedXiPoint 0 s = ⟨1 / 2, s.im⟩ := by
  apply Complex.ext <;> simp [sourceHorizontalAnnealedXiPoint]

/-- Half-density character of the annealed actual-Xi source point. -/
def sourceHorizontalAnnealedActualXiSecondCartierPrimeCharacter
    (alpha : ℝ) (q : XiRightZeroCopy) (p : Nat.Primes) : ℂ :=
  bilateralHalfDensityCharacter p
    (sourceHorizontalAnnealedXiPoint alpha (q.1.1 : XiDivisorSupport))

/-- On a strict-right Xi fibre, annealing makes the character unitary exactly by setting the
annealing exponent to zero.  No nonzero temperature moves that fibre to the unitary locus. -/
theorem norm_sourceHorizontalAnnealedActualXiSecondCartierPrimeCharacter_eq_one_iff
    (alpha : ℝ) (q : XiRightZeroCopy) (p : Nat.Primes) :
    ‖sourceHorizontalAnnealedActualXiSecondCartierPrimeCharacter alpha q p‖ = 1 ↔
      alpha = 0 := by
  rw [sourceHorizontalAnnealedActualXiSecondCartierPrimeCharacter,
    norm_bilateralHalfDensityCharacter_eq_one_iff p.2.two_le,
    sourceHorizontalAnnealedXiPoint_re]
  have hright : ((q.1.1 : XiDivisorSupport) : ℂ).re - 1 / 2 ≠ 0 := by
    have hcenter := xiRightCenteredZero_re_pos q
    rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hcenter
    norm_num at hcenter ⊢
    linarith
  constructor
  · intro h
    have hprod : alpha * (((q.1.1 : XiDivisorSupport) : ℂ).re - 1 / 2) = 0 := by
      linarith
    exact (mul_eq_zero.mp hprod).resolve_right hright
  · rintro rfl
    ring

/-- Coefficient-faithful bounded-orbit assertion after annealing one actual Xi fibre. -/
def SourceHorizontalAnnealedActualXiSecondCartierKreinPolarizedGhostOrbitBounded
    (alpha x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (p : Nat.Primes) : Prop :=
  SourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded
    (sourceHorizontalAnnealedActualXiSecondCartierPrimeCharacter alpha q p)
    (sourceHorizontalActualXiSecondCartierKreinScale x u q r N)

/-- Exact single-fibre firewall: a nondegenerate coefficient-faithful second-Cartier orbit cannot
be regularized by any nonzero annealing exponent. -/
theorem sourceHorizontalAnnealedActualXiSecondCartierKreinOrbitBounded_iff_alpha_eq_zero
    {x u r : ℝ} (alpha : ℝ) (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    SourceHorizontalAnnealedActualXiSecondCartierKreinPolarizedGhostOrbitBounded
        alpha x u q r N p ↔ alpha = 0 := by
  have hlam :
      sourceHorizontalAnnealedActualXiSecondCartierPrimeCharacter alpha q p ≠ 0 :=
    bilateralHalfDensityCharacter_ne_zero (by exact_mod_cast p.2.pos) _
  have hc := sourceHorizontalSecondCartierPointedKrein_actual_scale_ne_zero
    q hkappa hr N hjet
  rw [SourceHorizontalAnnealedActualXiSecondCartierKreinPolarizedGhostOrbitBounded,
    sourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded_iff hlam hc,
    norm_sourceHorizontalAnnealedActualXiSecondCartierPrimeCharacter_eq_one_iff]

/-- Universal boundedness of annealed coefficient-faithful actual-Xi second-Cartier orbits. -/
def EverySourceHorizontalAnnealedActualXiSecondCartierKreinOrbitBounded
    (alpha x u r : ℝ) (N : ℕ) (p : Nat.Primes) : Prop :=
  ∀ q : XiRightZeroCopy,
    SourceHorizontalAnnealedActualXiSecondCartierKreinPolarizedGhostOrbitBounded
      alpha x u q r N p

/-- **Annealing/RH trilemma.** Universal boundedness holds only through degenerate horizontal
collapse (`alpha = 0`) or through absence of strict-right Xi fibres (RH).  Thus every nonzero
coefficient-faithful annealing exponent leaves the original RH-strength moderation core intact. -/
theorem everySourceHorizontalAnnealedActualXiSecondCartierKreinOrbitBounded_iff
    {x u r : ℝ} (alpha : ℝ)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    EverySourceHorizontalAnnealedActualXiSecondCartierKreinOrbitBounded
        alpha x u r N p ↔ alpha = 0 ∨ RiemannHypothesis := by
  constructor
  · intro hbounded
    by_cases halpha : alpha = 0
    · exact Or.inl halpha
    · right
      by_contra hRH
      obtain ⟨q⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
      exact halpha
        ((sourceHorizontalAnnealedActualXiSecondCartierKreinOrbitBounded_iff_alpha_eq_zero
          alpha q hkappa hr N hjet p).1 (hbounded q))
  · rintro (halpha | hRH)
    · intro q
      exact
        (sourceHorizontalAnnealedActualXiSecondCartierKreinOrbitBounded_iff_alpha_eq_zero
          alpha q hkappa hr N hjet p).2 halpha
    · haveI : IsEmpty XiRightZeroCopy := isEmpty_xiRightZeroCopy_of_riemannHypothesis hRH
      exact fun q => isEmptyElim q

end

end RHTower
