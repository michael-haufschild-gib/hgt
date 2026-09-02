import GaloisForLFunctions.RHTower.FrankensteinMeyerHalfDensityL2KoszulDescent

/-!
# Pre-divisor Meyer--Koszul completion escape

The Meyer half-density embedding supplies a concrete comparison between strong source and Hilbert
completion before divisor specialization.  For every spectral parameter `s`, this module forms the
quotient of analytic vectors whose prime Koszul image returns to strong-source range by the
strong-source range itself.  Under analytic invertibility, this quotient vanishes exactly when the
analytic inverse preserves source provenance.  At an off-line Xi divisor it is therefore nonzero.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

abbrev DeningerMeyerHalfDensityL2Space :=
  Lp ℂ 2 (volume : Measure ℝ)

/-- The analytic prime Koszul coordinate before divisor specialization. -/
def deningerMeyerHalfDensityL2PrimeKoszulCoordinateAt
    (s : ℂ) (p : Nat.Primes) :
    DeningerMeyerHalfDensityL2Space →L[ℂ] DeningerMeyerHalfDensityL2Space :=
  primeKoszulCoord
    (fun _ : Fin 1 => MellinL2.additiveTranslationUnitary
      (Real.log (p.1 : ℝ)))
    (fun _ : Fin 1 => p.1) s 0

/-- The source prime Koszul coordinate before divisor specialization. -/
def deningerMeyerStrongLogPrimeKoszulCoordinateAt
    (s : ℂ) (p : Nat.Primes) :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget :=
  deningerMeyerStrongLogCenteredFlow (-Real.log (p.1 : ℝ)) -
    deltaS p.1 s • LinearMap.id

/-- Half-density realization intertwines the source and Hilbert Koszul coordinates for every `s`.
This is pre-divisor: `s` is an arbitrary complex parameter. -/
theorem deningerMeyerHalfDensityL2LM_primeKoszulCoordinateAt
    (s : ℂ) (p : Nat.Primes) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerHalfDensityL2LM
        (deningerMeyerStrongLogPrimeKoszulCoordinateAt s p g) =
      deningerMeyerHalfDensityL2PrimeKoszulCoordinateAt s p
        (deningerMeyerHalfDensityL2LM g) := by
  rw [deningerMeyerStrongLogPrimeKoszulCoordinateAt, LinearMap.sub_apply, map_sub,
    LinearMap.smul_apply, LinearMap.id_apply, map_smul,
    deningerMeyerHalfDensityL2LM_centeredFlow,
    deningerMeyerHalfDensityL2PrimeKoszulCoordinateAt, primeKoszulCoord,
    sub_apply, unitaryOp_apply, smul_apply, one_apply_eq_self]
  simp

/-- The embedded strong source inside the analytic Hilbert completion. -/
def deningerMeyerHalfDensityStrongRange :
    Submodule ℂ DeningerMeyerHalfDensityL2Space :=
  LinearMap.range deningerMeyerHalfDensityL2LM

/-- Vectors whose analytic Koszul image has retained strong-source provenance. -/
def deningerMeyerPrimeKoszulInverseDomainAt
    (s : ℂ) (p : Nat.Primes) :
    Submodule ℂ DeningerMeyerHalfDensityL2Space :=
  deningerMeyerHalfDensityStrongRange.comap
    (deningerMeyerHalfDensityL2PrimeKoszulCoordinateAt s p).toLinearMap

/-- Forward source transport always lies in the inverse domain. -/
theorem deningerMeyerHalfDensityStrongRange_le_inverseDomainAt
    (s : ℂ) (p : Nat.Primes) :
    deningerMeyerHalfDensityStrongRange ≤
      deningerMeyerPrimeKoszulInverseDomainAt s p := by
  rintro _ ⟨g, rfl⟩
  rw [deningerMeyerPrimeKoszulInverseDomainAt, Submodule.mem_comap]
  refine ⟨deningerMeyerStrongLogPrimeKoszulCoordinateAt s p g, ?_⟩
  exact deningerMeyerHalfDensityL2LM_primeKoszulCoordinateAt s p g

/-- Completion-escape subspace: inverse-domain vectors modulo retained source provenance. -/
def deningerMeyerPrimeKoszulCompletionEscapeAt
    (s : ℂ) (p : Nat.Primes) :
    Submodule ℂ
      (DeningerMeyerHalfDensityL2Space ⧸ deningerMeyerHalfDensityStrongRange) :=
  (deningerMeyerPrimeKoszulInverseDomainAt s p).map
    deningerMeyerHalfDensityStrongRange.mkQ

/-- Escape vanishes exactly when every inverse-domain vector retains source provenance. -/
theorem deningerMeyerPrimeKoszulCompletionEscapeAt_eq_bot_iff
    (s : ℂ) (p : Nat.Primes) :
    deningerMeyerPrimeKoszulCompletionEscapeAt s p = ⊥ ↔
      deningerMeyerPrimeKoszulInverseDomainAt s p ≤
        deningerMeyerHalfDensityStrongRange := by
  constructor
  · intro h x hx
    have hmem : deningerMeyerHalfDensityStrongRange.mkQ x ∈
        deningerMeyerPrimeKoszulCompletionEscapeAt s p := by
      exact ⟨x, hx, rfl⟩
    rw [h] at hmem
    rw [Submodule.mem_bot] at hmem
    exact (Submodule.Quotient.mk_eq_zero _).mp hmem
  · intro h
    rw [eq_bot_iff]
    rintro q ⟨x, hx, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h hx)

/-- Analytic inversion at `s` preserves the embedded strong source. -/
def DeningerMeyerHalfDensityL2ResolventPreservesStrongSourceAt
    (s : ℂ) (p : Nat.Primes) : Prop :=
  ∀ y : DeningerMeyerHalfDensityL2Space,
    y ∈ deningerMeyerHalfDensityStrongRange →
    ∃ x ∈ deningerMeyerHalfDensityStrongRange,
      deningerMeyerHalfDensityL2PrimeKoszulCoordinateAt s p x = y

/-- Under analytic invertibility, escape vanishing is exactly inverse source preservation. -/
theorem deningerMeyerPrimeKoszulCompletionEscapeAt_eq_bot_iff_preserves
    (s : ℂ) (p : Nat.Primes)
    (hbij : Function.Bijective
      (deningerMeyerHalfDensityL2PrimeKoszulCoordinateAt s p)) :
    deningerMeyerPrimeKoszulCompletionEscapeAt s p = ⊥ ↔
      DeningerMeyerHalfDensityL2ResolventPreservesStrongSourceAt s p := by
  rw [deningerMeyerPrimeKoszulCompletionEscapeAt_eq_bot_iff]
  constructor
  · intro h y hy
    obtain ⟨x, hx⟩ := hbij.2 y
    refine ⟨x, h ?_, hx⟩
    rw [deningerMeyerPrimeKoszulInverseDomainAt, Submodule.mem_comap]
    change deningerMeyerHalfDensityL2PrimeKoszulCoordinateAt s p x ∈
      deningerMeyerHalfDensityStrongRange
    rw [hx]
    exact hy
  · intro h x hx
    rw [deningerMeyerPrimeKoszulInverseDomainAt, Submodule.mem_comap] at hx
    obtain ⟨z, hz, hzx⟩ := h
      (deningerMeyerHalfDensityL2PrimeKoszulCoordinateAt s p x) hx
    have : z = x := hbij.1 hzx
    rwa [this] at hz

/-- Exact transgression: under analytic invertibility, completion escape vanishes exactly when the
source Koszul coordinate is surjective. -/
theorem deningerMeyerPrimeKoszulCompletionEscapeAt_eq_bot_iff_source_surjective
    (s : ℂ) (p : Nat.Primes)
    (hbij : Function.Bijective
      (deningerMeyerHalfDensityL2PrimeKoszulCoordinateAt s p)) :
    deningerMeyerPrimeKoszulCompletionEscapeAt s p = ⊥ ↔
      Function.Surjective (deningerMeyerStrongLogPrimeKoszulCoordinateAt s p) := by
  rw [deningerMeyerPrimeKoszulCompletionEscapeAt_eq_bot_iff_preserves s p hbij]
  constructor
  · intro h g
    obtain ⟨x, ⟨f, rfl⟩, hx⟩ := h (deningerMeyerHalfDensityL2LM g) ⟨g, rfl⟩
    refine ⟨f, deningerMeyerHalfDensityL2LM_injective ?_⟩
    rw [deningerMeyerHalfDensityL2LM_primeKoszulCoordinateAt, hx]
  · intro h y hy
    obtain ⟨g, hg⟩ := hy
    subst y
    obtain ⟨f, hf⟩ := h g
    refine ⟨deningerMeyerHalfDensityL2LM f, ⟨f, rfl⟩, ?_⟩
    rw [← deningerMeyerHalfDensityL2LM_primeKoszulCoordinateAt, hf]

/-- Every off-line Xi specialization carries nonzero completion escape at every prime. -/
theorem deningerMeyerPrimeKoszulCompletionEscapeAt_ne_bot_of_offLine
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (hrho : (rho : ℂ).re ≠ 1 / 2) :
    deningerMeyerPrimeKoszulCompletionEscapeAt (rho : ℂ) p ≠ ⊥ := by
  intro hzero
  have hbij : Function.Bijective
      (deningerMeyerHalfDensityL2PrimeKoszulCoordinateAt (rho : ℂ) p) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp
      (deningerMeyerHalfDensityL2PrimeKoszulCoordinate_isUnit_of_offLine rho p hrho)
  have hpreserve :
      DeningerMeyerHalfDensityL2ResolventPreservesStrongSourceAt (rho : ℂ) p :=
    (deningerMeyerPrimeKoszulCompletionEscapeAt_eq_bot_iff_preserves
      (rho : ℂ) p hbij).mp hzero
  exact not_halfDensityL2ResolventPreservesStrongSource_of_offLine rho p hrho
    hpreserve

/-- Closed pre-divisor completion-defect law at every Xi specialization. -/
theorem deningerMeyerPrimeKoszulCompletionEscape_law :
    ∀ (rho : XiDivisorSupport) (p : Nat.Primes),
      ((rho : ℂ).re ≠ 1 / 2 →
        deningerMeyerPrimeKoszulCompletionEscapeAt (rho : ℂ) p ≠ ⊥) ∧
      (deningerMeyerPrimeKoszulCompletionEscapeAt (rho : ℂ) p = ⊥ →
        (rho : ℂ).re = 1 / 2) := by
  intro rho p
  constructor
  · exact deningerMeyerPrimeKoszulCompletionEscapeAt_ne_bot_of_offLine rho p
  · contrapose!
    exact deningerMeyerPrimeKoszulCompletionEscapeAt_ne_bot_of_offLine rho p

end

end RHTower
