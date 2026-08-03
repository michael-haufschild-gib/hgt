import GaloisForLFunctions.RHTower.DeningerRamifiedTopConormalAmbidexterity
import GaloisForLFunctions.RHTower.DeningerCalderonWittAlgebraicSource

/-!
# Ramified top-conormal cocone on actual rational-Witt stages

Actual finite Deninger packet stages are function spaces on the quotient
`(ZMod m)ˣ / ⟨p⟩`; they do not contain the ramified zero fibre of the monic power algebra.
This file keeps those exact arithmetic labels and adjoins the forced top-conormal residue block.

Gauge-corrected rational-Witt refinement acts on the arithmetic label and leaves conormal grade
fixed.  Top embedding and residue commute with every refinement, the admitted sector is exactly
the final-grade support, and residue followed by the existing finite-stage cocone lands that
sector injectively in the literal algebraic Calderón--Witt packet.

This is a minimal finite-stage thickening.  It does not assert that the completed Xi/Gamma
realization intrinsically supplies the added conormal grade.
-/

namespace RHTower

noncomputable section

/-! ## Actual and ramified finite-stage Hilbert packets -/

/-- Standard finite Hilbert realization of one actual rational-Witt packet stage. -/
abbrev DeningerFiniteFrobeniusStageHilbert
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) :=
  DeningerRamifiedBlockHilbert
    (DeningerFiniteFrobeniusStageQuotient (p : ℕ) s)

/-- Actual packet stage with one ramified residue block of degree `n+1`. -/
abbrev DeningerRamifiedFiniteFrobeniusStageHilbert
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) (n : ℕ) :=
  DeningerRamifiedBlockHilbert
    (DeningerFiniteFrobeniusStageQuotient (p : ℕ) s × Fin (n + 1))

/-- Gauge-corrected pullback on standard Hilbert realizations of actual finite stages. -/
def deningerFiniteFrobeniusStageHilbertGaugePullback
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t)
    (x : DeningerFiniteFrobeniusStageHilbert p s) :
    DeningerFiniteFrobeniusStageHilbert p t :=
  WithLp.toLp 2 (fun q =>
    x.ofLp (deningerFiniteFrobeniusPacketGaugeTransition p hst q))

/-- Gauge-corrected pullback on the ramified stage, leaving residue grade fixed. -/
def deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t) (n : ℕ)
    (x : DeningerRamifiedFiniteFrobeniusStageHilbert p s n) :
    DeningerRamifiedFiniteFrobeniusStageHilbert p t n :=
  WithLp.toLp 2 (fun qr =>
    x.ofLp
      (deningerFiniteFrobeniusPacketGaugeTransition p hst qr.1, qr.2))

/-- Extended gauge pullbacks compose strictly. -/
theorem deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback_comp
    (p : Nat.Primes)
    {r s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hrs : r ≤ s) (hst : s ≤ t) (n : ℕ)
    (x : DeningerRamifiedFiniteFrobeniusStageHilbert p r n) :
    deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback p hst n
        (deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback p hrs n x) =
      deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback
        p (hrs.trans hst) n x := by
  ext qr
  simp only [deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback,
    WithLp.ofLp_toLp]
  rw [deningerFiniteFrobeniusPacketGaugeTransition_comp]

/-- Extended gauge pullback remains injective. -/
theorem deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback_injective
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t) (n : ℕ) :
    Function.Injective
      (deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback p hst n) := by
  intro x y hxy
  ext qr
  obtain ⟨q, hq⟩ :=
    deningerFiniteFrobeniusPacketGaugeTransition_surjective p hst qr.1
  have hpoint := congrArg (fun z => z.ofLp (q, qr.2)) hxy
  simpa only [deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback,
    WithLp.ofLp_toLp, hq] using hpoint

/-! ## Refinement-natural top-conormal structure -/

/-- Top-conormal embedding commutes with actual gauge-corrected refinement. -/
theorem deningerRamifiedFiniteStageGaugePullback_topConormalEmbedding
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t) (n : ℕ)
    (x : DeningerFiniteFrobeniusStageHilbert p s) :
    deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback p hst n
        (deningerTopConormalEmbedding n x) =
      deningerTopConormalEmbedding n
        (deningerFiniteFrobeniusStageHilbertGaugePullback p hst x) := by
  ext qr
  simp [deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback,
    deningerFiniteFrobeniusStageHilbertGaugePullback,
    deningerTopConormalEmbedding]

/-- Final-residue extraction commutes with actual gauge-corrected refinement. -/
theorem deningerTopConormalResidue_ramifiedFiniteStageGaugePullback
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t) (n : ℕ)
    (x : DeningerRamifiedFiniteFrobeniusStageHilbert p s n) :
    deningerTopConormalResidue n
        (deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback p hst n x) =
      deningerFiniteFrobeniusStageHilbertGaugePullback p hst
        (deningerTopConormalResidue n x) := by
  ext q
  rfl

/-- Final-grade support: the concrete admitted sector at one actual finite stage. -/
def DeningerRamifiedFiniteStageTopConormalAdmittedSector
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) (n : ℕ) :
    Set (DeningerRamifiedFiniteFrobeniusStageHilbert p s n) :=
  {x | ∀ q r, r ≠ Fin.last n → x.ofLp (q, r) = 0}

/-- The admitted sector is exactly the range of top-conormal embedding. -/
theorem mem_deningerRamifiedFiniteStageTopConormalAdmittedSector_iff
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) (n : ℕ)
    (x : DeningerRamifiedFiniteFrobeniusStageHilbert p s n) :
    x ∈ DeningerRamifiedFiniteStageTopConormalAdmittedSector p s n ↔
      ∃ y : DeningerFiniteFrobeniusStageHilbert p s,
        deningerTopConormalEmbedding n y = x := by
  constructor
  · intro hx
    refine ⟨deningerTopConormalResidue n x, ?_⟩
    ext qr
    rcases qr with ⟨q, r⟩
    by_cases hr : r = Fin.last n
    · subst r
      simp [deningerTopConormalEmbedding, deningerTopConormalResidue]
    · simp [deningerTopConormalEmbedding, hr, hx q r hr]
  · rintro ⟨y, rfl⟩ q r hr
    simp [deningerTopConormalEmbedding, hr]

/-- Top residue is injective after restriction to the admitted sector. -/
theorem deningerTopConormalResidue_injectiveOn_admittedSector
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) (n : ℕ) :
    Set.InjOn (deningerTopConormalResidue n)
      (DeningerRamifiedFiniteStageTopConormalAdmittedSector p s n) := by
  intro x hx y hy hres
  obtain ⟨a, ha⟩ :=
    (mem_deningerRamifiedFiniteStageTopConormalAdmittedSector_iff p s n x).mp hx
  obtain ⟨b, hb⟩ :=
    (mem_deningerRamifiedFiniteStageTopConormalAdmittedSector_iff p s n y).mp hy
  rw [← ha, ← hb, deningerTopConormalResidue_embedding,
    deningerTopConormalResidue_embedding] at hres
  rw [← ha, ← hb, hres]

/-- Every gauge refinement preserves the top-conormal admitted sector. -/
theorem deningerRamifiedFiniteStageGaugePullback_mem_admittedSector
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t) (n : ℕ)
    {x : DeningerRamifiedFiniteFrobeniusStageHilbert p s n}
    (hx : x ∈ DeningerRamifiedFiniteStageTopConormalAdmittedSector p s n) :
    deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback p hst n x ∈
      DeningerRamifiedFiniteStageTopConormalAdmittedSector p t n := by
  intro q r hr
  simp only [deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback,
    WithLp.ofLp_toLp]
  exact hx (deningerFiniteFrobeniusPacketGaugeTransition p hst q) r hr

/-! ## Coefficient-faithful landing in the literal algebraic packet -/

/-- Collapse only the forced conormal grade and use the existing actual finite-stage cocone. -/
def deningerRamifiedFiniteStageToAlgebraic
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) (n : ℕ)
    (x : DeningerRamifiedFiniteFrobeniusStageHilbert p s n) :
    DeningerPrimeFinitePacketGaugeAlgebraic p :=
  deningerPrimeFinitePacketGaugeStageToAlgebraic p s
    (deningerTopConormalResidue n x).ofLp

/-- On the top-conormal source sector, ramified landing is exactly the old arithmetic stage map. -/
theorem deningerRamifiedFiniteStageToAlgebraic_topConormalEmbedding
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) (n : ℕ)
    (x : DeningerFiniteFrobeniusStageHilbert p s) :
    deningerRamifiedFiniteStageToAlgebraic p s n
        (deningerTopConormalEmbedding n x) =
      deningerPrimeFinitePacketGaugeStageToAlgebraic p s x.ofLp := by
  rw [deningerRamifiedFiniteStageToAlgebraic,
    deningerTopConormalResidue_embedding]

/-- Ramified stage landings form a strict cocone over gauge refinement. -/
theorem deningerRamifiedFiniteStageToAlgebraic_transition
    (p : Nat.Primes)
    {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t) (n : ℕ)
    (x : DeningerRamifiedFiniteFrobeniusStageHilbert p s n) :
    deningerRamifiedFiniteStageToAlgebraic p t n
        (deningerRamifiedFiniteFrobeniusStageHilbertGaugePullback p hst n x) =
      deningerRamifiedFiniteStageToAlgebraic p s n x := by
  change
    deningerPrimeFinitePacketGaugeStageToAlgebraic p t
        (deningerFiniteFrobeniusPacketGaugeFunctionPullback p hst
          (deningerTopConormalResidue n x).ofLp) =
      deningerPrimeFinitePacketGaugeStageToAlgebraic p s
        (deningerTopConormalResidue n x).ofLp
  exact deningerPrimeFinitePacketGaugeStageToAlgebraic_transition p hst _

/-- The ramified landing is coefficient-faithful on the admitted sector. -/
theorem deningerRamifiedFiniteStageToAlgebraic_injectiveOn_admittedSector
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) (n : ℕ) :
    Set.InjOn (deningerRamifiedFiniteStageToAlgebraic p s n)
      (DeningerRamifiedFiniteStageTopConormalAdmittedSector p s n) := by
  intro x hx y hy hxy
  have hfun :
      (deningerTopConormalResidue n x).ofLp =
        (deningerTopConormalResidue n y).ofLp :=
    deningerPrimeFinitePacketGaugeStageToAlgebraic_injective p s hxy
  have hres : deningerTopConormalResidue n x =
      deningerTopConormalResidue n y := by
    ext q
    exact congrFun hfun q
  exact deningerTopConormalResidue_injectiveOn_admittedSector p s n hx hy hres

/-- Literal Hilbert adjunction on every actual rational-Witt finite stage. -/
theorem inner_deningerRamifiedFiniteStageTopConormalEmbedding_left
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) (n : ℕ)
    (x : DeningerFiniteFrobeniusStageHilbert p s)
    (y : DeningerRamifiedFiniteFrobeniusStageHilbert p s n) :
    inner ℂ (deningerTopConormalEmbedding n x) y =
      inner ℂ x (deningerTopConormalResidue n y) :=
  inner_deningerTopConormalEmbedding_left n x y

end

end RHTower
