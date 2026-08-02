import GaloisForLFunctions.RHTower.DeningerPrimeFinitePacketInverseLimit
import GaloisForLFunctions.RHTower.DeningerRationalWittPacketGaugeDescent
import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Global affine limit of the rational-Witt packet gauge

The finite rational-Witt transitions are dual not to the standard packet maps but to affine
gauge transitions

`q ↦ [aₛₜ] · ρₛₜ(q)`.

Their strict composition makes a genuine finite inverse system, but not an inverse system of
groups.  This module proves the global classification:

* the affine gauge limit is nonempty;
* the standard packet inverse limit acts simply transitively on it;
* hence it is a torsor under the literal Deninger packet;
* any chosen coherent gauge section yields a homeomorphism with the actual compact packet; and
* normalized packet Haar measure and its faithful continuous-to-`L²` channel transport to the
  affine limit.

Thus independent primitive-root gauges create no extra global packet states.  What is absent
from the affine presentation is a distinguished group origin; no group structure is imposed on
the gauge limit.
-/

namespace RHTower

open CategoryTheory
open MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

noncomputable section

/-- The gauge-corrected finite packet system as a type-valued inverse functor. -/
noncomputable def deningerPrimeFinitePacketGaugeFunctor (p : Nat.Primes) :
    (DeningerFiniteFrobeniusStage (p : ℕ))ᵒᵖ ⥤ Type where
  obj s :=
    DeningerFiniteFrobeniusStageQuotient (p : ℕ) (Opposite.unop s)
  map f :=
    ↾(deningerFiniteFrobeniusPacketGaugeTransition p (leOfHom f.unop))
  map_id s := by
    ext q
    exact deningerFiniteFrobeniusPacketGaugeTransition_refl p
      (Opposite.unop s) q
  map_comp f g := by
    ext q
    exact
      (deningerFiniteFrobeniusPacketGaugeTransition_comp p
        (leOfHom g.unop) (leOfHom f.unop) q).symm

/-- Coherent families for the affine, gauge-corrected finite packet transitions. -/
abbrev DeningerPrimeFinitePacketGaugeLimit (p : Nat.Primes) :=
  {x : ∀ s : DeningerFiniteFrobeniusStage (p : ℕ),
      DeningerFiniteFrobeniusStageQuotient (p : ℕ) s //
    ∀ {s t : DeningerFiniteFrobeniusStage (p : ℕ)} (hst : s ≤ t),
      deningerFiniteFrobeniusPacketGaugeTransition p hst (x t) = x s}

/-- The affine gauge limit has a coherent point.  This is a finite inverse-limit theorem,
not a choice of a stagewise origin. -/
theorem deningerPrimeFinitePacketGaugeLimit_nonempty (p : Nat.Primes) :
    Nonempty (DeningerPrimeFinitePacketGaugeLimit p) := by
  letI hfinite :
      ∀ j : (DeningerFiniteFrobeniusStage (p : ℕ))ᵒᵖ,
        Finite ((deningerPrimeFinitePacketGaugeFunctor p).obj j) :=
    fun j => by
      dsimp [deningerPrimeFinitePacketGaugeFunctor]
      infer_instance
  letI hnonempty :
      ∀ j : (DeningerFiniteFrobeniusStage (p : ℕ))ᵒᵖ,
        Nonempty ((deningerPrimeFinitePacketGaugeFunctor p).obj j) :=
    fun j => by
      dsimp [deningerPrimeFinitePacketGaugeFunctor]
      infer_instance
  obtain ⟨x, hx⟩ :=
    nonempty_sections_of_finite_inverse_system
      (deningerPrimeFinitePacketGaugeFunctor p)
  refine ⟨⟨fun s => x (Opposite.op s), ?_⟩⟩
  intro s t hst
  have hsec := hx ((homOfLE hst).op)
  exact hsec

/-- One noncanonical coherent affine origin, used only to exhibit a trivialization. -/
noncomputable def deningerPrimeFinitePacketGaugeLimitBasepoint
    (p : Nat.Primes) :
    DeningerPrimeFinitePacketGaugeLimit p :=
  Classical.choice (deningerPrimeFinitePacketGaugeLimit_nonempty p)

/-- Coordinatewise action of a coherent standard packet on a coherent affine packet. -/
noncomputable def deningerPrimeFinitePacketGaugeLimitMul
    (p : Nat.Primes)
    (a : DeningerPrimeFinitePacketGaugeLimit p)
    (x : DeningerPrimeFinitePacketLimit p) :
    DeningerPrimeFinitePacketGaugeLimit p :=
  ⟨fun s => a.1 s * x.1 s, by
    intro s t hst
    change
      (QuotientGroup.mk
          (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst) :
          DeningerFiniteFrobeniusStageQuotient (p : ℕ) s) *
          deningerFiniteFrobeniusStageQuotientMap hst
            (a.1 t * x.1 t) =
        a.1 s * x.1 s
    have ha := a.2 hst
    change
      (QuotientGroup.mk
          (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst) :
          DeningerFiniteFrobeniusStageQuotient (p : ℕ) s) *
          deningerFiniteFrobeniusStageQuotientMap hst (a.1 t) =
        a.1 s at ha
    rw [map_mul, ← mul_assoc, ha, x.2 hst]⟩

/-- Difference of two affine coherent packets is a coherent standard packet. -/
noncomputable def deningerPrimeFinitePacketGaugeLimitDiv
    (p : Nat.Primes)
    (a b : DeningerPrimeFinitePacketGaugeLimit p) :
    DeningerPrimeFinitePacketLimit p :=
  ⟨fun s => (a.1 s)⁻¹ * b.1 s, by
    intro s t hst
    change deningerFiniteFrobeniusStageQuotientMap hst
        ((a.1 t)⁻¹ * b.1 t) =
      (a.1 s)⁻¹ * b.1 s
    rw [map_mul, map_inv]
    have ha := a.2 hst
    have hb := b.2 hst
    change
      (QuotientGroup.mk
          (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst) :
          DeningerFiniteFrobeniusStageQuotient (p : ℕ) s) *
          deningerFiniteFrobeniusStageQuotientMap hst (a.1 t) =
        a.1 s at ha
    change
      (QuotientGroup.mk
          (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst) :
          DeningerFiniteFrobeniusStageQuotient (p : ℕ) s) *
          deningerFiniteFrobeniusStageQuotientMap hst (b.1 t) =
        b.1 s at hb
    rw [← ha, ← hb]
    let g :
        DeningerFiniteFrobeniusStageQuotient (p : ℕ) s :=
      QuotientGroup.mk
        (deningerPrimeFiniteWittCyclotomicGaugeUnit p hst)
    let A := deningerFiniteFrobeniusStageQuotientMap hst (a.1 t)
    let B := deningerFiniteFrobeniusStageQuotientMap hst (b.1 t)
    change A⁻¹ * B = (g * A)⁻¹ * (g * B)
    rw [inv_mul_eq_inv_mul_iff_mul_eq_mul]
    simpa only [mul_assoc] using
      congrArg (fun z => z * A) (mul_comm B g)⟩

theorem deningerPrimeFinitePacketGaugeLimitMul_div
    (p : Nat.Primes)
    (a b : DeningerPrimeFinitePacketGaugeLimit p) :
    deningerPrimeFinitePacketGaugeLimitMul p a
        (deningerPrimeFinitePacketGaugeLimitDiv p a b) = b := by
  apply Subtype.ext
  funext s
  simp [deningerPrimeFinitePacketGaugeLimitMul,
    deningerPrimeFinitePacketGaugeLimitDiv]

theorem deningerPrimeFinitePacketGaugeLimitDiv_mul
    (p : Nat.Primes)
    (a : DeningerPrimeFinitePacketGaugeLimit p)
    (x : DeningerPrimeFinitePacketLimit p) :
    deningerPrimeFinitePacketGaugeLimitDiv p a
        (deningerPrimeFinitePacketGaugeLimitMul p a x) = x := by
  apply Subtype.ext
  funext s
  simp [deningerPrimeFinitePacketGaugeLimitMul,
    deningerPrimeFinitePacketGaugeLimitDiv]

/-- **Torsor theorem.**  The standard packet inverse limit acts simply transitively on the
affine rational-Witt gauge limit. -/
theorem deningerPrimeFinitePacketGaugeLimit_simplyTransitive
    (p : Nat.Primes)
    (a b : DeningerPrimeFinitePacketGaugeLimit p) :
    ∃! x : DeningerPrimeFinitePacketLimit p,
      deningerPrimeFinitePacketGaugeLimitMul p a x = b := by
  refine ⟨deningerPrimeFinitePacketGaugeLimitDiv p a b,
    deningerPrimeFinitePacketGaugeLimitMul_div p a b, ?_⟩
  intro x hx
  calc
    x = deningerPrimeFinitePacketGaugeLimitDiv p a
        (deningerPrimeFinitePacketGaugeLimitMul p a x) :=
      (deningerPrimeFinitePacketGaugeLimitDiv_mul p a x).symm
    _ = deningerPrimeFinitePacketGaugeLimitDiv p a b := congrArg _ hx

/-- A chosen coherent affine point trivializes the torsor. -/
noncomputable def deningerPrimeFinitePacketGaugeLimitEquiv
    (p : Nat.Primes) :
    DeningerPrimeFinitePacketLimit p ≃
      DeningerPrimeFinitePacketGaugeLimit p where
  toFun :=
    deningerPrimeFinitePacketGaugeLimitMul p
      (deningerPrimeFinitePacketGaugeLimitBasepoint p)
  invFun a :=
    deningerPrimeFinitePacketGaugeLimitDiv p
      (deningerPrimeFinitePacketGaugeLimitBasepoint p) a
  left_inv x := by
    apply Subtype.ext
    funext s
    simp [deningerPrimeFinitePacketGaugeLimitMul,
      deningerPrimeFinitePacketGaugeLimitDiv]
  right_inv a := by
    apply Subtype.ext
    funext s
    simp [deningerPrimeFinitePacketGaugeLimitMul,
      deningerPrimeFinitePacketGaugeLimitDiv]

theorem deningerPrimeFinitePacketGaugeLimitEquiv_continuous
    (p : Nat.Primes) :
    Continuous (deningerPrimeFinitePacketGaugeLimitEquiv p) := by
  apply continuous_induced_rng.2
  change Continuous (fun x : DeningerPrimeFinitePacketLimit p =>
    fun s =>
      (deningerPrimeFinitePacketGaugeLimitBasepoint p).1 s * x.1 s)
  exact continuous_pi (fun s => by
    have hc : Continuous
        (fun _ : DeningerPrimeFinitePacketLimit p =>
          (deningerPrimeFinitePacketGaugeLimitBasepoint p).1 s) :=
      continuous_const
    exact hc.mul ((continuous_apply s).comp continuous_subtype_val))

theorem deningerPrimeFinitePacketGaugeLimitEquiv_symm_continuous
    (p : Nat.Primes) :
    Continuous (deningerPrimeFinitePacketGaugeLimitEquiv p).symm := by
  apply continuous_induced_rng.2
  change Continuous (fun a : DeningerPrimeFinitePacketGaugeLimit p =>
    fun s =>
      ((deningerPrimeFinitePacketGaugeLimitBasepoint p).1 s)⁻¹ * a.1 s)
  exact continuous_pi (fun s => by
    have hc : Continuous
        (fun _ : DeningerPrimeFinitePacketGaugeLimit p =>
          ((deningerPrimeFinitePacketGaugeLimitBasepoint p).1 s)⁻¹) :=
      continuous_const
    exact hc.mul ((continuous_apply s).comp continuous_subtype_val))

/-- Topological trivialization of the affine gauge torsor after choosing one coherent point. -/
noncomputable def deningerPrimeFinitePacketGaugeLimitHomeomorph
    (p : Nat.Primes) :
    DeningerPrimeFinitePacketLimit p ≃ₜ
      DeningerPrimeFinitePacketGaugeLimit p where
  toEquiv := deningerPrimeFinitePacketGaugeLimitEquiv p
  continuous_toFun :=
    deningerPrimeFinitePacketGaugeLimitEquiv_continuous p
  continuous_invFun :=
    deningerPrimeFinitePacketGaugeLimitEquiv_symm_continuous p

/-- **Global gauge classification.**  The affine rational-Witt gauge limit is a torsor
homeomorphic to the actual compact Deninger packet. -/
noncomputable def deningerPrimePacketGaugeLimitHomeomorph
    (p : Nat.Primes) :
    DeningerPacketFrobeniusQuotient p ≃ₜ
      DeningerPrimeFinitePacketGaugeLimit p :=
  (deningerPrimePacketFiniteLimitHomeomorph p).trans
    (deningerPrimeFinitePacketGaugeLimitHomeomorph p)

noncomputable instance deningerPrimeFinitePacketGaugeLimitCompactSpace
    (p : Nat.Primes) :
    CompactSpace (DeningerPrimeFinitePacketGaugeLimit p) :=
  (deningerPrimePacketGaugeLimitHomeomorph p).compactSpace

noncomputable instance deningerPrimeFinitePacketGaugeLimitMeasurableSpace
    (p : Nat.Primes) :
    MeasurableSpace (DeningerPrimeFinitePacketGaugeLimit p) :=
  borel (DeningerPrimeFinitePacketGaugeLimit p)

noncomputable instance deningerPrimeFinitePacketGaugeLimitBorelSpace
    (p : Nat.Primes) :
    BorelSpace (DeningerPrimeFinitePacketGaugeLimit p) :=
  ⟨rfl⟩

/-- Normalized Haar probability transported from the actual packet to its affine gauge
torsor. -/
noncomputable def deningerPrimeFinitePacketGaugeHaarMeasure
    (p : Nat.Primes) :
    Measure (DeningerPrimeFinitePacketGaugeLimit p) :=
  Measure.map (deningerPrimePacketGaugeLimitHomeomorph p)
    (deningerPrimePacketHaarMeasure p)

noncomputable instance deningerPrimeFinitePacketGaugeHaarMeasureProbability
    (p : Nat.Primes) :
    IsProbabilityMeasure
      (deningerPrimeFinitePacketGaugeHaarMeasure p) := by
  exact Measure.isProbabilityMeasure_map
    (deningerPrimePacketGaugeLimitHomeomorph p).continuous.measurable.aemeasurable

noncomputable instance deningerPrimeFinitePacketGaugeHaarMeasureIsOpenPos
    (p : Nat.Primes) :
    (deningerPrimeFinitePacketGaugeHaarMeasure p).IsOpenPosMeasure := by
  exact
    (deningerPrimePacketGaugeLimitHomeomorph p).continuous.isOpenPosMeasure_map
      (deningerPrimePacketGaugeLimitHomeomorph p).surjective

/-- Full real `L²` channel on the affine packet gauge limit. -/
abbrev DeningerPrimeFinitePacketGaugeHaarL2 (p : Nat.Primes) : Type :=
  Lp ℝ 2 (deningerPrimeFinitePacketGaugeHaarMeasure p)

def deningerPrimeFinitePacketGaugeContinuousToHaarL2
    (p : Nat.Primes) :
    C(DeningerPrimeFinitePacketGaugeLimit p, ℝ) →L[ℝ]
      DeningerPrimeFinitePacketGaugeHaarL2 p :=
  ContinuousMap.toLp 2 (deningerPrimeFinitePacketGaugeHaarMeasure p) ℝ

/-- Full-support transported Haar measure loses no continuous affine packet function. -/
theorem deningerPrimeFinitePacketGaugeContinuousToHaarL2_injective
    (p : Nat.Primes) :
    Function.Injective
      (deningerPrimeFinitePacketGaugeContinuousToHaarL2 p) := by
  exact ContinuousMap.toLp_injective
    (deningerPrimeFinitePacketGaugeHaarMeasure p)

end

end RHTower
