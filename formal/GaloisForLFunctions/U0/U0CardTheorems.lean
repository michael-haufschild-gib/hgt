/-
# u₀ ⟂ φ_b — the card theorems, conditional on the cover provider

This file states the three pipeline cards
* `u0-phi-independence.md` (connected `b ∈ M \ {0,-2}`),
* `u0-phi-independence-disconnected.md` (`b ∉ M`),
* `u0-phi-independence-all-parameters.md` (the union),
as the genuine independence `NoRelation ℂ(z) φ_b u₀` at the faithful carrier `meroField U`, where
`NoRelation` *is* the real "no nonzero polynomial relation" statement.

The remaining input is `PhibKummerInputs` — the Böttcher cover **Kummer-inputs provider for `φ_b`**
(per relation degree: the finite radical data with `Irreducible(X^{2ᵏ}−C a)`). It is *identical*
to the provider the parallel Böttcher agent is building for the q62 case (closed-loop FTC + period +
cover base field, in `Winding.lean` / `CoverConstruction.lean` / `FigureEight.lean` / `Q62Assembly.lean`)
— the **only** difference from q62 is the base element `GB` maps to `u₀` instead of `φ_{c₂}`. Everything
below is proved on top of that explicit hypothesis; when the shared provider lands, it should discharge
`PhibKummerInputs` and the three theorems become unconditional by specialization.
-/
import GaloisForLFunctions.U0.U0KummerRepick

open Polynomial Filter Topology Bottcher U0MeroCarrier U0KummerRepick

namespace U0CardTheorems

variable {U : Set ℂ}

/-- The shared Böttcher cover Kummer-inputs provider for `φ_b`.
Per relation degree `d`, a base field `B`, a `ℂ(z)`-algebra hom `i : B → meroField U`, a radicand `a`, a
base element `GB` with `i GB = u₀`, a primitive `2ᵏ`-th root `ζ` (`2ᵏ > d`), with `X^{2ᵏ}−C a` irreducible
and the radical relation `φ_b^{2ᵏ} = i a`. Its proof is the cover construction (`kummer_irreducible` ←
`not_square_of_period_ftc` ← the φ_b period + closed-loop FTC, over the cover base field `K = ℂ(p₀)`),
shared verbatim with `Bottcher.q62_disconnected_kummer` except `GB = u₀`. -/
def PhibKummerInputs (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b) : Prop :=
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ d : ℕ, ∃ (B : Type) (_ : Field B) (_ : Algebra (RatFunc ℂ) B)
        (i : B →ₐ[RatFunc ℂ] meroField U) (a GB ζ : B) (k : ℕ),
        d < 2 ^ k ∧ IsPrimitiveRoot ζ (2 ^ k) ∧ Irreducible ((X : Polynomial B) ^ (2 ^ k) - C a) ∧
        phiMero b hU_esc ^ (2 ^ k) = i a ∧
        i GB = algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)

/-- **u₀ ⟂ φ_b at the faithful carrier (the content of all three cards).** `NoRelation ℂ(z) φ_b u₀` in
`meroField U` — i.e. no nonzero polynomial relation between the inverse Böttcher coordinate `φ_b` and the
c-velocity `u₀` over `ℂ(z)`. Proof: the Kummer-inputs closure `u0_phi_independence_inputs` fed the cover
provider `phib_kummer_inputs`; the two u₀-specific inputs (`φ_b ≠ 0`, `u₀` transcendental) are discharged
inside the closure. The connected / disconnected / all-parameter cards are this theorem at the carriers
realizing the respective `b`-ranges. -/
theorem u0_phi_independence_carrier (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (hKummer : PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) :=
  u0_phi_independence_inputs hUo hUc hUne hUinf hU_ext hU_esc
    hKummer

/-- **Card `u0-phi-independence.md` (connected `b ∈ M \ {0,-2}`).** The carrier realizes a deep ball in
the exterior where `φ_b` is the single-valued connected-locus Böttcher coordinate. -/
theorem u0_phi_independence_connected (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (hKummer : PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) :=
  u0_phi_independence_carrier hUo hUc hUne hUinf hU_ext hU_esc hKummer

/-- **Card `u0-phi-independence-disconnected.md` (`b ∉ M`).** The carrier realizes a deep ball in the
escape set where `φ_b` carries its own dyadic monodromy. -/
theorem u0_phi_independence_disconnected (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (hKummer : PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) :=
  u0_phi_independence_carrier hUo hUc hUne hUinf hU_ext hU_esc hKummer

/-- **Card `u0-phi-independence-all-parameters.md` (all nonexceptional `b`).** Both Mandelbrot regions in
one statement — the same carrier independence, uniform in the parameter. -/
theorem u0_phi_independence_all_parameters (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (hKummer : PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) :=
  u0_phi_independence_carrier hUo hUc hUne hUinf hU_ext hU_esc hKummer

end U0CardTheorems

namespace U0CardTheorems

/-- Weaker U0 Kummer provider: per relation degree, supply only a non-square radicand whose `2^k`-th
root is `φ_b`, plus the base element mapping to `u₀`. The primitive root and irreducibility clauses of
`PhibKummerInputs` are then built by the Kummer algebra. -/
def PhibRadicalData (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b) : Prop :=
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ d : ℕ, ∃ (B : Type) (_ : Field B) (_ : Algebra (RatFunc ℂ) B)
        (i : B →ₐ[RatFunc ℂ] meroField U) (a GB : B) (k : ℕ),
        1 ≤ k ∧ d < 2 ^ k ∧ (∀ x : B, x ^ 2 ≠ a) ∧
        phiMero b hU_esc ^ (2 ^ k) = i a ∧
        i GB = algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)

/-- The weaker radical provider builds the original Kummer-input provider. This is the explicit
interface reduction: primitive dyadic roots and irreducibility of `X^(2^k)-C a` follow from the
per-depth non-square radicand. -/
theorem phibKummerInputs_of_radicalData (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (hRadical : PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc) :
    PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro d
  obtain ⟨B, hBfield, hBalg, i, a, GB, k, hk1, hdk, hns, hroot, hiGB⟩ := hRadical d
  have hneg : ∃ j : B, j ^ 2 = -1 := by
    refine ⟨algebraMap (RatFunc ℂ) B (algebraMap ℂ (RatFunc ℂ) Complex.I), ?_⟩
    rw [← map_pow, ← map_pow]
    rw [show Complex.I ^ 2 = (-1 : ℂ) from Complex.I_sq, map_neg, map_one, map_neg, map_one]
  have hirr : Irreducible ((X : Polynomial B) ^ (2 ^ k) - C a) :=
    kummer_irreducible hneg a hns k hk1
  obtain ⟨ζ₀, hζ₀ord, _hζ₀pow⟩ := exists_dyadic_primitive k
  have hζ₀prim : IsPrimitiveRoot ζ₀ (2 ^ k) := by
    have h := IsPrimitiveRoot.orderOf ζ₀
    rwa [hζ₀ord] at h
  let j : ℂ →+* B := (algebraMap (RatFunc ℂ) B).comp (algebraMap ℂ (RatFunc ℂ))
  have hinj : Function.Injective j :=
    (algebraMap (RatFunc ℂ) B).injective.comp (algebraMap ℂ (RatFunc ℂ)).injective
  exact ⟨B, hBfield, hBalg, i, a, GB, j ζ₀, k, hdk, hζ₀prim.map_of_injective hinj,
    hirr, hroot, hiGB⟩

/-- **u₀ ⟂ φ_b from the weaker radical-data provider.** This packages
`U0KummerRepick.u0_phi_independence_of_radical_data` at the card carrier. -/
theorem u0_phi_independence_carrier_radical_data (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (hRadical : PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) :=
  u0_phi_independence_carrier hUo hUc hUne hUinf hU_ext hU_esc
    (phibKummerInputs_of_radicalData hUo hUc hUne hUinf hU_ext hU_esc hRadical)

/-- **Card `u0-phi-independence.md` from radical data.** The connected card only needs the weaker
per-depth non-square provider; the Kummer tuple is built internally. -/
theorem u0_phi_independence_connected_radical_data (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (hRadical : PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) :=
  u0_phi_independence_carrier_radical_data hUo hUc hUne hUinf hU_ext hU_esc hRadical

/-- **Card `u0-phi-independence-disconnected.md` from radical data.** The disconnected card uses the
same non-square provider interface as the connected carrier. -/
theorem u0_phi_independence_disconnected_radical_data (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (hRadical : PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) :=
  u0_phi_independence_carrier_radical_data hUo hUc hUne hUinf hU_ext hU_esc hRadical

/-- **Card `u0-phi-independence-all-parameters.md` from radical data.** The all-parameter wrapper
exposes the same weaker missing input uniformly in `b`. -/
theorem u0_phi_independence_all_parameters_radical_data (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (hRadical : PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) :=
  u0_phi_independence_carrier_radical_data hUo hUc hUne hUinf hU_ext hU_esc hRadical

end U0CardTheorems

namespace U0CardTheorems

/-- Deck-scaling provider for the U0 Kummer radicand. Per relation degree, it supplies the same base
radicand data as `PhibRadicalData`, plus a finite extension carrying a square root of that radicand
which a deck automorphism scales by a multiplier of order greater than one while fixing the base. The
non-square clause of `PhibRadicalData` is then pure algebra. -/
def PhibSquareRootDeckData (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b) : Prop :=
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ d : ℕ, ∃ (B : Type) (_ : Field B) (_ : Algebra (RatFunc ℂ) B)
        (i : B →ₐ[RatFunc ℂ] meroField U) (a GB : B) (k : ℕ)
        (M : Type) (_ : Field M) (_ : Algebra B M) (σ : M ≃+* M) (F ζ : M),
        1 ≤ k ∧ d < 2 ^ k ∧
        F ^ 2 = algebraMap B M a ∧
        (∀ x : B, σ (algebraMap B M x) = algebraMap B M x) ∧
        σ F = ζ * F ∧ F ≠ 0 ∧ 1 < orderOf ζ ∧
        phiMero b hU_esc ^ (2 ^ k) = i a ∧
        i GB = algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)

/-- A finite square-root deck over the base radicand supplies `PhibRadicalData`. This is the bridge
from geometric deck scaling to the non-square provider consumed by the U0 Kummer close. -/
theorem phibRadicalData_of_squareRootDeckData (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (hDeck : PhibSquareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc) :
    PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro d
  obtain ⟨B, hBfield, hBalg, i, a, GB, k, M, hMfield, hBMalg, σ, F, ζ,
    hk1, hdk, hroot, hbase, hσF, hF, hζord, hphi, hiGB⟩ := hDeck d
  letI : Field B := hBfield
  letI : Algebra (RatFunc ℂ) B := hBalg
  letI : Field M := hMfield
  letI : Algebra B M := hBMalg
  refine ⟨B, hBfield, hBalg, i, a, GB, k, hk1, hdk, ?_, hphi, hiGB⟩
  exact Bottcher.not_square_of_scaled_root_fixed_base_of_order σ hbase hroot hσF hF hζord

/-- U0 carrier independence from finite square-root deck data over the Kummer radicand. -/
theorem u0_phi_independence_carrier_squareRootDeckData (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (hDeck : PhibSquareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) :=
  u0_phi_independence_carrier_radical_data hUo hUc hUne hUinf hU_ext hU_esc
    (phibRadicalData_of_squareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc hDeck)

end U0CardTheorems
