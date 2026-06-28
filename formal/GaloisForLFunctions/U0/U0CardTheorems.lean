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
import GaloisForLFunctions.Bottcher.BottcherIterateNonSquare

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

namespace U0CardTheorems

variable {U : Set ℂ}

/-- Radical data supplies the finite square-root deck provider by adjoining a square root of the
same radicand and using the Kummer deck automorphism at depth one. -/
theorem phibSquareRootDeckData_of_radicalData (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (hRadical : PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc) :
    PhibSquareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro d
  obtain ⟨B, hBfield, hBalg, i, a, GB, k, hk1, hdk, hns, hphi, hiGB⟩ := hRadical d
  letI : Field B := hBfield
  letI : Algebra (RatFunc ℂ) B := hBalg
  have hneg : ∃ j : B, j ^ 2 = -1 := by
    refine ⟨algebraMap (RatFunc ℂ) B (algebraMap ℂ (RatFunc ℂ) Complex.I), ?_⟩
    rw [← map_pow, ← map_pow]
    rw [show Complex.I ^ 2 = (-1 : ℂ) from Complex.I_sq, map_neg, map_one, map_neg, map_one]
  have hirr : Irreducible ((X : Polynomial B) ^ (2 ^ (1 : ℕ)) - C a) :=
    Bottcher.kummer_irreducible hneg a hns 1 (by norm_num)
  haveI : Fact (Irreducible ((X : Polynomial B) ^ (2 ^ (1 : ℕ)) - C a)) := ⟨hirr⟩
  obtain ⟨ζ₀, hζ₀ord, _hζ₀pow⟩ := Bottcher.exists_dyadic_primitive 1
  have hζ₀prim : IsPrimitiveRoot ζ₀ (2 ^ (1 : ℕ)) := by
    have h := IsPrimitiveRoot.orderOf ζ₀
    rwa [hζ₀ord] at h
  let j : ℂ →+* B := (algebraMap (RatFunc ℂ) B).comp (algebraMap ℂ (RatFunc ℂ))
  have hinj : Function.Injective j :=
    (algebraMap (RatFunc ℂ) B).injective.comp (algebraMap ℂ (RatFunc ℂ)).injective
  let ζB : B := j ζ₀
  have hζB : IsPrimitiveRoot ζB (2 ^ (1 : ℕ)) := hζ₀prim.map_of_injective hinj
  let M : Type := AdjoinRoot ((X : Polynomial B) ^ (2 ^ (1 : ℕ)) - C a)
  letI : Field M := inferInstance
  letI : Algebra B M := inferInstance
  let σAlg : M ≃ₐ[RatFunc ℂ] M :=
    (autAdjoinRootXPowSubC (2 ^ (1 : ℕ)) a hζB.toRootsOfUnity).restrictScalars
      (RatFunc ℂ)
  let F : M := AdjoinRoot.root ((X : Polynomial B) ^ (2 ^ (1 : ℕ)) - C a)
  let ζ : M := algebraMap B M ζB
  have hrootPow : F ^ (2 ^ (1 : ℕ)) = algebraMap B M a := by
    have he := AdjoinRoot.eval₂_root ((X : Polynomial B) ^ (2 ^ (1 : ℕ)) - C a)
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at he
    exact he
  have hFroot : F ^ 2 = algebraMap B M a := by
    simpa using hrootPow
  have hbase : ∀ x : B, (σAlg.toRingEquiv) (algebraMap B M x) = algebraMap B M x := by
    intro x
    change σAlg (algebraMap B M x) = algebraMap B M x
    rw [AlgEquiv.restrictScalars_apply]
    exact AlgEquiv.commutes _ x
  have hσF : (σAlg.toRingEquiv) F = ζ * F := by
    change σAlg F = ζ * F
    simp only [σAlg, F, ζ]
    rw [AlgEquiv.restrictScalars_apply, autAdjoinRootXPowSubC_root,
      hζB.val_toRootsOfUnity_coe, Algebra.smul_def]
  have hσζ : (σAlg.toRingEquiv) ζ = ζ := by
    change σAlg ζ = ζ
    simp only [σAlg, ζ]
    rw [AlgEquiv.restrictScalars_apply]
    exact AlgEquiv.commutes _ ζB
  have hF : F ≠ 0 := by
    intro h0
    have ha0 : a = 0 := by
      apply (algebraMap B M).injective
      rw [← hFroot, h0]
      norm_num
    exact hns 0 (by rw [ha0]; norm_num)
  have hζord : 1 < orderOf ζ := by
    have hprimM : IsPrimitiveRoot ζ (2 ^ (1 : ℕ)) :=
      hζB.map_of_injective (algebraMap B M).injective
    have hord : orderOf ζ = 2 ^ (1 : ℕ) := hprimM.eq_orderOf.symm
    rw [hord]
    norm_num
  exact ⟨B, hBfield, hBalg, i, a, GB, k, M, inferInstance, inferInstance, σAlg.toRingEquiv,
    F, ζ, hk1, hdk, hFroot, hbase, hσF, hF, hζord, hphi, hiGB⟩

end U0CardTheorems

namespace U0CardTheorems

variable {U : Set ℂ}

/-- The radical-data and square-root-deck provider interfaces for the U0 Kummer radicand are equivalent. -/
theorem phibRadicalData_iff_squareRootDeckData (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b) :
    PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc ↔
      PhibSquareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc := by
  constructor
  · exact phibSquareRootDeckData_of_radicalData hUo hUc hUne hUinf hU_ext hU_esc
  · exact phibRadicalData_of_squareRootDeckData hUo hUc hUne hUinf hU_ext hU_esc

end U0CardTheorems

namespace U0CardTheorems

variable {U : Set ℂ}

/-- The original Kummer-input provider already contains radical data: irreducibility of
`X^(2^k)-C a`, after re-picking at depth `d+1`, forces the radicand `a` to be non-square. -/
theorem phibRadicalData_of_kummerInputs (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (hKummer : PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc) :
    PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro d
  obtain ⟨B, hBfield, hBalg, i, a, GB, _ζ, k, hdk1, _hζ, hirr, hroot, hiGB⟩ :=
    hKummer (d + 1)
  letI : Field B := hBfield
  letI : Algebra (RatFunc ℂ) B := hBalg
  have hk1 : 1 ≤ k := by
    by_contra hknot
    have hk0 : k = 0 := by omega
    rw [hk0] at hdk1
    norm_num at hdk1
  have hdk : d < 2 ^ k := by omega
  exact ⟨B, hBfield, hBalg, i, a, GB, k, hk1, hdk,
    Bottcher.not_square_of_irreducible_X_pow_two_pow_sub_C hk1 hirr, hroot, hiGB⟩

/-- The full Kummer-input and radical-data provider interfaces for `φ_b` carry the same Lean content. -/
theorem phibKummerInputs_iff_radicalData (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b) :
    PhibKummerInputs hUo hUc hUne hUinf hU_ext hU_esc ↔
      PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc := by
  constructor
  · exact phibRadicalData_of_kummerInputs hUo hUc hUne hUinf hU_ext hU_esc
  · exact phibKummerInputs_of_radicalData hUo hUc hUne hUinf hU_ext hU_esc

end U0CardTheorems

namespace U0CardTheorems

variable {K B E : Type*} [Field K] [Field B] [Field E] [Algebra K B] [Algebra K E]

/-- A radical relation with a non-square radicand cannot have a surjective base map once the root is
already present in the target field. This is the formal obstruction to the naive U0 provider over the
same meromorphic carrier that contains `φ_b`: the Kummer base must be a proper descent/cover base, not a
surjective copy of the carrier. -/
theorem radical_image_not_surjective_of_nonSquare
    (i : B →ₐ[K] E) {F : E} {a : B} {k : ℕ}
    (hk1 : 1 ≤ k) (hns : ∀ x : B, x ^ 2 ≠ a) (hroot : F ^ (2 ^ k) = i a) :
    ¬ Function.Surjective i := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (F ^ (2 ^ (k - 1)))
  have hx2 : i (x ^ 2) = i a := by
    calc
      i (x ^ 2) = (i x) ^ 2 := by simp
      _ = (F ^ (2 ^ (k - 1))) ^ 2 := by rw [hx]
      _ = F ^ (2 ^ (k - 1) * 2) := by rw [pow_mul]
      _ = F ^ (2 ^ k) := by
          congr 1
          calc
            2 ^ (k - 1) * 2 = 2 ^ ((k - 1) + 1) := by rw [pow_succ]
            _ = 2 ^ k := by rw [Nat.sub_add_cancel hk1]
      _ = i a := hroot
  have hxa : x ^ 2 = a := i.injective hx2
  exact hns x hxa

variable {U : Set ℂ}

/-- Every per-depth map occurring in valid U0 radical data is necessarily non-surjective. This records
where the real provider has to live: the base field must omit the displayed `2^k`-th root and map into
the carrier as a proper descent, otherwise the radicand is visibly a square. -/
theorem phibRadicalData_nonSurjective_maps (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (hRadical : PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ d : ℕ, ∃ (B : Type) (_ : Field B) (_ : Algebra (RatFunc ℂ) B)
        (i : B →ₐ[RatFunc ℂ] meroField U) (a GB : B) (k : ℕ),
        1 ≤ k ∧ d < 2 ^ k ∧ (∀ x : B, x ^ 2 ≠ a) ∧
        phiMero b hU_esc ^ (2 ^ k) = i a ∧
        i GB = algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext) ∧
        ¬ Function.Surjective i := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro d
  obtain ⟨B, hBfield, hBalg, i, a, GB, k, hk1, hdk, hns, hroot, hiGB⟩ := hRadical d
  letI : Field B := hBfield
  letI : Algebra (RatFunc ℂ) B := hBalg
  exact ⟨B, hBfield, hBalg, i, a, GB, k, hk1, hdk, hns, hroot, hiGB,
    radical_image_not_surjective_of_nonSquare i hk1 hns hroot⟩

end U0CardTheorems

namespace U0CardTheorems

variable {U V : Set ℂ}

/-- Restricting the analytic `u₀` germ along `V ⊆ U ⊆ U0NaturalBoundary.Ext` gives the analytic `u₀`
germ on `V`. This is the U0-specific base-element compatibility needed by the deep radical provider. -/
theorem restrictAnalytic_u0AnSub (hVU : V ⊆ U) (hU_ext : U ⊆ U0NaturalBoundary.Ext) :
    restrictAnalytic hVU (u0AnSub hU_ext) =
      u0AnSub (U := V) (fun _ hz => hU_ext (hVU hz)) := by
  apply Subtype.ext
  show ((U0.u0 : Germ (𝓟 U) ℂ).compTendsto id
      (tendsto_principal_principal.mpr (fun _ hx => hVU hx))) =
    (U0.u0 : Germ (𝓟 V) ℂ)
  rw [Germ.coe_compTendsto]
  rfl

variable {U : Set ℂ}

/-- Topological deep data for the U0 radical provider.  Instead of asking for the radicand
`∮ d log(bottcherCoord∘f^[k])` period directly, this asks for a closed loop whose `f^[k]` image has
odd logarithmic winding.  The Böttcher chain-rule theorem turns this into the analytic odd-period
data consumed by `phibRadicalData_of_deepData`. -/
def PhibImageWindingDeepData (U : Set ℂ) (b : ℂ) : Prop :=
  ∀ d : ℕ, ∃ (Ext : Set ℂ)
    (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
    (_hUExt : U ⊆ Ext)
    (_hExtesc : ∀ z ∈ Ext, (quadratic b)^[d+1] z ∈ escapeOpen b)
    (_hExtU0 : Ext ⊆ U0NaturalBoundary.Ext)
    (aExt : analyticSubring Ext),
    (aExt : Germ (𝓟 Ext) ℂ)
        = (↑(fun z => bottcherCoord b ((quadratic b)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
    (∀ T : Set ℂ, T.Countable →
      ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
        (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
        (∀ θ : ℝ, HasDerivAt γ (γ' θ) θ) ∧
        γ (2 * Real.pi) = γ 0 ∧
        (∀ θ : ℝ, (quadratic b)^[d+1] (γ θ) ∉ T) ∧
        (∫ θ in (0:ℝ)..(2 * Real.pi),
            ((quadratic b)^[d+1] (γ θ))⁻¹ *
              ((∏ j ∈ Finset.range (d+1), 2 * (quadratic b)^[j] (γ θ)) * γ' θ))
          = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))

/-- U0 radical-data provider from the same deep odd-period loop data used in the hDisc Kummer route.
Per relation degree, a connected deeper domain `Ext` containing `U`, landing in the Böttcher escape set
under `f_b^[d+1]`, contained in the U0 natural-boundary exterior, and carrying the closed odd-period
loop for the iterate radicand supplies `PhibRadicalData`. The new U0 ingredient is only that `u₀`
restricts from `Ext` to `U`; non-squareness and the radical relation are the existing Böttcher deep-loop
bricks. -/
theorem phibRadicalData_of_deepData (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (deepdata :
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (_hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic b)^[d+1] z ∈ escapeOpen b)
        (_hExtU0 : Ext ⊆ U0NaturalBoundary.Ext)
        (aExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord b ((quadratic b)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic b)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                logDeriv (fun z => bottcherCoord b ((quadratic b)^[d+1] z)) (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI algU := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtU0, aExt, haExt, hloops⟩ :=
    deepdata d
  haveI := isDomain_analyticSubring Ext hExto hExtc.isPreconnected hExtc.nonempty
  letI algExt := (ratfuncToMero Ext hExto hExtc.isPreconnected hExtc.nonempty hExtinf).toAlgebra
  let i : meroField Ext →ₐ[RatFunc ℂ] meroField U :=
    { restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne with
      commutes' := fun r => RingHom.congr_fun
        (restrictMeroHom_ratfuncToMero hUExt hExto hExtc.isPreconnected hExtc.nonempty hExtinf
          hUo hUc hUne hUinf) r }
  refine ⟨meroField Ext, inferInstance, inferInstance, i,
    algebraMap (analyticSubring Ext) (meroField Ext) aExt,
    algebraMap (analyticSubring Ext) (meroField Ext) (u0AnSub hExtU0), d + 1,
    Nat.le_add_left 1 d, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ d))
  · exact bottcherIterateGerm_not_isSquare (d+1) hExto hExtc hExtesc hloops aExt haExt.symm
  · show phiMero b hU_esc ^ (2 ^ (d+1))
        = restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne
            (algebraMap (analyticSubring Ext) (meroField Ext) aExt)
    have hUesc_regime : ∀ z ∈ U, ‖b‖ ≤ ‖z‖ ∧ 2 < ‖z‖ := by
      intro z hz
      exact mem_escapeOpen_regime (hU_esc hz)
    exact radical_relation_germ (d+1) hUExt hUo hUc hUne hExto hExtc.isPreconnected hExtc.nonempty
      hUesc_regime (phiAnalytic b hU_esc) aExt rfl haExt
  · show restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne
        (algebraMap (analyticSubring Ext) (meroField Ext) (u0AnSub hExtU0))
      = algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)
    rw [restrictMeroHom_algebraMap, restrictAnalytic_u0AnSub]

end U0CardTheorems

namespace U0CardTheorems

variable {U : Set ℂ}

/-- U0 radical-data provider from topological image-winding deep data.  This discharges the analytic
radicand-period premise in `phibRadicalData_of_deepData` using
`pathInt_logDeriv_bottcherIterate_eq_imageInv`. -/
theorem phibRadicalData_of_imageWindingDeepData (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (deepdata : PhibImageWindingDeepData U b) :
    PhibRadicalData hUo hUc hUne hUinf hU_ext hU_esc := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI algU := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, hExtesc, hExtU0, aExt, haExt, hloops⟩ :=
    deepdata d
  haveI := isDomain_analyticSubring Ext hExto hExtc.isPreconnected hExtc.nonempty
  letI algExt := (ratfuncToMero Ext hExto hExtc.isPreconnected hExtc.nonempty hExtinf).toAlgebra
  let i : meroField Ext →ₐ[RatFunc ℂ] meroField U :=
    { restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne with
      commutes' := fun r => RingHom.congr_fun
        (restrictMeroHom_ratfuncToMero hUExt hExto hExtc.isPreconnected hExtc.nonempty hExtinf
          hUo hUc hUne hUinf) r }
  refine ⟨meroField Ext, inferInstance, inferInstance, i,
    algebraMap (analyticSubring Ext) (meroField Ext) aExt,
    algebraMap (analyticSubring Ext) (meroField Ext) (u0AnSub hExtU0), d + 1,
    Nat.le_add_left 1 d, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ d))
  · exact bottcherIterateGerm_not_isSquare_of_imageWinding (d+1) hExto hExtc hExtesc
      hloops aExt haExt.symm
  · show phiMero b hU_esc ^ (2 ^ (d+1))
        = restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne
            (algebraMap (analyticSubring Ext) (meroField Ext) aExt)
    have hUesc_regime : ∀ z ∈ U, ‖b‖ ≤ ‖z‖ ∧ 2 < ‖z‖ := by
      intro z hz
      exact mem_escapeOpen_regime (hU_esc hz)
    exact radical_relation_germ (d+1) hUExt hUo hUc hUne hExto hExtc.isPreconnected hExtc.nonempty
      hUesc_regime (phiAnalytic b hU_esc) aExt rfl haExt
  · show restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne
        (algebraMap (analyticSubring Ext) (meroField Ext) (u0AnSub hExtU0))
      = algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)
    rw [restrictMeroHom_algebraMap, restrictAnalytic_u0AnSub]

/-- U0 carrier independence directly from the deep odd-period data. This composes the new deep-data
provider with the existing radical-data Kummer close, so the remaining U0 card input is exactly the
geometric per-depth deep domain/loop construction. -/
theorem u0_phi_independence_carrier_deepData (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (deepdata :
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (_hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic b)^[d+1] z ∈ escapeOpen b)
        (_hExtU0 : Ext ⊆ U0NaturalBoundary.Ext)
        (aExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord b ((quadratic b)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic b)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                logDeriv (fun z => bottcherCoord b ((quadratic b)^[d+1] z)) (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) :=
  u0_phi_independence_carrier_radical_data hUo hUc hUne hUinf hU_ext hU_esc
    (phibRadicalData_of_deepData hUo hUc hUne hUinf hU_ext hU_esc deepdata)

/-- U0 carrier independence directly from topological image-winding deep data. -/
theorem u0_phi_independence_carrier_imageWindingDeepData (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hU_ext : U ⊆ U0NaturalBoundary.Ext) {b : ℂ} (hU_esc : U ⊆ escapeOpen b)
    (deepdata : PhibImageWindingDeepData U b) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hU_ext)) :=
  u0_phi_independence_carrier_radical_data hUo hUc hUne hUinf hU_ext hU_esc
    (phibRadicalData_of_imageWindingDeepData hUo hUc hUne hUinf hU_ext hU_esc deepdata)

end U0CardTheorems

namespace U0CardTheorems

/-- The Böttcher escape region lies in the exterior domain of the U0 natural-boundary theorem. -/
theorem escapeOpen_subset_U0Ext (b : ℂ) : escapeOpen b ⊆ U0NaturalBoundary.Ext := by
  intro z hz
  exact lt_trans (by norm_num : (1 : ℝ) < 2) (mem_escapeOpen_regime hz).2

variable {U : Set ℂ}

/-- U0 carrier independence from deep data on an escape carrier. The separate containment
`U ⊆ U0NaturalBoundary.Ext` is derived automatically from `U ⊆ escapeOpen b`. -/
theorem u0_phi_independence_escapeCarrier_deepData (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (deepdata :
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (_hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic b)^[d+1] z ∈ escapeOpen b)
        (_hExtU0 : Ext ⊆ U0NaturalBoundary.Ext)
        (aExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord b ((quadratic b)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic b)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                logDeriv (fun z => bottcherCoord b ((quadratic b)^[d+1] z)) (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U)
        (u0AnSub (hU_esc.trans (escapeOpen_subset_U0Ext b)))) := by
  exact u0_phi_independence_carrier_deepData hUo hUc hUne hUinf
    (hU_esc.trans (escapeOpen_subset_U0Ext b)) hU_esc deepdata

/-- U0 carrier independence on an escape carrier from topological image-winding deep data. -/
theorem u0_phi_independence_escapeCarrier_imageWindingDeepData (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b) (deepdata : PhibImageWindingDeepData U b) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U)
        (u0AnSub (hU_esc.trans (escapeOpen_subset_U0Ext b)))) := by
  exact u0_phi_independence_carrier_imageWindingDeepData hUo hUc hUne hUinf
    (hU_esc.trans (escapeOpen_subset_U0Ext b)) hU_esc deepdata

end U0CardTheorems

namespace U0CardTheorems

variable {U : Set ℂ}

/-- Connected-card U0 independence on an escape carrier from deep odd-period data. -/
theorem u0_phi_independence_connected_escapeCarrier_deepData (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (deepdata :
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (_hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic b)^[d+1] z ∈ escapeOpen b)
        (_hExtU0 : Ext ⊆ U0NaturalBoundary.Ext)
        (aExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord b ((quadratic b)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic b)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                logDeriv (fun z => bottcherCoord b ((quadratic b)^[d+1] z)) (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U)
        (u0AnSub (hU_esc.trans (escapeOpen_subset_U0Ext b)))) :=
  u0_phi_independence_escapeCarrier_deepData hUo hUc hUne hUinf hU_esc deepdata

/-- Connected-card U0 independence on an escape carrier from topological image-winding deep data. -/
theorem u0_phi_independence_connected_escapeCarrier_imageWindingDeepData (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b) (deepdata : PhibImageWindingDeepData U b) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U)
        (u0AnSub (hU_esc.trans (escapeOpen_subset_U0Ext b)))) :=
  u0_phi_independence_escapeCarrier_imageWindingDeepData hUo hUc hUne hUinf hU_esc deepdata

/-- Disconnected-card U0 independence on an escape carrier from deep odd-period data. -/
theorem u0_phi_independence_disconnected_escapeCarrier_deepData (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (deepdata :
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (_hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic b)^[d+1] z ∈ escapeOpen b)
        (_hExtU0 : Ext ⊆ U0NaturalBoundary.Ext)
        (aExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord b ((quadratic b)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic b)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                logDeriv (fun z => bottcherCoord b ((quadratic b)^[d+1] z)) (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U)
        (u0AnSub (hU_esc.trans (escapeOpen_subset_U0Ext b)))) :=
  u0_phi_independence_escapeCarrier_deepData hUo hUc hUne hUinf hU_esc deepdata

/-- Disconnected-card U0 independence on an escape carrier from topological image-winding deep data. -/
theorem u0_phi_independence_disconnected_escapeCarrier_imageWindingDeepData (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b) (deepdata : PhibImageWindingDeepData U b) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U)
        (u0AnSub (hU_esc.trans (escapeOpen_subset_U0Ext b)))) :=
  u0_phi_independence_escapeCarrier_imageWindingDeepData hUo hUc hUne hUinf hU_esc deepdata

/-- All-parameter U0 independence on an escape carrier from deep odd-period data. -/
theorem u0_phi_independence_all_parameters_escapeCarrier_deepData (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b)
    (deepdata :
      ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (_hUExt : U ⊆ Ext)
        (_hExtesc : ∀ z ∈ Ext, (quadratic b)^[d+1] z ∈ escapeOpen b)
        (_hExtU0 : Ext ⊆ U0NaturalBoundary.Ext)
        (aExt : analyticSubring Ext),
        (aExt : Germ (𝓟 Ext) ℂ)
            = (↑(fun z => bottcherCoord b ((quadratic b)^[d+1] z)) : Germ (𝓟 Ext) ℂ) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, (quadratic b)^[d+1] (γ θ) ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi),
                logDeriv (fun z => bottcherCoord b ((quadratic b)^[d+1] z)) (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U)
        (u0AnSub (hU_esc.trans (escapeOpen_subset_U0Ext b)))) :=
  u0_phi_independence_escapeCarrier_deepData hUo hUc hUne hUinf hU_esc deepdata

/-- All-parameter U0 independence on an escape carrier from topological image-winding deep data. -/
theorem u0_phi_independence_all_parameters_escapeCarrier_imageWindingDeepData (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite) {b : ℂ}
    (hU_esc : U ⊆ escapeOpen b) (deepdata : PhibImageWindingDeepData U b) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero b hU_esc)
      (algebraMap (analyticSubring U) (meroField U)
        (u0AnSub (hU_esc.trans (escapeOpen_subset_U0Ext b)))) :=
  u0_phi_independence_escapeCarrier_imageWindingDeepData hUo hUc hUne hUinf hU_esc deepdata

end U0CardTheorems
