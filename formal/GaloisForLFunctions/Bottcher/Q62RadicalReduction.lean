/-
# q62 disconnected/disconnected — reduction to per-depth NON-SQUARE radical data

This file sharpens `q62_disconnected_kummer` (`Q62KummerAssembly.lean`): rather than supplying the full
`Irreducible (X^{2^k} − C a)` per depth, one supplies only that the radicand `a = φ_{c₁}∘f^[k]` is **not
a square** in the base field `B` — the minimal geometric monodromy datum. All the surrounding algebra
(Capelli `p=2` irreducibility `kummer_irreducible`, the primitive `2^k`-th root lifted from `ℂ ⊆ B`, the
`−1 = i²` side condition) is discharged here, collapsing the disconnected/disconnected case to a single
clean geometric input: the period of `φ_{c₁}` around a `c₁`-cylinder loop that fixes `φ_{c₂}`.
-/
import GaloisForLFunctions.Bottcher.Q62KummerAssembly
import GaloisForLFunctions.Bottcher.BasinBranching

open Polynomial

namespace Bottcher

/-- **q62 disconnected/disconnected from per-depth NON-SQUARE radical data.** For the genuine Böttcher
coordinates `a₁ = φ_{c₁}`, `a₂ = φ_{c₂}` as germs in `meroField U`, algebraic independence over
`ℂ(z) = RatFunc ℂ` follows from: `φ_{c₁} ≠ 0`, `φ_{c₂}` transcendental, and — per depth `d` — a base
field `B ∋ φ_{c₂}` with the radicand `a = φ_{c₁}^{2^k}` (`k ≥ 1`, `d < 2^k`) **not a square** in `B`.
The irreducibility of `X^{2^k} − C a` (hence the Kummer tower) is built here from non-squareness via
`kummer_irreducible`; the primitive root is lifted from `ℂ` through `ℂ → ℂ(z) → B`. This is the minimal
algebraic surface of the disconnected case: the lone remaining input is the *geometric* non-squareness
`∀ b ∈ B, b² ≠ φ_{c₁}^{2^k}` — equivalently the dyadic period of `φ_{c₁}` around a cylinder loop
null-homotopic in the `c₂`-basin (so `φ_{c₂} ∈ B` is deck-fixed). -/
theorem q62_disconnected_of_radical_data {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) [Algebra (RatFunc ℂ) (meroField U)]
    (a₁ a₂ : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          (algebraMap (analyticSubring U) (meroField U) a₁) ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (data : haveI := isDomain_analyticSubring U hUo hUc hUne
      ∀ d : ℕ, ∃ (B : Type) (_ : Field B) (_ : Algebra (RatFunc ℂ) B)
      (i : B →ₐ[RatFunc ℂ] meroField U) (a GB : B) (k : ℕ),
      1 ≤ k ∧ d < 2 ^ k ∧ (∀ b : B, b ^ 2 ≠ a) ∧
      (algebraMap (analyticSubring U) (meroField U) a₁) ^ (2 ^ k) = i a ∧
      i GB = (algebraMap (analyticSubring U) (meroField U) a₂)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  apply q62_disconnected_kummer hUo hUc hUne a₁ a₂ hF hGtr
  intro d
  obtain ⟨B, hBfield, hBalg, i, a, GB, k, hk1, hdk, hns, hroot, hiGB⟩ := data d
  -- `−1` is a square in `B` (it contains `ℂ ⊇ {I}` via `ℂ → ℂ(z) → B`)
  have hneg : ∃ j : B, j ^ 2 = -1 := by
    refine ⟨algebraMap (RatFunc ℂ) B (algebraMap ℂ (RatFunc ℂ) Complex.I), ?_⟩
    rw [← map_pow, ← map_pow]
    rw [show Complex.I ^ 2 = (-1 : ℂ) from Complex.I_sq, map_neg, map_one, map_neg, map_one]
  -- irreducibility from non-squareness (Capelli p=2)
  have hirr : Irreducible (X ^ (2 ^ k) - C a) := kummer_irreducible hneg a hns k hk1
  -- primitive `2^k`-th root of unity in `B`, lifted from `ℂ` through `ℂ → ℂ(z) → B`
  obtain ⟨ζ₀, hζ₀ord, hζ₀pow⟩ := exists_dyadic_primitive k
  have hζ₀prim : IsPrimitiveRoot ζ₀ (2 ^ k) := by
    have h := IsPrimitiveRoot.orderOf ζ₀
    rwa [hζ₀ord] at h
  set j : ℂ →+* B := (algebraMap (RatFunc ℂ) B).comp (algebraMap ℂ (RatFunc ℂ)) with hj
  have hinj : Function.Injective j :=
    (algebraMap (RatFunc ℂ) B).injective.comp (algebraMap ℂ (RatFunc ℂ)).injective
  refine ⟨B, hBfield, hBalg, i, a, GB, j ζ₀, k, hdk, ?_, hirr, hroot, hiGB⟩
  exact hζ₀prim.map_of_injective hinj

end Bottcher
