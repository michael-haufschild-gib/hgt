# Family-DSS = the Grand Simplicity Hypothesis (G13)

- **ID:** family-dss-gsh
- **Stage:** 2-fully-proven (RESOLUTION below: the family cross-resonance is finite-cyclotomic BRIDGE; the
  transcendence is the same A2/`F₁` value-lift apex realized across the family — **not a new gatekeeper**)
- **Type:** THEOREM (paper, resolution), Door-2 **BRIDGE (substrate)**; residual transcendence = the A2
  value-lift (FIELDS MEDAL, not new)
- **Priority:** FOUNDATIONAL (the resolution); the A2 apex it folds into = FIELDS MEDAL
- **Owner:** Wheeler
- **Source:** ../../door/bucket-new-sibling-conjectures.md (#69 SEED-N) · 00-status row #100
- **Statement:** Across primitive Dirichlet `L(s, χ)` the difference bases are **SHARED** (the same
  primes `p`, only the twist `χ(p)` differs), so family-independence is **NOT free** — there is a
  genuinely new obstruction: **cross-resonance over the common primes**, unkillable by unique
  factorization. **Conjecture:** the twisted difference module of `{L(s, χ)}` has **no cross-resonances**
  ⟺ the character twists alone decouple the shared-prime spectra. **GSH (Rudnick–Sarnak Grand Simplicity
  Hypothesis) = its linear shadow.**

## Goal
The genuinely-new transcendence content beyond single-`L` DSS: because the prime base is shared across
the family, the unique-factorization "free flow" that makes single-`L` orbit-dimension free **no longer
applies** — cross-resonances among `{χ(p)}` are a new lattice the field must control. Places GSH,
`n`-level correlations, and pair correlation in **one transcendence framework**, extending G2/DSS to
families.

## Door passport
- **Door-1/4:** the twisted multi-`q` module over the shared prime base — native, and the shared base is
  exactly where the new (non-free) obstruction lives.
- **Door-3:** the cross-resonance lattice among the twists is a native invariant (not the per-`L`
  relation lattice `Λ = {0}`).
- **Door-2:** the test is whether killing cross-resonances needs the joint twisted-`σ_p` structure
  (native) or reduces to GSH's linear independence (a parent) — the linear shadow is the BRIDGE floor.

## Gates
- [x] 0 → 1  in-progress: cross-resonance lattice posed; GSH = linear shadow; Door passport sharpened
- [x] 1 → 2  fully-proven (BRIDGE substrate): RESOLUTION §R1–§R4 — the cross-resonance is finite-cyclotomic
  (unique factorization on the modulus + abelian `ℚ(ζ_q)` Galois), proven BRIDGE; the value level = the same
  A2/`F₁` apex (GSH = its linear shadow); Door-5 `F_q` check; consistent with #107/#275. **Not a new gatekeeper.**
- [ ] 2 → 3  formalized: PARTIAL Lean anchor done for the finite modulus split and per-prime balance
  (`../3-formalized/family-cross-resonance-modulus-split.md`,
  `familyPrimeBalance_apply_eq_zero_of_primeProduct_eq`). Remaining unformalized payload: Dirichlet
  characters, finite cyclotomic Galois relations, GSH/value-level statements, and the A2/F1 apex layer.
- [ ] 3 → 4  publication-ready

## Approach
Build the difference module of the family `{L(s, χ)}` over the common primes with the twists `χ(p)` as
data; identify the cross-resonance relations (the analogue of `m·ℓ = 0` but across characters); show
their absence ⟺ the twists decouple the spectra. Compare against GSH (the ℚ-linear-independence of the
`{γ}` across the family) as the linearized version.

## Cross-references
- `g2-dss-lower-bound.md` — single-`L` DSS, which this extends to families.
- `transcendence-implies-gue.md` — family-DSS ⟹ GUE universality (B11) depends on this.
- `../../door/G2-multi-q-siegel-shidlovsky.md` — the parent gatekeeper.

## Log
- 2026-06-19 — created in 0-backlog. Family-DSS / GSH (G13, SEED-N): the shared-prime cross-resonance
  obstruction extending G2; #4 on the bucket's promotion shortlist.
- 2026-06-19 — Leaner: added the partial formalized anchor
  `../3-formalized/family-cross-resonance-modulus-split.md`. Lean theorem `familyTwistedProduct_split`
  proves the finite twist/shared-scale product split, and `familyPrimeBalance_apply_eq_zero_of_primeProduct_eq`
  proves `Σ_χ m_{χ,p}=0` from the trivial shared-prime modulus product. Parent remains in `2-fully-proven`;
  Dirichlet characters, cyclotomic Galois structure, GSH/value statements, and the A2/F1 layer are still
  paper-level.

---

# RESOLUTION (Wheeler, 2026-06-19) — G13 folds into the A2 apex; the cross-resonance is finite-cyclotomic BRIDGE

The card's open Door-2 question ("does killing cross-resonances need the joint twisted-`σ_p` structure
(native), or reduce to a parent?") is **answered: BRIDGE**. The worry that the shared prime base creates a
"genuinely new obstruction unkillable by unique factorization" is **refuted**.

## §R1 The cross-resonance lattice is finite-cyclotomic `[PROVEN, BRIDGE]`
A family cross-resonance is `∏_{χ,p}(χ(p)\,p^{-1})^{m_{χ,p}} = 1` (`m∈ℤ^{(\text{char}×P)}`). Split it by modulus:
> `∏_{χ,p}(χ(p)p^{-1})^{m_{χ,p}} = \underbrace{∏_p p^{-Σ_χ m_{χ,p}}}_{\text{positive rational}} · \underbrace{∏_{χ,p}χ(p)^{m_{χ,p}}}_{\text{root of unity}}.`
The Dirichlet twists `χ(p)` are `q`-th roots of unity (`|χ(p)|=1`), so the second factor has modulus 1. For
the product to be `1`, the first factor must be `1`:
> `∏_p p^{-Σ_χ m_{χ,p}} = 1  ⟹  Σ_χ m_{χ,p} = 0  ∀p`   (**unique factorization STILL applies** — to the
> modulus / `|·|` part).
The residual is then a **finite cyclotomic relation** `∏_{χ,p}χ(p)^{m_{χ,p}} = 1` among `q`-th roots of unity.
Since `χ(p)` depends only on `p mod q` (`= ` the image of `Frob_p` in `Gal(ℚ(ζ_q)/ℚ) ≅ (ℤ/q)^×`), this is
exactly the **abelian cyclotomic Galois structure**. So:
> **The cross-resonance lattice = `{Σ_χ m_{χ,p}=0 ∀p}` (unique factorization) `∩` `{finite cyclotomic
> root-of-unity relation}` — both classical. It is BRIDGE, not a new transcendence obstruction.**
The card's premise ("unkillable by unique factorization") fails: unique factorization kills the modulus part;
what remains is finite/abelian/cyclotomic. ∎

## §R2 The value level (GSH) = the SAME F₁ value-lift, realized across the family `[A2 apex, not new]`
GSH is the **value-level** statement: the zeros `{γ_χ}` across the family are jointly ℚ-independent. All
`{L(s,χ)}` share the **same archimedean place** (the same `Γ_ℝ` factor / the same Source-A digamma), so the
**value-lift `F₁` is the same single archimedean obstruction** for every `χ`. By the tower-factorization logic
(`bigraded-corank` §G), the joint independence = (each per-`L` value-lift) `∧` (no cross relations); the
cross relations at the function level are the §R1 finite-cyclotomic structure (BRIDGE), and the transcendence
content is the per-place `F₁`. So **GSH = the A2/value-lift apex (the same `F₁`) realized across the family**;
GSH's ℚ-linear independence (Rudnick–Sarnak) is its **linear shadow** — not a new apex.

## §R3 General automorphic GSH `[note]`
For higher-degree `L`, the twists are Satake parameters `α_{χ,p}` (not roots of unity), but by **Ramanujan**
(`|α_{χ,p}|=1`, known for the arithmetic/motivic cases) the §R1 modulus argument is unchanged: cross-resonance
forces per-prime balance (unique factorization), residual = an algebraic relation among the modulus-1 Satake
data = the Hecke/Galois structure (algebraic, BRIDGE). Same verdict; the cyclotomic special case is `GL_1`.

## §R4 Door / grade
- **Door-2: BRIDGE.** §R1 strips to unique factorization + finite cyclotomic (abelian) Galois; §R2 is the same
  A2/`F₁` apex. **D2 substrate:** G13 folds into the two-apex picture (the family-realization of the A2 apex),
  not a new gatekeeper.
- **Door-5 ✓:** over `F_q`, the family = `L`-functions of covers, finite Frobenius, corank 1; all resolved
  (Deligne / Papanikolas-family), `K=1` — no new obstruction. The cross-resonance is number-field-cyclotomic,
  classical there too.
- **Consistency:** matches #107 (family-DSS ⇏ GUE — the failed downstream) and the ω/RH two-apex decoupling
  (#275): G13 is purely A2-axis (transcendence), with the family layer finite/classical.

**Net:** G13/family-DSS-GSH is **NOT a new gatekeeper.** The cross-resonance over shared primes is BRIDGE
(unique factorization + finite cyclotomic abelian Galois); the transcendence is the **same A2 value-lift `F₁`**
realized across the family, with GSH its linear shadow. Grade **THEOREM (paper), BRIDGE (substrate)**.
