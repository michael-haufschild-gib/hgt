# Family-DSS = the Grand Simplicity Hypothesis (G13)

- **ID:** family-dss-gsh
- **Stage:** 0-backlog
- **Type:** CANDIDATE → CONJECTURE (native; extends G2)
- **Priority:** FIELDS MEDAL
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
- [ ] 0 → 1  in-progress: the twisted (shared-prime) multi-`q` module defined; the cross-resonance
  lattice posed; GSH identified as the linear shadow; Door passport sharpened
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
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
