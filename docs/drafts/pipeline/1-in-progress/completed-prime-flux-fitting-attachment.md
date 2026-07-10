# Completed prime-flux attachment to the canonical Fitting seam

- **ID:** completed-prime-flux-fitting-attachment
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** RHTower `WeldZeroGenerator` + `CanonicalCutoffTorsionSeam`
- **Statement:** `[CONJECTURE]` At every zero `ρ` of `ξ` in the open critical strip, if `m = ordρ(ξ)`, then the continued infinite-prime flux `−ζ′/ζ` has normalized punctured limit `−1`, and this value is exactly the constant jet defining the canonical non-split Fitting boundary in `ℚ[X]/(X^m)`.

## Goal

Attach the already-constructed canonical sheared torsion seam to the completed arithmetic carrier.
The right-half-plane identity `−ζ′/ζ = Σ Λ(n)n⁻ˢ` supplies an infinite source whose
frequencies all lie in the prime-log weld lattice.  Its meromorphic continuation has a pole at each
strip zero; the local residue should produce, rather than assume, the seam's surviving boundary
class.  This does not assert RH or spectral positivity.  It removes the independent Fitting-boundary
hypothesis from the arithmetic local model.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

1. Peel `ξ` at an arbitrary point and prove the punctured local identity
   `(s−ρ) logDeriv ξ(s) = m + (s−ρ) logDeriv h(s)` with `h(ρ) ≠ 0`.
2. At a zero, divide the negative logarithmic derivative by `m`; continuity of the unit term gives
   the limit `−1` without a simple-zero hypothesis.
3. In the open strip, prove `ordρ(ζ) = ordρ(ξ)` because `archFactor` is an analytic unit, and
   transfer the same limit to `−ζ′/ζ`.
4. Set the canonical seam depth to this order.  The zero hypothesis supplies `m > 0`, hence its
   Fitting boundary is nonzero and its class is the jet of the same scalar `−1`.
5. Package the right-half-plane von Mangoldt identity and prime-log frequency support with the local
   strip residue theorem, making the global source and local seam one unconditional capstone.

## Open core

`[OPEN CORE]` The local residue and arithmetic-source identification do not themselves construct a
positive spectral realization or annihilate off-line charge.  That later global step must use the
non-split seam without replacing it by a split diagonal presentation.

## Log

- 2026-07-10 — created in 1-in-progress; local `ξ` residue theorem typechecked in scratch.
