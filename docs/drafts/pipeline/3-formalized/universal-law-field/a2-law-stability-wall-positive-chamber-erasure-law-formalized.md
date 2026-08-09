# A₂ law-stability wall and positive chamber erasure — Lean certification

- **ID:** ULF-LSW-1
- **Paper card:**
  `a2-law-stability-wall-positive-chamber-erasure-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveStabilityWall`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## New reusable content

Mathlib has no comparison lemma for `Complex.arg` on the upper half-plane.  This module supplies it:

- `arg_pos_of_im_pos`, `arg_lt_pi_of_im_pos` — the phase of an upper half-plane point lies in
  `(0, π)`;
- `arg_div_eq_sub` — there `arg (z / w) = arg z − arg w` exactly, no branch correction;
- `arg_lt_arg_iff_cross_pos` — hence `arg w < arg z ↔ 0 < Im(z · conj w)`: the phase order **is**
  the sign of the cross product.

## Certified declarations

### Theorem 1 — complete wall classification

`subrep_classification` proves that a subrepresentation of `E = (ℂ →id ℂ)`, i.e. a pair of subspaces
of `ℂ` with `U₁ ≤ U₂`, is one of exactly three: `(⊥,⊥)`, `(⊥,⊤)`, `(⊤,⊤)`.  `subrep_proper_nonzero`
extracts the card's statement: the unique nonzero proper subobject is `S₂ = (0, ℂ)`.

`stability_iff` then proves, for charges in the open upper half-plane,

`arg z₂ < arg (z₁ + z₂) ↔ arg z₂ < arg z₁`,

which is exactly (2): stability of `E` — the unique nonzero proper subobject having strictly smaller
phase — is the phase order of the two simples.  The proof is the cross-product criterion plus
`Im(z₂ · conj z₂) = 0`, which is the certified form of "the argument of the sum of two non-collinear
upper half-plane vectors lies strictly between their arguments".

`arg_eq_of_arg_eq` proves that when `arg z₁ = arg z₂` the sum has the same phase: `E` is strictly
semistable on the wall.

### Theorem 2 — positivity identifies opposite chambers

For `z₁(θ) = exp(i(π/2+θ))`, `z₂(θ) = exp(i(π/2−θ))` with `|θ| < π/2`:

- `wallCharge₁_im`, `wallCharge₂_im`, `wallCharge_im_pos` — both charges have imaginary part
  `cos θ > 0`, so they lie in the open upper half-plane;
- `wallCharge_cross` — `Im(z₁ · conj z₂) = sin 2θ`;
- `wallFamily_stable_iff_pos` — hence `E` is stable **exactly** for `θ > 0` (and, with
  `arg_eq_of_arg_eq`, strictly semistable at `θ = 0`);
- `wallCharge_sum` — `z₁ + z₂ = 2i cos θ`;
- `wallFamily_modulus_packet` — the packet is `(1, 1, 2|cos θ|)`;
- `wallFamily_modulus_packet_symm` — it is the same at `θ` and `−θ`;
- `positive_chamber_erasure` — the capstone: stable at `θ > 0`, unstable at `−θ`, identical
  moduli.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveStabilityWall.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveStabilityWall
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed with no warnings.  `#print axioms` on the subobject classification, the phase
criterion, the stability criterion, the semistable wall, the wall family and the capstone reports
only `propext`, `Classical.choice`, and `Quot.sound`.  No project axiom, placeholder, hypothesis
interface, or unresolved theorem premise is used.

## Exact field consequence

Three levels come apart on one fixed object: the algebraic exact law never changes; the constitutive
phase order changes which composite is admitted as stable; and the positive modulus quotient
identifies the two opposite chambers.  An observer change can therefore alter the effective
factorization doctrine of the theorem category itself, not merely erase information about a fixed
theorem — and positivity is exactly the reader that cannot see which side of the wall the law is on.
